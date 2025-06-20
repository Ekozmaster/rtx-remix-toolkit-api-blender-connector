# FILE: remix_bake_worker.py

import bpy
import os
import sys
import json
import argparse
import traceback
from datetime import datetime

# --- Worker-Specific Functions ---

def log(msg, *a):
    """Timestamped print to stderr for logging."""
    t = datetime.now().strftime("%H:%M:%S.%f")[:-3]
    print(f"[BakeWorker] {t} | {msg % a if a else msg}", file=sys.stderr, flush=True)

def setup_render_engine():
    """Configures Cycles for baking, enabling GPU if available."""
    try:
        bpy.context.scene.render.engine = 'CYCLES'
        cycles_prefs = bpy.context.preferences.addons["cycles"].preferences
        
        # Enable all available devices for the preferred backend
        dev_type = getattr(cycles_prefs, "compute_device_type", "NONE")
        if dev_type in {"CUDA", "OPTIX", "HIP", "METAL", "ONEAPI"}:
            cycles_prefs.compute_device_type = dev_type
            bpy.context.scene.cycles.device = 'GPU'
            
            # Get devices and enable them
            devices = cycles_prefs.get_devices_for_type(dev_type)
            enabled_devices = []
            for device in devices:
                device.use = True
                enabled_devices.append(device.name)
            
            if enabled_devices:
                log(f"GPU ({dev_type}) enabled for devices: {', '.join(enabled_devices)}")
            else:
                log(f"Warning: Preferred backend {dev_type} has no available devices. Falling back to CPU.")
                bpy.context.scene.cycles.device = 'CPU'
        else:
            bpy.context.scene.cycles.device = 'CPU'
            log("No GPU backend selected in preferences. Using CPU.")
            
    except Exception as e:
        log(f"Error setting up GPU render engine: {e}. Defaulting to CPU.")
        bpy.context.scene.cycles.device = 'CPU'

def perform_bake(task):
    """Main function to execute a single bake task with stable, conditional logic."""
    obj_name = task['object_name']
    mat_uuid = task['material_uuid']
    target_socket_name = task['target_socket_name']
    bake_type = task['bake_type']

    obj = bpy.data.objects.get(obj_name)
    if not obj:
        log(f"ERROR: Object '{obj_name}' not found in the scene.")
        return False

    mat = next((m for m in bpy.data.materials if m.get("uuid") == mat_uuid), None)
    if not mat or not mat.use_nodes:
        log(f"ERROR: Material with UUID '{mat_uuid}' not found or does not use nodes.")
        return False

    nt = mat.node_tree
    
    # --- Initialize resources for safe cleanup in 'finally' block ---
    img = None
    tex_node = None
    hijack_emit_node = None
    original_link_info = None # Use a dictionary to store names, which is safer than storing the link object

    try:
        log(f"Baking '{mat.name}' -> '{target_socket_name}' (Type: {bake_type}) for '{obj.name}'")

        # --- 1. Isolate Object and Create Bake Target Image (Universal for all bakes) ---
        for o in bpy.context.scene.objects:
            o.hide_render = (o.name != obj.name)

        img = bpy.data.images.new(
            name=os.path.basename(task['output_path']),
            width=task['resolution_x'],
            height=task['resolution_y'],
            alpha=True
        )
        img.filepath_raw = task['output_path']
        img.file_format = 'PNG'
        if task['is_value_bake'] or bake_type == 'NORMAL':
            img.colorspace_settings.name = 'Non-Color'

        tex_node = nt.nodes.new('ShaderNodeTexImage')
        tex_node.image = img
        nt.nodes.active = tex_node # This is critical: the active node must be the target image

        # --- 2. Conditionally Modify Node Tree (The Core Fix) ---
        output_node = next((n for n in nt.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
        if not output_node:
            raise RuntimeError(f"No active material output in '{mat.name}'")

        if bake_type == 'EMIT':
            log(" > EMIT bake detected. Applying emission hijack.")
            
            # Find the socket to bake from (including the displacement special case)
            original_socket = None
            if target_socket_name == "Displacement":
                 original_socket = output_node.inputs.get(target_socket_name)
            else:
                bsdf = next((n for n in nt.nodes if n.type == 'BSDF_PRINCIPLED'), None)
                if not bsdf: raise RuntimeError(f"No Principled BSDF in '{mat.name}' for EMIT bake.")
                original_socket = bsdf.inputs.get(target_socket_name)
            
            if not original_socket or not original_socket.is_linked:
                log(f" > Socket '{target_socket_name}' not linked. Skipping EMIT bake.")
                return True

            # Store link info as names, then hijack
            if output_node.inputs['Surface'].is_linked:
                link = output_node.inputs['Surface'].links[0]
                original_link_info = {"from_node": link.from_node.name, "from_socket": link.from_socket.name, "to_socket": link.to_socket.name}
            
            hijack_emit_node = nt.nodes.new('ShaderNodeEmission')
            nt.links.new(original_socket.links[0].from_socket, hijack_emit_node.inputs['Color'])
            nt.links.new(hijack_emit_node.outputs['Emission'], output_node.inputs['Surface'])
        else:
            log(f" > {bake_type} bake detected. No emission hijack needed.")
            # For non-EMIT bakes (like ROUGHNESS, NORMAL), leaving the node tree untouched is correct.

        # --- 3. Configure and Execute Bake ---
        scn = bpy.context.scene
        scn.render.bake.use_clear = True
        scn.render.bake.margin = 16
        scn.cycles.samples = 1
        
        # STABILITY FIX: Replace bpy.ops with direct data access for selection
        for o in bpy.context.view_layer.objects:
            o.select_set(False)
        obj.select_set(True)
        bpy.context.view_layer.objects.active = obj

        log(" > Starting bpy.ops.object.bake(type='%s')", bake_type)
        t_start = datetime.now()
        bpy.ops.object.bake(type=bake_type)
        t_end = datetime.now()
        log(" > Bake finished in %.2fs. Saving image...", (t_end - t_start).total_seconds())

        img.save()
        log(" > Image saved to: %s", task['output_path'])
        return True

    except Exception as e:
        log(f"!!! BAKE FAILED for '{mat.name}' -> '{target_socket_name}' !!!\n{traceback.format_exc()}")
        return False
        
    finally:
        # --- 4. Restore Original State (CRITICAL FOR STABILITY) ---
        log(" > Cleaning up material '%s'...", mat.name)
        
        # This block only runs if a hijack was performed
        if hijack_emit_node:
            if output_node.inputs['Surface'].is_linked:
                 nt.links.remove(output_node.inputs['Surface'].links[0])
            nt.nodes.remove(hijack_emit_node)
            if original_link_info:
                # Safely restore the link using the stored names
                from_node = nt.nodes.get(original_link_info["from_node"])
                if from_node:
                    from_socket = from_node.outputs.get(original_link_info["from_socket"])
                    to_socket = output_node.inputs.get(original_link_info["to_socket"])
                    if from_socket and to_socket:
                        nt.links.new(from_socket, to_socket)

        # Cleanup that happens for ALL bakes
        if tex_node and tex_node.name in nt.nodes:
            nt.nodes.remove(tex_node)
        
        if img and img.name in bpy.data.images:
            bpy.data.images.remove(img)
            
        for o in bpy.context.scene.objects:
            o.hide_render = False
        log(" > Cleanup complete.")

# --- Main Execution Block ---

if __name__ == "__main__":
    final_exit_code = 0
    try:
        # --- Argument Parsing ---
        parser = argparse.ArgumentParser()
        # Blender's arg parser can be tricky; we get args after '--'
        argv = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else []
        parser.add_argument("--tasks-json", help="JSON string of bake tasks.", required=True)
        args = parser.parse_args(argv)

        tasks_to_run = json.loads(args.tasks_json)
        log(f"Worker started. Received {len(tasks_to_run)} task(s).")
        
        setup_render_engine()

        for i, task in enumerate(tasks_to_run):
            log(f"--- Task {i+1}/{len(tasks_to_run)} ---")
            if not perform_bake(task):
                final_exit_code = 1 # Mark failure if any task fails
        
    except Exception as e:
        log("!!! UNHANDLED WORKER ERROR !!!")
        log(f"Error: {e}")
        traceback.print_exc(file=sys.stderr)
        final_exit_code = 1

    finally:
        log(f"Worker finished. Exiting with code: {final_exit_code}")
        # Flush streams and quit Blender
        sys.stdout.flush()
        sys.stderr.flush()
        bpy.ops.wm.quit_blender()
        sys.exit(final_exit_code)