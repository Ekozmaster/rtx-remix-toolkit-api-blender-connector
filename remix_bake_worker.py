import bpy
import os
import sys
import json
import argparse
import traceback
from datetime import datetime
import time
import re
import tempfile # <-- ADD THIS LINE
import uuid     # <-- ADD THIS LINE
from threading import Lock, RLock
from collections import defaultdict

# --- Worker-Specific Globals & Functions ---

class Counter:
    def __init__(self, total=0):
        self.i = 0
        self.total = total
    
    # ---> START OF FIX 2.A: ADD A METHOD TO SET THE CURRENT NUMBER <---
    def set_current(self, n):
        self.i = n
    # ---> END OF FIX 2.A <---
    
    def get_progress_str(self):
        return f"Task {self.i}/{self.total}"

task_counter = Counter()
realized_mesh_cache = {} 
worker_pid = os.getpid()

# --- THE DEFINITIVE FIX V2 ---
# 1. A per-material lock for standard node operations.
material_locks = defaultdict(RLock)
# 2. A single, global lock to serialize the material.copy() operation.
COPY_BAKE_GLOBAL_LOCK = Lock()

def log(msg, *a):
    t = datetime.now().strftime("%H:%M:%S.%f")[:-3]
    progress_str = task_counter.get_progress_str()
    print(f"[BakeWorker-{worker_pid}] {t} | {progress_str} | {msg % a if a else msg}", file=sys.stderr, flush=True)

def setup_render_engine():
    log("Setting up render engine...")
    try:
        bpy.context.scene.render.engine = 'CYCLES'
        bpy.context.scene.cycles.samples = 1 
        cycles_prefs = bpy.context.preferences.addons["cycles"].preferences
        preferred_order = ["OPTIX", "CUDA", "HIP", "METAL", "ONEAPI"]
        available_backends = [b[0] for b in cycles_prefs.get_device_types(bpy.context)]
        dev_type = next((b for b in preferred_order if b in available_backends), "NONE")
        log(f" > Found best available backend: {dev_type}")
        if dev_type != "NONE":
            cycles_prefs.compute_device_type = dev_type
            bpy.context.scene.cycles.device = 'GPU'
            for device in cycles_prefs.get_devices_for_type(dev_type): device.use = True
            log(f" > SUCCESS: GPU ({dev_type}) enabled.")
        else:
            bpy.context.scene.cycles.device = 'CPU'
            log(" > No compatible GPU backend found. Using CPU.")
    except Exception as e:
        log(f" > ERROR setting up render engine: {e}. Defaulting to CPU.")
        bpy.context.scene.cycles.device = 'CPU'


def _get_socket_to_bake(node_tree, target_socket_name):
    output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
    if not output_node: return None
    if output_node.inputs['Surface'].is_linked:
        final_shader_node = output_node.inputs['Surface'].links[0].from_node
        socket = final_shader_node.inputs.get(target_socket_name)
        if socket: return socket
    return output_node.inputs.get(target_socket_name)
               
      
def perform_bake_task(task):
    # ---> START OF FIX 2.B: USE THE GLOBAL NUMBER FROM THE TASK <---
    # Instead of incrementing a local counter, we set the global one we received.
    global_num = task.get("global_task_number", 0) # Use .get() for safety
    task_counter.set_current(global_num)
    # ---> END OF FIX 2.B <---
    
    bake_target_obj_name = task['object_name']
    bake_target_obj = bpy.data.objects.get(bake_target_obj_name)
    
    if not bake_target_obj:
        log(f"!!! BAKE TASK FAILED for '{bake_target_obj_name}'. Object not found in blend file.")
        return False
        
    try:
        # ------------------- REMOVED SECTION START -------------------
        # The worker's only job is to reconstruct the UVs from the file provided by the main addon.
        # uv_data_path = task.get("uv_data_filepath")
        # if uv_data_path and os.path.exists(uv_data_path):
        #     log(f" > Reconstructing UVs for '{bake_target_obj.name}' from file...")
        #     try:
        #         with open(uv_data_path, 'r') as f:
        #             uv_data_flat = json.load(f)
        #         
        #         if not bake_target_obj.data: raise RuntimeError("Object has no mesh data.")
        #         
        #         while bake_target_obj.data.uv_layers:
        #             bake_target_obj.data.uv_layers.remove(bake_target_obj.data.uv_layers[0])
        #             
        #         uv_layer = bake_target_obj.data.uv_layers.new(name="UVMap_Bakeable")
        #         uv_layer.data.foreach_set('uv', uv_data_flat)
        #         uv_layer.active_render = True
        #         bake_target_obj.data.uv_layers.active = uv_layer
        #         log(f"   > SUCCESS: Reconstructed and activated UV map for '{bake_target_obj.name}'.")
        #     except Exception as e:
        #         log(f"   > FAILED to apply UV data from file '{uv_data_path}': {e}")
        #         raise # Re-raise the exception to fail the task
        # -------------------- REMOVED SECTION END --------------------

        # --- NEW OPTIMIZED UV HANDLING ---
        # Simply ensure the first UV map is the active one for baking.
        if bake_target_obj.data and bake_target_obj.data.uv_layers:
            if bake_target_obj.data.uv_layers.active is None or bake_target_obj.data.uv_layers.active_index != 0:
                bake_target_obj.data.uv_layers.active_index = 0
                log(f" > Activated existing UV map for '{bake_target_obj.name}'.")
        else:
            log(f" > WARNING: No UV maps found on '{bake_target_obj.name}'. Bake may fail or produce incorrect results.")
            # This is a fallback warning; the main addon should ensure UVs exist.
        
        original_mat = next((m for m in bpy.data.materials if m.get("uuid") == task['material_uuid']), None)
        if not original_mat: raise RuntimeError(f"Material UUID '{task['material_uuid']}' not found.")
        
        log(f"Starting Bake: Obj='{bake_target_obj.name}', Mat='{original_mat.name}', Type='{task['bake_type']}'")
        perform_single_bake_operation(bake_target_obj, original_mat, task)
        return True

    except Exception:
        log(f"!!! BAKE TASK FAILED for '{bake_target_obj_name}' !!!")
        log(traceback.format_exc())
        return False
        
def _recover_packed_image_for_bake(image_datablock):
    """
    [DEFINITIVE V2 - ROBUST RECOVERY]
    Worker-side function to handle packed images. It saves packed/generated
    image data to a temporary file that the bake process can use. This version
    is more robust as it manually creates a new image and copies pixels,
    avoiding the unreliable datablock.copy().save() method.
    Returns the path to the temporary file, or the original path if unchanged.
    """
    if not image_datablock:
        return None

    filepath = ""
    try:
        # Check for an existing, valid file path first.
        if image_datablock.filepath_from_user():
            filepath = abspath(image_datablock.filepath_from_user())
    except Exception:
        pass # Path is invalid, proceed to recovery check.

    if os.path.exists(filepath):
        return filepath # Image is already valid on disk, no recovery needed.

    # If no valid path, check if it has pixel data in memory (packed/generated).
    if image_datablock.has_data:
        # This is the recovery path for in-memory images.
        temp_dir = tempfile.gettempdir()
        # Create a safe, unique filename for the temporary image.
        safe_name = "".join(c for c in image_datablock.name if c.isalnum() or c in ('_', '.', '-')).strip()
        temp_filename = f"remix_bake_worker_{worker_pid}_{safe_name}_{uuid.uuid4().hex[:6]}.png"
        temp_filepath = os.path.join(temp_dir, temp_filename)
        
        try:
            # --- THE ROBUST METHOD ---
            # 1. Create a new, blank image datablock.
            image_for_saving = bpy.data.images.new(
                name=f"temp_save_{image_datablock.name}",
                width=image_datablock.size[0],
                height=image_datablock.size[1],
                alpha=True # Always use alpha for safety
            )
            
            # 2. Explicitly copy the pixels from the source to the new image.
            #    If this line fails, the source truly has no readable pixel data.
            image_for_saving.pixels = image_datablock.pixels[:]

            # 3. Save the NEW image, which we know has valid pixel data.
            image_for_saving.filepath_raw = temp_filepath
            image_for_saving.file_format = 'PNG'
            image_for_saving.save()
            
            # 4. Clean up the temporary datablock we created.
            bpy.data.images.remove(image_for_saving)
            
            log(f" > Successfully recovered packed image '{image_datablock.name}' to temporary file for baking.")
            return temp_filepath
        except Exception as e:
            # This will catch the "does not have any image data" error if pixels[:] fails.
            log(f" > ERROR: Failed to recover packed image '{image_datablock.name}': {e}")
            # Clean up the failed save attempt if it exists.
            if 'image_for_saving' in locals() and image_for_saving.name in bpy.data.images:
                bpy.data.images.remove(image_for_saving)
            return None
    
    # If the image has no valid path AND no data, it's unrecoverable.
    return None

def perform_single_bake_operation(obj, original_mat, task):
    """
    [DEFINITIVE V3.2 - Using Robust Recovery]
    Performs a single bake operation. This version ALWAYS works on a temporary
    copy of the material and uses the new, robust recovery logic.
    """
    mat_for_bake = None
    temp_mat_name_for_cleanup = None
    original_mat_slot_index = -1
    img = None
    render_bake = bpy.context.scene.render.bake

    try:
        # --- Stage 1: Create a temporary, isolated copy for the bake ---
        mat_for_bake = original_mat.copy()
        temp_mat_name_for_cleanup = mat_for_bake.name
        nt = mat_for_bake.node_tree
        if not nt: raise RuntimeError(f"Material copy '{mat_for_bake.name}' failed to create a node tree.")

        # --- In-Worker Texture Re-linking and Recovery ---
        # After material.copy(), image datablocks are duplicated and empty.
        # We must find the original datablock (which has the pixels) and recover it.
        if nt:
            for node in nt.nodes:
                if node.type == 'TEX_IMAGE' and node.image:
                    copied_image = node.image
                    
                    # The original datablock is stored in the .original property if it's a copy.
                    # If it's not a copy (or if the link is broken), .original is None.
                    source_datablock_with_pixels = copied_image.original if copied_image.original else copied_image
                    
                    # Use our new, robust recovery function on the correct source datablock.
                    recovered_path = _recover_packed_image_for_bake(source_datablock_with_pixels)
                    
                    if recovered_path:
                        # Replace the node's broken image reference with a new, valid one.
                        try:
                            node.image = bpy.data.images.load(recovered_path, check_existing=True)
                        except Exception as e:
                            log(f" > ERROR loading recovered image '{recovered_path}': {e}")
        # ---> END OF THE DEFINITIVE FIX <---

        # --- Stage 2: Temporarily assign the copy to the object ---
        # (The rest of the function remains the same as your provided code)
        for i, slot in enumerate(obj.material_slots):
            if slot.material == original_mat:
                slot.material = mat_for_bake
                original_mat_slot_index = i
                break
        
        if original_mat_slot_index == -1:
            raise RuntimeError(f"Could not find original material '{original_mat.name}' on object '{obj.name}' to replace.")

        # ... (The rest of your function from Stage 3 onwards is correct and does not need to be changed) ...
        # --- Stage 3: Prepare the bake image and arguments ---
        if obj.data.uv_layers: obj.data.uv_layers.active_index = 0
        
        img = bpy.data.images.new(name=f"BakeTarget_{task['material_uuid']}", width=task['resolution_x'], height=task['resolution_y'], alpha=True)
        img.filepath_raw = task['output_path']
        img.file_format = 'PNG'
        if task.get('is_value_bake') or task['bake_type'] in ['NORMAL', 'ROUGHNESS']:
            img.colorspace_settings.name = 'Non-Color'
        
        bake_args = {'use_clear': True, 'margin': 8, 'type': task['bake_type']}

        # --- Stage 4: Modify the temporary material copy based on bake type ---
        hijack_nodes = []
        
        if task['bake_type'] == 'EMIT':
            output_node = next((n for n in nt.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
            socket_to_bake = _get_socket_to_bake(nt, task['target_socket_name'])
            
            if not socket_to_bake:
                log(" > Socket not found for EMIT bake, skipping.")
                return
            
            if output_node and output_node.inputs['Surface'].is_linked:
                for link in list(output_node.inputs['Surface'].links):
                    nt.links.remove(link)
            
            emission_node = nt.nodes.new('ShaderNodeEmission')
            hijack_nodes.append(emission_node)
            source_socket = socket_to_bake.links[0].from_socket if socket_to_bake.is_linked else None
            
            if source_socket:
                if task.get('is_value_bake'): nt.links.new(source_socket, emission_node.inputs['Strength'])
                else: nt.links.new(source_socket, emission_node.inputs['Color'])
            
            if output_node:
                nt.links.new(emission_node.outputs['Emission'], output_node.inputs['Surface'])

        elif task['bake_type'] == 'DIFFUSE':
            render_bake.use_pass_direct = False
            render_bake.use_pass_indirect = False
            render_bake.use_pass_color = True

        tex_node = nt.nodes.new('ShaderNodeTexImage')
        tex_node.image = img
        nt.nodes.active = tex_node
        hijack_nodes.append(tex_node)
        
        # --- Stage 5: Execute the bake ---
        bpy.ops.object.select_all(action='DESELECT')
        bpy.context.view_layer.objects.active = obj
        obj.select_set(True)

        log(" > CALLING BAKE with args: %s", bake_args)
        bpy.ops.object.bake(**bake_args)
        img.save()
        log(" > Bake successful.")

    finally:
        # --- Stage 6: Guaranteed Cleanup ---
        if task['bake_type'] == 'DIFFUSE':
            render_bake.use_pass_direct = True
            render_bake.use_pass_indirect = True
            render_bake.use_pass_color = True

        if obj and original_mat_slot_index != -1 and len(obj.material_slots) > original_mat_slot_index:
            obj.material_slots[original_mat_slot_index].material = original_mat
        
        mat_to_clean = bpy.data.materials.get(temp_mat_name_for_cleanup) if temp_mat_name_for_cleanup else None
        if mat_to_clean:
            bpy.data.materials.remove(mat_to_clean, do_unlink=True)

        if img and img.name in bpy.data.images:
            bpy.data.images.remove(img)

def persistent_worker_loop():
    log("Persistent worker started. Awaiting commands...")
    try:
        initial_command_str = sys.stdin.readline()
        command = json.loads(initial_command_str)
        if command.get("action") == "load_blend":
            blend_file = command.get("blend_file")
            task_counter.total = command.get("total_tasks", 0)
            if blend_file and os.path.exists(blend_file):
                bpy.ops.wm.open_mainfile(filepath=blend_file)
                log(f"Successfully loaded blend file: {blend_file}")
                setup_render_engine()
                print(json.dumps({"status": "ready"}), flush=True)
            else:
                raise RuntimeError(f"Blend file not found: {blend_file}")
    except Exception as e:
        log(f"!!! FATAL: Could not process initial 'load_blend' command: {e}")
        print(json.dumps({"status": "error", "reason": str(e)}), flush=True)
        return

    while True:
        line = sys.stdin.readline()
        if not line:
            log("Input stream closed. Exiting.")
            break 
        result_payload = {}
        try:
            task = json.loads(line)
            if task.get("action") == "quit":
                log("Quit command received. Exiting.")
                break
            success = perform_bake_task(task)
            result_payload = {
                "status": "success" if success else "failure",
                "task_uuid": task.get("material_uuid", "unknown"),
                "target": task.get("target_socket_name", "unknown")
            }
        except json.JSONDecodeError:
            result_payload = {"status": "error", "reason": f"invalid_json: {line}"}
        except Exception as e:
            log(f"!!! UNHANDLED WORKER ERROR during task loop: {e}")
            result_payload = {"status": "error", "reason": str(e)}
        print(json.dumps(result_payload), flush=True)

    for obj_name in realized_mesh_cache.values():
        obj = bpy.data.objects.get(obj_name)
        if obj:
            mesh_data = obj.data
            bpy.data.objects.remove(obj)
            if mesh_data and mesh_data.users == 0: bpy.data.meshes.remove(mesh_data)
    log("Worker task processing complete.")

if __name__ == "__main__":
    final_exit_code = 0
    try:
        parser = argparse.ArgumentParser()
        parser.add_argument("--persistent", action="store_true")
        args, _ = parser.parse_known_args(sys.argv[sys.argv.index("--") + 1:])
        if args.persistent:
            persistent_worker_loop()
        else:
            final_exit_code = 1
    except Exception:
        log("!!! UNHANDLED WORKER ERROR !!!"); log(traceback.format_exc())
        final_exit_code = 1
    finally:
        log(f"Worker finished. Exiting with code: {final_exit_code}")
        sys.stdout.flush(); sys.stderr.flush()
        sys.exit(final_exit_code)
