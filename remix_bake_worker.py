import bpy
import os
import sys
import json
import argparse
import traceback
from datetime import datetime
import time
import math
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
    """
    [DEFINITIVE V2 - UNIVERSAL SHADER FINDER]
    Finds a target socket to bake from, regardless of the shader node setup.
    It starts from the final Material Output and works backwards to find the
    main shader, making it compatible with Principled BSDF, custom node
    groups, or any other setup.
    """
    # Find the active Material Output node.
    output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
    if not output_node:
        log(" > Could not find an active Material Output node.")
        return None

    # Check if the main 'Surface' input is connected to anything.
    if not output_node.inputs['Surface'].is_linked:
        log(" > Material Output node's Surface is not connected to any shader.")
        return None

    # This is the final shader node connected to the output.
    # It could be Principled BSDF, a custom group, a Mix Shader, etc.
    final_shader_node = output_node.inputs['Surface'].links[0].from_node

    # Now, look for the target socket on this final shader node.
    socket = final_shader_node.inputs.get(target_socket_name)
    if socket:
        return socket

    # If not found on the main shader, it might be a direct output (unlikely but possible)
    socket = output_node.inputs.get(target_socket_name)
    if socket:
        return socket

    log(f" > Could not find socket '{target_socket_name}' on the final shader '{final_shader_node.name}'.")
    return None

    
                     
def perform_bake_task(task):
    # ---> THIS IS THE FIX: Read the global number and set the counter <---
    global_num = task.get("global_task_number", task_counter.i + 1)
    task_counter.set_current(global_num)
    # ---> END OF FIX <---

    bake_target_obj_name = task['object_name']
    bake_target_obj = bpy.data.objects.get(bake_target_obj_name)

    if not bake_target_obj:
        log(f"!!! BAKE TASK FAILED for '{bake_target_obj_name}'. Object not found.")
        return False

    try:
        if bake_target_obj.data and bake_target_obj.data.uv_layers:
            if bake_target_obj.data.uv_layers.active_index != 0:
                bake_target_obj.data.uv_layers.active_index = 0
        else:
            log(f" > WARNING: No UV maps on '{bake_target_obj_name}'.")

        original_mat = next((m for m in bpy.data.materials if m.get("uuid") == task['material_uuid']), None)
        if not original_mat:
            raise RuntimeError(f"Material UUID '{task['material_uuid']}' not found.")

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
    [DEFINITIVE V43 - CORRECT OPERATOR CALL]
    This version corrects the embarrassing and repeated TypeError. The bake pass
    settings (use_pass_color, etc.) are now correctly set on the scene's render
    bake settings BEFORE calling the operator, as required by the API. This
    ensures native DIFFUSE bakes execute correctly without crashing.
    """
    # Define all backup variables BEFORE the try block to prevent NameErrors
    scene = bpy.context.scene
    render_settings = scene.render
    bake_settings = render_settings.bake
    image_settings = render_settings.image_settings
    
    original_film_transparent = render_settings.film_transparent
    original_format = image_settings.file_format
    original_color_depth = image_settings.color_depth
    original_compression = image_settings.compression
    original_use_pass_direct = bake_settings.use_pass_direct
    original_use_pass_indirect = bake_settings.use_pass_indirect
    original_use_pass_color = bake_settings.use_pass_color
    
    mat_for_bake = None
    temp_mat_name_for_cleanup = None
    original_mat_slot_index = -1
    img = None
    
    output_node = None
    original_surface_link = None
    hijack_nodes = []

    try:
        mat_for_bake = original_mat.copy()
        temp_mat_name_for_cleanup = mat_for_bake.name
        nt = mat_for_bake.node_tree
        if not nt: raise RuntimeError("Material copy failed.")
        
        for i, slot in enumerate(obj.material_slots):
            if slot.material == original_mat:
                slot.material = mat_for_bake
                original_mat_slot_index = i; break
        if original_mat_slot_index == -1: raise RuntimeError("Could not find original material on object.")

        uv_layer_name_from_task = task.get('uv_layer')
        if uv_layer_name_from_task and uv_layer_name_from_task in obj.data.uv_layers:
            obj.data.uv_layers.active = obj.data.uv_layers[uv_layer_name_from_task]

        img = bpy.data.images.new(name=f"BakeTarget_{task['material_uuid']}", width=task['resolution_x'], height=task['resolution_y'], alpha=True)
        img.filepath_raw = task['output_path']
        
        image_settings.file_format = 'PNG'
        is_high_precision = task['bake_type'] == 'NORMAL' or task['target_socket_name'] == 'Displacement'
        if is_high_precision:
            image_settings.color_depth, image_settings.compression = '16', 0
        else:
            image_settings.color_depth, image_settings.compression = '8', 15
        if not task.get('is_color_data', False):
            img.colorspace_settings.name = 'Non-Color'

        tex_node = nt.nodes.new('ShaderNodeTexImage')
        tex_node.image = img
        nt.nodes.active, tex_node.select = tex_node, True
        hijack_nodes.append(tex_node)
        
        bake_type = task['bake_type']
        bake_args = {'use_clear': True, 'margin': 16, 'type': bake_type}

        if bake_type == 'EMIT':
            log(f" > Setting up EMIT hijack for: {task['target_socket_name']}.")
            output_node = next((n for n in nt.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
            if output_node and output_node.inputs['Surface'].is_linked:
                original_surface_link = output_node.inputs['Surface'].links[0]
            
            socket_to_bake = _get_socket_to_bake(nt, task['target_socket_name'])
            if not socket_to_bake: 
                log(f" > WARNING: Could not find socket '{task['target_socket_name']}' to bake. Skipping this task.")
                return 

            emission_node = nt.nodes.new('ShaderNodeEmission')
            hijack_nodes.append(emission_node)
            if socket_to_bake.is_linked:
                source_socket = socket_to_bake.links[0].from_socket
                if task.get('is_value_bake'): nt.links.new(source_socket, emission_node.inputs['Strength'])
                else: nt.links.new(source_socket, emission_node.inputs['Color'])
            else:
                default_val = socket_to_bake.default_value
                if task.get('is_value_bake'):
                    final_value = sum(default_val) / len(default_val) if hasattr(default_val, '__len__') and len(default_val) > 0 else float(default_val)
                    emission_node.inputs['Strength'].default_value = final_value
                else:
                    emission_node.inputs['Color'].default_value = default_val
            
            if output_node:
                if original_surface_link: nt.links.remove(original_surface_link)
                nt.links.new(emission_node.outputs['Emission'], output_node.inputs['Surface'])
        
        else:
            log(f" > Using native bake pass '{bake_type}'.")
            # --- THIS IS THE FIX ---
            # Set the bake pass properties on the context, NOT in the operator call.
            if bake_type == 'DIFFUSE':
                bake_settings.use_pass_direct = False
                bake_settings.use_pass_indirect = False
                bake_settings.use_pass_color = True
        
        bpy.ops.object.select_all(action='DESELECT')
        bpy.context.view_layer.objects.active = obj
        obj.select_set(True)
        log(" > CALLING BAKE with args: %s", bake_args)
        bpy.ops.object.bake(**bake_args)
        img.save()
        log(" > Bake successful.")

    finally:
        # Restore all settings correctly
        render_settings.film_transparent = original_film_transparent
        image_settings.file_format = original_format
        image_settings.color_depth = original_color_depth
        image_settings.compression = original_compression
        bake_settings.use_pass_direct = original_use_pass_direct
        bake_settings.use_pass_indirect = original_use_pass_indirect
        bake_settings.use_pass_color = original_use_pass_color

        if 'nt' in locals() and nt and output_node:
            if original_surface_link and not output_node.inputs['Surface'].is_linked:
                try: nt.links.new(original_surface_link.from_socket, output_node.inputs['Surface'])
                except Exception: pass
            for node in hijack_nodes:
                if node and node.name in nt.nodes: nt.nodes.remove(node)
        
        if obj and original_mat_slot_index != -1:
            try: obj.material_slots[original_mat_slot_index].material = original_mat
            except Exception: pass
        
        mat_to_clean = bpy.data.materials.get(temp_mat_name_for_cleanup)
        if mat_to_clean: bpy.data.materials.remove(mat_to_clean, do_unlink=True)
        if img and img.name in bpy.data.images: bpy.data.images.remove(img)

def persistent_worker_loop():
    """Main loop for the worker. Includes PID in all stdout messages."""
    log("Persistent worker started. Awaiting commands...")
    
    # A dedicated function to send JSON to stdout, ensuring the PID is always included.
    def send_json_message(payload):
        payload['pid'] = worker_pid # <-- THE FIX: Always add the PID
        print(json.dumps(payload), flush=True)

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
                send_json_message({"status": "ready"}) # <-- Use the helper function
            else:
                raise RuntimeError(f"Blend file not found: {blend_file}")
    except Exception as e:
        log(f"!!! FATAL: Could not process initial 'load_blend' command: {e}")
        send_json_message({"status": "error", "details": str(e)})
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
                "details": f"Task for material {task.get('material_name')} on {task.get('object_name')}"
            }
        except json.JSONDecodeError:
            result_payload = {"status": "error", "details": f"invalid_json: {line}"}
        except Exception as e:
            log(f"!!! UNHANDLED WORKER ERROR during task loop: {e}")
            result_payload = {"status": "error", "details": str(e)}

        send_json_message(result_payload) # <-- Use the helper function

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
