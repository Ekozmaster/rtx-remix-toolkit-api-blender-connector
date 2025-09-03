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
import collections
from threading import Lock, RLock
from collections import defaultdict
from collections import deque

# --- Worker-Specific Globals & Functions ---

class Counter:
    def __init__(self, total=0):
        self.i = 0
        self.total = total
    
    def set_current(self, n):
        self.i = n
    
    def set_total(self, n):
        self.total = n
    
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
         
def _apply_texture_translation_map(task):
    """
    [DEFINITIVE V3 - Corrected for Worker Script]
    Reads the texture translation map from a task and forces the repathing
    of any corresponding image datablocks in the worker's current context.
    It correctly handles paths containing the <UDIM> token and gets the base
    bake directory directly from the task data.
    """
    from bpy.path import abspath

    texture_map = task.get('texture_translation_map', {})
    bake_dir = task.get('bake_dir') # Get bake_dir from the task data
    if not texture_map or not bake_dir:
        log(" > No texture translation map found in task, skipping repath.")
        return

    log(" > Applying texture translation map for this task...")
    reloaded_count = 0
    for image_name, correct_path in texture_map.items():
        image = bpy.data.images.get(image_name)
        if image:
            # --- START OF THE UDIM FIX ---
            if "<UDIM>" in correct_path:
                log(f"   - Repathing UDIM set '{image.name}' to template '{os.path.basename(correct_path)}'")
                image.source = 'TILED'
                # For UDIMs, the path is already a full, valid template from the main addon
                image.filepath_raw = correct_path 
            # --- END OF THE UDIM FIX ---
            else: # Standard, non-UDIM image logic
                current_path = ""
                try: current_path = abspath(image.filepath)
                except Exception: pass

                if current_path.replace('\\', '/') != correct_path.replace('\\', '/') or not image.has_data:
                    log(f"   - Repathing standard image '{image.name}' to '{os.path.basename(correct_path)}'")
                    if correct_path == "GHOST_DATA_UNRECOVERABLE":
                        log(f"   - CRITICAL ERROR: Main addon marked '{image.name}' as unrecoverable. Cannot repath.")
                        continue

                    # The path from the main addon is already absolute and validated
                    if os.path.exists(correct_path):
                        image.filepath = correct_path
                        image.source = 'FILE'
                    else:
                        log(f"   - CRITICAL ERROR: Remap path not found for '{image.name}': '{correct_path}'")
                        continue
            
            # --- Common Reload Logic ---
            try:
                image.reload()
                if not image.has_data:
                     # --- THIS IS THE FIX: Removed the invalid 'level' argument ---
                     log(f"   - INFO: Image '{image.name}' is packed. Recovering from memory.")
                else:
                    reloaded_count += 1
            except Exception as e:
                log(f"   - CRITICAL ERROR: Failed to reload '{image.name}': {e}")
    
    log(f" > Texture repathing complete. {reloaded_count} images reloaded.")
          
def _find_bsdf_and_output_nodes(node_tree):
    """Finds the active Principled BSDF and Material Output nodes."""
    bsdf_node = next((n for n in node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
    output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
    if not output_node:
        output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL'), None)
    return bsdf_node, output_node

def _find_universal_decal_mixer(start_node, end_node, visited_nodes):
    """
    [ITERATIVE VERSION] Finds an intermediate mix shader between a start and end node.
    This version uses a queue to perform a breadth-first search, making it immune to
    stack overflows. It correctly handles nested node groups.
    
    Returns:
        A tuple (found_node, group_instance_node) or None.
        - found_node: The Mix Shader that was found.
        - group_instance_node: The Group Node that contains the found_node, or None if it's in the main tree.
    """
    # The queue stores tuples of: (node_to_check, parent_group_instance)
    q = deque([(start_node, None)])
    visited_nodes.add(start_node)

    while q:
        current_node, parent_group = q.popleft()

        if current_node == end_node:
            continue

        # --- Base Case: Success ---
        if current_node.type == 'MIX_SHADER':
            log(f"      - [Iterative Search] SUCCESS: Found Mix Shader '{current_node.name}'.")
            return (current_node, parent_group)

        # --- Iteration Case 1: Traverse into a Group Node ---
        if current_node.type == 'GROUP' and current_node.node_tree:
            log(f"      - [Iterative Search] Traversing into Group Node: '{current_node.name}' (Tree: '{current_node.node_tree.name}')")
            group_tree = current_node.node_tree
            internal_output = next((n for n in group_tree.nodes if n.type == 'GROUP_OUTPUT' and n.is_active_output), None)
            
            if internal_output:
                shader_input = next((s for s in internal_output.inputs if s.type == 'SHADER' and s.is_linked), None)
                if shader_input:
                    # The next node to check is inside the group, and its "parent" is the current_node group instance.
                    next_node_in_group = shader_input.links[0].from_node
                    if next_node_in_group not in visited_nodes:
                        visited_nodes.add(next_node_in_group)
                        q.append((next_node_in_group, current_node))

        # --- Iteration Case 2: Traverse to the previous node in the chain ---
        next_input_to_follow = next((inp for inp in current_node.inputs if inp.type == 'SHADER' and inp.is_linked), None)
        if next_input_to_follow:
            previous_node = next_input_to_follow.links[0].from_node
            if previous_node not in visited_nodes:
                visited_nodes.add(previous_node)
                # The parent_group context carries over to the previous node.
                q.append((previous_node, parent_group))
                
    # If the queue empties, no mix shader was found in the path.
    return None

def _get_socket_to_bake(node_tree, target_socket_name):
    """
    [DEFINITIVE V4 - ITERATIVE] Finds a target socket by iteratively
    traversing the shader graph backwards from the material output. This version
    is immune to stack overflows from deep node graphs and is fully aware of
    nested node groups.
    """
    log(f" > Starting robust ITERATIVE search for socket '{target_socket_name}'...")

    output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
    if not output_node:
        # Fallback to any material output if the active one isn't found
        output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL'), None)
        if not output_node:
            log("   - ERROR: Could not find any Material Output node.")
            return None

    if not output_node.inputs['Surface'].is_linked:
        # As a final fallback for some channels, check the displacement socket directly
        if target_socket_name == 'Displacement' and 'Displacement' in output_node.inputs:
             log(" > Surface is unlinked. Checking direct Displacement output as a fallback.")
             return output_node.inputs['Displacement']
        log("   - ERROR: Material Output node's Surface is not connected.")
        return None

    # --- Iterative Search Setup ---
    # The deque will store tuples of (node_to_visit, node_tree_it_belongs_to)
    q = deque()
    # The visited set will store tuples of (node.name, node_tree.name) to prevent reprocessing
    visited = set()

    # Start the search from the node connected to the material output
    start_node = output_node.inputs['Surface'].links[0].from_node
    q.append(start_node)
    visited.add((start_node.name, node_tree.name))
    log(f"   - Starting search from node: '{start_node.name}'")

    while q:
        current_node = q.popleft()

        # --- Base Case 1: Success ---
        # The target socket is a direct input on the current node.
        if target_socket_name in current_node.inputs:
            log(f"      - SUCCESS: Found target socket '{target_socket_name}' on node '{current_node.name}'.")
            return current_node.inputs[target_socket_name]

        # --- Iteration Case 1: The current node is a Group. Dive into it. ---
        if current_node.type == 'GROUP' and current_node.node_tree:
            log(f"      - Traversing into Group Node: '{current_node.name}'")
            group_tree = current_node.node_tree
            # Find the group's own output node to trace backwards from.
            group_output_node = next((n for n in group_tree.nodes if n.type == 'GROUP_OUTPUT'), None)
            
            if group_output_node:
                # Find the shader input on the group's output node, as that's the "end" of the internal graph.
                shader_input = next((s for s in group_output_node.inputs if s.type == 'SHADER' and s.is_linked), None)
                if shader_input:
                    # The next node to check is the one connected to the group's internal output.
                    internal_node_to_visit = shader_input.links[0].from_node
                    if (internal_node_to_visit.name, group_tree.name) not in visited:
                        q.append(internal_node_to_visit)
                        visited.add((internal_node_to_visit.name, group_tree.name))
                        log(f"        - Queued internal node for visit: '{internal_node_to_visit.name}'")

        # --- Iteration Case 2: Traverse backwards through any shader input. ---
        # This handles Mix Shaders, Add Shaders, etc.
        for shader_input in (inp for inp in current_node.inputs if inp.type == 'SHADER' and inp.is_linked):
            previous_node = shader_input.links[0].from_node
            if (previous_node.name, node_tree.name) not in visited:
                log(f"      - Traversing from '{current_node.name}' backwards to '{previous_node.name}'...")
                q.append(previous_node)
                visited.add((previous_node.name, node_tree.name))

    # --- Base Case 2: Failure ---
    # If the queue becomes empty, we've explored all paths.
    # Check the direct Displacement socket as a final fallback.
    if target_socket_name == 'Displacement' and 'Displacement' in output_node.inputs:
         log(" > Search failed for shader path, but found a direct connection to Material Output Displacement.")
         return output_node.inputs['Displacement']
         
    log(f" > FINAL WARNING: Iterative search could not find a source for '{target_socket_name}'.")
    return None

def _setup_bake_environment(task, obj, original_mat):
    """
    [V2] Sets up the bake environment. The 'original_mat' is now guaranteed to be the
    exact datablock from the object's material slot.
    """
    scene = bpy.context.scene
    render_settings = scene.render
    bake_settings = render_settings.bake
    image_settings = render_settings.image_settings

    original_settings = {
        'format': image_settings.file_format,
        'color_depth': image_settings.color_depth,
        'compression': image_settings.compression,
        'film_transparent': render_settings.film_transparent,
        'original_mat': original_mat,
        'original_mat_slot_index': -1,
    }

    with COPY_BAKE_GLOBAL_LOCK:
        mat_for_bake = original_mat.copy()

    nt = mat_for_bake.node_tree
    if not nt:
        raise RuntimeError("Material copy failed.")

    # --- START OF THE FIX ---
    # The 'original_mat' passed to this function is now the exact datablock from the
    # object's slot. We can use a direct reference comparison to find its index.
    original_mat_slot_index = -1
    for i, slot in enumerate(obj.material_slots):
        if slot.material == original_mat:
            slot.material = mat_for_bake
            original_mat_slot_index = i
            break
    # --- END OF THE FIX ---

    if original_mat_slot_index == -1:
        # This error should now be virtually impossible to hit, but is kept as a safeguard.
        raise RuntimeError("Could not find original material on object (logic error).")
    original_settings['original_mat_slot_index'] = original_mat_slot_index

    img = bpy.data.images.new(
        name=f"BakeTarget_{task['material_uuid']}",
        width=task['resolution_x'], height=task['resolution_y'], alpha=True
    )
    img.filepath_raw = task['output_path']
    image_settings.file_format = 'PNG'
    is_high_precision = task['bake_type'] == 'NORMAL' or task['target_socket_name'] == 'Displacement'
    image_settings.color_depth = '16' if is_high_precision else '8'
    image_settings.compression = 0 if is_high_precision else 15

    if not task.get('is_color_data', False):
        img.colorspace_settings.name = 'Non-Color'
    else:
        img.colorspace_settings.name = 'sRGB'

    tex_node = nt.nodes.new('ShaderNodeTexImage')
    tex_node.image = img
    nt.nodes.active, tex_node.select = tex_node, True

    return {
        "scene": scene,
        "mat_for_bake": mat_for_bake,
        "nt": nt,
        "img": img,
        "tex_node": tex_node,
        "original_settings": original_settings,
    }
    
def _bake_base_albedo_pass(setup_data, task, final_mix_shader_original, active_output_node, main_shader_link_from, group_node_instance):
    """
    [MODIFIED] Performs Pass 1. If the task is a simple decal composite,
    it copies the original texture. Otherwise, it bakes the base albedo.
    """
    nt = setup_data['nt']
    img = setup_data['img']
    render_settings = setup_data['scene'].render
    obj = bpy.data.objects.get(task['object_name'])

    # --- START OF THE FIX ---
    # This task is a decal composite, but the underlying albedo is a simple texture.
    # Instead of baking, we just copy the original texture's pixel data.
    if task.get("is_simple_decal_composite"):
        log("   - Pass 1: Copying original base albedo from source texture (simple material).")
        original_path = task.get("original_base_color_path")
        if original_path and os.path.exists(original_path):
            try:
                # Load the source image, resize if necessary, and copy its pixels
                source_img = bpy.data.images.load(original_path)
                if source_img.size[0] != img.size[0] or source_img.size[1] != img.size[1]:
                    source_img.scale(img.size[0], img.size[1])
                img.pixels = source_img.pixels[:]
                bpy.data.images.remove(source_img)
                log("     - Successfully copied pixels from: %s", os.path.basename(original_path))
            except Exception as e:
                log("    - Pass 1 ERROR: Could not load or copy original base color from '%s': %e. Result will be black.", original_path, e)
                img.pixels = [0.0] * len(img.pixels) # Fill with black on failure
        else:
            log("    - Pass 1 WARNING: Original base color path was not provided or not found. Result will be black.")
            img.pixels = [0.0] * len(img.pixels)
        return # Skip the rest of the baking logic for this pass
    # --- END OF THE FIX ---

    log("   - Pass 1: Baking Base Albedo (Opaque) using EMIT to: %s", os.path.basename(task['output_path']))
    base_shader_input = final_mix_shader_original.inputs[1]
    pass1_cleanup = {'link': None, 'group_instance': None, 'original_tree': None, 'temp_tree': None, 'emission_node': None}
    
    try:
        if active_output_node.inputs['Surface'].is_linked:
            nt.links.remove(active_output_node.inputs['Surface'].links[0])
        
        if base_shader_input.is_linked:
            base_shader_socket = base_shader_input.links[0].from_socket
            
            if group_node_instance:
                original_tree = group_node_instance.node_tree
                temp_tree = original_tree.copy()
                group_node_instance.node_tree = temp_tree
                pass1_cleanup.update({'group_instance': group_node_instance, 'original_tree': original_tree, 'temp_tree': temp_tree})
                base_node_in_copy = temp_tree.nodes.get(base_shader_socket.node.name)
                base_socket_in_copy = base_node_in_copy.outputs[base_shader_socket.name]
                group_output = next(n for n in temp_tree.nodes if n.type == 'GROUP_OUTPUT')
                shader_output = next(s for s in group_output.inputs if s.type == 'SHADER')
                for link in list(shader_output.links):
                    temp_tree.links.remove(link)
                temp_tree.links.new(base_socket_in_copy, shader_output)
                nt.links.new(main_shader_link_from, active_output_node.inputs['Surface'])
            else:
                nt.links.new(base_shader_socket, active_output_node.inputs['Surface'])
            
            socket_to_bake = _get_socket_to_bake(nt, "Base Color")

            if socket_to_bake:
                emission_node = nt.nodes.new('ShaderNodeEmission')
                pass1_cleanup['emission_node'] = emission_node

                if active_output_node.inputs['Surface'].is_linked:
                    nt.links.remove(active_output_node.inputs['Surface'].links[0])

                if socket_to_bake.is_linked:
                    nt.links.new(socket_to_bake.links[0].from_socket, emission_node.inputs['Color'])
                else:
                    emission_node.inputs['Color'].default_value = socket_to_bake.default_value
                
                pass1_cleanup['link'] = nt.links.new(emission_node.outputs['Emission'], active_output_node.inputs['Surface'])
                
                render_settings.film_transparent = False
                
                bpy.ops.object.select_all(action='DESELECT')
                obj.select_set(True)
                bpy.context.view_layer.objects.active = obj
                bpy.ops.object.bake(type='EMIT', use_clear=True, margin=16)
            else:
                log("    - Pass 1 WARNING: Could not find 'Base Color' socket. Bake for this pass will be black.")
                img.pixels = [0.0] * len(img.pixels)
    finally:
        if pass1_cleanup.get('link'): nt.links.remove(pass1_cleanup['link'])
        if pass1_cleanup.get('emission_node') and pass1_cleanup['emission_node'].name in nt.nodes: nt.nodes.remove(pass1_cleanup['emission_node'])
        if pass1_cleanup.get('group_instance'): pass1_cleanup['group_instance'].node_tree = pass1_cleanup['original_tree']
        if pass1_cleanup.get('temp_tree'): bpy.data.node_groups.remove(pass1_cleanup['temp_tree'])

def _flip_uvs_horizontally(obj):
    """
    Directly manipulates the UV data of an object to flip it horizontally.
    This is more robust than using bpy.ops.
    """
    if not obj or obj.type != 'MESH':
        log(" > WARNING: Cannot flip UVs, object is not a mesh.")
        return

    mesh = obj.data
    if not mesh.uv_layers:
        log(" > WARNING: Cannot flip UVs, no UV layers found on the object.")
        return

    # Use the active UV layer for rendering
    uv_layer = mesh.uv_layers.active
    if not uv_layer:
        log(" > WARNING: No active UV layer to flip.")
        return

    log("   - Flipping UVs horizontally via direct data access...")
    for uv_data in uv_layer.data:
        # Flip the U coordinate (the first component of the uv vector)
        uv_data.uv[0] = 1.0 - uv_data.uv[0]
    log("   - UV flip complete.")


def _bake_decal_albedo_pass(setup_data, task, decal_albedo_path, final_mix_shader_original, active_output_node, main_shader_link_from, group_node_instance):
    """Performs Pass 2 of the 3-pass bake: Decal Albedo."""
    log("   - Pass 2: Baking Decal Albedo (Transparent) to: %s", os.path.basename(decal_albedo_path))
    nt = setup_data['nt']
    tex_node = setup_data['tex_node']
    render_settings = setup_data['scene'].render
    obj = bpy.data.objects.get(task['object_name'])

    decal_shader_input = final_mix_shader_original.inputs[2]
    decal_albedo_img = bpy.data.images.new(name="DecalAlbedo", width=task['resolution_x'], height=task['resolution_y'], alpha=True)
    decal_albedo_img.filepath_raw = decal_albedo_path
    tex_node.image = decal_albedo_img
    pass2_cleanup = {'link': None, 'group_instance': None, 'original_tree': None, 'temp_tree': None}

    try:
        # Flip UVs horizontally using the robust method
        _flip_uvs_horizontally(obj)

        if decal_shader_input.is_linked:
            decal_shader_socket = decal_shader_input.links[0].from_socket
            if group_node_instance:
                original_tree = group_node_instance.node_tree
                temp_tree = original_tree.copy()
                group_node_instance.node_tree = temp_tree
                pass2_cleanup.update({'group_instance': group_node_instance, 'original_tree': original_tree, 'temp_tree': temp_tree})
                decal_node_in_copy = temp_tree.nodes.get(decal_shader_socket.node.name)
                decal_socket_in_copy = decal_node_in_copy.outputs[decal_shader_socket.name]
                group_output = next(n for n in temp_tree.nodes if n.type == 'GROUP_OUTPUT')
                shader_output = next(s for s in group_output.inputs if s.type == 'SHADER')
                for link in list(shader_output.links):
                    temp_tree.links.remove(link)
                temp_tree.links.new(decal_socket_in_copy, shader_output)
                nt.links.new(main_shader_link_from, active_output_node.inputs['Surface'])
            else:
                nt.links.new(decal_shader_socket, active_output_node.inputs['Surface'])
            pass2_cleanup['link'] = active_output_node.inputs['Surface'].links[0]

            render_settings.film_transparent = True
            
            # --- FIX: Select and activate the object before baking ---
            bpy.ops.object.select_all(action='DESELECT')
            obj.select_set(True)
            bpy.context.view_layer.objects.active = obj
            bpy.ops.object.bake(type='DIFFUSE', use_clear=True, margin=16)
            # --- END OF FIX ---
    finally:
        # Flip UVs back to their original state
        _flip_uvs_horizontally(obj)

        if pass2_cleanup['link']: nt.links.remove(pass2_cleanup['link'])
        if pass2_cleanup['group_instance']: pass2_cleanup['group_instance'].node_tree = pass2_cleanup['original_tree']
        if pass2_cleanup['temp_tree']: bpy.data.node_groups.remove(pass2_cleanup['temp_tree'])

    return decal_albedo_img

def _bake_decal_alpha_mask_pass(setup_data, task, decal_alpha_mask_path, final_mix_shader_original, active_output_node, main_shader_link_from, group_node_instance):
    """Performs Pass 3 of the 3-pass bake: Decal Alpha Mask."""
    log("   - Pass 3: Baking Decal Alpha Mask to: %s", os.path.basename(decal_alpha_mask_path))
    nt = setup_data['nt']
    tex_node = setup_data['tex_node']
    render_settings = setup_data['scene'].render

    fac_socket = final_mix_shader_original.inputs['Fac']
    decal_alpha_img = bpy.data.images.new(name="DecalAlpha", width=task['resolution_x'], height=task['resolution_y'], alpha=False)
    decal_alpha_img.filepath_raw = decal_alpha_mask_path
    decal_alpha_img.colorspace_settings.name = 'Non-Color'
    tex_node.image = decal_alpha_img
    pass3_cleanup = {'link': None, 'emission_node_name': None, 'group_instance': None, 'original_tree': None, 'temp_tree': None}

    try:
        if fac_socket.is_linked:
            fac_source_socket = fac_socket.links[0].from_socket
            local_nt = nt
            source_socket_to_use = fac_source_socket
            if group_node_instance:
                original_tree = group_node_instance.node_tree
                temp_tree = original_tree.copy()
                group_node_instance.node_tree = temp_tree
                local_nt = temp_tree
                pass3_cleanup.update({'group_instance': group_node_instance, 'original_tree': original_tree, 'temp_tree': temp_tree})
                node_in_copy = local_nt.nodes.get(fac_source_socket.node.name)
                source_socket_to_use = node_in_copy.outputs[fac_source_socket.name]

            emission_node = local_nt.nodes.new('ShaderNodeEmission')
            pass3_cleanup['emission_node_name'] = emission_node.name
            local_nt.links.new(source_socket_to_use, emission_node.inputs['Color'])
            
            if group_node_instance:
                group_output = next(n for n in local_nt.nodes if n.type == 'GROUP_OUTPUT')
                shader_output = next(s for s in group_output.inputs if s.type == 'SHADER')
                for link in list(shader_output.links):
                    local_nt.links.remove(link)
                local_nt.links.new(emission_node.outputs['Emission'], shader_output)
                nt.links.new(main_shader_link_from, active_output_node.inputs['Surface'])
            else:
                nt.links.new(emission_node.outputs['Emission'], active_output_node.inputs['Surface'])
            pass3_cleanup['link'] = active_output_node.inputs['Surface'].links[0]
            
            render_settings.film_transparent = True
            
            # --- FIX: Select and activate the object before baking ---
            obj = bpy.data.objects.get(task['object_name'])
            bpy.ops.object.select_all(action='DESELECT')
            obj.select_set(True)
            bpy.context.view_layer.objects.active = obj
            bpy.ops.object.bake(type='EMIT', use_clear=True, margin=16)
            # --- END OF FIX ---
    finally:
        if pass3_cleanup['link']: nt.links.remove(pass3_cleanup['link'])
        if pass3_cleanup['group_instance']: pass3_cleanup['group_instance'].node_tree = pass3_cleanup['original_tree']
        if pass3_cleanup['temp_tree']: bpy.data.node_groups.remove(pass3_cleanup['temp_tree'])
        elif pass3_cleanup['emission_node_name']:
            node_to_remove = nt.nodes.get(pass3_cleanup['emission_node_name'])
            if node_to_remove: nt.nodes.remove(node_to_remove)

    return decal_alpha_img

def _composite_decal_bakes(img, decal_albedo_img, decal_alpha_img):
    """Composites the baked decal layers into the final albedo."""
    try:
        log("   - Compositing decal over base albedo with corrected alpha...")

        # Manually flip the decal albedo image horizontally.
        log("     - Flipping decal albedo bake horizontally...")
        width, height = decal_albedo_img.size
        pixels = list(decal_albedo_img.pixels)
        flipped_pixels = [0.0] * len(pixels)
        components = 4 # RGBA

        for y in range(height):
            for x in range(width):
                source_idx = (y * width + x) * components
                dest_idx = (y * width + (width - 1 - x)) * components
                flipped_pixels[dest_idx:dest_idx + components] = pixels[source_idx:source_idx + components]

        decal_albedo_img.pixels[:] = flipped_pixels
        log("     - Flip complete.")

        # Ensure pixel caches are up-to-date before proceeding
        img.pixels[0]
        decal_albedo_img.pixels[0]
        decal_alpha_img.pixels[0]

        total_pixels = width * height
        
        base_pixels = list(img.pixels)
        decal_pixels = list(decal_albedo_img.pixels)
        alpha_mask_pixels = list(decal_alpha_img.pixels) 
        
        final_decal_pixels = list(decal_pixels)

        for i in range(total_pixels):
            rgba_idx = i * 4
            mask_idx = i * 4 
            final_alpha = alpha_mask_pixels[mask_idx]

            for c in range(3):
                base_val = base_pixels[rgba_idx + c]
                decal_val = decal_pixels[rgba_idx + c]
                base_pixels[rgba_idx + c] = base_val * (1.0 - final_alpha) + decal_val * final_alpha
            
            base_pixels[rgba_idx + 3] = 1.0
            final_decal_pixels[rgba_idx + 3] = final_alpha

        log("     - Saving final composite albedo: %s", os.path.basename(img.filepath_raw))
        img.pixels[:] = base_pixels
        img.save()
        
        log("     - Saving decal albedo with correct alpha: %s", os.path.basename(decal_albedo_img.filepath_raw))
        decal_albedo_img.pixels[:] = final_decal_pixels
        decal_albedo_img.save()
        
        log("     - Saving decal alpha mask: %s", os.path.basename(decal_alpha_img.filepath_raw))
        decal_alpha_img.save()
        
        log("   - Compositing complete.")
    except Exception as e:
        log(f"!!! ERROR during corrected compositing: {e}")
        log(traceback.format_exc())
        img.save()
        decal_albedo_img.save()
        decal_alpha_img.save()

def _perform_simple_bake(setup_data, task, active_output_node):
    """
    [CORRECTED - V5 NORMAL MAP FIX] Performs a simple, single-pass bake. This version
    now forces the bake type to 'NORMAL' when the target socket is 'Normal', ensuring
    correct vector data is generated. It also retains the previous fix for handling
    vector-to-float default value assignments.
    """
    nt = setup_data['nt']
    img = setup_data['img']
    obj = bpy.data.objects.get(task['object_name'])
    
    # --- START OF THE FIX ---
    # Determine the correct bake type. If the task is for a Normal map,
    # we MUST override any other setting and use the native 'NORMAL' bake type.
    bake_type = 'NORMAL' if task['target_socket_name'] == 'Normal' else task['bake_type']
    # --- END OF THE FIX ---

    bpy.context.scene.render.engine = 'CYCLES'

    if bake_type in ['EMIT', 'DISPLACEMENT']:
        log(f" > Performing EMIT bake for socket '{task['target_socket_name']}'...")
        
        socket_to_bake = _get_socket_to_bake(nt, task['target_socket_name'])

        if not socket_to_bake:
            log(f" > SIMPLE BAKE WARNING: Could not find socket '{task['target_socket_name']}'. Skipping.")
            return

        original_from_socket = None
        original_to_socket = None
        if active_output_node and active_output_node.inputs['Surface'].is_linked:
            link = active_output_node.inputs['Surface'].links[0]
            original_from_socket, original_to_socket = link.from_socket, link.to_socket
            nt.links.remove(link)

        emission_node = nt.nodes.new('ShaderNodeEmission')
        try:
            if socket_to_bake.is_linked:
                input_socket_name = 'Strength' if task.get('is_value_bake') else 'Color'
                nt.links.new(socket_to_bake.links[0].from_socket, emission_node.inputs[input_socket_name])
            else:
                input_socket = emission_node.inputs['Strength' if task.get('is_value_bake') else 'Color']
                
                is_source_array = hasattr(socket_to_bake.default_value, '__len__')
                is_dest_array = hasattr(input_socket.default_value, '__len__')

                if is_source_array and not is_dest_array:
                    avg_val = sum(socket_to_bake.default_value[:3]) / 3.0
                    input_socket.default_value = avg_val
                else:
                    input_socket.default_value = socket_to_bake.default_value

            if active_output_node:
                nt.links.new(emission_node.outputs['Emission'], active_output_node.inputs['Surface'])
            
            bpy.ops.object.select_all(action='DESELECT')
            obj.select_set(True)
            bpy.context.view_layer.objects.active = obj
            
            bpy.ops.object.bake(type='EMIT', use_clear=True, margin=16)
            img.save()

        finally:
            if emission_node.name in nt.nodes:
                nt.nodes.remove(emission_node)
            if original_from_socket and original_to_socket:
                if original_from_socket.node.name in nt.nodes and original_to_socket.node.name in nt.nodes:
                    nt.links.new(original_from_socket, original_to_socket)
    else:
        # This 'else' block now correctly handles the 'NORMAL' bake type, as well as any other native types.
        log(f" > Performing NATIVE bake for type '{bake_type}'...")
        bpy.ops.object.select_all(action='DESELECT')
        obj.select_set(True)
        bpy.context.view_layer.objects.active = obj
        bpy.ops.object.bake(type=bake_type, use_clear=True, margin=16)
        img.save()
        
def perform_single_bake_operation(obj, original_mat, task):
    """
    Orchestrates the entire bake operation for a single task,
    choosing between a 3-pass decal bake or a simple bake.
    """
    setup_data = None
    decal_albedo_img = None
    decal_alpha_img = None

    try:
        setup_data = _setup_bake_environment(task, obj, original_mat)
        nt = setup_data['nt']

        target_socket_name = task['target_socket_name']
        bsdf_node, active_output_node = _find_bsdf_and_output_nodes(nt)
        
        found_decal_info = None
        if bsdf_node and active_output_node and active_output_node.inputs['Surface'].is_linked:
            start_node = active_output_node.inputs['Surface'].links[0].from_node
            # Assuming _find_universal_decal_mixer is defined elsewhere as requested
            found_decal_info = _find_universal_decal_mixer(start_node, bsdf_node, set())
        
        if target_socket_name == "Base Color" and found_decal_info:
            log(" > Complex decal setup detected. Initiating 3-Pass Bake.")
            base, ext = os.path.splitext(task['output_path'])
            decal_albedo_path = f"{base}_decal{ext}"
            decal_alpha_mask_path = f"{base}_decal_alpha{ext}"

            final_mix_shader_original, group_node_instance = found_decal_info
            
            main_shader_link_from, main_shader_link_to = None, None
            if active_output_node.inputs['Surface'].is_linked:
                main_link = active_output_node.inputs['Surface'].links[0]
                main_shader_link_from = main_link.from_socket
                main_shader_link_to = main_link.to_socket
            else:
                raise RuntimeError("Material Output has no input link for bake.")

            # --- Execute 3-Pass Bake ---
            _bake_base_albedo_pass(setup_data, task, final_mix_shader_original, active_output_node, main_shader_link_from, group_node_instance)
            decal_albedo_img = _bake_decal_albedo_pass(setup_data, task, decal_albedo_path, final_mix_shader_original, active_output_node, main_shader_link_from, group_node_instance)
            decal_alpha_img = _bake_decal_alpha_mask_pass(setup_data, task, decal_alpha_mask_path, final_mix_shader_original, active_output_node, main_shader_link_from, group_node_instance)

            # --- Restore original main shader link ---
            if main_shader_link_from and main_shader_link_to:
                # Ensure no other link is present before creating the new one
                if active_output_node.inputs['Surface'].is_linked:
                    nt.links.remove(active_output_node.inputs['Surface'].links[0])
                nt.links.new(main_shader_link_from, main_shader_link_to)
            
            _composite_decal_bakes(setup_data['img'], decal_albedo_img, decal_alpha_img)

        else:
            _perform_simple_bake(setup_data, task, active_output_node)

        log(" > Bake successful.")

    except Exception as e:
        log(f"!!! BAKE TASK FAILED for '{obj.name}' during operation !!!")
        log(traceback.format_exc())
        raise e
    finally:
        # --- Cleanup ---
        if setup_data:
            render_settings = setup_data['scene'].render
            image_settings = setup_data['scene'].render.image_settings
            original_settings = setup_data['original_settings']
            
            image_settings.file_format = original_settings['format']
            image_settings.color_depth = original_settings['color_depth']
            image_settings.compression = original_settings['compression']
            render_settings.film_transparent = original_settings['film_transparent']

            if obj and original_settings['original_mat_slot_index'] != -1:
                try:
                    obj.material_slots[original_settings['original_mat_slot_index']].material = original_settings['original_mat']
                except Exception:
                    pass
            
            if 'nt' in setup_data and 'tex_node' in setup_data and setup_data['nt'].nodes.get(setup_data['tex_node'].name):
                setup_data['nt'].nodes.remove(setup_data['nt'].nodes.get(setup_data['tex_node'].name))
            
            mat_to_clean = bpy.data.materials.get(setup_data['mat_for_bake'].name)
            if mat_to_clean:
                bpy.data.materials.remove(mat_to_clean, do_unlink=True)

            if setup_data.get('img') and setup_data['img'].name in bpy.data.images:
                bpy.data.images.remove(setup_data['img'])

        if decal_albedo_img and decal_albedo_img.name in bpy.data.images:
            bpy.data.images.remove(decal_albedo_img)
        if decal_alpha_img and decal_alpha_img.name in bpy.data.images:
            bpy.data.images.remove(decal_alpha_img)

def persistent_worker_loop():
    """
    [CORRECTED TASK COUNTING & ROBUST MATERIAL LOOKUP V2] Main loop for the worker.
    It now finds the material to bake by checking the object's actual material slots
    against the UUID/name from the task, ensuring the correct datablock is used.
    """
    
    def send_json_message(payload):
        payload['pid'] = worker_pid
        print(json.dumps(payload), flush=True)

    try:
        log("Persistent worker started. Initializing...")
        send_json_message({"status": "ready"})
        log("Worker is READY. Awaiting bake tasks...")

    except Exception as e:
        log(f"!!! FATAL: Could not initialize worker environment: {e}")
        send_json_message({"status": "error", "details": f"Initialization failed: {e}"})
        return

    # --- Main task processing loop ---
    while True:
        line = sys.stdin.readline()
        if not line:
            log("Input stream closed. Exiting.")
            break
            
        result_payload = {}
        success = False
        task = {}
        try:
            task = json.loads(line)
            if task.get("action") == "quit":
                log("Quit command received. Shutting down gracefully.")
                break 

            task_counter.set_current(task.get('global_task_number', 0))
            task_counter.set_total(task.get('total_tasks', 0))
            
            bpy.ops.wm.open_mainfile(filepath=task['task_blend_file'], load_ui=False)
            log("Loaded task-specific file: %s", os.path.basename(task.get('task_blend_file', '')))
            
            setup_render_engine()
            _apply_texture_translation_map(task)

            obj = bpy.data.objects.get(task['object_name'])
            # --- START OF THE FIX ---
            # Find the specific material datablock that is assigned to the object,
            # matching the identifiers from the task. This is more robust than a global search.
            mat_to_bake = None
            if obj:
                # First, try to find the material on the object by its unique ID.
                for slot in obj.material_slots:
                    if slot.material and slot.material.get("uuid") == task['material_uuid']:
                        mat_to_bake = slot.material
                        break
                
                # If not found by UUID (e.g., older data), fall back to matching by name.
                if not mat_to_bake:
                    for slot in obj.material_slots:
                        if slot.material and slot.material.name == task['material_name']:
                            mat_to_bake = slot.material
                            log(f" > WARNING: Could not find material by UUID on object. Fell back to name '{task['material_name']}'.")
                            break
            # --- END OF THE FIX ---
            
            if obj and mat_to_bake:
                perform_single_bake_operation(obj, mat_to_bake, task)
                success = True
            else:
                log("!!! ERROR: Could not find object '%s' or assigned material '%s' (UUID: %s) after loading file. Skipping.", 
                    task['object_name'], task['material_name'], task.get('material_uuid'))
                success = False

            result_payload = {
                "status": "success" if success else "failure",
                "details": f"Task for material {task.get('material_name')} on {task.get('object_name')}"
            }
        except json.JSONDecodeError:
            result_payload = {"status": "error", "details": f"invalid_json: {line}"}
        except Exception as e:
            log(f"!!! UNHANDLED WORKER ERROR during task loop: {e}")
            log(traceback.format_exc())
            result_payload = {"status": "error", "details": str(e)}

        send_json_message(result_payload)
        
        log("  > Cleaning up worker scene after task...")
        bpy.ops.wm.read_factory_settings(use_empty=True)

    log("Worker task processing complete. Exiting.")

if __name__ == "__main__":
    final_exit_code = 0
    try:
        # --- This new startup logic runs before anything else ---
        # 1. Create a parser to find our custom arguments.
        parser = argparse.ArgumentParser()
        parser.add_argument("--persistent", action="store_true")
        parser.add_argument("--lib-path", type=str, default=None)
        
        # 2. Parse only the known arguments that come after '--'.
        args, _ = parser.parse_known_args(sys.argv[sys.argv.index("--") + 1:])

        # 3. If a library path was passed, add it to the system path immediately.
        if args.lib_path and os.path.isdir(args.lib_path):
            if args.lib_path not in sys.path:
                sys.path.insert(0, args.lib_path)
        # --- End of new startup logic ---

        if args.persistent:
            persistent_worker_loop()
        else:
            # This logic would be for the old single-shot worker, which is now deprecated.
            # We can log an error or simply do nothing.
            log("ERROR: Worker was started without the --persistent flag. This mode is deprecated.")
            final_exit_code = 1
            
    except Exception:
        # Use the worker's own logger to report any catastrophic startup failure.
        log("!!! UNHANDLED WORKER STARTUP ERROR !!!")
        log(traceback.format_exc())
        final_exit_code = 1
        
    finally:
        log(f"Worker finished. Exiting with code: {final_exit_code}")
        sys.stdout.flush()
        sys.stderr.flush()
        sys.exit(final_exit_code)
