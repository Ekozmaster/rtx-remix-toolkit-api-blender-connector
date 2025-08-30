bl_info = { 
    "name": "Remix Asset Ingestion",
    "blender": (4, 2, 0),
    "category": "Helper",
    "version": (3, 5, 0), # Incremented version
    "author": "Frisser :) (Integrated Baking by Gemini)",
    "description": "Export mesh assets as OBJ, with parallel texture baking, ingest into Remix with versioning, and handle multiple textures.",
    "location": "View3D > Remix Ingestor",
    "warning": "",
    "wiki_url": "",
    "tracker_url": "",
    "support": "COMMUNITY",
}

import bpy
import requests
import os
import logging
import tempfile
import time
import shutil
import re
import threading
import logging
import bmesh
import collections
from pxr import Usd, Sdf
from bpy.props import BoolProperty, StringProperty, CollectionProperty, IntProperty, EnumProperty, FloatProperty, PointerProperty
from bpy.types import Operator, Panel, PropertyGroup, AddonPreferences
import bpy_extras.io_utils
import urllib.parse
import subprocess
from pathlib import Path
from mathutils import Vector, Matrix
import math
from threading import Lock
from datetime import datetime
from subprocess import Popen, PIPE
import json
import sys
import uuid
import textwrap
from queue import Queue, Empty
from collections import defaultdict
from bpy.path import abspath
import traceback
from collections import defaultdict, deque 
import atexit
import hashlib

# --- Globals & Configuration ---
log_file_path = ""
export_lock = False # Use a simple boolean lock
remix_import_lock = False # Use a simple boolean lock
conversion_count = 0
is_applying_preset = False
PSUTIL_INSTALLED = False
PILLOW_INSTALLED = False
ACTIVE_WORKER_PROCESSES = []
TEMP_FILES_FOR_ATEXIT_CLEANUP = []
TEMP_DIR_PREFIX = "remix_ingestor_temp_"
# --- NEW: Material Caching Globals ---
global_material_hash_cache = {}
global_image_hash_cache = {}
# Define the custom paths here to be used by all functions
CUSTOM_COLLECT_PATH = os.path.join(tempfile.gettempdir(), "remix_collect")
CUSTOM_FINALIZE_PATH = os.path.join(tempfile.gettempdir(), "remix_finalize")

# Baking Worker Configuration
BAKE_WORKER_PY = None 
#MAX_CONCURRENT_BAKE_WORKERS = max(1, os.cpu_count() // 2)
MAX_CONCURRENT_BAKE_WORKERS = 4
BAKE_BATCH_SIZE_PER_WORKER = 5

def get_sentinel_path():
    """
    Returns the path to a 'restart.required' sentinel file inside the addon's root directory.
    This provides a persistent, file-based flag for managing the post-installation restart message.
    """
    try:
        addon_root_dir = os.path.dirname(os.path.realpath(__file__))
        return os.path.join(addon_root_dir, "restart.required")
    except NameError:
        # Fallback for edge cases.
        addon_folder_name = __name__.split('.')[0]
        scripts_path = bpy.utils.user_resource('SCRIPTS')
        return os.path.join(scripts_path, 'addons', addon_folder_name, "restart.required")

def get_persistent_lib_path():
    """
    [NEW FUNCTION FOR PERSISTENCE] Returns a path to a shared library folder
    outside the addon's directory to survive updates and Blender version changes.
    Path is typically .../scripts/remix_ingestor_libs/
    """
    # Get the user's main scripts directory, which is stable across versions.
    try:
        scripts_path = bpy.utils.user_resource('SCRIPTS')
    except (AttributeError, RuntimeError):
        # Fallback for headless or unusual contexts
        home = os.path.expanduser("~")
        scripts_path = os.path.join(home, ".blender_remix_ingestor_libs")

    # Define our unique, persistent library folder name.
    persistent_lib_dir = os.path.join(scripts_path, "remix_ingestor_libs")
    
    # Ensure this directory exists every time we check.
    try:
        os.makedirs(persistent_lib_dir, exist_ok=True)
    except Exception as e:
        # If creation fails, we cannot proceed.
        logging.critical(f"CRITICAL: Could not create persistent library directory at '{persistent_lib_dir}'. Dependency installation will fail. Error: {e}")
        return None # Return None to indicate failure

    return persistent_lib_dir

def check_dependencies():
    """
    (CORRECTED FOR PERSISTENCE) Checks if psutil and Pillow are installed.
    This version adds the addon's persistent 'remix_ingestor_libs' directory
    to the Python path, making the dependency check robust and portable.
    """
    # --- THIS IS THE FIX ---
    # Get the path to our addon's PERSISTENT library folder.
    lib_path = get_persistent_lib_path()

    # If the path is valid and not already in Python's list of search paths, add it.
    if lib_path and os.path.isdir(lib_path) and lib_path not in sys.path:
        sys.path.insert(0, lib_path) # Insert at the beginning to ensure it's checked first
        logging.info(f"Dynamically added persistent 'lib' directory to system path: {lib_path}")
    # --- END OF FIX ---

    global PSUTIL_INSTALLED, PILLOW_INSTALLED
    try:
        # Now, this import will search the newly added persistent path first.
        import psutil
        PSUTIL_INSTALLED = True
        logging.info("Dependency 'psutil' is installed.")
    except ImportError:
        PSUTIL_INSTALLED = False
        logging.warning("Dependency 'psutil' is NOT installed.")
    try:
        from PIL import Image
        PILLOW_INSTALLED = True
        logging.info("Dependency 'Pillow' is installed.")
    except ImportError:
        PILLOW_INSTALLED = False
        logging.warning("Dependency 'Pillow' is NOT installed.")

class REMIX_OT_install_dependency(Operator):
    """(CORRECTED V4 - Sentinel File) Installs a library into a local 'lib' folder and creates a persistent restart flag."""
    bl_idname = "remix.install_dependency"
    bl_label = "Install Dependency"
    bl_description = "Downloads and installs a required library. Blender may need to be restarted."
    bl_options = {'REGISTER', 'INTERNAL'}

    dependency: StringProperty(default="")
    _timer = None
    _thread = None
    _queue = None

    def _install_in_thread(self, py_exec, dependency_name, target_dir, queue_ref):
        try:
            # The target_dir is now the persistent one. We still ensure it exists.
            os.makedirs(target_dir, exist_ok=True)
            subprocess.run([py_exec, "-m", "ensurepip"], check=True, capture_output=True)
            subprocess.run([py_exec, "-m", "pip", "install", "--upgrade", "pip"], check=True, capture_output=True)
            result = subprocess.run(
                [py_exec, "-m", "pip", "install", f"--target={target_dir}", dependency_name],
                capture_output=True, text=True, check=True
            )
            logging.info(f"{dependency_name} installation successful:\n" + result.stdout)
            queue_ref.put(('INFO', f"{dependency_name} installed successfully!"))
        except subprocess.CalledProcessError as e:
            logging.error(f"Failed to install {dependency_name}. See System Console. Error:\n{e.stderr}")
            queue_ref.put(('ERROR', "Installation failed. Check System Console."))
        except FileNotFoundError:
            logging.error(f"Failed to install {dependency_name}: Python executable not found.")
            queue_ref.put(('ERROR', "Python executable not found."))
        finally:
            check_dependencies()
            queue_ref.put(('FINISHED', ''))

    def modal(self, context, event):
        if event.type != 'TIMER':
            return {'PASS_THROUGH'}

        is_finished = False
        try:
            while True:
                report_type, message = self._queue.get_nowait()
                if report_type == 'FINISHED':
                    is_finished = True
                else:
                    self.report({report_type}, message)
                    # --- THIS IS THE FIX ---
                    # If an install is successful, create the sentinel file.
                    if report_type == 'INFO':
                        sentinel_path = get_sentinel_path()
                        try:
                            with open(sentinel_path, 'w') as f:
                                f.write(datetime.now().isoformat())
                            logging.info(f"Created restart sentinel file at: {sentinel_path}")
                        except Exception as e:
                            logging.error(f"Could not create sentinel file: {e}")
                    # --- END OF FIX ---
        except Empty:
            pass

        if is_finished:
            context.scene.remix_is_installing_dependency = False
            context.window_manager.event_timer_remove(self._timer)
            context.workspace.status_text_set(None)
            for region in context.area.regions:
                if region.type == 'UI':
                    region.tag_redraw()
            return {'FINISHED'}
            
        return {'PASS_THROUGH'}

    def execute(self, context):
        if not self.dependency:
            self.report({'ERROR'}, "No dependency specified.")
            return {'CANCELLED'}
        
        context.scene.remix_is_installing_dependency = True
        self._queue = Queue()
        py_exec = sys.executable
        
        # --- MODIFIED TO USE PERSISTENT PATH ---
        # Install to the persistent directory, not the addon's local one.
        target_install_dir = get_persistent_lib_path()
        if not target_install_dir:
            self.report({'ERROR'}, "Could not determine a persistent library path. See console for details.")
            return {'CANCELLED'}
        # --- END OF MODIFICATION ---

        self._thread = threading.Thread(target=self._install_in_thread, args=(py_exec, self.dependency, target_install_dir, self._queue))
        self._thread.start()
        self._timer = context.window_manager.event_timer_add(0.2, window=context.window)
        context.window_manager.modal_handler_add(self)
        context.workspace.status_text_set(f"Installing {self.dependency} in the background...")
        return {'RUNNING_MODAL'}

def cleanup_orphan_directories():
    """
    [DEFINITIVE FIX V2] Scans and cleans ALL addon-related temporary directories on startup.
    - Wipes the entire bake cache ('remix_collect') to ensure a fresh start.
    - Intelligently removes only orphaned session folders ('remix_finalize') from crashed instances.
    """
    if not PSUTIL_INSTALLED:
        logging.warning("Orphan cleanup skipped: 'psutil' is not installed.")
        return

    import psutil
    # List of all base paths that the addon might create temp folders in.
    paths_to_scan = [CUSTOM_COLLECT_PATH, CUSTOM_FINALIZE_PATH]
    
    logging.info(f"Startup cleanup: Scanning custom paths...")

    for base_path in paths_to_scan:
        if not os.path.exists(base_path):
            continue

        # --- THIS IS THE CORRECTED LOGIC ---
        # If we are scanning the bake cache directory, wipe its contents completely.
        if os.path.normpath(base_path) == os.path.normpath(CUSTOM_COLLECT_PATH):
            logging.info(f"Wiping bake cache directory: {base_path}")
            try:
                for item_name in os.listdir(base_path):
                    item_path = os.path.join(base_path, item_name)
                    if os.path.isdir(item_path):
                        shutil.rmtree(item_path)
                    else:
                        os.remove(item_path)
            except Exception as e:
                logging.error(f"Failed to wipe bake cache directory '{base_path}': {e}")
            # Continue to the next path in paths_to_scan
            continue

        # For all other paths (i.e., remix_finalize), use the existing orphan-check logic.
        logging.info(f"Scanning for orphaned session directories in: {base_path}")
        try:
            for dirname in os.listdir(base_path):
                if dirname.startswith(TEMP_DIR_PREFIX):
                    orphan_path = os.path.join(base_path, dirname)
                    lock_file_path = os.path.join(orphan_path, 'blender.lock')

                    if not os.path.exists(lock_file_path):
                        logging.warning(f"Found temp dir '{orphan_path}' without a lock file. Deleting.")
                        try:
                            shutil.rmtree(orphan_path)
                        except Exception as e:
                            logging.error(f"Failed to delete orphaned dir '{orphan_path}': {e}")
                        continue

                    try:
                        with open(lock_file_path, 'r') as f:
                            pid = int(f.read().strip())

                        # Check if the process ID from the lock file is still running
                        if not psutil.pid_exists(pid):
                            logging.info(f"Found orphan directory from dead process (PID: {pid}). Deleting: {orphan_path}")
                            shutil.rmtree(orphan_path)
                        else:
                            logging.debug(f"Skipping temp directory '{orphan_path}' as it belongs to a running process (PID: {pid}).")

                    except (ValueError, FileNotFoundError) as e:
                        logging.error(f"Error processing lock file for '{orphan_path}'. Deleting directory. Reason: {e}")
                        try:
                            shutil.rmtree(orphan_path)
                        except Exception as e_del:
                            logging.error(f"Could not delete corrupted temp dir '{orphan_path}': {e_del}")
        except Exception as e:
            logging.error(f"An unexpected error occurred during orphan cleanup scan for '{base_path}': {e}")

class REMIX_OT_restart_blender(Operator):
    """Saves the file and restarts Blender."""
    bl_idname = "remix.restart_blender"
    bl_label = "Save and Restart Blender"
    bl_description = "Saves the current file and restarts Blender to apply changes"
    bl_options = {'REGISTER', 'INTERNAL'}

    def execute(self, context):
        try:
            # Get current Blender executable and file path
            blender_path = bpy.app.binary_path
            filepath = bpy.data.filepath

            if filepath:
                # Save the current file before restarting
                bpy.ops.wm.save_mainfile()
                subprocess.Popen([blender_path, filepath])
            else:
                # If the file is unsaved, just open a new instance
                subprocess.Popen([blender_path])

            # Quit the current instance
            bpy.ops.wm.quit_blender()

        except Exception as e:
            self.report({'ERROR'}, f"Could not restart Blender: {e}")
            logging.error(f"Failed to restart Blender: {e}", exc_info=True)

        return {'FINISHED'}

class RemixIngestorPreferences(AddonPreferences):
    bl_idname = __name__ # <--- THIS IS THE CORRECT LINE

    # --- Global Settings ---
    apply_modifiers: BoolProperty(
        name="Apply Modifiers",
        description="Apply modifiers before exporting OBJ files",
        default=True
    )
    
    # --- Server Settings ---
    remix_server_url: StringProperty(
        name="Server URL",
        description="URL of the Remix server (e.g., http://localhost:8011/stagecraft).",
        default="http://localhost:8011/stagecraft",
        subtype='NONE' # Use 'NONE' to avoid registration errors
    )
    remix_export_url: StringProperty(
        name="Export API URL",
        description="URL of the Export API (e.g., http://localhost:8011/ingestcraft/mass-validator/queue).",
        default="http://localhost:8011/ingestcraft/mass-validator/queue",
        subtype='NONE' # Use 'NONE' to avoid registration errors
    )
    remix_verify_ssl: BoolProperty(
        name="Verify SSL",
        description="Verify SSL certificates when connecting to the server",
        default=True
    )
    remix_ingest_directory: StringProperty(
        name="Ingest Directory",
        description="Directory on the server to ingest assets and textures (e.g., /ProjectFolder/Assets)",
        default="/ProjectFolder/Assets",
        subtype='DIR_PATH'
    )

    # --- Export Settings ---
    remix_use_selection_only: BoolProperty(
        name="Export Selected Objects Only",
        description="Export only selected objects",
        default=False
    )
    flip_faces_export: BoolProperty(
        name="Flip Normals During Export",
        description="When checked, normals will be flipped during export.",
        default=False
    )
    # --- NEW FUNCTION ---
    mirror_on_export: BoolProperty(
        name="Mirror on Export",
        description="Mirror objects along the X-axis during export",
        default=False
    )
    remix_use_custom_name: BoolProperty(
        name="Use Custom Name",
        description="Use a custom base name for exported OBJ files",
        default=False
    )
    remix_base_obj_name: StringProperty(
        name="Base OBJ Name",
        description="Base name for the exported OBJ files",
        default="exported_object"
    )
    remix_replace_stock_mesh: BoolProperty(
        name="Replace Stock Mesh",
        description="Replace the selected stock mesh in Remix",
        default=False
    )
    remix_bake_material_only: BoolProperty(
        name="Enable simplistic hashing to bake less.",
        description="Do not enable if you are using the same procedral material across different objects.",
        default=True
    )
    remix_export_scale: FloatProperty(
        name="Export Scale",
        description="Scale factor for exporting OBJ",
        default=1.0,
        min=-10000.0,
        max=10000.0
    )
    obj_export_forward_axis: EnumProperty(
        name="Forward Axis",
        description="Choose the forward axis for OBJ export",
        items=[('X','X',''),('NEGATIVE_X','-X',''),('Y','Y',''),('NEGATIVE_Y','-Y',''),('Z','Z',''),('NEGATIVE_Z','-Z','')],
        default='NEGATIVE_Z'
    )
    obj_export_up_axis: EnumProperty(
        name="Up Axis",
        description="Choose the up axis for OBJ export",
        items=[('X','X',''),('Y','Y',''),('NEGATIVE_X','-X',''),('NEGATIVE_Y','-Y',''),('Z','Z',''),('NEGATIVE_Z','-Z','')],
        default='Y'
    )

    # --- Import Settings ---
    flip_normals_import: BoolProperty(
        name="Flip Normals During Import",
        description="When checked, normals will be flipped during import.",
        default=False
    )
    mirror_import: BoolProperty(
        name="Mirror on Import",
        description="Mirror objects along the X-axis during import",
        default=False
    )
    remix_import_scale: FloatProperty(
        name="Import Scale",
        description="Scale factor for importing USD files",
        default=1.0,
        min=-10000.0,
        max=10000.0
    )
    remix_import_original_textures: BoolProperty(
        name="Import Original Textures",
        description="Attach original textures to imported USD meshes",
        default=False
    )
    usd_import_forward_axis: EnumProperty(
        name="USD Import Forward Axis",
        description="Choose the forward axis for USD import",
        items=[('X','X',''),('Y','Y',''),('Z','Z',''),('NEGATIVE_X','-X',''),('NEGATIVE_Y','-Y',''),('NEGATIVE_Z','-Z','')],
        default='Y'
    )
    usd_import_up_axis: EnumProperty(
        name="USD Up Axis",
        description="Choose the up axis for USD import",
        items=[('X','X',''),('Y','Y',''),('Z','Z',''),('-X','-X',''),('-Y','-Y',''),('-Z','-Z','')],
        default='Z',
    )
    
    # --- Other/UI Settings ---
    remix_preset: EnumProperty(
        name="Presets",
        description="Select preset configurations for export and import settings",
        items=[('CUSTOM', "Custom", ""), ('UNREAL_ENGINE', "Unreal Engine", "")],
        default='CUSTOM'
    )
    remix_show_info: BoolProperty(
        name="Show Information",
        description="Show additional information in the panel",
        default=False
    )
    bake_method: EnumProperty(
        name="Bake Method",
        description="Emit Hijack bakes metallic texutres correctly, and glass looks more like what you expected. Native is able to bake node setups that intercept the Principled BSDF and the Material Output but fails for metals and glass",
        items=[
            ('EMIT_HIJACK', "Legacy Emit Hijack (Recommended)", "Manually creates Emission shaders to bake any channel. Slower, but provides a universal fallback."),
            ('NATIVE', "Native PBR (Experimental)", "Uses Blender's built-in bake passes. Faster, but requires newer Blender versions for full support.")
        ],
        default='EMIT_HIJACK'
    )

    # --- Substance Painter Settings ---
    spp_exe: StringProperty(
        name="Substance Painter Executable Path",
        subtype='FILE_PATH',
        default="C:/Program Files/Adobe/Adobe Substance 3D Painter/Adobe Substance 3D Painter.exe"
    )
    export_folder: StringProperty(
        name="Object Export Folder Path",
        subtype='DIR_PATH',
        default=""
    )

    def draw(self, context):
        layout = self.layout
        layout.label(text="Global Preferences:")
        # You can add any settings you want to appear in the main Add-on Preferences window here.
        layout.prop(self, "apply_modifiers")
        layout.prop(self, "remix_server_url")
        layout.prop(self, "remix_export_url")
        layout.prop(self, "spp_exe")
        layout.prop(self, "export_folder")

class AssetNumberItem(PropertyGroup):
    blend_name: StringProperty(name="Blend File Name")
    asset_number: IntProperty(name="Asset Number", default=1)

class CustomSettingsBackup(PropertyGroup):
    obj_export_forward_axis: StringProperty()
    obj_export_up_axis: StringProperty()
    flip_faces_export: BoolProperty()
    mirror_import: BoolProperty()
    remix_export_scale: FloatProperty()
    remix_use_selection_only: BoolProperty()
    remix_ingest_directory: StringProperty()
    remix_verify_ssl: BoolProperty()
    remix_import_original_textures: BoolProperty()


def setup_logger():
    global log_file_path
    for handler in logging.root.handlers[:]:
        logging.root.removeHandler(handler)
    try:
        scripts_dir = bpy.utils.user_resource('SCRIPTS')
        logs_dir = os.path.join(scripts_dir, "logs")
        os.makedirs(logs_dir, exist_ok=True)
        log_file_path = os.path.join(logs_dir, "remix_asset_ingestor.log")

        logging.basicConfig(
            filename=log_file_path,
            filemode='a',
            format='%(asctime)s - %(levelname)s - %(message)s',
            level=logging.DEBUG
        )

        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.DEBUG)
        console_formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
        console_handler.setFormatter(console_formatter)
        logging.getLogger().addHandler(console_handler)

        logging.info("Remix Asset Ingestor addon registered.")
        print(f"Logging initialized. Log file at: {log_file_path}")
    except Exception as e:
        print(f"Failed to set up logging: {e}")


def is_blend_file_saved():
    return bool(bpy.data.filepath)

def _kill_all_active_workers():
    """
    [FIXED FOR FILE CLEANUP]
    This function is registered with atexit and runs when Blender closes.
    It ensures all orphan worker processes are terminated AND removes any
    temporary files that were registered in the global list, covering crashes.
    """
    # --- 1. Terminate Worker Processes ---
    if ACTIVE_WORKER_PROCESSES:
        logging.info(f"Blender is closing. Terminating {len(ACTIVE_WORKER_PROCESSES)} orphan worker process(es)...")
        for worker_proc in ACTIVE_WORKER_PROCESSES:
            if worker_proc and worker_proc.poll() is None:
                try:
                    logging.debug(f" > Killing orphan PID: {worker_proc.pid}")
                    worker_proc.kill()
                except Exception as e:
                    logging.error(f"Failed to kill orphan worker PID {worker_proc.pid}: {e}")
        ACTIVE_WORKER_PROCESSES.clear()

    # --- 2. Clean Up Registered Temporary Files ---
    if TEMP_FILES_FOR_ATEXIT_CLEANUP:
        logging.info(f"Performing atexit cleanup for {len(TEMP_FILES_FOR_ATEXIT_CLEANUP)} registered temp files/dirs...")
        for path_to_clean in TEMP_FILES_FOR_ATEXIT_CLEANUP:
            if not path_to_clean or not os.path.exists(path_to_clean):
                continue
            try:
                if os.path.isdir(path_to_clean):
                    shutil.rmtree(path_to_clean)
                    logging.debug(f" > atexit: Removed temp directory: {path_to_clean}")
                else:
                    os.remove(path_to_clean)
                    logging.debug(f" > atexit: Removed temp file: {path_to_clean}")
            except Exception as e:
                logging.error(f"atexit cleanup failed for '{path_to_clean}': {e}")
        TEMP_FILES_FOR_ATEXIT_CLEANUP.clear()

def _collect_relevant_node_groups(start_tree, relevant_groups_set, visited_groups_set):
    """
    Recursively traverses a node tree to find all used node groups, including nested ones,
    to avoid scanning unused, orphaned groups from the global bpy.data.node_groups list.
    """
    if not start_tree or start_tree in visited_groups_set:
        return

    visited_groups_set.add(start_tree)

    for node in start_tree.nodes:
        if node.type == 'GROUP' and node.node_tree:
            # Add the found group to our set of relevant groups
            relevant_groups_set.add(node.node_tree)
            # Recurse into the found group to find any nested groups
            _collect_relevant_node_groups(node.node_tree, relevant_groups_set, visited_groups_set)
      
def convert_exr_textures_to_png(context, objects_to_export):
    """
    [DEFINITIVE] Finds all EXR textures used in materials ON THE SPECIFIED OBJECTS
    and within their DEPENDENT NODE GROUPS. Converts them to PNG in-place, updates
    nodes, is BIT-DEPTH AWARE, and completely avoids scanning unused global data.
    """
    global conversion_count
    try:
        bpy.ops.file.unpack_all(method="USE_LOCAL")
        logging.info("Starting DEEPLY TARGETED conversion of EXR textures to PNG (Bit-Depth Aware).")
        
        # --- DEFINITIVE FIX ---
        # Step 1: Collect a unique set of materials ONLY from the objects being exported.
        materials_in_use = {
            slot.material for obj in objects_to_export 
            if hasattr(obj, 'material_slots') 
            for slot in obj.material_slots if slot.material
        }

        if not materials_in_use:
            logging.info("No materials found on the objects selected for export. Skipping EXR conversion.")
            return True, []

        logging.info(f"Scanning {len(materials_in_use)} materials and their dependencies for export selection.")

        # Step 2: Get the top-level node trees from the materials in use.
        material_node_trees = {mat.node_tree for mat in materials_in_use if mat.use_nodes and mat.node_tree}

        # Step 3: Use the new helper to recursively find all dependent node groups.
        relevant_node_groups = set()
        visited_groups = set()
        for tree in material_node_trees:
            _collect_relevant_node_groups(tree, relevant_node_groups, visited_groups)
        
        # Step 4: The final list to scan is the combination of the material trees and only their relevant groups.
        node_trees_to_scan = list(material_node_trees.union(relevant_node_groups))
        logging.info(f"Deep scan identified {len(node_trees_to_scan)} total relevant node trees to check.")
        # --- END OF DEFINITIVE FIX ---

        replaced_textures = []
        conversion_count = 0

        for node_tree in node_trees_to_scan:
            if not node_tree: continue
            success, textures = process_nodes_recursively(node_tree.nodes, node_tree, context)
            if not success:
                return False, []
            replaced_textures.extend(textures)

        logging.info(f"Deeply targeted scan complete. Converted {conversion_count} EXR textures to PNG.")
        return True, replaced_textures

    except Exception as e:
        logging.error(f"Error during deeply targeted EXR to PNG conversion: {e}", exc_info=True)
        return False, []

def process_nodes_recursively(nodes, node_tree, context): # <--- CONTEXT IS NOW A PARAMETER
    """
    Helper function to traverse a node tree, including groups, to find
    and convert EXR image nodes with bit-depth awareness.
    """
    global conversion_count
    replaced_textures = []

    # <--- MODIFICATION START: Safe handling of scene settings --->
    # Get the scene's image save settings
    scene_settings = context.scene.render.image_settings
    # Store the user's original settings so we can restore them
    original_color_depth = scene_settings.color_depth
    original_compression = scene_settings.compression
    # <--- MODIFICATION END --->

    try:
        for node in nodes:
            if node.type == 'GROUP' and node.node_tree:
                # Recurse into node groups, passing context along
                success, textures = process_nodes_recursively(node.node_tree.nodes, node.node_tree, context)
                if not success:
                    # If recursion fails, ensure we still restore settings before exiting
                    raise RuntimeError("Recursive processing failed.")
                replaced_textures.extend(textures)

            elif node.type == 'TEX_IMAGE' and node.image and node.image.source == 'FILE':
                # Check if the image is an EXR
                filepath = node.image.filepath_from_user()
                if not filepath or not filepath.lower().endswith('.exr'):
                    continue

                exr_path = bpy.path.abspath(filepath)
                if not os.path.exists(exr_path):
                    logging.warning(f"EXR file does not exist, skipping: {exr_path}")
                    continue

                # Create the new PNG path
                png_path = os.path.splitext(exr_path)[0] + ".png"
                logging.info(f"Converting '{os.path.basename(exr_path)}' -> '{os.path.basename(png_path)}'")
                
                image = node.image

                # <--- MODIFICATION START: Bit-Depth Aware Settings --->
                # An EXR with depth 64 is 16-bit half-float. Depth 128 is 32-bit full-float.
                # Anything >= 64 should be saved as a 16-bit PNG to preserve precision.
                if image.depth >= 64:
                    logging.info(f" > Source EXR is high bit-depth ({image.depth}-bit float). Saving as 16-BIT PNG with no compression.")
                    scene_settings.color_depth = '16'
                    scene_settings.compression = 0  # 0% compression for max quality on data maps
                else:
                    logging.info(f" > Source EXR is standard bit-depth. Saving as 8-BIT PNG.")
                    scene_settings.color_depth = '8'
                    scene_settings.compression = 15 # Default compression is fine for 8-bit

                # Perform the conversion
                new_image = bpy.data.images.new(
                    name=os.path.basename(png_path),
                    width=image.size[0],
                    height=image.size[1],
                    alpha=(image.channels == 4),
                    float_buffer=(image.depth >= 64) # Use float buffer for high-bit depth sources
                )
                new_image.pixels = image.pixels[:]
                new_image.file_format = 'PNG'
                new_image.filepath_raw = png_path
                new_image.save() # This now uses our temporary, bit-depth aware settings
                # <--- MODIFICATION END --->

                # Replace the node's image with the new PNG version
                node.image = new_image
                conversion_count += 1

                material_name = get_material_name_from_node_tree(node_tree)
                if material_name:
                    replaced_textures.append((material_name, exr_path, png_path))

        return True, replaced_textures
    except Exception as e:
        logging.error(f"Error during node processing: {e}", exc_info=True)
        return False, []
    finally:
        # <--- MODIFICATION START: Restore Original Settings --->
        # This block is GUARANTEED to run, even if an error occurs.
        # This prevents the addon from permanently changing the user's render settings.
        scene_settings.color_depth = original_color_depth
        scene_settings.compression = original_compression
        # <--- MODIFICATION END --->

def get_material_name_from_node_tree(node_tree):
    """Utility to find which material a node tree belongs to."""
    for mat in bpy.data.materials:
        if mat.node_tree == node_tree:
            return mat.name
    return None

def check_and_report_gpu_settings(context):
    """
    Checks Cycles preferences for available backends and device status.
    Returns a formatted string for display.
    """
    report_lines = ["--- GPU Compute Settings ---"]
    prefs = context.preferences
    cycles_prefs_addon = prefs.addons.get('cycles')

    if not cycles_prefs_addon:
        report_lines.append("Cycles render addon is not enabled.")
        return "\n".join(report_lines)

    cycles_prefs = cycles_prefs_addon.preferences
    
    # Get all possible backend APIs available in this Blender build
    # This function call IS correct and requires the context.
    available_backends = cycles_prefs.get_device_types(context)
    backend_names = [backend[1] for backend in available_backends]
    report_lines.append(f"Available Backends: {', '.join(backend_names) if backend_names else 'None'}")
    
    # Get the currently selected backend
    current_backend = cycles_prefs.compute_device_type
    report_lines.append(f"Active Backend: {current_backend}")
    report_lines.append("-" * 20)

    # Get devices for the active backend
    try:
        # THIS IS THE CORRECTED LINE: The 'context' argument has been removed.
        devices = cycles_prefs.get_devices_for_type(current_backend)
        
        if not devices:
            report_lines.append(f"No {current_backend} devices found.")
        else:
            report_lines.append(f"Detected {current_backend} Devices:")
            for device in devices:
                status = "ENABLED" if device.use else "DISABLED"
                device_info = f"  - {device.name} ({device.type}): {status}"
                report_lines.append(device_info)
    except Exception as e:
        report_lines.append(f"Could not query devices for {current_backend}: {e}")

    return "\n".join(report_lines)

class SYSTEM_OT_show_gpu_report(bpy.types.Operator):
    """Shows a popup with the GPU settings report."""
    bl_idname = "system.show_gpu_report"
    bl_label = "GPU Settings Report"
    bl_options = {'REGISTER', 'INTERNAL'}

    report_message: bpy.props.StringProperty(
        name="Report Message",
        description="The report message to display",
        default="No report generated."
    )

    def execute(self, context):
        return {'FINISHED'}

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self, width=450)

    def draw(self, context):
        layout = self.layout
        # Use a box for better visual separation
        box = layout.box()
        # Split the message into lines and draw each as a label
        for line in self.report_message.split('\n'):
            box.label(text=line)


class SYSTEM_OT_check_gpu_settings(bpy.types.Operator):
    """Checks GPU settings and displays them in a popup dialog."""
    bl_idname = "system.check_gpu_settings"
    bl_label = "Check GPU Settings"
    bl_description = "Check available and active GPU rendering devices for Cycles"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        # Generate the report string
        report = check_and_report_gpu_settings(context)
        
        # Log the full report to the system console for debugging
        print("\n" + report + "\n")

        # Call the popup operator to display the report to the user
        bpy.ops.system.show_gpu_report('INVOKE_DEFAULT', report_message=report)
        
        return {'FINISHED'}

    
def batch_flip_normals_optimized(meshes_to_flip, context):
    """
    [DEFINITIVE PERFORMANCE & STABILITY FIX] Flips normals for a list of mesh
    objects by iterating through each one and using the bmesh API directly.
    This avoids the progressive slowdown caused by Undo System and Scene Update
    overhead from repeated bpy.ops calls in a loop. This method provides

    consistent, reliable performance for any number of objects.
    """
    if not meshes_to_flip:
        return

    num_meshes = len(meshes_to_flip)
    logging.info(f"Batch flip normals (Direct API Mode): Preparing to flip {num_meshes} meshes.")
    start_time = time.time()

    # Store original state to restore it perfectly
    original_active = context.view_layer.objects.active
    original_selected = list(context.selected_objects)
    original_mode = 'OBJECT'
    if context.object and hasattr(context.object, 'mode'):
        original_mode = context.object.mode

    # A single mode_set at the beginning is safe and ensures correct state
    if context.mode != 'OBJECT':
        bpy.ops.object.mode_set(mode='OBJECT')

    processed_count = 0
    failed_objects = []
    try:
        # --- CORE LOGIC: Iterate and use the direct, fast bmesh API ---
        for i, obj in enumerate(meshes_to_flip):
            # Provide UI feedback to prevent the appearance of a freeze
            if i % 25 == 0: # Update status every 25 objects
                elapsed = time.time() - start_time
                status_text = f"Flipping normals: {i}/{num_meshes} ({elapsed:.1f}s)"
                context.workspace.status_text_set(status_text)

            if not obj or obj.type != 'MESH' or not obj.data:
                continue

            try:
                # The bmesh API is the correct, lightweight way to handle this in a script
                bm = bmesh.new()
                bm.from_mesh(obj.data)
                
                for face in bm.faces:
                    face.normal_flip()
                
                # Write the changes back to the mesh data block
                bm.to_mesh(obj.data)
                bm.free()
                obj.data.update() # Mark the mesh for a viewport update
                processed_count += 1
            except Exception as e:
                logging.error(f"Failed to flip normals for '{obj.name}' using bmesh API. The object may have corrupt data. Error: {e}")
                failed_objects.append(obj.name)
        
        logging.info(f"Successfully flipped normals for {processed_count}/{num_meshes} meshes.")
        if failed_objects:
            logging.warning(f"Could not process the following objects: {', '.join(failed_objects)}")

    finally:
        # --- State Restoration ---
        context.workspace.status_text_set(None) # Clear the status bar
        
        bpy.ops.object.select_all(action='DESELECT')
        for obj in original_selected:
            if obj and obj.name in context.view_layer.objects:
                try:
                    obj.select_set(True)
                except (ReferenceError, RuntimeError):
                    pass
        
        if original_active and original_active.name in context.view_layer.objects:
            context.view_layer.objects.active = original_active
        
        if original_mode != 'OBJECT' and context.view_layer.objects.active:
            try:
                bpy.ops.object.mode_set(mode=original_mode)
            except RuntimeError:
                pass
        
        end_time = time.time()
        logging.info(f"Batch flip normals operation finished in {end_time - start_time:.2f} seconds.")

def batch_mirror_objects_optimized(meshes_to_mirror, context):
    """
    Mirrors a list of mesh objects by applying their scale (batched),
    then performing bmesh vertex mirroring (X-axis) and normal flipping
    within a single Edit Mode session for all meshes.
    """
    if not meshes_to_mirror:
        logging.debug("Batch Mirror: No meshes to mirror.")
        return

    original_active_object = context.view_layer.objects.active
    original_selected_objects = list(context.selected_objects) # Make a copy
    original_mode = 'OBJECT'
    if context.object and hasattr(context.object, 'mode'):
        original_mode = context.object.mode
    elif context.mode:
        original_mode = context.mode

    logging.info(f"Batch Mirror: Starting process for {len(meshes_to_mirror)} meshes.")
    edit_mode_entered_successfully = False

    try:
        # --- Ensure OBJECT mode for all initial operations ---
        if context.mode != 'OBJECT':
            if bpy.ops.object.mode_set.poll():
                bpy.ops.object.mode_set(mode='OBJECT')
                context.view_layer.update() 
                logging.debug(f"Batch Mirror: Switched to OBJECT mode for setup. Current mode: {context.mode}")
                if context.mode != 'OBJECT': 
                    logging.error("Batch Mirror: Failed to switch to OBJECT mode even after command and update. Aborting.")
                    return
            else:
                logging.error("Batch Mirror: Cannot poll to switch to OBJECT mode for setup. Aborting.")
                return

        # --- 1. Batch Apply Scale Transformations ---
        bpy.ops.object.select_all(action='DESELECT')
        
        meshes_for_scale_apply = []
        for obj in meshes_to_mirror:
            if obj.type == 'MESH' and obj.name in context.view_layer.objects:
                obj.select_set(True)
                meshes_for_scale_apply.append(obj)
        
        if meshes_for_scale_apply:
            context.view_layer.objects.active = meshes_for_scale_apply[0]
            logging.debug(f"Batch Mirror: Applying scale to {len(meshes_for_scale_apply)} selected meshes. Active: '{meshes_for_scale_apply[0].name}'.")
            try:
                bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
                logging.info(f"  Successfully batch applied scale to {len(meshes_for_scale_apply)} meshes.")
            except RuntimeError as e_scale:
                logging.warning(f"  Failed to batch apply scale: {e_scale}")
        else:
            logging.info("Batch Mirror: No valid mesh objects were selected for scale application.")
            return

        # --- 2. Prepare for BMesh Operations ---
        selected_for_bmesh = [obj for obj in context.selected_objects if obj.type == 'MESH']

        if not selected_for_bmesh:
            logging.info("Batch Mirror: No valid mesh objects are selected for BMesh operations after scale apply.")
            return

        active_for_edit_mode = context.view_layer.objects.active
        if not (active_for_edit_mode and active_for_edit_mode in selected_for_bmesh and active_for_edit_mode.type == 'MESH'):
            active_for_edit_mode = selected_for_bmesh[0]
            context.view_layer.objects.active = active_for_edit_mode
        
        if not (active_for_edit_mode and active_for_edit_mode.type == 'MESH'): 
            logging.warning("Batch Mirror: Active object is not suitable (not a mesh or not selected) for entering EDIT mode. Skipping BMesh part.")
            return

        logging.debug(f"Batch Mirror: Attempting to enter EDIT mode with active object '{active_for_edit_mode.name}'. Selected for BMesh: {len(selected_for_bmesh)}")

        # --- 3. BMesh Vertex Mirror & Normal Flip (Single Edit Mode Session) ---
        if bpy.ops.object.mode_set.poll(): 
            logging.debug(f"Batch Mirror: Poll for object.mode_set successful (active: {context.view_layer.objects.active.name if context.view_layer.objects.active else 'None'}).")
            bpy.ops.object.mode_set(mode='EDIT') 
            logging.debug("Batch Mirror: bpy.ops.object.mode_set(mode='EDIT') called.")

            context.view_layer.update() 
            logging.debug(f"Batch Mirror: After mode_set and view_layer.update(), context.mode is now: '{context.mode}'")

            # CORRECTED CONDITION HERE:
            if context.mode == 'EDIT_MESH': # Check for 'EDIT_MESH' specifically for meshes
                edit_mode_entered_successfully = True
                logging.info("Batch Mirror: Successfully confirmed and entered EDIT_MESH mode.") # Updated log message
                
                processed_in_edit = 0
                for obj_in_edit in bpy.context.selected_editable_objects:
                    if obj_in_edit.type == 'MESH':
                        mesh = obj_in_edit.data
                        bm = bmesh.from_edit_mesh(mesh)

                        for vert in bm.verts:
                            vert.co.x *= -1
                        for face in bm.faces:
                            face.normal_flip()
                        
                        bmesh.update_edit_mesh(mesh, loop_triangles=False, destructive=False)
                        processed_in_edit +=1
                logging.debug(f"Batch Mirror: BMesh operations completed for {processed_in_edit} objects in Edit Mode.")
                
                if bpy.ops.object.mode_set.poll(): 
                    bpy.ops.object.mode_set(mode='OBJECT')
                    context.view_layer.update() 
                    logging.debug(f"Batch Mirror: Exited EDIT_MESH mode. Current mode: {context.mode}")
                    if context.mode != 'OBJECT':
                        logging.warning("Batch Mirror: Attempted to exit EDIT_MESH mode, but still not in OBJECT mode.")
                else:
                    logging.warning("Batch Mirror: Could not poll to exit EDIT_MESH mode after BMesh operations.")
            else:
                logging.error(f"Batch Mirror: Failed to enter EDIT_MESH mode (context.mode was '{context.mode}' after command and update). BMesh operations skipped.")
        else:
            logging.error(f"Batch Mirror: bpy.ops.object.mode_set.poll() returned False. Cannot attempt to switch to EDIT mode. (Active: {context.view_layer.objects.active.name if context.view_layer.objects.active else 'None'}, Type: {context.view_layer.objects.active.type if context.view_layer.objects.active else 'N/A'}). BMesh operations skipped.")
            
    except Exception as e:
        logging.error(f"Batch Mirror: Error during main operation: {e}", exc_info=True)
        if edit_mode_entered_successfully and context.mode == 'EDIT_MESH': # Check EDIT_MESH here too
            if bpy.ops.object.mode_set.poll():
                bpy.ops.object.mode_set(mode='OBJECT')
                context.view_layer.update()
    finally:
        # --- 4. Restore Original State ---
        logging.debug("Batch Mirror: Restoring original state...")
        if context.mode != 'OBJECT':
            if bpy.ops.object.mode_set.poll():
                bpy.ops.object.mode_set(mode='OBJECT')
                context.view_layer.update()

        bpy.ops.object.select_all(action='DESELECT')
        for obj in original_selected_objects:
            if obj and obj.name in context.view_layer.objects: 
                try: obj.select_set(True)
                except RuntimeError: pass
        
        if original_active_object and original_active_object.name in context.view_layer.objects: 
            context.view_layer.objects.active = original_active_object
        elif context.selected_objects: 
             context.view_layer.objects.active = context.selected_objects[0]
        else: 
            context.view_layer.objects.active = None

        if original_mode != 'OBJECT' and context.mode == 'OBJECT':
            can_restore_original_mode = False
            active_obj_for_restore = context.view_layer.objects.active
            if active_obj_for_restore:
                # For EDIT_MESH, the original_mode would have been 'EDIT_MESH' if it started there,
                # but we usually assume original_mode is one of the main context.mode strings.
                # The original_mode variable stores 'OBJECT', 'EDIT', 'POSE' etc.
                # So if original_mode was 'EDIT' (generic), it should be fine to try to set it back.
                if original_mode == 'EDIT' and active_obj_for_restore.type in {'MESH', 'CURVE', 'SURFACE', 'FONT', 'META', 'ARMATURE'}:
                    can_restore_original_mode = True
                elif original_mode == 'POSE' and active_obj_for_restore.type == 'ARMATURE':
                     can_restore_original_mode = True
                elif original_mode in {'SCULPT', 'VERTEX_PAINT', 'WEIGHT_PAINT', 'TEXTURE_PAINT'} and active_obj_for_restore.type == 'MESH':
                    can_restore_original_mode = True
            
            if can_restore_original_mode and bpy.ops.object.mode_set.poll(mode=original_mode): 
                try: bpy.ops.object.mode_set(mode=original_mode)
                except RuntimeError as e_mode_restore: 
                    logging.warning(f"Batch Mirror (finally): Could not restore original mode '{original_mode}': {e_mode_restore}")
            elif context.mode != original_mode :
                 logging.warning(f"Batch Mirror (finally): Conditions (or poll) not met to restore original mode '{original_mode}'. Mode remains '{context.mode}'.")
        logging.info("Batch Mirror: Process finished.")


def _get_base_name_and_suffix_parts(obj_name):
    # Pattern 1: Handles "name_S1.S2" (e.g., inst_62EC3A6022F09C50_0.001)
    match_custom_extended = re.fullmatch(r'(.+?)_(\d+)\.(\d+)$', obj_name)
    if match_custom_extended:
        base, p1_str, p2_str = match_custom_extended.groups()
        try:
            return base, (int(p1_str), int(p2_str))
        except ValueError:
            pass 

    # Pattern 2: Handles "name.S2" (e.g., inst_Cool.001)
    match_blender_suffix = re.fullmatch(r'(.+?)\.(\d+)$', obj_name)
    if match_blender_suffix:
        base, num_str = match_blender_suffix.groups()
        try:
            return base, (int(num_str),)
        except ValueError:
            pass

    # Pattern 3: Handles "name_S1" (e.g., inst_62EC3A6022F09C50_0)
    match_custom_simple = re.fullmatch(r'(.+?)_(\d+)$', obj_name)
    if match_custom_simple:
        base, p1_str = match_custom_simple.groups()
        try:
            return base, (int(p1_str),)
        except ValueError:
            pass
    
    return obj_name, None
     
def _perform_duplicate_cleanup_phase_module(context, scene_to_clean):
    logging.info(f"Starting combined cleanup in scene: '{scene_to_clean.name}'")

    deleted_objects_count_inst = 0 
    deleted_objects_mesh_pattern = 0 

    original_window_scene = context.window.scene
    original_active_object_in_original_scene = context.active_object 
    original_selected_objects_in_original_scene = list(context.selected_objects)

    original_mode = 'OBJECT' 
    if original_window_scene == context.scene: 
        if context.object and hasattr(context.object, 'mode'):
            original_mode = context.object.mode 
        elif context.mode: 
            original_mode = context.mode

    try: 
        if context.window.scene != scene_to_clean:
            context.window.scene = scene_to_clean
            logging.debug(f"Cleanup phase: Switched active window scene to '{scene_to_clean.name}'.")

        if context.mode != 'OBJECT':
            active_obj_for_mode_set = context.view_layer.objects.active 
            if not active_obj_for_mode_set and scene_to_clean.objects:
                candidate_active = next((obj for obj in scene_to_clean.objects if obj.type in {'MESH', 'CURVE', 'EMPTY', 'ARMATURE'}), None)
                if candidate_active and candidate_active.name in context.view_layer.objects: 
                    context.view_layer.objects.active = candidate_active
            
            if bpy.ops.object.mode_set.poll(): 
                try: 
                    bpy.ops.object.mode_set(mode='OBJECT')
                    logging.debug(f"Cleanup phase: Switched to OBJECT mode in '{scene_to_clean.name}'.")
                except RuntimeError as e: 
                    logging.warning(f"Cleanup phase: Could not set OBJECT mode in '{scene_to_clean.name}': {e}")
            else:
                logging.warning(f"Cleanup phase: Cannot poll bpy.ops.object.mode_set to OBJECT in '{scene_to_clean.name}'. Mode remains {context.mode}.")
    
        logging.info(f"Starting 'inst_' object cleanup in '{scene_to_clean.name}'.")
        if bpy.ops.object.select_all.poll():
            bpy.ops.object.select_all(action='DESELECT')

        objects_to_delete_inst_collector = [] 
        objects_to_keep_inst_collector = []    

        grouped_by_base_inst = collections.defaultdict(list)
        prefix_to_scan_inst = "inst_"
        all_inst_objects_in_scene = [obj for obj in scene_to_clean.objects if obj.name.startswith(prefix_to_scan_inst)]

        for obj_inst in all_inst_objects_in_scene: 
            base_name_part, suffix_key_part = _get_base_name_and_suffix_parts(obj_inst.name)
            # logging.debug(f"Parsing inst_ name: '{obj_inst.name}' -> base: '{base_name_part}', suffix_key: {suffix_key_part}") # Reduced verbosity
            grouped_by_base_inst[base_name_part].append({
                'obj': obj_inst, 
                'name': obj_inst.name, 
                'suffix_key': suffix_key_part
            })

        for base_name_part, obj_infos_list in grouped_by_base_inst.items():
            plain_originals = [info for info in obj_infos_list if info['suffix_key'] is None]
            suffixed_duplicates = [info for info in obj_infos_list if info['suffix_key'] is not None]
        
            object_to_keep_info_dict = None 
            current_group_objects_to_delete = [] 

            if plain_originals:
                plain_originals.sort(key=lambda x: x['name']) 
                object_to_keep_info_dict = plain_originals[0] 
                current_group_objects_to_delete.extend(p_info['obj'] for p_info in plain_originals[1:])
                current_group_objects_to_delete.extend(s_info['obj'] for s_info in suffixed_duplicates)
            elif suffixed_duplicates: 
                suffixed_duplicates.sort(key=lambda x: (x['suffix_key'], x['name'])) # type: ignore
                object_to_keep_info_dict = suffixed_duplicates[0] 
                current_group_objects_to_delete.extend(s_info['obj'] for s_info in suffixed_duplicates[1:])
            else: 
                if obj_infos_list: 
                        logging.warning(f"'inst_' cleanup for base '{base_name_part}': Group with {len(obj_infos_list)} items had no plain or suffixed. Fallback: keep first by name.")
                        if len(obj_infos_list) > 0: 
                            obj_infos_list.sort(key=lambda x: x['name'])
                            object_to_keep_info_dict = obj_infos_list[0]
                            current_group_objects_to_delete.extend(info['obj'] for info in obj_infos_list[1:])

            if object_to_keep_info_dict:
                objects_to_keep_inst_collector.append(object_to_keep_info_dict['obj'])
                # logging.debug(f"'inst_' cleanup for base '{base_name_part}': Keeping '{object_to_keep_info_dict['name']}'...") # Reduced verbosity
            # else: # Reduced verbosity
                # logging.debug(f"'inst_' cleanup for base '{base_name_part}': No object chosen to keep...")
            objects_to_delete_inst_collector.extend(current_group_objects_to_delete)

        kept_inst_objects_set = set(objects_to_keep_inst_collector) 
        unique_objects_to_delete_inst_final = list(set(
            obj for obj in objects_to_delete_inst_collector 
            if obj and obj.name in scene_to_clean.objects and obj not in kept_inst_objects_set 
        ))
    
        if unique_objects_to_delete_inst_final:
            logging.info(f"'inst_' cleanup: Identified {len(unique_objects_to_delete_inst_final)} unique 'inst_' objects for deletion.")
            if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')
            active_obj_inst_del = context.view_layer.objects.active
            active_obj_inst_del_cleared = False
            if active_obj_inst_del and active_obj_inst_del in unique_objects_to_delete_inst_final:
                context.view_layer.objects.active = None
                active_obj_inst_del_cleared = True

            selected_for_deletion_count = 0
            for obj_to_del in unique_objects_to_delete_inst_final: 
                if obj_to_del.name in context.view_layer.objects : 
                    try:
                        obj_to_del.select_set(True); selected_for_deletion_count +=1
                    except RuntimeError as e_select: logging.warning(f"Could not select '{obj_to_del.name}' for inst_ deletion: {e_select}")
                else: logging.warning(f"'{obj_to_del.name}' for inst_ deletion not in view layer.")
        
            if selected_for_deletion_count > 0: 
                bpy.ops.object.delete(); deleted_objects_count_inst = selected_for_deletion_count 
                logging.info(f"'inst_' cleanup: Batch deleted {deleted_objects_count_inst} objects.")
            else: logging.info("'inst_' cleanup: No 'inst_' objects ultimately selected for deletion.")
        
            if active_obj_inst_del_cleared: 
                if active_obj_inst_del and (active_obj_inst_del.name not in scene_to_clean.objects): 
                    if scene_to_clean.objects: 
                        new_active_candidate = next((obj for obj in scene_to_clean.objects if obj.type in {'MESH', 'EMPTY', 'ARMATURE'}), None)
                        if new_active_candidate and new_active_candidate.name in context.view_layer.objects:
                                context.view_layer.objects.active = new_active_candidate
                elif active_obj_inst_del and active_obj_inst_del.name in scene_to_clean.objects: 
                    if active_obj_inst_del.name in context.view_layer.objects :
                        context.view_layer.objects.active = active_obj_inst_del
        else: logging.info("'inst_' cleanup: No 'inst_' objects scheduled for deletion.")

        final_kept_inst_objects_set = { obj for obj in objects_to_keep_inst_collector if obj.name in scene_to_clean.objects }
        logging.info(f"After 'inst_' cleanup, {len(final_kept_inst_objects_set)} 'inst_' objects remain for mesh.#### cleanup reference.")
    
        logging.info(f"Starting 'mesh.####' OBJECT cleanup in scene: '{scene_to_clean.name}'.")
        objects_to_delete_mesh_pattern_collector = []
        if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')

        all_mesh_dot_pattern_objects_in_scene = [ obj for obj in scene_to_clean.objects if obj.type == 'MESH' and re.fullmatch(r"mesh\.(\d+)", obj.name) ]

        if all_mesh_dot_pattern_objects_in_scene:
            for mesh_obj in all_mesh_dot_pattern_objects_in_scene:
                is_used_or_parented_safely = False
                if mesh_obj.parent and mesh_obj.parent in final_kept_inst_objects_set:
                    is_used_or_parented_safely = True; # logging.debug(f"Mesh '{mesh_obj.name}' KEPT: parent is kept inst.")
                if not is_used_or_parented_safely:
                    for inst_obj in final_kept_inst_objects_set: 
                        if inst_obj.type == 'EMPTY': 
                            if inst_obj.instance_type == 'OBJECT' and inst_obj.instance_object == mesh_obj: is_used_or_parented_safely = True; break
                            if inst_obj.instance_type == 'COLLECTION' and inst_obj.instance_collection and mesh_obj.name in inst_obj.instance_collection.all_objects: is_used_or_parented_safely = True; break
                if not is_used_or_parented_safely and mesh_obj.parent:
                    parent_obj = mesh_obj.parent
                    if parent_obj.name in scene_to_clean.objects: 
                        is_parent_kept_inst = parent_obj in final_kept_inst_objects_set
                        is_parent_mesh_dot = parent_obj.type == 'MESH' and re.fullmatch(r"mesh\.(\d+)", parent_obj.name)
                        if not is_parent_kept_inst and not is_parent_mesh_dot: is_used_or_parented_safely = True; # logging.debug(f"Mesh '{mesh_obj.name}' KEPT: parent is regular.")
                if not is_used_or_parented_safely and mesh_obj.data and mesh_obj.data.users > 1:
                    for user_obj in scene_to_clean.objects: 
                        if user_obj.data == mesh_obj.data and user_obj != mesh_obj:
                            is_user_kept_inst = user_obj in final_kept_inst_objects_set
                            is_user_mesh_dot = user_obj.type == 'MESH' and re.fullmatch(r"mesh\.(\d+)", user_obj.name)
                            is_user_deleted_inst = user_obj.name.startswith(prefix_to_scan_inst) and not is_user_kept_inst
                            if not is_user_mesh_dot and not is_user_deleted_inst : is_used_or_parented_safely = True; break # logging.debug(f"Mesh '{mesh_obj.name}' KEPT: data used by other significant obj.")
                if not is_used_or_parented_safely:
                    is_in_root = scene_to_clean.collection and mesh_obj.name in scene_to_clean.collection.objects
                    if mesh_obj.parent is None and (is_in_root or not any(coll == scene_to_clean.collection for coll in mesh_obj.users_collection)): # If unparented & in root, or unparented & not in any other meaningful collection part of main scene structure (heuristic)
                        objects_to_delete_mesh_pattern_collector.append(mesh_obj) # logging.info(f"Unused 'mesh.####' object '{mesh_obj.name}' scheduled for deletion.")

            if objects_to_delete_mesh_pattern_collector:
                unique_objects_to_delete_mesh_final = list(set( obj for obj in objects_to_delete_mesh_pattern_collector if obj and obj.name in scene_to_clean.objects ))
                if unique_objects_to_delete_mesh_final:
                    logging.info(f"'mesh.####' cleanup: Identified {len(unique_objects_to_delete_mesh_final)} objects for deletion.")
                    if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')
                    active_obj_mesh_del = context.view_layer.objects.active; active_obj_mesh_del_cleared = False
                    if active_obj_mesh_del and active_obj_mesh_del in unique_objects_to_delete_mesh_final: context.view_layer.objects.active = None; active_obj_mesh_del_cleared = True
                    
                    selected_for_mesh_del_count = 0
                    for obj_to_del in unique_objects_to_delete_mesh_final:
                        if obj_to_del.name in context.view_layer.objects: obj_to_del.select_set(True); selected_for_mesh_del_count +=1
                        else: logging.warning(f"'{obj_to_del.name}' for mesh.#### deletion not in view layer.")
                    
                    if selected_for_mesh_del_count > 0 and context.selected_objects: 
                        bpy.ops.object.delete(); deleted_objects_mesh_pattern = selected_for_mesh_del_count
                        logging.info(f"'mesh.####' cleanup: Batch deleted {deleted_objects_mesh_pattern} objects.")
                        if active_obj_mesh_del_cleared: 
                            if active_obj_mesh_del and (active_obj_mesh_del.name not in scene_to_clean.objects): 
                                if scene_to_clean.objects: 
                                    new_active = next((o for o in scene_to_clean.objects if o.type in {'MESH', 'EMPTY'}), None)
                                    if new_active and new_active.name in context.view_layer.objects: context.view_layer.objects.active = new_active
                            elif active_obj_mesh_del and active_obj_mesh_del.name in scene_to_clean.objects and active_obj_mesh_del.name in context.view_layer.objects:
                                context.view_layer.objects.active = active_obj_mesh_del
                    else: logging.info("'mesh.####' cleanup: No objects ultimately selected for deletion.")
                else: logging.info("'mesh.####' cleanup: No objects for deletion after filtering.")
            else: logging.info("'mesh.####' cleanup: No candidates initially identified.")

    except Exception as e_cleanup_main: 
        logging.error(f"Error during main cleanup phase in '{scene_to_clean.name}': {e_cleanup_main}", exc_info=True)
    finally: 
        current_scene_name_at_finally = context.window.scene.name
        if context.window.scene != original_window_scene: context.window.scene = original_window_scene; # logging.debug(f"Cleanup: Restored window scene to '{original_window_scene.name}'.")
        if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')
        for obj_ref in original_selected_objects_in_original_scene: 
            if obj_ref and obj_ref.name in original_window_scene.objects: 
                s_obj = original_window_scene.objects.get(obj_ref.name)
                if s_obj and s_obj.name in context.view_layer.objects: 
                    try: s_obj.select_set(True)
                    except RuntimeError: pass
        o_active_name = original_active_object_in_original_scene.name if original_active_object_in_original_scene else None
        if o_active_name and o_active_name in original_window_scene.objects:
            s_active = original_window_scene.objects.get(o_active_name)
            if s_active and s_active.name in context.view_layer.objects: 
                try: context.view_layer.objects.active = s_active
                except Exception: pass
        elif context.view_layer.objects.active is not None: context.view_layer.objects.active = None 
        
        final_mode = context.mode 
        if final_mode != original_mode:
            can_set_orig = (original_mode == 'OBJECT') or (context.view_layer.objects.active is not None) 
            if can_set_orig and bpy.ops.object.mode_set.poll():
                try: bpy.ops.object.mode_set(mode=original_mode)
                except RuntimeError : pass # logging.warning(f"Cleanup (finally): Could not restore mode to '{original_mode}'.")

    logging.info(f"Finished cleanup for scene '{scene_to_clean.name}'. Deleted {deleted_objects_count_inst} 'inst_', {deleted_objects_mesh_pattern} 'mesh.####'.")
    return {'deleted_objects_inst': deleted_objects_count_inst, 'deleted_objects_mesh_pattern': deleted_objects_mesh_pattern}

def copy_exported_files(obj_path, mtl_path, destination):
    try:
        os.makedirs(destination, exist_ok=True)
        shutil.copy2(obj_path, destination)
        if os.path.exists(mtl_path):
            shutil.copy2(mtl_path, destination)
        else:
            logging.warning(f"MTL file does not exist: {mtl_path}")
            return False
        logging.info(f"Copied exported files to {destination}")
        return True
    except Exception as e:
        logging.error(f"Failed to copy exported files: {e}")
        return False

def make_request_with_retries(method, url, headers=None, json_payload=None, retries=3, delay=5, **kwargs):
    last_response = None
    for attempt in range(1, retries + 1):
        try:
            logging.debug(f"Attempt {attempt}: {method} {url}")
            response = requests.request(method, url, headers=headers, json=json_payload, timeout=60, **kwargs)
            last_response = response
            logging.debug(f"Response: {response.status_code} - {response.text}")
            if response.status_code in [200, 201, 204]:
                return response
            else:
                logging.warning(f"Attempt {attempt} failed with status {response.status_code}")
        except requests.exceptions.RequestException as e:
            logging.warning(f"Attempt {attempt} encountered exception: {e}")
            # For network errors, last_response remains None or the last http error response
    
    if last_response is not None:
         logging.error(f"All {retries} attempts failed for {method} {url}. Last status: {last_response.status_code}")
    else:
         logging.error(f"All {retries} attempts failed for {method} {url}. No response from server (network error).")

    return last_response # Return the last response object, even if it's an error

def verify_texture_files_exist(context):
    return True, []


def update_remix_preset(self, context):
    global is_applying_preset
    if is_applying_preset:
        return
    is_applying_preset = True
    addon_prefs = context.preferences.addons[__name__].preferences

    if addon_prefs.remix_preset == 'UNREAL_ENGINE':
        backup = context.scene.remix_custom_settings_backup
        backup.obj_export_forward_axis = addon_prefs.obj_export_forward_axis
        backup.obj_export_up_axis = addon_prefs.obj_export_up_axis
        backup.flip_faces_export = addon_prefs.flip_faces_export
        backup.mirror_import = addon_prefs.mirror_import
        backup.remix_export_scale = addon_prefs.remix_export_scale
        backup.remix_use_selection_only = addon_prefs.remix_use_selection_only
        backup.remix_ingest_directory = addon_prefs.remix_ingest_directory
        backup.remix_verify_ssl = addon_prefs.remix_verify_ssl
        backup.remix_import_original_textures = addon_prefs.remix_import_original_textures

        addon_prefs.obj_export_forward_axis = 'Y'
        addon_prefs.obj_export_up_axis = 'Z'
        addon_prefs.flip_faces_export = True
        addon_prefs.remix_export_scale = 1.0
        addon_prefs.remix_ingest_directory = "/ProjectFolder/Assets"
        addon_prefs.remix_verify_ssl = True
        addon_prefs.remix_import_original_textures = False

        logging.info("Applied 'Unreal Engine' preset settings.")

    elif addon_prefs.remix_preset == 'CUSTOM':
        logging.info("Preset set to 'Custom'. No changes applied.")
    else:
        logging.warning(f"Unknown preset selected: {addon_prefs.remix_preset}")

    is_applying_preset = False


def set_preset_to_custom(context):
    global is_applying_preset
    if not is_applying_preset:
        addon_prefs = context.preferences.addons[__name__].preferences
        if addon_prefs.remix_preset != 'CUSTOM':
            is_applying_preset = True
            addon_prefs.remix_preset = 'CUSTOM'
            logging.info("Preset switched to 'Custom' due to manual changes.")

            backup = context.scene.remix_custom_settings_backup
            backup.obj_export_forward_axis = addon_prefs.obj_export_forward_axis
            backup.obj_export_up_axis = addon_prefs.obj_export_up_axis
            backup.flip_faces_export = addon_prefs.flip_faces_export
            backup.mirror_import = addon_prefs.mirror_import
            backup.remix_export_scale = addon_prefs.remix_export_scale
            backup.remix_use_selection_only = addon_prefs.remix_use_selection_only
            backup.remix_ingest_directory = addon_prefs.remix_ingest_directory
            backup.remix_verify_ssl = addon_prefs.remix_verify_ssl
            backup.remix_import_original_textures = addon_prefs.remix_import_original_textures

            logging.debug("Custom settings have been backed up after manual changes.")
            is_applying_preset = False


def set_preset_to_custom(self, context):
    global is_applying_preset
    addon_prefs = context.preferences.addons[__name__].preferences
    if not is_applying_preset and addon_prefs.remix_preset != 'CUSTOM':
        addon_prefs.remix_preset = 'CUSTOM'
        logging.info("Preset switched to 'Custom' due to manual changes.")


def get_blend_filename():
    blend_file = bpy.path.basename(bpy.data.filepath)
    blend_name, _ = os.path.splitext(blend_file)
    return blend_name if blend_name else "untitled"


def get_asset_number(context):
    addon_prefs = context.preferences.addons[__name__].preferences
    blend_name = get_blend_filename()
    if addon_prefs.remix_use_custom_name and addon_prefs.remix_use_selection_only and addon_prefs.remix_base_obj_name:
        base_name = addon_prefs.remix_base_obj_name
        logging.debug(f"Using 'remix_base_obj_name' for asset numbering: {base_name}")
    else:
        base_name = blend_name
        logging.debug(f"Using blend file base name for asset numbering: {base_name}")

    for item in context.scene.remix_asset_number:
        if item.blend_name == base_name:
            asset_number = item.asset_number
            item.asset_number += 1
            logging.debug(f"Retrieved and incremented asset number {asset_number} for base name '{base_name}'.")
            return base_name, asset_number

    new_item = context.scene.remix_asset_number.add()
    new_item.blend_name = base_name
    new_item.asset_number = 2
    logging.debug(f"Initialized asset number 1 for new base name '{base_name}'.")
    return base_name, 1


def ensure_single_leading_slash(path):
    return f'/{path.lstrip("/")}'


def replace_texture(material_name, old_texture_path, new_texture_path):
    material = bpy.data.materials.get(material_name)
    if not material or not material.use_nodes:
        print(f"Material '{material_name}' not found or does not use nodes.")
        return
    for node in material.node_tree.nodes:
        if node.type == 'TEX_IMAGE' and node.image and os.path.abspath(node.image.filepath) == os.path.abspath(old_texture_path):
            if os.path.exists(new_texture_path):
                node.image = bpy.data.images.load(new_texture_path)
                print(f"Texture replaced successfully in material '{material_name}'")
            else:
                print(f"New texture file does not exist: {new_texture_path}")


def flip_normals_api(obj):
    try:
        if obj and obj.type == 'MESH':
            logging.debug(f"Starting normals flip for object: {obj.name}")
            bm = bmesh.new()
            bm.from_mesh(obj.data)
            for face in bm.faces:
                face.normal_flip()
            bm.to_mesh(obj.data)
            bm.free()
            obj.data.update()
            logging.debug(f"Normals flipped for object '{obj.name}'.")
            print(f"Normals flipped for object '{obj.name}'.")
        else:
            logging.warning(f"Object '{obj.name}' is not a mesh.")
            print(f"Object '{obj.name}' is not a mesh.")
    except Exception as e:
        logging.error(f"Error flipping normals for object '{obj.name}': {e}")
        print(f"Error flipping normals for object '{obj.name}': {e}")
        
def fetch_selected_mesh_prim_paths():
    """
    Fetches the list of currently-selected mesh prim paths from the Remix server.
    Returns a list of paths (each with a single leading slash) under "/meshes/".
    Falls back to a default server URL if addon preferences are unavailable.
    """
    try:
        # Default in case preferences aren't accessible
        server_url_base = "http://localhost:8011/stagecraft"
        verify_ssl_cert = True

        # Attempt to read the user’s configured server URL and SSL setting
        try:
            context = bpy.context
            addon_prefs = context.preferences.addons[__name__].preferences
            server_url_base = addon_prefs.remix_server_url.rstrip('/')
            verify_ssl_cert = addon_prefs.remix_verify_ssl
            url = f"{server_url_base}/assets/?selection=true&filter_session_assets=false&exists=true"
        except (AttributeError, KeyError):
            logging.warning(
                "fetch_selected_mesh_prim_paths: Could not get addon_prefs from context. Using default URL."
            )
            url = f"{server_url_base}/assets/?selection=true&filter_session_assets=false&exists=true"

        headers = {'accept': 'application/lightspeed.remix.service+json; version=1.0'}
        response = make_request_with_retries('GET', url, headers=headers, verify=verify_ssl_cert)

        if not response or response.status_code != 200:
            logging.error(
                f"Failed to fetch selected mesh prim paths. Status: "
                f"{response.status_code if response else 'No Response'}"
            )
            return []

        data = response.json()

        # First, look for the modern "prim_paths" key; fall back to "asset_paths"
        asset_or_prim_paths = data.get("prim_paths")
        if asset_or_prim_paths is None:
            logging.warning(
                "fetch_selected_mesh_prim_paths: Key 'prim_paths' not found in server response, "
                "trying 'asset_paths' as fallback."
            )
            asset_or_prim_paths = data.get("asset_paths", [])

        # Filter to only those under "/meshes/"
        selected_meshes = [
            path for path in asset_or_prim_paths
            if "/meshes/" in path.lower()
        ]

        logging.info(f"Selected mesh prim paths: {selected_meshes}")
        # Ensure each has exactly one leading slash and no trailing slash
        return [ensure_single_leading_slash(p.rstrip('/')) for p in selected_meshes]

    except Exception as e:
        logging.error(f"Error fetching selected mesh prim paths: {e}", exc_info=True)
        return []
        
def attach_original_textures(imported_objects, context, base_dir):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        if not imported_objects:
            logging.warning("No imported objects to attach textures.")
            print("No imported objects to attach textures.")
            return

        import_original_textures = addon_prefs.remix_import_original_textures

        blend_file_path = bpy.data.filepath
        if not blend_file_path:
            logging.error("Blend file has not been saved. Cannot determine textures directory.")
            print("Blend file has not been saved. Cannot determine textures directory.")
            return

        blend_dir = os.path.dirname(blend_file_path).replace('\\', '/')
        textures_subdir = os.path.join(blend_dir, "textures").replace('\\', '/')
        logging.debug(f"Textures subdirectory path: {textures_subdir}")
        # print(f"Textures subdirectory path: {textures_subdir}") # Redundant with logging

        if not os.path.exists(textures_subdir):
            try:
                os.makedirs(textures_subdir, exist_ok=True)
                logging.info(f"Created 'textures' subdirectory: {textures_subdir}")
                # print(f"Created 'textures' subdirectory: {textures_subdir}")
            except Exception as e:
                logging.error(f"Failed to create textures subdirectory '{textures_subdir}': {e}")
                # print(f"Failed to create textures subdirectory '{textures_subdir}': {e}")
                return
        # else: # Not strictly necessary to log if it exists, can be verbose
            # logging.debug(f"'textures' subdirectory already exists: {textures_subdir}")
            # print(f"'textures' subdirectory already exists: {textures_subdir}")

        # --- OPTIMIZATION: Collect unique materials first ---
        unique_materials = set()
        for obj in imported_objects:
            if obj.type == 'MESH': # Ensure we only consider mesh objects for materials
                for mat_slot in obj.material_slots:
                    if mat_slot.material:
                        unique_materials.add(mat_slot.material)
        
        if not unique_materials:
            logging.warning("No materials found on imported objects to process.")
            return

        logging.info(f"Found {len(unique_materials)} unique materials to process for texture attachment.")

        # --- Process each unique material only once ---
        for mat in unique_materials:
            logging.info(f"Processing unique material: {mat.name}")
            # print(f"Processing unique material: {mat.name}") # Redundant

            if not mat.use_nodes:
                mat.use_nodes = True
                logging.info(f"Enabled node usage for material '{mat.name}'.")
                # print(f"Enabled node usage for material '{mat.name}'.")

            principled_bsdf = None
            image_texture_node = None # Use a more descriptive name

            # Find existing Principled BSDF and Image Texture nodes
            for node in mat.node_tree.nodes:
                if node.type == 'BSDF_PRINCIPLED' and not principled_bsdf: # Take the first one
                    principled_bsdf = node
                elif node.type == 'TEX_IMAGE' and not image_texture_node: # Take the first one
                    image_texture_node = node
                if principled_bsdf and image_texture_node: # Found both, no need to continue loop
                    break
            
            if not principled_bsdf:
                principled_bsdf = mat.node_tree.nodes.new(type='ShaderNodeBsdfPrincipled')
                principled_bsdf.location = (200, 0) # Adjusted location for clarity
                logging.info(f"Created Principled BSDF node for material '{mat.name}'.")
                # print(f"Created Principled BSDF node for material '{mat.name}'.")

            if not image_texture_node:
                image_texture_node = mat.node_tree.nodes.new(type='ShaderNodeTexImage')
                image_texture_node.location = (0, 0)
                logging.info(f"Created Image Texture node for material '{mat.name}'.")
                # print(f"Created Image Texture node for material '{mat.name}'.")

            # Extract hash from material name (assuming mat.name is consistently formatted)
            match = re.match(r'^mat_([A-Fa-f0-9]{16})', mat.name) # Simplified regex if suffix doesn't matter for hash
            if not match:
                 # Fallback if the primary pattern with a dot isn't matched, or if it's just the hash
                match = re.match(r'([A-Fa-f0-9]{16})', mat.name) # Try to find a 16-char hex hash anywhere
            
            if match:
                # If the regex had a group for the hash specifically, use it.
                # If it's the full match (e.g. r'([A-Fa-f0-9]{16})'), group(0) or group(1) might be it.
                # Safest to check groups.
                mat_hash = match.group(1) if match.groups() else match.group(0)
                logging.debug(f"Extracted hash '{mat_hash}' from material '{mat.name}'.")
            else:
                logging.warning(f"Material name '{mat.name}' does not match expected hash pattern. Cannot determine texture.")
                # print(f"Material name '{mat.name}' does not match expected hash pattern.")
                continue # Skip this material if no hash

            texture_file_dds = f"{mat_hash}.dds"
            texture_path_dds = os.path.join(base_dir, "textures", texture_file_dds).replace('\\', '/')
            # logging.info(f"Looking for DDS texture file: {texture_path_dds}") # Can be verbose
            # print(f"Looking for texture file: {texture_file_dds}")

            if os.path.exists(texture_path_dds):
                target_image_path_for_node = texture_path_dds
                target_image_name_for_node = os.path.basename(texture_path_dds)
                is_png_converted = False

                if import_original_textures: # DDS to PNG conversion path
                    png_filename = f"{mat_hash}.png"
                    png_path_full = os.path.join(textures_subdir, png_filename).replace('\\', '/')
                    logging.info(f"Attempting to use/convert to PNG: {png_path_full} from DDS: {texture_path_dds}")
                    # print(f"Preparing to convert DDS to PNG: {texture_path_dds} -> {png_path_full}")

                    if not os.path.exists(png_path_full) or os.path.getmtime(texture_path_dds) > os.path.getmtime(png_path_full):
                        try:
                            dds_image_data = bpy.data.images.load(texture_path_dds, check_existing=True) # check_existing is important
                            # Create a new image for PNG conversion to avoid modifying dds_image_data's filepath directly before saving
                            png_image_data_new = bpy.data.images.new(
                                name=png_filename, # Use clean filename
                                width=dds_image_data.size[0],
                                height=dds_image_data.size[1],
                                alpha=(dds_image_data.channels == 4)
                            )
                            png_image_data_new.pixels = list(dds_image_data.pixels) # Copy pixels
                            png_image_data_new.file_format = 'PNG'
                            png_image_data_new.filepath_raw = png_path_full # Set path for saving
                            png_image_data_new.save()
                            logging.info(f"Converted and saved PNG image: {png_path_full}")
                            # print(f"Saved PNG image: {png_path_full}")
                            
                            # Clean up the loaded DDS image datablock if it's no longer needed by other parts of Blender
                            # (or if we exclusively want to use the PNG from now on)
                            bpy.data.images.remove(dds_image_data)
                            is_png_converted = True
                            target_image_path_for_node = png_path_full
                            target_image_name_for_node = png_filename

                        except Exception as e_conv:
                            logging.error(f"Failed to convert DDS to PNG for texture '{texture_file_dds}': {e_conv}")
                            # print(f"Failed to convert DDS to PNG for texture '{texture_file_dds}': {e_conv}")
                            # Fallback to DDS if conversion fails
                            target_image_path_for_node = texture_path_dds
                            target_image_name_for_node = texture_file_dds
                    else:
                        logging.info(f"PNG texture already exists and is up-to-date: {png_path_full}")
                        # print(f"PNG texture already exists: {png_path_full}")
                        target_image_path_for_node = png_path_full
                        target_image_name_for_node = png_filename
                        is_png_converted = True # It exists, so it's "converted" for our purposes
                
                # Load the target image (either original DDS or converted PNG)
                loaded_image_for_node = bpy.data.images.load(target_image_path_for_node, check_existing=True)
                image_texture_node.image = loaded_image_for_node
                logging.info(f"Assigned image '{target_image_name_for_node}' to texture node in material '{mat.name}'.")

                # Link texture to Principled BSDF's Base Color
                links = mat.node_tree.links
                base_color_input = principled_bsdf.inputs.get('Base Color')
                if base_color_input:
                    # Remove existing links to Base Color if any
                    for link in list(base_color_input.links): # Iterate over a copy
                        links.remove(link)
                        logging.debug(f"Removed existing link to Base Color for material '{mat.name}'.")
                    
                    links.new(image_texture_node.outputs['Color'], base_color_input)
                    logging.info(f"Connected Image Texture to Base Color for material '{mat.name}'.")
                    # print(f"Connected Image Texture to Base Color for material '{mat.name}'.")
                else:
                    logging.warning(f"No 'Base Color' input found in Principled BSDF for material '{mat.name}'.")
                    # print(f"No 'Base Color' input found in Principled BSDF for material '{mat.name}'.")

            else: # DDS file does not exist
                logging.warning(f"Texture file does not exist for material '{mat.name}': {texture_path_dds}")
                # print(f"Texture file does not exist for material '{mat.name}': {texture_path_dds}")
                # Optionally clear the image on the node if the file is missing
                if image_texture_node.image:
                    image_texture_node.image = None 
                    logging.info(f"Cleared missing image from texture node in material '{mat.name}'.")


    except Exception as e:
        logging.error(f"Error attaching original textures: {e}", exc_info=True)
        # print(f"Error attaching original textures: {e}")

def attach_mesh_reference(prim_path, usd_file, context):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        encoded_prim = urllib.parse.quote(prim_path, safe='')
        url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/{encoded_prim}/file-paths"
        payload = {"asset_file_path": usd_file, "force": False}
        headers = {
            'accept': 'application/lightspeed.remix.service+json; version=1.0',
            'Content-Type': 'application/lightspeed.remix.service+json; version=1.0'
        }

        logging.info(f"Attaching mesh reference via POST to: {url}")
        response = make_request_with_retries('POST', url, json_payload=payload, headers=headers, verify=addon_prefs.remix_verify_ssl)
        if not response or response.status_code != 200:
            logging.error("Failed to attach mesh reference.")
            return None

        reference_paths = response.json().get("reference_paths", [[]])
        if not reference_paths or not reference_paths[0]:
            logging.error("No reference paths returned in response.")
            return None

        reference_path = reference_paths[0][0]
        logging.info(f"Mesh reference attached at: {reference_path}")
        return ensure_single_leading_slash(reference_path)
    except Exception as e:
        logging.error(f"Error attaching mesh reference: {e}")
        return None
    

def construct_dynamic_prim_path(reference_path, obj_name, mesh_name, append_world=True):
    try:
        if not reference_path:
            logging.error("Reference path is None or empty. Cannot construct dynamic prim path.")
            print("Reference path is None or empty. Cannot construct dynamic prim path.")
            return None

        clean_mesh_name = mesh_name.replace('.', '_')
        if append_world:
            dynamic_path = f"{reference_path}/XForms/World/{obj_name}/{clean_mesh_name}"
        else:
            dynamic_path = f"{reference_path}/{obj_name}/{clean_mesh_name}"
        logging.debug(f"Constructed dynamic prim path: {dynamic_path}")
        return ensure_single_leading_slash(dynamic_path)
    except Exception as e:
        logging.error(f"Error constructing dynamic prim path: {e}")
        print(f"Error constructing dynamic prim path: {e}")
        return None


def select_mesh_prim_in_remix(reference_prim, context):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        encoded_prim = urllib.parse.quote(reference_prim, safe='')
        url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/selection/{encoded_prim}"
        headers = {
            'accept': 'application/lightspeed.remix.service+json; version=1.0'
        }

        logging.info(f"Selecting mesh prim at: {url}")
        print(f"Selecting mesh prim at: {url}")

        response = make_request_with_retries(
            'PUT',
            url,
            headers=headers,
            verify=addon_prefs.remix_verify_ssl
        )

        if response and response.status_code in [200, 204]:
            logging.info("Mesh prim selected successfully.")
            return True
        else:
            status = response.status_code if response else 'No Response'
            response_text = response.text if response else 'No Response'
            logging.error(f"Failed to select mesh prim. Status: {status}, Response: {response_text}")
            print(f"Failed to select mesh prim. Status: {status}, Response: {response_text}")
            return False
    except Exception as e:
        logging.error(f"Error selecting mesh prim: {e}")
        print(f"Error selecting mesh prim: {e}")
        return False


def get_actual_mesh_name(mesh_objects):
    try:
        if not mesh_objects:
            return "DefaultMesh"
        return mesh_objects[0].name
    except Exception as e:
        logging.error(f"Error retrieving actual mesh name: {e}")
        print(f"Error retrieving actual mesh name: {e}")
        return "DefaultMesh"

def blender_mat_to_remix(mat_name):
    """
    Convert a Blender material name to a Remix-friendly name.
    For example, replace spaces and periods with underscores.
    """
    return mat_name.replace(" ", "_").replace(".", "_")
    
def handle_special_texture_assignments(self, context, reference_prim, export_data=None):
    """
    [DEFINITIVE V18 - CORRECTED DATA LOOKUP]
    This version fixes the logical flaw where special texture information was stored
    by an (object, material) key but retrieved only by material. This version reorganizes
    the data purely by material, ensuring a correct lookup and assignment.
    """
    addon_prefs = context.preferences.addons[__name__].preferences
    
    try:
        logging.info("--- Starting Special Texture Assignment (Corrected Data Lookup) ---")

        final_mtl_name_map = (export_data or {}).get("material_name_map", {})
        special_texture_info_by_obj_mat = (export_data or {}).get('bake_info', {}).get('special_texture_info', {})

        if not special_texture_info_by_obj_mat:
            logging.info("No special textures to process.")
            return {'FINISHED'}

        # --- THIS IS THE FIX: Reorganize the data ---
        # Create a new dictionary keyed ONLY by the original material name.
        assignments_by_original_mat_name = defaultdict(list)
        for (obj_name, mat_name), texture_list in special_texture_info_by_obj_mat.items():
            for texture_data in texture_list:
                 assignments_by_original_mat_name[mat_name].append(texture_data)
        # --- END OF FIX ---

        textures_for_ingest = []
        ingest_dir_server = addon_prefs.remix_ingest_directory.rstrip('/\\')
        server_textures_output_dir = os.path.join(ingest_dir_server, "textures").replace('\\', '/')

        SPECIAL_TEXTURE_MAP = {
            "HEIGHT": "height_texture",
            "EMISSIVE": "emissive_mask_texture",
            "ANISOTROPY": "anisotropy_texture",
            "TRANSMITTANCE": "transmittance_texture",
        }

        # This loop now correctly builds the list of files to upload
        for mat_name, texture_list in assignments_by_original_mat_name.items():
            for texture_data in texture_list:
                local_path, tex_type = texture_data.get('path'), texture_data.get('type')
                if not (local_path and tex_type and os.path.exists(local_path)):
                    continue
                
                # Add to the upload list and update the server path in our assignment dictionary
                textures_for_ingest.append([local_path, tex_type.upper()])
                base_name = os.path.splitext(os.path.basename(local_path))[0]
                server_path = os.path.join(server_textures_output_dir, f"{base_name}.{tex_type[0].lower()}.rtex.dds").replace('\\', '/')
                texture_data['server_path'] = server_path # Add the final server path back to the dict
                texture_data['usd_input'] = SPECIAL_TEXTURE_MAP.get(tex_type)

        if not textures_for_ingest:
            logging.warning("No valid special textures found to upload.")
            return {'FINISHED'}

        # (The ingestion payload and request can remain the same)
        logging.info(f"Ingesting {len(textures_for_ingest)} total special textures...")
        base_api_url = addon_prefs.remix_export_url.rstrip('/')
        ingest_payload = { "executor": 1, "name": "Material(s)", "context_plugin": { "name": "TextureImporter", "data": { "allow_empty_input_files_list": True, "channel": "Default", "context_name": "ingestcraft", "cook_mass_template": True, "create_context_if_not_exist": True, "create_output_directory_if_missing": True, "data_flows": [{ "channel": "Default", "name": "InOutData", "push_input_data": True, "push_output_data": False }], "default_output_endpoint": "/stagecraft/assets/default-directory", "expose_mass_queue_action_ui": False, "expose_mass_ui": True, "global_progress_value": 0, "hide_context_ui": True, "input_files": [], "output_directory": "", "progress": [0, "Initializing", True] } }, "check_plugins": [ {"name": "MaterialShaders", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllMaterials"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "ignore_not_convertable_shaders": False, "progress": [0, "Initializing", True], "save_on_fix_failure": True, "shader_subidentifiers": {"AperturePBR_Opacity": ".*"}}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_on_exit": False}, "name": "CurrentStage"}}, {"name": "ConvertToDDS", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllShaders"}], "resultor_plugins": [{"data": {"channel": "cleanup_files", "cleanup_input": True, "cleanup_output": False, "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True]}, "name": "FileCleanup"}], "data": {"channel": "Default", "conversion_args": {"inputs:diffuse_texture": {"args": ["--format", "bc7", "--mip-gamma-correct"]}, "inputs:emissive_mask_texture": {"args": ["--format", "bc7", "--mip-gamma-correct"]}, "inputs:height_texture": {"args": ["--format", "bc4", "--no-mip-gamma-correct", "--mip-filter", "max"]}}, "cook_mass_template": False, "data_flows": [{"channel": "cleanup_files", "name": "InOutData", "push_input_data": True, "push_output_data": True}, {"channel": "write_metadata", "name": "InOutData", "push_input_data": False, "push_output_data": True}, {"channel": "ingestion_output", "name": "InOutData", "push_input_data": False, "push_output_data": True}], "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True, "suffix": ".rtex.dds"}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_on_exit": False}, "name": "CurrentStage"}}, ], "resultor_plugins": [{"name": "FileMetadataWritter", "data": {"channel": "write_metadata", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True]}}] }
        ingest_payload["context_plugin"]["data"]["input_files"] = textures_for_ingest
        ingest_payload["context_plugin"]["data"]["output_directory"] = server_textures_output_dir
        ingest_response = make_request_with_retries('POST', f"{base_api_url}/material", json_payload=ingest_payload, verify=addon_prefs.remix_verify_ssl)
        if not ingest_response or ingest_response.status_code >= 400: return {'CANCELLED'}

        stagecraft_api_url_base = addon_prefs.remix_server_url.rstrip('/')
        all_inputs_url = f"{stagecraft_api_url_base}/textures/?selection=true&filter_session_prims=false&exists=true"
        all_inputs_response = make_request_with_retries('GET', all_inputs_url, headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'}, verify=addon_prefs.remix_verify_ssl)
        if not all_inputs_response or all_inputs_response.status_code != 200: return {'CANCELLED'}

        server_mat_name_to_prim_map = {}
        for prim_path, _ in all_inputs_response.json().get("textures", []):
            try:
                if "/Looks/" in prim_path:
                    base_shader_path, _ = prim_path.rsplit('.inputs:', 1)
                    material_name_from_server = base_shader_path.rsplit('/Looks/', 1)[-1].split('/')[0]
                    if material_name_from_server not in server_mat_name_to_prim_map:
                        server_mat_name_to_prim_map[material_name_from_server] = base_shader_path
            except ValueError: continue
        
        # This final lookup loop is now correct
        final_put_payload_list = []
        for original_blender_name, assignments_list in assignments_by_original_mat_name.items():
            final_exported_name = final_mtl_name_map.get(original_blender_name)
            if not final_exported_name:
                logging.warning(f"  Could not find a temporary name mapping for '{original_blender_name}'.")
                continue

            sanitized_name_to_find = final_exported_name.replace('-', '_')
            server_shader_prim = server_mat_name_to_prim_map.get(sanitized_name_to_find)
            
            if server_shader_prim:
                logging.info(f"  SUCCESS: Matched Blender material '{original_blender_name}' to server prim '{server_shader_prim}' using sanitized name '{sanitized_name_to_find}'.")
                for assignment in assignments_list:
                    if assignment.get('usd_input') and assignment.get('server_path'):
                        final_put_payload_list.append([f"{server_shader_prim}.inputs:{assignment['usd_input']}", assignment['server_path']])
            else:
                 logging.warning(f"  FAILED: Could not find server prim for sanitized name '{sanitized_name_to_find}'. Available server names: {list(server_mat_name_to_prim_map.keys())}")

        if not final_put_payload_list:
            logging.warning("Assignment payload is empty after matching. No special textures will be assigned.")
            return {'FINISHED'}

        update_texture_connection_url = f"{stagecraft_api_url_base}/textures/"
        put_payload = {"force": False, "textures": final_put_payload_list}
        put_response = make_request_with_retries('PUT', update_texture_connection_url, json_payload=put_payload, headers={"accept": "application/lightspeed.remix.service+json; version=1.0", "Content-Type": "application/lightspeed.remix.service+json; version=1.0"}, verify=addon_prefs.remix_verify_ssl)
        
        if not put_response or put_response.status_code >= 400: return {'CANCELLED'}

        logging.info("--- Finished Special Texture Assignment Successfully ---")
        return {'FINISHED'}

    except Exception as e:
        logging.error(f"A critical error occurred: {e}", exc_info=True)
        return {'CANCELLED'}
        
def trim_prim_path(prim_path, segments_to_trim=0):
    try:
        segments = prim_path.strip('/').split('/')
        if segments_to_trim > 0:
            trimmed_segments = segments[:-segments_to_trim] if len(segments) > segments_to_trim else []
            trimmed_path = '/' + '/'.join(trimmed_segments)
        else:
            ref_index = None
            for i, segment in enumerate(segments):
                if segment.startswith('ref_'):
                    ref_index = i
                    break
            if ref_index is not None:
                trimmed_segments = segments[:ref_index + 1]
                trimmed_path = '/' + '/'.join(trimmed_segments)
            else:
                trimmed_path = prim_path
                logging.warning(f"No 'ref_' segment found in prim path: {prim_path}. Returning original path.")
                print(f"No 'ref_' segment found in prim path: {prim_path}. Returning original path.")

        logging.debug(f"Trimmed prim path from '{prim_path}' to '{trimmed_path}'")
        print(f"Trimmed prim path from '{prim_path}' to '{trimmed_path}'")
        return trimmed_path
    except Exception as e:
        logging.error(f"Error trimming prim path '{prim_path}': {e}")
        print(f"Error trimming prim path '{prim_path}': {e}")
        return prim_path

def _get_base_name_and_suffix_parts(obj_name):
    # Pattern 1: Handles "name_S1.S2" (e.g., inst_62EC3A6022F09C50_0.001)
    match_custom_extended = re.fullmatch(r'(.+?)_(\d+)\.(\d+)$', obj_name)
    if match_custom_extended:
        base, p1_str, p2_str = match_custom_extended.groups()
        try:
            return base, (int(p1_str), int(p2_str))
        except ValueError:
            pass 

    # Pattern 2: Handles "name.S2" (e.g., inst_Cool.001)
    match_blender_suffix = re.fullmatch(r'(.+?)\.(\d+)$', obj_name)
    if match_blender_suffix:
        base, num_str = match_blender_suffix.groups()
        try:
            return base, (int(num_str),)
        except ValueError:
            pass

    # Pattern 3: Handles "name_S1" (e.g., inst_62EC3A6022F09C50_0)
    match_custom_simple = re.fullmatch(r'(.+?)_(\d+)$', obj_name)
    if match_custom_simple:
        base, p1_str = match_custom_simple.groups()
        try:
            return base, (int(p1_str),)
        except ValueError:
            pass
    
    return obj_name, None

def _perform_transform_application_phase_module(context, scene_to_process):
    processed_count = 0
    logging.info(f"Starting BATCH transform_apply phase for scene: '{scene_to_process.name if scene_to_process else 'None'}'.")
    if not scene_to_process:
        logging.error("Transform phase: scene_to_process is None. Aborting.")
        return {'transformed': 0}

    original_window_scene = context.window.scene
    original_active_object_in_original_scene = context.active_object
    original_selected_objects_in_original_scene = list(context.selected_objects)
    original_mode = 'OBJECT'
    if original_window_scene == context.scene:
        if context.object and hasattr(context.object, 'mode'):
            original_mode = context.object.mode
        else:
            original_mode = context.mode

    try:
        if context.window.scene != scene_to_process:
            context.window.scene = scene_to_process
            logging.info(f"Transform phase: Temporarily set active window scene to '{scene_to_process.name}'.")
    
        if not scene_to_process.view_layers or not context.view_layer:
            logging.error(f"Transform phase: Scene '{scene_to_process.name}' has no view layers or no active context view layer. Aborting.")
            return {'transformed': 0}
        target_view_layer = context.view_layer
        logging.info(f"Transform phase: Using view layer '{target_view_layer.name}' for scene '{scene_to_process.name}'.")

        if context.mode != 'OBJECT':
            current_active = target_view_layer.objects.active
            if not current_active and scene_to_process.objects:
                candidate_active = next((obj for obj in scene_to_process.objects if obj.type in {'MESH', 'EMPTY', 'CURVE', 'ARMATURE'}), None)
                if candidate_active: target_view_layer.objects.active = candidate_active
    
            if bpy.ops.object.mode_set.poll():
                try: bpy.ops.object.mode_set(mode='OBJECT')
                except RuntimeError as e_mode:
                    logging.error(f"Transform phase: Could not switch to OBJECT mode in '{scene_to_process.name}': {e_mode}. Aborting.", exc_info=False)
                    return {'transformed': 0}
            else:
                logging.error(f"Transform phase: Cannot poll mode_set to OBJECT in '{scene_to_process.name}'. Active: {target_view_layer.objects.active}. Aborting.")
                return {'transformed': 0}
            if not target_view_layer.objects.active and current_active and current_active.name in target_view_layer.objects:
                target_view_layer.objects.active = current_active


        if bpy.ops.object.select_all.poll():
            bpy.ops.object.select_all(action='DESELECT')

        objects_to_transform_in_batch = []
        total_eligible_objects = 0
        for obj in scene_to_process.objects:
            if obj.type in {'MESH', 'CURVE', 'FONT', 'SURFACE', 'EMPTY', 'ARMATURE'}:
                if obj.type == 'EMPTY' or (obj.data is not None):
                    total_eligible_objects += 1
                    if obj.name in target_view_layer.objects:
                        try:
                            obj.select_set(True)
                            objects_to_transform_in_batch.append(obj)
                        except RuntimeError as e_select_vl:
                            logging.warning(f"Transform phase: Could not select object '{obj.name}' in view layer '{target_view_layer.name}': {e_select_vl}")
                    else:
                        logging.warning(f"Transform phase: Object '{obj.name}' in scene '{scene_to_process.name}' but not in its active view layer '{target_view_layer.name}'. Cannot select for transform.")
    
        if not objects_to_transform_in_batch:
            logging.info(f"Transform phase: No objects were selected in '{scene_to_process.name}' for batch transform (Total eligible: {total_eligible_objects}).")
            return {'transformed': 0}

        logging.info(f"Transform phase: Selected {len(objects_to_transform_in_batch)} objects in '{scene_to_process.name}' for batch transform.")
    
        current_active_in_target_vl = target_view_layer.objects.active
        if not current_active_in_target_vl or current_active_in_target_vl not in objects_to_transform_in_batch:
            if objects_to_transform_in_batch:
                target_view_layer.objects.active = objects_to_transform_in_batch[0]
        logging.info(f"Transform phase: Active object for batch transform in '{scene_to_process.name}': {target_view_layer.objects.active.name if target_view_layer.objects.active else 'None'}")

        if objects_to_transform_in_batch and target_view_layer.objects.active:
            logging.info(f" BATCH APPLY: Applying Rotation & Scale to {len(context.selected_objects)} selected objects in '{scene_to_process.name}'. Active: {context.active_object.name if context.active_object else 'None'}") # type: ignore
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True, properties=False)
    
            for obj_verify in objects_to_transform_in_batch:
                if obj_verify.data and hasattr(obj_verify.data, 'update'): obj_verify.data.update()
                rotation_applied = all(abs(angle) < 0.0001 for angle in obj_verify.rotation_euler)
                scale_applied = all(abs(s - 1.0) < 0.0001 for s in obj_verify.scale)
                if rotation_applied and scale_applied:
                    logging.debug(f"  VERIFIED BATCH: Transforms applied for {obj_verify.name}")
                    processed_count += 1
                else:
                    logging.warning(f"  VERIFICATION FAILED BATCH for {obj_verify.name}: Rot {obj_verify.rotation_euler}, Scale {obj_verify.scale}")
        else:
            logging.warning(f" BATCH APPLY: Skipped due to no selected objects or no active object in '{scene_to_process.name}' for transform_apply.")

        if bpy.ops.object.select_all.poll():
            bpy.ops.object.select_all(action='DESELECT')
        logging.info(f" BATCH APPLY: Done. Verified {processed_count} objects successfully transformed in '{scene_to_process.name}'.")

    except Exception as e_transform:
        logging.error(f"Transform phase: Error during transform application in '{scene_to_process.name}': {e_transform}", exc_info=True)
    finally:
        current_scene_name_at_finally_start = context.window.scene.name
        if context.window.scene != original_window_scene:
            context.window.scene = original_window_scene
            logging.info(f"Transform phase: Restored active window scene to '{original_window_scene.name}' (was '{current_scene_name_at_finally_start}').")
    
        if bpy.ops.object.select_all.poll():
            bpy.ops.object.select_all(action='DESELECT')
    
        for obj_ref in original_selected_objects_in_original_scene:
            if obj_ref and obj_ref.name in original_window_scene.objects:
                scene_obj_to_select = original_window_scene.objects.get(obj_ref.name)
                if scene_obj_to_select and scene_obj_to_select.name in context.view_layer.objects:
                    try: scene_obj_to_select.select_set(True)
                    except RuntimeError as e_select:
                        logging.warning(f"Could not re-select object '{scene_obj_to_select.name}' in '{original_window_scene.name}': {e_select}")
    
        if original_active_object_in_original_scene and \
            original_active_object_in_original_scene.name in original_window_scene.objects:
            scene_obj_to_activate = original_window_scene.objects.get(original_active_object_in_original_scene.name)
            if scene_obj_to_activate and scene_obj_to_activate.name in context.view_layer.objects:
                try: context.view_layer.objects.active = scene_obj_to_activate
                except Exception as e_active:
                    logging.warning(f"Could not restore active object to '{scene_obj_to_activate.name}' in '{original_window_scene.name}': {e_active}")
        elif context.view_layer.objects.active is not None :
            context.view_layer.objects.active = None
            logging.debug(f"Original active object not restored in '{original_window_scene.name}'; active object cleared.")

        current_context_mode_final = context.mode
        if current_context_mode_final != original_mode:
            can_set_original_mode = (original_mode == 'OBJECT') or (context.view_layer.objects.active is not None)
    
            if can_set_original_mode and bpy.ops.object.mode_set.poll():
                try: bpy.ops.object.mode_set(mode=original_mode)
                except RuntimeError as e_mode_restore_final_ctx:
                    logging.warning(f"Transform phase (finally): Could not restore mode in '{original_window_scene.name}' to '{original_mode}': {e_mode_restore_final_ctx}")
            elif not can_set_original_mode:
                logging.warning(f"Transform phase (finally): Conditions not met to restore mode to '{original_mode}' in '{original_window_scene.name}'. Mode remains '{current_context_mode_final}'.")

    logging.info(f"Finished BATCH transform_apply phase. Processed {processed_count} objects in '{scene_to_process.name if scene_to_process else 'None'}'.")
    return {'transformed': processed_count}

def _perform_object_transfer_phase_module(context, main_scene, source_scene):
    """
    Batch-transfer all objects from source_scene into main_scene.collection.
    Unlink each object from any collections except the target, then link them all at once.
    """
    transferred_count = 0

    # Ensure main scene has a master collection
    main_collection = main_scene.collection
    if main_collection is None:
        logging.error(f"Object transfer: Main scene '{main_scene.name}' has no master collection.")
        return {'transferred_count': 0}

    # Gather all objects in the source scene
    objects_to_transfer = list(source_scene.objects)
    logging.info(f"Object transfer: Preparing to move {len(objects_to_transfer)} objects from '{source_scene.name}' to '{main_scene.name}'.")

    # -- 1. Batch-unlink: for each object, remove it from every collection except the main target
    for obj in objects_to_transfer:
        # Copy the list because we're modifying it during iteration
        for coll in list(obj.users_collection):
            if coll != main_collection:
                try:
                    coll.objects.unlink(obj)
                except Exception as e:
                    logging.warning(f"Object transfer: could not unlink {obj.name} from {coll.name}: {e}")

    # -- 2. Batch-link: link each object to the main scene collection if not already linked
    for obj in objects_to_transfer:
        if obj.name not in main_collection.objects:
            try:
                main_collection.objects.link(obj)
                transferred_count += 1
            except Exception as e:
                logging.error(f"Object transfer: could not link {obj.name} to {main_collection.name}: {e}")

    # -- 3. Refresh view layer and scene tags
    if main_scene.view_layers:
        # Update the first view layer (or whichever is active)
        main_scene.view_layers[0].update()
    main_scene.update_tag()

    logging.info(f"Finished object transfer. Transferred {transferred_count} objects from '{source_scene.name}' to '{main_scene.name}'.")
    return {'transferred_count': transferred_count}

def _perform_duplicate_cleanup_phase_module(context, scene_to_clean):
    logging.info(f"Starting combined cleanup in scene: '{scene_to_clean.name}'")

    deleted_objects_count_inst = 0 
    deleted_objects_mesh_pattern = 0 

    original_window_scene = context.window.scene
    original_active_object_in_original_scene = context.active_object 
    original_selected_objects_in_original_scene = list(context.selected_objects)

    original_mode = 'OBJECT' 
    if original_window_scene == context.scene: 
        if context.object and hasattr(context.object, 'mode'):
            original_mode = context.object.mode 
        elif context.mode: 
            original_mode = context.mode

    try: 
        if context.window.scene != scene_to_clean:
            context.window.scene = scene_to_clean
            logging.debug(f"Cleanup phase: Switched active window scene to '{scene_to_clean.name}'.")

        if context.mode != 'OBJECT':
            active_obj_for_mode_set = context.view_layer.objects.active 
            if not active_obj_for_mode_set and scene_to_clean.objects:
                candidate_active = next((obj for obj in scene_to_clean.objects if obj.type in {'MESH', 'CURVE', 'EMPTY', 'ARMATURE'}), None)
                if candidate_active and candidate_active.name in context.view_layer.objects: 
                    context.view_layer.objects.active = candidate_active
            
            if bpy.ops.object.mode_set.poll(): 
                try: 
                    bpy.ops.object.mode_set(mode='OBJECT')
                    logging.debug(f"Cleanup phase: Switched to OBJECT mode in '{scene_to_clean.name}'.")
                except RuntimeError as e: 
                    logging.warning(f"Cleanup phase: Could not set OBJECT mode in '{scene_to_clean.name}': {e}")
            else:
                logging.warning(f"Cleanup phase: Cannot poll bpy.ops.object.mode_set to OBJECT in '{scene_to_clean.name}'. Mode remains {context.mode}.")
    
        logging.info(f"Starting 'inst_' object cleanup in '{scene_to_clean.name}'.")
        if bpy.ops.object.select_all.poll():
            bpy.ops.object.select_all(action='DESELECT')

        objects_to_delete_inst_collector = [] 
        objects_to_keep_inst_collector = []    

        grouped_by_base_inst = collections.defaultdict(list)
        prefix_to_scan_inst = "inst_"
        all_inst_objects_in_scene = [obj for obj in scene_to_clean.objects if obj.name.startswith(prefix_to_scan_inst)]

        for obj_inst in all_inst_objects_in_scene: 
            base_name_part, suffix_key_part = _get_base_name_and_suffix_parts(obj_inst.name)
            # logging.debug(f"Parsing inst_ name: '{obj_inst.name}' -> base: '{base_name_part}', suffix_key: {suffix_key_part}") # Reduced verbosity
            grouped_by_base_inst[base_name_part].append({
                'obj': obj_inst, 
                'name': obj_inst.name, 
                'suffix_key': suffix_key_part
            })

        for base_name_part, obj_infos_list in grouped_by_base_inst.items():
            plain_originals = [info for info in obj_infos_list if info['suffix_key'] is None]
            suffixed_duplicates = [info for info in obj_infos_list if info['suffix_key'] is not None]
        
            object_to_keep_info_dict = None 
            current_group_objects_to_delete = [] 

            if plain_originals:
                plain_originals.sort(key=lambda x: x['name']) 
                object_to_keep_info_dict = plain_originals[0] 
                current_group_objects_to_delete.extend(p_info['obj'] for p_info in plain_originals[1:])
                current_group_objects_to_delete.extend(s_info['obj'] for s_info in suffixed_duplicates)
            elif suffixed_duplicates: 
                suffixed_duplicates.sort(key=lambda x: (x['suffix_key'], x['name'])) # type: ignore
                object_to_keep_info_dict = suffixed_duplicates[0] 
                current_group_objects_to_delete.extend(s_info['obj'] for s_info in suffixed_duplicates[1:])
            else: 
                if obj_infos_list: 
                        logging.warning(f"'inst_' cleanup for base '{base_name_part}': Group with {len(obj_infos_list)} items had no plain or suffixed. Fallback: keep first by name.")
                        if len(obj_infos_list) > 0: 
                            obj_infos_list.sort(key=lambda x: x['name'])
                            object_to_keep_info_dict = obj_infos_list[0]
                            current_group_objects_to_delete.extend(info['obj'] for info in obj_infos_list[1:])

            if object_to_keep_info_dict:
                objects_to_keep_inst_collector.append(object_to_keep_info_dict['obj'])
                # logging.debug(f"'inst_' cleanup for base '{base_name_part}': Keeping '{object_to_keep_info_dict['name']}'...") # Reduced verbosity
            # else: # Reduced verbosity
                # logging.debug(f"'inst_' cleanup for base '{base_name_part}': No object chosen to keep...")
            objects_to_delete_inst_collector.extend(current_group_objects_to_delete)

        kept_inst_objects_set = set(objects_to_keep_inst_collector) 
        unique_objects_to_delete_inst_final = list(set(
            obj for obj in objects_to_delete_inst_collector 
            if obj and obj.name in scene_to_clean.objects and obj not in kept_inst_objects_set 
        ))
    
        if unique_objects_to_delete_inst_final:
            logging.info(f"'inst_' cleanup: Identified {len(unique_objects_to_delete_inst_final)} unique 'inst_' objects for deletion.")
            if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')
            active_obj_inst_del = context.view_layer.objects.active
            active_obj_inst_del_cleared = False
            if active_obj_inst_del and active_obj_inst_del in unique_objects_to_delete_inst_final:
                context.view_layer.objects.active = None
                active_obj_inst_del_cleared = True

            selected_for_deletion_count = 0
            for obj_to_del in unique_objects_to_delete_inst_final: 
                if obj_to_del.name in context.view_layer.objects : 
                    try:
                        obj_to_del.select_set(True); selected_for_deletion_count +=1
                    except RuntimeError as e_select: logging.warning(f"Could not select '{obj_to_del.name}' for inst_ deletion: {e_select}")
                else: logging.warning(f"'{obj_to_del.name}' for inst_ deletion not in view layer.")
        
            if selected_for_deletion_count > 0: 
                bpy.ops.object.delete(); deleted_objects_count_inst = selected_for_deletion_count 
                logging.info(f"'inst_' cleanup: Batch deleted {deleted_objects_count_inst} objects.")
            else: logging.info("'inst_' cleanup: No 'inst_' objects ultimately selected for deletion.")
        
            if active_obj_inst_del_cleared: 
                if active_obj_inst_del and (active_obj_inst_del.name not in scene_to_clean.objects): 
                    if scene_to_clean.objects: 
                        new_active_candidate = next((obj for obj in scene_to_clean.objects if obj.type in {'MESH', 'EMPTY', 'ARMATURE'}), None)
                        if new_active_candidate and new_active_candidate.name in context.view_layer.objects:
                                context.view_layer.objects.active = new_active_candidate
                elif active_obj_inst_del and active_obj_inst_del.name in scene_to_clean.objects: 
                    if active_obj_inst_del.name in context.view_layer.objects :
                        context.view_layer.objects.active = active_obj_inst_del
        else: logging.info("'inst_' cleanup: No 'inst_' objects scheduled for deletion.")

        final_kept_inst_objects_set = { obj for obj in objects_to_keep_inst_collector if obj.name in scene_to_clean.objects }
        logging.info(f"After 'inst_' cleanup, {len(final_kept_inst_objects_set)} 'inst_' objects remain for mesh.#### cleanup reference.")
    
        logging.info(f"Starting 'mesh.####' OBJECT cleanup in scene: '{scene_to_clean.name}'.")
        objects_to_delete_mesh_pattern_collector = []
        if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')

        all_mesh_dot_pattern_objects_in_scene = [ obj for obj in scene_to_clean.objects if obj.type == 'MESH' and re.fullmatch(r"mesh\.(\d+)", obj.name) ]

        if all_mesh_dot_pattern_objects_in_scene:
            for mesh_obj in all_mesh_dot_pattern_objects_in_scene:
                is_used_or_parented_safely = False
                if mesh_obj.parent and mesh_obj.parent in final_kept_inst_objects_set:
                    is_used_or_parented_safely = True; # logging.debug(f"Mesh '{mesh_obj.name}' KEPT: parent is kept inst.")
                if not is_used_or_parented_safely:
                    for inst_obj in final_kept_inst_objects_set: 
                        if inst_obj.type == 'EMPTY': 
                            if inst_obj.instance_type == 'OBJECT' and inst_obj.instance_object == mesh_obj: is_used_or_parented_safely = True; break
                            if inst_obj.instance_type == 'COLLECTION' and inst_obj.instance_collection and mesh_obj.name in inst_obj.instance_collection.all_objects: is_used_or_parented_safely = True; break
                if not is_used_or_parented_safely and mesh_obj.parent:
                    parent_obj = mesh_obj.parent
                    if parent_obj.name in scene_to_clean.objects: 
                        is_parent_kept_inst = parent_obj in final_kept_inst_objects_set
                        is_parent_mesh_dot = parent_obj.type == 'MESH' and re.fullmatch(r"mesh\.(\d+)", parent_obj.name)
                        if not is_parent_kept_inst and not is_parent_mesh_dot: is_used_or_parented_safely = True; # logging.debug(f"Mesh '{mesh_obj.name}' KEPT: parent is regular.")
                if not is_used_or_parented_safely and mesh_obj.data and mesh_obj.data.users > 1:
                    for user_obj in scene_to_clean.objects: 
                        if user_obj.data == mesh_obj.data and user_obj != mesh_obj:
                            is_user_kept_inst = user_obj in final_kept_inst_objects_set
                            is_user_mesh_dot = user_obj.type == 'MESH' and re.fullmatch(r"mesh\.(\d+)", user_obj.name)
                            is_user_deleted_inst = user_obj.name.startswith(prefix_to_scan_inst) and not is_user_kept_inst
                            if not is_user_mesh_dot and not is_user_deleted_inst : is_used_or_parented_safely = True; break # logging.debug(f"Mesh '{mesh_obj.name}' KEPT: data used by other significant obj.")
                if not is_used_or_parented_safely:
                    is_in_root = scene_to_clean.collection and mesh_obj.name in scene_to_clean.collection.objects
                    if mesh_obj.parent is None and (is_in_root or not any(coll == scene_to_clean.collection for coll in mesh_obj.users_collection)): # If unparented & in root, or unparented & not in any other meaningful collection part of main scene structure (heuristic)
                        objects_to_delete_mesh_pattern_collector.append(mesh_obj) # logging.info(f"Unused 'mesh.####' object '{mesh_obj.name}' scheduled for deletion.")

            if objects_to_delete_mesh_pattern_collector:
                unique_objects_to_delete_mesh_final = list(set( obj for obj in objects_to_delete_mesh_pattern_collector if obj and obj.name in scene_to_clean.objects ))
                if unique_objects_to_delete_mesh_final:
                    logging.info(f"'mesh.####' cleanup: Identified {len(unique_objects_to_delete_mesh_final)} objects for deletion.")
                    if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')
                    active_obj_mesh_del = context.view_layer.objects.active; active_obj_mesh_del_cleared = False
                    if active_obj_mesh_del and active_obj_mesh_del in unique_objects_to_delete_mesh_final: context.view_layer.objects.active = None; active_obj_mesh_del_cleared = True
                    
                    selected_for_mesh_del_count = 0
                    for obj_to_del in unique_objects_to_delete_mesh_final:
                        if obj_to_del.name in context.view_layer.objects: obj_to_del.select_set(True); selected_for_mesh_del_count +=1
                        else: logging.warning(f"'{obj_to_del.name}' for mesh.#### deletion not in view layer.")
                    
                    if selected_for_mesh_del_count > 0 and context.selected_objects: 
                        bpy.ops.object.delete(); deleted_objects_mesh_pattern = selected_for_mesh_del_count
                        logging.info(f"'mesh.####' cleanup: Batch deleted {deleted_objects_mesh_pattern} objects.")
                        if active_obj_mesh_del_cleared: 
                            if active_obj_mesh_del and (active_obj_mesh_del.name not in scene_to_clean.objects): 
                                if scene_to_clean.objects: 
                                    new_active = next((o for o in scene_to_clean.objects if o.type in {'MESH', 'EMPTY'}), None)
                                    if new_active and new_active.name in context.view_layer.objects: context.view_layer.objects.active = new_active
                            elif active_obj_mesh_del and active_obj_mesh_del.name in scene_to_clean.objects and active_obj_mesh_del.name in context.view_layer.objects:
                                context.view_layer.objects.active = active_obj_mesh_del
                    else: logging.info("'mesh.####' cleanup: No objects ultimately selected for deletion.")
                else: logging.info("'mesh.####' cleanup: No objects for deletion after filtering.")
            else: logging.info("'mesh.####' cleanup: No candidates initially identified.")

    except Exception as e_cleanup_main: 
        logging.error(f"Error during main cleanup phase in '{scene_to_clean.name}': {e_cleanup_main}", exc_info=True)
    finally: 
        current_scene_name_at_finally = context.window.scene.name
        if context.window.scene != original_window_scene: context.window.scene = original_window_scene; # logging.debug(f"Cleanup: Restored window scene to '{original_window_scene.name}'.")
        if bpy.ops.object.select_all.poll(): bpy.ops.object.select_all(action='DESELECT')
        for obj_ref in original_selected_objects_in_original_scene: 
            if obj_ref and obj_ref.name in original_window_scene.objects: 
                s_obj = original_window_scene.objects.get(obj_ref.name)
                if s_obj and s_obj.name in context.view_layer.objects: 
                    try: s_obj.select_set(True)
                    except RuntimeError: pass
        o_active_name = original_active_object_in_original_scene.name if original_active_object_in_original_scene else None
        if o_active_name and o_active_name in original_window_scene.objects:
            s_active = original_window_scene.objects.get(o_active_name)
            if s_active and s_active.name in context.view_layer.objects: 
                try: context.view_layer.objects.active = s_active
                except Exception: pass
        elif context.view_layer.objects.active is not None: context.view_layer.objects.active = None 
        
        final_mode = context.mode 
        if final_mode != original_mode:
            can_set_orig = (original_mode == 'OBJECT') or (context.view_layer.objects.active is not None) 
            if can_set_orig and bpy.ops.object.mode_set.poll():
                try: bpy.ops.object.mode_set(mode=original_mode)
                except RuntimeError : pass # logging.warning(f"Cleanup (finally): Could not restore mode to '{original_mode}'.")

    logging.info(f"Finished cleanup for scene '{scene_to_clean.name}'. Deleted {deleted_objects_count_inst} 'inst_', {deleted_objects_mesh_pattern} 'mesh.####'.")
    return {'deleted_objects_inst': deleted_objects_count_inst, 'deleted_objects_mesh_pattern': deleted_objects_mesh_pattern}
  
def _stable_repr(value):
    """Creates a stable, repeatable string representation for various data types."""
    if isinstance(value, (int, str, bool)):
        return str(value)
    elif isinstance(value, float):
        # Format float to a consistent number of decimal places
        return f"{value:.8f}"
    elif isinstance(value, (bpy.types.bpy_prop_array, tuple, list)):
        if not value: return '[]'
        try:
            # Check if all items are numeric for consistent formatting
            if all(isinstance(x, (int, float)) for x in value):
                return '[' + ','.join([f"{item:.8f}" if isinstance(item, float) else str(item) for item in value]) + ']'
        except TypeError:
            pass
        # Fallback for mixed or non-numeric types
        return repr(value)
    elif hasattr(value, 'to_list'):
        # For mathutils types like Vector, Color, Quaternion
        list_val = value.to_list()
        if not list_val: return '[]'
        return '[' + ','.join([f"{item:.8f}" if isinstance(item, float) else str(item) for item in list_val]) + ']'
    elif value is None:
        return 'None'
    else:
        # Generic fallback for any other type
        return repr(value)

def _hash_image(img, image_hash_cache):
    """
    [DEFINITIVE V2 - UDIM AWARE]
    Calculates a hash for an image datablock. It is now fully UDIM-aware,
    iterating through all existing tile files and hashing their content
    to ensure that changes to any tile will correctly invalidate the cache.
    """
    if not img:
        return "NO_IMAGE_DATABLOCK"

    cache_key = img.name_full if hasattr(img, 'name_full') else str(id(img))
    if image_hash_cache is not None and cache_key in image_hash_cache:
        return image_hash_cache[cache_key]

    calculated_digest = None
    hasher = hashlib.md5()

    try:
        # --- NEW: UDIM HASHING LOGIC ---
        if img.source == 'TILED':
            logging.debug(f"  > Hashing UDIM set for '{img.name}'...")
            found_any_tiles = False
            # Sort tiles by number for a consistent hash order
            sorted_tiles = sorted(img.tiles, key=lambda t: t.number)
            
            for tile in sorted_tiles:
                # Construct the real path for each tile file
                tile_path = abspath(img.filepath_raw.replace('<UDIM>', str(tile.number)))
                if os.path.isfile(tile_path):
                    found_any_tiles = True
                    # Add the tile number to the hash to account for swaps
                    hasher.update(str(tile.number).encode('utf-8'))
                    # Add the content of the tile file to the hash
                    with open(tile_path, "rb") as f:
                        buf = f.read(131072) # Read first 128kb is enough
                        hasher.update(buf)
                else:
                    # If a tile is missing, we still add its number to the hash
                    # to differentiate from a set that doesn't have this tile defined.
                    hasher.update(f"missing_{tile.number}".encode('utf-8'))

            if found_any_tiles:
                calculated_digest = hasher.hexdigest()
            else:
                logging.warning(f"  > UDIM set '{img.name}' has no valid tile files on disk.")
                # Fall through to the fallback hash method if no tiles were found

        # --- EXISTING LOGIC FOR STANDARD TEXTURES ---
        if calculated_digest is None:
            if hasattr(img, 'packed_file') and img.packed_file and hasattr(img.packed_file, 'data') and img.packed_file.data:
                data_to_hash = bytes(img.packed_file.data[:131072])
                hasher.update(data_to_hash)
                calculated_digest = hasher.hexdigest()
            
            elif hasattr(img, 'filepath_raw') and img.filepath_raw:
                resolved_abs_path = abspath(img.filepath_raw)
                if os.path.isfile(resolved_abs_path):
                    with open(resolved_abs_path, "rb") as f:
                        data_from_file = f.read(131072)
                    hasher.update(data_from_file)
                    calculated_digest = hasher.hexdigest()

        # --- FALLBACK FOR GENERATED OR INVALID TEXTURES ---
        if calculated_digest is None:
            fallback_data = f"FALLBACK|{getattr(img, 'name_full', 'N/A')}|{getattr(img, 'source', 'N/A')}"
            hasher.update(fallback_data.encode('utf-8'))
            calculated_digest = hasher.hexdigest()

    except Exception as e:
        logging.error(f"[_hash_image Error] Hashing failed for '{img.name}': {e}", exc_info=True)
        # Ensure a failsafe hash is always returned
        fallback_data = f"ERROR_FALLBACK|{getattr(img, 'name_full', 'N/A')}"
        hasher.update(fallback_data.encode('utf-8'))
        calculated_digest = hasher.hexdigest()

    if image_hash_cache is not None:
        image_hash_cache[cache_key] = calculated_digest

    return calculated_digest

def _ensure_image_uuids(context):
    """
    [DEFINITIVE UUID TAGGING]
    Iterates through all image datablocks in the current blend file and assigns a
    unique, persistent UUID to a custom property if it doesn't already have one.
    This provides a stable identifier for tracking images across processes.
    """
    logging.info("Ensuring all image datablocks have a persistent UUID...")
    for image in bpy.data.images:
        if 'remix_bake_uuid' not in image:
            image['remix_bake_uuid'] = str(uuid.uuid4())
    logging.info("UUID tagging complete.")
    
def _find_bsdf_and_output_nodes(node_tree):
    """Finds the active Principled BSDF and Material Output nodes."""
    bsdf_node = next((n for n in node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
    output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
    if not output_node:
        output_node = next((n for n in node_tree.nodes if n.type == 'OUTPUT_MATERIAL'), None)
    return bsdf_node, output_node

def _find_universal_decal_mixer(current_node, end_node, visited_nodes):
    """Recursively searches backwards from a starting node to find a Mix Shader."""
    if current_node in visited_nodes or current_node == end_node:
        return None
    visited_nodes.add(current_node)

    if current_node.type == 'MIX_SHADER':
        return (current_node, None)

    if current_node.type == 'GROUP' and current_node.node_tree:
        group_tree = current_node.node_tree
        internal_output = next((n for n in group_tree.nodes if n.type == 'GROUP_OUTPUT' and n.is_active_output), None)
        if internal_output:
            shader_input = next((s for s in internal_output.inputs if s.type == 'SHADER' and s.is_linked), None)
            if shader_input:
                found_result = _find_universal_decal_mixer(shader_input.links[0].from_node, end_node, visited_nodes)
                if found_result:
                    found_node, _ = found_result
                    return (found_node, current_node)

    next_input = next((inp for inp in current_node.inputs if inp.type == 'SHADER' and inp.is_linked), None)
    if next_input:
        return _find_universal_decal_mixer(next_input.links[0].from_node, end_node, visited_nodes)
    
    return None

def _material_has_decal_setup(mat):
    """Checks if a material has a decal setup (a Mix Shader between BSDF and output)."""
    if not mat or not mat.use_nodes or not mat.node_tree:
        return False
    
    nt = mat.node_tree
    bsdf_node, active_output_node = _find_bsdf_and_output_nodes(nt)

    if bsdf_node and active_output_node and active_output_node.inputs['Surface'].is_linked:
        start_node = active_output_node.inputs['Surface'].links[0].from_node
        found_decal_info = _find_universal_decal_mixer(start_node, bsdf_node, set())
        return found_decal_info is not None
        
    return False

def get_material_hash(mat, obj=None, material_slot_index=None, force=True, image_hash_cache=None, bake_method='EMIT_HIJACK', ignore_mesh_context=False):
    """
    [PRODUCTION VERSION - HYBRID HASHING] Calculates a highly detailed hash.
    Includes a switch to completely ignore all mesh context (including UVs) for
    the most aggressive caching, controlled by the 'ignore_mesh_context' parameter.
    """
    HASH_VERSION = "v_HYBRID_UV_AWARE_11"

    if not mat:
        return None

    recipe_parts = [f"VERSION:{HASH_VERSION}", f"BAKE_METHOD:{bake_method}"]

    # --- Material and Node Hashing (This part remains unchanged) ---
    if not mat.use_nodes or not mat.node_tree:
        recipe_parts.append("NON_NODE_MATERIAL")
        recipe_parts.append(f"DiffuseColor:{_stable_repr(mat.diffuse_color)}")
        recipe_parts.append(f"Metallic:{_stable_repr(mat.metallic)}")
        recipe_parts.append(f"Roughness:{_stable_repr(mat.roughness)}")
    else:
        if image_hash_cache is None: image_hash_cache = {}
        all_node_recipes, all_link_recipes = [], []
        trees_to_process, processed_trees = deque([mat.node_tree]), {mat.node_tree}
        while trees_to_process:
            current_tree = trees_to_process.popleft()
            for node in current_tree.nodes:
                node_parts = [f"NODE:{node.name}", f"TYPE:{node.bl_idname}"]
                for prop in node.bl_rna.properties:
                    if prop.is_readonly or prop.identifier in ['rna_type', 'name', 'label', 'inputs', 'outputs', 'parent', 'internal_links', 'color_ramp', 'image', 'node_tree', 'outputs']: continue
                    try:
                        value = getattr(node, prop.identifier)
                        node_parts.append(f"PROP:{prop.identifier}={_stable_repr(value)}")
                    except AttributeError: continue
                for inp in node.inputs:
                    if not inp.is_linked and hasattr(inp, 'default_value'):
                        node_parts.append(f"INPUT_DEFAULT:{inp.identifier}={_stable_repr(inp.default_value)}")
                if node.type == 'VALUE' and hasattr(node.outputs[0], 'default_value'):
                    node_parts.append(f"VALUE_NODE_OUTPUT={_stable_repr(node.outputs[0].default_value)}")
                if node.type == 'TEX_IMAGE' and node.image:
                    node_parts.append(f"SPECIAL_CONTENT_HASH:{_hash_image(node.image, image_hash_cache)}")
                elif node.type == 'ShaderNodeValToRGB':
                    cr = node.color_ramp
                    if cr: node_parts.append(f"SPECIAL_CONTENT_STOPS:[{','.join([f'STOP({_stable_repr(s.position)}, {_stable_repr(s.color)})' for s in cr.elements])}]")
                if node.type == 'GROUP' and node.node_tree and node.node_tree not in processed_trees:
                    trees_to_process.append(node.node_tree)
                    processed_trees.add(node.node_tree)
                all_node_recipes.append("||".join(sorted(node_parts)))
            for link in current_tree.links:
                all_link_recipes.append(f"LINK:{link.from_node.name}.{link.from_socket.identifier}->{link.to_node.name}.{link.to_socket.identifier}")
        recipe_parts.extend(sorted(all_node_recipes))
        recipe_parts.extend(sorted(all_link_recipes))

    # --- THE CORRECTED LOGIC SWITCH ---
    # The entire mesh context block is now skipped if ignore_mesh_context is True.
    if not ignore_mesh_context and obj and obj.type == 'MESH' and obj.data and material_slot_index is not None:
        mesh_context_parts = ["MESH_CONTEXT_START"]
        bm = bmesh.new()
        bm.from_mesh(obj.data)
        bm.faces.ensure_lookup_table()

        active_uv_layer = obj.data.uv_layers.active
        if active_uv_layer:
            mesh_context_parts.append(f"UV_MAP_NAME:{active_uv_layer.name}")
            uv_data_string = "".join(f"{i}:{l.uv.x:.6f},{l.uv.y:.6f};" for i, l in enumerate(active_uv_layer.data))
            uv_hash = hashlib.md5(uv_data_string.encode('utf-8')).hexdigest()
            mesh_context_parts.append(f"UV_HASH:{uv_hash}")
        else:
            mesh_context_parts.append("UV_HASH:NONE")

        topo_string = "".join(f"{f.index}:{','.join(str(v.index) for v in f.verts)};" for f in sorted(bm.faces, key=lambda face: face.index))
        mesh_context_parts.append(f"TOPO_HASH:{hashlib.md5(topo_string.encode('utf-8')).hexdigest()}")
        assigned_face_indices_string = ",".join(str(f.index) for f in sorted(bm.faces, key=lambda face: face.index) if f.material_index == material_slot_index)
        mesh_context_parts.append(f"ASSIGN_HASH:{hashlib.md5(assigned_face_indices_string.encode('utf-8')).hexdigest()}")

        recipe_parts.extend(mesh_context_parts)
        bm.free()

    final_recipe_string = "|||".join(recipe_parts)
    return hashlib.md5(final_recipe_string.encode('utf-8')).hexdigest()

class OBJECT_OT_import_captures(bpy.types.Operator, bpy_extras.io_utils.ImportHelper):
    """Import multiple USD files, treating base_name.### as the same asset, with per-file texture handling."""
    bl_idname = "object.import_captures"
    bl_label = "Import USD Captures (Smart V3 – Extra Optimized)"
    bl_options = {'REGISTER', 'UNDO'}

    filename_ext: StringProperty(default=".usd,.usda,.usdc,.usdz", options={'HIDDEN'})
    files: CollectionProperty(
        name="File Path",
        type=bpy.types.OperatorFileListElement,
    )
    directory: StringProperty(subtype='DIR_PATH')

    # ─── Precompile regexes once ─────────────────────────────────────────────────────
    _inst_re    = re.compile(r'inst_[0-9a-fA-F]+_\d+')
    _suffix_re  = re.compile(r'[._]\d+$')

    _addons_original_state: dict
    _processed_conceptual_asset_bases: set

    def _get_conceptual_asset_base_name(self, obj: bpy.types.Object) -> str:
        """
        Determine the conceptual base name for an object.
        1) Climb ancestors looking for “inst_HEXID_NUM”.
        2) If none, strip a single “.NNN” or “_NNN” suffix via one regex.
        """
        topmost_inst_name = None
        temp_obj = obj

        # Traverse up: if name (split at first dot) matches inst pattern, keep the highest ancestor’s name
        while temp_obj:
            core_name = temp_obj.name.partition('.')[0]
            if OBJECT_OT_import_captures._inst_re.fullmatch(core_name):
                topmost_inst_name = core_name
            temp_obj = temp_obj.parent

        if topmost_inst_name:
            return topmost_inst_name

        # Otherwise strip “.123” or “_123” via one compiled regex
        return OBJECT_OT_import_captures._suffix_re.sub("", obj.name)

    def _manage_addons(self, context: bpy.types.Context, addons_to_target: list, disable_mode: bool = True):
        """
        Disable or re-enable addons by manipulating their modules directly (no bpy.ops).
        Stores (module, was_enabled) in self._addons_original_state.
        """
        prefs = context.preferences
        addons = prefs.addons

        if disable_mode:
            self._addons_original_state = {}
            for addon_name in addons_to_target:
                addon_entry = addons.get(addon_name)
                if addon_entry:
                    module = addon_entry.module
                    was_enabled = bool(module and getattr(module, "__BL_REGISTERED__", False))
                    self._addons_original_state[addon_name] = (module, was_enabled)

                    if was_enabled:
                        logging.info(f"Disabling addon for import stability: {addon_name}")
                        unregister_fn = getattr(module, "unregister", None)
                        if unregister_fn:
                            try:
                                unregister_fn()
                                module.__BL_REGISTERED__ = False
                                logging.info(f"Successfully disabled: {addon_name}")
                            except Exception as e_disable:
                                logging.warning(f"Error disabling addon {addon_name}: {e_disable}")
                        else:
                            logging.warning(f"Addon {addon_name} has no unregister() function.")
                    else:
                        logging.info(f"Addon {addon_name} was already disabled or not fully registered.")
                else:
                    # Mark as not installed
                    self._addons_original_state[addon_name] = (None, None)
                    logging.info(f"Addon {addon_name} not found/installed.")
        else:
            for addon_name, (module, original_state) in self._addons_original_state.items():
                if module and original_state:
                    logging.info(f"Re-enabling addon: {addon_name}")
                    register_fn = getattr(module, "register", None)
                    if register_fn:
                        try:
                            register_fn()
                            module.__BL_REGISTERED__ = True
                            logging.info(f"Successfully re-enabled: {addon_name}")
                        except Exception as e_enable:
                            logging.error(f"Failed to re-enable addon {addon_name}: {e_enable}")
                    else:
                        logging.error(f"Addon {addon_name} has no register() function.")
                elif original_state is None:
                    logging.info(f"Addon {addon_name} was not installed originally; no action taken.")
                else:
                    logging.info(f"Addon {addon_name} was originally disabled; leaving as is.")
            self._addons_original_state = {}

    def _import_and_process_files_iteratively(self, context, temp_scene, addon_prefs, main_scene_ref):
        """
        (V12 - Corrected Fidelity Import)
        This function's ONLY responsibility is to import the USD file with perfect fidelity and
        perform the user's de-duplication logic. It correctly preserves the entire hierarchy,
        including parent containers, for downstream processing.
        """
        # 1) Set up importer preferences
        original_importer_settings = {}
        usd_importer_addon = context.preferences.addons.get('io_scene_usd')
        if usd_importer_addon:
            importer_prefs = usd_importer_addon.preferences
            for attr in ("axis_forward", "axis_up"):
                if hasattr(importer_prefs, attr):
                    original_importer_settings[attr] = getattr(importer_prefs, attr)

            importer_prefs.axis_forward = getattr(addon_prefs, "usd_import_forward_axis", "-Z")
            importer_prefs.axis_up = getattr(addon_prefs, "usd_import_up_axis", "Y")

        # Cache settings
        remix_scale = getattr(addon_prefs, "remix_import_scale", 1.0)
        attach_textures_flag = bool(getattr(addon_prefs, "remix_import_original_textures", False))
        valid_exts = tuple(ext.strip().lower() for ext in self.filename_ext.split(','))
    
        # Local state
        all_keep_objs = []
        processed_files_count = 0
        textures_processed_for_count = 0
    
        # Switch to temp scene for the duration of the loop
        original_scene_for_loop = context.window.scene
        context.window.scene = temp_scene

        for file_elem in self.files:
            filepath = os.path.join(self.directory, file_elem.name)
            if not (os.path.exists(filepath) and filepath.lower().endswith(valid_exts)):
                continue

            processed_files_count += 1
            logging.debug(f"[{processed_files_count}/{len(self.files)}] Importing: {filepath}")

            for obj in temp_scene.objects:
                obj["_pre_import_marker"] = True
        
            # Import using the native scale parameter. This is the only transform-related action.
            try:
                bpy.ops.wm.usd_import(filepath=filepath, scale=remix_scale)
            except Exception as e_import:
                logging.error(f"Error importing {filepath}: {e_import}", exc_info=True)
                for obj in temp_scene.objects:
                    obj.pop("_pre_import_marker", None)
                continue

            newly_added_raw_objects = [obj for obj in temp_scene.objects if "_pre_import_marker" not in obj]
            for obj in temp_scene.objects:
                obj.pop("_pre_import_marker", None)

            if not newly_added_raw_objects:
                continue

            # Your robust de-duplication and hierarchy preservation logic
            unique_meshes = [obj for obj in newly_added_raw_objects if obj.type == 'MESH' and self._get_conceptual_asset_base_name(obj) not in self._processed_conceptual_asset_bases]
            for mesh in unique_meshes:
                self._processed_conceptual_asset_bases.add(self._get_conceptual_asset_base_name(obj))

            keepers_set = set(unique_meshes)
            newly_added_set = set(newly_added_raw_objects)
            for mesh_obj in unique_meshes:
                parent = mesh_obj.parent
                while parent and parent in newly_added_set:
                    # This is the corrected part: we now add ALL parents to the keepers set.
                    keepers_set.add(parent)
                    parent = parent.parent
        
            unique_keepers_this_file = list(keepers_set)
            discards = [obj for obj in newly_added_raw_objects if obj not in keepers_set]

            # Material de-duplication
            for obj in unique_keepers_this_file:
                if obj.type == 'MESH':
                    for slot in obj.material_slots:
                        mat = slot.material
                        if not mat: continue
                        base_mat_name = mat.name.split('.')[0]
                        if base_mat_name in bpy.data.materials and base_mat_name != mat.name:
                            slot.material = bpy.data.materials[base_mat_name]

            # Texture handling
            if attach_textures_flag:
                meshes_for_texture = [obj for obj in unique_keepers_this_file if obj.type == 'MESH']
                if meshes_for_texture and is_blend_file_saved():
                    attach_original_textures(meshes_for_texture, context, os.path.dirname(filepath))
                    textures_processed_for_count += len(meshes_for_texture)

            # Delete discarded objects
            for obj_del in discards:
                if obj_del.name in bpy.data.objects:
                    bpy.data.objects.remove(obj_del, do_unlink=True)
        
            # Prune and append
            all_keep_objs.extend([o for o in unique_keepers_this_file if o and o.name in bpy.data.objects])

        # Restore context and settings
        context.window.scene = original_scene_for_loop
        if usd_importer_addon:
            for attr, val in original_importer_settings.items():
                setattr(usd_importer_addon.preferences, attr, val)

        return list(dict.fromkeys(all_keep_objs)), processed_files_count, textures_processed_for_count
        
    def _perform_batch_mesh_transformations(self, context, meshes_to_transform, do_mirror, do_flip):
        """
        [FIXED]
        Performs batch mirroring and/or normal flipping. Mirroring is done in a single
        Edit Mode session for performance and stability. Normal flipping (when done
        without mirroring) is now handled by iterating and calling the robust `flip_normals_api`
        for each mesh, ensuring correctness.
        """
        if not meshes_to_transform or (not do_mirror and not do_flip):
            return

        logging.info(f"Performing batch transformations (Mirror: {do_mirror}, Flip: {do_flip}) on {len(meshes_to_transform)} meshes.")

        # --- State Backup ---
        original_active = context.view_layer.objects.active
        original_selected = list(context.selected_objects)
        original_mode = 'OBJECT'
        if context.object and hasattr(context.object, 'mode'):
            original_mode = context.object.mode

        try:
            # --- Setup: Ensure Object Mode ---
            if context.mode != 'OBJECT':
                bpy.ops.object.mode_set(mode='OBJECT')

            bpy.ops.object.select_all(action='DESELECT')

            valid_meshes = [
                obj for obj in meshes_to_transform
                if obj and obj.type == 'MESH' and obj.name in context.view_layer.objects
            ]

            if not valid_meshes:
                logging.warning("No valid meshes were available for batch transformation.")
                return

            # --- Primary Operation: Mirroring ---
            # This is the more complex operation and benefits from a batch approach.
            # Mirroring inherently requires normals to be flipped, so we handle that here.
            if do_mirror:
                logging.debug("Applying mirror transformation to meshes.")
                for obj in valid_meshes:
                    obj.select_set(True)

                if valid_meshes:
                    context.view_layer.objects.active = valid_meshes[0]

                    # Apply scale once before mirroring for correct pivot.
                    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)

                    # Single edit mode session for all selected meshes.
                    bpy.ops.object.mode_set(mode='EDIT')
                    if context.mode == 'EDIT_MESH':
                        for obj_in_edit in context.selected_editable_objects:
                            mesh_data = obj_in_edit.data
                            bm = bmesh.from_edit_mesh(mesh_data)

                            # Mirror vertices on the X-axis.
                            for v in bm.verts:
                                v.co.x *= -1

                            # A mirror operation inverts face orientation, so normals must be flipped to compensate.
                            for f in bm.faces:
                                f.normal_flip()

                            bmesh.update_edit_mesh(mesh_data)

                        bpy.ops.object.mode_set(mode='OBJECT')
                    else:
                        logging.error(f"Failed to enter EDIT_MESH mode. Mirroring skipped.")

            # --- Secondary Operation: Normal Flipping (only if NOT mirroring) ---
            # This is executed if the user ONLY ticked "Flip Normals Import".
            # If they ticked both, the mirror operation already handled the flip.
            if do_flip and not do_mirror:
                logging.debug("Applying normal flip transformation to meshes.")
                for obj in valid_meshes:
                    # Use the robust, per-object API which is known to work reliably.
                    flip_normals_api(obj)

        except Exception as e:
            logging.error(f"Error during batch mesh transformation: {e}", exc_info=True)
            # Ensure we exit edit mode on error
            if context.mode != 'OBJECT':
                try:
                    bpy.ops.object.mode_set(mode='OBJECT')
                except RuntimeError:
                    pass
        finally:
            # --- State Restoration ---
            bpy.ops.object.select_all(action='DESELECT')
            for obj in original_selected:
                if obj and obj.name in context.view_layer.objects:
                    try:
                        obj.select_set(True)
                    except (ReferenceError, RuntimeError):
                        pass
            if original_active and original_active.name in context.view_layer.objects:
                context.view_layer.objects.active = original_active

            # Restore the original mode if it was something other than Object mode
            if context.mode == 'OBJECT' and original_mode != 'OBJECT' and context.active_object:
                try:
                    bpy.ops.object.mode_set(mode=original_mode)
                except RuntimeError:
                    pass

    def execute(self, context: bpy.types.Context) -> set[str]:
        """
        (V14 - DEFINITIVE USER-REQUESTED FIX)
        This version correctly makes the 'Import USD Captures' operator's behavior
        match the 'Import from Remix' operator. It now applies location and rotation
        transforms for cleanup but correctly PRESERVES the scale transform set by the
        user, fixing the inconsistency.
        """
        start_time = time.perf_counter()
        addon_prefs = context.preferences.addons[__name__].preferences
        
        if not self.files:
            self.report({'WARNING'}, "No files selected for import.")
            return {'CANCELLED'}

        original_main_scene = context.scene
        import_scene_temp = None
        self._processed_conceptual_asset_bases = set()

        try:
            # Create a clean, temporary scene for the import
            temp_scene_name = f"USD_Import_Temp_{uuid.uuid4().hex[:8]}"
            import_scene_temp = bpy.data.scenes.new(temp_scene_name)

            # ─── STEP 1: Import with perfect fidelity ───────────────────────
            all_final_keepers, imported_files_count, textures_count = \
                self._import_and_process_files_iteratively(
                    context, import_scene_temp, addon_prefs, original_main_scene
                )

            if not all_final_keepers:
                self.report({'INFO'}, f"Processed {imported_files_count} files. No unique assets were kept.")
                return {'FINISHED'}

            # ─── STEP 2: Transfer objects to the main scene ────────────────
            context.window.scene = original_main_scene
            transferred_count = 0
            for obj in all_final_keepers:
                if obj and obj.name in import_scene_temp.objects:
                    # Unlink from all temp collections before linking
                    for coll in list(obj.users_collection):
                        coll.objects.unlink(obj)
                    original_main_scene.collection.objects.link(obj)
                    transferred_count += 1

            # ─── STEP 3: Finalize objects in the main scene ────────────────
            bpy.ops.object.select_all(action='DESELECT')
            active_obj_set = False
            for obj in all_final_keepers:
                if obj and obj.name in original_main_scene.objects:
                    original_main_scene.objects[obj.name].select_set(True)
                    if not active_obj_set:
                        context.view_layer.objects.active = original_main_scene.objects[obj.name]
                        active_obj_set = True
            
            if context.selected_objects:
                # Apply optional user transformations first
                if addon_prefs.mirror_import:
                    batch_mirror_objects_optimized(context.selected_objects, context)
                if addon_prefs.flip_normals_import:
                    batch_flip_normals_optimized(context.selected_objects, context)
                
                # This bakes the parent transforms into the children before removing the relationship
                logging.info("Clearing parents while keeping transforms to remove relationship lines.")
                bpy.ops.object.parent_clear(type='CLEAR_KEEP_TRANSFORM')

                # --- NEW CLEANUP STEP ---
                # Now that transforms are baked, we can safely delete the empty parents.
                logging.info("Cleaning up temporary parent Empties.")
                empties_to_delete = [
                    obj for obj in all_final_keepers 
                    if obj and obj.type == 'EMPTY' and obj.name in context.scene.objects
                ]
                if empties_to_delete:
                    bpy.ops.object.select_all(action='DESELECT')
                    for empty in empties_to_delete:
                        # Check existence again in case it was part of another hierarchy
                        if empty.name in context.scene.objects:
                           context.scene.objects[empty.name].select_set(True)
                    if context.selected_objects:
                        bpy.ops.object.delete()
                
                # --- THIS IS THE FIX ---
                # After deletion, create a fresh list of only the surviving MESH objects.
                # We iterate through the potentially "dirty" list of keepers and use a
                # try/except block to safely ignore the dead references to deleted empties.
                bpy.ops.object.select_all(action='DESELECT')
                surviving_meshes = []
                for obj in all_final_keepers:
                    try:
                        # This check will raise a ReferenceError if 'obj' points to a deleted object.
                        if obj.type == 'MESH':
                            surviving_meshes.append(obj)
                    except ReferenceError:
                        # This was a deleted empty object. We safely ignore it and continue.
                        pass
                
                if surviving_meshes:
                    for mesh in surviving_meshes:
                        mesh.select_set(True)
                    context.view_layer.objects.active = surviving_meshes[0]
                    # --- THE REAL FIX IS HERE: Changed scale=True to scale=False ---
                    # This applies location and rotation to clean the object's transforms,
                    # but now leaves the scale transform intact, matching the other button.
                    logging.info("Applying location and rotation transforms to finalize objects, preserving scale.")
                    bpy.ops.object.transform_apply(location=True, rotation=True, scale=False)

            bpy.ops.object.select_all(action='DESELECT')
            
            # Build report message
            report_parts = [
                f"Processed {imported_files_count} USD file(s).",
                f"Kept {len(self._processed_conceptual_asset_bases)} unique conceptual assets ({transferred_count} total objects).",
                f"Finalized and un-parented objects in '{original_main_scene.name}'."
            ]
            if textures_count > 0:
                report_parts.append(f"Applied textures for {textures_count} mesh objects.")

            self.report({'INFO'}, " ".join(report_parts))
            return {'FINISHED'}

        except Exception as e:
            logging.critical(f"Fatal error during import execution: {e}", exc_info=True)
            self.report({'ERROR'}, "Critical import failure. See system console.")
            return {'CANCELLED'}

        finally:
            if import_scene_temp and import_scene_temp.name in bpy.data.scenes:
                bpy.data.scenes.remove(import_scene_temp, do_unlink=True)
            elapsed = time.perf_counter() - start_time
            print(f"[Import USD Captures] Total time: {elapsed:.2f} seconds")

    def invoke(self, context: bpy.types.Context, event: bpy.types.Event) -> set[str]:
        if not is_blend_file_saved():
            self.report({'WARNING'}, "Please save your Blender file before importing USD captures.")
            return {'CANCELLED'}
        context.window_manager.fileselect_add(self)
        return {'RUNNING_MODAL'}

class OBJECT_OT_import_usd_from_remix(Operator):
    bl_idname = "object.import_usd_from_remix"
    bl_label = "Import USD from Remix (Robust)"
    bl_options = {'REGISTER', 'UNDO'}

    # This operator will reuse helper methods from OBJECT_OT_import_captures
    # for transform application and object transfer.

    def _perform_usd_import_into_scene(self, context, target_scene, usd_file_paths_to_import, addon_prefs_instance):
        """
        Imports specified USD files into the target_scene for Remix workflow.
        Manages USD importer preferences.
        Applies Remix-specific post-import operations like scaling, mirroring, normal flipping.
        Returns a list of top-level Blender objects created from the imported USDs.
        """
        imported_top_level_objects_map = {} # Store as {usd_filepath: [objects]}
        user_selected_forward_axis = addon_prefs_instance.usd_import_forward_axis

        original_importer_settings = {}
        usd_importer_addon = context.preferences.addons.get('io_scene_usd')
        if usd_importer_addon:
            importer_prefs = usd_importer_addon.preferences
            attrs_to_backup = ['axis_forward', 'axis_up', 'scale', 'import_materials', 'import_meshes'] # Add more if needed
            for attr in attrs_to_backup:
                if hasattr(importer_prefs, attr):
                    original_importer_settings[attr] = getattr(importer_prefs, attr)
            logging.debug(f"Backed up USD importer settings for Remix import: {original_importer_settings.keys()}")
    
        original_window_scene = context.window.scene
    
        # List to collect meshes for batch mirroring
        all_meshes_to_mirror_in_temp = []
    
        try:
            if usd_importer_addon:
                importer_prefs = usd_importer_addon.preferences
                if hasattr(importer_prefs, 'axis_forward'):
                    importer_prefs.axis_forward = user_selected_forward_axis
                    logging.info(f"Remix import: Set USD importer axis_forward to '{user_selected_forward_axis}'.")
                # Set other "default" UMI-like settings
                if hasattr(importer_prefs, 'import_materials'): importer_prefs.import_materials = 'USD_PREVIEW_SURFACE'
                if hasattr(importer_prefs, 'import_meshes'): importer_prefs.import_meshes = True
                # Add other desired defaults for USD import here
        
            if context.window.scene != target_scene:
                context.window.scene = target_scene
                logging.info(f"Temporarily set active window scene to '{target_scene.name}' for Remix USD import.")

            for usd_file_path in usd_file_paths_to_import:
                logging.info(f"Importing (Remix) '{usd_file_path}' into temp scene '{target_scene.name}'")
            
                # Store objects already in the temp scene to identify newly added ones
                objects_before_import_in_temp = set(target_scene.objects)
                bpy.ops.object.select_all(action='DESELECT') # Deselect in temp scene

                try:
                    bpy.ops.wm.usd_import(filepath=usd_file_path)
                    logging.info(f"  Successfully imported (Remix) {os.path.basename(usd_file_path)} into {target_scene.name}.")
                
                    objects_after_import_in_temp = set(target_scene.objects)
                    newly_added_objects = list(objects_after_import_in_temp - objects_before_import_in_temp)
                
                    if not newly_added_objects:
                        if context.selected_objects:
                            newly_added_objects = list(context.selected_objects)
                            logging.debug(f"  Remix import of {os.path.basename(usd_file_path)}: using selected objects as newly added.")
                        else:
                            logging.warning(f"  Remix import of {os.path.basename(usd_file_path)}: No new objects detected by diff and nothing selected. Subsequent per-object operations might be skipped for this file.")
                            imported_top_level_objects_map[usd_file_path] = []
                            continue

                    imported_top_level_objects_map[usd_file_path] = newly_added_objects
                    logging.info(f"  Remix import: Identified {len(newly_added_objects)} new top-level objects from {os.path.basename(usd_file_path)}.")

                    import_scale = addon_prefs_instance.remix_import_scale
                    if import_scale != 1.0:
                        for obj in newly_added_objects:
                            if obj.type in {'MESH', 'CURVE', 'EMPTY'}:
                                obj.scale = tuple(s * import_scale for s in obj.scale)
                                logging.debug(f"  Applied import scale {import_scale} to object: {obj.name} (Remix temp).")
                
                    if addon_prefs_instance.mirror_import:
                        for obj in newly_added_objects:
                             if obj.type == 'MESH':
                                all_meshes_to_mirror_in_temp.append(obj)

                    if addon_prefs_instance.flip_normals_import:
                        for obj in newly_added_objects:
                            if obj.type == 'MESH':
                                flip_normals_api(obj)
                                logging.debug(f"  Flipped normals for imported object: {obj.name} (Remix temp).")
            
                except RuntimeError as e_imp_remix:
                    logging.error(f"  Runtime error importing (Remix) {usd_file_path} into {target_scene.name}: {e_imp_remix}", exc_info=True)
                except Exception as ex_gen_remix:
                    logging.error(f"  Unexpected error importing (Remix) {usd_file_path}: {ex_gen_remix}", exc_info=True)

        finally:
            # Perform batch mirror operation after all imports are done, but before restoring the scene state.
            if addon_prefs_instance.mirror_import and all_meshes_to_mirror_in_temp:
                logging.info(f"Applying batch mirror to {len(all_meshes_to_mirror_in_temp)} imported Remix objects.")
                valid_meshes_to_mirror = list(dict.fromkeys(
                    obj for obj in all_meshes_to_mirror_in_temp if obj and obj.name in target_scene.objects
                ))
                if valid_meshes_to_mirror:
                    batch_mirror_objects_optimized(valid_meshes_to_mirror, context)

            # Restore Blender's original settings
            if usd_importer_addon and original_importer_settings:
                importer_prefs = usd_importer_addon.preferences
                for attr, val in original_importer_settings.items():
                    try: setattr(importer_prefs, attr, val)
                    except Exception: pass
                logging.debug("Restored Blender's USD importer preferences (Remix).")
        
            if context.window.scene != original_window_scene:
                try:
                    context.window.scene = original_window_scene
                    logging.info(f"Restored active window scene to '{original_window_scene.name}' (Remix).")
                except Exception as e_restore_scene_remix:
                    logging.error(f"Failed to restore original window scene '{original_window_scene.name}' (Remix): {e_restore_scene_remix}", exc_info=True)

        return imported_top_level_objects_map

    def execute(self, context):
        addon_prefs = context.preferences.addons[__name__].preferences
        global remix_import_lock
        if remix_import_lock:
            self.report({'INFO'}, "Another USD import (Remix) is already in progress.")
            return {'CANCELLED'}

        if not is_blend_file_saved():
            bpy.ops.object.show_popup('INVOKE_DEFAULT', message="Please save your Blender file before importing USD assets from Remix.", success=False)
            return {'CANCELLED'}

        remix_import_lock = True
        logging.info("Lock acquired for USD import process (Remix).")

        main_scene = context.scene
        import_scene_temp = None
        all_imported_usd_filepaths = []
        base_dir_for_textures = ""
        all_imported_objects_from_temp = []
        # --- FIX: Store names early, as strings survive object deletion ---
        imported_object_names = []


        try:
            # --- Step 1 & 2: Fetch and determine file paths (Unchanged) ---
            assets_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/?selection=true&filter_session_assets=false&exists=true"
            response = make_request_with_retries('GET', assets_url, headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'}, verify=addon_prefs.remix_verify_ssl)
            if not response or response.status_code != 200:
                self.report({'ERROR'}, "Failed to connect to Remix server for asset list.")
                return {'CANCELLED'}

            data = response.json()
            prim_paths = data.get("prim_paths", data.get("asset_paths", []))
            mesh_prim_paths = [path for path in prim_paths if "/meshes/" in path.lower()]

            if not mesh_prim_paths:
                self.report({'WARNING'}, "No mesh assets found in Remix server selection.")
                return {'CANCELLED'}

            first_mesh_path = mesh_prim_paths[0]
            segments = first_mesh_path.strip('/').split('/')
            if len(segments) < 3:
                self.report({'ERROR'}, f"Cannot determine reference prim from path: {first_mesh_path}")
                return {'CANCELLED'}
            
            ref_prim_for_path_api = '/' + '/'.join(segments[:3])
            encoded_ref_prim = urllib.parse.quote(ref_prim_for_path_api, safe='')
            file_paths_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/{encoded_ref_prim}/file-paths"
            
            response_files = make_request_with_retries('GET', file_paths_url, headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'}, verify=addon_prefs.remix_verify_ssl)
            if not response_files or response_files.status_code != 200:
                self.report({'ERROR'}, "Failed to retrieve file paths for selected prims.")
                return {'CANCELLED'}

            file_data = response_files.json()
            try:
                base_dir_source = file_data['reference_paths'][0][1][1]
                base_dir_for_textures = os.path.dirname(base_dir_source).replace('\\', '/')
            except (IndexError, KeyError, TypeError):
                 self.report({'ERROR'}, "Could not determine base directory from server response.")
                 return {'CANCELLED'}

            for mesh_path in mesh_prim_paths:
                mesh_name = mesh_path.strip('/').split('/')[2]
                usd_path = os.path.join(base_dir_for_textures, "meshes", f"{mesh_name}.usd").replace('\\', '/')
                if os.path.exists(usd_path) and usd_path not in all_imported_usd_filepaths:
                    all_imported_usd_filepaths.append(usd_path)

            if not all_imported_usd_filepaths:
                self.report({'INFO'}, "No new USD files from Remix selection to import.")
                return {'FINISHED'}

            # --- Step 3: Import into a temporary scene (Unchanged) ---
            temp_scene_name = f"Remix_Import_Temp_{uuid.uuid4().hex[:8]}"
            import_scene_temp = bpy.data.scenes.new(temp_scene_name)
            
            imported_obj_map = self._perform_usd_import_into_scene(context, import_scene_temp, all_imported_usd_filepaths, addon_prefs)
            all_imported_objects_from_temp = [obj for obj_list in imported_obj_map.values() for obj in obj_list]

            if not all_imported_objects_from_temp and import_scene_temp.objects:
                all_imported_objects_from_temp = list(import_scene_temp.objects)

            if not all_imported_objects_from_temp:
                 self.report({'WARNING'}, "No objects were imported from Remix.")
                 return {'CANCELLED'}
            
            # --- FIX: Get the names of all imported objects before any are deleted ---
            imported_object_names = [obj.name for obj in all_imported_objects_from_temp if obj]

            # --- Step 4: Transfer, Finalize, and Cleanup (Main logic change is here) ---
            context.window.scene = main_scene
            for obj in all_imported_objects_from_temp:
                if obj and obj.name in import_scene_temp.objects:
                    for coll in list(obj.users_collection):
                        coll.objects.unlink(obj)
                    main_scene.collection.objects.link(obj)
            
            bpy.ops.object.select_all(action='DESELECT')
            active_obj_set = False
            for name in imported_object_names:
                obj = main_scene.objects.get(name)
                if obj:
                    obj.select_set(True)
                    if not active_obj_set:
                        context.view_layer.objects.active = obj
                        active_obj_set = True

            if context.selected_objects:
                if addon_prefs.mirror_import:
                    batch_mirror_objects_optimized(context.selected_objects, context)
                if addon_prefs.flip_normals_import:
                    batch_flip_normals_optimized(context.selected_objects, context)
                
                bpy.ops.object.parent_clear(type='CLEAR_KEEP_TRANSFORM')

                empties_to_delete = [
                    main_scene.objects.get(name) for name in imported_object_names 
                    if main_scene.objects.get(name) and main_scene.objects.get(name).type == 'EMPTY'
                ]
                if empties_to_delete:
                    bpy.ops.object.select_all(action='DESELECT')
                    for empty in empties_to_delete:
                       empty.select_set(True)
                    if context.selected_objects:
                        bpy.ops.object.delete()
                
                bpy.ops.object.select_all(action='DESELECT')
                surviving_meshes = [
                    main_scene.objects.get(name) for name in imported_object_names
                    if main_scene.objects.get(name) and main_scene.objects.get(name).type == 'MESH'
                ]
                
                if surviving_meshes:
                    for mesh in surviving_meshes:
                        mesh.select_set(True)
                    context.view_layer.objects.active = surviving_meshes[0]
                    bpy.ops.object.transform_apply(location=True, rotation=True, scale=False)

            # --- Final Step: Attach Textures using a clean list ---
            bpy.ops.object.select_all(action='DESELECT')
            
            # --- FIX: Rebuild the final list from the scene using the saved names ---
            final_objects_for_texture = [main_scene.objects.get(name) for name in imported_object_names if main_scene.objects.get(name)]

            if addon_prefs.remix_import_original_textures and base_dir_for_textures and final_objects_for_texture:
                attach_original_textures(final_objects_for_texture, context, base_dir_for_textures)

            self.report({'INFO'}, f"Remix import complete. Processed {len(all_imported_usd_filepaths)} file(s).")
            return {'FINISHED'}

        except Exception as e:
            logging.error(f"Unexpected error during Remix USD import: {e}", exc_info=True)
            self.report({'ERROR'}, "A critical error occurred. See system console for details.")
            return {'CANCELLED'}
        finally:
            if import_scene_temp and import_scene_temp.name in bpy.data.scenes:
                bpy.data.scenes.remove(import_scene_temp, do_unlink=True)
            remix_import_lock = False
            logging.info("Lock released for USD import process (Remix).")
    
class OBJECT_OT_export_and_ingest(Operator):
    bl_idname = "object.export_and_ingest"
    bl_label = "Export and Ingest (Dynamic Workers)"
    bl_options = {'REGISTER', 'UNDO'}

    # --- Operator State Variables ---
    _timer = None
    _op_lock: Lock = None
    _export_data: dict = {}
    _operator_state: str = 'INITIALIZING' 

    # --- Dynamic Worker Management State ---
    _worker_slots: list = []
    _master_task_queue: collections.deque = None
    _comm_threads: list = []
    _results_queue: Queue = None
    _log_queue: Queue = None
    _total_tasks: int = 0
    _finished_tasks: int = 0
    _failed_tasks: int = 0
    
    # --- Configuration for Smart Scaling ---
    MAX_POTENTIAL_WORKERS: int = max(1, os.cpu_count()) 
    INITIAL_WORKER_COUNT: int = 3
    
    # --- Event-Driven Stabilization ---
    _initial_tasks_finished_count: int = 0

    # Time in seconds between dynamic scaling decisions.
    RESOURCE_CHECK_INTERVAL_SEC: int = 0.5
    _next_resource_check_time: float = 0.0
    
    # How many consecutive checks must be "high" before scaling down.
    HIGH_USAGE_SUSTAINED_CHECKS: int = 3
    _high_usage_counter: int = 0

    # Resource usage thresholds (as percentages).
    CPU_HIGH_THRESHOLD: int = 95
    RAM_HIGH_THRESHOLD: int = 95
    CPU_LOW_THRESHOLD: int = 85
    RAM_LOW_THRESHOLD: int = 85
    
    # --- START OF DEBUGGING SIMULATION ---
    def _get_system_resources(self):
        """
        [DEBUG SIMULATION] This method is modified to always report 99% CPU usage
        to trigger the worker scale-down logic for debugging purposes.
        """
        # In a real scenario, this would use psutil.
        # We are forcing a high CPU value here.
        simulated_cpu = 99.0
        simulated_ram = 50.0 # Keep RAM normal to isolate the CPU trigger

        if PSUTIL_INSTALLED:
            import psutil
            # We still get the real RAM usage.
            simulated_ram = psutil.virtual_memory().percent
        
        return simulated_cpu, simulated_ram

    def _communication_thread_target(self, worker_process):
        """Dedicated thread to read stdout from a single worker."""
        if not worker_process or not worker_process.stdout: return
        try:
            for line in iter(worker_process.stdout.readline, ''):
                if line: self._results_queue.put(line.strip())
        except Exception: pass

    def _log_thread_target(self, worker_process):
        """Dedicated thread to read stderr from a single worker for live logging."""
        if not worker_process or not worker_process.stderr: return
        try:
            for line in iter(worker_process.stderr.readline, ''):
                if line: self._log_queue.put(line.strip())
        except Exception: pass
                       
        
    def _launch_new_worker(self, slot_index):
        if slot_index >= len(self._worker_slots): return
        slot = self._worker_slots[slot_index]
        if slot['process'] is not None and slot['process'].poll() is None: return

        lib_path = get_persistent_lib_path()
        if not lib_path:
            logging.error("CRITICAL: Could not get persistent library path. Cannot launch workers.")
            slot['status'] = 'failed'
            return

        logging.info(f"→ Launching PERSISTENT worker for slot {slot_index}...")
        
        # --- THIS IS THE MODIFIED COMMAND ---
        cmd = [
            bpy.app.binary_path, 
            "--factory-startup", 
            "--background", 
            "--python", BAKE_WORKER_PY, 
            "--", 
            "--persistent", # <-- ADDED THIS FLAG
            "--lib-path", lib_path
        ]
    
        try:
            creation_flags = subprocess.CREATE_NEW_PROCESS_GROUP if sys.platform == "win32" else 0
            worker = subprocess.Popen(
                cmd, 
                stdin=subprocess.PIPE, 
                stdout=subprocess.PIPE, 
                stderr=subprocess.PIPE, 
                creationflags=creation_flags, 
                text=True, 
                encoding='utf-8', 
                bufsize=1
            )
            ACTIVE_WORKER_PROCESSES.append(worker)
        
            slot['process'] = worker
            slot['status'] = 'launching'
            slot['launch_time'] = time.monotonic()

            comm_thread = threading.Thread(target=self._communication_thread_target, args=(worker,), daemon=True)
            log_thread = threading.Thread(target=self._log_thread_target, args=(worker,), daemon=True)
            comm_thread.start()
            log_thread.start()
            self._comm_threads.extend([comm_thread, log_thread])

            # --- [REMOVED] ---
            # The initial load command is no longer sent. The worker will start,
            # report its readiness, and then wait for its first task. We do not
            # write anything to its stdin upon launch.
            # --- [END OF REMOVAL] ---

        except Exception as e:
            logging.error(f"Could not launch worker for slot {slot_index}: {e}", exc_info=True)
            slot['status'] = 'failed'
            
        
    def _terminate_worker(self, slot_index):
        """
        [HYBRID SHUTDOWN V2 - AGGRESSIVE FAILSAFE] Gracefully shuts down a worker.
        1. Sends a 'quit' command and waits for a clean exit.
        2. If it times out, sends a terminate signal and waits 0.5 seconds.
        3. If it's still running, forcefully kills the process immediately.
        """
        if slot_index >= len(self._worker_slots):
            return

        slot = self._worker_slots[slot_index]
        worker = slot.get('process')

        if worker and worker.poll() is None:
            logging.info(f"Attempting graceful shutdown for worker in slot {slot_index} (PID: {worker.pid})...")
            try:
                # --- Step 1: The Polite Request ---
                quit_command = json.dumps({"action": "quit"}) + "\n"
                worker.stdin.write(quit_command)
                worker.stdin.flush()
                worker.stdin.close() # Signal that we're done writing

                # --- Step 2: The Waiting Period (5 seconds) ---
                worker.wait(timeout=5)
                logging.info(f"Worker {slot_index} (PID: {worker.pid}) shut down gracefully.")

            except (subprocess.TimeoutExpired, BrokenPipeError, OSError):
                # --- Step 3: The Forceful Takedown (if graceful shutdown fails) ---
                logging.warning(f"Worker {slot_index} did not respond to quit command. Forcibly terminating (PID: {worker.pid}).")
                worker.terminate()
                try:
                    # --- THIS IS THE MODIFIED LOGIC ---
                    # Give it only 0.5 seconds to die after the terminate signal.
                    worker.wait(timeout=0.5)
                    logging.info(f"Worker {slot_index} (PID: {worker.pid}) terminated successfully.")
                    # --- END OF MODIFICATION ---
                except subprocess.TimeoutExpired:
                    # --- THIS IS THE MODIFIED LOGIC ---
                    # If it's still alive after 0.5 seconds, use the final, most aggressive method.
                    logging.error(f"Worker {slot_index} (PID: {worker.pid}) did not terminate. Killing process now.")
                    worker.kill()
                    # --- END OF MODIFICATION ---
            finally:
                # --- Final Cleanup ---
                if worker in ACTIVE_WORKER_PROCESSES:
                    ACTIVE_WORKER_PROCESSES.remove(worker)
                slot['process'] = None
                slot['status'] = 'suspended'
          
    def _material_uses_udims(self, mat):
        """Checks if a material uses any UDIM (tiled) image textures."""
        if not mat or not mat.use_nodes:
            return False
        for node in mat.node_tree.nodes:
            if node.type == 'TEX_IMAGE' and node.image and node.image.source == 'TILED':
                return True
        return False

          
    def _hash_and_rename_file(self, file_path):
        """
        Calculates the SHA1 hash of a file's content, renames the file to include
        the hash, and returns the new file path.
        """
        if not os.path.exists(file_path):
            return file_path # Return original if file doesn't exist

        hasher = hashlib.sha1()
        try:
            with open(file_path, 'rb') as f:
                while chunk := f.read(8192): # Read in 8k chunks
                    hasher.update(chunk)
            
            # Get the first 8 characters of the hex digest for a shorter hash
            file_hash = hasher.hexdigest()[:8].upper()

            # Construct the new filename
            directory, filename = os.path.split(file_path)
            name, ext = os.path.splitext(filename)
            new_filename = f"{name}_{file_hash}{ext}"
            new_filepath = os.path.join(directory, new_filename)

            # Rename the file
            os.rename(file_path, new_filepath)
            logging.info(f"Hashed and renamed '{filename}' to '{new_filename}'")
            
            return new_filepath
        except Exception as e:
            logging.error(f"Failed to hash and rename file '{file_path}': {e}", exc_info=True)
            return file_path # Return original path on failure
    
    def _realize_geonodes_object_non_destructively(self, context, obj):
        """
        [DEFINITIVE V8 - CORRECTED MIRROR TRANSFORM] Realizes a generator, correctly
        transfers materials, AND applies all transforms to the resulting objects.
        This transform application is critical to ensure subsequent operations like
        mirroring work correctly from the world origin.
        """
        logging.warning(f"Performing non-destructive realization for '{obj.name}'...")

        original_active = context.view_layer.objects.active
        original_selected = list(context.selected_objects)

        # Take a snapshot of all object names present in the scene BEFORE the operation.
        objects_before_names = {o.name for o in bpy.data.objects}

        # --- NEW: Identify materials used inside the GeoNodes modifier ---
        materials_to_assign = set()
        gn_modifier = next((m for m in obj.modifiers if m.type == 'NODES'), None)
        if gn_modifier and gn_modifier.node_group:
            node_tree = gn_modifier.node_group
            for node in node_tree.nodes:
                if node.type == 'SET_MATERIAL' and node.inputs['Material'].default_value is not None:
                    materials_to_assign.add(node.inputs['Material'].default_value)
            logging.info(f"Found {len(materials_to_assign)} materials to transfer from '{obj.name}' GeoNodes tree: {[m.name for m in materials_to_assign]}")

        temp_duplicate = None
        try:
            bpy.ops.object.select_all(action='DESELECT')
            obj.select_set(True)
            context.view_layer.objects.active = obj
            bpy.ops.object.duplicate(linked=False)
    
            temp_duplicate = context.view_layer.objects.active
            if not temp_duplicate:
                raise RuntimeError("Failed to create a temporary duplicate for realization.")

            gn_modifier = next((m for m in temp_duplicate.modifiers if m.type == 'NODES'), None)
            if gn_modifier and gn_modifier.node_group:
                node_tree = gn_modifier.node_group
                output_node = next((n for n in node_tree.nodes if n.type == 'GROUP_OUTPUT'), None)
                if output_node:
                    realize_node = node_tree.nodes.new(type='GeometryNodeRealizeInstances')
                    realize_node.location = (output_node.location.x - 200, output_node.location.y)
                    target_socket = next((s for s in output_node.inputs if s.type == 'GEOMETRY'), None)
                    if target_socket and target_socket.is_linked:
                        original_link = target_socket.links[0]
                        source_socket = original_link.from_socket
                        node_tree.links.new(source_socket, realize_node.inputs['Geometry'])
                        node_tree.links.new(realize_node.outputs['Geometry'], target_socket)
                        logging.info(f"Temporarily inserted 'Realize Instances' node for '{temp_duplicate.name}'.")
    
            bpy.ops.object.convert(target='MESH')
    
            # Compare the "after" state to the "before" state to find all new objects.
            objects_after_names = {o.name for o in bpy.data.objects}
            new_object_names = objects_after_names - objects_before_names

            if not new_object_names:
                # If convert resulted in a single object (the temp_duplicate itself), use that.
                if temp_duplicate.name in objects_before_names:
                        new_object_names = {temp_duplicate.name}
                else:
                    raise RuntimeError(f"Realization process for '{obj.name}' did not create any new objects.")
    
            final_realized_objects = [bpy.data.objects[name] for name in new_object_names if name in bpy.data.objects]

            # --- Material Assignment ---
            for new_obj in final_realized_objects:
                existing_mats = {slot.material for slot in new_obj.material_slots if slot.material}
                for mat_from_node in materials_to_assign:
                    if mat_from_node not in existing_mats:
                        new_obj.data.materials.append(mat_from_node)
                logging.info(f"Ensured {len(new_obj.material_slots)} materials are present on new realized object '{new_obj.name}'.")

            # --- THIS IS THE FIX: Apply transforms to lock geometry in world space ---
            # This is crucial for operations like mirroring to work correctly.
            if final_realized_objects:
                bpy.ops.object.select_all(action='DESELECT')
                active_set = False
                for new_obj in final_realized_objects:
                    # Ensure the object exists in the current view layer to be selectable
                    if new_obj.name in context.view_layer.objects:
                        new_obj.select_set(True)
                        if not active_set:
                            context.view_layer.objects.active = new_obj
                            active_set = True
                
                # Check that we actually have a selection and an active object before applying
                if context.view_layer.objects.active and context.selected_objects:
                    logging.info(f"Applying all transforms to {len(final_realized_objects)} realized objects to fix world position.")
                    bpy.ops.object.transform_apply(location=True, rotation=True, scale=True)
                else:
                    logging.warning("Could not apply transforms to realized objects; none were selectable in the view layer.")
            # --- END OF FIX ---

            # Process and track the newly found objects for cleanup.
            for i, new_obj in enumerate(final_realized_objects):
                base_name = f"{obj.name}_RealizedTemp"
                # Avoid renaming the object if it's the only one and was the duplicate
                if len(final_realized_objects) > 1 or new_obj.name != temp_duplicate.name:
                    new_obj.name = base_name if i == 0 else f"{base_name}.{i:03d}"
                self._export_data['temp_realized_object_names'].append(new_obj.name)

            logging.info(f"Successfully created and processed {len(final_realized_objects)} temporary realized objects: {[o.name for o in final_realized_objects]}")
            return final_realized_objects

        except Exception as e:
            logging.error(f"Failed to realize Geometry Nodes for object '{obj.name}': {e}", exc_info=True)
            # Cleanup any objects that were created before the error
            objects_after_error_names = {o.name for o in bpy.data.objects}
            to_remove_names = objects_after_error_names - objects_before_names
            for name in to_remove_names:
                if name in bpy.data.objects:
                    bpy.data.objects.remove(bpy.data.objects[name], do_unlink=True)
            return []
        finally:
            # Restore original scene state
            bpy.ops.object.select_all(action='DESELECT')
            for o in original_selected:
                if o and o.name in bpy.data.objects:
                    try: o.select_set(True)
                    except (ReferenceError, RuntimeError): pass
            if original_active and original_active.name in bpy.data.objects:
                context.view_layer.objects.active = original_active
                
    def _validate_textures(self, context, objects_to_export):
        """
        [DEFINITIVE V11 - NON-DESTRUCTIVE VALIDATION]
        Performs a READ-ONLY check on all textures. It ensures that for every
        image used, Blender either knows its file path on disk OR has the pixel
        data packed in memory. It does NOT modify any image datablocks.
        The worker is now responsible for handling the unpacking of in-memory data.
        """
        logging.info("Starting non-destructive texture validation...")
    
        has_unrecoverable_textures = False
        processed_materials = set()

        def get_all_image_nodes_recursive(node_tree):
            for node in node_tree.nodes:
                if node.type == 'TEX_IMAGE' and node.image:
                    yield node.image
                elif node.type == 'GROUP' and node.node_tree:
                    yield from get_all_image_nodes_recursive(node.node_tree)

        for obj in objects_to_export:
            if obj.type != 'MESH' or not obj.data:
                continue
        
            for slot in obj.material_slots:
                mat = slot.material
                if not mat or not mat.use_nodes or mat in processed_materials:
                    continue
            
                processed_materials.add(mat)
                for image in get_all_image_nodes_recursive(mat.node_tree):
                    if not image:
                        continue
                
                    # Try to force a pixel read to update the has_data flag
                    try:
                        _ = len(image.pixels)
                    except RuntimeError:
                        pass # This is expected if data is truly missing

                    filepath = ""
                    try:
                        if image.filepath_from_user():
                            filepath = abspath(image.filepath_from_user())
                    except Exception:
                        filepath = ""

                    # The core validation: A texture is valid if it has a path OR has packed data.
                    is_valid_on_disk = os.path.exists(filepath)
                    has_packed_data = image.has_data

                    if not is_valid_on_disk and not has_packed_data:
                        logging.error(
                            f"UNRECOVERABLE: Image '{image.name}' in material '{mat.name}' has NO pixel data in memory, AND its source file is missing. The addon cannot proceed."
                        )
                        has_unrecoverable_textures = True

        if has_unrecoverable_textures:
            self.report({'ERROR'}, "Unrecoverable textures found. Export aborted. See System Console.")
            return False

        logging.info("Texture validation successful. All textures are either on disk or packed.")
        return True

    def _validate_and_recover_image_source(self, image_datablock, temp_dir):
        """
        Ensures an image datablock has a valid, on-disk source file for the baker to read.
        If the path is invalid but pixel data exists (e.g., packed file), it saves
        the data to the provided temporary directory and reloads it.
        This logic is copied from the addon's own _prepare_and_validate_textures function.
        """
        if not image_datablock:
            return True

        filepath = ""
        try:
            # Use filepath_from_user() to respect user-set paths
            filepath = abspath(image_datablock.filepath_from_user())
        except Exception:
            logging.debug(f"Could not resolve path for image '{image_datablock.name}'. Will attempt recovery.")
            filepath = ""

        # If the file doesn't exist on disk, but Blender has the pixel data in memory
        if not os.path.exists(filepath) and image_datablock.has_data:
            logging.warning(f"Source image '{image_datablock.name}' has no valid file path. Recovering from memory for bake.")
            try:
                safe_name = "".join(c for c in image_datablock.name if c.isalnum() or c in ('_', '.', '-')).strip()
                ext = ".png" # Default to PNG for recovery
                
                # For UDIMs, the name might be like 'texture.<UDIM>.png'. We need a clean base name.
                base_name = re.sub(r'<UDIM>', 'tile', safe_name) # Replace udim token for the temp file
                base_name, _ = os.path.splitext(base_name)
                recovery_path = os.path.join(temp_dir, f"{base_name}{ext}")

                # Save a copy of the image data to the new path
                # This forces the data onto the disk where the baker can find it.
                image_copy = image_datablock.copy()
                image_copy.filepath_raw = recovery_path
                image_copy.file_format = 'PNG'
                image_copy.save()
                
                # CRITICAL: Point the original image datablock to the newly saved file and reload
                image_datablock.filepath = recovery_path
                image_datablock.source = 'FILE' # It's now a single file, not a tiled source for the purpose of this bake
                image_datablock.reload()
                
                logging.info(f"Successfully recovered source image '{image_datablock.name}' to '{recovery_path}'")
                # Add the temp file to the cleanup list
                self._export_data['temp_files_to_clean'].add(recovery_path)

            except Exception as e:
                self.report({'ERROR'}, f"Failed to recover source image data for '{image_datablock.name}': {e}")
                logging.error(f"Could not save in-memory data for source image '{image_datablock.name}': {e}", exc_info=True)
                return False # This is a critical failure
        
        return True
                                                                              
    def _is_simple_pbr_setup(self, mat):
        """
        [DEFINITIVE V4 - RECURSIVE] Determines if a material is simple.
        This version uses a dedicated recursive helper function (_is_branch_procedural)
        to correctly traverse the entire node tree, including arbitrarily nested node
        groups, from every relevant input socket. It is guaranteed to find any
        procedural node in the chain.
        """
        if not mat or not mat.use_nodes or not mat.node_tree:
            return False

        # Find the essential nodes for a complete material analysis
        bsdf_node = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
        output_node = next((n for n in mat.node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
        if not output_node:
            output_node = next((n for n in mat.node_tree.nodes if n.type == 'OUTPUT_MATERIAL'), None)

        # A material isn't a simple PBR setup if it's missing these key components
        if not output_node or not bsdf_node:
            return False

        # Gather all top-level sockets that feed the final material output
        sockets_to_check = []
        sockets_to_check.extend(bsdf_node.inputs)
        sockets_to_check.extend([output_node.inputs['Displacement'], output_node.inputs['Volume']])

        # For each connected input, start a deep recursive search.
        for socket in sockets_to_check:
            if socket.is_linked:
                start_node = socket.links[0].from_node
                # Call the recursive helper. If it finds anything procedural, the material is complex.
                if self._is_branch_procedural(start_node, set()):
                    logging.info(
                        f"Material '{mat.name}' is complex. Reason: A procedural node was found in the "
                        f"chain leading to the '{socket.name}' input."
                    )
                    return False # Bake is required

        # If all connected branches are clean, the material is simple.
        logging.info(f"Material '{mat.name}' has a simple PBR setup. Baking will be skipped.")
        return True

        
    def _is_branch_procedural(self, current_node, visited_nodes):
        """
        [RECURSIVE HELPER] Traverses backwards from a starting node. Returns True if
        it finds a procedural node, and False if the entire branch ends in only
        textures or safe passthroughs. Handles nested node groups correctly.
        """
        # Base Case 1: We've already checked this node, or the branch is empty.
        if not current_node or current_node in visited_nodes:
            return False # Not procedural

        visited_nodes.add(current_node)

        # Base Case 2: We've reached a texture. This is a simple, valid endpoint.
        if current_node.type == 'TEX_IMAGE':
            return False # Not procedural

        # Define nodes that don't generate data themselves but just pass it through.
        SAFE_PASSTHROUGH_NODES = {
            'ShaderNodeUVMap', 'ShaderNodeTexCoord', 'ShaderNodeNormalMap',
            'ShaderNodeAttribute', 'NodeReroute', 'ShaderNodeMapping',
            'ShaderNodeDisplacement' # <-- THIS IS THE SURGICAL CHANGE
        }

        # Recursive Case 1: The node is a safe passthrough. We need to check what feeds into it.
        if current_node.bl_idname in SAFE_PASSTHROUGH_NODES:
            for input_socket in current_node.inputs:
                if input_socket.is_linked:
                    prev_node = input_socket.links[0].from_node
                    # If any of the inputs are fed by a procedural branch, this whole branch is procedural.
                    if self._is_branch_procedural(prev_node, visited_nodes):
                        return True
            return False # All inputs to this passthrough node were simple.

        # Recursive Case 2: The node is a group. We need to dive inside and check its origins.
        if current_node.type == 'GROUP' and current_node.node_tree:
            group_output = next((n for n in current_node.node_tree.nodes if n.type == 'GROUP_OUTPUT'), None)
            if group_output:
                for input_socket in group_output.inputs:
                    if input_socket.is_linked:
                        prev_node = input_socket.links[0].from_node
                        # If any branch inside the group is procedural, the whole group is.
                        if self._is_branch_procedural(prev_node, visited_nodes):
                            return True
            return False # All inputs inside this group were simple.

        # Final Case: If the node is not a texture and not a safe passthrough/group,
        # it MUST be a procedural node (Mix, Math, Noise, etc.).
        return True # This branch is procedural.
        
    def _find_largest_texture_resolution_recursive(self, node_tree, visited_groups=None):
        """
        Recursively traverses a node tree, including nested groups, to find the
        maximum width and height among all TEX_IMAGE nodes.
        """
        if visited_groups is None:
            visited_groups = set()

        max_w, max_h = 0, 0

        for node in node_tree.nodes:
            if node.type == 'TEX_IMAGE' and node.image:
                max_w = max(max_w, node.image.size[0])
                max_h = max(max_h, node.image.size[1])
            elif node.type == 'GROUP' and node.node_tree and node.node_tree.name not in visited_groups:
                visited_groups.add(node.node_tree.name)
                group_w, group_h = self._find_largest_texture_resolution_recursive(node.node_tree, visited_groups)
                max_w = max(max_w, group_w)
                max_h = max(max_h, group_h)

        return max_w, max_h
        
    def _get_texture_path_from_socket(self, socket):
        """
        Traces a socket back to its ultimate source node and, if it's a TEX_IMAGE
        node, returns the absolute path to its image file.
        """
        if not socket or not socket.is_linked:
            return None
        
        source_node = self._find_ultimate_source_node(socket)
        
        if source_node and source_node.type == 'TEX_IMAGE' and source_node.image:
            try:
                filepath = abspath(source_node.image.filepath_from_user())
                if os.path.exists(filepath):
                    return filepath
            except Exception:
                pass

        return None

    def _material_has_decal_setup(self, mat):
        """
        Checks if a material has a decal setup by looking for a Mix Shader
        node anywhere in the path between the main BSDF and the Material Output.
        """
        if not mat or not mat.use_nodes or not mat.node_tree:
            return False
        
        nt = mat.node_tree
        bsdf_node, active_output_node = self._find_bsdf_and_output_nodes(nt)

        if bsdf_node and active_output_node and active_output_node.inputs['Surface'].is_linked:
            start_node = active_output_node.inputs['Surface'].links[0].from_node
            found_decal_info = self._find_universal_decal_mixer(start_node, bsdf_node, set())
            return found_decal_info is not None
            
        return False

    # --- MODIFIED TASK COLLECTION FUNCTION ---
    def _initialize_bake_session(self, export_data):
        """Initializes the bake directory and data structures for a new session."""
        if not is_blend_file_saved():
            raise RuntimeError("Blend file must be saved to create a bake/temp directory.")

        bake_dir = CUSTOM_COLLECT_PATH
        os.makedirs(bake_dir, exist_ok=True)

        bake_info = {
            'tasks': [],
            'bake_dir': bake_dir,
            'special_texture_info': defaultdict(list),
            'udim_materials': set(),
            'cached_materials': {}
        }
        export_data['bake_info'] = bake_info

        global global_image_hash_cache
        global_image_hash_cache.clear()
        
        logging.info("Bake session initialized and image cache cleared.")
        return bake_info

    def _identify_and_prepare_udim_atlases(self, objects_to_process):
        """
        Performs a pre-pass to find objects with UDIM materials and creates the
        necessary 'remix_atlas_uv' map for them to prevent race conditions.
        """
        objects_needing_atlas = defaultdict(set)
        for obj in objects_to_process:
            if obj.type != 'MESH' or not obj.data: continue
            for slot in obj.material_slots:
                mat = slot.material
                if mat and self._material_uses_udims(mat):
                    udim_node = next((n for n in mat.node_tree.nodes if n.type == 'TEX_IMAGE' and n.image and n.image.source == 'TILED'), None)
                    if udim_node and udim_node.image:
                        tiles = sorted([t for t in udim_node.image.tiles if t.label], key=lambda t: t.number)
                        if tiles:
                            tile_tuple = tuple(t.number for t in tiles)
                            objects_needing_atlas[tile_tuple].add(obj)

        if objects_needing_atlas:
            logging.info("Pre-creating UDIM atlas UV maps to prevent race condition...")
            for tile_numbers, object_set in objects_needing_atlas.items():
                tiles_for_transform = [type('ImageTile', (object,), {'number': num})() for num in tile_numbers]
                self._transform_uvs_for_atlas(list(object_set), tiles_for_transform)

    def _create_bake_task(self, obj, mat, channel_details, bake_settings, bake_info, special_texture_map):
        """Creates a dictionary for a single bake task."""
        channel_name, bake_type, is_val, is_color = channel_details
        safe_mat_name = "".join(c for c in mat.name if c.isalnum() or c in ('_', '-')).strip()
        safe_socket_name = channel_name.replace(' ', '')
        hash_for_filename = bake_settings['material_hash'][:8] if bake_settings['material_hash'] else f"NOHSH_{uuid.uuid4().hex[:6]}"
        output_filename = f"{safe_mat_name}_{hash_for_filename}_{safe_socket_name}.png"
        output_path = os.path.join(bake_info['bake_dir'], output_filename)

        if channel_name in special_texture_map:
            bake_info['special_texture_info'][(obj.name, mat.name)].append({
                'path': output_path, 'type': special_texture_map[channel_name]
            })

        final_bake_type = 'EMIT' if bake_settings['uses_udims'] and bake_type == 'DIFFUSE' else bake_type

        return {
            "material_name": mat.name, "material_uuid": bake_settings['material_uuid'], "object_name": obj.name,
            "bake_type": final_bake_type, "output_path": output_path, "target_socket_name": channel_name,
            "is_value_bake": is_val, "is_color_data": is_color,
            "resolution_x": bake_settings['resolution_x'], "resolution_y": bake_settings['resolution_y'],
            "uv_layer": bake_settings['uv_layer'], "material_hash": bake_settings['material_hash'],
            "bake_method": bake_settings['bake_method']
        }

    def _generate_tasks_for_material(self, obj, slot_index, mat, bake_info, bake_method, channels, special_texture_map):
        """
        Analyzes a single material on a specific object and generates all necessary
        bake tasks for it, returning an empty list if no baking is needed.
        """
        material_tasks = []
        
        uses_udims = self._material_uses_udims(mat)
        if uses_udims and mat.name not in bake_info['udim_materials']:
            bake_info['udim_materials'].add(mat.name)

        material_hash = get_material_hash(mat, obj, slot_index, image_hash_cache=global_image_hash_cache, bake_method=bake_method)
        hash_for_log = f"Hash: {material_hash[:8]}..." if material_hash else "Hash: [FAILED]"

        if material_hash and material_hash in global_material_hash_cache:
            logging.info(f"  CACHE HIT: Context for '{mat.name}' on '{obj.name}' ({hash_for_log}) is cached. Reusing.")
            cached_data = global_material_hash_cache[material_hash]
            bake_info['cached_materials'][material_hash] = cached_data
            for socket_name, path in cached_data.items():
                if socket_name in special_texture_map:
                     bake_info['special_texture_info'][(obj.name, mat.name)].append({'path': path, 'type': special_texture_map[socket_name]})
            return []

        logging.info(f"  CACHE MISS: Context for '{mat.name}' on '{obj.name}' ({hash_for_log}) will be processed.")
        is_complex = not self._is_simple_pbr_setup(mat)
        has_decal = _material_has_decal_setup(mat)

        if is_complex or uses_udims:
            log_reason_parts = []
            if is_complex: log_reason_parts.append("complex setup")
            if uses_udims: log_reason_parts.append("UDIM textures")
            logging.info(f"  - Queuing FULL BAKE for material '{mat.name}' on '{obj.name}' (Reason: {', '.join(log_reason_parts)}).")

            DEFAULT_BAKE_RESOLUTION = 2048
            res_x, res_y = DEFAULT_BAKE_RESOLUTION, DEFAULT_BAKE_RESOLUTION
            uv_layer = obj.data.uv_layers.active.name if obj.data.uv_layers.active else obj.data.uv_layers[0].name

            if uses_udims:
                udim_node = next((n for n in mat.node_tree.nodes if n.type == 'TEX_IMAGE' and n.image and n.image.source == 'TILED'), None)
                if udim_node and udim_node.image:
                    tiles = sorted([t for t in udim_node.image.tiles if t.label], key=lambda t: t.number)
                    if tiles:
                        tile_width, tile_height = udim_node.image.size
                        if tile_width > 0 and tile_height > 0:
                            res_x, res_y = tile_width * len(tiles), tile_height
                            logging.info(f"   - UDIMs detected. Setting bake resolution to {res_x}x{res_y} for atlas.")
                uv_layer = "remix_atlas_uv"
            else:
                max_w, max_h = self._find_largest_texture_resolution_recursive(mat.node_tree)
                if max_w > 0: res_x = max_w
                if max_h > 0: res_y = max_h
                if max_w > 0 or max_h > 0: logging.info(f"   - Dynamically set bake resolution to {res_x}x{res_y}.")

            mat_uuid = mat.get("uuid", str(uuid.uuid4())); mat["uuid"] = mat_uuid
            task_templates = list(channels['core'])
            bsdf, output_node = _find_bsdf_and_output_nodes(mat.node_tree)

            for channel_details in channels['optional']:
                channel_name = channel_details[0]
                socket = (output_node.inputs.get(channel_name) if channel_name == "Displacement" and output_node else (bsdf.inputs.get(channel_name) if bsdf else None))
                if (socket and socket.is_linked) or (channel_name == "Alpha" and socket and not math.isclose(socket.default_value, 1.0)):
                    task_templates.append(channel_details)
            
            bake_settings = {'material_hash': material_hash, 'resolution_x': res_x, 'resolution_y': res_y, 'uv_layer': uv_layer, 'bake_method': bake_method, 'material_uuid': mat_uuid, 'uses_udims': uses_udims}
            for channel_details in task_templates:
                material_tasks.append(self._create_bake_task(obj, mat, channel_details, bake_settings, bake_info, special_texture_map))
        
        elif has_decal:
            logging.info(f"  - Queuing DECAL COMPOSITE task for simple material '{mat.name}' on '{obj.name}'.")
            bsdf_node, _ = _find_bsdf_and_output_nodes(mat.node_tree)
            if bsdf_node:
                original_base_color_path = self._get_texture_path_from_socket(bsdf_node.inputs['Base Color'])
                if not original_base_color_path:
                    logging.warning(f"    - Could not find a valid source texture for 'Base Color' on simple material '{mat.name}'. It will be treated as black.")
                
                DEFAULT_BAKE_RESOLUTION = 2048
                max_w, max_h = self._find_largest_texture_resolution_recursive(mat.node_tree)
                res_x = max_w if max_w > 0 else DEFAULT_BAKE_RESOLUTION
                res_y = max_h if max_h > 0 else DEFAULT_BAKE_RESOLUTION
                mat_uuid = mat.get("uuid", str(uuid.uuid4())); mat["uuid"] = mat_uuid
                
                output_path = os.path.join(bake_info['bake_dir'], f"{''.join(c for c in mat.name if c.isalnum())}_{material_hash[:8]}_BaseColor.png")
                
                material_tasks.append({
                    "material_name": mat.name, "material_uuid": mat_uuid, "object_name": obj.name,
                    "bake_type": "EMIT", "target_socket_name": "Base Color", "output_path": output_path,
                    "resolution_x": res_x, "resolution_y": res_y, "uv_layer": obj.data.uv_layers.active.name,
                    "material_hash": material_hash, "bake_method": bake_method, "is_simple_decal_composite": True,
                    "original_base_color_path": original_base_color_path
                })
                if material_hash:
                    if material_hash not in global_material_hash_cache: global_material_hash_cache[material_hash] = {}
                    global_material_hash_cache[material_hash]['Base Color'] = output_path
                    for socket_name in ["Metallic", "Roughness", "Normal"]:
                         path = self._get_texture_path_from_socket(bsdf_node.inputs[socket_name])
                         if path: global_material_hash_cache[material_hash][socket_name] = path
        else:
            logging.info(f"  - Material '{mat.name}' is simple. Checking for existing special textures to use directly.")
            bsdf, output_node = _find_bsdf_and_output_nodes(mat.node_tree)
            sockets_to_scan = {}
            if bsdf:
                sockets_to_scan.update({"Emission Color": bsdf.inputs.get("Emission Color"), "Alpha": bsdf.inputs.get("Alpha")})
            if output_node:
                sockets_to_scan["Displacement"] = output_node.inputs.get("Displacement")

            for socket_name, socket in sockets_to_scan.items():
                if socket and socket.is_linked:
                    texture_path = self._get_texture_path_from_socket(socket)
                    if texture_path and os.path.exists(texture_path):
                        server_texture_type = special_texture_map.get(socket_name)
                        if server_texture_type:
                            logging.info(f"    > Found direct-use special map for '{socket_name}' at: {os.path.basename(texture_path)}")
                            bake_info['special_texture_info'][(obj.name, mat.name)].append({'path': texture_path, 'type': server_texture_type})

        return material_tasks

    def collect_bake_tasks(self, context, objects_to_process, export_data):
        """
        Main entry point to generate all bake tasks. It orchestrates the process by
        calling its own specialized helper methods.
        """
        bake_info = self._initialize_bake_session(export_data)
        
        addon_prefs = context.preferences.addons[__name__].preferences
        bake_method = addon_prefs.bake_method
        logging.info(f"  > Using selected Bake Method for all tasks: {bake_method}.")

        SPECIAL_TEXTURE_MAP = {
            "Displacement": "HEIGHT", "Emission Color": "EMISSIVE", "Alpha": "OPACITY",
            "Anisotropy": "ANISOTROPY", "Transmission": "TRANSMITTANCE",
            "Subsurface Radius": "MEASUREMENT_DISTANCE", "Subsurface Scale": "SINGLE_SCATTERING"
        }
        
        channels = {
            'core': [("Base Color", 'DIFFUSE', False, True), ("Metallic", 'EMIT', True, False), ("Roughness", 'ROUGHNESS', True, False), ("Normal", 'NORMAL', False, False)] if bake_method == 'NATIVE' else [("Base Color", 'EMIT', False, True), ("Metallic", 'EMIT', True, False), ("Roughness", 'EMIT', True, False), ("Normal", 'NORMAL', False, False)],
            'optional': [("Alpha", 'EMIT', True, False), ("Displacement", 'DISPLACEMENT', True, False), ("Emission Color", 'EMIT', False, True), ("Anisotropy", 'EMIT', True, False), ("Transmission", 'EMIT', True, False), ("Subsurface Radius", 'EMIT', False, True), ("Subsurface Scale", 'EMIT', True, False)]
        }

        logging.info("Analyzing materials with mesh-aware caching...")
        self._identify_and_prepare_udim_atlases(objects_to_process)
        
        all_tasks = []
        for obj in objects_to_process:
            if obj.type != 'MESH' or not obj.data or not obj.data.uv_layers:
                continue

            for slot_index, slot in enumerate(obj.material_slots):
                mat = slot.material
                if not mat or not mat.use_nodes:
                    continue
                
                material_tasks = self._generate_tasks_for_material(obj, slot_index, mat, bake_info, bake_method, channels, SPECIAL_TEXTURE_MAP)
                all_tasks.extend(material_tasks)

        bake_info['tasks'] = all_tasks
        if bake_info['tasks']:
            logging.info(f"Generated {len(bake_info['tasks'])} new bake tasks.")
        if bake_info['cached_materials']:
            logging.info(f"Will reuse cached textures for {len(bake_info['cached_materials'])} material contexts.")
            
        return all_tasks, {}, bake_info['bake_dir'], bake_info.get('special_texture_info', {})
        
    def _launch_persistent_worker(self):
        """Launches a single persistent worker and starts the communication threads."""
        if self._persistent_worker:
            return True # Worker already running

        self._results_queue = Queue()
        self._log_queue = Queue()

        cmd = [
            bpy.app.binary_path,
            "--background",
            "--python", BAKE_WORKER_PY,
            "--",
            "--persistent"
        ]

        try:
            flags = subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0
            self._persistent_worker = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                creationflags=flags, text=True, encoding='utf-8', bufsize=1
            )
        
            # --- THIS IS THE PRECISE FIX ---
            # The 'args' tuple was missing, causing the TypeError. We pass the worker
            # process to the thread target functions as they expect.
            self._comm_thread = threading.Thread(target=self._communication_thread_target, args=(self._persistent_worker,), daemon=True)
            self._comm_thread.start()

            self._log_thread = threading.Thread(target=self._log_thread_target, args=(self._persistent_worker,), daemon=True)
            self._log_thread.start()
            # --- END OF FIX ---

            logging.info(f"→ Launched persistent worker PID {self._persistent_worker.pid}")
            return True
        except Exception as e:
            logging.error(f"Could not launch persistent bake worker: {e}", exc_info=True)
            return False
                                        
    def _prepare_and_validate_textures(self, context, objects_to_export):
        """
        [DEFINITIVE V20 - ROBUST NAME-BASED MAPPING]
        This version abandons the use of custom property UUIDs, which proved unreliable
        during the 'bpy.data.libraries.write' operation. It now creates a translation map
        where the key is the original 'image.name' from the main Blender session. The worker
        will use this name to find the corresponding (potentially renamed) datablock.
        """
        logging.info("Starting texture preparation (Robust Name-Based Mapping Strategy)...")

        bake_dir = CUSTOM_COLLECT_PATH
        os.makedirs(bake_dir, exist_ok=True)
        texture_translation_map = {}
        has_unrecoverable_textures = False

        # Helper to find only images actively used in the material node graph
        def _find_live_images(start_node):
            live_images_in_tree = set()
            nodes_to_visit = collections.deque([start_node])
            visited_nodes = {start_node}
            while nodes_to_visit:
                current_node = nodes_to_visit.popleft()
                if current_node.type == 'TEX_IMAGE' and current_node.image:
                    live_images_in_tree.add(current_node.image)
                for input_socket in current_node.inputs:
                    if input_socket.is_linked:
                        for link in input_socket.links:
                            prev_node = link.from_node
                            if prev_node not in visited_nodes:
                                visited_nodes.add(prev_node)
                                nodes_to_visit.append(prev_node)
                if current_node.type == 'GROUP' and current_node.node_tree:
                    group_tree = current_node.node_tree
                    group_output = next((n for n in group_tree.nodes if n.type == 'GROUP_OUTPUT'), None)
                    if group_output and group_output not in visited_nodes:
                            visited_nodes.add(group_output)
                            nodes_to_visit.append(group_output)
            return live_images_in_tree

        materials_to_scan = {
            slot.material for obj in objects_to_export
            if obj.data for slot in obj.material_slots if slot.material and slot.material.use_nodes
        }

        all_live_images = set()
        for mat in materials_to_scan:
            output_node = next((n for n in mat.node_tree.nodes if n.type == 'OUTPUT_MATERIAL'), None)
            if output_node:
                all_live_images.update(_find_live_images(output_node))

        for image in all_live_images:
            image_name_key = image.name
            if not image_name_key or image_name_key in texture_translation_map:
                continue

            resolved_path = ""
            is_on_disk = False

            if image.library:
                try:
                    resolved_path = bpy.path.abspath(image.filepath, library=image.library)
                    if os.path.exists(resolved_path): is_on_disk = True
                except Exception: pass
    
            if not is_on_disk:
                try:
                    resolved_path = bpy.path.abspath(image.filepath)
                    if os.path.exists(resolved_path): is_on_disk = True
                except Exception: pass

            if is_on_disk:
                texture_translation_map[image_name_key] = resolved_path
                continue

            # Attempt aggressive recovery from memory
            try:
                if image.size[0] == 0 or image.size[1] == 0: raise RuntimeError("Image has zero dimensions.")
                _ = image.pixels[0] # Force a pixel read to ensure data is accessible

                safe_name = "".join(c for c in image.name if c.isalnum() or c in ('_', '.', '-')).strip()
                temp_filename = f"recovered_{safe_name}_{uuid.uuid4().hex[:6]}.png"
                new_safe_path = os.path.join(bake_dir, temp_filename)

                temp_image = bpy.data.images.new(name=f"temp_save_{image.name}", width=image.size[0], height=image.size[1], alpha=True)
                temp_image.pixels = image.pixels[:]
                temp_image.filepath_raw = new_safe_path
                temp_image.file_format = 'PNG'
                temp_image.save()
        
                texture_translation_map[image_name_key] = new_safe_path
                self._export_data['temp_files_to_clean'].add(new_safe_path)
                bpy.data.images.remove(temp_image)
                logging.info(f"  > Successfully recovered '{image.name}' to temp file: {new_safe_path}")

            except Exception as e:
                logging.error(f"  - UNRECOVERABLE: Image '{image.name}' has no valid path and no readable pixel data. Reason: {e}")
                texture_translation_map[image_name_key] = "GHOST_DATA_UNRECOVERABLE"
                has_unrecoverable_textures = True

        if has_unrecoverable_textures:
            self.report({'ERROR'}, "Unrecoverable/missing textures found. Export aborted. See System Console.")
            return None # Return None on failure

        logging.info("Texture preparation complete. Handing off to workers for baking and final cleanup.")
        return texture_translation_map
    
    def modal(self, context, event):
        if event.type != 'TIMER':
            return {'PASS_THROUGH'}

        with self._op_lock:
            # --- START OF THE DEFINITIVE FIX ---
            # Phase 0: Check for Completion FIRST. This is the highest priority.
            if self._finished_tasks >= self._total_tasks and self._operator_state not in ['FINISHING', 'CLEANING_UP']:
                logging.info("All bake tasks are complete. Moving to finalization.")
                self._operator_state = 'FINISHING'
                
                if self._failed_tasks > 0:
                    self.report({'ERROR'}, f"{self._failed_tasks} bake task(s) failed. See console.")
                    return self._cleanup(context, {'CANCELLED'})
                else:
                    try:
                        self._finalize_export(context)
                        self.report({'INFO'}, f"Export complete. Baked {self._total_tasks} textures.")
                        return self._cleanup(context, {'FINISHED'})
                    except Exception as e:
                        logging.error(f"A critical error occurred during _finalize_export: {e}", exc_info=True)
                        self.report({'ERROR'}, "Finalization failed. See console for details.")
                        return self._cleanup(context, {'CANCELLED'})
            # --- END OF THE DEFINITIVE FIX ---

            # --- Phase 1: Process Logs & Worker Results ---
            try:
                while not self._log_queue.empty():
                    print(self._log_queue.get_nowait())
            except Empty:
                pass

            try:
                while not self._results_queue.empty():
                    result_line = self._results_queue.get_nowait()
                    try:
                        result = json.loads(result_line)
                        worker_pid = result.get("pid")
                        slot_index = next((i for i, s in enumerate(self._worker_slots) if s.get('process') and s['process'].pid == worker_pid), -1)
                        if slot_index == -1:
                            continue

                        slot = self._worker_slots[slot_index]
                        status = result.get("status")

                        if status == "ready":
                            slot['status'] = 'ready'
                            slot['ready_time'] = time.monotonic()
                            logging.info(f"Worker in slot {slot_index} (PID: {worker_pid}) is READY. (Init time: {slot['ready_time'] - slot['launch_time']:.2f}s)")
                
                        elif status in ["success", "failure"]:
                            self._finished_tasks += 1
                            slot['tasks_completed'] += 1
                            if status == "failure":
                                self._failed_tasks += 1
                    
                            if self._operator_state == 'STABILIZING':
                                self._initial_tasks_finished_count += 1
                                logging.info(f"Initial task finished. ({self._initial_tasks_finished_count}/{min(self.INITIAL_WORKER_COUNT, self._total_tasks)} needed to start scaling)")

                            if slot['peak_ram_on_task'] > 0:
                                n = sum(s['tasks_completed'] for s in self._worker_slots)
                                self._running_average_peak_ram = self._running_average_peak_ram * (n - 1) / n if n > 1 else slot['peak_ram_on_task']
                    
                            slot['status'] = 'ready'
                            slot['task_start_time'] = 0 # Reset task timer
                    
                        elif status == "error":
                            logging.error(f"Worker in slot {slot_index} reported a critical error: {result.get('details', 'N/A')}")
                            self._handle_failed_worker(slot_index, requeue_task=True)
                    except (json.JSONDecodeError, KeyError):
                        pass
            except Empty:
                pass

            # --- Phase 2: Dispatch Tasks to Ready Workers ---
            for i, slot in enumerate(self._worker_slots):
                if slot['status'] == 'ready' and self._master_task_queue:
                    task_to_dispatch = self._master_task_queue.popleft()
                    # The global_task_number and total_tasks are now pre-assigned.
                    # We no longer need to manage a dispatch counter here.
                    task_to_dispatch['task_blend_file'] = bpy.data.filepath
                    try:
                        slot['process'].stdin.write(json.dumps(task_to_dispatch) + "\n")
                        slot['process'].stdin.flush()
                        slot['status'] = 'running'
                        slot['current_task'] = task_to_dispatch
                        slot['peak_ram_on_task'] = 0
                        slot['task_start_time'] = time.monotonic() # Start the task timer
                    except (IOError, BrokenPipeError):
                        logging.error(f"Pipe to worker {i} was broken. Requeueing task and handling failed worker.")
                        self._master_task_queue.appendleft(task_to_dispatch)
                        # No dispatch counter to decrement anymore.
                        self._handle_failed_worker(i, requeue_task=False)

            # --- Phase 3: Main State Machine Logic ---
            current_time = time.monotonic()
            cpu_now, ram_now = self._get_system_resources()
            self._update_peak_utilization(cpu_now, ram_now)

            if self._operator_state == 'RAMPING_UP':
                logging.info("--- State: Ramping Up ---")
                bpy.ops.wm.save_mainfile()
        
                num_to_launch = min(len(self._worker_slots), self.INITIAL_WORKER_COUNT, self._total_tasks)
                logging.info(f"Launching initial set of {num_to_launch} workers...")
                for i in range(num_to_launch):
                    self._launch_new_worker(i)
        
                self._initial_tasks_finished_count = 0
                self._operator_state = 'STABILIZING'
                logging.info(f"Entering stabilization. Waiting for {num_to_launch} initial task(s) to complete.")

            elif self._operator_state == 'STABILIZING':
                num_required = min(self.INITIAL_WORKER_COUNT, self._total_tasks)
                if self._initial_tasks_finished_count >= num_required:
                    logging.info("--- State: Stabilization Finished (event-driven). Switching to Running. ---")
                    self._operator_state = 'RUNNING'
                    self._next_resource_check_time = current_time

            elif self._operator_state == 'RUNNING':
                if current_time >= self._next_resource_check_time:
                    self._next_resource_check_time = current_time + self.RESOURCE_CHECK_INTERVAL_SEC
            
                    is_cpu_high = cpu_now > self.CPU_HIGH_THRESHOLD
                    is_ram_high = ram_now > self.RAM_HIGH_THRESHOLD

                    if is_cpu_high or is_ram_high:
                        self._high_usage_counter += 1
                        if self._high_usage_counter >= self.HIGH_USAGE_SUSTAINED_CHECKS:
                            logging.warning(f"Sustained high resource usage detected (CPU:{cpu_now}%, RAM:{ram_now}%). Initiating scale-down.")
                            
                            running_workers = [(i, s) for i, s in enumerate(self._worker_slots) if s['status'] in ['running', 'ready']]
                            
                            if len(running_workers) > self.INITIAL_WORKER_COUNT:
                                if is_cpu_high and not is_ram_high:
                                    running_workers.sort(key=lambda item: item[1].get('task_start_time', 0))
                                    slot_to_terminate_index, _ = running_workers[0]
                                    logging.warning(f"  > High CPU is the primary issue. Terminating longest-running worker (Slot {slot_to_terminate_index}) as a precaution against stalls.")
                                    self._handle_failed_worker(slot_to_terminate_index, requeue_task=True)
                                elif is_ram_high:
                                    running_workers.sort(key=lambda item: item[1]['tasks_completed'])
                                    slot_to_terminate_index, _ = running_workers[0]
                                    logging.warning(f"  > High RAM is the primary issue. Terminating least productive worker (Slot {slot_to_terminate_index}).")
                                    self._handle_failed_worker(slot_to_terminate_index, requeue_task=True)
                            
                            self._high_usage_counter = 0
                    else:
                        self._high_usage_counter = 0

            # --- Phase 4: Crash & Stall Detection ---
            TASK_TIMEOUT_SECONDS = 300 # 5 minutes
            for i, slot in enumerate(self._worker_slots):
                if slot.get('process') and slot['process'].poll() is not None and slot['status'] in ['running', 'launching']:
                    logging.error(f"Worker in slot {i} (PID: {slot.get('process').pid}) has crashed unexpectedly!")
                    self._handle_failed_worker(i, requeue_task=True)
                
                task_start_time = slot.get('task_start_time', 0)
                if slot['status'] == 'running' and task_start_time > 0 and (current_time - task_start_time) > TASK_TIMEOUT_SECONDS:
                    logging.error(f"Worker in slot {i} (PID: {slot.get('process').pid}) has been running the same task for over {TASK_TIMEOUT_SECONDS} seconds. Assuming stall and terminating.")
                    self._handle_failed_worker(i, requeue_task=True)
    
            # --- Phase 5: UI Update ---
            if self._operator_state != 'FINISHING':
                progress = (self._finished_tasks / self._total_tasks) * 100 if self._total_tasks > 0 else 100
                active_workers = sum(1 for s in self._worker_slots if s['status'] in ['running', 'launching', 'ready'])
                status_text = (f"Baking... {self._finished_tasks}/{self._total_tasks} ({progress:.0f}%) | "
                               f"Active: {active_workers} | Queued: {len(self._master_task_queue)} | State: {self._operator_state}")
                if self._failed_tasks > 0:
                    status_text += f" | FAILED: {self._failed_tasks}"
                context.workspace.status_text_set(status_text)

            return {'PASS_THROUGH'}
            
    def _handle_failed_worker(self, slot_index, requeue_task=True):
        """
        Manages a worker that has stopped, either by crashing or by being
        gracefully terminated. Can requeue the task it was working on.
        """
        if slot_index >= len(self._worker_slots): return
    
        slot = self._worker_slots[slot_index]
    
        # If requested, put the task it was working on back at the front of the queue.
        if requeue_task and 'current_task' in slot and slot['current_task']:
            task = slot['current_task']
            self._master_task_queue.appendleft(task)
            logging.warning(f"Requeueing task for material '{task.get('material_name')}' from failed worker {slot_index}.")
    
        slot['current_task'] = None
        slot['flagged_for_termination'] = False # Reset flag
        self._terminate_worker(slot_index) # This will terminate the process and set status to 'suspended'
        
    def _is_geonodes_generator(self, obj):
        """
        [MODIFIED FROM ADDON 2]
        Detects if an object is a complex Geometry Nodes generator that needs realization.
        The primary heuristic is checking if materials are set inside the node tree
        that are not present in the object's actual material slots.
        """
        if not hasattr(obj, 'modifiers'):
            return False

        gn_modifier = next((m for m in obj.modifiers if m.type == 'NODES'), None)
        if not gn_modifier or not gn_modifier.node_group:
            return False

        # Get all materials currently in the object's slots
        slot_materials = {s.material for s in obj.material_slots if s.material}

        node_tree = gn_modifier.node_group
        # Find all materials being set by "Set Material" nodes inside the tree
        node_materials = {
            n.inputs['Material'].default_value
            for n in node_tree.nodes
            if n.type == 'SET_MATERIAL' and n.inputs['Material'].default_value is not None
        }

        # If there are materials set in the nodes that are not in the object's slots,
        # it's a generator that needs to be realized.
        if node_materials and not node_materials.issubset(slot_materials):
            logging.info(f"Object '{obj.name}' detected as a GeoNodes generator.")
            return True

        return False
            
    def _combine_albedo_and_opacity(self, color_map_path, opacity_map_path, output_path):
        """
        [NEW - NON-DESTRUCTIVE] Loads a color map and a grayscale opacity map, combines them
        into a new RGBA image, and saves it to the specified 'output_path'. This function
        does not modify the original source files.
        """
        if not PILLOW_INSTALLED:
            logging.error("Pillow library is not installed. Cannot combine albedo and opacity maps.")
            self.report({'ERROR'}, "Pillow dependency not found. Cannot create transparency.")
            return False

        if not os.path.exists(color_map_path) or not os.path.exists(opacity_map_path):
            logging.warning(f"Skipping texture combination: one or both maps missing. Color: '{os.path.exists(color_map_path)}', Opacity: '{os.path.exists(opacity_map_path)}'")
            return False

        logging.info(f"  > Combining '{os.path.basename(color_map_path)}' with opacity from '{os.path.basename(opacity_map_path)}'")

        try:
            from PIL import Image

            # Load the base color map and ensure it has an alpha channel to modify.
            albedo_img = Image.open(color_map_path).convert("RGBA")

            # Load the opacity map and ensure it's a single-channel grayscale ("Luminance").
            opacity_img = Image.open(opacity_map_path).convert("L")

            # Ensure images are the same size before combining.
            if albedo_img.size != opacity_img.size:
                logging.warning(f"    - Albedo and opacity maps have different sizes. Resizing opacity map to {albedo_img.size}.")
                opacity_img = opacity_img.resize(albedo_img.size, Image.Resampling.LANCZOS)

            # This is the correct method: put the grayscale opacity_img into the alpha channel of the albedo_img.
            albedo_img.putalpha(opacity_img)

            # Save the combined RGBA image to the new, specified temporary output path.
            albedo_img.save(output_path, "PNG")
            logging.info(f"    - Successfully created temporary RGBA texture at: {os.path.basename(output_path)}")
            return True

        except Exception as e:
            logging.error(f"Failed during texture combination for '{color_map_path}': {e}", exc_info=True)
            self.report({'WARNING'}, "Failed to combine color and opacity maps.")
            return False

    def _get_system_resources(self):
        """Helper to get current CPU and RAM usage, returns (0,0) if psutil fails."""
        if PSUTIL_INSTALLED:
            import psutil
            return psutil.cpu_percent(), psutil.virtual_memory().percent
        return 0, 0

    def _update_peak_utilization(self, cpu, ram):
        """Updates the peak utilization for all currently running workers."""
        for slot in self._worker_slots:
            if slot['status'] == 'running':
                slot['peak_cpu_since_ready'] = max(slot['peak_cpu_since_ready'], cpu)
                # Update the new per-task peak RAM tracker
                slot['peak_ram_on_task'] = max(slot['peak_ram_on_task'], ram)
      
    def _preflight_validation(self, objects_to_process):
        """
        [NEW - Pre-flight Check]
        Validates that every material being processed is only assigned to objects
        that are valid for baking (e.g., have UV maps). This prevents a single
        "bad apple" object from corrupting a shared material's state and causing
        a misleading failure on a different, valid object.
        """
        logging.info("--- Starting Pre-flight Material & Object Validation ---")
        
        materials_to_check = {
            slot.material
            for obj in objects_to_process
            if obj.data
            for slot in obj.material_slots if slot.material
        }

        if not materials_to_check:
            logging.info("No materials to validate. Pre-flight check passed.")
            return True, ""

        # Build a map of every user of each material in the entire blend file
        all_materials_map = collections.defaultdict(list)
        for obj in bpy.data.objects:
            if obj.type == 'MESH':
                for slot in obj.material_slots:
                    if slot.material:
                        all_materials_map[slot.material].append(obj)

        for mat in materials_to_check:
            if mat in all_materials_map:
                for user_obj in all_materials_map[mat]:
                    # The critical check: Is this a mesh and does it lack a UV map?
                    if user_obj.type == 'MESH' and not user_obj.data.uv_layers:
                        error_message = (
                            f"Export Canceled: Pre-flight check failed.\n\n"
                            f"Material '{mat.name}' is used by object '{user_obj.name}', "
                            f"which is a MESH but has NO UV MAPS.\n\n"
                            f"Baking requires a UV map. Please add a UV map to '{user_obj.name}' or remove the material from it."
                        )
                        logging.error(error_message)
                        return False, error_message
        
        logging.info("--- Pre-flight Validation Successful ---")
        return True, ""

    def execute(self, context):
        if not PSUTIL_INSTALLED:
            self.report({'ERROR'}, "Dependency 'psutil' is not installed. Please install it from the addon panel.")
            return {'CANCELLED'}

        global export_lock
        if export_lock:
            self.report({'INFO'}, "Another export is already in progress.")
            return {'CANCELLED'}
    
        addon_prefs = context.preferences.addons[__name__].preferences
        if addon_prefs.remix_ingest_directory == "/ProjectFolder/Assets":
            message = "Please change the Ingest Directory from the default value before exporting."
            self.report({'ERROR'}, message)
            logging.error(message)
            return {'CANCELLED'}

        export_lock = True

        self._op_lock = Lock()
        self._operator_state = 'INITIALIZING'
        self._export_data = {
            "objects_for_export": [], "bake_info": {}, "temp_files_to_clean": set(),
            "original_material_assignments": {}, "temp_materials_for_cleanup": [],
            "normals_were_flipped": False, "was_mirrored_on_export": False, 
            "temp_realized_object_names": []
        }
        self._results_queue = Queue()
        self._log_queue = Queue()
        self._comm_threads = []
        self._finished_tasks = 0
        self._failed_tasks = 0
        self._high_usage_counter = 0
        self._running_average_peak_ram = 5.0

        try:
            if not is_blend_file_saved():
                raise RuntimeError("Please save the .blend file before exporting.")

            initial_selection = {
                o for o in (context.selected_objects if addon_prefs.remix_use_selection_only else context.scene.objects)
                if o.type in {'MESH', 'CURVE'} and o.visible_get() and not o.hide_render
            }
            if not initial_selection: raise RuntimeError("No suitable visible objects found to export.")

            is_valid, error_msg = self._preflight_validation(initial_selection)
            if not is_valid:
                bpy.ops.object.show_popup('INVOKE_DEFAULT', message=error_msg, success=False)
                return self._cleanup(context, {'CANCELLED'})

            final_export_list = set(initial_selection)
            generators_found = {obj for obj in initial_selection if self._is_geonodes_generator(obj)}
            if generators_found:
                source_objects_to_exclude = set()
                logging.info(f"Found {len(generators_found)} Geometry Node generator(s) that require realization.")
                for gen_obj in generators_found:
                    ivy_modifier = next((m for m in gen_obj.modifiers if m.type == 'NODES' and 'Baga_Ivy_Generator' in m.name), None)
                    if ivy_modifier:
                        leaf_coll_input = ivy_modifier.get("Input_24")
                        flower_coll_input = ivy_modifier.get("Input_21")
                        if leaf_coll_input and isinstance(leaf_coll_input, bpy.types.Collection):
                            source_objects_to_exclude.update(leaf_coll_input.objects)
                        if flower_coll_input and isinstance(flower_coll_input, bpy.types.Collection):
                            source_objects_to_exclude.update(flower_coll_input.objects)
                    realized_objects = self._realize_geonodes_object_non_destructively(context, gen_obj)
                    final_export_list.update(realized_objects)
                final_export_list -= generators_found
                final_export_list -= source_objects_to_exclude

            self._export_data["objects_for_export"] = [o for o in final_export_list if o and o.type == 'MESH']
            if not self._export_data["objects_for_export"]: raise RuntimeError("Processing resulted in no valid mesh objects to export.")
        
            logging.info(f"Final object list for processing: {[o.name for o in self._export_data['objects_for_export']]}")
        
            texture_map = self._prepare_and_validate_textures(context, self._export_data["objects_for_export"])
            if texture_map is None:
                return self._cleanup(context, {'CANCELLED'})
        
            success, _ = convert_exr_textures_to_png(context, self._export_data["objects_for_export"])
            if not success: raise RuntimeError("Failed to convert EXR textures to PNG.")

            all_tasks, _, _, _ = self.collect_bake_tasks(context, self._export_data["objects_for_export"], self._export_data)

            self._total_tasks = len(all_tasks)

            # --- THIS IS THE FIX ---
            # Pre-assign task numbers and total tasks to each task dictionary.
            # This makes the task number persistent, even if requeued.
            for i, task in enumerate(all_tasks):
                task['global_task_number'] = i + 1
                task['total_tasks'] = self._total_tasks
            # --- END OF FIX ---

            if not all_tasks:
                logging.info("No bake tasks required. Finalizing export directly.")
                self._finalize_export(context)
                return self._cleanup(context, {'FINISHED'})
        
            logging.info(f"Found {self._total_tasks} bake tasks. Initializing dynamic worker pool.")
            self._master_task_queue = collections.deque(all_tasks)
        
            num_potential_slots = min(self._total_tasks, self.MAX_POTENTIAL_WORKERS)
            self._worker_slots = [{
                'status': 'idle', 'process': None, 'current_task': None, 
                'launch_time': 0, 'ready_time': 0,
                'peak_cpu_since_ready': 0, 
                'peak_ram_on_task': 0,
                'tasks_completed': 0
            } for _ in range(num_potential_slots)]
        
            self._operator_state = 'RAMPING_UP'
            self._timer = context.window_manager.event_timer_add(0.1, window=context.window)
            context.window_manager.modal_handler_add(self)
            return {'RUNNING_MODAL'}

        except Exception as e:
            logging.error(f"Export failed during setup: {e}", exc_info=True)
            self.report({'ERROR'}, f"Export setup failed: {e}")
            return self._cleanup(context, {'CANCELLED'})
            
    def _handle_failed_worker(self, slot_index, requeue_task=True):
        """
        Manages a worker that has stopped, either by crashing or by being
        gracefully terminated. Can requeue the task it was working on.
        """
        if slot_index >= len(self._worker_slots): return
    
        slot = self._worker_slots[slot_index]
    
        # If requested, put the task it was working on back at the front of the queue.
        if requeue_task and 'current_task' in slot and slot['current_task']:
            task = slot['current_task']
            self._master_task_queue.appendleft(task)
            logging.warning(f"Requeueing task for material '{task.get('material_name')}' from failed worker {slot_index}.")
    
        slot['current_task'] = None
        slot['flagged_for_termination'] = False # Reset flag
        self._terminate_worker(slot_index) # This will terminate the process and set status to 'suspended'

    def _combine_color_and_alpha(self, color_map_path, alpha_mask_path):
        """
        Loads an RGB color map and a grayscale alpha mask, combines them into a
        single RGBA image, and overwrites the original color map path.
        """
        if not PILLOW_INSTALLED:
            logging.error("Pillow library is not installed. Cannot combine baked textures.")
            self.report({'ERROR'}, "Pillow dependency not found. Cannot create transparency.")
            return

        if not os.path.exists(color_map_path) or not os.path.exists(alpha_mask_path):
            logging.warning(f"Skipping texture combination: one or both maps missing. Color: '{os.path.exists(color_map_path)}', Alpha: '{os.path.exists(alpha_mask_path)}'")
            return

        logging.info(f"  > Combining '{os.path.basename(color_map_path)}' with alpha from '{os.path.basename(alpha_mask_path)}'")

        try:
            from PIL import Image

            # Load the base color map and ensure it's RGBA
            color_img = Image.open(color_map_path).convert("RGBA")
            # Load the alpha mask and ensure it's single-channel grayscale
            alpha_img = Image.open(alpha_mask_path).convert("L")

            if color_img.size != alpha_img.size:
                logging.warning(f"    - Color and alpha maps have different sizes. Resizing alpha mask to {color_img.size}.")
                alpha_img = alpha_img.resize(color_img.size, Image.Resampling.LANCZOS)

            # Put the grayscale mask into the alpha channel of the color image
            color_img.putalpha(alpha_img)

            # Save the combined RGBA image, overwriting the original color map
            color_img.save(color_map_path, "PNG")
            logging.info(f"    - Successfully created final RGBA texture at: {os.path.basename(color_map_path)}")

            # Add the temporary alpha mask file to the cleanup list
            self._export_data['temp_files_to_clean'].add(alpha_mask_path)

        except Exception as e:
            logging.error(f"Failed during texture combination for '{color_map_path}': {e}", exc_info=True)
            self.report({'WARNING'}, "Failed to combine baked textures.")

    def _combine_color_and_alpha(self, color_map_path, alpha_mask_path):
        """
        Loads an RGB color map and a grayscale alpha mask, combines them into a
        single RGBA image, and overwrites the original color map path.
        """
        if not PILLOW_INSTALLED:
            logging.error("Pillow library is not installed. Cannot combine baked textures.")
            self.report({'ERROR'}, "Pillow dependency not found. Cannot create transparency.")
            return

        if not os.path.exists(color_map_path) or not os.path.exists(alpha_mask_path):
            logging.warning(f"Skipping texture combination: one or both maps missing. Color: '{os.path.exists(color_map_path)}', Alpha: '{os.path.exists(alpha_mask_path)}'")
            return

        logging.info(f"  > Combining '{os.path.basename(color_map_path)}' with alpha from '{os.path.basename(alpha_mask_path)}'")

        try:
            from PIL import Image

            # Load the base color map and ensure it's RGBA
            color_img = Image.open(color_map_path).convert("RGBA")
            # Load the alpha mask and ensure it's single-channel grayscale
            alpha_img = Image.open(alpha_mask_path).convert("L")

            if color_img.size != alpha_img.size:
                logging.warning(f"    - Color and alpha maps have different sizes. Resizing alpha mask to {color_img.size}.")
                alpha_img = alpha_img.resize(color_img.size, Image.Resampling.LANCZOS)

            # Put the grayscale mask into the alpha channel of the color image
            color_img.putalpha(alpha_img)

            # Save the combined RGBA image, overwriting the original color map
            color_img.save(color_map_path, "PNG")
            logging.info(f"    - Successfully created final RGBA texture at: {os.path.basename(color_map_path)}")

            # Add the temporary alpha mask file to the cleanup list
            self._export_data['temp_files_to_clean'].add(alpha_mask_path)

        except Exception as e:
            logging.error(f"Failed during texture combination for '{color_map_path}': {e}", exc_info=True)
            self.report({'WARNING'}, "Failed to combine baked textures.")
          
    def _finalize_export(self, context):
        """
        [DEFINITIVE V15 - CORRECT ALPHA COMPOSITING]
        Handles the final steps of the export. This version fixes the critical bug where baked
        alpha maps were not being found and combined with their corresponding base color maps.
        The logic now uses the bake task list for a direct, reliable lookup instead of guessing filenames.
        """
        addon_prefs = context.preferences.addons[__name__].preferences
        self._export_data['original_active_uvs'] = {}

        try:
            logging.info("--- Finalizing Export (Composite & Atlas Aware) ---")
            bake_info = self._export_data.get('bake_info', {})

            # --- PHASE 1: TEXTURE COMPOSITING & CACHING ---
            if bake_info and bake_info.get('tasks'):
                logging.info("Checking for baked alpha maps to combine...")
                tasks = bake_info.get('tasks', [])
                
                # --- THIS IS THE FIX ---
                # Create a reliable lookup map from the tasks list: {material_hash: {socket_name: path}}
                tasks_by_hash = defaultdict(dict)
                for task in tasks:
                    mat_hash = task.get('material_hash')
                    socket_name = task.get('target_socket_name')
                    if mat_hash and socket_name:
                        tasks_by_hash[mat_hash][socket_name] = task.get('output_path')

                # Now, iterate through the hashes to find pairs of Base Color and Alpha maps.
                for mat_hash, baked_maps in tasks_by_hash.items():
                    if "Base Color" in baked_maps and "Alpha" in baked_maps:
                        color_map_path = baked_maps["Base Color"]
                        alpha_mask_path = baked_maps["Alpha"]
                        
                        # Verify both files exist before attempting to combine them.
                        if os.path.exists(color_map_path) and os.path.exists(alpha_mask_path):
                            log_msg = (
                                f"Found corresponding Base Color and Alpha bakes for hash {mat_hash[:8]}... "
                                f"Combining '{os.path.basename(alpha_mask_path)}' into '{os.path.basename(color_map_path)}'."
                            )
                            logging.info(log_msg)
                            self._combine_color_and_alpha(color_map_path, alpha_mask_path)
                # --- END OF FIX ---
        
                logging.info("Updating global material cache with newly baked textures...")
                for task in bake_info.get('tasks', []):
                    mat_hash = task.get('material_hash')
                    socket_name = task.get('target_socket_name')
                    output_path = task.get('output_path')

                    if mat_hash and socket_name and os.path.exists(output_path):
                        if mat_hash not in global_material_hash_cache:
                            global_material_hash_cache[mat_hash] = {}
                        global_material_hash_cache[mat_hash][socket_name] = output_path
                logging.info(f"Global cache now contains {len(global_material_hash_cache)} unique materials.")

            # --- PHASE 2: MATERIAL PREPARATION ---
            self._prepare_materials_for_export(context, objects_to_process=self._export_data["objects_for_export"])

            # --- PHASE 3: GEOMETRY PREPARATION ---
            final_meshes_for_obj = self._export_data.get("objects_for_export", [])
            if not final_meshes_for_obj:
                raise RuntimeError("Final object list for export is empty after processing.")

            if addon_prefs.mirror_on_export:
                logging.info("Applying 'Mirror on Export' to final export meshes.")
                batch_mirror_objects_optimized(final_meshes_for_obj, context)
                self._export_data["was_mirrored_on_export"] = True

            if addon_prefs.flip_faces_export:
                logging.info("Applying 'Flip Normals' to final export meshes.")
                batch_flip_normals_optimized(final_meshes_for_obj, context)
                self._export_data["normals_were_flipped"] = True

            # --- PHASE 4: FILE EXPORT ---
            base_name, asset_number = get_asset_number(context)
            obj_filename = f"{base_name}_{asset_number}.obj"

            base_finalize_path = CUSTOM_FINALIZE_PATH
            os.makedirs(base_finalize_path, exist_ok=True)
            temp_dir_name = f"{TEMP_DIR_PREFIX}{base_name}_{asset_number}_{uuid.uuid4().hex[:8]}"
            temp_asset_dir = os.path.join(base_finalize_path, temp_dir_name)
            os.makedirs(temp_asset_dir, exist_ok=True)

            try:
                with open(os.path.join(temp_asset_dir, 'blender.lock'), 'w') as f:
                    f.write(str(os.getpid()))
            except Exception as e:
                raise RuntimeError(f"Could not create .lock file, aborting export: {e}")

            self._export_data["temp_files_to_clean"].add(temp_asset_dir)
            exported_obj_path = os.path.join(temp_asset_dir, obj_filename)

            logging.info("Preparing selection and UV maps for OBJ exporter...")
            bpy.ops.object.select_all(action='DESELECT')
            selectable_meshes = [obj for obj in final_meshes_for_obj if obj and obj.name in context.view_layer.objects]
            if not selectable_meshes:
                raise RuntimeError("None of the final meshes are selectable in the current view layer.")
            for obj in selectable_meshes:
                obj.select_set(True)
            context.view_layer.objects.active = selectable_meshes[0]

            for obj in final_meshes_for_obj:
                uses_stitched_material = any(
                    slot.material and slot.material.name.endswith("__UDIM_STITCHED") 
                    for slot in obj.material_slots
                )
                if uses_stitched_material and obj.data and "remix_atlas_uv" in obj.data.uv_layers:
                    if obj.data.uv_layers.active:
                        self._export_data['original_active_uvs'][obj.name] = obj.data.uv_layers.active.name
                
                    obj.data.uv_layers.active = obj.data.uv_layers["remix_atlas_uv"]
                    logging.info(f"  > Set active UV map to 'remix_atlas_uv' for '{obj.name}' for export.")

            logging.info(f" > Exporting {len(context.selected_objects)} objects to OBJ...")
            bpy.ops.wm.obj_export(
                filepath=exported_obj_path, check_existing=True, export_selected_objects=True,
                forward_axis=addon_prefs.obj_export_forward_axis, up_axis=addon_prefs.obj_export_up_axis,
                global_scale=addon_prefs.remix_export_scale, apply_modifiers=addon_prefs.apply_modifiers,
                export_materials=True, path_mode='COPY', export_pbr_extensions=True
            )

            logging.info(f"Exported to temporary OBJ: {exported_obj_path}")

            # --- PHASE 5: API UPLOAD AND SERVER COMMUNICATION ---
            ingested_usd = upload_to_api(exported_obj_path, addon_prefs.remix_ingest_directory, context)
            if not ingested_usd:
                raise RuntimeError("API upload failed.")

            final_reference_prim = self._replace_or_append_on_server(context, ingested_usd)
            if not final_reference_prim:
                raise RuntimeError("Server replace/append operation failed.")

            if bake_info.get('special_texture_info'):
                handle_special_texture_assignments(self, context, final_reference_prim, export_data=self._export_data)

        except Exception as e:
            logging.error(f"Export finalization failed: {e}", exc_info=True)
            self.report({'ERROR'}, f"Finalization failed: {e}")
            raise RuntimeError(f"Finalization process failed.") from e
            
    def _find_ultimate_source_node(self, start_socket):
        """
        [IMPROVED & RENAMED] Traces back from a socket to find the ultimate source node.
        This is a more robust version that correctly handles node groups, reroutes,
        and common passthrough nodes like Normal Map or Displacement.
        Returns the source TEX_IMAGE node, or None if the chain is procedural.
        """
        if not start_socket.is_linked:
            return None

        q = collections.deque([(start_socket.links[0].from_node, start_socket.links[0].from_socket)])
        visited_groups = set()

        while q:
            node, socket = q.popleft()

            # Base case: Found the image source.
            if node.type == 'TEX_IMAGE':
                return node

            # --- Traversal Logic ---
            # Reroute: Follow the input link.
            if node.type == 'REROUTE':
                if node.inputs[0].is_linked:
                    q.append((node.inputs[0].links[0].from_node, node.inputs[0].links[0].from_socket))
            # Node Group: Dive inside the group.
            elif node.type == 'GROUP' and node.node_tree and node.node_tree.name not in visited_groups:
                visited_groups.add(node.node_tree.name)
                # Find the internal output socket that corresponds to the external one we came from.
                internal_out = next((s for n in node.node_tree.nodes if n.type == 'GROUP_OUTPUT' for s in n.inputs if s.identifier == socket.identifier), None)
                if internal_out and internal_out.is_linked:
                    q.append((internal_out.links[0].from_node, internal_out.links[0].from_socket))
            # Passthrough Nodes: Follow the relevant input (e.g., the 'Color' input of a Normal Map).
            elif node.type in ('NORMAL_MAP', 'DISPLACEMENT', 'BUMP', 'VECTOR_BUMP'):
                input_name = 'Color' if node.type == 'NORMAL_MAP' else 'Height'
                if input_name in node.inputs and node.inputs[input_name].is_linked:
                    q.append((node.inputs[input_name].links[0].from_node, node.inputs[input_name].links[0].from_socket))

        # If the loop finishes, the source was not a TEX_IMAGE node (it was procedural).
        return None
          
    def _bake_udim_material_to_atlas(self, context, mat, objects_using_mat, bake_dir):
        """
        [DEFINITIVE V4 - SIMPLIFIED & COMPLETE]
        Stitches UDIM tiles into new atlas textures and creates a new material. This version
        is complete and assumes the 'remix_atlas_uv' map has already been created by the
        collector function, resolving the race condition.
        """
        if not PILLOW_INSTALLED:
            self.report({'ERROR'}, "Pillow dependency not installed, cannot stitch UDIMs.")
            return None
        if not mat or not mat.use_nodes:
            return None
        
        from PIL import Image

        logging.info(f"--- Starting UDIM Stitch for Material: '{mat.name}' ---")
    
        bake_info = self._export_data.get('bake_info', {})
    
        bsdf = next((n for n in mat.node_tree.nodes if n.type == "BSDF_PRINCIPLED"), None)
        output_node = next((n for n in mat.node_tree.nodes if n.type == "OUTPUT_MATERIAL"), None)
        if not bsdf or not output_node:
            logging.warning(f"No Principled BSDF or Material Output in '{mat.name}'. Cannot stitch.")
            return None

        udim_jobs = defaultdict(list)
        all_sockets_to_check = list(bsdf.inputs) + [output_node.inputs['Displacement']]
        for socket in all_sockets_to_check:
            if not socket.is_linked: continue
            source_node = self._find_ultimate_source_node(socket)
            if source_node and source_node.image and source_node.image.source == 'TILED':
                udim_jobs[source_node].append(socket.name)

        if not udim_jobs:
            logging.info(f"No UDIM textures found to stitch for '{mat.name}'.")
            return None

        stitched_mat_name = f"{mat.name}__UDIM_STITCHED"
        final_stitched_mat = bpy.data.materials.new(name=stitched_mat_name)
        self._export_data["material_name_map"][mat.name] = final_stitched_mat.name
        self._export_data["temp_materials_for_cleanup"].append(final_stitched_mat)
    
        final_stitched_mat.use_nodes = True
        nt = final_stitched_mat.node_tree
        for node in nt.nodes: nt.nodes.remove(node)
    
        new_bsdf = nt.nodes.new('ShaderNodeBsdfPrincipled')
        new_mat_output = nt.nodes.new('ShaderNodeOutputMaterial')
        nt.links.new(new_bsdf.outputs['BSDF'], new_mat_output.inputs['Surface'])
    
        uv_map_node = nt.nodes.new('ShaderNodeUVMap')
        uv_map_node.uv_map = "remix_atlas_uv" # This is now safe

        for udim_node, target_socket_names in udim_jobs.items():
            image = udim_node.image
            tiles = sorted([t for t in image.tiles if t.label], key=lambda t: t.number)
            if not tiles: continue

            logging.info(f"Stitching {len(tiles)} tiles for '{image.name}' used in socket(s): {target_socket_names}")
        
            tile_width, tile_height = 0, 0
            # Safely determine tile size
            for tile in tiles:
                tile_path = abspath(image.filepath_raw.replace('<UDIM>', str(tile.number)))
                if os.path.exists(tile_path):
                    try:
                        with Image.open(tile_path) as img_tile:
                            tile_width, tile_height = img_tile.size
                        break
                    except Exception as e:
                        logging.warning(f"Could not read tile image {tile_path}: {e}")
            if tile_width == 0 or tile_height == 0:
                logging.error(f"Could not determine tile size for '{image.name}'. Skipping this set.")
                continue

            atlas_width = tile_width * len(tiles)
            atlas_height = tile_height
            atlas_pil_image = Image.new('RGBA', (atlas_width, atlas_height))

            for i, tile in enumerate(tiles):
                tile_path = abspath(image.filepath_raw.replace('<UDIM>', str(tile.number)))
                if not os.path.exists(tile_path): continue
            
                with Image.open(tile_path) as tile_pil_image:
                    if tile_pil_image.size != (tile_width, tile_height):
                        tile_pil_image = tile_pil_image.resize((tile_width, tile_height), Image.Resampling.LANCZOS)
                    atlas_pil_image.paste(tile_pil_image, (i * tile_width, 0))

            safe_mat_name = "".join(c for c in mat.name if c.isalnum())
            safe_img_name = "".join(c for c in image.name if c.isalnum())
            atlas_filename = f"{safe_mat_name}_{safe_img_name}_atlas.png"
            atlas_filepath = os.path.join(bake_dir, atlas_filename)
            atlas_pil_image.save(atlas_filepath)

            atlas_tex_node = nt.nodes.new('ShaderNodeTexImage')
            atlas_tex_node.image = bpy.data.images.load(atlas_filepath)
            nt.links.new(uv_map_node.outputs['UV'], atlas_tex_node.inputs['Vector'])
        
            is_data = any(n in s for s in target_socket_names for n in ['Normal', 'Roughness', 'Metallic', 'Displacement'])
            atlas_tex_node.image.colorspace_settings.name = 'Non-Color' if is_data else 'sRGB'

            for socket_name in target_socket_names:
                target_socket = new_bsdf.inputs.get(socket_name) or new_mat_output.inputs.get(socket_name)
                if not target_socket: continue
            
                if socket_name == 'Normal':
                    normal_map_node = nt.nodes.new('ShaderNodeNormalMap')
                    nt.links.new(atlas_tex_node.outputs['Color'], normal_map_node.inputs['Color'])
                    nt.links.new(normal_map_node.outputs['Normal'], target_socket)
                elif socket_name == 'Displacement':
                    disp_node = nt.nodes.new('ShaderNodeDisplacement')
                    nt.links.new(atlas_tex_node.outputs['Color'], disp_node.inputs['Height'])
                    nt.links.new(disp_node.outputs['Displacement'], new_mat_output.inputs['Displacement'])
                    bake_info['special_texture_info'][(stitched_mat_name, stitched_mat_name)].append({
                        'path': atlas_filepath, 'type': 'HEIGHT'
                    })
                else:
                    nt.links.new(atlas_tex_node.outputs['Color'], target_socket)

        logging.info(f"--- Finished UDIM Stitch for '{mat.name}', created '{final_stitched_mat.name}' ---")
        return final_stitched_mat

    def _load_tile_robustly(self, tile_path, tile_label):
        """
        [FROM ADDON 2] A dedicated, robust helper to load a single image tile from disk.
        """
        tile_image = None
        try:
            tile_image = bpy.data.images.load(tile_path, check_existing=True)
            if len(tile_image.pixels) > 0:
                return tile_image
            tile_image.reload()
            if len(tile_image.pixels) > 0:
                return tile_image
            logging.warning(f"CRITICAL: Could not load pixel data for tile '{tile_label}' from path '{tile_path}'.")
            bpy.data.images.remove(tile_image)
            return None
        except Exception as e:
            logging.error(f"An unexpected error occurred while loading tile '{tile_label}' from '{tile_path}': {e}", exc_info=True)
            if tile_image:
                bpy.data.images.remove(tile_image)
            return None

    def _transform_uvs_for_atlas(self, objects_to_process, processed_tiles):
        """
        [FROM ADDON 2] Creates a new UV map and transforms coordinates to fit the stitched atlas.
        """
        if not objects_to_process or not processed_tiles: return
        num_tiles = len(processed_tiles)
        if num_tiles == 0: return
        
        logging.info(f"Transforming UVs for {len(objects_to_process)} object(s) to fit {num_tiles}-tile atlas.")
        tile_number_to_atlas_index = {tile.number: i for i, tile in enumerate(processed_tiles)}
        
        for obj in objects_to_process:
            if not obj.data or not obj.data.uv_layers: continue
            
            source_uv_layer = obj.data.uv_layers[0]
            if not source_uv_layer: continue

            atlas_uv_map_name = "remix_atlas_uv"
            if atlas_uv_map_name in obj.data.uv_layers:
                atlas_uv_layer = obj.data.uv_layers[atlas_uv_map_name]
            else:
                atlas_uv_layer = obj.data.uv_layers.new(name=atlas_uv_map_name)

            obj.data.uv_layers.active = atlas_uv_layer

            for loop_index in range(len(source_uv_layer.data)):
                u_original, v_original = source_uv_layer.data[loop_index].uv
                tile_u_offset = math.floor(u_original)
                udim_number = 1001 + tile_u_offset
                atlas_index = tile_number_to_atlas_index.get(udim_number)
                
                if atlas_index is not None:
                    u_fractional = u_original - tile_u_offset
                    u_new = (u_fractional + atlas_index) / num_tiles
                    atlas_uv_layer.data[loop_index].uv = (u_new, v_original)
                else:
                    # If a UV coord points to a tile that doesn't exist, collapse it to zero.
                    atlas_uv_layer.data[loop_index].uv = (0.0, 0.0)

    def _prepare_materials_for_export(self, context, objects_to_process):
        """
        [DEFINITIVE V19 - CORRECT NAME MAPPING FIX]
        This version corrects the critical bug where the material name map, used by the
        special texture assignment function, was not being populated with the final, prefixed
        material name (e.g., 'EXPORT_matname'). It now stores the correct final name, ensuring
        the subsequent lookup on the server will succeed.
        """
        logging.info("Preparing unique, baked materials for export (with correct name mapping)...")

        self._export_data["material_name_map"] = {}
        self._export_data["original_material_assignments"] = {
            obj.name: [s.material for s in obj.material_slots] for obj in objects_to_process if obj
        }

        bake_cache = global_material_hash_cache

        for obj in objects_to_process:
            if not obj: continue
            for slot_index, slot in enumerate(obj.material_slots):
                original_mat = slot.material
                if not original_mat: continue

                sanitized_mat_name = re.sub(r'[\s.-]', '_', original_mat.name)
                final_mat_for_export = None

                mat_hash = get_material_hash(original_mat, obj, slot_index, ignore_mesh_context=False)

                if mat_hash in bake_cache:
                    unique_baked_mat_name = f"BAKED_{sanitized_mat_name}"
                    logging.info(f"  - CACHE HIT: Found baked textures for '{original_mat.name}' (Hash: {mat_hash[:8]}...). Building new material: '{unique_baked_mat_name}'")
                    final_mat_for_export = self._build_material_from_textures(unique_baked_mat_name, bake_cache[mat_hash])
                    # --- THIS IS THE FIX ---
                    # Store the FULL, final name including the "BAKED_" prefix.
                    self._export_data["material_name_map"][original_mat.name] = unique_baked_mat_name
                    # --- END OF FIX ---
                else:
                    logging.info(f"  - CACHE MISS: Material '{original_mat.name}' is simple and was not baked. Copying for export.")
                    unique_copy_name = f"EXPORT_{sanitized_mat_name}"
                    final_mat_for_export = original_mat.copy()
                    final_mat_for_export.name = unique_copy_name
                    self._export_data["temp_materials_for_cleanup"].append(final_mat_for_export)
                    # --- THIS IS THE FIX ---
                    # Store the FULL, final name including the "EXPORT_" prefix.
                    self._export_data["material_name_map"][original_mat.name] = unique_copy_name
                    # --- END OF FIX ---

                if final_mat_for_export:
                    obj.material_slots[slot_index].material = final_mat_for_export
                
    def _build_material_from_textures(self, name, texture_paths):
        """
        [NEW HELPER] Creates and returns a new Blender material with a simple
        Principled BSDF setup from a dictionary of texture paths.
        {'Base Color': 'path/to/albedo.png', 'Normal': 'path/to/normal.png', ...}
        """
        # Check if a material with this name already exists to reuse it
        mat = bpy.data.materials.get(name)
        if mat:
            return mat

        logging.info(f"   - Building temporary material '{name}'...")
        mat = bpy.data.materials.new(name=name)
        self._export_data["temp_materials_for_cleanup"].append(mat)
        mat.use_nodes = True
        nt = mat.node_tree
        nt.nodes.clear()

        bsdf = nt.nodes.new('ShaderNodeBsdfPrincipled')
        out = nt.nodes.new('ShaderNodeOutputMaterial')
        nt.links.new(bsdf.outputs['BSDF'], out.inputs['Surface'])

        for socket_name, path in texture_paths.items():
            if not os.path.exists(path):
                logging.warning(f"    - Texture not found, skipping: {path}")
                continue
        
            tex_node = nt.nodes.new('ShaderNodeTexImage')
            try:
                tex_node.image = bpy.data.images.load(path, check_existing=True)
            except RuntimeError:
                logging.error(f"    - Failed to load image: {path}")
                nt.nodes.remove(tex_node)
                continue
        
            # Set colorspace correctly
            is_color = socket_name in ["Base Color", "Emission Color", "Subsurface Color"]
            tex_node.image.colorspace_settings.name = 'sRGB' if is_color else 'Non-Color'

            # Link the texture to the correct socket
            if socket_name == "Base Color":
                nt.links.new(tex_node.outputs['Color'], bsdf.inputs['Base Color'])
                # If the combined texture has alpha, use it
                if 'Alpha' in tex_node.outputs:
                    nt.links.new(tex_node.outputs['Alpha'], bsdf.inputs['Alpha'])
            elif socket_name == "Normal":
                norm_map = nt.nodes.new('ShaderNodeNormalMap')
                nt.links.new(tex_node.outputs['Color'], norm_map.inputs['Color'])
                nt.links.new(norm_map.outputs['Normal'], bsdf.inputs['Normal'])
            elif socket_name != "Alpha": # Alpha is handled with Base Color
                if bsdf.inputs.get(socket_name):
                    nt.links.new(tex_node.outputs['Color'], bsdf.inputs[socket_name])
    
        return mat

    def _replace_or_append_on_server(self, context, ingested_usd):
        """
        Smarter workflow handler. Automatically detects if an asset with the same
        base name exists to perform a replace, otherwise appends a new asset.
        The "Replace Stock Mesh" checkbox now serves as an override to force
        replacement of the currently selected, unrelated mesh.
        """
        addon_prefs = context.preferences.addons[__name__].preferences

        # 1. Determine the base name of the asset being exported to search for it on the server.
        if addon_prefs.remix_use_custom_name and addon_prefs.remix_base_obj_name:
            base_name_to_search = addon_prefs.remix_base_obj_name
        else:
            blend_name = get_blend_filename()
            base_name_to_search = extract_base_name(blend_name)

        logging.info(f"Searching for existing asset on server with base name: '{base_name_to_search}'")
        prim_path_on_server, _ = check_blend_file_in_prims(base_name_to_search, context)

        # 3. DECISION: Enter REPLACE mode if an existing version is found OR if the user manually checks the box.
        if prim_path_on_server or addon_prefs.remix_replace_stock_mesh:
    
            prim_to_replace = prim_path_on_server
    
            if not prim_to_replace:
                logging.info("No match found by name, but 'Replace' is checked. Replacing current selection.")
                selected_prims = fetch_selected_mesh_prim_paths()
                if not selected_prims:
                    raise RuntimeError("The 'Replace Stock Mesh' option is ticked, but no mesh is selected in Remix.")
        
                prim_to_replace = next((p for p in selected_prims if "/meshes/" in p.lower()), None)
                if not prim_to_replace:
                        raise RuntimeError("'Replace Stock Mesh' is ticked, but the selection is not a mesh prim.")

            logging.info(f"Entering REPLACE workflow. Target prim: {prim_to_replace}")
            success, new_ref = replace_mesh_with_put_request(prim_to_replace, ingested_usd, context=context)
            if not success:
                raise RuntimeError(f"Failed to replace mesh for prim: {prim_to_replace}")
    
            select_mesh_prim_in_remix(new_ref, context)
            return new_ref

        # 4. If no existing version was found and the box is unchecked, enter APPEND mode.
        else:
            logging.info("Entering APPEND workflow (no existing asset found by name).")
        
            selected_prims = fetch_selected_mesh_prim_paths()
        
            if selected_prims:
                valid_parent_prims = [p for p in selected_prims if "/Looks/" not in p]

                if valid_parent_prims:
                    full_path = valid_parent_prims[0]
                
                    # --- START OF THE REFINED FIX ---
                    # Trim the full prim path back to the asset's root container.
                    # The expected structure is /RootNode/meshes/mesh_...
                    segments = full_path.strip('/').split('/')
                    if len(segments) >= 3 and segments[1] == 'meshes':
                        # Reconstruct the path to be the container, e.g., /RootNode/meshes/mesh_...
                        target_prim_for_append = '/' + '/'.join(segments[:3])
                        logging.info(f"Selected prim path '{full_path}' was trimmed to '{target_prim_for_append}' for append operation.")
                    else:
                        # If the path structure is unexpected, fall back to the selected prim path.
                        target_prim_for_append = full_path
                        logging.warning(f"Could not determine asset root from '{full_path}'. Using full path as parent.")
                    # --- END OF THE REFINED FIX ---

                else:
                    target_prim_for_append = "/RootNode/meshes"
                    logging.warning(f"Selection contained no valid parent prims. Appending to default location: {target_prim_for_append}")
            else:
                target_prim_for_append = "/RootNode/meshes"
                logging.info(f"No prim selected in Remix. Appending to default location: {target_prim_for_append}")
    
            success, new_ref = append_mesh_with_post_request(target_prim_for_append, ingested_usd, context)
            if not success:
                raise RuntimeError(f"Failed to append mesh under prim: {target_prim_for_append}")

            select_mesh_prim_in_remix(new_ref, context)
            return new_ref

    def _cleanup(self, context, return_value):
        """
        [DEFINITIVE V9 - Full State & Data Restoration]
        Handles all post-operation cleanup. This version is the canonical function for
        restoring the Blender scene to its original state, now including the
        DELETION of the temporary 'remix_atlas_uv' map after all other state
        (materials, normals, mirroring, active UV maps) has been restored.
        """
        global export_lock

        # --- 1. SHUTDOWN EXTERNAL PROCESSES ---
        if hasattr(self, '_worker_slots') and self._worker_slots:
            logging.info(f"Shutting down {len(self._worker_slots)} worker process(es)...")
            for slot in self._worker_slots:
                worker = slot.get('process')
                if worker and worker.poll() is None:
                    try:
                        worker.terminate()
                    except Exception as e:
                        logging.warning(f"Could not terminate worker PID {worker.pid}: {e}")
        
            for slot in self._worker_slots:
                worker = slot.get('process')
                if worker and worker.poll() is None:
                    try:
                        worker.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        worker.kill()

        if hasattr(self, '_comm_threads'):
            for thread in self._comm_threads:
                if thread.is_alive():
                    thread.join(timeout=1)
            self._comm_threads.clear()
        
        # --- 2. RESTORE BLENDER SCENE STATE ---
    
        # Restore Mirroring
        if self._export_data.get("was_mirrored_on_export"):
            objects_that_were_mirrored = self._export_data.get("objects_for_export", [])
            if objects_that_were_mirrored:
                logging.info("Restoring original orientation for mirrored objects.")
                batch_mirror_objects_optimized(objects_that_were_mirrored, context)
    
        # Restore Normals
        if self._export_data.get("normals_were_flipped"):
            objects_that_were_flipped = self._export_data.get("objects_for_export", [])
            if objects_that_were_flipped:
                logging.info("Restoring original normals for exported objects.")
                batch_flip_normals_optimized(objects_that_were_flipped, context)

        # Restore Materials
        original_assignments = self._export_data.get("original_material_assignments", {})
        if original_assignments:
            logging.debug("Restoring original material assignments.")
            for obj_name, original_mats in original_assignments.items():
                obj = bpy.data.objects.get(obj_name)
                if obj and len(obj.material_slots) == len(original_mats):
                    for i, original_mat in enumerate(original_mats):
                        obj.material_slots[i].material = original_mat

        # Restore Active UV Maps
        original_uvs = self._export_data.get("original_active_uvs", {})
        if original_uvs:
            logging.info("Restoring original active UV map assignments.")
            for obj_name, original_map_name in original_uvs.items():
                obj = bpy.data.objects.get(obj_name)
                if obj and obj.data and original_map_name in obj.data.uv_layers:
                    try:
                        # Set the active UV layer back to the one stored before export
                        obj.data.uv_layers.active = obj.data.uv_layers[original_map_name]
                    except Exception as e_uv:
                        logging.warning(f"Could not restore active UV map for '{obj_name}': {e_uv}")

        # --- 3. DELETE TEMPORARY BLENDER DATA ---
    
        # --- THIS IS THE NEW PART: Remove the temporary atlas UV map ---
        logging.info("Removing temporary atlas UV maps...")
        atlas_uv_map_name = "remix_atlas_uv"
        objects_that_were_processed = self._export_data.get("objects_for_export", [])
        for obj in objects_that_were_processed:
            if obj and obj.data and atlas_uv_map_name in obj.data.uv_layers:
                try:
                    uv_layer_to_remove = obj.data.uv_layers[atlas_uv_map_name]
                    obj.data.uv_layers.remove(uv_layer_to_remove)
                    logging.debug(f"  - Removed '{atlas_uv_map_name}' from '{obj.name}'.")
                except Exception as e_rem:
                    logging.warning(f"Could not remove temporary UV map '{atlas_uv_map_name}' from '{obj.name}': {e_rem}")
        # --- END OF NEW PART ---

        for temp_mat in self._export_data.get("temp_materials_for_cleanup", []):
            if temp_mat and temp_mat.name in bpy.data.materials:
                try: bpy.data.materials.remove(temp_mat, do_unlink=True)
                except Exception: pass
    
        for obj_name in self._export_data.get('temp_realized_object_names', []):
            obj = bpy.data.objects.get(obj_name)
            if obj:
                mesh_data = obj.data
                try:
                    bpy.data.objects.remove(obj, do_unlink=True)
                    if mesh_data and mesh_data.users == 0:
                        bpy.data.meshes.remove(mesh_data)
                except Exception: pass
            
        # --- 4. CLEANUP DISK AND UI ---
        for path_to_clean in self._export_data.get("temp_files_to_clean", set()):
            if os.path.normpath(path_to_clean) == os.path.normpath(CUSTOM_COLLECT_PATH):
                logging.info(f"Preserving bake directory '{path_to_clean}' for session caching.")
                continue
        
            if not os.path.exists(path_to_clean):
                continue
            try:
                if os.path.isdir(path_to_clean):
                    shutil.rmtree(path_to_clean)
                else:
                    os.remove(path_to_clean)
            except Exception as e:
                logging.warning(f"Could not remove temporary path '{path_to_clean}': {e}")
    
        self._export_data.get("temp_files_to_clean", set()).clear()

        if self._timer:
            context.window_manager.event_timer_remove(self._timer)
        self._timer = None
        context.workspace.status_text_set(None)
    
        # --- 5. FINAL SAVE & LOCK RELEASE ---
        if return_value == {'FINISHED'}:
            try:
                logging.info("Performing final save to clean the .blend file of temporary data.")
                bpy.ops.wm.save_mainfile()
            except Exception as e:
                logging.error(f"Final save failed: {e}")
                self.report({'WARNING'}, "Final save failed. Your file may contain temporary data.")
            
        export_lock = False
        logging.debug("Export lock released. Cleanup complete.")

        return return_value

    def cancel(self, context):
        # The main cleanup function now handles worker shutdown
        if self._export_data.get("normals_were_flipped"):
            logging.info("Operation cancelled, flipping normals back to original state.")
            batch_flip_normals_optimized(self._export_data["mesh_objects_to_export"], context)
        
        self._restore_original_materials()
        
        return self._cleanup(context, {'CANCELLED'})
       
def copy_exported_files(obj_path, mtl_path, destination):
    try:
        os.makedirs(destination, exist_ok=True)
        shutil.copy2(obj_path, destination)
        if os.path.exists(mtl_path):
            shutil.copy2(mtl_path, destination)
        else:
            logging.warning(f"MTL file does not exist: {mtl_path}")
            return False
        logging.info(f"Copied exported files to {destination}")
        return True
    except Exception as e:
        logging.error(f"Failed to copy exported files: {e}")
        return False

# At module scope, add this global variable:
ingest_error_message = ""

def upload_to_api(obj_path, ingest_dir, context):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        url = addon_prefs.remix_export_url.rstrip('/') + "/model"
        abs_obj_path = os.path.abspath(obj_path).replace('\\', '/')
        meshes_subdir = os.path.join(ingest_dir, "meshes").replace('\\', '/')

        # This is the correct, full payload structure the server expects.
        # The dynamic values for input/output paths will be inserted into it.
        payload = {
            "executor": 1,
            "name": "Model(s)",
            "context_plugin": {
                "name": "AssetImporter",
                "data": {
                    "allow_empty_input_files_list": True, "bake_material": False, "baking_scales": False,
                    "channel": "Default", "close_stage_on_exit": True, "context_name": "ingestcraft",
                    "convert_fbx_to_y_up": False, "convert_fbx_to_z_up": False, "convert_stage_up_y": False,
                    "convert_stage_up_z": False, "cook_mass_template": True, "create_context_if_not_exist": True,
                    "create_output_directory_if_missing": True, "create_world_as_default_root_prim": True,
                    "data_flows": [
                        {"channel": "write_metadata", "name": "InOutData", "push_input_data": True, "push_output_data": True},
                        {"channel": "ingestion_output", "name": "InOutData", "push_input_data": False, "push_output_data": True}
                    ],
                    "default_output_endpoint": "/stagecraft/assets/default-directory", "disabling_instancing": False,
                    "embed_mdl_in_usd": True, "embed_textures": True, "export_hidden_props": False,
                    "export_mdl_gltf_extension": False, "export_preview_surface": False, "export_separate_gltf": False,
                    "expose_mass_queue_action_ui": True, "expose_mass_ui": True, "full_path_keep": False,
                    "global_progress_value": 0, "hide_context_ui": True, "ignore_animations": False,
                    "ignore_camera": False, "ignore_flip_rotations": False, "ignore_light": False,
                    "ignore_materials": False, "ignore_pivots": False, "ignore_unbound_bones": False,
                    "input_files": [], "keep_all_materials": False, "merge_all_meshes": False,
                    "output_directory": "", "output_usd_extension": "usd", "progress": [0, "Initializing", True],
                    "single_mesh": False, "smooth_normals": True, "support_point_instancer": False,
                    "use_double_precision_to_usd_transform_op": False, "use_meter_as_world_unit": False
                }
            },
            "check_plugins": [
                {"name": "ClearUnassignedMaterial", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "include_geom_subset": True, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllMeshes"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "DefaultMaterial", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "include_geom_subset": False, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllMeshes"}], "data": {"channel": "Default", "context_name": "", "cook_mass_template": False, "default_material_mdl_name": "OmniPBR", "default_material_mdl_url": "OmniPBR.mdl", "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "MaterialShaders", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllMaterials"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "ignore_not_convertable_shaders": False, "progress": [0, "Initializing", True], "save_on_fix_failure": True, "shader_subidentifiers": {"AperturePBR_Opacity": ".*", "AperturePBR_Translucent": "translucent|glass|trans"}}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "ValueMapping", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllShaders"}], "data": {"attributes": {"inputs:emissive_intensity": [{"input_value": 10000, "operator": "=", "output_value": 1}]}, "channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True}, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "ConvertToOctahedral", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllShaders"}], "data": {"channel": "Default", "conversion_args": {"inputs:normalmap_texture": {"encoding_attr": "inputs:encoding", "replace_suffix": "_Normal", "suffix": "_OTH_Normal"}}, "cook_mass_template": False, "data_flows": [{"channel": "cleanup_files", "name": "InOutData", "push_input_data": True, "push_output_data": True}], "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "replace_udim_textures_by_empty": True, "save_on_fix_failure": True}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "ConvertToDDS", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllShaders"}], "data": {"channel": "Default", "conversion_args": {"inputs:diffuse_texture": {"args": ["--format", "bc7", "--mip-gamma-correct"]}, "inputs:emissive_mask_texture": {"args": ["--format", "bc7", "--mip-gamma-correct"]}, "inputs:height_texture": {"args": ["--format", "bc4", "--no-mip-gamma-correct", "--mip-filter", "max"]}, "inputs:metallic_texture": {"args": ["--format", "bc4", "--no-mip-gamma-correct"]}, "inputs:normalmap_texture": {"args": ["--format", "bc5", "--no-mip-gamma-correct"]}, "inputs:reflectionroughness_texture": {"args": ["--format", "bc4", "--no-mip-gamma-correct"]}, "inputs:transmittance_texture": {"args": ["--format", "bc7", "--mip-gamma-correct"]}}, "cook_mass_template": False, "data_flows": [{"channel": "cleanup_files", "name": "InOutData", "push_input_data": True, "push_output_data": True}, {"channel": "write_metadata", "name": "InOutData", "push_input_data": False, "push_output_data": True}], "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "replace_udim_textures_by_empty": True, "save_on_fix_failure": True, "suffix": ".rtex.dds"}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "RelativeAssetPaths", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllPrims"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "RelativeReferences", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "AllPrims"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_dependency_between_round": True, "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_all_layers_on_exit": True}, "name": "DependencyIterator"}},
                {"name": "WrapRootPrims", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "Nothing"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True, "set_default_prim": True, "wrap_prim_name": "XForms"}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_on_exit": True}, "name": "CurrentStage"}},
                {"name": "ApplyUnitScale", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False, "select_session_layer_prims": False}, "name": "RootPrims"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": True, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True, "scale_target": 1}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_on_exit": True}, "name": "CurrentStage"}},
                {"name": "WrapRootPrims", "selector_plugins": [{"data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "select_from_root_layer_only": False}, "name": "Nothing"}], "data": {"channel": "Default", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True], "save_on_fix_failure": True, "set_default_prim": True, "wrap_prim_name": "ReferenceTarget"}, "stop_if_fix_failed": True, "context_plugin": {"data": {"channel": "Default", "close_stage_on_exit": False, "cook_mass_template": False, "create_context_if_not_exist": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "hide_context_ui": False, "progress": [0, "Initializing", True], "save_on_exit": True}, "name": "CurrentStage"}}
            ],
            "resultor_plugins": [
                {"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_input": True, "cleanup_output": False, "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True]}},
                {"name": "FileMetadataWritter", "data": {"channel": "write_metadata", "cook_mass_template": False, "expose_mass_queue_action_ui": False, "expose_mass_ui": False, "global_progress_value": 0, "progress": [0, "Initializing", True]}}
            ]
        }

        # --- Inject dynamic values into the correct payload ---
        payload["context_plugin"]["data"]["input_files"] = [abs_obj_path]
        payload["context_plugin"]["data"]["output_directory"] = meshes_subdir

        logging.info(f"Uploading OBJ to {url}")
        # Using the previously corrected make_request_with_retries to get detailed errors
        response = make_request_with_retries('POST', url, json_payload=payload, verify=addon_prefs.remix_verify_ssl, retries=1)

        if response is None or response.status_code not in [200, 201, 204]:
            error_detail = "No response from server (network error)."
            status_code = "N/A"
            if response is not None:
                status_code = response.status_code
                try:
                    error_detail = response.json().get("detail", response.text)
                except json.JSONDecodeError:
                    error_detail = response.text
            
            logging.error(f"Failed to upload OBJ. Status: {status_code}, Response: {error_detail}")
            if status_code == 500 and "validation did not complete successfully" in error_detail:
                error_msg = "Ingestion failed: The server validation failed. Check server logs and ensure Ingest Directory is a valid project path."
                bpy.ops.object.show_popup('INVOKE_DEFAULT', message=error_msg, success=False)
            return None

        # Success path
        response_data = response.json()
        completed_schemas = response_data.get("completed_schemas", [])
        if not completed_schemas:
            logging.error("No completed schemas found in successful response.")
            return None

        # Extract the final USD path from the complex response
        # This logic is based on the structure of the provided payload
        final_usd_path = None
        try:
            data_flows = completed_schemas[0].get("context_plugin", {}).get("data", {}).get("data_flows", [])
            for flow in data_flows:
                if flow.get("channel") == "ingestion_output" and flow.get("output_data"):
                    final_usd_path = flow["output_data"][0].replace('\\', '/')
                    break
            if final_usd_path:
                 logging.info(f"Successfully ingested. Server returned USD Path: {final_usd_path}")
                 return final_usd_path
            else:
                logging.error("Could not find final USD path in server response's 'ingestion_output' data flow.")
                return None
        except (IndexError, KeyError) as e_parse:
            logging.error(f"Error parsing successful response for USD path: {e_parse}", exc_info=True)
            return None

    except Exception as e_general:
        logging.error(f"An unexpected error occurred in upload_to_api: {e_general}", exc_info=True)
        return None

    
def check_blend_file_in_prims(blend_name, context):
    """
    [DEFINITIVE V3 - PRECISE PATTERN MATCHING] Finds a prim on the server that
    matches the asset's base name followed by a version number. It no longer strips
    parts of names and instead uses a precise regex pattern to prevent incorrectly
    matching assets like 'Test_55' with 'Test6_16'.
    """
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        server_url = addon_prefs.remix_server_url.rstrip('/')
        get_url = f"{server_url}/assets/?selection=false&filter_session_assets=false&exists=true"
        headers = {'accept': 'application/lightspeed.remix.service+json; version=1.0'}

        logging.info(f"Fetching prims from: {get_url}")
        response = make_request_with_retries('GET', get_url, headers=headers, verify=addon_prefs.remix_verify_ssl)

        if not response or response.status_code != 200:
            logging.error(f"Failed to fetch prims. Status: {response.status_code if response else 'No Response'}")
            return None, None

        data = response.json()
        asset_or_prim_paths = data.get("prim_paths", data.get("asset_paths", []))
        
        # This is the CONCEPTUAL base name (e.g., "Test", or "Test6").
        if addon_prefs.remix_use_custom_name and addon_prefs.remix_use_selection_only and addon_prefs.remix_base_obj_name:
            base_name_to_search = addon_prefs.remix_base_obj_name
        else:
            # We use the blend_name directly as the base, without stripping anything.
            base_name_to_search = blend_name

        logging.debug(f"Searching for prims with base name pattern: '{base_name_to_search}_<version>'")
        
        # --- THIS IS THE CRITICAL FIX ---
        # We build a precise regex pattern. It means:
        # ^                  - Must start with
        # (base_name)        - Our exact base name (e.g., "Test" or "Test6")
        # _                  - Followed by an underscore
        # \d+                - Followed by one or more numbers
        # $                  - And nothing else after it.
        # re.IGNORECASE makes the match case-insensitive.
        match_pattern = re.compile(f"^{re.escape(base_name_to_search)}_\\d+$", re.IGNORECASE)

        for path in asset_or_prim_paths:
            segments = path.strip('/').split('/')
            
            # Check every part of the server path.
            for segment in segments:
                # Does the server prim name (e.g., "Test_55" or "Test6_16") match our precise pattern?
                if match_pattern.fullmatch(segment):
                    
                    logging.info(f"PRECISE MATCH FOUND: Local base '{base_name_to_search}' matches server asset '{segment}' in path '{path}'")
                    
                    # We found the correct asset. Now find its reference prim.
                    reference_prim_path = None
                    for i, ref_segment in enumerate(segments):
                        if ref_segment.lower().startswith('ref_'):
                            reference_prim_path = '/' + '/'.join(segments[:i + 1])
                            break
                    
                    if reference_prim_path:
                        logging.info(f"Reference prim identified: {reference_prim_path} for matched path {path}")
                        # Return the full path of the asset we found and its reference prim.
                        return path, reference_prim_path
                    else:
                        logging.warning(f"Found matching asset name '{segment}' but no 'ref_' prim in path '{path}'.")
                        break # Stop checking segments in this path

        logging.info(f"No asset matching the precise pattern '{base_name_to_search}_<version>' was found on the server.")
        return None, None

    except Exception as e:
        logging.error(f"Error checking prims: {e}", exc_info=True)
        return None, None

def extract_base_name(blend_name):
    match = re.match(r"^(.*?)(?:_\d+)?$", blend_name)
    if match:
        return match.group(1)
    return blend_name


def fetch_file_paths_from_reference_prim(reference_prim, context):
    addon_prefs = context.preferences.addons[__name__].preferences
    ingest_directory = addon_prefs.remix_ingest_directory
    textures_subdir = os.path.join(ingest_directory, "textures").replace('\\', '/')
    logging.debug(f"Returning textures directory: {textures_subdir}")
    print(f"Returning textures directory: {textures_subdir}")
    return textures_subdir, textures_subdir
    

def replace_mesh_with_put_request(prim_path, new_usd, existing_path='', existing_layer='', context=None):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        segments = prim_path.strip('/').split('/')
        ref_index = None
        for i, segment in enumerate(segments):
            if segment.lower().startswith('ref_'):
                ref_index = i
                break

        if ref_index is not None:
            trimmed_segments = segments[:ref_index + 1]
            trimmed_prim_path = '/' + '/'.join(trimmed_segments)
        else:
            if len(segments) >= 3:
                trimmed_prim_path = '/' + '/'.join(segments[:3])
            else:
                logging.error(f"Invalid prim path: {prim_path}")
                return False, None

        logging.debug(f"Trimmed prim path to '{trimmed_prim_path}'")
        print(f"Trimmed prim path to '{trimmed_prim_path}'")

        encoded_path = urllib.parse.quote(trimmed_prim_path, safe='')
        logging.debug(f"Encoded trimmed prim path: {encoded_path}")
        print(f"Encoded trimmed prim path: {encoded_path}")

        url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/{encoded_path}/file-paths"
        logging.debug(f"Constructed PUT URL: {url}")
        print(f"Constructed PUT URL: {url}")

        payload = {
            "asset_file_path": new_usd.replace('/', '\\'),
            "force": False
        }
        logging.debug(f"PUT Payload: {payload}")
        print(f"PUT Payload: {payload}")

        headers_put = {
            'Content-Type': 'application/lightspeed.remix.service+json; version=1.0'
        }

        logging.info(f"Replacing mesh via PUT request to: {url} with payload: {payload}")
        print(f"Replacing mesh via PUT request to: {url} with payload: {payload}")

        response_put = make_request_with_retries(
            method='PUT',
            url=url,
            headers=headers_put,
            json_payload=payload,
            verify=addon_prefs.remix_verify_ssl
        )

        if response_put and response_put.status_code in [200, 204]:
            logging.info(f"Mesh replaced successfully via PUT request for prim: {trimmed_prim_path}")
            print(f"Mesh replaced successfully via PUT request for prim: {trimmed_prim_path}")

            try:
                response_json = response_put.json()
                new_reference_paths = response_json.get("reference_paths", [])
                if new_reference_paths and len(new_reference_paths[0]) > 0:
                    new_reference_path = new_reference_paths[0][0]
                    logging.info(f"New Reference Path: {new_reference_path}")
                    print(f"New Reference Path: {new_reference_path}")
                    return True, new_reference_path
                else:
                    logging.error("No new reference paths found in the PUT response.")
                    print("No new reference paths found in the PUT response.")
                    return False, None
            except ValueError:
                logging.error("Failed to parse JSON response from PUT request.")
                print("Failed to parse JSON response from PUT request.")
                return False, None
        else:
            status = response_put.status_code if response_put else 'No Response'
            response_text = response_put.text if response_put else 'No Response'
            logging.error(f"Failed to replace mesh via PUT. Status: {status}, Response: {response_text}")
            print(f"Failed to replace mesh via PUT. Status: {status}, Response: {response_text}")
            return False, None
    finally:
        pass
    

def append_mesh_with_post_request(reference_path, ingested_usd, context):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        if reference_path is None:
            parent_prim = "/RootNode/meshes"
            logging.debug(f"No reference path provided. Using default parent prim path: {parent_prim}")
            print(f"No reference path provided. Using default parent prim path: {parent_prim}")
        else:
            parent_prim = reference_path
            logging.debug(f"Using provided reference path as parent prim: {parent_prim}")
            print(f"Using provided reference path as parent prim: {parent_prim}")

        encoded_parent_prim = urllib.parse.quote(parent_prim, safe='')
        logging.debug(f"Encoded parent prim path: {encoded_parent_prim}")
        print(f"Encoded parent prim path: {encoded_parent_prim}")

        base_url = addon_prefs.remix_server_url.rstrip('/')
        if base_url.endswith('/stagecraft'):
            append_url = f"{base_url}/assets/{encoded_parent_prim}/file-paths"
        else:
            append_url = f"{base_url}/stagecraft/assets/{encoded_parent_prim}/file-paths"
        logging.debug(f"Constructed append URL: {append_url}")
        print(f"Constructed append URL: {append_url}")

        payload = {
            "asset_file_path": ingested_usd.replace('\\', '/'),
            "force": False
        }

        headers = {
            'accept': 'application/lightspeed.remix.service+json; version=1.0',
            'Content-Type': 'application/lightspeed.remix.service+json; version=1.0'
        }

        logging.info(f"Appending mesh via POST to: {append_url} with payload: {payload}")
        print(f"Appending mesh via POST to: {append_url} with payload: {payload}")

        response = make_request_with_retries(
            method='POST',
            url=append_url,
            json_payload=payload,
            headers=headers,
            verify=addon_prefs.remix_verify_ssl
        )

        if not response or response.status_code not in [200, 201, 204]:
            status = response.status_code if response else 'No Response'
            response_text = response.text if response else 'No Response'
            logging.error(f"Failed to append mesh via POST. Status: {status}, Response: {response_text}")
            print(f"Failed to append mesh via POST. Status: {status}, Response: {response_text}")
            return False, None

        response_data = response.json()
        reference_paths = response_data.get("reference_paths", [])
        if not reference_paths or not reference_paths[0]:
            logging.error("No reference paths returned in response.")
            print("No reference paths returned in response.")
            return False, None

        reference_path_returned = reference_paths[0][0]
        logging.info(f"Mesh appended successfully via POST request. Reference path: {reference_path_returned}")
        print(f"Mesh appended successfully via POST request. Reference path: {reference_path_returned}")
        return True, reference_path_returned

    except Exception as e:
        logging.error(f"Error appending mesh via POST request: {e}")
        print(f"Error appending mesh via POST request: {e}")
        return False, None
    

def mirror_object(obj):
    try:
        logging.debug(f"Starting mirroring process for object: {obj.name}")

        if obj and obj.type == 'MESH':
            bpy.ops.object.select_all(action='DESELECT')
            obj.select_set(True)
            bpy.context.view_layer.objects.active = obj

            bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
            logging.debug(f"Applied scale transformations for object '{obj.name}'.")

            mesh = obj.data
            bm = bmesh.new()
            bm.from_mesh(mesh)

            for vert in bm.verts:
                vert.co.x *= -1

            logging.debug(f"Mirrored vertices for object '{obj.name}' along the X-axis.")

            for face in bm.faces:
                face.normal_flip()

            logging.debug(f"Flipped normals for object '{obj.name}'.")

            bm.to_mesh(mesh)
            bm.free()

            mesh.update()
            logging.debug(f"Mesh updated for object '{obj.name}'.")

            logging.debug(f"Mirroring process completed for object: {obj.name}")
        else:
            logging.warning(f"Object '{obj.name}' is not a mesh.")
            print(f"Object '{obj.name}' is not a mesh.")
    except Exception as e:
        logging.error(f"Error mirroring object '{obj.name}': {e}")
        print(f"Error mirroring object '{obj.name}': {e}")
        
class OBJECT_OT_show_popup(Operator):
    bl_idname = "object.show_popup"
    bl_label = "Popup Message"
    bl_options = {'REGISTER'}

    message: StringProperty(default="")
    success: BoolProperty(default=True)

    def draw(self, context):
        layout = self.layout
        row = layout.row()
        if self.success:
            row.label(text=self.message, icon='INFO')
        else:
            row.label(text=self.message, icon='ERROR')

    def execute(self, context):
        return {'FINISHED'}

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self, width=400)


class OBJECT_OT_info_operator(Operator):
    bl_idname = "object.info_operator"
    bl_label = "Hover for Information"
    bl_description = (
        "Please dont overwhelm the addon by exporting 50 procedral materials at once! Your pc will thank me."
    )

    def execute(self, context):
        return {'FINISHED'}


class OBJECT_OT_toggle_info_display(Operator):
    bl_idname = "object.toggle_info_display"
    bl_label = "Toggle Information Display"
    bl_options = {'REGISTER'}

    def execute(self, context):
        addon_prefs = context.preferences.addons[__name__].preferences
        addon_prefs.remix_show_info = not addon_prefs.remix_show_info
        if addon_prefs.remix_show_info:
            self.report({'INFO'}, "Information text displayed.")
            logging.info("Information text displayed.")
        else:
            self.report({'INFO'}, "Information text hidden.")
            logging.info("Information text hidden.")
        return {'FINISHED'}


class OBJECT_OT_reset_options(Operator):
    bl_idname = "object.reset_remix_ingestor_options"
    bl_label = "Reset Options"
    bl_options = {'REGISTER'}

    def execute(self, context):
        addon_prefs = context.preferences.addons[__name__].preferences
        
        # --- Reset All Options to Default Values ---
        addon_prefs.remix_use_selection_only = False
        addon_prefs.remix_use_custom_name = False
        addon_prefs.remix_import_original_textures = False
        addon_prefs.remix_import_scale = 1.0
        addon_prefs.flip_faces_export = False
        addon_prefs.mirror_on_export = False
        addon_prefs.mirror_import = False
        addon_prefs.flip_normals_import = False
        addon_prefs.remix_replace_stock_mesh = False
        addon_prefs.remix_bake_material_only = True
        
        addon_prefs.obj_export_forward_axis = 'NEGATIVE_Z'
        addon_prefs.obj_export_up_axis = 'Y'
        addon_prefs.remix_server_url = "http://localhost:8011/stagecraft"
        addon_prefs.remix_export_url = "http://localhost:8011/ingestcraft/mass-validator/queue"
        addon_prefs.remix_export_scale = 1.0
        addon_prefs.remix_preset = 'CUSTOM'
        addon_prefs.remix_verify_ssl = True
        addon_prefs.apply_modifiers = True

        # --- THIS IS THE FIX ---
        # Reset the custom base name string to its default.
        addon_prefs.remix_base_obj_name = "exported_object"
        # --- END OF FIX ---
        
        self.report({'INFO'}, "Remix Ingestor options have been reset to their default values.")
        logging.info("Remix Ingestor options have been reset to their default values.")
        return {'FINISHED'}

class EXPORT_OT_SubstancePainterExporter(Operator):
    """Export selected mesh objects to Substance Painter"""
    bl_idname = "export.substance_painter"
    bl_label = "Export to Substance Painter"

    def execute(self, context):
        preferences = context.preferences
        export_folder = preferences.addons[__name__].preferences.export_folder
        substance_painter_path = preferences.addons[__name__].preferences.spp_exe
        objects = context.selected_objects

        # Validate export folder
        if not os.path.exists(export_folder):
            from pathlib import Path
            export_folder = Path(bpy.path.abspath('//'))

        # Validate selection
        if not objects:
            self.report({"INFO"}, "No object selected")
            return {'CANCELLED'}

        export_paths = []
        try:
            for obj in objects:
                path = self.export_object(export_folder, obj)
                if path:
                    export_paths.append(path)

            if export_paths:
                self.open_substance_painter(export_paths, substance_painter_path)
            return {'FINISHED'}
        except Exception as e:
            self.report({"ERROR"}, f"Failed to export objects: {str(e)}")
            return {'CANCELLED'}

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def check_material(self, obj):
        """Ensure each mesh has at least one material with nodes"""
        if len(obj.data.materials) == 0:
            new_mat = bpy.data.materials.new(name=f"{obj.name}_material")
            new_mat.use_nodes = True
            obj.data.materials.append(new_mat)
            self.report({"INFO"}, f"{obj.name}: material '{new_mat.name}' added")

    def export_object(self, export_folder, obj):
        """Export a single mesh object as FBX and return its path"""
        if obj.type != 'MESH':
            self.report({"WARNING"}, f"{obj.name} is not a mesh, skipped")
            return None

        self.check_material(obj)

        object_folder = os.path.join(export_folder, obj.name)
        os.makedirs(object_folder, exist_ok=True)
        texture_folder = os.path.join(object_folder, f"{obj.name}_textures")
        os.makedirs(texture_folder, exist_ok=True)

        export_path = os.path.join(object_folder, f"{obj.name}.fbx")
        bpy.ops.export_scene.fbx(
            filepath=export_path,
            global_scale=1.0,
            apply_unit_scale=True,
            use_selection=True
        )
        self.report({"INFO"}, f"Exported {obj.name} to {export_path}")
        return export_path

    def open_substance_painter(self, export_paths, spp_exe):
        try:
            # ---- project-creation options --------------------------------------
            args = [
                spp_exe,
                '--size', '2048',                                # document resolution
                '--template', 'pbr-metal-rough-alpha-blend',     # project template
                '--normal_format', 'OpenGL',                     # normal map space
                '--uvtile'                                       # enable UV-tile workflow
            ]
            # --------------------------------------------------------------------

            # keep the original --mesh pairs
            args += [mesh for path in export_paths for mesh in ["--mesh", path]]

            subprocess.Popen(args, stdout=subprocess.PIPE, text=True)
            self.report({"INFO"}, "Opening Substance Painter with: " + " ".join(args))
        except Exception as e:
            self.report({'ERROR'}, f"Could not open Substance Painter: {str(e)}")

class OBJECT_OT_flip_normals_on_selected(Operator):
    """Flips the normals for all selected mesh objects."""
    bl_idname = "object.flip_normals_on_selected"
    bl_label = "Flip Normals on Selected"
    bl_description = "Flips the face normals of all currently selected mesh objects"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        # This operator is only active if there is at least one selected mesh object
        return any(obj.type == 'MESH' for obj in context.selected_objects)

    def execute(self, context):
        # Gather only the mesh objects from the current selection
        meshes_to_flip = [obj for obj in context.selected_objects if obj.type == 'MESH']
        
        if not meshes_to_flip:
            self.report({'WARNING'}, "No mesh objects were selected.")
            return {'CANCELLED'}

        logging.info(f"User triggered 'Flip Normals on Selected' for {len(meshes_to_flip)} object(s).")
        
        # Call the existing, robust batch processing function
        batch_flip_normals_optimized(meshes_to_flip, context)
        
        self.report({'INFO'}, f"Flipped normals on {len(meshes_to_flip)} selected object(s).")
        return {'FINISHED'}

class VIEW3D_PT_remix_ingestor(Panel):
    bl_label = "Remix Asset Ingestion"
    bl_idname = "VIEW3D_PT_remix_ingestor"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'Remix Ingestor'

    def draw(self, context):
        layout = self.layout
        addon_prefs = context.preferences.addons[__name__].preferences

        # --- THIS IS THE FIX ---
        # Check for the physical sentinel file to decide if a restart is needed.
        sentinel_path = get_sentinel_path()
        
        # Condition 1: Dependencies are installed AND a restart is required.
        if PSUTIL_INSTALLED and PILLOW_INSTALLED and os.path.exists(sentinel_path):
            box = layout.box()
            box.label(text="Restart Required", icon='ERROR')
            box.label(text="Dependencies were installed successfully.")
            box.label(text="Please restart to enable the addon.")
            box.operator("remix.restart_blender", text="Save and Restart", icon='RECOVER_LAST')
            return # Stop drawing here

        # Condition 2: Dependencies are NOT installed.
        if not PSUTIL_INSTALLED or not PILLOW_INSTALLED:
            box = layout.box()
            box.label(text="Dependencies Required", icon='ERROR')

            if getattr(context.scene, 'remix_is_installing_dependency', False):
                info_box = box.box()
                info_row = info_box.row(align=True)
                info_row.label(text="Installing dependency...", icon='SORTTIME')
            else:
                if not PSUTIL_INSTALLED:
                    col = box.column(align=True)
                    col.label(text="'psutil' is needed for resource management.")
                    op = col.operator("remix.install_dependency", text="Install psutil", icon='CONSOLE')
                    op.dependency = 'psutil'

                if not PILLOW_INSTALLED:
                    col = box.column(align=True)
                    col.label(text="'Pillow' is needed for texture processing.")
                    op = col.operator("remix.install_dependency", text="Install Pillow", icon='CONSOLE')
                    op.dependency = 'Pillow'
            return # Stop drawing here
        # --- END OF FIX ---

        # --- SECTION 2: Main Addon UI ---
        # This section is now only drawn if dependencies are installed and no restart is pending.
        export_box = layout.box()
        export_box.label(text="Export & Ingest", icon='EXPORT')
        # ... (rest of your panel's UI code is unchanged)
        export_box.prop(addon_prefs, "remix_ingest_directory", text="Ingest Directory")
        export_box.prop(addon_prefs, "remix_use_selection_only", text="Export Selected Objects Only")

        if addon_prefs.remix_use_selection_only:
            export_box.prop(addon_prefs, "remix_use_custom_name", text="Use Custom Name")
            if addon_prefs.remix_use_custom_name:
                base_name_box = export_box.box()
                base_name_box.label(text="Base OBJ Name", icon='FILE_BLEND')
                base_name_box.prop(addon_prefs, "remix_base_obj_name", text="")

        export_box.prop(addon_prefs, "remix_replace_stock_mesh", text="Replace Stock Mesh")
        export_box.prop(addon_prefs, "mirror_on_export", text="Mirror on Export")
        export_box.prop(addon_prefs, "flip_faces_export", text="Flip Normals During Export")
        export_box.prop(addon_prefs, "remix_bake_material_only")
        export_box.prop(addon_prefs, "apply_modifiers")
    
        row = export_box.row(align=True)
        row.label(text="Forward Axis:")
        row.prop(addon_prefs, "obj_export_forward_axis", text="")
        row = export_box.row(align=True)
        row.label(text="Up Axis:")
        row.prop(addon_prefs, "obj_export_up_axis", text="")
    
        export_box.prop(addon_prefs, "remix_export_scale", text="Export Scale")
        export_box.operator("object.export_and_ingest", text="Export and Ingest", icon='PLAY')

        import_box = layout.box()
        import_box.label(text="USD Import", icon='IMPORT')
        # import_box.prop(addon_prefs, "mirror_import", text="Mirror on Import")
        # import_box.prop(addon_prefs, "flip_normals_import", text="Flip Normals on Import")
        import_box.prop(addon_prefs, "remix_import_scale", text="Import Scale")
        import_box.prop(addon_prefs, "remix_import_original_textures", text="Import Original Textures")
    
        import_box.operator("object.import_usd_from_remix", text="Import from Remix")
        import_box.operator("object.import_captures", text="Import USD Captures")

        utilities_box = layout.box()
        utilities_box.label(text="Utilities", icon='TOOL_SETTINGS')
        utilities_box.operator("system.check_gpu_settings", text="Check GPU Settings", icon='SYSTEM')
        utilities_box.operator("object.flip_normals_on_selected", text="Flip Normals on Selected", icon='NORMALS_FACE')

        reset_box = layout.box()
        reset_box.operator("object.reset_remix_ingestor_options", text="Reset All Options", icon='FILE_REFRESH')

        info_box = layout.box()
        info_row = info_box.row()
        info_row.operator("object.info_operator", text="Hover for Info", icon='INFO')

classes = [
    RemixIngestorPreferences,
    OBJECT_OT_export_and_ingest,
    OBJECT_OT_import_usd_from_remix,
    OBJECT_OT_import_captures,
    OBJECT_OT_reset_options,
    OBJECT_OT_show_popup,
    VIEW3D_PT_remix_ingestor,
    OBJECT_OT_info_operator,
    OBJECT_OT_toggle_info_display,
    AssetNumberItem,
    CustomSettingsBackup,
    EXPORT_OT_SubstancePainterExporter,
    SYSTEM_OT_check_gpu_settings,
    SYSTEM_OT_show_gpu_report,
    # --- The new generalized installer and restart operators ---
    REMIX_OT_install_dependency,
    REMIX_OT_restart_blender,
    OBJECT_OT_flip_normals_on_selected,
]
           
def register():
    global BAKE_WORKER_PY
    log = logging.getLogger(__name__)

    # --- THIS IS THE FIX ---
    # Call check_dependencies() first to set up the sys.path and global flags.
    check_dependencies()
    
    # After checking, see if a restart was pending.
    sentinel_path = get_sentinel_path()
    # If all dependencies are now present and the sentinel file exists, it's the first
    # successful launch post-installation. We can now remove the file.
    if PSUTIL_INSTALLED and PILLOW_INSTALLED and os.path.exists(sentinel_path):
        try:
            os.remove(sentinel_path)
            logging.info("Dependencies found, removing restart sentinel file.")
        except OSError as e:
            logging.warning(f"Could not remove sentinel file '{sentinel_path}': {e}")
    # --- END OF FIX ---
    
    cleanup_orphan_directories()

    try:
        setup_logger()
        BAKE_WORKER_PY = os.path.join(os.path.dirname(os.path.realpath(__file__)), "remix_bake_worker.py")
        if not os.path.exists(BAKE_WORKER_PY):
            log.critical(f"Bake worker script 'remix_bake_worker.py' NOT FOUND at {BAKE_WORKER_PY}")

        for cls in classes:
            bpy.utils.register_class(cls)

        bpy.types.Scene.remix_custom_settings_backup = PointerProperty(type=CustomSettingsBackup)
        bpy.types.Scene.remix_asset_number = CollectionProperty(type=AssetNumberItem)
        
        # This flag is still useful for showing the "Installing..." message.
        bpy.types.Scene.remix_is_installing_dependency = BoolProperty(default=False)

        atexit.register(_kill_all_active_workers)
        log.info("Remix Ingestor addon registration complete with orphan process handler and startup cleanup.")
    except Exception as e:
        log.error(f"Addon registration failed: {e}", exc_info=True)
        raise

def unregister():
    log = logging.getLogger(__name__)
    _kill_all_active_workers()

    try:
        if hasattr(atexit, 'unregister'):
            atexit.unregister(_kill_all_active_workers)
            log.info("atexit handler for orphan processes has been unregistered.")
    except Exception as e:
        log.warning(f"Could not explicitly unregister atexit handler: {e}")

    for cls in reversed(classes):
        try: bpy.utils.unregister_class(cls)
        except RuntimeError: pass
        
    try:
        del bpy.types.Scene.remix_asset_number
        del bpy.types.Scene.remix_custom_settings_backup
        # Remove the now-unused property.
        del bpy.types.Scene.remix_is_installing_dependency
    except (AttributeError, TypeError):
        pass
        
    log.info("Remix Ingestor addon unregistered.")

if __name__ == "__main__":
    register()
