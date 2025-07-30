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
# Define the custom paths here to be used by all functions
CUSTOM_COLLECT_PATH = os.path.join(tempfile.gettempdir(), "remix_collect")
CUSTOM_FINALIZE_PATH = os.path.join(tempfile.gettempdir(), "remix_finalize")

# Baking Worker Configuration
BAKE_WORKER_PY = None 
#MAX_CONCURRENT_BAKE_WORKERS = max(1, os.cpu_count() // 2)
MAX_CONCURRENT_BAKE_WORKERS = 4
BAKE_BATCH_SIZE_PER_WORKER = 5

def check_dependencies():
    """Checks if psutil and Pillow are installed and updates the global state."""
    global PSUTIL_INSTALLED, PILLOW_INSTALLED
    try:
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
    """Attempts to install a specified Python library using pip."""
    bl_idname = "remix.install_dependency"
    bl_label = "Install Dependency"
    bl_description = "Downloads and installs a required library. Blender may need to be restarted."
    bl_options = {'REGISTER', 'INTERNAL'}

    dependency: StringProperty(
        name="Dependency Name",
        description="The name of the library to install (e.g., 'psutil', 'Pillow')",
        default=""
    )

    def execute(self, context):
        if not self.dependency:
            self.report({'ERROR'}, "No dependency specified.")
            return {'CANCELLED'}

        try:
            py_exec = sys.executable
            # Ensure pip is available and updated
            subprocess.run([py_exec, "-m", "ensurepip"], check=True, capture_output=True)
            subprocess.run([py_exec, "-m", "pip", "install", "--upgrade", "pip"], check=True, capture_output=True)
            # Install the dependency
            result = subprocess.run(
                [py_exec, "-m", "pip", "install", self.dependency],
                capture_output=True,
                text=True,
                check=True
            )
            logging.info(f"{self.dependency} installation successful:\n" + result.stdout)
            self.report({'INFO'}, f"{self.dependency} installed successfully! Please restart Blender to apply.")
            context.scene.remix_install_complete = True # Generic flag for restart button

        except subprocess.CalledProcessError as e:
            error_message = (f"Failed to install {self.dependency}. See System Console for details. Error:\n{e.stderr}")
            logging.error(error_message)
            self.report({'ERROR'}, "Installation failed. Check System Console.")
            context.scene.remix_install_complete = False
        except FileNotFoundError:
            error_message = f"Failed to install {self.dependency}: Python executable not found."
            logging.error(error_message)
            self.report({'ERROR'}, error_message)
            context.scene.remix_install_complete = False

        check_dependencies() # Re-check after installation attempt
        return {'FINISHED'}

# Call the check immediately when the script is loaded
check_dependencies()

def cleanup_orphan_directories():
    """
    [DEFINITIVE FIX] Scans the specific custom directories for orphaned temp folders
    left over from previous crashed sessions and deletes them.
    """
    if not PSUTIL_INSTALLED:
        logging.warning("Orphan cleanup skipped: 'psutil' is not installed.")
        return

    import psutil
    # List of all base paths that the addon might create temp folders in.
    paths_to_scan = [CUSTOM_COLLECT_PATH, CUSTOM_FINALIZE_PATH]
    
    logging.info(f"Startup cleanup: Scanning custom paths for orphan directories...")

    for base_path in paths_to_scan:
        if not os.path.exists(base_path):
            continue # Skip if the base directory (e.g., 'collect') doesn't even exist.

        logging.debug(f" > Scanning: {base_path}")
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

class REMIX_OT_install_psutil(Operator):
    """Attempts to install the psutil library using pip."""
    bl_idname = "remix.install_psutil"
    bl_label = "Install Dependency (psutil)"
    bl_description = "Downloads and installs the 'psutil' library required for dynamic resource management. Blender may need to be restarted."
    bl_options = {'REGISTER', 'INTERNAL'}

    def execute(self, context):
        try:
            py_exec = sys.executable
            # Using 'subprocess.run' is simpler for one-off commands.
            # It waits for the command to complete.
            result = subprocess.run(
                [py_exec, "-m", "pip", "install", "psutil"],
                capture_output=True,
                text=True,
                check=True # This will raise a CalledProcessError if pip fails
            )
            logging.info("psutil installation successful:\n" + result.stdout)
            self.report({'INFO'}, "psutil installed successfully! Please restart Blender.")
            # Set a flag to show the restart button
            context.scene.remix_install_complete = True

        except subprocess.CalledProcessError as e:
            error_message = (
                "Failed to install psutil. See System Console for details. "
                f"Error:\n{e.stderr}"
            )
            logging.error(error_message)
            self.report({'ERROR'}, "Installation failed. Check System Console for details.")
            context.scene.remix_install_complete = False
        except FileNotFoundError:
            error_message = "Failed to install psutil: Python executable or pip not found."
            logging.error(error_message)
            self.report({'ERROR'}, error_message)
            context.scene.remix_install_complete = False

        return {'FINISHED'}


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
      
def convert_exr_textures_to_png(context): # <--- CONTEXT IS NOW PASSED IN
    """
    Finds all EXR textures used in materials, converts them to PNG in-place,
    and updates the material nodes to point to the new PNG files.
    This version is BIT-DEPTH AWARE, saving 16-bit PNGs for high-precision EXRs.
    """
    global conversion_count
    try:
        # Unpacking is good practice to ensure local file paths
        bpy.ops.file.unpack_all(method="USE_LOCAL")
        logging.info("Starting direct conversion of EXR textures to PNG (Bit-Depth Aware).")
        
        # Gather all node trees that could contain image textures
        node_trees = list(bpy.data.node_groups) + \
                     [mat.node_tree for mat in bpy.data.materials if mat.use_nodes]

        replaced_textures = []
        conversion_count = 0

        for node_tree in node_trees:
            if not node_tree: continue
            # Pass the context object to the helper function
            success, textures = process_nodes_recursively(node_tree.nodes, node_tree, context) # <--- CONTEXT IS NOW PASSED IN
            if not success:
                return False, []
            replaced_textures.extend(textures)

        logging.info(f"Directly converted {conversion_count} EXR textures to PNG.")
        return True, replaced_textures

    except Exception as e:
        logging.error(f"Error during EXR to PNG conversion: {e}", exc_info=True)
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
    [UPDATED - MORE ROBUST]
    This function handles the assignment of any "special" textures (like height,
    emissive, etc.). This version includes a more robust material matching logic
    with a final fallback check to ensure simple material names are always found,
    making the assignment process more reliable.
    """
    addon_prefs = context.preferences.addons[__name__].preferences
    
    try:
        logging.info("--- Starting Special Texture Assignment (Robust Match) ---")

        bake_info = (export_data or {}).get('bake_info', {})
        special_texture_info = bake_info.get('special_texture_info', {})

        if not special_texture_info:
            logging.info("No special textures (height, emissive, etc.) were found to process.")
            return {'FINISHED'}

        # These sleeps are likely here to wait for server processing.
        # They are kept as they appear necessary for your setup.
        logging.info("Discovering all server-side material prims...")
        time.sleep(3)
        if not select_mesh_prim_in_remix(reference_prim, context):
             logging.warning("Could not select reference prim before querying materials.")
        time.sleep(1)
        all_selected_prims = fetch_selected_mesh_prim_paths()
        server_material_prims = [p for p in all_selected_prims if '/Looks/' in p]

        if not server_material_prims:
            logging.warning("Could not discover any server-side material prims. Cannot assign special textures.")
            return {'FINISHED'}
        logging.info(f"Found {len(server_material_prims)} material prims on server.")

        for server_material_prim_path in server_material_prims:
            prim_name_on_server = server_material_prim_path.split('/')[-1]
            
            base_name_from_server = None
            if '__UDIM_STITCHED' in prim_name_on_server:
                base_name_from_server = prim_name_on_server.split('__UDIM_STITCHED')[0]
            elif prim_name_on_server.endswith('_BAKED'):
                potential_base = prim_name_on_server.removesuffix('_BAKED')
                base_name_from_server = potential_base
            else:
                base_name_from_server = prim_name_on_server

            original_blender_mat_key = None 
            original_blender_mat_name = None 
            
            if base_name_from_server:
                # Your existing complex matching logic (kept intact)
                for key in special_texture_info.keys():
                    mat_name_to_check = None
                    expected_baked_name = None

                    if isinstance(key, tuple):
                        obj_name, mat_name = key
                        mat_name_to_check = mat_name
                        safe_obj_name = "".join(c for c in obj_name if c.isalnum() or c in ('_', '-')).strip()
                        safe_mat_name = "".join(c for c in mat_name if c.isalnum() or c in ('_', '-')).strip()
                        expected_baked_name = f"{safe_obj_name}_{safe_mat_name}"
                    
                    elif isinstance(key, str):
                        mat_name_to_check = key
                        expected_baked_name = blender_mat_to_remix(mat_name_to_check)

                    if expected_baked_name and (expected_baked_name == base_name_from_server or blender_mat_to_remix(mat_name_to_check) == base_name_from_server):
                        original_blender_mat_key = key
                        original_blender_mat_name = mat_name_to_check
                        break
            
            # --- THIS IS THE CRUCIAL UPDATE ---
            # If the complex logic above failed, try a simple direct name match as a fallback.
            if not original_blender_mat_key:
                for key in special_texture_info.keys():
                     # Get the raw material name, whether the key is a string or a tuple
                     mat_name = key[1] if isinstance(key, tuple) else key
                     if mat_name == prim_name_on_server:
                         original_blender_mat_key = key
                         original_blender_mat_name = mat_name
                         logging.debug(f"  > Matched server prim '{prim_name_on_server}' via direct name fallback.")
                         break
            # --- END OF UPDATE ---
            
            if not original_blender_mat_key:
                logging.debug(f"  > Server prim '{prim_name_on_server}' did not match any local materials with special textures. Skipping.")
                continue

            texture_list_for_mat = special_texture_info.get(original_blender_mat_key, [])
            
            if not texture_list_for_mat:
                continue

            logging.info(f"Processing {len(texture_list_for_mat)} special textures for server prim: '{prim_name_on_server}' (from Blender material: '{original_blender_mat_name}')")

            for texture_data in texture_list_for_mat:
                local_texture_path = texture_data.get('path')
                server_texture_type = texture_data.get('type')

                if not local_texture_path or not os.path.exists(local_texture_path) or not server_texture_type:
                    logging.error(f"  > Matched server prim for '{original_blender_mat_name}', but its local texture data is incomplete or file not found. Skipping this texture.")
                    continue
                
                logging.info(f"  - Processing texture type '{server_texture_type}' from path: {os.path.basename(local_texture_path)}")
                
                ingest_dir_server = addon_prefs.remix_ingest_directory.rstrip('/\\')
                server_textures_output_dir = os.path.join(ingest_dir_server, "textures").replace('\\', '/')
                base_api_url = addon_prefs.remix_export_url.rstrip('/')
                stagecraft_api_url_base = addon_prefs.remix_server_url.rstrip('/')
                ingest_payload = {"executor":1,"name":"Material(s)","context_plugin":{"name":"TextureImporter","data":{"allow_empty_input_files_list":True,"channel":"Default","context_name":"ingestcraft","cook_mass_template":True,"create_context_if_not_exist":True,"create_output_directory_if_missing":True,"data_flows":[{"channel":"Default","name":"InOutData","push_input_data":True,"push_output_data":False}],"default_output_endpoint":"/stagecraft/assets/default-directory","expose_mass_queue_action_ui":False,"expose_mass_ui":True,"global_progress_value":0,"hide_context_ui":True,"input_files":[],"output_directory":"","progress":[0,"Initializing",True]}},"check_plugins":[{"name":"MaterialShaders","selector_plugins":[{"data":{"channel":"Default","cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"select_from_root_layer_only":False},"name":"AllMaterials"}],"data":{"channel":"Default","cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"ignore_not_convertable_shaders":False,"progress":[0,"Initializing",True],"save_on_fix_failure":True,"shader_subidentifiers":{"AperturePBR_Opacity":".*"}},"stop_if_fix_failed":True,"context_plugin":{"data":{"channel":"Default","close_stage_on_exit":False,"cook_mass_template":False,"create_context_if_not_exist":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"hide_context_ui":False,"progress":[0,"Initializing",True],"save_on_exit":False},"name":"CurrentStage"}},{"name":"ConvertToOctahedral","selector_plugins":[{"data":{"channel":"Default","cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"select_from_root_layer_only":False},"name":"AllShaders"}],"resultor_plugins":[{"data":{"channel":"cleanup_files_normal","cleanup_input":True,"cleanup_output":False,"cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True]},"name":"FileCleanup"}],"data":{"channel":"Default","conversion_args":{"inputs:normalmap_texture":{"encoding_attr":"inputs:encoding","replace_suffix":"_Normal","suffix":"_OTH_Normal"}},"cook_mass_template":False,"data_flows":[{"channel":"cleanup_files_normal","name":"InOutData","push_input_data":True,"push_output_data":True}],"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"replace_udim_textures_by_empty":False,"save_on_fix_failure":True},"stop_if_fix_failed":True,"context_plugin":{"data":{"channel":"Default","close_stage_on_exit":False,"cook_mass_template":False,"create_context_if_not_exist":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"hide_context_ui":False,"progress":[0,"Initializing",True],"save_on_exit":False},"name":"CurrentStage"}},{"name":"ConvertToDDS","selector_plugins":[{"data":{"channel":"Default","cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"select_from_root_layer_only":False},"name":"AllShaders"}],"resultor_plugins":[{"data":{"channel":"cleanup_files","cleanup_input":True,"cleanup_output":False,"cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True]},"name":"FileCleanup"}],"data":{"channel":"Default","conversion_args":{"inputs:diffuse_texture":{"args":["--format","bc7","--mip-gamma-correct"]},"inputs:emissive_mask_texture":{"args":["--format","bc7","--mip-gamma-correct"]},"inputs:height_texture":{"args":["--format","bc4","--no-mip-gamma-correct","--mip-filter","max"]},"inputs:metallic_texture":{"args":["--format","bc4","--no-mip-gamma-correct"]},"inputs:normalmap_texture":{"args":["--format","bc5","--no-mip-gamma-correct"]},"inputs:reflectionroughness_texture":{"args":["--format","bc4","--no-mip-gamma-correct"]},"inputs:transmittance_texture":{"args":["--format","bc7","--mip-gamma-correct"]}},"cook_mass_template":False,"data_flows":[{"channel":"cleanup_files","name":"InOutData","push_input_data":True,"push_output_data":True},{"channel":"write_metadata","name":"InOutData","push_input_data":False,"push_output_data":True},{"channel":"ingestion_output","name":"InOutData","push_input_data":False,"push_output_data":True}],"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"replace_udim_textures_by_empty":False,"save_on_fix_failure":True,"suffix":".rtex.dds"},"stop_if_fix_failed":True,"context_plugin":{"data":{"channel":"Default","close_stage_on_exit":False,"cook_mass_template":False,"create_context_if_not_exist":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"hide_context_ui":False,"progress":[0,"Initializing",True],"save_on_exit":False},"name":"CurrentStage"}},{"name":"MassTexturePreview","selector_plugins":[{"data":{"channel":"Default","cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"select_from_root_layer_only":False},"name":"Nothing"}],"data":{"channel":"Default","cook_mass_template":False,"expose_mass_queue_action_ui":True,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True],"save_on_fix_failure":True},"stop_if_fix_failed":True,"context_plugin":{"data":{"channel":"Default","close_stage_on_exit":False,"cook_mass_template":False,"create_context_if_not_exist":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"hide_context_ui":False,"progress":[0,"Initializing",True],"save_on_exit":False},"name":"CurrentStage"}}],"resultor_plugins":[{"name":"FileMetadataWritter","data":{"channel":"write_metadata","cook_mass_template":False,"expose_mass_queue_action_ui":False,"expose_mass_ui":False,"global_progress_value":0,"progress":[0,"Initializing",True]}}]}
                ingest_payload["context_plugin"]["data"]["input_files"] = [[local_texture_path, server_texture_type.upper()]]
                ingest_payload["context_plugin"]["data"]["output_directory"] = server_textures_output_dir

                ingest_response = make_request_with_retries('POST', f"{base_api_url}/material", json_payload=ingest_payload, verify=addon_prefs.remix_verify_ssl)
                if not ingest_response or ingest_response.status_code >= 400:
                    logging.error(f"  > Failed to ingest special texture. Server responded with status {ingest_response.status_code if ingest_response else 'N/A'}")
                    continue

                time.sleep(2)
                
                base_filename = os.path.splitext(os.path.basename(local_texture_path))[0]
                final_ingested_texture_path_on_server = os.path.join(server_textures_output_dir, f"{base_filename}.{server_texture_type[0].lower()}.rtex.dds").replace('\\', '/')
                
                try:
                    encoded_material_prim = urllib.parse.quote(server_material_prim_path, safe='')
                    textures_on_material_url = f"{stagecraft_api_url_base}/assets/{encoded_material_prim}/textures"
                    textures_response = make_request_with_retries('GET', textures_on_material_url, headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'}, verify=addon_prefs.remix_verify_ssl)
                    
                    textures_data = textures_response.json().get("textures", [])
                    if not textures_data or not textures_data[0]:
                        logging.error(f"  > Server returned an empty texture list for material prim: {server_material_prim_path}.")
                        continue
                    
                    shader_core_input_prim = textures_data[0][0]
                    encoded_shader_core_input = urllib.parse.quote(shader_core_input_prim, safe='')
                    input_prim_query_url = f"{stagecraft_api_url_base}/textures/{encoded_shader_core_input}/material/inputs?texture_type={server_texture_type.upper()}"
                    
                    input_prim_response = make_request_with_retries('GET', input_prim_query_url, headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'}, verify=addon_prefs.remix_verify_ssl)
                    if not input_prim_response or input_prim_response.status_code >= 400:
                        logging.error(f"  > Failed to get the '{server_texture_type}' input prim path from the server.")
                        continue
                    
                    shader_input_target_prim = input_prim_response.json().get("prim_paths", [[]])[0]
                    if not shader_input_target_prim:
                        logging.error(f"  > Server did not return a valid prim path for the '{server_texture_type}' input.")
                        continue

                    logging.info(f"  > Target prim for '{server_texture_type}' assignment: {shader_input_target_prim}")
                    update_texture_connection_url = f"{stagecraft_api_url_base}/textures/"
                    put_payload = {"force": False, "textures": [[shader_input_target_prim, final_ingested_texture_path_on_server]]}
                    
                    put_response = make_request_with_retries('PUT', update_texture_connection_url, json_payload=put_payload, headers={"accept": "application/lightspeed.remix.service+json; version=1.0", "Content-Type": "application/lightspeed.remix.service+json; version=1.0"}, verify=addon_prefs.remix_verify_ssl)
                    if not put_response or put_response.status_code >= 400:
                        logging.error(f"  > Failed to update shader with '{server_texture_type}' texture.")
                        continue

                    logging.info(f"  > Successfully assigned '{server_texture_type}' texture for material '{original_blender_mat_name}'.")

                except (IndexError, KeyError, TypeError, json.JSONDecodeError) as e:
                    logging.error(f"  > Could not parse a valid shader prim or response for '{server_material_prim_path}': {e}", exc_info=True)
                    continue

        logging.info("--- Finished Special Texture Assignment ---")
        return {'FINISHED'}

    except Exception as e:
        logging.error(f"A critical error occurred in handle_special_texture_assignments: {e}", exc_info=True)
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

def batch_flip_normals_optimized(meshes_to_flip, context):
    """
    Flips normals for a list of mesh objects in a batch using a single
    Edit Mode session, which is much faster and more reliable.
    This is the complete, non-simplified version.
    """
    if not meshes_to_flip:
        return

    logging.info(f"Batch flip normals: Preparing to flip {len(meshes_to_flip)} meshes.")

    # Store original state to restore it perfectly
    original_active = context.view_layer.objects.active
    original_selected = list(context.selected_objects)
    original_mode = 'OBJECT'
    if context.object and hasattr(context.object, 'mode'):
        original_mode = context.object.mode

    # Ensure we are in Object Mode to safely change selection and active object
    if context.mode != 'OBJECT':
        bpy.ops.object.mode_set(mode='OBJECT')

    try:
        # Deselect everything and then select only the meshes we need to flip
        bpy.ops.object.select_all(action='DESELECT')
        
        valid_meshes_to_flip = []
        for obj in meshes_to_flip:
            if obj and obj.type == 'MESH' and obj.name in context.view_layer.objects:
                obj.select_set(True)
                valid_meshes_to_flip.append(obj)
        
        if not valid_meshes_to_flip:
            logging.warning("No valid meshes were available for normal flipping.")
            return

        # Set one of the valid meshes as the active object to allow entering Edit Mode
        context.view_layer.objects.active = valid_meshes_to_flip[0]

        # Switch to Edit Mode for all selected meshes at once
        bpy.ops.object.mode_set(mode='EDIT')
        
        # THE CORE FIX: Check for 'EDIT_MESH' instead of 'EDIT'
        if context.mode == 'EDIT_MESH':
            # Perform the operations
            bpy.ops.mesh.select_all(action='SELECT')
            bpy.ops.mesh.flip_normals()
            logging.info(f"Flipped normals for {len(valid_meshes_to_flip)} meshes.")
            # Go back to Object mode
            bpy.ops.object.mode_set(mode='OBJECT')
        else:
            logging.warning(f"Could not switch to EDIT_MESH mode (current mode: {context.mode}). Normals not flipped.")
            # Ensure we still exit to Object mode if something went wrong
            if context.mode != 'OBJECT':
                bpy.ops.object.mode_set(mode='OBJECT')

    finally:
        # Restore the original selection and active object
        bpy.ops.object.select_all(action='DESELECT')
        for obj in original_selected:
            if obj and obj.name in context.view_layer.objects:
                obj.select_set(True)
        
        if original_active and original_active.name in context.view_layer.objects:
            context.view_layer.objects.active = original_active
        
        # Restore the original mode if it was something other than Object mode
        if original_mode != 'OBJECT' and context.view_layer.objects.active:
            try:
                bpy.ops.object.mode_set(mode=original_mode)
            except RuntimeError:
                # It's okay if we can't restore the mode, Object mode is a safe default.
                pass
        logging.info("Batch flip normals: Operation finished.")

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
        1) Optionally override USD importer’s axis prefs so meshes aren’t “all facing upward.”
        2) Import each USD into `temp_scene` (no per‐file redraws).
        3) Detect newly created objects via a “marker” property.
        4) Keep only unique meshes by conceptual base name.
        5) Collapse transforms, optionally attach textures, then prune any dead references.
        6) Return a final list of still‐alive keeper objects, plus counts of processed files/textures.
        """

        # 1) Override USD importer preferences ONCE at the start of this batch
        original_importer_settings = {}
        usd_importer_addon = context.preferences.addons.get('io_scene_usd')
        if usd_importer_addon:
            importer_prefs = usd_importer_addon.preferences
            # Back up the axis settings and scale
            for attr in ("axis_forward", "axis_up"):
                if hasattr(importer_prefs, attr):
                    original_importer_settings[attr] = getattr(importer_prefs, attr)

            # Pull from addon_prefs: assume “usd_import_forward_axis” and “usd_import_up_axis” exist
            forward_axis = getattr(addon_prefs, "usd_import_forward_axis", "-Z")
            up_axis = getattr(addon_prefs, "usd_import_up_axis", "Y")
            if hasattr(importer_prefs, "axis_forward"):
                importer_prefs.axis_forward = forward_axis
            if hasattr(importer_prefs, "axis_up"):
                importer_prefs.axis_up = up_axis

            logging.debug(f"USD Importer axes set to Forward={forward_axis}, Up={up_axis}.")

        # Local aliases for speed
        data_materials = bpy.data.materials
        data_objects = bpy.data.objects
        materials_seen = set(data_materials.keys())
        processed_bases = self._processed_conceptual_asset_bases

        # 2) Cache transform/texture flags once
        remix_scale = getattr(addon_prefs, "remix_import_scale", 1.0)
        scale_needed = abs(remix_scale - 1.0) > 1e-6
        mirror_flag = bool(getattr(addon_prefs, "mirror_import", False))
        flip_flag = bool(getattr(addon_prefs, "flip_normals_import", False))
        attach_textures_flag = bool(getattr(addon_prefs, "remix_import_original_textures", False))

        if scale_needed:
            scale_matrix = Matrix.Diagonal((remix_scale, remix_scale, remix_scale, 1.0))
        if mirror_flag:
            mirror_matrix = Matrix.Scale(-1.0, 4, (1.0, 0.0, 0.0))

        valid_exts = tuple(ext.strip().lower() for ext in self.filename_ext.split(','))

        all_keep_objs = []
        processed_files_count = 0
        textures_processed_for_count = 0

        # 3) Switch to temp_scene once (avoiding repeated context switches)
        original_scene_for_loop = context.window.scene
        context.window.scene = temp_scene

        for file_elem in self.files:
            filepath = os.path.join(self.directory, file_elem.name)
            if not (os.path.exists(filepath) and filepath.lower().endswith(valid_exts)):
                logging.warning(f"Skipping invalid file: {filepath}")
                continue

            processed_files_count += 1
            if getattr(bpy.app, "debug", False):
                logging.debug(f"[{processed_files_count}/{len(self.files)}] Importing: {filepath}")

            # Tag all existing objects in temp_scene with a “pre‐import marker”
            for obj in temp_scene.objects:
                obj["_pre_import_marker"] = True

            # Import WITHOUT calling view_layer.update() each time
            try:
                bpy.ops.wm.usd_import(filepath=filepath)
            except Exception as e_import:
                logging.error(f"Error importing {filepath}: {e_import}", exc_info=True)
                # Clean up markers
                for obj in temp_scene.objects:
                    obj.pop("_pre_import_marker", None)
                continue

            # 4) Collect newly created objects: those missing the marker
            newly_added_raw_objects = [
                obj for obj in temp_scene.objects
                if "_pre_import_marker" not in obj
            ]

            # Remove markers from all
            for obj in temp_scene.objects:
                obj.pop("_pre_import_marker", None)

            if not newly_added_raw_objects:
                logging.warning(f"No new objects detected in {filepath}")
                continue

            # 5) Classify “unique meshes” vs “discards” in one pass
            unique_meshes = []
            discards = []
            get_base = self._get_conceptual_asset_base_name

            for obj_raw in newly_added_raw_objects:
                if obj_raw.type != 'MESH':
                    discards.append(obj_raw)
                    continue

                base_name = get_base(obj_raw)
                if base_name not in processed_bases:
                    processed_bases.add(base_name)
                    unique_meshes.append(obj_raw)
                else:
                    discards.append(obj_raw)

            if not unique_meshes:
                # No unique meshes ⇒ discard everything
                discards = newly_added_raw_objects.copy()
            else:
                # Also keep any parents of each unique mesh (if they live in the newly‐added set)
                newly_set = set(newly_added_raw_objects)
                keepers_set = set(unique_meshes)
                for mesh in unique_meshes:
                    parent = mesh.parent
                    while parent and parent in newly_set:
                        keepers_set.add(parent)
                        parent = parent.parent

                for obj_raw in newly_added_raw_objects:
                    if obj_raw not in keepers_set and obj_raw not in discards:
                        discards.append(obj_raw)

                unique_meshes = list(keepers_set)

            # 6) Material dedupe: “one‐pass” replacement of duplicate materials
            mats_before = materials_seen.copy()
            for obj in unique_meshes:
                for slot in obj.material_slots:
                    mat = slot.material
                    if not mat:
                        continue
                    base_mat_name = mat.name.split('.')[0]
                    if base_mat_name in mats_before and base_mat_name != mat.name:
                        master_mat = data_materials.get(base_mat_name)
                        if master_mat:
                            slot.material = master_mat
                            if mat.users == 0:
                                try:
                                    data_materials.remove(mat, do_unlink=True)
                                except Exception:
                                    pass
                    else:
                        mats_before.add(mat.name)
            materials_seen = mats_before

            # 7) Apply transforms (scale, mirror, flip), collect meshes_for_texture
            meshes_for_texture = []
            for keeper_obj in unique_meshes:
                # Scale (only top‐level objects)
                if scale_needed and keeper_obj.type in {
                    'MESH', 'CURVE', 'EMPTY', 'ARMATURE', 'LIGHT', 'CAMERA'
                }:
                    if not keeper_obj.parent or keeper_obj.parent not in unique_meshes:
                        keeper_obj.matrix_world = scale_matrix @ keeper_obj.matrix_world

                # Mirror (only selected meshes)
                if mirror_flag and keeper_obj.type == 'MESH' and keeper_obj.select_get():
                    keeper_obj.matrix_world = mirror_matrix @ keeper_obj.matrix_world

                # Flip normals
                if flip_flag and keeper_obj.type == 'MESH':
                    mesh_data = keeper_obj.data
                    if hasattr(mesh_data, "flip_normals"):
                        mesh_data.flip_normals()

                # Mark for texture attachment
                if attach_textures_flag and keeper_obj.type == 'MESH':
                    meshes_for_texture.append(keeper_obj)

            # 8) Attach textures if requested (ONLY on still‐alive meshes)
            if meshes_for_texture and is_blend_file_saved():
                attach_original_textures(meshes_for_texture, context, os.path.dirname(filepath))
                textures_processed_for_count += len(meshes_for_texture)

            # 9) Delete/discard “discards” if still present
            for obj_del in discards:
                if obj_del.name in temp_scene.objects:
                    # Unlink from only those collections that reference it
                    for coll in list(obj_del.users_collection):
                        coll.objects.unlink(obj_del)
                    if obj_del.name in temp_scene.collection.objects:
                        temp_scene.collection.objects.unlink(obj_del)
                    data_blk = obj_del.data
                    data_objects.remove(obj_del, do_unlink=True)
                    if data_blk and data_blk.users == 0:
                        if isinstance(data_blk, bpy.types.Mesh):
                            bpy.data.meshes.remove(data_blk)
                        elif isinstance(data_blk, bpy.types.Curve):
                            bpy.data.curves.remove(data_blk)

            # 10) CRASH‐FIXED FILTER: prune any dead references from unique_meshes
            pruned = []
            for o in unique_meshes:
                try:
                    nm = o.name
                except ReferenceError:
                    continue
                if nm in temp_scene.objects:
                    pruned.append(o)
            unique_meshes[:] = pruned

            all_keep_objs.extend(unique_meshes)

        # end for file_elem

        # Restore original scene
        context.window.scene = original_scene_for_loop

        # 11) FINAL DEDUPLICATION (only still‐alive objects)
        keepers_by_name = {}
        all_keep_objs_valid = []
        for obj in all_keep_objs:
            if not obj:
                continue
            try:
                nm = obj.name
            except ReferenceError:
                continue
            if nm in bpy.data.objects and nm not in keepers_by_name:
                keepers_by_name[nm] = obj
                all_keep_objs_valid.append(obj)

        all_keep_objs = all_keep_objs_valid

        # 12) Restore USD importer prefs back to what they were
        if usd_importer_addon and original_importer_settings:
            importer_prefs = usd_importer_addon.preferences
            for attr, val in original_importer_settings.items():
                if hasattr(importer_prefs, attr):
                    try:
                        setattr(importer_prefs, attr, val)
                    except Exception as e_restore:
                        logging.warning(f"Could not restore USD importer setting {attr}: {e_restore}")
            logging.debug("USD importer axis settings restored.")

        return all_keep_objs, processed_files_count, textures_processed_for_count

    def execute(self, context: bpy.types.Context) -> set[str]:
        """
        1) Disable addons that might interfere.  
        2) Create (or optionally reuse) a temp scene.  
        3) Run the optimized _import_and_process_files_iteratively().  
        4) Apply a final “orientation fix” if meshes still end up upside‐down.  
        5) Transfer keepers to the main scene, remove extras, restore addons.
        """
        start_time = time.perf_counter()
        try:
            current_addon_name    = __name__.split('.')[0]
            addon_prefs_instance  = context.preferences.addons[current_addon_name].preferences
        except (KeyError, AttributeError):
            self.report({'ERROR'}, "Could not retrieve addon preferences. Import cancelled.")
            return {'CANCELLED'}

        if not self.files:
            self.report({'WARNING'}, "No files selected for import.")
            return {'CANCELLED'}

        original_main_scene = context.scene
        import_scene_temp   = None
        addons_for_stability= ['blenderkit']

        self._processed_conceptual_asset_bases = set()
        self._addons_original_state           = {}

        all_keep_in_temp = []
        imported_files_count = 0
        textures_count = 0

        try:
            # ─── 1) Disable interfering addons ─────────────────────────────────
            self._manage_addons(context, addons_for_stability, disable_mode=True)

            # ─── 2) Create a uniquely named temp scene ─────────────────────────
            temp_scene_name = "USD_Import_Temp_V3"
            idx = 0
            while temp_scene_name in bpy.data.scenes:
                idx += 1
                temp_scene_name = f"USD_Import_Temp_V3_{idx}"
            import_scene_temp = bpy.data.scenes.new(temp_scene_name)
            logging.info(f"Created temporary scene: {import_scene_temp.name}")

            # ─── 3) Import & per‐file processing ───────────────────────────────
            all_keep_in_temp, imported_files_count, textures_count = \
                self._import_and_process_files_iteratively(
                    context,
                    import_scene_temp,
                    addon_prefs_instance,
                    original_main_scene
                )

            if not all_keep_in_temp:
                self.report(
                    {'INFO'},
                    f"Processed {imported_files_count} files. No unique assets were kept."
                )
                return {'FINISHED'}

            # ─── 4) Final Transforms Phase (apply orientation fix) ──────────────
            if context.window.scene != import_scene_temp:
                context.window.scene = import_scene_temp

            # Deselect everything if something is selected
            if any(ob.select_get() for ob in import_scene_temp.objects):
                for ob in import_scene_temp.objects:
                    ob.select_set(False)

            valid_keepers = []
            active_for_transform = None
            for obj_k in all_keep_in_temp:
                if not obj_k:
                    continue
                try:
                    nm = obj_k.name
                except ReferenceError:
                    continue
                if nm in import_scene_temp.objects and nm in context.view_layer.objects:
                    obj_k.select_set(True)
                    valid_keepers.append(obj_k)
                    if active_for_transform is None:
                        active_for_transform = obj_k

            if valid_keepers and active_for_transform:
                context.view_layer.objects.active = active_for_transform

                # — Orientation Fix —  
                # If your USDs still import “lying flat/upside‐down,” change `axis='X'` and `angle` as needed.
                # For example, to rotate −90° about X so “front” faces +Y instead of +Z:
                do_orientation_fix = True  # set False if you don’t need it
                logging.info("Applying +90 degree X-axis rotation to fix orientation.")
                # This creates a rotation matrix for +90 degrees around the X axis
                rot_x_pos_90 = Matrix.Rotation(math.pi / 2, 4, 'X') 
                for ob in valid_keepers:
                    # Apply the rotation to the object's world matrix
                    ob.matrix_world = rot_x_pos_90 @ ob.matrix_world

                logging.info(f"Applying final transforms to {len(valid_keepers)} keepers.")
                _perform_transform_application_phase_module(context, import_scene_temp)
            elif all_keep_in_temp:
                logging.warning(
                    "No valid keeper objects selected for final transform or active object could not be set."
                )

            # Restore to main scene
            if context.window.scene != original_main_scene:
                context.window.scene = original_main_scene

            # ─── 5) Transfer from temp_scene to main_scene ───────────────────────
            transferred_count = 0
            if import_scene_temp.objects:
                # Build a set of names we want to keep
                keeper_names_final = set()
                for obj in all_keep_in_temp:
                    if not obj:
                        continue
                    try:
                        nm = obj.name
                    except ReferenceError:
                        continue
                    if nm in import_scene_temp.objects:
                        keeper_names_final.add(nm)

                # Delete any extras in temp_scene
                extras = [
                    ob for ob in list(import_scene_temp.objects)
                    if ob.name not in keeper_names_final
                ]
                if extras:
                    if context.window.scene != import_scene_temp:
                        context.window.scene = import_scene_temp
                    for ob_rem in extras:
                        for coll_s in list(ob_rem.users_collection):
                            coll_s.objects.unlink(ob_rem)
                        if ob_rem.name in import_scene_temp.collection.objects:
                            import_scene_temp.collection.objects.unlink(ob_rem)
                        data_blk = ob_rem.data
                        bpy.data.objects.remove(ob_rem, do_unlink=True)
                        if data_blk and data_blk.users == 0:
                            if isinstance(data_blk, bpy.types.Mesh):
                                bpy.data.meshes.remove(data_blk)
                            elif isinstance(data_blk, bpy.types.Curve):
                                bpy.data.curves.remove(data_blk)
                    if context.window.scene != original_main_scene:
                        context.window.scene = original_main_scene

                # Link keepers directly into main scene’s root collection
                target_coll = original_main_scene.collection
                for obj in import_scene_temp.objects:
                    if obj.name in keeper_names_final:
                        target_coll.objects.link(obj)
                        transferred_count += 1

            # Build report message
            report_parts = [
                f"Processed {imported_files_count} USD file(s).",
                f"Kept {len(self._processed_conceptual_asset_bases)} unique conceptual assets ({len(all_keep_in_temp)} total objects).",
                f"Transferred {transferred_count} objects to '{original_main_scene.name}'."
            ]
            if getattr(addon_prefs_instance, "remix_import_original_textures", False):
                if is_blend_file_saved():
                    report_parts.append(f"Applied textures for {textures_count} mesh objects.")
                else:
                    report_parts.append("Texture attachment skipped (blend file not saved).")

            self.report({'INFO'}, " ".join(report_parts))
            return {'FINISHED'}

        except Exception as e:
            logging.critical(f"Fatal error during import execution: {e}", exc_info=True)
            self.report({'ERROR'}, "Critical import failure. See system console.")
            return {'CANCELLED'}

        finally:
            # ─── Clean up temp scene ───────────────────────────────────────────────
            if import_scene_temp and import_scene_temp.name in bpy.data.scenes:
                logging.info(f"Removing temporary scene: {import_scene_temp.name}")
                for window in context.window_manager.windows:
                    if window.scene == import_scene_temp:
                        window.scene = original_main_scene
                if context.window.scene == import_scene_temp:
                    context.window.scene = original_main_scene
                bpy.data.scenes.remove(import_scene_temp, do_unlink=True)

            # ─── Restore previously disabled addons ─────────────────────────────────
            self._manage_addons(context, addons_for_stability, disable_mode=False)
            logging.info("Addon states restored.")
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
                        # Sometimes USD import might select objects instead of just adding them,
                        # or if it imports into an existing hierarchy, the diff might be complex.
                        # Fallback to selected if any, otherwise log a warning.
                        if context.selected_objects:
                            newly_added_objects = list(context.selected_objects)
                            logging.debug(f"  Remix import of {os.path.basename(usd_file_path)}: using selected objects as newly added.")
                        else:
                            logging.warning(f"  Remix import of {os.path.basename(usd_file_path)}: No new objects detected by diff and nothing selected. Subsequent per-object operations might be skipped for this file.")
                            imported_top_level_objects_map[usd_file_path] = []
                            continue # Skip to next file if nothing seems to have been imported from this one

                    imported_top_level_objects_map[usd_file_path] = newly_added_objects
                    logging.info(f"  Remix import: Identified {len(newly_added_objects)} new top-level objects from {os.path.basename(usd_file_path)}.")

                    # Apply your addon-specific scaling, mirroring, normal flipping
                    import_scale = addon_prefs_instance.remix_import_scale
                    if import_scale != 1.0:
                        for obj in newly_added_objects:
                            if obj.type in {'MESH', 'CURVE', 'EMPTY'}: # Apply scale to relevant types
                                obj.scale = tuple(s * import_scale for s in obj.scale) # Direct multiplication
                                logging.debug(f"  Applied import scale {import_scale} to object: {obj.name} (Remix temp).")
                    
                    if addon_prefs_instance.mirror_import:
                        for obj in newly_added_objects:
                             if obj.type == 'MESH':
                                logging.info(f"  Mirroring object: {obj.name} (Remix temp).")
                                mirror_object(obj) # Your existing function

                    if addon_prefs_instance.flip_normals_import:
                        for obj in newly_added_objects:
                            if obj.type == 'MESH':
                                flip_normals_api(obj) # Your existing function
                                logging.debug(f"  Flipped normals for imported object: {obj.name} (Remix temp).")
                
                except RuntimeError as e_imp_remix:
                    logging.error(f"  Runtime error importing (Remix) {usd_file_path} into {target_scene.name}: {e_imp_remix}", exc_info=True)
                    # self.report is not available here, main execute will report
                except Exception as ex_gen_remix:
                    logging.error(f"  Unexpected error importing (Remix) {usd_file_path}: {ex_gen_remix}", exc_info=True)

        finally: # Restore settings and original scene
            if usd_importer_addon and original_importer_settings:
                importer_prefs = usd_importer_addon.preferences
                for attr, val in original_importer_settings.items():
                    try: setattr(importer_prefs, attr, val)
                    except Exception: pass # Logged in captures version
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
        logging.debug("Lock acquired for USD import process (Remix).")

        main_scene = context.scene
        import_scene_temp = None
        all_imported_usd_filepaths_to_process = []
        base_dir_for_textures = ""
        all_newly_imported_objects_in_temp = [] # Collect all objects from all USDs

        try:
            # --- Step 1: Fetch USD paths from Remix server ---
            # Use "prim_paths" as the key from server response
            assets_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/?selection=true&filter_session_assets=false&exists=true"
            # assets_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/?selection=true&filter_session_prims=false&exists=true" # Consider if this parameter also needs to change
            response = make_request_with_retries(
                method='GET', url=assets_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )
            if not response or response.status_code != 200:
                self.report({'ERROR'}, "Failed to connect to Remix server for asset list.")
                logging.error(f"Failed to connect to Remix server for asset list. Status: {response.status_code if response else 'No Response'}")
                return {'CANCELLED'}

            data = response.json()
            # CHANGED: Expect "prim_paths" instead of "asset_paths"
            asset_or_prim_paths = data.get("prim_paths", [])
            if not asset_or_prim_paths: # If "prim_paths" is empty or not found, try "asset_paths" as a fallback for older API versions
                logging.warning("Key 'prim_paths' not found or empty in server response, trying 'asset_paths' as fallback.")
                asset_or_prim_paths = data.get("asset_paths", [])

            mesh_prim_paths_from_remix = [path for path in asset_or_prim_paths if "meshes" in path.lower()]

            if not mesh_prim_paths_from_remix:
                self.report({'WARNING'}, "No mesh assets found in Remix server selection (checked 'prim_paths' and 'asset_paths').")
                logging.warning("No mesh assets found in Remix server selection (checked 'prim_paths' and 'asset_paths'). Response data: %s", data)
                return {'CANCELLED'}
            logging.info(f"Fetched mesh prim paths from Remix: {mesh_prim_paths_from_remix}")

            # --- Step 2: Determine base_dir and list of USD files to import ---
            # This part uses the first mesh path to get a reference for fetching file system paths
            first_mesh_path_remix = mesh_prim_paths_from_remix[0]
            # Trim the path to get the reference prim (e.g., /RootNode/meshes/mesh_ID)
            # The original script used [:4] assuming paths like /<some_root>/<project>/<asset_group>/<asset_id>/mesh
            # If the path is /RootNode/meshes/mesh_1B17A0CFBC5B20A0, [:4] gives /RootNode/meshes/mesh_1B17A0CFBC5B20A0
            # If the path is /RootNode/meshes/mesh_1B17A0CFBC5B20A0/mesh, [:4] also gives /RootNode/meshes/mesh_1B17A0CFBC5B20A0
            segments_for_ref_prim = first_mesh_path_remix.strip('/').split('/')
            if len(segments_for_ref_prim) >= 3 : # Ensure at least /RootNode/meshes/mesh_ID
                 # We need up to the mesh_ID part. If original first_mesh_path_remix was /RootNode/meshes/mesh_ID/mesh
                 # segments_for_ref_prim = ['RootNode', 'meshes', 'mesh_ID', 'mesh']
                 # We want '/RootNode/meshes/mesh_ID', which is segments_for_ref_prim[:3] if we add leading '/'
                 # If it was /RootNode/meshes/mesh_ID
                 # segments_for_ref_prim = ['RootNode', 'meshes', 'mesh_ID']
                 # also segments_for_ref_prim[:3]
                trimmed_prim_path_for_file_paths_api = '/' + '/'.join(segments_for_ref_prim[:3]) # Path like /RootNode/meshes/mesh_ID
            else:
                self.report({'ERROR'}, f"Cannot determine reference prim for file path API from: {first_mesh_path_remix}")
                logging.error(f"Cannot determine reference prim for file path API from: {first_mesh_path_remix}")
                return {'CANCELLED'}

            logging.info(f"Using trimmed prim path for file-paths API: {trimmed_prim_path_for_file_paths_api}")
            encoded_trimmed_path_remix = urllib.parse.quote(trimmed_prim_path_for_file_paths_api, safe='')

            file_paths_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/{encoded_trimmed_path_remix}/file-paths"
            response_files = make_request_with_retries(
                method='GET', url=file_paths_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )

            if not response_files or response_files.status_code != 200:
                self.report({'ERROR'}, f"Failed to retrieve file paths for reference prim: {trimmed_prim_path_for_file_paths_api}")
                logging.error(f"Failed to retrieve file paths for reference prim: {trimmed_prim_path_for_file_paths_api}. Status: {response_files.status_code if response_files else 'No Response'}")
                return {'CANCELLED'}

            file_data = response_files.json()
            reference_paths_list = file_data.get("reference_paths", [])
            logging.debug(f"File data response for {trimmed_prim_path_for_file_paths_api}: {file_data}")

            potential_base_path_source = None
            if reference_paths_list and \
               reference_paths_list[0] and \
               len(reference_paths_list[0]) > 1 and \
               isinstance(reference_paths_list[0][1], list) and \
               len(reference_paths_list[0][1]) > 1 and \
               isinstance(reference_paths_list[0][1][1], str):
                potential_base_path_source = reference_paths_list[0][1][1]
                logging.info(f"Identified potential absolute path for base_dir (from ...[0][1][1]): {potential_base_path_source}")
            else:
                log_msg = "Could not find the expected absolute file path in Remix server response structure (expected ...[0][1][1]). Details: "
                # (Detailed logging as before)
                self.report({'WARNING'}, "Remix Response: File path structure for base directory unexpected.")
                logging.warning(log_msg + f"Full reference_paths_list: {reference_paths_list}")


            if potential_base_path_source and os.path.isabs(potential_base_path_source) and os.path.exists(os.path.dirname(potential_base_path_source)):
                base_dir_for_textures = os.path.dirname(potential_base_path_source).replace('\\', '/')
                logging.info(f"Base directory for USDs and textures (Remix): {base_dir_for_textures}")
            else:
                err_msg = f"Could not determine a valid absolute base directory. Path used for dirname: '{potential_base_path_source}'. "
                err_msg += f"isabs: {os.path.isabs(str(potential_base_path_source))}, "
                err_msg += f"exists(dirname): {os.path.exists(os.path.dirname(str(potential_base_path_source)) if potential_base_path_source else '')}."
                self.report({'ERROR'}, "Base directory determination failed.")
                logging.error(err_msg)
                return {'CANCELLED'}

            for mesh_path_remix in mesh_prim_paths_from_remix:
                segments = mesh_path_remix.strip('/').split('/')
                # Example prim_path: /RootNode/meshes/mesh_1B17A0CFBC5B20A0/mesh
                # strip('/') -> "RootNode/meshes/mesh_1B17A0CFBC5B20A0/mesh"
                # split('/') -> segments = ['RootNode', 'meshes', 'mesh_1B17A0CFBC5B20A0', 'mesh']
                # We need 'mesh_1B17A0CFBC5B20A0', which is segments[2].
                #
                # Example prim_path: /RootNode/meshes/mesh_1B17A0CFBC5B20A0 (if it can also come without /mesh suffix)
                # strip('/') -> "RootNode/meshes/mesh_1B17A0CFBC5B20A0"
                # split('/') -> segments = ['RootNode', 'meshes', 'mesh_1B17A0CFBC5B20A0']
                # We need 'mesh_1B17A0CFBC5B20A0', which is segments[2].
                # len(segments) would be 3.
                
                if len(segments) > 2: # Check if segments[2] exists (i.e., length is at least 3)
                    mesh_name_from_prim = segments[2] # CORRECTED BACK to segments[2]
                    relative_usd_path = f"meshes/{mesh_name_from_prim}.usd"
                    usd_file_full_path = os.path.join(base_dir_for_textures, relative_usd_path).replace('\\', '/')
                    logging.info(f"Constructed full USD path for import: {usd_file_full_path} from prim {mesh_path_remix}")

                    if os.path.exists(usd_file_full_path):
                        mesh_object_name_expected = os.path.splitext(os.path.basename(usd_file_full_path))[0]
                        if bpy.data.objects.get(mesh_object_name_expected):
                            logging.info(f"Mesh '{mesh_object_name_expected}' (from {usd_file_full_path}) already exists in the main scene. Skipping import from Remix.")
                            # self.report({'INFO'}, f"Mesh '{mesh_object_name_expected}' from Remix already exists. Skipping.") # self.report not available here
                            print(f"INFO: Mesh '{mesh_object_name_expected}' from Remix already exists. Skipping.")
                            continue
                        all_imported_usd_filepaths_to_process.append(usd_file_full_path)
                    else:
                        logging.warning(f"Constructed USD file path from Remix data does not exist: {usd_file_full_path}")
                else:
                    logging.warning(f"Mesh path '{mesh_path_remix}' from Remix does not have expected segment count for filename extraction (expected at least 3 segments like RootNode/meshes/name/...).")

            if not all_imported_usd_filepaths_to_process:
                self.report({'INFO'}, "No new USD files from Remix selection to import (all may exist, paths invalid, or structure unexpected).")
                return {'FINISHED'} # Changed from CANCELLED to FINISHED as it's a valid state.

            # --- Step 2 (was 4): Create isolated import environment ---
            temp_scene_name = "Remix_USD_Import_Temp_V3" # Using V3 from import_captures for consistency
            idx = 0
            while temp_scene_name in bpy.data.scenes:
                idx += 1
                temp_scene_name = f"Remix_USD_Import_Temp_V3_{idx}"
            import_scene_temp = bpy.data.scenes.new(temp_scene_name)
            logging.info(f"Created temporary scene for Remix import: {import_scene_temp.name}")

            # --- Step 3 (was 5): Perform actual USD import into temporary scene ---
            imported_obj_map = self._perform_usd_import_into_scene(
                context,
                import_scene_temp,
                all_imported_usd_filepaths_to_process,
                addon_prefs
            )

            for objs_list in imported_obj_map.values():
                all_newly_imported_objects_in_temp.extend(objs_list)

            # Check if any objects were actually put into the temp scene directly by the importer,
            # even if our map is empty due to logic issues in _perform_usd_import_into_scene's tracking.
            if not all_newly_imported_objects_in_temp and not import_scene_temp.objects:
                self.report({'WARNING'}, "No objects were imported into the temporary scene from Remix.")
                # Cleanup is handled in finally
                return {'CANCELLED'}
            elif not all_newly_imported_objects_in_temp and import_scene_temp.objects:
                logging.warning("Tracking of newly imported objects failed, but temp scene has objects. Proceeding with all objects in temp scene.")
                all_newly_imported_objects_in_temp = list(import_scene_temp.objects)


            # --- Step 4 (was 6): Apply Transforms in temporary scene ---
            # Ensure context is on temp_scene before applying transforms
            original_window_scene_for_transform = context.window.scene
            if context.window.scene != import_scene_temp:
                context.window.scene = import_scene_temp
                logging.debug(f"Switched to temp scene '{import_scene_temp.name}' for transform application.")

            transform_stats = _perform_transform_application_phase_module(context, import_scene_temp)
            logging.info(f"Transform application phase for Remix import completed: {transform_stats}")

            if context.window.scene != original_window_scene_for_transform:
                context.window.scene = original_window_scene_for_transform # Switch back
                logging.debug(f"Switched back to original scene '{original_window_scene_for_transform.name}' after transform.")


            # --- Step 5 (was 7): Transfer objects to main scene ---
            transfer_stats = _perform_object_transfer_phase_module(context, main_scene, import_scene_temp)
            logging.info(f"Object transfer phase for Remix import completed: {transfer_stats}")


            # --- Step 6 (was 8): Attach original textures (Your existing logic) ---
            final_objects_in_main_scene = []
            if all_newly_imported_objects_in_temp :
                for temp_obj_ref in all_newly_imported_objects_in_temp: # temp_obj_ref might be an invalid reference if deleted from temp
                    try:
                        # Check if temp_obj_ref is still valid and get its name
                        # It might have been deleted if it was only in temp_scene and that scene was cleared or obj removed
                        # The objects are now in main_scene
                        main_scene_obj = main_scene.objects.get(temp_obj_ref.name) # temp_obj_ref.name might fail if ref is dead
                        if main_scene_obj:
                            final_objects_in_main_scene.append(main_scene_obj)
                    except ReferenceError:
                        logging.warning(f"A temporary object reference was no longer valid when checking for texture attachment.")
                        continue # Skip dead references
            else: # Fallback if tracking failed but objects were transferred
                logging.warning("all_newly_imported_objects_in_temp was empty; trying to identify transferred objects by name from previous temp scene content.")
                # This assumes _perform_object_transfer_phase_module correctly moved everything
                # and we don't have the original names if all_newly_imported_objects_in_temp was truly empty from the start
                # This branch is less robust. The best is to ensure all_newly_imported_objects_in_temp is populated correctly.
                # For now, if it's empty, this will likely result in no textures attached.

            if addon_prefs.remix_import_original_textures and base_dir_for_textures and final_objects_in_main_scene:
                logging.info(f"Attaching original textures (Remix import) to {len(final_objects_in_main_scene)} objects using base_dir: {base_dir_for_textures}.")
                attach_original_textures(final_objects_in_main_scene, context, base_dir_for_textures)
            elif not final_objects_in_main_scene:
                logging.warning("No final objects identified in main scene for texture attachment (Remix).")
            elif not addon_prefs.remix_import_original_textures:
                logging.info("Import original textures option is disabled.")
            elif not base_dir_for_textures:
                logging.warning("Base directory for textures was not determined; skipping texture attachment.")

            self.report({'INFO'}, f"Remix USD import completed. Processed {len(all_imported_usd_filepaths_to_process)} file(s). Transferred {transfer_stats.get('transferred_count',0)} top-level groups/objects.")
            return {'FINISHED'}

        except Exception as e_remix_main:
            logging.error(f"Unexpected error during main Remix USD import execute: {e_remix_main}", exc_info=True)
            self.report({'ERROR'}, f"Unexpected error during Remix import: {str(e_remix_main)}")
            return {'CANCELLED'}
        finally:
            if import_scene_temp and import_scene_temp.name in bpy.data.scenes:
                logging.info(f"Removing temporary Remix import scene: {import_scene_temp.name}")
                # Ensure no window is using the temp scene before removal
                for window in context.window_manager.windows:
                    if window.scene == import_scene_temp:
                        window.scene = main_scene # Switch to the main scene
                if context.window.scene == import_scene_temp: # Current context window
                     context.window.scene = main_scene

                bpy.data.scenes.remove(import_scene_temp, do_unlink=True)

            remix_import_lock = False
            logging.debug("Lock released for USD import process (Remix).")

class OBJECT_OT_export_and_ingest(Operator):
    bl_idname = "object.export_and_ingest"
    bl_label = "Export and Ingest (Dynamic Workers)"
    bl_options = {'REGISTER', 'UNDO'}

    # --- Operator State Variables ---
    _timer = None
    _op_lock: Lock = None
    _export_data: dict = {}

    # --- Dynamic Worker Management State ---
    _worker_slots: list = [] # Replaces _worker_pool. Tracks status of each potential worker.
    _task_batches: list = [] # Pre-calculated batches of tasks for each worker slot.
    _comm_threads: list = []
    _results_queue: Queue = None
    _log_queue: Queue = None
    _total_tasks: int = 0
    _finished_tasks: int = 0
    _failed_tasks: int = 0
    _resource_check_counter: int = 0

    # --- Configuration for Dynamic Workers ---
    MAX_POTENTIAL_WORKERS: int = max(1, os.cpu_count()) # Sane upper limit
    RESOURCE_CHECK_INTERVAL_SEC: int = 2 # How often to check system resources
    CPU_HIGH_THRESHOLD: int = 90 # % CPU to trigger worker termination
    RAM_HIGH_THRESHOLD: int = 90 # % RAM to trigger worker termination
    CPU_LOW_THRESHOLD: int = 80  # % CPU to allow new worker launch
    RAM_LOW_THRESHOLD: int = 80  # % RAM to allow new worker launch

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
        """
        [FINAL CORRECTED] Launches a worker with the correct Windows process flags
        to ensure it is terminated when the parent (Blender) closes, and registers
        it with the atexit handler for graceful shutdown.
        """
        if slot_index >= len(self._worker_slots):
            return

        slot = self._worker_slots[slot_index]
        if slot['process'] is not None and slot['process'].poll() is None:
            logging.warning(f"Attempted to launch worker for slot {slot_index}, but a process already exists.")
            return

        logging.info(f"→ Launching ISOLATED worker for slot {slot_index}...")
        cmd = [
            bpy.app.binary_path,
            "--factory-startup",
            "--background",
            "--python", BAKE_WORKER_PY,
            "--",
            "--persistent"
        ]
    
        try:
            # --- THIS IS THE FIX ---
            creation_flags = 0
            if sys.platform == "win32":
                # This flag is crucial. It groups the new process with its own
                # children, allowing terminate() to work reliably and preventing orphans
                # if the main Blender process is killed forcefully.
                creation_flags = subprocess.CREATE_NEW_PROCESS_GROUP
            # --- END OF FIX ---

            worker = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                creationflags=creation_flags, # Use the new flags here
                text=True,
                encoding='utf-8',
                bufsize=1
            )
        
            # Add the newly created process to our global registry for atexit.
            ACTIVE_WORKER_PROCESSES.append(worker)
        
            slot['process'] = worker
            slot['status'] = 'launching'

            comm_thread = threading.Thread(target=self._communication_thread_target, args=(worker,), daemon=True)
            log_thread = threading.Thread(target=self._log_thread_target, args=(worker,), daemon=True)
            comm_thread.start()
            log_thread.start()
            self._comm_threads.extend([comm_thread, log_thread])

            load_command = json.dumps({
                "action": "load_blend",
                "blend_file": abspath(bpy.data.filepath),
                "total_tasks": self._total_tasks
            }) + "\n"
            worker.stdin.write(load_command)
            worker.stdin.flush()

        except Exception as e:
            logging.error(f"Could not launch worker for slot {slot_index}: {e}", exc_info=True)
            slot['status'] = 'failed'
        
    def _terminate_worker(self, slot_index):
        """
        [CORRECTED] Terminates a worker and REMOVES it from the global
        atexit registry to prevent double-killing.
        """
        if slot_index >= len(self._worker_slots):
            return

        slot = self._worker_slots[slot_index]
        worker = slot.get('process')

        if worker and worker.poll() is None:
            logging.warning(f"Terminating worker in slot {slot_index} (PID: {worker.pid}).")
            try:
                worker.terminate()
                worker.wait(timeout=2)
            except (subprocess.TimeoutExpired, Exception):
                worker.kill()
            finally:
                # --- THIS IS THE FIX ---
                # Remove the now-dead process from the global registry.
                if worker in ACTIVE_WORKER_PROCESSES:
                    ACTIVE_WORKER_PROCESSES.remove(worker)
                # --- END OF FIX ---
            
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
        [DEFINITIVE V7 - CORRECTED MATERIAL ASSIGNMENT] Realizes a generator and
        correctly captures ALL resulting mesh objects and, crucially, transfers the
        materials used inside the Geometry Nodes tree to the new realized objects.
        This ensures the final export list has the correct materials for baking.
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

            # --- THE CORE FIX ---
            # For every new object created by the realization...
            for new_obj in final_realized_objects:
                # 1. Get a list of materials already in the object's slots.
                existing_mats = {slot.material for slot in new_obj.material_slots if slot.material}
                # 2. For each material identified from the GN tree...
                for mat_from_node in materials_to_assign:
                    # 3. ...if it's not already on the object, add it.
                    if mat_from_node not in existing_mats:
                        new_obj.data.materials.append(mat_from_node)
                logging.info(f"Ensured {len(new_obj.material_slots)} materials are present on new realized object '{new_obj.name}'.")

            # Process and track the newly found objects for cleanup.
            for i, new_obj in enumerate(final_realized_objects):
                base_name = f"{obj.name}_RealizedTemp"
                # Avoid renaming the object if it's the only one and was the duplicate
                if len(final_realized_objects) > 1 or new_obj.name != temp_duplicate.name:
                    new_obj.name = base_name if i == 0 else f"{base_name}.{i:03d}"
                self._export_data['temp_realized_object_names'].append(new_obj.name)

            logging.info(f"Successfully created and assigned materials to {len(final_realized_objects)} temporary realized objects: {[o.name for o in final_realized_objects]}")
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
        [CORRECTED V7 - ALPHA AWARE - COMPLETE] Determines if a material is a "simple" PBR setup.
        It now correctly identifies materials that use the Alpha channel as complex,
        triggering a bake for transparency. This is the full, unabridged function.
        """
        if not mat or not mat.use_nodes or not mat.node_tree:
            return False

        bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
        if not bsdf:
            return False

        temp_mat = bpy.data.materials.new(name="__temp_default_bsdf")
        temp_mat.use_nodes = True
        default_bsdf = temp_mat.node_tree.nodes.new('ShaderNodeBsdfPrincipled')

        try:
            # --- NEW: Explicitly check the Alpha socket first ---
            alpha_socket = bsdf.inputs.get("Alpha")
            if alpha_socket:
                # If Alpha is linked or its value is not 1.0, it needs baking.
                if alpha_socket.is_linked or not math.isclose(alpha_socket.default_value, 1.0, rel_tol=1e-5):
                    logging.info(f"Material '{mat.name}' is complex. Reason: Alpha channel is used (Value: {alpha_socket.default_value:.3f} or Linked).")
                    return False
            # --- END OF NEW CHECK ---

            sockets_to_check = {}
            for socket in default_bsdf.inputs:
                if socket.type in ('VALUE', 'VECTOR', 'RGBA') and not socket.hide_value:
                    # We already checked alpha, so skip it here.
                    if socket.name == "Alpha":
                        continue
                    sockets_to_check[socket.name] = socket.default_value if socket.type == 'VALUE' else socket.default_value[:]
    
            for socket_name, default_value in sockets_to_check.items():
                socket = bsdf.inputs.get(socket_name)
                if not socket:
                    continue

                # CONDITION 1: Check connected nodes
                if socket.is_linked:
                    link = socket.links[0]
                    source_node = link.from_node

                    if source_node.type == 'TEX_IMAGE':
                        continue
            
                    if socket_name == "Normal" and source_node.type == 'NORMAL_MAP':
                        color_input = source_node.inputs.get('Color')
                        if color_input and color_input.is_linked and color_input.links[0].from_node.type == 'TEX_IMAGE':
                            continue
            
                    logging.info(f"Material '{mat.name}' is complex. Reason: Input '{socket_name}' is driven by a non-texture node ('{source_node.type}').")
                    return False

                # CONDITION 2: Check unconnected sockets for default values
                else:
                    current_value = socket.default_value
            
                    is_different = False
                    if isinstance(default_value, (float, int)):
                        if not math.isclose(current_value, default_value, rel_tol=1e-5):
                            is_different = True
                    elif isinstance(default_value, (tuple, list)):
                        current_value_list = list(current_value)
                        default_value_list = list(default_value)
                        if len(current_value_list) == len(default_value_list):
                             if not all(math.isclose(a, b, rel_tol=1e-5) for a, b in zip(current_value_list, default_value_list)):
                                is_different = True
                        else:
                            is_different = True

                    if is_different:
                        current_val_str = f"[{', '.join(f'{v:.3f}' for v in current_value)}]" if hasattr(current_value, '__iter__') else f"{current_value:.3f}"
                        default_val_str = f"[{', '.join(f'{v:.3f}' for v in default_value)}]" if hasattr(default_value, '__iter__') else f"{default_value:.3f}"
                        logging.info(f"Material '{mat.name}' is complex. Reason: Unconnected input '{socket_name}' has non-default value ({current_val_str} vs default {default_val_str}).")
                        return False
    
            # Special check for the Normal socket
            normal_socket = bsdf.inputs.get("Normal")
            if normal_socket and normal_socket.is_linked:
                source_node = normal_socket.links[0].from_node
                if source_node.type == 'NORMAL_MAP':
                    color_input = source_node.inputs.get('Color')
                    if not (color_input and color_input.is_linked and color_input.links[0].from_node.type == 'TEX_IMAGE'):
                        logging.info(f"Material '{mat.name}' is complex. Reason: 'Normal' input is linked to a complex Normal Map setup.")
                        return False
                else:
                    logging.info(f"Material '{mat.name}' is complex. Reason: 'Normal' input is driven by a non-texture node ('{source_node.type}').")
                    return False

        finally:
            bpy.data.materials.remove(temp_mat)

        logging.info(f"Material '{mat.name}' has a simple PBR setup. Baking will be skipped.")
        return True
    
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

    def collect_bake_tasks(self, context, objects_to_process, export_data):
        """
        [DEFINITIVE V7 - PID LOCK FILE]
        Also creates its bake directory with the unique prefix and a PID lock file.
        """
        tasks = []
        if not is_blend_file_saved():
            raise RuntimeError("Blend file must be saved to create a bake/temp directory.")

        # ################################################################## #
        # THIS IS THE THIRD CRITICAL CHANGE                                  #
        # Create the bake dir with the unique prefix and write the lock file.#
        # ################################################################## #
        base_bake_path = CUSTOM_COLLECT_PATH
        os.makedirs(base_bake_path, exist_ok=True)

        # Create a uniquely named sub-folder inside the custom base path
        bake_dir_name = f"{TEMP_DIR_PREFIX}baked_textures_{uuid.uuid4().hex[:8]}"
        bake_dir = os.path.join(base_bake_path, bake_dir_name)
        os.makedirs(bake_dir, exist_ok=True)
        
        # Write the lock file with the current process ID
        try:
            with open(os.path.join(bake_dir, 'blender.lock'), 'w') as f:
                f.write(str(os.getpid()))
        except Exception as e:
            raise RuntimeError(f"Could not create .lock file for bake directory, aborting: {e}")

        export_data['temp_files_to_clean'].add(bake_dir)

        bake_info = {
            'tasks': [], 'bake_dir': bake_dir, 'special_texture_info': defaultdict(list),
            'udim_materials': set()
        }
        export_data['bake_info'] = bake_info

        SPECIAL_TEXTURE_MAP = {
            "Displacement": "HEIGHT",
            "Emission Color": "EMISSIVE",
            "Anisotropy": "ANISOTROPY",
            "Transmission": "TRANSMITTANCE",
            "Subsurface Radius": "MEASUREMENT_DISTANCE",
            "Subsurface Scale": "SINGLE_SCATTERING",
            "Alpha": "OPACITY"
        }
        CORE_PBR_CHANNELS = [
            ("Base Color", 'EMIT', False, True),
            ("Metallic", 'EMIT', True, False),
            ("Roughness", 'EMIT', True, False),
            ("Normal", 'NORMAL', False, False),
        ]
        OPTIONAL_CHANNELS = [
            ("Alpha", 'EMIT', True, False),
            ("Displacement", 'EMIT', True, False),
            ("Emission Color", 'EMIT', False, True),
            ("Anisotropy", 'EMIT', True, False),
            ("Transmission", 'EMIT', True, False),
            ("Subsurface Radius", 'EMIT', False, True),
            ("Subsurface Scale", 'EMIT', True, False)
        ]

        DEFAULT_BAKE_RESOLUTION = 2048

        logging.info("Analyzing materials using corrected replication strategy...")

        processed_object_material_pairs = set()

        for obj in objects_to_process:
            if obj.type != 'MESH' or not obj.data or not obj.data.uv_layers:
                continue

            for slot in obj.material_slots:
                mat = slot.material
                if not mat or not mat.use_nodes:
                    continue

                # --- THIS IS THE CRITICAL FIX ---
                # This check MUST come first to prevent processing the same material multiple times
                # if it's in multiple slots on the same object.
                if (obj.name, mat.name) in processed_object_material_pairs:
                    continue
                processed_object_material_pairs.add((obj.name, mat.name))
                # --- END OF FIX ---

                handled_by_direct_ingest = set()
            
                output_node = next((n for n in mat.node_tree.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
                bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)

                # Master list of all special sockets for direct ingestion
                special_sockets_to_check = {
                    "Displacement": (output_node, "HEIGHT"),
                    "Emission Color": (bsdf, "EMISSIVE"),
                    "Transmission": (bsdf, "TRANSMITTANCE"),
                    "Anisotropy": (bsdf, "ANISOTROPY"),
                    # Alpha is intentionally excluded here to let the albedo combination logic handle it
                    "Subsurface Radius": (bsdf, "MEASUREMENT_DISTANCE"),
                    "Subsurface Scale": (bsdf, "SINGLE_SCATTERING")
                }

                for socket_name, (node_to_check, server_type) in special_sockets_to_check.items():
                    if not node_to_check: continue
                    socket = node_to_check.inputs.get(socket_name)

                    if socket and socket.is_linked:
                        source_node = self._find_ultimate_source_node(socket)
                        if source_node and source_node.image and source_node.image.filepath and not self._material_uses_udims(mat):
                            filepath = abspath(source_node.image.filepath)
                            if os.path.exists(filepath):
                                logging.info(f"  > DIRECT INGEST: Found texture for '{socket_name}' on '{mat.name}'. Queuing.")
                                bake_info['special_texture_info'][(obj.name, mat.name)].append({'path': filepath, 'type': server_type})
                                handled_by_direct_ingest.add(socket_name)
            
                # --- Logic for actual baking (now runs only once per material) ---
                final_shader_node = None
                if output_node and output_node.inputs['Surface'].is_linked:
                    final_shader_node = output_node.inputs['Surface'].links[0].from_node

                is_complex = not self._is_simple_pbr_setup(mat)
                uses_udims = self._material_uses_udims(mat)

                if not (is_complex or uses_udims):
                    continue

                log_reason_parts = []
                if is_complex: log_reason_parts.append("complex setup")
                if uses_udims: log_reason_parts.append("UDIM textures")
                logging.info(f"  - Queuing BAKE tasks for material '{mat.name}' on object '{obj.name}' (Reason: {', '.join(log_reason_parts)}).")

                bake_resolution_x, bake_resolution_y = DEFAULT_BAKE_RESOLUTION, DEFAULT_BAKE_RESOLUTION
                uv_layer_for_bake = obj.data.uv_layers.active.name if obj.data.uv_layers.active else obj.data.uv_layers[0].name

                if uses_udims:
                    if mat.name not in bake_info['udim_materials']:
                        bake_info['udim_materials'].add(mat.name)
                        udim_node = next((n for n in mat.node_tree.nodes if n.type == 'TEX_IMAGE' and n.image and n.image.source == 'TILED'), None)
                        if udim_node and udim_node.image:
                            tiles = sorted([t for t in udim_node.image.tiles if t.label], key=lambda t: t.number)
                            if tiles:
                                tile_width, tile_height = udim_node.image.size
                                if tile_width == 0 or tile_height == 0:
                                    first_tile_path = abspath(udim_node.image.filepath_raw.replace('<UDIM>', str(tiles[0].number)))
                                    if os.path.exists(first_tile_path):
                                        temp_img = self._load_tile_robustly(first_tile_path, tiles[0].label)
                                        if temp_img:
                                            tile_width, tile_height = temp_img.size
                                            bpy.data.images.remove(temp_img)
                                if len(tiles) > 0 and tile_width > 0:
                                    bake_resolution_x = tile_width * len(tiles)
                                    bake_resolution_y = tile_height
                                    logging.info(f"   - UDIMs detected. Setting bake resolution to {bake_resolution_x}x{bake_resolution_y} for atlas.")
                                    objects_using_mat = [o for o in objects_to_process if mat in [s.material for s in o.material_slots]]
                                    self._transform_uvs_for_atlas(objects_using_mat, tiles)
                                    uv_layer_for_bake = "remix_atlas_uv"
                else:
                    max_w, max_h = self._find_largest_texture_resolution_recursive(mat.node_tree)
                    if max_w > 0: bake_resolution_x = max_w
                    if max_h > 0: bake_resolution_y = max_h
                    if max_w > 0 or max_h > 0: logging.info(f"   - Dynamically set bake resolution to {bake_resolution_x}x{bake_resolution_y}.")

                mat_uuid = mat.get("uuid", str(uuid.uuid4())); mat["uuid"] = mat_uuid

                task_templates = list(CORE_PBR_CHANNELS)

                for channel_name, bake_type, is_val, is_color in OPTIONAL_CHANNELS:
                    if channel_name in handled_by_direct_ingest:
                        continue

                    if channel_name == "Displacement":
                        socket = output_node.inputs.get(channel_name) if output_node else None
                    else:
                        socket = final_shader_node.inputs.get(channel_name) if final_shader_node else None

                    if (socket and socket.is_linked) or \
                       (channel_name == "Alpha" and socket and not math.isclose(socket.default_value, 1.0)):
                        task_templates.append((channel_name, bake_type, is_val, is_color))

                for channel_name, bake_type, is_val, is_color in task_templates:
                    safe_obj_name = "".join(c for c in obj.name if c.isalnum() or c in ('_', '-')).strip()
                    safe_mat_name = "".join(c for c in mat.name if c.isalnum() or c in ('_', '-')).strip()
                    safe_socket_name = channel_name.replace(' ', '')
                    if uses_udims:
                        output_filename = f"{safe_mat_name}_{safe_socket_name}_baked.png"
                    else:
                        output_filename = f"{safe_obj_name}_{safe_mat_name}_{safe_socket_name}_baked.png"

                    output_path = os.path.join(bake_dir, output_filename)

                    if channel_name in SPECIAL_TEXTURE_MAP and channel_name != "Alpha":
                        bake_info['special_texture_info'][(obj.name, mat.name)].append({
                            'path': output_path, 'type': SPECIAL_TEXTURE_MAP[channel_name]
                        })

                    tasks.append({
                        "material_name": mat.name, "material_uuid": mat_uuid, "object_name": obj.name,
                        "bake_type": 'EMIT' if uses_udims and bake_type == 'DIFFUSE' else bake_type,
                        "output_path": output_path, "target_socket_name": channel_name,
                        "is_value_bake": is_val, "is_color_data": is_color,
                        "resolution_x": bake_resolution_x, "resolution_y": bake_resolution_y,
                        "uv_layer": uv_layer_for_bake
                    })

        bake_info['tasks'] = tasks
        if bake_info['tasks']: logging.info(f"Generated {len(bake_info['tasks'])} total BAKE tasks for procedural/UDIM materials.")
    
        total_special_maps = sum(len(v) for v in bake_info['special_texture_info'].values())
        if total_special_maps > 0: logging.info(f"Found a total of {total_special_maps} special maps to be ingested (some may be from bakes).")

        return tasks, {}, bake_dir, bake_info.get('special_texture_info', {})
    
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

          
    def modal(self, context, event):
        """
        [DEFINITIVE V3 - Corrected Terminate After Task]
        This is the complete and corrected modal loop. It implements the robust
        resource manager that flags workers for termination but allows them to finish
        their current task. The critical bug where successfully completed tasks were
        requeued has been fixed by calling the worker handler with `requeue_task=False`
        after a graceful shutdown.
        """
        if event.type != 'TIMER':
            return {'PASS_THROUGH'}

        with self._op_lock:
            # First-tick initialization
            if not hasattr(self, '_initialized'):
                self._initialized = True
                logging.info(f"Saving blend file for {self._total_tasks} bake tasks...")
                bpy.ops.wm.save_mainfile()
            
                self._master_task_queue = collections.deque(
                    task for batch in self._task_batches for task in batch
                )
            
                num_to_launch = min(len(self._worker_slots), MAX_CONCURRENT_BAKE_WORKERS)
                for i in range(num_to_launch):
                    if self._worker_slots[i]['status'] == 'idle':
                        self._launch_new_worker(i)
                return {'PASS_THROUGH'}

            # --- Phase 1: Process Logs & Results ---
            try:
                while not self._log_queue.empty():
                    print(self._log_queue.get_nowait())
            except Empty: pass

            try:
                while not self._results_queue.empty():
                    result_line = self._results_queue.get_nowait()
                    try:
                        result = json.loads(result_line)
                        status = result.get("status")
                        worker_pid = result.get("pid")
                        slot_index = -1
                        if worker_pid:
                            for i, s in enumerate(self._worker_slots):
                                if s.get('process') and s['process'].pid == worker_pid:
                                    slot_index = i; break
                        if slot_index == -1: continue

                        slot = self._worker_slots[slot_index]

                        if status == "ready":
                            slot['status'] = 'ready'
                            logging.info(f"Worker in slot {slot_index} (PID: {worker_pid}) is now READY.")
                    
                        elif status in ["success", "failure"]:
                            self._finished_tasks += 1
                            if status == "failure": self._failed_tasks += 1
                        
                            # Check if this worker was flagged for termination
                            if slot.get('flagged_for_termination'):
                                logging.warning(f"Worker {slot_index} finished its task and is now being terminated as flagged.")
                                # THIS IS THE FIX: Terminate the worker, but DO NOT requeue its successfully completed task.
                                self._handle_failed_worker(slot_index, requeue_task=False)
                            else:
                                # If not flagged, it's ready for another task
                                slot['status'] = 'ready'
                            
                        elif status == "error":
                            logging.error(f"Worker in slot {slot_index} reported a critical error: {result.get('details', 'N/A')}")
                            # Terminate immediately on critical error and requeue its task by default.
                            self._handle_failed_worker(slot_index)
                    except (json.JSONDecodeError, KeyError): pass
            except Empty: pass

            # --- Phase 2: Resilient Task Dispatching ---
            for i, slot in enumerate(self._worker_slots):
                if slot['status'] == 'ready':
                    if self._master_task_queue:
                        task_to_dispatch = self._master_task_queue.popleft()
                        try:
                            slot['process'].stdin.write(json.dumps(task_to_dispatch) + "\n")
                            slot['process'].stdin.flush()
                            slot['status'] = 'running'
                            slot['current_task'] = task_to_dispatch
                        except (IOError, BrokenPipeError):
                            logging.error(f"Pipe to worker {i} was broken. Requeueing task.")
                            self._master_task_queue.appendleft(task_to_dispatch)
                            self._handle_failed_worker(i)
                    else:
                        slot['status'] = 'finished'

            # --- Phase 3: Dynamic Worker Management & Monitoring ---
            self._resource_check_counter += 1
            if (self._resource_check_counter * 0.1) >= self.RESOURCE_CHECK_INTERVAL_SEC:
                self._resource_check_counter = 0
                if PSUTIL_INSTALLED:
                    import psutil
                    cpu_usage = psutil.cpu_percent()
                    ram_usage = psutil.virtual_memory().percent

                    if cpu_usage < self.CPU_LOW_THRESHOLD and ram_usage < self.RAM_LOW_THRESHOLD:
                        for i, slot in enumerate(self._worker_slots):
                            if slot['status'] in ['idle', 'suspended']:
                                self._launch_new_worker(i)
                                slot['flagged_for_termination'] = False # Clear flag on relaunch
                                break
                
                    elif cpu_usage > self.CPU_HIGH_THRESHOLD or ram_usage > self.RAM_HIGH_THRESHOLD:
                        for i, slot in reversed(list(enumerate(self._worker_slots))):
                            if slot['status'] == 'running' and not slot.get('flagged_for_termination'):
                                logging.warning(f"High resource usage detected. Flagging worker {i} for termination after its current task.")
                                slot['flagged_for_termination'] = True
                                break

            # Monitor for unexpected crashes
            for i, slot in enumerate(self._worker_slots):
                if slot.get('process') and slot['process'].poll() is not None and slot['status'] == 'running':
                    logging.error(f"Worker in slot {i} (PID: {slot['process'].pid}) has crashed unexpectedly!")
                    # A real crash, so we DO want to requeue the task.
                    self._handle_failed_worker(i, requeue_task=True)
            
            # --- Phase 4: UI Update & Completion Check ---
            if self._total_tasks > 0:
                progress = (self._finished_tasks / self._total_tasks) * 100
                status_text = f"Baking... {self._finished_tasks}/{self._total_tasks} ({progress:.0f}%)"
                if self._failed_tasks > 0: status_text += f" - FAILED: {self._failed_tasks}"
                active_workers = sum(1 for s in self._worker_slots if s['status'] in ['running', 'launching'])
                status_text += f" | Active: {active_workers} | Queued: {len(self._master_task_queue)}"
                context.workspace.status_text_set(status_text)
        
            if self._finished_tasks >= self._total_tasks:
                if self._failed_tasks > 0:
                    self.report({'ERROR'}, f"{self._failed_tasks} bake task(s) failed. See console.")
                    return self._cleanup(context, {'CANCELLED'})
                else:
                    logging.info("All bake tasks completed successfully.")
                    self._finalize_export(context)
                    self.report({'INFO'}, f"Export complete. Baked {self._total_tasks} textures.")
                    return self._cleanup(context, {'FINISHED'})

            return {'PASS_THROUGH'}
        
    def _handle_failed_worker(self, slot_index, requeue_task=True):
        """
        Helper function to terminate a worker. Can optionally requeue the task
        it was working on.
        """
        if slot_index >= len(self._worker_slots): return
    
        slot = self._worker_slots[slot_index]
    
        # Requeue the task it was working on, ONLY if requested.
        if requeue_task and 'current_task' in slot and slot['current_task']:
            task = slot['current_task']
            self._master_task_queue.appendleft(task) # Put it back at the front of the line
            logging.warning(f"Requeueing task '{task.get('bake_type')}' for material '{task.get('material_name')}' from failed worker {slot_index}.")
    
        slot['current_task'] = None
        self._terminate_worker(slot_index) # This sets status to 'suspended'
       
          
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
    
    def _combine_albedo_and_opacity(self, color_map_path, opacity_map_path):
        """
        [CORRECTED] Loads a color map and a grayscale opacity map, and combines them into a
        single RGBA image. The opacity map's values are placed into the alpha channel of the
        color map. The final combined image overwrites the original color map path.
        """
        try:
            from PIL import Image, ImageOps
        except ImportError:
            logging.error("Pillow library is not installed. Cannot combine albedo and opacity maps.")
            self.report({'ERROR'}, "Pillow dependency not found. Cannot create transparency.")
            return

        if not os.path.exists(color_map_path) or not os.path.exists(opacity_map_path):
            logging.warning(f"Skipping texture combination: one or both maps missing. Color: '{os.path.exists(color_map_path)}', Opacity: '{os.path.exists(opacity_map_path)}'")
            return

        logging.info(f"  > Combining '{os.path.basename(color_map_path)}' with opacity from '{os.path.basename(opacity_map_path)}'")

        try:
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

            # Save the combined RGBA image, overwriting the original color map.
            albedo_img.save(color_map_path, "PNG")
            logging.info(f"    - Successfully created RGBA texture at: {os.path.basename(color_map_path)}")

        except Exception as e:
            logging.error(f"Failed during texture combination for '{color_map_path}': {e}", exc_info=True)
            self.report({'WARNING'}, "Failed to combine color and opacity maps.")

    def execute(self, context):
        if not PSUTIL_INSTALLED:
            self.report({'ERROR'}, "Dependency 'psutil' is not installed. Please install it from the addon panel.")
            return {'CANCELLED'}

        global export_lock
        if export_lock:
            self.report({'INFO'}, "Another export is already in progress.")
            return {'CANCELLED'}

        export_lock = True

        # Initialize operator state
        self._timer = None
        self._op_lock = Lock()
        self._export_data = {
            "objects_for_export": [], 
            "bake_info": {}, 
            "temp_files_to_clean": set(),
            "original_material_assignments": {}, 
            "temp_materials_for_cleanup": [],
            "normals_were_flipped": False, 
            "temp_realized_object_names": []
        }
        self._task_batches = []
        self._worker_slots = []
        self._comm_threads = []
        self._results_queue = Queue()
        self._log_queue = Queue()
        self._total_tasks = 0
        self._finished_tasks = 0
        self._failed_tasks = 0
        self._resource_check_counter = 0

        try:
            logging.info("Checking for EXR textures to convert before export...")
            success, _ = convert_exr_textures_to_png(context)
            if not success:
                raise RuntimeError("Failed to convert EXR textures to PNG.")

            addon_prefs = context.preferences.addons[__name__].preferences
            if not is_blend_file_saved():
                raise RuntimeError("Please save the .blend file before exporting.")

            initial_selection = {
                o for o in (context.selected_objects if addon_prefs.remix_use_selection_only else context.scene.objects)
                if o.type in {'MESH', 'CURVE'} and o.visible_get() and not o.hide_render
            }

            if not initial_selection:
                raise RuntimeError("No suitable visible objects found to export.")

            # --- YOUR OLD WORKING CODE ---
            final_export_list = set(initial_selection)
            generators_found = {obj for obj in initial_selection if self._is_geonodes_generator(obj)}
            
            source_objects_to_exclude = set()
            if generators_found:
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
            # --- END OF YOUR OLD WORKING CODE ---

            self._export_data["objects_for_export"] = [o for o in final_export_list if o and o.type == 'MESH']

            if not self._export_data["objects_for_export"]:
                raise RuntimeError("Processing resulted in no valid mesh objects to export.")

            logging.info(f"Final object list for processing: {[o.name for o in self._export_data['objects_for_export']]}")

            if not self._validate_textures(context, self._export_data["objects_for_export"]): raise RuntimeError("Texture validation failed.")

            all_tasks, _, _, _ = self.collect_bake_tasks(
                context, self._export_data["objects_for_export"], self._export_data
            )
            self._total_tasks = len(all_tasks)

            any_udims_found = any(self._material_uses_udims(s.material) for obj in self._export_data["objects_for_export"] for s in obj.material_slots if s.material)
            
            if not all_tasks and not any_udims_found:
                logging.info("No complex materials or UDIMs found. Finalizing export directly with simple textures.")
                self._finalize_export(context)
                return self._cleanup(context, {'FINISHED'})

            if all_tasks:
                logging.info(f"Found {self._total_tasks} bake tasks. Starting worker pool...")
                for i, task in enumerate(all_tasks):
                    task['global_task_number'] = i + 1

                num_batches = min(self._total_tasks, MAX_CONCURRENT_BAKE_WORKERS)
                self._task_batches = [[] for _ in range(num_batches)]
                for i, task in enumerate(all_tasks):
                    self._task_batches[i % num_batches].append(task)

                self._worker_slots = [{'process': None, 'status': 'idle', 'batch_index': i, 'flagged_for_termination': False} for i in range(num_batches)]

                self._timer = context.window_manager.event_timer_add(0.1, window=context.window)
                context.window_manager.modal_handler_add(self)
                return {'RUNNING_MODAL'}
            
            else:
                logging.info("No bake tasks, but UDIMs found. Proceeding directly to finalization for stitching.")
                self._finalize_export(context)
                return self._cleanup(context, {'FINISHED'})

        except Exception as e:
            logging.error(f"Export failed during setup: {e}", exc_info=True)
            self.report({'ERROR'}, f"Export setup failed: {e}")
            return self._cleanup(context, {'CANCELLED'})

    def _finalize_export(self, context):
        """
        [DEFINITIVE V10 - PID LOCK FILE]
        Handles the final steps of the export process, including creating the temporary
        directory with a PID lock file for guaranteed cleanup on the next startup,
        even after a forced shutdown of Blender.
        """
        addon_prefs = context.preferences.addons[__name__].preferences
        original_active_uvs = {}

        try:
            logging.info("--- Finalizing Export (PID Lock Implementation) ---")

            bake_info = self._export_data.get('bake_info', {})
            path_remap = {}

            # Hash baked texture filenames to prevent caching issues
            if bake_info and bake_info.get('tasks'):
                logging.info("Hashing baked textures before proceeding...")
                unique_paths_to_hash = {task.get('output_path') for task in bake_info['tasks'] if task.get('output_path')}

                for original_path in unique_paths_to_hash:
                    if original_path and os.path.exists(original_path):
                        new_hashed_path = self._hash_and_rename_file(original_path)
                        path_remap[original_path] = new_hashed_path

                if path_remap:
                    for task in bake_info.get('tasks', []):
                        original_path = task.get('output_path')
                        if original_path in path_remap:
                            task['output_path'] = path_remap[original_path]

                    if bake_info.get('special_texture_info'):
                        for mat_name, texture_list in bake_info['special_texture_info'].items():
                            for texture_data in texture_list:
                                original_special_path = texture_data.get('path')
                                if original_special_path in path_remap:
                                    texture_data['path'] = path_remap[original_special_path]

            # Combine Albedo and Opacity maps if they were baked
            if bake_info and bake_info.get('tasks') and PILLOW_INSTALLED:
                tasks = bake_info.get('tasks', [])
                tasks_by_mat_uuid = defaultdict(dict)
                for task in tasks:
                    tasks_by_mat_uuid[task['material_uuid']][task['target_socket_name']] = task['output_path']

                logging.info("Combining baked Color and Alpha maps into final RGBA textures...")
                for mat_uuid, maps in tasks_by_mat_uuid.items():
                    if "Base Color" in maps and "Alpha" in maps:
                        self._combine_albedo_and_opacity(maps["Base Color"], maps["Alpha"])

            final_meshes_for_obj = self._export_data.get("objects_for_export", [])
            if not final_meshes_for_obj:
                raise RuntimeError("Final object list for export is empty.")

            logging.info(f" > Finalizing with {len(final_meshes_for_obj)} mesh objects: {[o.name for o in final_meshes_for_obj]}")

            any_udims_found = bake_info.get('udim_materials')
            if self._total_tasks > 0 or any_udims_found:
                logging.info(f"Preparing materials for export (Bakes: {self._total_tasks > 0}, UDIMs: {bool(any_udims_found)}).")
                self._prepare_materials_for_export(context, objects_to_process=final_meshes_for_obj)
            else:
                logging.info(" > No bakes or UDIMs found. Exporting with original materials.")

            if addon_prefs.flip_faces_export:
                logging.info("Applying 'Flip Normals' to final export meshes.")
                batch_flip_normals_optimized(final_meshes_for_obj, context)
                self._export_data["normals_were_flipped"] = True

            base_name, asset_number = get_asset_number(context)
            obj_filename = f"{base_name}_{asset_number}.obj"

            # Use the global constant for the base path
            base_finalize_path = CUSTOM_FINALIZE_PATH
            os.makedirs(base_finalize_path, exist_ok=True)

            # Create the temp dir inside the custom path
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

            logging.info("Preparing selection for OBJ exporter...")
            bpy.ops.object.select_all(action='DESELECT')
            selectable_meshes = [obj for obj in final_meshes_for_obj if obj and obj.name in context.view_layer.objects]
            if not selectable_meshes:
                raise RuntimeError("None of the final meshes are selectable in the current view layer.")
            for obj in selectable_meshes:
                obj.select_set(True)
            context.view_layer.objects.active = selectable_meshes[0]

            # Set the active UV map to the atlas map for objects that were processed
            for obj in final_meshes_for_obj:
                if obj.data and "remix_atlas_uv" in obj.data.uv_layers:
                     if obj.data.uv_layers.active:
                         original_active_uvs[obj.name] = obj.data.uv_layers.active.name
                     obj.data.uv_layers.active = obj.data.uv_layers["remix_atlas_uv"]

            logging.info(f" > Exporting {len(context.selected_objects)} objects to OBJ...")
            bpy.ops.wm.obj_export(
                filepath=exported_obj_path, check_existing=True, export_selected_objects=True,
                forward_axis=addon_prefs.obj_export_forward_axis, up_axis=addon_prefs.obj_export_up_axis,
                global_scale=addon_prefs.remix_export_scale, apply_modifiers=addon_prefs.apply_modifiers,
                export_materials=True, path_mode='COPY', export_pbr_extensions=True
            )

            logging.info(f"Exported to temporary OBJ: {exported_obj_path}")

            ingested_usd = upload_to_api(exported_obj_path, addon_prefs.remix_ingest_directory, context)
            if not ingested_usd:
                raise RuntimeError("API upload failed.")

            final_reference_prim = self._replace_or_append_on_server(context, ingested_usd)
            if not final_reference_prim:
                raise RuntimeError("Server replace/append operation failed.")

            if bake_info.get('special_texture_info'):
                handle_special_texture_assignments(self, context, final_reference_prim, export_data=self._export_data)

            source_bake_dir = bake_info.get('bake_dir')
            destination_dir = r"C:\Users\Friss\Documents\Test3" # User-specific path, kept as is
            if source_bake_dir and os.path.isdir(source_bake_dir):
                shutil.copytree(source_bake_dir, destination_dir, dirs_exist_ok=True)

        except Exception as e:
            logging.error(f"Export finalization failed: {e}", exc_info=True)
            self.report({'ERROR'}, f"Finalization failed: {e}")

        finally:
            if original_active_uvs:
                for obj_name, original_map_name in original_active_uvs.items():
                    obj = bpy.data.objects.get(obj_name)
                    if obj and obj.data and original_map_name in obj.data.uv_layers:
                        obj.data.uv_layers.active = obj.data.uv_layers[original_map_name]
                        
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
        [FROM ADDON 2 - ADAPTED FOR ADDON 1]
        Stitches existing UDIM tiles into a new atlas texture. This does NOT bake,
        it combines the source images directly. It has been adapted to integrate
        with Addon 1's more advanced special texture handling.
        """
        if not mat or not mat.use_nodes:
            return None, None
        logging.info(f"--- Starting UDIM Stitch for Material: '{mat.name}' ---")
        
        bake_info = self._export_data.get('bake_info', {})
        
        bsdf = next((n for n in mat.node_tree.nodes if n.type == "BSDF_PRINCIPLED"), None)
        output_node = next((n for n in mat.node_tree.nodes if n.type == "OUTPUT_MATERIAL"), None)
        if not bsdf or not output_node:
            logging.warning(f"No Principled BSDF or Material Output found in '{mat.name}'. Cannot stitch.")
            return mat, None

        udim_jobs = collections.defaultdict(list)
        sockets_to_check = list(bsdf.inputs) + [output_node.inputs['Displacement']]
        for socket in sockets_to_check:
            if not socket.is_linked: continue
            # Use Addon 1's more robust node finding function
            source_node = self._find_ultimate_source_node(socket)
            if source_node and source_node.image and source_node.image.source == 'TILED':
                udim_jobs[source_node].append(socket.name)

        if not udim_jobs:
            logging.info(f"No UDIM textures found to stitch for material '{mat.name}'.")
            return mat, None

        final_stitched_mat = bpy.data.materials.new(name=f"{mat.name}__UDIM_STITCHED")
        self._export_data["temp_materials_for_cleanup"].append(final_stitched_mat)
        
        final_stitched_mat.use_nodes = True
        nt = final_stitched_mat.node_tree
        for node in nt.nodes: nt.nodes.remove(node)
        
        new_bsdf = nt.nodes.new('ShaderNodeBsdfPrincipled')
        new_mat_output = nt.nodes.new('ShaderNodeOutputMaterial')
        nt.links.new(new_bsdf.outputs['BSDF'], new_mat_output.inputs['Surface'])
        
        uv_map_node = nt.nodes.new('ShaderNodeUVMap')
        uv_map_node.uv_map = "remix_atlas_uv"

        all_processed_tiles = []
        for udim_node, target_socket_names in udim_jobs.items():
            image = udim_node.image
            tiles = sorted([t for t in image.tiles if t.label], key=lambda t: t.number)
            if not all_processed_tiles: all_processed_tiles = tiles
            
            if not tiles:
                logging.warning(f"UDIM texture '{image.name}' has no valid tiles. Skipping.")
                continue

            logging.info(f"Found {len(tiles)} tiles for UDIM texture '{image.name}'. Stitching...")
            tile_width, tile_height = image.size

            if tile_width == 0 or tile_height == 0:
                # Logic to determine size from first available tile
                for tile in tiles:
                    tile_path = abspath(image.filepath_raw.replace('<UDIM>', str(tile.number)))
                    if os.path.exists(tile_path):
                        loaded_tile = self._load_tile_robustly(tile_path, tile.label)
                        if loaded_tile:
                            tile_width, tile_height = loaded_tile.size
                            bpy.data.images.remove(loaded_tile)
                            break
                if tile_width == 0: # If still zero, error and default
                    logging.error(f"Could not determine tile size for '{image.name}'. Defaulting to 2048.")
                    tile_width, tile_height = 2048, 2048

            atlas_width = tile_width * len(tiles)
            atlas_height = tile_height
            
            safe_mat_name = "".join(c for c in mat.name if c.isalnum() or c in ('_', '.', '-'))
            safe_img_name = "".join(c for c in image.name if c.isalnum() or c in ('_', '.', '-'))
            atlas_filename = f"{safe_mat_name}_{safe_img_name}_atlas.png"
            atlas_filepath = os.path.join(bake_dir, atlas_filename)

            atlas_image = bpy.data.images.new(name=atlas_filename, width=atlas_width, height=atlas_height, alpha=True)
            atlas_image.filepath_raw = atlas_filepath
            atlas_image.file_format = 'PNG'
            atlas_pixels = [0.0] * (atlas_width * atlas_height * 4)

            for i, tile in enumerate(tiles):
                tile_path = abspath(image.filepath_raw.replace('<UDIM>', str(tile.number)))
                if not os.path.exists(tile_path): continue
                
                tile_image = self._load_tile_robustly(tile_path, tile.label)
                if not tile_image: continue

                try:
                    if tile_image.size[0] != tile_width or tile_image.size[1] != tile_height:
                        tile_image.scale(tile_width, tile_height)
                    
                    tile_pixels = tile_image.pixels[:]
                    for y in range(tile_height):
                        src_start = (y * tile_width) * 4
                        src_end = src_start + (tile_width * 4)
                        dest_x = i * tile_width
                        dest_start = (y * atlas_width + dest_x) * 4
                        dest_end = dest_start + (tile_width * 4)
                        atlas_pixels[dest_start:dest_end] = tile_pixels[src_start:src_end]
                finally:
                    bpy.data.images.remove(tile_image)

            atlas_image.pixels = atlas_pixels
            atlas_image.save()
            
            atlas_tex_node = nt.nodes.new('ShaderNodeTexImage')
            atlas_tex_node.image = atlas_image
            nt.links.new(uv_map_node.outputs['UV'], atlas_tex_node.inputs['Vector'])
            
            is_data = any(n in s for s in target_socket_names for n in ['Normal', 'Roughness', 'Metallic', 'Displacement'])
            atlas_image.colorspace_settings.name = 'Non-Color' if is_data else 'sRGB'

            for socket_name in target_socket_names:
                target_socket = new_bsdf.inputs.get(socket_name) or new_mat_output.inputs.get(socket_name)
                if not target_socket: continue
                
                if 'Normal' in socket_name:
                    normal_map_node = nt.nodes.new('ShaderNodeNormalMap')
                    nt.links.new(atlas_tex_node.outputs['Color'], normal_map_node.inputs['Color'])
                    nt.links.new(normal_map_node.outputs['Normal'], target_socket)
                elif 'Displacement' in socket_name:
                    disp_node = nt.nodes.new('ShaderNodeDisplacement')
                    nt.links.new(atlas_tex_node.outputs['Color'], disp_node.inputs['Height'])
                    nt.links.new(disp_node.outputs['Displacement'], new_mat_output.inputs['Displacement'])
                    # ** ADAPTATION FOR ADDON 1 **
                    # Use the advanced special_texture_info structure
                    bake_info['special_texture_info'][mat.name].append({
                        'path': atlas_filepath, 'type': 'HEIGHT'
                    })
                else:
                    nt.links.new(atlas_tex_node.outputs['Color'], target_socket)

        self._transform_uvs_for_atlas(objects_using_mat, all_processed_tiles)
        logging.info(f"--- Finished UDIM Stitch for '{mat.name}' ---")
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
        [OBJECT-CENTRIC FIX V2]
        This function has been completely rewritten to be object-centric. It iterates
        through each object and its material slots, creating a unique baked material
        for each slot that used a procedural or UDIM material. This ensures that
        objects with unique UVs receive their corresponding unique baked textures.
        """
        logging.info("Preparing final export materials (Object-Centric Fix)...")

        self._export_data["original_material_assignments"] = {
            obj.name: [s.material for s in obj.material_slots] for obj in objects_to_process if obj
        }

        bake_info = self._export_data.get('bake_info', {})
    
        # --- START OF THE FIX: Group tasks by object AND material ---
        tasks_by_object_and_mat_uuid = defaultdict(list)
        for task in bake_info.get('tasks', []):
            key = (task.get("object_name"), task.get("material_uuid"))
            tasks_by_object_and_mat_uuid[key].append(task)
    
        # Iterate through objects first, then their materials.
        for obj in objects_to_process:
            if not obj: continue
        
            # We need to iterate over a copy because we are modifying the slots
            for i, slot in enumerate(list(obj.material_slots)):
                original_assignments = self._export_data["original_material_assignments"].get(obj.name)
                if not original_assignments or i >= len(original_assignments):
                    continue
                
                original_mat = original_assignments[i]
                if not original_mat:
                    continue

                mat_uuid = original_mat.get("uuid")
            
                # Find the specific bake tasks for THIS object and THIS material
                tasks_for_this_slot = tasks_by_object_and_mat_uuid.get((obj.name, mat_uuid))
            
                # If tasks exist, it means this specific slot needs a new, unique baked material
                if tasks_for_this_slot:
                    logging.info(f"   - Building unique baked material for object '{obj.name}', slot {i} (original: '{original_mat.name}')...")
                
                    # Create a unique name for the new material
                    safe_obj_name = "".join(c for c in obj.name if c.isalnum() or c in ('_', '-')).strip()
                    safe_mat_name = "".join(c for c in original_mat.name if c.isalnum() or c in ('_', '-')).strip()
                    baked_mat_name = f"{safe_obj_name}_{safe_mat_name}_BAKED"
                
                    baked_mat = bpy.data.materials.new(name=baked_mat_name)
                    self._export_data["temp_materials_for_cleanup"].append(baked_mat)
                    baked_mat.use_nodes = True
                    nt = baked_mat.node_tree
                    for node in nt.nodes: nt.nodes.remove(node)
            
                    bsdf = nt.nodes.new('ShaderNodeBsdfPrincipled')
                    out = nt.nodes.new('ShaderNodeOutputMaterial')
                    nt.links.new(bsdf.outputs['BSDF'], out.inputs['Surface'])
            
                    uv_map_node = None
                    if original_mat.name in bake_info.get('udim_materials', set()):
                        uv_map_node = nt.nodes.new('ShaderNodeUVMap')
                        uv_map_node.uv_map = "remix_atlas_uv"

                    unique_textures = {os.path.basename(t['output_path']): t for t in tasks_for_this_slot}.values()
                    for task in unique_textures:
                        if not os.path.exists(task['output_path']): continue
                    
                        tex_node = nt.nodes.new('ShaderNodeTexImage')
                        tex_node.image = bpy.data.images.load(task["output_path"], check_existing=True)
                
                        if uv_map_node:
                            nt.links.new(uv_map_node.outputs['UV'], tex_node.inputs['Vector'])

                        if not task.get("is_color_data", False):
                            tex_node.image.colorspace_settings.name = 'Non-Color'
                
                        target_name = task.get("target_socket_name")
                        if target_name == "Base Color":
                            nt.links.new(tex_node.outputs['Color'], bsdf.inputs['Base Color'])
                            nt.links.new(tex_node.outputs['Alpha'], bsdf.inputs['Alpha'])
                        elif target_name == "Normal":
                            norm_map = nt.nodes.new('ShaderNodeNormalMap')
                            nt.links.new(tex_node.outputs['Color'], norm_map.inputs['Color'])
                            nt.links.new(norm_map.outputs['Normal'], bsdf.inputs['Normal'])
                        elif target_name != "Alpha":
                            socket_name = {"Emission": "Emission Color"}.get(target_name, target_name)
                            if bsdf.inputs.get(socket_name):
                                nt.links.new(tex_node.outputs['Color'], bsdf.inputs[socket_name])
                
                    # Assign the new, unique material to the object's slot
                    obj.material_slots[i].material = baked_mat
        # --- END OF THE FIX ---
    
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
        [DEFINITIVE V6 - CORRECTED CLEANUP]
        Handles all post-operation cleanup tasks. This version correctly references
        _worker_slots instead of the old _worker_pool.
        """
        global export_lock

        # --- 1. SHUTDOWN EXTERNAL PROCESSES ---
        # ---> THIS IS THE FIX: Use self._worker_slots, not self._worker_pool <---
        if hasattr(self, '_worker_slots') and self._worker_slots:
            logging.info(f"Shutting down {len(self._worker_slots)} worker process(es)...")
            # We iterate over the 'process' object within each slot dictionary
            for slot in self._worker_slots:
                worker = slot.get('process')
                if worker and worker.poll() is None:
                    try:
                        worker.terminate()
                    except Exception as e:
                        logging.warning(f"Could not terminate worker PID {worker.pid}: {e}")
            
            # Wait for them to terminate
            for slot in self._worker_slots:
                worker = slot.get('process')
                if worker and worker.poll() is None:
                    try:
                        worker.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        worker.kill()
        # ---> END OF FIX <---

        if hasattr(self, '_comm_threads'):
            for thread in self._comm_threads:
                if thread.is_alive():
                    thread.join(timeout=1)
            self._comm_threads.clear()
        
        # --- 2. RESTORE BLENDER SCENE STATE ---
        if self._export_data.get("normals_were_flipped"):
            objects_that_were_flipped = self._export_data.get("objects_for_export", [])
            if objects_that_were_flipped:
                logging.info("Restoring original normals for exported objects.")
                batch_flip_normals_optimized(objects_that_were_flipped, context)

        original_assignments = self._export_data.get("original_material_assignments", {})
        if original_assignments:
            logging.debug("Restoring original material assignments.")
            for obj_name, original_mats in original_assignments.items():
                obj = bpy.data.objects.get(obj_name)
                if obj and len(obj.material_slots) == len(original_mats):
                    for i, original_mat in enumerate(original_mats):
                        obj.material_slots[i].material = original_mat

        # --- 3. DELETE TEMPORARY BLENDER DATA ---
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
            if not os.path.exists(path_to_clean):
                continue
            try:
                if os.path.isdir(path_to_clean):
                    shutil.rmtree(path_to_clean)
                else:
                    os.remove(path_to_clean)
            except Exception as e:
                logging.warning(f"Could not remove temporary path '{path_to_clean}': {e}")
        # ---> START OF FIX: UNREGISTER CLEANED FILES <---
        # Clear the global list so the atexit handler doesn't try to delete them again.
        TEMP_FILES_FOR_ATEXIT_CLEANUP.clear()
        # ---> END OF FIX <---

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

def check_blend_file_in_prims(blend_name, context): # Added context
    addon_prefs = context.preferences.addons[__name__].preferences # Use context to get prefs
    try:
        server_url = addon_prefs.remix_server_url.rstrip('/')
        # Consider if filter_session_assets should be filter_session_prims
        get_url = f"{server_url}/assets/?selection=false&filter_session_assets=false&exists=true"
        headers = {'accept': 'application/lightspeed.remix.service+json; version=1.0'}

        logging.info(f"Fetching prims from: {get_url}")
        response = make_request_with_retries('GET', get_url, headers=headers, verify=addon_prefs.remix_verify_ssl)

        if not response or response.status_code != 200:
            logging.error(f"Failed to fetch prims from Remix server. Status: {response.status_code if response else 'No Response'}")
            return None, None

        data = response.json()
        # CORRECTED: Look for "prim_paths", fallback to "asset_paths"
        asset_or_prim_paths = data.get("prim_paths")
        if asset_or_prim_paths is None: # Check if key exists
            logging.warning("check_blend_file_in_prims: Key 'prim_paths' not found in server response, trying 'asset_paths' as fallback.")
            asset_or_prim_paths = data.get("asset_paths", [])
        
        logging.debug(f"Retrieved asset_or_prim_paths for check_blend_file_in_prims: {asset_or_prim_paths[:10]}...") # Log first few

        if addon_prefs.remix_use_custom_name and addon_prefs.remix_use_selection_only and addon_prefs.remix_base_obj_name:
            base_name = addon_prefs.remix_base_obj_name
            logging.debug(f"Using custom base OBJ name for prim search: {base_name}")
        else:
            base_name = extract_base_name(blend_name) # Assuming extract_base_name is correct
            logging.debug(f"Using blend file base name for prim search: {base_name}")

        for path in asset_or_prim_paths:
            segments = path.strip('/').split('/')
            # Check if any segment (typically the mesh name part) contains the base_name
            # This logic might need refinement depending on how specific the match needs to be.
            # Example: if base_name is "Test" and path is "/RootNode/meshes/Test_1/mesh"
            # segments could be ['RootNode', 'meshes', 'Test_1', 'mesh']
            # We'd want to check 'Test_1' against 'Test'
            path_lower = path.lower() # For case-insensitive comparison of the whole path
            base_name_lower = base_name.lower()

            # More targeted check: often the mesh ID is the 3rd segment if path starts with /
            # e.g. /RootNode/meshes/mesh_ID_or_Name
            # or 4th if it's /Project/AssetGroup/mesh_ID_or_Name
            # A simple "in" check for the base_name in the path string is a broad approach.
            if base_name_lower in path_lower: # General check
            # A more specific check might be:
            # if len(segments) > 2 and base_name_lower in segments[2].lower(): # Checks the typical mesh name slot
                logging.info(f"Prim with base name potentially found: {path}")
                # print(f"Prim with base name found: {path}") # Covered by logging

                prim_path_to_return = '/' + '/'.join(segments) # Reconstruct full path with leading slash

                reference_prim_path = None
                # Find the segment starting with 'ref_' to determine the reference prim
                for i, segment in enumerate(segments):
                    if segment.lower().startswith('ref_'):
                        reference_prim_path = '/' + '/'.join(segments[:i + 1])
                        break
                
                if reference_prim_path:
                    logging.info(f"Reference prim identified: {reference_prim_path} for matched path {prim_path_to_return}")
                    # print(f"Reference prim identified: {reference_prim_path}") # Covered by logging
                    return prim_path_to_return, reference_prim_path
                else:
                    # If no 'ref_' segment, but a match was found, what should be returned?
                    # The original code would continue the loop if no 'ref_' was found for a given path match.
                    # This means only paths that contain 'base_name' AND have a 'ref_' segment are considered.
                    logging.debug(f"Path '{path}' contained base name '{base_name}' but no 'ref_' segment found. Continuing search.")
                    # If any path matching base_name should be returned even without 'ref_', this logic needs change.
                    # For now, sticking to original intent: needs 'ref_'.

        logging.info(f"No reference prim found containing base name '{base_name}' AND a 'ref_' segment.")
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
        "Warning. If mesh names are the same, exporting will automatically replace the other mesh..."
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
        addon_prefs.remix_use_selection_only = False
        addon_prefs.remix_use_custom_name = False
        addon_prefs.remix_import_original_textures = False
        addon_prefs.remix_import_scale = 1.0
        addon_prefs.flip_faces_export = False
        addon_prefs.mirror_import = False
        addon_prefs.obj_export_forward_axis = 'NEGATIVE_Z'
        addon_prefs.obj_export_up_axis = 'Y'
        addon_prefs.remix_server_url = "http://localhost:8011/stagecraft"
        addon_prefs.remix_export_url = "http://localhost:8011/ingestcraft/mass-validator/queue"
        addon_prefs.remix_export_scale = 1.0
        addon_prefs.remix_preset = 'CUSTOM'
        addon_prefs.remix_verify_ssl = True
        addon_prefs.remix_import_original_textures = False
        addon_prefs.apply_modifiers = True

        self.report({'INFO'}, "Remix Ingestor options have been reset to default, except for the custom base OBJ name.")
        logging.info("Remix Ingestor options have been reset to default, except for the custom base OBJ name.")
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

class VIEW3D_PT_remix_ingestor(Panel):
    bl_label = "Remix Asset Ingestion"
    bl_idname = "VIEW3D_PT_remix_ingestor"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'Remix Ingestor'

    def draw(self, context):
        layout = self.layout
        addon_prefs = context.preferences.addons[__name__].preferences

        # --- NEW: Combined Dependency Check ---
        if not PSUTIL_INSTALLED or not PILLOW_INSTALLED:
            box = layout.box()
            box.label(text="Dependencies Required", icon='ERROR')
            
            if not PSUTIL_INSTALLED:
                col = box.column(align=True)
                col.label(text="'psutil' is needed for resource management.")
                op = col.operator("remix.install_dependency", text="Install psutil", icon='CONSOLE')
                op.dependency = 'psutil'

            if not PILLOW_INSTALLED:
                col = box.column(align=True)
                col.label(text="'Pillow' is needed for texture fixing.")
                op = col.operator("remix.install_dependency", text="Install Pillow", icon='CONSOLE')
                op.dependency = 'Pillow'

            if getattr(context.scene, 'remix_install_complete', False):
                 info_box = box.box()
                 info_box.label(text="Installation successful!", icon='CHECKMARK')
                 info_box.label(text="Please restart Blender now to apply.")
                 box.operator("remix.restart_blender", text="Save and Restart Blender", icon='RECOVER_LAST')
            
            return # Stop drawing the rest of the panel

        # --- Main Addon UI (only drawn if all dependencies are installed) ---
        presets_box = layout.box()
        presets_box.label(text="Presets", icon='SETTINGS')
        row = presets_box.row()
        row.prop(addon_prefs, "remix_preset", text="")

        export_box = layout.box()
        export_box.label(text="Export & Ingest", icon='EXPORT')
        export_box.prop(addon_prefs, "remix_ingest_directory", text="Ingest Directory")
        export_box.prop(addon_prefs, "remix_use_selection_only", text="Export Selected Objects Only")

        if addon_prefs.remix_use_selection_only:
            export_box.prop(addon_prefs, "remix_use_custom_name", text="Use Custom Name")
            if addon_prefs.remix_use_custom_name:
                base_name_box = export_box.box()
                base_name_box.label(text="Base OBJ Name", icon='FILE_BLEND')
                base_name_box.prop(addon_prefs, "remix_base_obj_name", text="")

        export_box.prop(addon_prefs, "remix_replace_stock_mesh", text="Replace Stock Mesh")
        export_box.prop(addon_prefs, "flip_faces_export", text="Flip Normals During Export")
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
        import_box.prop(addon_prefs, "mirror_import", text="Mirror on Import")
        import_box.prop(addon_prefs, "flip_normals_import", text="Flip Normals on Import")
        import_box.prop(addon_prefs, "remix_import_scale", text="Import Scale")
        import_box.prop(addon_prefs, "remix_import_original_textures", text="Import Original Textures")
        
        import_box.operator("object.import_usd_from_remix", text="Import from Remix")
        import_box.operator("object.import_captures", text="Import USD Captures")

        utilities_box = layout.box()
        utilities_box.label(text="Utilities", icon='TOOL_SETTINGS')
        utilities_box.operator("system.check_gpu_settings", text="Check GPU Settings", icon='SYSTEM')

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
]
     
      
      
def register():
    global BAKE_WORKER_PY
    log = logging.getLogger(__name__)

    # ################################################################## #
    # THIS IS THE FIRST CRITICAL CHANGE                                  #
    # Run the orphan cleanup routine every time the addon loads.         #
    check_dependencies()
    cleanup_orphan_directories()
    # ################################################################## #

    try:
        setup_logger()
        BAKE_WORKER_PY = os.path.join(os.path.dirname(os.path.realpath(__file__)), "remix_bake_worker.py")
        if not os.path.exists(BAKE_WORKER_PY):
            log.critical(f"Bake worker script 'remix_bake_worker.py' NOT FOUND at {BAKE_WORKER_PY}")

        for cls in classes:
            bpy.utils.register_class(cls)

        bpy.types.Scene.remix_custom_settings_backup = PointerProperty(type=CustomSettingsBackup)
        bpy.types.Scene.remix_asset_number = CollectionProperty(type=AssetNumberItem)
        bpy.types.Scene.remix_install_complete = BoolProperty(
            name="Remix Install Complete",
            description="Tracks if a dependency installation has been attempted.",
            default=False
        )
        
        # We can still keep the atexit handler for graceful shutdowns, but it's no longer the primary defense
        atexit.register(_kill_all_active_workers)
        log.info("Remix Ingestor addon registration complete with orphan process handler and startup cleanup.")
    except Exception as e:
        log.error(f"Addon registration failed: {e}", exc_info=True)
        raise

def unregister():
    log = logging.getLogger(__name__)

    # --- THIS IS THE FIX ---
    # First, gracefully shut down any workers that might be running
    # and clear the global registry. This effectively disables the atexit handler.
    _kill_all_active_workers()

    # The atexit documentation notes that unregistering can be problematic.
    # The safest method is to ensure the registered function does nothing
    # after the module is unlinked, which is what clearing the list achieves.
    # For good measure, we can try to unregister it, but we'll wrap it in a
    # try...except block as it's not guaranteed to exist or work in all
    # Blender shutdown scenarios.
    try:
        import atexit
        # This is a less-common function and was only added in Python 3.9
        # so we check for its existence before calling.
        if hasattr(atexit, 'unregister'):
            atexit.unregister(_kill_all_active_workers)
            log.info("atexit handler for orphan processes has been unregistered.")
    except Exception as e:
        log.warning(f"Could not explicitly unregister atexit handler: {e}")
    # --- END OF FIX ---

    for cls in reversed(classes):
        try:
            bpy.utils.unregister_class(cls)
        except RuntimeError:
            pass
    try:
        del bpy.types.Scene.remix_asset_number
        del bpy.types.Scene.remix_custom_settings_backup
        del bpy.types.Scene.remix_install_complete
    except (AttributeError, TypeError):
        pass
        
    log.info("Remix Ingestor addon unregistered.")

if __name__ == "__main__":
    register()
