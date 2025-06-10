bl_info = { 
    "name": "Remix Asset Ingestion",
    "blender": (4, 2, 0),
    "category": "Helper",
    "version": (3, 3, 0),
    "author": "Frisser :)",
    "description": "Export mesh assets as OBJ, ingest into Remix with versioning, and handle multiple textures.",
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
import logging
import bmesh
import collections
from pxr import Usd, Sdf
from bpy.props import BoolProperty, StringProperty, CollectionProperty, IntProperty, EnumProperty, FloatProperty
from bpy.types import Operator, Panel, PropertyGroup, AddonPreferences
import bpy_extras.io_utils
import urllib.parse
import subprocess
from pathlib import Path
from mathutils import Matrix
import math

# Initialize global variables
log_file_path = ""
export_lock = False
remix_import_lock = False
conversion_count = 0
is_applying_preset = False

class RemixIngestorPreferences(AddonPreferences):
    bl_idname = __name__

    apply_modifiers: BoolProperty(
        name="Apply Modifiers",
        description="Apply modifiers before exporting OBJ files",
        default=True
    )

    remix_server_url: StringProperty(
        name="Server URL",
        description="URL of the Remix server (e.g., http://localhost:8011/stagecraft).",
        default="http://localhost:8011/stagecraft",
        subtype='NONE'
    )
    remix_export_url: StringProperty(
        name="Export API URL",
        description="URL of the Export API (e.g., http://localhost:8011/ingestcraft/mass-validator/queue).",
        default="http://localhost:8011/ingestcraft/mass-validator/queue",
        subtype='NONE'
    )
    remix_verify_ssl: BoolProperty(
        name="Verify SSL",
        description="Verify SSL certificates when connecting to the server",
        default=True
    )
    remix_use_selection_only: BoolProperty(
        name="Export Selected Objects Only",
        description="Export only selected objects",
        default=False
    )
    flip_normals_import: BoolProperty(
        name="Flip Normals During Import",
        description="When checked, normals will be flipped during import.",
        default=False
    )
    remix_ingest_directory: StringProperty(
        name="Ingest Directory",
        description="Directory on the server to ingest assets and textures (e.g., /ProjectFolder/Assets)",
        default="/ProjectFolder/Assets",
        subtype='DIR_PATH'
    )
    flip_faces_export: BoolProperty(
        name="Flip Normals During Export",
        description="When checked, normals will be flipped during export.",
        default=False
    )
    obj_export_forward_axis: EnumProperty(
        name="Forward Axis",
        description="Choose the forward axis for OBJ export",
        items=[
            ('X', 'X', "Forward along X-axis"),
            ('NEGATIVE_X', 'Negative X', "Forward along negative X-axis"),
            ('Y', 'Y', "Forward along Y-axis"),
            ('NEGATIVE_Y', 'Negative Y', "Forward along negative Y-axis"),
            ('Z', 'Z', "Forward along Z-axis"),
            ('NEGATIVE_Z', 'Negative Z', "Forward along negative Z-axis"),
        ],
        default='NEGATIVE_Z'
    )
    obj_export_up_axis: EnumProperty(
        name="Up Axis",
        description="Choose the up axis for OBJ export",
        items=[
            ('X', 'X', "Up along X-axis"),
            ('NEGATIVE_X', 'Negative X', "Up along negative X-axis"),
            ('Y', 'Y', "Up along Y-axis"),
            ('NEGATIVE_Y', 'Negative Y', "Up along negative Y-axis"),
            ('Z', 'Z', "Up along Z-axis"),
            ('NEGATIVE_Z', 'Negative Z', "Up along negative Z-axis"),
        ],
        default='Y'
    )
    remix_export_scale: FloatProperty(
        name="Export Scale",
        description="Scale factor for exporting OBJ",
        default=1.0,
        min=-10000.0,
        max=10000.0
    )
    remix_preset: EnumProperty(
        name="Presets",
        description="Select preset configurations for export and import settings",
        items=[
            ('CUSTOM', "Custom", "Use custom settings"),
            ('UNREAL_ENGINE', "Unreal Engine", "Apply settings optimized for Unreal Engine")
        ],
        default='CUSTOM'
    )
    remix_base_obj_name: StringProperty(
        name="Base OBJ Name",
        description="Base name for the exported OBJ files",
        default="exported_object",
        subtype='NONE'
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
    remix_use_custom_name: BoolProperty(
        name="Use Custom Name",
        description="Use a custom base name for exported OBJ files",
        default=False
    )
    remix_replace_stock_mesh: BoolProperty(
        name="Replace Stock Mesh",
        description="Replace the selected stock mesh in Remix",
        default=False
    )
    remix_show_info: BoolProperty(
        name="Show Information",
        description="Show additional information in the panel",
        default=False
    )
    mirror_import: BoolProperty(
        name="Mirror on Import",
        description="Mirror objects along the X-axis during import",
        default=False
    )

    # CORRECTED: Default value for usd_import_up_axis changed to 'Z' to have a valid default pair.
    # A common setup is Z-Up, Y-Forward.
    usd_import_forward_axis: EnumProperty( # New Property
        name="USD Import Forward Axis",
        description="Choose the forward axis for USD import. This tells Blender how to interpret the source USD's forward direction.",
        items=[
            ('X', 'X Positive', "Interpret source Forward as X Positive"),
            ('Y', 'Y Positive', "Interpret source Forward as Y Positive"),
            ('Z', 'Z Positive', "Interpret source Forward as Z Positive"),
            ('NEGATIVE_X', 'X Negative', "Interpret source Forward as X Negative"),
            ('NEGATIVE_Y', 'Y Negative', "Interpret source Forward as Y Negative"),
            ('NEGATIVE_Z', 'Z Negative', "Interpret source Forward as Z Negative"),
        ],
        default='Y' 
    )
    usd_import_up_axis: EnumProperty(
        name="USD Up Axis",
        description="Choose the up axis for USD import. This tells Blender how to interpret the source USD's up direction.",
        items=[('X','X Positive',''),('Y','Y Positive',''),('Z','Z Positive',''),('-X','X Negative',''),('-Y','Y Negative',''),('-Z','Z Negative','')],
        default='Z', # CORRECTED: Changed default from 'Y' to 'Z'
    )

    # ------------------------------------------------------------------
    # Added for Substance-Painter workflow
    # ------------------------------------------------------------------
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
        layout.prop(self, "apply_modifiers", text="Apply Modifiers")

class AssetNumberItem(PropertyGroup):
    blend_name: StringProperty(name="Blend File Name")
    asset_number: IntProperty(name="Asset Number", default=1)


class CustomSettingsBackup(PropertyGroup):
    obj_export_forward_axis: EnumProperty(
        name="Forward Axis",
        items=[
            ('X', 'X', "Forward along X-axis"),
            ('NEGATIVE_X', 'Negative X', "Forward along negative X-axis"),
            ('Y', 'Y', "Forward along Y-axis"),
            ('NEGATIVE_Y', 'Negative Y', "Forward along negative Y-axis"),
            ('Z', 'Z', "Forward along Z-axis"),
            ('NEGATIVE_Z', 'Negative Z', "Forward along negative Z-axis"),
        ],
        default='NEGATIVE_Z',
    )
    obj_export_up_axis: EnumProperty(
        name="Up Axis",
        items=[
            ('X', 'X', "Up along X-axis"),
            ('NEGATIVE_X', 'Negative X', "Up along negative X-axis"),
            ('Y', 'Y', "Up along Y-axis"),
            ('NEGATIVE_Y', 'Negative Y', "Up along negative Y-axis"),
            ('Z', 'Z', "Up along Z-axis"),
            ('NEGATIVE_Z', 'Negative Z', "Up along negative Z-axis"),
        ],
        default='Y',
    )
    flip_faces_export: BoolProperty(
        name="Flip Normals During Export",
        default=False,
    )
    mirror_import: BoolProperty(
        name="Mirror on Import",
        default=False,
    )
    remix_export_scale: FloatProperty(
        name="Export Scale",
        default=1.0,
        min=-10000.0,
        max=10000.0
    )
    remix_use_selection_only: BoolProperty(
        name="Export Selected Objects Only",
        default=False,
    )
    remix_ingest_directory: StringProperty(
        name="Ingest Directory",
        default="/ProjectFolder/Assets",
        subtype='DIR_PATH'
    )
    remix_verify_ssl: BoolProperty(
        name="Verify SSL",
        default=True
    )
    remix_import_original_textures: BoolProperty(
        name="Import Original Textures",
        default=False
    )


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


def make_request_with_retries(method, url, headers=None, json_payload=None, retries=3, delay=5, **kwargs):
    for attempt in range(1, retries + 1):
        try:
            logging.debug(f"Attempt {attempt}: {method} {url}")
            response = requests.request(method, url, headers=headers, json=json_payload, timeout=60, **kwargs)
            logging.debug(f"Response: {response.status_code} - {response.text}")
            if response.status_code in [200, 201, 204]:
                return response
            else:
                logging.warning(f"Attempt {attempt} failed with status {response.status_code}")
        except requests.exceptions.RequestException as e:
            logging.warning(f"Attempt {attempt} encountered exception: {e}")
        if attempt < retries:
            time.sleep(delay)
    logging.error(f"All {retries} attempts failed for {method} {url}")
    return None


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
    try:
        # Ensure addon_prefs are fetched correctly if needed, or pass context
        # For simplicity here, assuming addon_prefs can be accessed or are passed if this were a class method
        # If this is a global function, it might need context passed to get addon_prefs.
        # For now, let's assume the URL is constructed directly as per its original likely intent.
        # This might need access to `addon_prefs.remix_server_url` and `addon_prefs.remix_verify_ssl`
        # For a standalone function, these would need to be passed or accessed via context.
        # I'll replicate the direct URL construction for now, but this is a point of attention for context.
        
        # To make this function testable and robust, it should ideally take context
        # and get preferences from there.
        # However, sticking to minimal changes to fix the immediate issue:
        
        # Placeholder for addon_prefs - IN A REAL SCENARIO, THIS NEEDS PROPER ACCESS VIA CONTEXT
        class MockAddonPrefs:
            def __init__(self):
                self.remix_server_url = "http://localhost:8011/stagecraft" # Default or fetched
                self.remix_verify_ssl = True # Default or fetched

        # If context is available:
        # addon_prefs = context.preferences.addons[__name__].preferences
        # url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/?selection=true&filter_session_assets=false&exists=true"
        # verify_ssl = addon_prefs.remix_verify_ssl

        # Using placeholder for now based on common usage in the script
        # THIS IS A SIMPLIFICATION FOR THE SAKE OF THE EXAMPLE CORRECTION.
        # THE ORIGINAL FUNCTION MIGHT HAVE HAD A WAY TO GET ADDON_PREFS.
        # If it's called from an operator, `context.preferences.addons[__name__].preferences` is the way.
        
        # Assuming this function is called from within an operator method where 'context' is available
        # If not, it needs 'context' as an argument. For this example, I'll assume it can get prefs.
        # This part is tricky as the original function signature wasn't shown in the error snippet.
        # Let's assume it's called from a context where addon_prefs are accessible like others.
        # This typically means it's a method of a class that has self.report, or context is passed.
        # Given its usage, it's likely called from an Operator.

        # --- THIS IS A GUESS - THE FUNCTION NEEDS CONTEXT TO GET PREFERENCES ---
        # Fallback to a hardcoded URL if context isn't available, which is not ideal
        # but shows the core fix. A better solution involves passing context.
        server_url_base = "http://localhost:8011/stagecraft"
        verify_ssl_cert = True
        
        # Attempt to get preferences if context is available in the scope this function is called from
        # This is a common pattern in Blender addons.
        try:
            context = bpy.context # Try to get global context if available
            addon_prefs = context.preferences.addons[__name__].preferences
            server_url_base = addon_prefs.remix_server_url.rstrip('/')
            verify_ssl_cert = addon_prefs.remix_verify_ssl
            url = f"{server_url_base}/assets/?selection=true&filter_session_assets=false&exists=true"
             # Consider if filter_session_assets should be filter_session_prims
        except (AttributeError, KeyError):
            logging.warning("fetch_selected_mesh_prim_paths: Could not get addon_prefs from context. Using default URL.")
            url = "http://localhost:8011/stagecraft/assets/?selection=true&filter_session_assets=false&exists=true"
            # url = "http://localhost:8011/stagecraft/assets/?selection=true&filter_session_prims=false&exists=true" # Potential change
        # --- END GUESS ---

        headers = {'accept': 'application/lightspeed.remix.service+json; version=1.0'}
        response = make_request_with_retries(
            'GET',
            url,
            headers=headers,
            verify=verify_ssl_cert # Use fetched or default
        )
        if not response or response.status_code != 200:
            logging.error(f"Failed to fetch selected mesh prim paths. Status: {response.status_code if response else 'No Response'}")
            # print("Failed to fetch selected mesh prim paths.") # Covered by logging
            return []

        data = response.json()
        # CORRECTED: Look for "prim_paths", fallback to "asset_paths"
        asset_or_prim_paths = data.get("prim_paths")
        if asset_or_prim_paths is None: # Check if key exists, even if list is empty
            logging.warning("fetch_selected_mesh_prim_paths: Key 'prim_paths' not found in server response, trying 'asset_paths' as fallback.")
            asset_or_prim_paths = data.get("asset_paths", [])
        
        selected_meshes = [path for path in asset_or_prim_paths if "/meshes/" in path.lower()]
        logging.info(f"Selected mesh prim paths: {selected_meshes}")
        # print(f"Selected mesh prim paths: {selected_meshes}") # Covered by logging
        return [ensure_single_leading_slash(p.rstrip('/')) for p in selected_meshes]
    except Exception as e:
        logging.error(f"Error fetching selected mesh prim paths: {e}", exc_info=True)
        # print(f"Error fetching selected mesh prim paths: {e}") # Covered by logging
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
    
def handle_height_textures(context, reference_prim, exported_objects=None):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        logging.info(f"Starting height texture processing for reference_prim: {reference_prim}")
        
        if exported_objects is not None:
            mesh_objects = [obj for obj in exported_objects if obj.type == 'MESH']
        else:
            # Fallback: if no specific exported_objects, process selected or all scene meshes
            # This part might need adjustment based on whether this function is ONLY for post-export
            # or also for general height texture handling. Assuming post-export for now.
            if context.selected_objects and addon_prefs.remix_use_selection_only:
                 mesh_objects = [obj for obj in context.selected_objects if obj.type == 'MESH']
            else:
                 mesh_objects = [obj for obj in context.scene.objects if obj.type == 'MESH']


        used_materials = set()
        for obj in mesh_objects:
            for slot in obj.material_slots:
                if slot.material:
                    used_materials.add(slot.material)

        height_textures_to_process = [] # Stores (material_name, texture_file_path)
        for mat in used_materials:
            if not mat.use_nodes or not mat.node_tree:
                continue
            for node in mat.node_tree.nodes:
                # Simplified: Check for Displacement or Bump nodes
                # This could be made more robust to find any image texture intended for height/displacement
                if node.type in {'DISPLACEMENT', 'BUMP'}: # Check typical nodes
                    # Find linked image texture to the 'Height' or 'Normal' input
                    # For Displacement node, it's 'Height'. For Bump, it's also 'Height'.
                    # If Bump uses a Normal Map node, that's a different path (not height texture directly)
                    height_input_socket_name = 'Height' # Common for both
                    if node.type == 'BUMP' and not node.inputs.get('Height').is_linked and node.inputs.get('Normal').is_linked:
                        # If Bump node's Height is not linked, but Normal is, it might be fed by a Normal Map node.
                        # This function is for raw height textures, so skip this case for now.
                        # Or, trace back from Normal input if logic is to handle normal maps too.
                        # For now, assuming direct height texture input.
                        pass

                    height_input = node.inputs.get(height_input_socket_name)
                    if height_input and height_input.is_linked:
                        source_node = height_input.links[0].from_node
                        if source_node.type == 'TEX_IMAGE' and source_node.image:
                            tex_path = bpy.path.abspath(source_node.image.filepath).replace('\\', '/')
                            if os.path.exists(tex_path):
                                # Only add if not already scheduled for this material (though material loop should handle it)
                                if not any(ht[0] == mat.name for ht in height_textures_to_process):
                                     height_textures_to_process.append((mat.name, tex_path))
                                logging.info(f"Found height texture '{tex_path}' for material '{mat.name}' via node '{node.name}'.")
                            else:
                                logging.warning(f"Height texture path '{tex_path}' for material '{mat.name}' does not exist.")
        
        if not height_textures_to_process:
            logging.info("No height textures found linked to Displacement/Bump nodes for processing.")
            return {'FINISHED'}

        ingest_dir_server = addon_prefs.remix_ingest_directory # This is server path
        # TextureImporter in payload uses server paths.
        # The 'textures_subdir' on the server is where TextureImporter will place processed textures.
        server_textures_output_dir = os.path.join(ingest_dir_server, "textures").replace('\\', '/')
        # No need to os.makedirs for server_textures_output_dir here, server handles it.

        base_api_url = addon_prefs.remix_export_url.rstrip('/') # For mass-validator/queue

        for material_name, local_tex_file_path in height_textures_to_process:
            logging.info(f"Processing height texture for material '{material_name}': {local_tex_file_path}")

            # STEP 1: Ingest the texture file (via TextureImporter on the server)
            # The input_files should be the *local path* to the texture that the server can access
            # or that the payload implies will be uploaded/found by the server.
            # The current TextureImporter payload in the script implies server-side access or direct provision.
            # Assuming local_tex_file_path is accessible or handled by the ingestcraft API.
            ingest_payload = {
                "executor": 1, "name": "Material(s)",
                "context_plugin": {
                    "name": "TextureImporter",
                    "data": {
                        "context_name": "ingestcraft",
                        "input_files": [[local_tex_file_path, "HEIGHT"]], # Texture path and its type
                        "output_directory": server_textures_output_dir, # Server path for output
                        "allow_empty_input_files_list": True,
                        "data_flows": [{"name": "InOutData", "push_input_data": True}],
                        "hide_context_ui": True, "create_context_if_not_exist": True,
                        "expose_mass_ui": True, "cook_mass_template": True
                    }
                },
                "check_plugins": [ # Simplified, use your detailed check_plugins
                    {"name": "MaterialShaders", "selector_plugins": [{"name": "AllMaterials", "data": {}}], "data": {"shader_subidentifiers": {"AperturePBR_Opacity": ".*"}}, "stop_if_fix_failed": True, "context_plugin": {"name": "CurrentStage", "data": {}}},
                    {"name": "ConvertToOctahedral", "selector_plugins": [{"name": "AllShaders", "data": {}}], "resultor_plugins": [{"name": "FileCleanup", "data": {"channel": "cleanup_files_normal", "cleanup_output": False}}], "data": {"data_flows": [{"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"}]}, "stop_if_fix_failed": True, "context_plugin": {"name": "CurrentStage", "data": {}}},
                    {"name": "ConvertToDDS", "selector_plugins": [{"name": "AllShaders", "data": {}}], "resultor_plugins": [{"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}}], "data": {"data_flows": [{"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"}, {"name": "InOutData", "push_output_data": True, "channel": "write_metadata"}, {"name": "InOutData", "push_output_data": True, "channel": "ingestion_output"}]}, "stop_if_fix_failed": True, "context_plugin": {"name": "CurrentStage", "data": {}}},
                    {"name": "MassTexturePreview", "selector_plugins": [{"name": "Nothing", "data": {}}], "data": {"expose_mass_queue_action_ui": True}, "stop_if_fix_failed": True, "context_plugin": {"name": "CurrentStage", "data": {}}}
                ],
                "resultor_plugins": [{"name": "FileMetadataWritter", "data": {"channel": "write_metadata"}}]
            }
            
            logging.debug(f"Texture ingest payload for '{material_name}': {ingest_payload}")
            ingest_response = make_request_with_retries(
                'POST', f"{base_api_url}/material", # Endpoint for material/texture ingestion
                json_payload=ingest_payload, verify=addon_prefs.remix_verify_ssl
            )

            if not ingest_response or ingest_response.status_code not in [200, 201, 204]:
                logging.error(f"Failed to ingest height texture for material '{material_name}'. Status: {ingest_response.status_code if ingest_response else 'No Response'}, Response: {ingest_response.text if ingest_response else 'N/A'}")
                return {'CANCELLED'} # Or continue to next texture? For now, fail hard.
            
            ingest_data = ingest_response.json()
            final_ingested_texture_path_on_server = None
            
            # Parse ingest_data to find the path of the *processed* texture (e.g., the .dds or .h.rtex.dds)
            # This logic needs to correctly navigate the 'completed_schemas' as in upload_to_api
            completed_schemas = ingest_data.get("completed_schemas", [])
            if completed_schemas:
                # Look in data_flows of the ConvertToDDS plugin for the output path
                for schema in completed_schemas:
                    for plugin_run in schema.get("check_plugins", []):
                        if plugin_run.get("name") == "ConvertToDDS":
                            plugin_data = plugin_run.get("data", {})
                            for flow in plugin_data.get("data_flows", []):
                                if flow.get("channel") == "ingestion_output" and flow.get("push_output_data") and flow.get("output_data"):
                                    # output_data is a list of paths
                                    for out_path in flow["output_data"]:
                                        if isinstance(out_path, str) and (out_path.lower().endswith(".dds") or out_path.lower().endswith(".rtex.dds")):
                                            # Heuristic: prefer .h.rtex.dds if multiple DDS outputs
                                            if ".h.rtex.dds" in out_path.lower() or final_ingested_texture_path_on_server is None:
                                                final_ingested_texture_path_on_server = out_path.replace('\\','/')
                                            if ".h.rtex.dds" in out_path.lower(): # Prioritize this exact match
                                                break 
                                    if final_ingested_texture_path_on_server and ".h.rtex.dds" in final_ingested_texture_path_on_server.lower():
                                        break 
                            if final_ingested_texture_path_on_server and ".h.rtex.dds" in final_ingested_texture_path_on_server.lower():
                                break
                    if final_ingested_texture_path_on_server and ".h.rtex.dds" in final_ingested_texture_path_on_server.lower():
                        break
            
            if not final_ingested_texture_path_on_server:
                logging.error(f"Failed to find final ingested texture path for material '{material_name}' from TextureImporter response. Full response: {ingest_data}")
                return {'CANCELLED'}
            logging.info(f"Successfully ingested height texture for material '{material_name}'. Server path: {final_ingested_texture_path_on_server}")

            # STEP 2: Construct the material prim asset path dynamically
            remix_mat_name = blender_mat_to_remix(material_name) # Sanitize material name
            # 'reference_prim' is the path to the parent of XForms/World, e.g., /RootNode/meshes/mesh_ID/ref_ID
            material_prim_on_stage = f"{reference_prim}/XForms/World/Looks/{remix_mat_name}"
            encoded_material_prim = urllib.parse.quote(material_prim_on_stage, safe='')
            logging.debug(f"Constructed material prim path on stage: {material_prim_on_stage}")

            # STEP 3: Fetch the list of shader input connections for this material prim
            stagecraft_api_url_base = addon_prefs.remix_server_url.rstrip('/') # For /assets/ and /textures/
            textures_on_material_url = f"{stagecraft_api_url_base}/assets/{encoded_material_prim}/textures"
            
            textures_response = make_request_with_retries(
                'GET', textures_on_material_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )
            if not textures_response or textures_response.status_code != 200:
                logging.error(f"Failed to retrieve texture connections for material prim: {material_prim_on_stage}. Status: {textures_response.status_code if textures_response else 'N/A'}")
                return {'CANCELLED'}
            
            textures_data = textures_response.json()
            shader_core_input_prim = None # This will be like /.../Shader.inputs:diffuse_texture
            textures_list = textures_data.get("textures", []) # List of [input_prim_path, texture_asset_path]
            if textures_list and len(textures_list) > 0 and textures_list[0] and isinstance(textures_list[0], list) and len(textures_list[0]) > 0:
                shader_core_input_prim = textures_list[0][0] # Take the first available input prim as a representative of the shader
            else:
                logging.error(f"No shader input connections found in textures response for material: {material_prim_on_stage}. Response: {textures_data}")
                return {'CANCELLED'}
            logging.debug(f"Representative shader core input prim for material '{material_name}': {shader_core_input_prim}")

            # STEP 4: Get the specific 'HEIGHT' shader input prim path using the representative input prim
            encoded_shader_core_input = urllib.parse.quote(shader_core_input_prim, safe='')
            height_input_query_url = f"{stagecraft_api_url_base}/textures/{encoded_shader_core_input}/material/inputs?texture_type=HEIGHT"
            
            height_input_prim_response = make_request_with_retries(
                'GET', height_input_query_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )
            if not height_input_prim_response or height_input_prim_response.status_code != 200:
                logging.error(f"Failed to fetch 'HEIGHT' type shader input prim using representative '{shader_core_input_prim}'. Status: {height_input_prim_response.status_code if height_input_prim_response else 'N/A'}")
                return {'CANCELLED'}
            
            height_input_data = height_input_prim_response.json()
            # CORRECTED: Expect "prim_paths" key
            height_shader_input_prim_paths = height_input_data.get("prim_paths", []) 
            
            if not height_shader_input_prim_paths or not height_shader_input_prim_paths[0]:
                logging.error(f"No height shader input prim path returned in response for material '{material_name}'. Query URL: {height_input_query_url}, Response: {height_input_data}")
                return {'CANCELLED'} # Fail if no height input target
            
            height_shader_input_target_prim = height_shader_input_prim_paths[0] # This is the actual target like /.../Shader.inputs:height_texture
            logging.info(f"Target prim for height texture assignment of material '{material_name}': {height_shader_input_target_prim}")

            # STEP 5: Update the shader input with the ingested height texture (via PUT to /textures/)
            # The /textures/ endpoint takes a list of [target_shader_input_prim, texture_asset_path]
            update_texture_connection_url = f"{stagecraft_api_url_base}/textures/" 
            put_payload = {
                "force": False, # or True, depending on desired behavior
                "textures": [
                    [height_shader_input_target_prim, final_ingested_texture_path_on_server]
                ]
            }
            logging.debug(f"PUT payload to connect height texture: {put_payload} to URL: {update_texture_connection_url}")
            
            put_response = make_request_with_retries(
                'PUT', update_texture_connection_url, json_payload=put_payload,
                headers={
                    "accept": "application/lightspeed.remix.service+json; version=1.0",
                    "Content-Type": "application/lightspeed.remix.service+json; version=1.0"
                },
                verify=addon_prefs.remix_verify_ssl
            )
            if not put_response or put_response.status_code not in [200, 201, 204]:
                logging.error(f"Failed to update shader input with ingested height texture for material '{material_name}'. Target prim: {height_shader_input_target_prim}, Texture: {final_ingested_texture_path_on_server}. Status: {put_response.status_code if put_response else 'N/A'}, Response: {put_response.text if put_response else 'N/A'}")
                return {'CANCELLED'}

            logging.info(f"Successfully updated height texture for material '{material_name}' using prim: {height_shader_input_target_prim} with texture: {final_ingested_texture_path_on_server}")

        logging.info("Height texture processing for all materials completed successfully.")
        return {'FINISHED'}

    except Exception as e:
        logging.error(f"Error handling height textures: {e}", exc_info=True)
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
  Flips normals for a list of mesh objects in a batch using bpy.ops.
  Assumes context.scene and context.view_layer are set correctly for the objects.
  """
  if not meshes_to_flip:
    logging.debug("Batch flip normals: No meshes to flip.")
    return

  logging.info(f"Batch flip normals: Preparing to flip {len(meshes_to_flip)} meshes.")

  # Store original state
  original_active_object = context.view_layer.objects.active
  original_selected_objects = list(context.selected_objects) # Make a copy
 
  # Determine original mode more robustly
  original_mode = 'OBJECT' # Default
  if context.object and hasattr(context.object, 'mode'):
    original_mode = context.object.mode
  elif context.mode: # Fallback for older Blender or different contexts
    original_mode = context.mode
 
  logging.debug(f"Batch flip normals: Original mode: {original_mode}, Active: {original_active_object.name if original_active_object else 'None'}, Selected: {len(original_selected_objects)}")

  try:
    # --- 1. Ensure OBJECT mode for reliable selection and active object setting ---
    if context.mode != 'OBJECT':
      can_set_object_mode = True
      if not bpy.ops.object.mode_set.poll():
        # If polling fails, it might be due to no active object suitable for the current mode.
        # Try to set a temporary active object from the scene if one exists.
        if not context.view_layer.objects.active and context.scene.objects:
          # Pick any object, preferably not one we are about to process if possible,
          # but any valid object will do to allow mode_set.
          temp_active = next((obj for obj in context.scene.objects if obj.type in {'MESH', 'EMPTY', 'LIGHT', 'CAMERA'}), None)
          if temp_active and temp_active.name in context.view_layer.objects:
            context.view_layer.objects.active = temp_active
          else: # If no suitable temp active can be found
            can_set_object_mode = False
        elif not context.view_layer.objects.active : # No scene objects at all
          can_set_object_mode = False


      if can_set_object_mode and bpy.ops.object.mode_set.poll():
        bpy.ops.object.mode_set(mode='OBJECT')
        logging.debug("Batch flip normals: Switched to OBJECT mode for setup.")
      elif context.mode != 'OBJECT': # If still not in object mode
        logging.warning("Batch flip normals: Could not switch to OBJECT mode for setup. Aborting flip.")
        return # Cannot proceed reliably

    # --- 2. Deselect all and select the target meshes ---
    if bpy.ops.object.select_all.poll():
      bpy.ops.object.select_all(action='DESELECT')

    actually_selected_meshes = []
    for mesh_obj in meshes_to_flip:
      if mesh_obj and mesh_obj.name in context.view_layer.objects and mesh_obj.type == 'MESH':
        try:
          mesh_obj.select_set(True)
          actually_selected_meshes.append(mesh_obj)
        except RuntimeError as e:
          logging.warning(f"Batch flip normals: Could not select mesh {mesh_obj.name}: {e}")
      elif not mesh_obj:
        logging.warning("Batch flip normals: Encountered a None object in meshes_to_flip list.")
      else:
        logging.warning(f"Batch flip normals: Mesh {mesh_obj.name} (type: {mesh_obj.type}) not in current view layer or not a MESH. Skipping.")
   
    if not actually_selected_meshes:
      logging.info("Batch flip normals: No valid meshes were selected for flipping from the provided list.")
      return

    # --- 3. Set Active Object (required for mode_set to EDIT) ---
    # Ensure the active object is one of the selected meshes
    if context.view_layer.objects.active not in actually_selected_meshes:
      context.view_layer.objects.active = actually_selected_meshes[0]
   
    logging.debug(f"Batch flip normals: Selected {len(actually_selected_meshes)} meshes. Active for EDIT mode: {context.view_layer.objects.active.name if context.view_layer.objects.active else 'None'}")

    # --- 4. Switch to EDIT mode and perform operations ---
    if bpy.ops.object.mode_set.poll():
      bpy.ops.object.mode_set(mode='EDIT')
      logging.debug("Batch flip normals: Switched to EDIT mode.")
    else:
      logging.warning("Batch flip normals: Cannot switch to EDIT mode (poll failed). Aborting flip.")
      # Attempt to restore object mode before returning as we might have changed selections
      if context.mode != 'OBJECT' and bpy.ops.object.mode_set.poll():
        bpy.ops.object.mode_set(mode='OBJECT')
      return

    if context.mode == 'EDIT':
      bpy.ops.mesh.select_all(action='SELECT') # Select all geometry of all selected objects
      bpy.ops.mesh.flip_normals()
      logging.info(f"Batch flip normals: Flipped normals for {len(actually_selected_meshes)} meshes.")
     
      # Switch back to OBJECT mode
      if bpy.ops.object.mode_set.poll():
        bpy.ops.object.mode_set(mode='OBJECT')
        logging.debug("Batch flip normals: Switched back to OBJECT mode.")
      else:
        logging.warning("Batch flip normals: Could not switch back to OBJECT mode after flipping (poll failed).")
    else:
      logging.warning("Batch flip normals: Not in EDIT mode after attempting switch. Normals not flipped.")

  except Exception as e:
    logging.error(f"Batch flip normals: Error during main operation: {e}", exc_info=True)
    # Ensure we try to get back to object mode in case of error during edit mode ops
    if context.mode == 'EDIT':
      try:
        if bpy.ops.object.mode_set.poll():
          bpy.ops.object.mode_set(mode='OBJECT')
      except Exception as e_restore_on_error:
        logging.error(f"Batch flip normals: Error trying to restore OBJECT mode after main error: {e_restore_on_error}")
  finally:
    # --- 5. Restore original selection and mode ---
    logging.debug("Batch flip normals: Entering finally block for state restoration.")
    try:
      # Ensure we are in OBJECT mode before restoring selection and original_active_object
      if context.mode != 'OBJECT':
        if bpy.ops.object.mode_set.poll():
          bpy.ops.object.mode_set(mode='OBJECT')
        else: # If we can't get to object mode, further restoration might be unstable
          logging.warning("Batch flip normals (finally): Could not ensure OBJECT mode. State restoration might be incomplete.")
     
      # Deselect all current selections (made by this function)
      if bpy.ops.object.select_all.poll():
        bpy.ops.object.select_all(action='DESELECT')

      # Reselect original objects
      for obj in original_selected_objects:
        if obj and obj.name in context.view_layer.objects: # Check if obj still exists and is in layer
          try:
            obj.select_set(True)
          except RuntimeError as e_reselect:
            logging.warning(f"Batch flip normals (finally): Could not re-select original object '{obj.name}': {e_reselect}")
     
      # Restore active object if it still exists and is in the current view layer
      if original_active_object and original_active_object.name in context.view_layer.objects:
        context.view_layer.objects.active = original_active_object
      elif context.selected_objects: # If original active is gone/invalid, try setting to one of the reselected.
        context.view_layer.objects.active = context.selected_objects[0]
      else: # If nothing is selected (e.g. original selection was empty or objects deleted)
        context.view_layer.objects.active = None
     
      logging.debug(f"Batch flip normals (finally): Restored active to: {context.view_layer.objects.active.name if context.view_layer.objects.active else 'None'}, Selected count: {len(context.selected_objects)}")

      # Restore original mode (only if it was not OBJECT and conditions allow)
      if original_mode != 'OBJECT' and context.mode == 'OBJECT':
        can_restore_original_mode = False
        if original_mode == 'EDIT': # Edit mode needs an active mesh/curve etc.
          if context.view_layer.objects.active and context.view_layer.objects.active.type in {'MESH', 'CURVE', 'SURFACE', 'FONT', 'META', 'ARMATURE'}: # Armature for edit bones
            can_restore_original_mode = True
        elif original_mode in {'POSE', 'SCULPT', 'VERTEX_PAINT', 'WEIGHT_PAINT', 'TEXTURE_PAINT'}: # These modes also usually need a suitable active object
          if context.view_layer.objects.active: # Check if active object is suitable might be more complex here, basic check for now
            can_restore_original_mode = True
       
        if can_restore_original_mode and bpy.ops.object.mode_set.poll():
          try:
            bpy.ops.object.mode_set(mode=original_mode)
            logging.debug(f"Batch flip normals (finally): Restored original mode to '{original_mode}'.")
          except RuntimeError as e_mode_restore:
            logging.warning(f"Batch flip normals (finally): Could not restore original mode '{original_mode}': {e_mode_restore}")
        elif context.mode != original_mode : # If we couldn't restore
          logging.warning(f"Batch flip normals (finally): Conditions not met to restore original mode '{original_mode}'. Mode remains '{context.mode}'.")
      elif context.mode == original_mode:
        logging.debug(f"Batch flip normals (finally): Mode already same as original ('{original_mode}'). No change.")


    except Exception as e_finally:
      logging.error(f"Batch flip normals: Critical error in 'finally' block during state restoration: {e_finally}", exc_info=True)
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
        Optimized USD import loop:
          - Switch once to temp_scene
          - Use set-difference to detect new objects
          - Progress bar via window_manager.progress_*
          - Set cursor to WAIT via window.cursor_set, then restore
          - Integrate existing logic: conceptual-base filtering, transform application, texture attach, cleanup
        Returns: (all_keep_objs, processed_files_count, textures_processed_for_count)
        """
        import bpy
        import os
        import logging
        from mathutils import Matrix

        wm = context.window_manager
        win = context.window

        total_files = len(self.files)
        # Begin progress
        try:
            wm.progress_begin(0, total_files)
        except Exception:
            pass

        # Attempt to set wait cursor, if supported
        try:
            win.cursor_set('WAIT')
        except Exception:
            pass

        # Switch once to temp_scene
        original_scene = context.window.scene
        context.window.scene = temp_scene

        all_keep_objs = []
        processed_files_count = 0
        textures_processed_for_count = 0

        # Prepare USD importer prefs backup if needed
        usd_importer_addon = context.preferences.addons.get('io_scene_usd')
        original_importer_settings = {}
        if usd_importer_addon:
            importer_prefs = usd_importer_addon.preferences
            # Backup relevant settings; adjust as needed
            for attr in ("axis_forward", "axis_up"):
                if hasattr(importer_prefs, attr):
                    original_importer_settings[attr] = getattr(importer_prefs, attr)
            # Apply from addon_prefs if desired; this matches your original logic
            forward_axis = getattr(addon_prefs, "usd_import_forward_axis", None)
            up_axis = getattr(addon_prefs, "usd_import_up_axis", None)
            if forward_axis and hasattr(importer_prefs, "axis_forward"):
                importer_prefs.axis_forward = forward_axis
            if up_axis and hasattr(importer_prefs, "axis_up"):
                importer_prefs.axis_up = up_axis
            logging.debug(f"USD Importer axes set to Forward={forward_axis}, Up={up_axis}.")

        # Prepare for transform flags once
        remix_scale = getattr(addon_prefs, "remix_import_scale", 1.0)
        scale_needed = abs(remix_scale - 1.0) > 1e-6
        if scale_needed:
            scale_matrix = Matrix.Diagonal((remix_scale, remix_scale, remix_scale, 1.0))
        mirror_flag = bool(getattr(addon_prefs, "mirror_import", False))
        flip_flag = bool(getattr(addon_prefs, "flip_normals_import", False))
        attach_textures_flag = bool(getattr(addon_prefs, "remix_import_original_textures", False))

        # If mirror_flag needs a matrix:
        if mirror_flag:
            mirror_matrix = Matrix.Scale(-1.0, 4, (1.0, 0.0, 0.0))

        # For material dedupe
        data_materials = bpy.data.materials
        materials_seen = set(data_materials.keys())

        # Process each file
        for idx, file_elem in enumerate(self.files):
            # Update progress early if skipping
            try:
                wm.progress_update(idx)
            except Exception:
                pass

            filepath = os.path.join(self.directory, file_elem.name)
            # Only proceed if file exists and extension matches
            valid_exts = tuple(ext.strip().lower() for ext in self.filename_ext.split(','))
            if not (os.path.exists(filepath) and filepath.lower().endswith(valid_exts)):
                continue

            processed_files_count += 1

            # Detect pre-import objects
            before_objs = set(temp_scene.objects)

            # Import USD
            try:
                bpy.ops.wm.usd_import(filepath=filepath)
            except Exception as e_import:
                logging.error(f"Error importing {filepath}: {e_import}", exc_info=True)
                # skip to next
                continue

            # Detect newly added objects
            after_objs = set(temp_scene.objects)
            new_objs = [o for o in after_objs if o not in before_objs]

            if not new_objs:
                logging.warning(f"No new objects detected in import of {filepath}")
                # maybe fallback to selected?
                if context.selected_objects:
                    new_objs = list(context.selected_objects)
                else:
                    continue

            # 1) Classify unique meshes vs discards
            unique_meshes = []
            discards = []
            get_base = self._get_conceptual_asset_base_name
            for obj_raw in new_objs:
                if obj_raw.type != 'MESH':
                    discards.append(obj_raw)
                    continue
                base_name = get_base(obj_raw)
                if base_name not in self._processed_conceptual_asset_bases:
                    self._processed_conceptual_asset_bases.add(base_name)
                    unique_meshes.append(obj_raw)
                else:
                    discards.append(obj_raw)

            if not unique_meshes:
                # nothing unique; discard all
                discards = new_objs.copy()
            else:
                # keep parents of unique meshes if in new_objs
                newly_set = set(new_objs)
                keepers_set = set(unique_meshes)
                for mesh in unique_meshes:
                    parent = mesh.parent
                    while parent and parent in newly_set:
                        keepers_set.add(parent)
                        parent = parent.parent
                # anything not in keepers_set goes to discards if not already
                for obj_raw in new_objs:
                    if obj_raw not in keepers_set and obj_raw not in discards:
                        discards.append(obj_raw)
                unique_meshes = list(keepers_set)

            # 2) Material dedupe on unique_meshes
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
                            # remove old if unused
                            if mat.users == 0:
                                try:
                                    data_materials.remove(mat, do_unlink=True)
                                except Exception:
                                    pass
                    else:
                        mats_before.add(mat.name)
            materials_seen = mats_before

            # 3) Apply transforms & collect for texture
            meshes_for_texture = []
            for keeper in unique_meshes:
                # scale
                if scale_needed and keeper.type in {'MESH', 'CURVE', 'EMPTY', 'ARMATURE', 'LIGHT', 'CAMERA'}:
                    if not keeper.parent or keeper.parent not in unique_meshes:
                        keeper.matrix_world = scale_matrix @ keeper.matrix_world
                # mirror
                if mirror_flag and keeper.type == 'MESH' and keeper.select_get():
                    keeper.matrix_world = mirror_matrix @ keeper.matrix_world
                # flip normals
                if flip_flag and keeper.type == 'MESH':
                    mesh_data = keeper.data
                    if hasattr(mesh_data, "flip_normals"):
                        mesh_data.flip_normals()
                # mark for texture attach
                if attach_textures_flag and keeper.type == 'MESH':
                    meshes_for_texture.append(keeper)

            # 4) Attach textures if requested and blend saved
            if meshes_for_texture and bpy.data.filepath:
                try:
                    attach_original_textures(meshes_for_texture, context, os.path.dirname(filepath))
                    textures_processed_for_count += len(meshes_for_texture)
                except Exception as e_tex:
                    logging.error(f"Error attaching textures for {filepath}: {e_tex}", exc_info=True)

            # 5) Delete discards
            for obj_del in discards:
                if obj_del.name in temp_scene.objects:
                    # unlink from collections
                    for coll in list(obj_del.users_collection):
                        try:
                            coll.objects.unlink(obj_del)
                        except Exception:
                            pass
                    # unlink from scene.collection
                    if obj_del.name in temp_scene.collection.objects:
                        temp_scene.collection.objects.unlink(obj_del)
                    # remove object data-block
                    data_blk = obj_del.data
                    try:
                        bpy.data.objects.remove(obj_del, do_unlink=True)
                    except Exception:
                        pass
                    # remove mesh data if orphaned
                    if data_blk and data_blk.users == 0:
                        try:
                            if isinstance(data_blk, bpy.types.Mesh):
                                bpy.data.meshes.remove(data_blk)
                            elif isinstance(data_blk, bpy.types.Curve):
                                bpy.data.curves.remove(data_blk)
                        except Exception:
                            pass

            # 6) Prune dead references from unique_meshes
            pruned = []
            for o in unique_meshes:
                try:
                    if o.name in temp_scene.objects:
                        pruned.append(o)
                except ReferenceError:
                    continue
            unique_meshes = pruned

            # 7) Accumulate keepers
            all_keep_objs.extend(unique_meshes)

            # Update progress
            try:
                wm.progress_update(idx + 1)
            except Exception:
                pass

        # end for files

        # Restore USD importer prefs
        if usd_importer_addon and original_importer_settings:
            importer_prefs = usd_importer_addon.preferences
            for attr, val in original_importer_settings.items():
                if hasattr(importer_prefs, attr):
                    try:
                        setattr(importer_prefs, attr, val)
                    except Exception:
                        pass
            logging.debug("USD importer axis settings restored.")

        # Restore scene
        context.window.scene = original_scene

        # Restore cursor
        try:
            win.cursor_set('DEFAULT')
        except Exception:
            pass
        # End progress
        try:
            wm.progress_end()
        except Exception:
            pass

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
    bl_label = "Export and Ingest Selected Objects"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        addon_prefs = context.preferences.addons[__name__].preferences
        
        # Check if the ingest directory is still the default one.
        if addon_prefs.remix_ingest_directory.strip() == "/ProjectFolder/Assets":
            popup_message = "Please change the Ingest Directory to inside the Project folder."
            logging.warning(popup_message)
            # Using the same popup code as for unsaved blend file.
            bpy.ops.object.show_popup('INVOKE_DEFAULT', message=popup_message, success=False)
            return {'CANCELLED'}

        global export_lock
        if export_lock:
            self.report({'INFO'}, "Another export is already in progress.")
            logging.info("Another export is already in progress.")
            return {'CANCELLED'}

        if not is_blend_file_saved():
            popup_message = "Please save your Blender file before exporting and ingesting assets."
            logging.warning(popup_message)
            bpy.ops.object.show_popup('INVOKE_DEFAULT', message=popup_message, success=False)
            return {'CANCELLED'}

        # (Rest of your existing code follows unchanged...)
        bpy.ops.file.unpack_all(method="USE_LOCAL")
        logging.info("Successfully unpacked all packed files.")
        self.report({'INFO'}, "All packed files have been unpacked.")

        export_lock = True
        logging.debug("Lock acquired for export process.")

        normals_flipped = False
        temp_filepath = ""
        mtl_filepath = ""

        try:
            success, missing_textures = verify_texture_files_exist(context)
            if not isinstance(success, bool) or not isinstance(missing_textures, list):
                error_message = "verify_texture_files_exist() should return a tuple (bool, list)."
                logging.error(error_message)
                self.report({'ERROR'}, error_message)
                return {'CANCELLED'}

            if not success:
                error_message = "Export canceled due to missing texture files:\n"
                for obj_name, mat_name, node_name, img_path in missing_textures:
                    error_message += f" - Object: {obj_name}, Material: {mat_name}, Node: {node_name}, Path: {img_path}\n"
                logging.error(error_message)
                self.report({'ERROR'}, "Missing texture files. Check the log for details.")
                bpy.ops.object.show_popup('INVOKE_DEFAULT', message=error_message, success=False)
                export_lock = False
                logging.debug("Lock released for export process due to missing textures.")
                return {'CANCELLED'}
                
            success, replaced_textures = convert_exr_textures_to_png(context)
            if not isinstance(success, bool) or not isinstance(replaced_textures, list):
                error_message = "convert_exr_textures_to_png() should return a tuple (bool, list)."
                logging.error(error_message)
                self.report({'ERROR'}, error_message)
                return {'CANCELLED'}

            if not success:
                self.report({'ERROR'}, "Failed to convert EXR textures to PNG.")
                logging.error("Failed to convert EXR textures to PNG.")
                return {'CANCELLED'}

            for material_name, old_path, new_path in replaced_textures:
                replace_texture(material_name, old_path, new_path)

            mesh_objects = [obj for obj in (context.selected_objects if addon_prefs.remix_use_selection_only else context.scene.objects) if obj.type == 'MESH']
            logging.debug(f"Number of mesh objects to process: {len(mesh_objects)}")
            if not mesh_objects:
                self.report({'WARNING'}, "No mesh objects found to export.")
                logging.warning("No mesh objects found to export.")
                return {'CANCELLED'}

            if addon_prefs.flip_faces_export:
                for obj in mesh_objects:
                    flip_normals_api(obj)
                    logging.debug(f"Flipped normals for object: {obj.name}")
                    print(f"Flipped normals for object: {obj.name}")
                normals_flipped = True
                logging.info("Normals flipped before export.")
                print("Normals flipped before export.")

            base_name, asset_number = get_asset_number(context)
            if not isinstance(base_name, str) or not isinstance(asset_number, int):
                error_message = "get_asset_number() should return a tuple (base_name, asset_number)."
                logging.error(error_message)
                self.report({'ERROR'}, error_message)
                return {'CANCELLED'}

            obj_filename = f"{base_name}_{asset_number}.obj"
            temp_dir = tempfile.gettempdir().replace('\\', '/')
            temp_filepath = os.path.join(temp_dir, obj_filename).replace('\\', '/')
            logging.info(f"Temporary OBJ filepath: {temp_filepath}")

            forward_axis = addon_prefs.obj_export_forward_axis
            up_axis = addon_prefs.obj_export_up_axis
            # Increase scale by modifying the global_scale parameter:
            export_scale = addon_prefs.remix_export_scale

            result = bpy.ops.wm.obj_export(
                filepath=temp_filepath,
                check_existing=True,
                filter_blender=False,
                filter_backup=False,
                filter_image=False,
                filter_movie=False,
                filter_python=False,
                filter_font=False,
                filter_sound=False,
                filter_text=False,
                filter_archive=False,
                filter_btx=False,
                filter_collada=False,
                filter_alembic=False,
                filter_usd=False,
                filter_obj=False,
                filter_volume=False,
                filter_folder=True,
                filter_blenlib=False,
                filemode=8,
                display_type='DEFAULT',
                sort_method='DEFAULT',
                export_animation=False,
                start_frame=-2147483648,
                end_frame=2147483647,
                forward_axis=forward_axis,
                up_axis=up_axis,
                global_scale=export_scale,
                apply_modifiers=True,
                export_eval_mode='DAG_EVAL_VIEWPORT',
                export_selected_objects=addon_prefs.remix_use_selection_only,
                export_uv=True,
                export_normals=True,
                export_colors=False,
                export_materials=True,
                export_pbr_extensions=True,
                path_mode='ABSOLUTE',
                export_triangulated_mesh=False,
                export_curves_as_nurbs=False,
                export_object_groups=False,
                export_material_groups=False,
                export_vertex_groups=False,
                export_smooth_groups=False,
                smooth_group_bitflags=False,
                filter_glob='*.obj;*.mtl',
                collection=''
            )

            if result != {'FINISHED'} or not os.path.exists(temp_filepath):
                self.report({'ERROR'}, "OBJ export failed; file not found.")
                logging.error("OBJ export failed; file not found.")
                return {'CANCELLED'}

            mtl_filepath = temp_filepath.replace('.obj', '.mtl')

            ingested_usd = upload_to_api(temp_filepath, addon_prefs.remix_ingest_directory, context)
            if not isinstance(ingested_usd, str):
                self.report({'ERROR'}, "Failed to ingest OBJ into Remix.")
                logging.error("Failed to ingest OBJ into Remix.")
                return {'CANCELLED'}

            if addon_prefs.remix_replace_stock_mesh:
                logging.debug("Replace Stock Mesh option is checked. Proceeding to replace using fetched prim paths.")
                prim_paths = fetch_selected_mesh_prim_paths()
                if not isinstance(prim_paths, list):
                    error_message = "fetch_selected_mesh_prim_paths() should return a list."
                    logging.error(error_message)
                    self.report({'ERROR'}, error_message)
                    return {'CANCELLED'}

                if not prim_paths:
                    self.report({'ERROR'}, "Replace Stock Mesh is ticked but no selected mesh prim paths were found.")
                    logging.error("Replace Stock Mesh is ticked but no selected mesh prim paths were found.")
                    return {'CANCELLED'}

                for prim_path in prim_paths:
                    result_replace = replace_mesh_with_put_request(prim_path, ingested_usd, "", "", context)
                    if not isinstance(result_replace, tuple) or len(result_replace) != 2:
                        error_message = "replace_mesh_with_put_request() should return a tuple (bool, str)."
                        logging.error(error_message)
                        self.report({'ERROR'}, error_message)
                        return {'CANCELLED'}

                    success_replace, new_reference_path = result_replace

                    if success_replace and isinstance(new_reference_path, str):
                        self.report({'INFO'}, "Ingest Complete - Mesh Replaced")
                        logging.info("Mesh replaced successfully in Remix.")
                        print("Mesh replaced successfully in Remix.")

                        select_success = select_mesh_prim_in_remix(new_reference_path, context)
                        if not select_success:
                            self.report({'WARNING'}, "Failed to select mesh prim in Remix.")
                            logging.warning("Failed to select mesh prim in Remix.")

                        ingest_result = handle_height_textures(context, new_reference_path, exported_objects=mesh_objects)
                        if ingest_result != {'FINISHED'}:
                            self.report({'ERROR'}, "Failed to process height textures.")
                            logging.error("Failed to process height textures.")
                            return {'CANCELLED'}

                    else:
                        self.report({'ERROR'}, f"Failed to replace mesh via PUT request for prim: {prim_path}.")
                        logging.error(f"Failed to replace mesh via PUT request for prim: {prim_path}.")
                        return {'CANCELLED'}

            else:
                logging.debug("Replace Stock Mesh option is unchecked. Proceeding with replacement if prim exists, else append.")
                prim_path, reference_path = check_blend_file_in_prims(base_name, context)
                if not isinstance(prim_path, (str, type(None))) or not isinstance(reference_path, (str, type(None))):
                    error_message = "check_blend_file_in_prims() should return a tuple (str or None, str or None)."
                    logging.error(error_message)
                    self.report({'ERROR'}, error_message)
                    return {'CANCELLED'}

                if prim_path:
                    logging.info(f"Existing prim found: {prim_path}. Initiating replacement.")
                    print(f"Existing prim found: {prim_path}. Initiating replacement.")

                    result_fetch = fetch_file_paths_from_reference_prim(reference_path, context)
                    if not isinstance(result_fetch, tuple) or len(result_fetch) != 2:
                        error_message = "fetch_file_paths_from_reference_prim() should return a tuple (str, str)."
                        logging.error(error_message)
                        self.report({'ERROR'}, error_message)
                        export_lock = False
                        logging.debug("Lock released for export process due to failed asset path retrieval.")
                        return {'CANCELLED'}

                    existing_path, existing_layer = result_fetch

                    if not existing_path or not existing_layer:
                        self.report({'ERROR'}, "Failed to retrieve existing asset file paths for replacement.")
                        logging.error("Failed to retrieve existing asset file paths for replacement.")
                        export_lock = False
                        logging.debug("Lock released for export process due to failed asset path retrieval.")
                        return {'CANCELLED'}

                    result_replace = replace_mesh_with_put_request(reference_path, ingested_usd, existing_path, existing_layer, context)
                    if not isinstance(result_replace, tuple) or len(result_replace) != 2:
                        error_message = "replace_mesh_with_put_request() should return a tuple (bool, str)."
                        logging.error(error_message)
                        self.report({'ERROR'}, error_message)
                        return {'CANCELLED'}

                    success_replace, new_reference_path = result_replace

                    if success_replace and isinstance(new_reference_path, str):
                        self.report({'INFO'}, "Ingest Complete - Mesh Replaced")
                        logging.info("Mesh replaced successfully in Remix.")
                        print("Mesh replaced successfully in Remix.")

                        select_success = select_mesh_prim_in_remix(new_reference_path, context)
                        if not select_success:
                            self.report({'WARNING'}, "Failed to select mesh prim in Remix.")
                            logging.warning("Failed to select mesh prim in Remix.")

                        ingest_result = handle_height_textures(context, new_reference_path, exported_objects=mesh_objects)
                        if ingest_result != {'FINISHED'}:
                            self.report({'ERROR'}, "Failed to process height textures.")
                            logging.error("Failed to process height textures.")
                            return {'CANCELLED'}
                    else:
                        self.report({'ERROR'}, "Failed to replace mesh via PUT request.")
                        logging.error("Failed to replace mesh via PUT request.")
                        return {'CANCELLED'}
                else:
                    logging.info("No existing prim found. Proceeding to append the new mesh.")
                    print("No existing prim found. Proceeding to append the new mesh.")

                    selected_prim_paths = fetch_selected_mesh_prim_paths()
                    if not isinstance(selected_prim_paths, list):
                        error_message = "fetch_selected_mesh_prim_paths() should return a list."
                        logging.error(error_message)
                        self.report({'ERROR'}, error_message)
                        export_lock = False
                        logging.debug("Lock released for export process due to failed prim path retrieval.")
                        return {'CANCELLED'}

                    if not selected_prim_paths:
                        self.report({'ERROR'}, "Failed to retrieve the target prim path from Remix server.")
                        logging.error("Failed to retrieve the target prim path from Remix server.")
                        export_lock = False
                        logging.debug("Lock released for export process due to failed prim path retrieval.")
                        return {'CANCELLED'}

                    for prim_path_full in selected_prim_paths:
                        trimmed_prim_path = trim_prim_path(prim_path_full, segments_to_trim=1)
                        logging.info(f"Trimmed prim path for appending: {trimmed_prim_path}")
                        print(f"Trimmed prim path for appending: {trimmed_prim_path}")

                        result_append = append_mesh_with_post_request(trimmed_prim_path, ingested_usd, context)
                        if not isinstance(result_append, tuple) or len(result_append) != 2:
                            error_message = "append_mesh_with_post_request() should return a tuple (bool, str)."
                            logging.error(error_message)
                            self.report({'ERROR'}, error_message)
                            return {'CANCELLED'}

                        success_append, new_reference_path = result_append

                        if success_append and isinstance(new_reference_path, str):
                            self.report({'INFO'}, "Ingest Complete - Mesh Appended")
                            logging.info("Mesh appended successfully in Remix.")
                            print("Mesh appended successfully in Remix.")

                            obj_name = obj_filename.replace('.obj', '')
                            actual_mesh = get_actual_mesh_name(mesh_objects)
                            dynamic_prim = construct_dynamic_prim_path(new_reference_path, obj_name, actual_mesh, append_world=True)
                            if not dynamic_prim:
                                self.report({'ERROR'}, "Failed to construct dynamic prim path.")
                                logging.error("Failed to construct dynamic prim path.")
                                return {'CANCELLED'}

                            ingest_result = handle_height_textures(context, new_reference_path, exported_objects=mesh_objects)
                            if ingest_result != {'FINISHED'}:
                                self.report({'ERROR'}, "Failed to process height textures.")
                                logging.error("Failed to process height textures.")
                                return {'CANCELLED'}
                        else:
                            self.report({'ERROR'}, "Failed to append mesh via POST request.")
                            logging.error("Failed to append mesh via POST request.")
                            return {'CANCELLED'}

            return {'FINISHED'}

        except Exception as e:
            logging.error(f"Unexpected error during export and ingest: {e}")
            self.report({'ERROR'}, f"Failed Ingest: {e}")
            return {'CANCELLED'}

        finally:
            if normals_flipped:
                for obj in mesh_objects:
                    flip_normals_api(obj)
                    logging.debug(f"Flipped normals back for object after export: {obj.name}")
                    print(f"Flipped normals back for object after export: {obj.name}")

                logging.info("Normals flipped back after export to restore original state.")
                print("Normals flipped back after export to restore original state.")

            if temp_filepath and os.path.exists(temp_filepath):
                try:
                    os.remove(temp_filepath)
                    logging.info(f"Deleted temporary OBJ file: {temp_filepath}")
                    print(f"Deleted temporary OBJ file: {temp_filepath}")
                except Exception as e:
                    logging.error(f"Failed to delete temporary OBJ file: {e}")
                    print(f"Failed to delete temporary OBJ file: {e}")

            if mtl_filepath and os.path.exists(mtl_filepath):
                try:
                    os.remove(mtl_filepath)
                    logging.info(f"Deleted temporary MTL file: {mtl_filepath}")
                    print(f"Deleted temporary MTL file: {mtl_filepath}")
                except Exception as e:
                    logging.error(f"Failed to delete temporary MTL file: {e}")
                    print(f"Failed to delete temporary MTL file: {e}")

            export_lock = False
            logging.debug("Lock released for export process.")
            
def convert_exr_textures_to_png(context):
    global conversion_count
    try:
        bpy.ops.file.unpack_all(method="USE_LOCAL")
        logging.info("Starting conversion of EXR textures to PNG.")
        node_trees = list(bpy.data.node_groups) + \
                     [mat.node_tree for mat in bpy.data.materials if mat.use_nodes] + \
                     [scene.node_tree for scene in bpy.data.scenes if scene.use_nodes]

        replaced_textures = []
        conversion_count = 0

        for node_tree in node_trees:
            success, textures = process_nodes_recursively(node_tree.nodes, node_tree)
            if not success:
                return False, []
            replaced_textures.extend(textures)

        logging.info(f"Converted {conversion_count} EXR textures to PNG.")
        return True, replaced_textures

    except Exception as e:
        logging.error(f"Error during EXR to PNG conversion: {e}")
        return False, []
    
def process_nodes_recursively(nodes, node_tree):
    global conversion_count
    replaced_textures = []
    try:
        for node in nodes:
            if node.type == 'GROUP' and node.node_tree:
                success, textures = process_nodes_recursively(node.node_tree.nodes, node.node_tree)
                if not success:
                    return False, []
                replaced_textures.extend(textures)
            elif node.type == 'TEX_IMAGE' and node.image and node.image.source == 'FILE':
                ext = os.path.splitext(node.image.filepath)[1].lower()
                if ext in ['.exr', '.exr_multi_layer']:
                    exr_path = bpy.path.abspath(node.image.filepath)
                    if not os.path.exists(exr_path):
                        logging.warning(f"EXR file does not exist: {exr_path}")
                        continue

                    png_path = os.path.splitext(exr_path)[0] + ".png"
                    if os.path.exists(png_path):
                        logging.warning(f"PNG already exists and will be overwritten: {png_path}")

                    image = node.image
                    image.reload()
                    new_image = bpy.data.images.new(name=os.path.basename(png_path), width=image.size[0], height=image.size[1], alpha=(image.channels == 4))
                    new_image.pixels = image.pixels[:]
                    new_image.file_format = 'PNG'
                    new_image.filepath_raw = png_path
                    new_image.save()

                    node.image = new_image
                    os.remove(exr_path)
                    conversion_count += 1

                    material_name = get_material_name_from_node_tree(node_tree)
                    if material_name:
                        replaced_textures.append((material_name, exr_path, png_path))
        return True, replaced_textures
    except Exception as e:
        logging.error(f"Error during node processing: {e}")
        return False, []

def get_material_name_from_node_tree(node_tree):
    for mat in bpy.data.materials:
        if mat.node_tree == node_tree:
            return mat.name
    return None

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
        os.makedirs(meshes_subdir, exist_ok=True)
        logging.debug(f"'meshes' subdirectory ensured at: {meshes_subdir}")

        # This usd_output_path is what we expect the server to create or confirm
        usd_filename = os.path.splitext(os.path.basename(obj_path))[0] + ".usd"
        expected_usd_output_path = os.path.join(meshes_subdir, usd_filename).replace('\\', '/')
        logging.debug(f"Expected USD Output Path by client: {expected_usd_output_path}")

        payload = {
            "executor": 1,
            "name": "Model(s)",
            "context_plugin": {
                "name": "AssetImporter",
                "data": {
                    "context_name": "ingestcraft",
                    "input_files": [abs_obj_path],
                    "output_directory": meshes_subdir, # This is the directory ON THE SERVER
                    "allow_empty_input_files_list": True,
                    "data_flows": [
                        {
                            "name": "InOutData",
                            "push_input_data": True,
                            "push_output_data": True,
                            "channel": "write_metadata"
                        },
                        {
                            "name": "InOutData",
                            "push_output_data": True,
                            "channel": "ingestion_output"
                        }
                    ],
                    "output_usd_extension": "usd",
                    "hide_context_ui": True,
                    "create_context_if_not_exist": True,
                    "ignore_unbound_bones": False,
                    "expose_mass_ui": True,
                    "expose_mass_queue_action_ui": True,
                    "cook_mass_template": True,
                    "close_stage_on_exit": True
                }
            },
            "check_plugins": [ # ... (rest of your payload remains the same)
                {
                    "name": "ClearUnassignedMaterial", "selector_plugins": [{"name": "AllMeshes", "data": {"include_geom_subset": True}}], "data": {}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "DefaultMaterial", "selector_plugins": [{"name": "AllMeshes", "data": {}}], "data": {}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "MaterialShaders", "selector_plugins": [{"name": "AllMaterials", "data": {}}], "data": {"shader_subidentifiers": {"AperturePBR_Translucent": "translucent|glass|trans", "AperturePBR_Opacity": ".*"}}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "ValueMapping", "selector_plugins": [{"name": "AllShaders", "data": {}}], "data": {"attributes": {"inputs:emissive_intensity": [{"operator": "=", "input_value": 10000, "output_value": 1}]}},
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "ConvertToOctahedral", "selector_plugins": [{"name": "AllShaders", "data": {}}], "resultor_plugins": [{"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}}],
                    "data": {"data_flows": [{"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"}]}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "ConvertToDDS", "selector_plugins": [{"name": "AllShaders", "data": {}}], "resultor_plugins": [{"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}}],
                    "data": {"data_flows": [{"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"}, {"name": "InOutData", "push_output_data": True, "channel": "write_metadata"}]}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "RelativeAssetPaths", "selector_plugins": [{"name": "AllPrims", "data": {}}], "data": {}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "RelativeReferences", "selector_plugins": [{"name": "AllPrims", "data": {}}], "data": {}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "DependencyIterator", "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "WrapRootPrims", "selector_plugins": [{"name": "Nothing", "data": {}}], "data": {"wrap_prim_name": "XForms"}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "CurrentStage", "data": {"save_on_exit": True, "close_stage_on_exit": False}}
                },
                {
                    "name": "WrapRootPrims", "selector_plugins": [{"name": "Nothing", "data": {}}], "data": {"wrap_prim_name": "ReferenceTarget"}, "stop_if_fix_failed": True,
                    "context_plugin": {"name": "CurrentStage", "data": {"save_on_exit": True, "close_stage_on_exit": False}}
                }
            ],
            "resultor_plugins": [
                {"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}},
                {"name": "FileMetadataWritter", "data": {"channel": "write_metadata"}}
            ]
        }

        logging.info(f"Uploading OBJ to {url}")
        response = make_request_with_retries('POST', url, json_payload=payload, verify=addon_prefs.remix_verify_ssl, retries=1)

        if response is None:
            logging.error("Failed to upload OBJ: No response from server.")
            return None

        if response.status_code == 500:
            try:
                response_data_error = response.json()
                detail = response_data_error.get("detail", "")
            except Exception:
                detail = response.text # Fallback to raw text if JSON parsing fails
            
            # Check for your specific error message regarding ingest directory
            if "The validation did not complete successfully" in detail or "ingest_directory" in detail.lower(): # Made check more robust
                error_msg = "Ingestion failed: Please ensure the Ingest Directory in addon preferences is set correctly within your project structure on the server."
                logging.error(f"{error_msg} Server detail: {detail}")
                bpy.ops.object.show_popup('INVOKE_DEFAULT', message=error_msg, success=False)
                return None
            else: # Generic 500 error
                logging.error(f"Failed to upload OBJ. Status: 500, Response: {detail}")
                return None


        if response.status_code != 200: # Handles other non-500 errors
            logging.error(f"Failed to upload OBJ. Status: {response.status_code}, Response: {response.text}")
            return None

        response_data = response.json()
        completed_schemas = response_data.get("completed_schemas", [])
        if not completed_schemas:
            logging.error("No completed schemas found in response.")
            return None

        # --- CORRECTED USD PATH EXTRACTION ---
        usd_path_from_response = None
        try:
            context_plugin_data = completed_schemas[0].get("context_plugin", {}).get("data", {})
            data_flows = context_plugin_data.get("data_flows", [])
            
            for flow in data_flows:
                # Check for flows that are likely to contain the final USD output path
                if flow.get("push_output_data") and flow.get("output_data"):
                    if isinstance(flow["output_data"], list) and len(flow["output_data"]) > 0:
                        potential_path = flow["output_data"][0]
                        if isinstance(potential_path, str) and potential_path.lower().endswith(".usd"):
                            # Prefer paths from "ingestion_output" or "write_metadata" if available
                            if flow.get("channel") in ["ingestion_output", "write_metadata"]:
                                usd_path_from_response = potential_path.replace('\\', '/')
                                logging.info(f"Found USD path in data_flows (channel: '{flow.get('channel')}'): {usd_path_from_response}")
                                break # Prefer this path
                            elif usd_path_from_response is None: # If not set yet, take any USD path
                                usd_path_from_response = potential_path.replace('\\', '/')
                                logging.info(f"Found potential USD path in data_flows (channel: '{flow.get('channel')}'): {usd_path_from_response}")
            
            if usd_path_from_response:
                 # Ensure the path matches what we expect or use the server's authoritative path
                if os.path.normpath(usd_path_from_response) == os.path.normpath(expected_usd_output_path):
                    logging.debug(f"API returned USD Path matches expected client path: {usd_path_from_response}")
                else:
                    logging.warning(f"API returned USD Path '{usd_path_from_response}' differs from client expected path '{expected_usd_output_path}'. Using API path.")
                return usd_path_from_response # Return the path from the API response
            else:
                logging.error("No suitable USD output path found in 'data_flows' in the response.")
                return None

        except Exception as e_parse:
            logging.error(f"Error parsing 'data_flows' for USD path: {e_parse}", exc_info=True)
            logging.error("No USD path found in the response due to parsing error.")
            return None
        # --- END OF CORRECTION ---

    # Removed 'finally: pass' as it's not needed
    # Errors and None returns are handled above.
    # If an exception occurs before a return, it will propagate.
    except requests.exceptions.RequestException as e_req:
        logging.error(f"Network request failed during API upload: {e_req}", exc_info=True)
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
        addon_prefs = context.preferences.addons[__name__].preferences
        layout = self.layout

        presets_box = layout.box()
        presets_box.label(text="Presets", icon='GROUP')
        row = presets_box.row()
        row.prop(addon_prefs, "remix_preset", text="")

        export_box = layout.box()
        export_box.label(text="Export Settings", icon='EXPORT')
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
        export_box.prop(addon_prefs, "apply_modifiers", text="Apply Modifiers")
        row = export_box.row(align=True)
        row.label(text="Forward Axis")
        row.prop(addon_prefs, "obj_export_forward_axis", text="", expand=False)
        row = export_box.row(align=True)
        row.label(text="Up Axis")
        row.prop(addon_prefs, "obj_export_up_axis", text="", expand=False)
        export_box.prop(addon_prefs, "remix_export_scale", text="Export Scale")

        # ------------------------------------------------------------------
        # New button: Export to Substance
        # ------------------------------------------------------------------
        #export_box.operator("export.substance_painter", text="Export to Substance", icon='EXPORT')

        export_box.operator("object.export_and_ingest", text="Export and Ingest")

        import_box = layout.box()
        import_box.label(text="USD Import", icon='IMPORT')
        import_box.prop(addon_prefs, "mirror_import", text="Mirror on Import")
        import_box.prop(addon_prefs, "flip_normals_import", text="Flip Normals During Import")
        import_box.prop(addon_prefs, "remix_import_scale", text="Import Scale")
        import_box.prop(addon_prefs, "remix_import_original_textures", text="Import Original Textures")
        
        # New Dropdown for USD Import Forward Axis
        #row = import_box.row(align=True)
        #row.label(text="Forward Axis (USD Source):")
        #row.prop(addon_prefs, "usd_import_forward_axis", text="")

        import_box.operator("object.import_usd_from_remix", text="Import USD from Remix")
        import_box.operator("object.import_captures", text="Import USD Captures")

        reset_box = layout.box()
        reset_box.label(text="Reset Options", icon='FILE_REFRESH')
        reset_box.operator("object.reset_remix_ingestor_options", text="Reset Options")

        info_box = layout.box()
        info_row = info_box.row()
        info_row.operator("object.info_operator", text="Hover for Information", icon='INFO')

classes = [
    RemixIngestorPreferences,
    OBJECT_OT_export_and_ingest,
    OBJECT_OT_import_usd_from_remix,
    OBJECT_OT_import_captures, # Added new class here
    OBJECT_OT_reset_options,
    OBJECT_OT_show_popup,
    VIEW3D_PT_remix_ingestor,
    OBJECT_OT_info_operator,
    OBJECT_OT_toggle_info_display,
    AssetNumberItem,
    CustomSettingsBackup,
    EXPORT_OT_SubstancePainterExporter
]

def register():
    setup_logger()
    for cls in classes:
        bpy.utils.register_class(cls)

    bpy.types.Scene.remix_custom_settings_backup = bpy.props.PointerProperty(type=CustomSettingsBackup)
    bpy.types.Scene.remix_asset_number = bpy.props.CollectionProperty(type=AssetNumberItem)


def unregister():
    del bpy.types.Scene.remix_asset_number
    del bpy.types.Scene.remix_custom_settings_backup

    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
