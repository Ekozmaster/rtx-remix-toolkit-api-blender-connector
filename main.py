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
from bpy.props import BoolProperty, StringProperty, CollectionProperty, IntProperty, EnumProperty, FloatProperty
from bpy.types import Operator, Panel, PropertyGroup, AddonPreferences
import urllib.parse

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
        url = "http://localhost:8011/stagecraft/assets/?selection=true&filter_session_assets=false&exists=true"
        headers = {'accept': 'application/lightspeed.remix.service+json; version=1.0'}
        response = make_request_with_retries(
            'GET',
            url,
            headers=headers,
            verify=True
        )
        if not response or response.status_code != 200:
            logging.error("Failed to fetch selected mesh prim paths.")
            print("Failed to fetch selected mesh prim paths.")
            return []

        asset_paths = response.json().get("asset_paths", [])
        selected_meshes = [path for path in asset_paths if "/meshes/" in path.lower()]
        logging.info(f"Selected mesh prim paths: {selected_meshes}")
        print(f"Selected mesh prim paths: {selected_meshes}")
        return [ensure_single_leading_slash(p.rstrip('/')) for p in selected_meshes]
    except Exception as e:
        logging.error(f"Error fetching selected mesh prim paths: {e}")
        print(f"Error fetching selected mesh prim paths: {e}")
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
        print(f"Textures subdirectory path: {textures_subdir}")

        if not os.path.exists(textures_subdir):
            try:
                os.makedirs(textures_subdir, exist_ok=True)
                logging.info(f"Created 'textures' subdirectory: {textures_subdir}")
                print(f"Created 'textures' subdirectory: {textures_subdir}")
            except Exception as e:
                logging.error(f"Failed to create textures subdirectory '{textures_subdir}': {e}")
                print(f"Failed to create textures subdirectory '{textures_subdir}': {e}")
                return
        else:
            logging.debug(f"'textures' subdirectory already exists: {textures_subdir}")
            print(f"'textures' subdirectory already exists: {textures_subdir}")           

        # Iterate over each imported object
        for obj in imported_objects:
            print(f"Processing object: {obj.name}")
            logging.info(f"Processing object: {obj.name}")

            for mat_slot in obj.material_slots:
                mat = mat_slot.material
                if not mat:
                    logging.warning(f"Object '{obj.name}' has an empty material slot.")
                    print(f"Object '{obj.name}' has an empty material slot.")
                    continue

                print(f"Processing material: {mat.name}")
                logging.info(f"Processing material: {mat.name}")

                if not mat.use_nodes:
                    mat.use_nodes = True
                    logging.info(f"Enabled node usage for material '{mat.name}'.")
                    print(f"Enabled node usage for material '{mat.name}'.")

                principled_bsdf = None
                for node in mat.node_tree.nodes:
                    if node.type == 'BSDF_PRINCIPLED':
                        principled_bsdf = node
                        break

                if not principled_bsdf:
                    principled_bsdf = mat.node_tree.nodes.new(type='ShaderNodeBsdfPrincipled')
                    principled_bsdf.location = (400, 0)
                    logging.info(f"Created Principled BSDF node for material '{mat.name}'.")
                    print(f"Created Principled BSDF node for material '{mat.name}'.")

                image_texture = None
                for node in mat.node_tree.nodes:
                    if node.type == 'TEX_IMAGE':
                        image_texture = node
                        break

                if not image_texture:
                    image_texture = mat.node_tree.nodes.new(type='ShaderNodeTexImage')
                    image_texture.location = (0, 0)
                    logging.info(f"Created Image Texture node for material '{mat.name}'.")
                    print(f"Created Image Texture node for material '{mat.name}'.")

                match = re.match(r'^mat_([A-Fa-f0-9]{16})\.', mat.name)
                if match:
                    mat_hash = match.group(1)
                    logging.debug(f"Extracted hash '{mat_hash}' from material '{mat.name}'.")
                else:
                    match = re.match(r'^mat_([A-Fa-f0-9]{16})$', mat.name)
                    if match:
                        mat_hash = match.group(1)
                        logging.debug(f"Extracted hash '{mat_hash}' from material '{mat.name}'.")
                    else:
                        logging.warning(f"Material name '{mat.name}' does not match expected hash pattern.")
                        print(f"Material name '{mat.name}' does not match expected hash pattern.")
                        continue

                texture_file = f"{mat_hash}.dds"
                texture_path = os.path.join(base_dir, "textures", texture_file).replace('\\', '/')
                print(f"Looking for texture file: {texture_file}")
                logging.info(f"Looking for texture file: {texture_file}")

                if os.path.exists(texture_path):
                    if import_original_textures:
                        png_filename = f"{mat_hash}.png"
                        png_path = os.path.join(textures_subdir, png_filename).replace('\\', '/')
                        logging.info(f"Preparing to convert DDS to PNG: {texture_path} -> {png_path}")
                        print(f"Preparing to convert DDS to PNG: {texture_path} -> {png_path}")

                        if not os.path.exists(png_path):
                            try:
                                dds_image = bpy.data.images.load(texture_path)
                                logging.info(f"Loaded DDS image: {texture_path}")
                                print(f"Loaded DDS image: {texture_path}")

                                png_image = bpy.data.images.new(
                                    name=os.path.basename(png_path),
                                    width=dds_image.size[0],
                                    height=dds_image.size[1],
                                    alpha=(dds_image.channels == 4)
                                )
                                logging.debug(f"Created new PNG image: {png_path}")

                                png_image.pixels = list(dds_image.pixels)
                                logging.debug(f"Copied pixel data from DDS to PNG for '{png_filename}'.")

                                png_image.file_format = 'PNG'
                                png_image.filepath_raw = png_path
                                png_image.save()

                                logging.info(f"Saved PNG image: {png_path}")
                                print(f"Saved PNG image: {png_path}")

                                dds_image.user_clear()
                                bpy.data.images.remove(dds_image)
                                logging.debug(f"Unloaded DDS image: {texture_path}")
                            except Exception as e:
                                logging.error(f"Failed to convert DDS to PNG for texture '{texture_file}': {e}")
                                print(f"Failed to convert DDS to PNG for texture '{texture_file}': {e}")
                                continue
                        else:
                            logging.info(f"PNG texture already exists: {png_path}")
                            print(f"PNG texture already exists: {png_path}")

                        try:
                            existing_png = bpy.data.images.get(os.path.basename(png_path))
                            if existing_png:
                                image_texture.image = existing_png
                                logging.info(f"Assigned existing PNG texture '{png_filename}' to material '{mat.name}'.")
                                print(f"Assigned existing PNG texture '{png_filename}' to material '{mat.name}'.")
                            else:
                                png_image = bpy.data.images.load(png_path)
                                image_texture.image = png_image
                                logging.info(f"Assigned PNG texture '{png_filename}' to material '{mat.name}'.")
                                print(f"Assigned PNG texture '{png_filename}' to material '{mat.name}'.")
                            links = mat.node_tree.links
                            base_color_input = principled_bsdf.inputs.get('Base Color')
                            if base_color_input:
                                existing_links = [link for link in links if link.to_socket == base_color_input]
                                for link in existing_links:
                                    links.remove(link)
                                    logging.debug(f"Removed existing link to Base Color for material '{mat.name}'.")
                                    print(f"Removed existing link to Base Color for material '{mat.name}'.")
                                links.new(image_texture.outputs['Color'], base_color_input)
                                logging.info(f"Connected Image Texture to Base Color for material '{mat.name}'.")
                                print(f"Connected Image Texture to Base Color for material '{mat.name}'.")
                            else:
                                logging.warning(f"No 'Base Color' input found in Principled BSDF for material '{mat.name}'.")
                                print(f"No 'Base Color' input found in Principled BSDF for material '{mat.name}'.")
                        except Exception as e:
                            logging.error(f"Failed to assign PNG texture '{png_filename}' to material '{mat.name}': {e}")
                            print(f"Failed to assign PNG texture '{png_filename}' to material '{mat.name}': {e}")
                    else:
                        try:
                            existing_dds = bpy.data.images.get(os.path.basename(texture_path))
                            if existing_dds:
                                image_texture.image = existing_dds
                                logging.info(f"Assigned existing DDS texture '{texture_file}' to material '{mat.name}'.")
                                print(f"Assigned existing DDS texture '{texture_file}' to material '{mat.name}'.")
                            else:
                                dds_image = bpy.data.images.load(texture_path)
                                image_texture.image = dds_image
                                logging.info(f"Assigned DDS texture '{texture_file}' to material '{mat.name}'.")
                                print(f"Assigned DDS texture '{texture_file}' to material '{mat.name}'.")
                            links = mat.node_tree.links
                            base_color_input = principled_bsdf.inputs.get('Base Color')
                            if base_color_input:
                                existing_links = [link for link in links if link.to_socket == base_color_input]
                                for link in existing_links:
                                    links.remove(link)
                                    logging.debug(f"Removed existing link to Base Color for material '{mat.name}'.")
                                    print(f"Removed existing link to Base Color for material '{mat.name}'.")
                                links.new(image_texture.outputs['Color'], base_color_input)
                                logging.info(f"Connected Image Texture to Base Color for material '{mat.name}'.")
                                print(f"Connected Image Texture to Base Color for material '{mat.name}'.")
                            else:
                                logging.warning(f"No 'Base Color' input found in Principled BSDF for material '{mat.name}'.")
                                print(f"No 'Base Color' input found in Principled BSDF for material '{mat.name}'.")
                        except Exception as e:
                            logging.error(f"Failed to assign DDS texture '{texture_file}' to material '{mat.name}': {e}")
                            print(f"Failed to assign DDS texture '{texture_file}' to material '{mat.name}': {e}")
                else:
                    logging.warning(f"Texture file does not exist for material '{mat.name}': {texture_path}")
                    print(f"Texture file does not exist for material '{mat.name}': {texture_path}")

    except Exception as e:
        logging.error(f"Error attaching original textures: {e}")
        print(f"Error attaching original textures: {e}")


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
        logging.info("Starting height texture processing.")
        # Determine mesh objects to process
        if exported_objects is not None:
            mesh_objects = [obj for obj in exported_objects if obj.type == 'MESH']
        else:
            mesh_objects = [obj for obj in context.scene.objects if obj.type == 'MESH']

        # Collect unique materials used by these meshes
        used_materials = set()
        for obj in mesh_objects:
            for slot in obj.material_slots:
                if slot.material:
                    used_materials.add(slot.material)

        # Collect height texture data from each material:
        # (each tuple: (reference prim, material name, texture file path))
        height_textures = []
        for mat in used_materials:
            if not mat.use_nodes or not mat.node_tree:
                continue
            for node in mat.node_tree.nodes:
                if node.type in {'DISPLACEMENT', 'BUMP'}:
                    height_input = node.inputs.get('Height')
                    if height_input and height_input.is_linked:
                        linked_node = height_input.links[0].from_node
                        if linked_node.type == 'TEX_IMAGE' and linked_node.image:
                            tex_path = bpy.path.abspath(linked_node.image.filepath).replace('\\', '/')
                            if os.path.exists(tex_path):
                                height_textures.append((reference_prim, mat.name, tex_path))
        if not height_textures:
            logging.info("No height textures found to process.")
            return {'FINISHED'}

        # Ensure the textures output directory exists
        ingest_dir = addon_prefs.remix_ingest_directory
        textures_subdir = os.path.join(ingest_dir, "textures").replace('\\', '/')
        if not os.path.exists(textures_subdir):
            os.makedirs(textures_subdir, exist_ok=True)
            logging.info(f"Created textures subdirectory: {textures_subdir}")

        # Base URL for the export API (strip trailing slash)
        base_url = addon_prefs.remix_export_url.rstrip('/')

        # Process each collected height texture
        for ref_prim, material_name, tex_file in height_textures:
            # STEP 1: Ingest the texture file (via TextureImporter)
            ingest_payload = {
                "executor": 1,
                "name": "Material(s)",
                "context_plugin": {
                    "name": "TextureImporter",
                    "data": {
                        "context_name": "ingestcraft",
                        "input_files": [[tex_file, "HEIGHT"]],
                        "output_directory": textures_subdir,
                        "allow_empty_input_files_list": True,
                        "data_flows": [{"name": "InOutData", "push_input_data": True}],
                        "hide_context_ui": True,
                        "create_context_if_not_exist": True,
                        "expose_mass_ui": True,
                        "cook_mass_template": True
                    }
                },
                "check_plugins": [
                    {
                        "name": "MaterialShaders",
                        "selector_plugins": [{"name": "AllMaterials", "data": {}}],
                        "data": {"shader_subidentifiers": {"AperturePBR_Opacity": ".*"}},
                        "stop_if_fix_failed": True,
                        "context_plugin": {"name": "CurrentStage", "data": {}}
                    },
                    {
                        "name": "ConvertToOctahedral",
                        "selector_plugins": [{"name": "AllShaders", "data": {}}],
                        "resultor_plugins": [
                            {"name": "FileCleanup", "data": {"channel": "cleanup_files_normal", "cleanup_output": False}}
                        ],
                        "data": {
                            "data_flows": [
                                {"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"}
                            ]
                        },
                        "stop_if_fix_failed": True,
                        "context_plugin": {"name": "CurrentStage", "data": {}}
                    },
                    {
                        "name": "ConvertToDDS",
                        "selector_plugins": [{"name": "AllShaders", "data": {}}],
                        "resultor_plugins": [
                            {"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}}
                        ],
                        "data": {
                            "data_flows": [
                                {"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"},
                                {"name": "InOutData", "push_output_data": True, "channel": "write_metadata"},
                                {"name": "InOutData", "push_output_data": True, "channel": "ingestion_output"}
                            ]
                        },
                        "stop_if_fix_failed": True,
                        "context_plugin": {"name": "CurrentStage", "data": {}}
                    },
                    {
                        "name": "MassTexturePreview",
                        "selector_plugins": [{"name": "Nothing", "data": {}}],
                        "data": {"expose_mass_queue_action_ui": True},
                        "stop_if_fix_failed": True,
                        "context_plugin": {"name": "CurrentStage", "data": {}}
                    }
                ],
                "resultor_plugins": [
                    {"name": "FileMetadataWritter", "data": {"channel": "write_metadata"}}
                ]
            }
            ingest_response = make_request_with_retries(
                'POST', f"{base_url}/material", json_payload=ingest_payload, verify=addon_prefs.remix_verify_ssl
            )
            if not ingest_response or ingest_response.status_code not in [200, 201, 204]:
                logging.error(f"Failed to ingest height texture for material '{material_name}'.")
                return {'CANCELLED'}
            ingest_data = ingest_response.json()
            completed_schemas = ingest_data.get("completed_schemas", [])
            final_texture_path = None
            for schema in completed_schemas:
                for plugin in schema.get("check_plugins", []):
                    if plugin.get("name") == "ConvertToDDS":
                        for flow in plugin.get("data", {}).get("data_flows", []):
                            output_data = flow.get("output_data")
                            if output_data and any(".h.rtex.dds" in od for od in output_data):
                                final_texture_path = next(od for od in output_data if ".h.rtex.dds" in od)
                                break
                        if final_texture_path:
                            break
                if final_texture_path:
                    break
            if not final_texture_path:
                logging.error("Failed to find final ingested texture path from ConvertToDDS.")
                return {'CANCELLED'}

            # STEP 2: Construct the material prim asset path dynamically
            # Build material prim: reference prim + '/XForms/World/Looks/' + sanitized material name
            remix_mat_name = blender_mat_to_remix(material_name)
            material_prim = f"{ref_prim}/XForms/World/Looks/{remix_mat_name}"
            encoded_material_prim = urllib.parse.quote(material_prim, safe='')

            # STEP 3: Fetch the list of shader input prims for this material
            textures_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/{encoded_material_prim}/textures"
            textures_response = make_request_with_retries(
                'GET', textures_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )
            if not textures_response or textures_response.status_code != 200:
                logging.error(f"Failed to retrieve textures for material prim: {material_prim}")
                return {'CANCELLED'}
            textures_data = textures_response.json()
            shader_input_prim = None
            textures_list = textures_data.get("textures", [])
            if textures_list and len(textures_list) > 0 and textures_list[0]:
                shader_input_prim = textures_list[0][0]
            else:
                logging.error("No shader input prim found in textures response.")
                return {'CANCELLED'}

            # STEP 4: Get the height shader input prim from the shader input prim
            encoded_shader_input = urllib.parse.quote(shader_input_prim, safe='')
            height_prim_url = f"{addon_prefs.remix_server_url.rstrip('/')}/textures/{encoded_shader_input}/material/inputs?texture_type=HEIGHT"
            height_prim_response = make_request_with_retries(
                'GET', height_prim_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )
            if not height_prim_response or height_prim_response.status_code != 200:
                logging.error("Failed to fetch height shader input prim.")
                return {'CANCELLED'}
            height_prim_data = height_prim_response.json()
            asset_paths = height_prim_data.get("asset_paths", [])
            if not asset_paths or not asset_paths[0]:
                logging.error("No height shader input prim returned in response.")
                return {'CANCELLED'}
            height_shader_prim = asset_paths[0]

            # STEP 5: Update the shader input with the ingested height texture (via PUT)
            put_url = f"{addon_prefs.remix_server_url.rstrip('/')}/textures/"
            put_payload = {
                "force": False,
                "textures": [
                    [height_shader_prim, final_texture_path]
                ]
            }
            put_response = make_request_with_retries(
                'PUT', put_url, json_payload=put_payload,
                headers={
                    "accept": "application/lightspeed.remix.service+json; version=1.0",
                    "Content-Type": "application/lightspeed.remix.service+json; version=1.0"
                },
                verify=addon_prefs.remix_verify_ssl
            )
            if not put_response or put_response.status_code not in [200, 201, 204]:
                logging.error("Failed to update shader input with ingested height texture.")
                return {'CANCELLED'}

            logging.info(f"Updated height texture for material '{material_name}' using prim: {height_shader_prim}")

        logging.info("Height texture processing for all materials completed successfully.")
        return {'FINISHED'}

    except Exception as e:
        logging.error(f"Error handling height textures: {e}")
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
   

class OBJECT_OT_import_usd_from_remix(Operator):
    bl_idname = "object.import_usd_from_remix"
    bl_label = "Import USD from Remix"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        addon_prefs = context.preferences.addons[__name__].preferences
        global remix_import_lock
        if remix_import_lock:
            self.report({'INFO'}, "Another USD import is already in progress.")
            logging.info("Another USD import is already in progress.")
            return {'CANCELLED'}

        if not is_blend_file_saved():
            popup_message = "Please save your Blender file before importing USD assets."
            logging.warning(popup_message)
            bpy.ops.object.show_popup('INVOKE_DEFAULT', message=popup_message, success=False)
            return {'CANCELLED'}

        remix_import_lock = True
        logging.debug("Lock acquired for USD import process.")

        try:
            assets_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/?selection=true&filter_session_assets=false&exists=true"
            logging.info(f"Fetching assets from Remix server: {assets_url}")

            response = make_request_with_retries(
                method='GET',
                url=assets_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )

            if not response or response.status_code != 200:
                self.report({'ERROR'}, "Failed to connect to the Remix server after multiple attempts.")
                logging.error("Failed to connect to the Remix server after multiple attempts.")
                return {'CANCELLED'}

            data = response.json()
            mesh_paths = [path for path in data.get("asset_paths", []) if "meshes" in path.lower()]
            logging.debug(f"Mesh Paths Retrieved: {mesh_paths}")

            if not mesh_paths:
                self.report({'WARNING'}, "Mesh assets not found in Remix server.")
                logging.warning("Mesh assets not found in Remix server.")
                return {'CANCELLED'}

            imported_objects = []
            base_dir = ""

            first_mesh_path = mesh_paths[0]
            trimmed_segments = first_mesh_path.split('/')[:4]
            trimmed_prim_path = '/'.join(trimmed_segments)
            logging.debug(f"Trimmed Prim Path: {trimmed_prim_path}")

            encoded_trimmed_path = urllib.parse.quote(trimmed_prim_path, safe='')
            logging.debug(f"Encoded Trimmed Prim Path: {encoded_trimmed_path}")

            file_paths_url = f"{addon_prefs.remix_server_url.rstrip('/')}/assets/{encoded_trimmed_path}/file-paths"
            logging.debug(f"Constructed File Paths URL: {file_paths_url}")

            response = make_request_with_retries(
                method='GET',
                url=file_paths_url,
                headers={'accept': 'application/lightspeed.remix.service+json; version=1.0'},
                verify=addon_prefs.remix_verify_ssl
            )

            if not response or response.status_code != 200:
                self.report({'ERROR'}, f"Failed to retrieve file paths for prim: {trimmed_prim_path}")
                logging.error(f"Failed to retrieve file paths for prim: {trimmed_prim_path}")
                return {'CANCELLED'}

            file_data = response.json()
            reference_paths = file_data.get("reference_paths", [])
            logging.debug(f"Reference Paths Retrieved: {reference_paths}")

            if not reference_paths:
                self.report({'WARNING'}, "No reference paths found in the Remix server response.")
                logging.warning("No reference paths found in the Remix server response.")
                return {'CANCELLED'}

            usd_paths = reference_paths[0][1] if len(reference_paths[0]) > 1 else []
            if len(usd_paths) < 2:
                self.report({'WARNING'}, "Insufficient file paths in the response.")
                logging.warning("Insufficient file paths in the response.")
                return {'CANCELLED'}

            existing_layer_id = usd_paths[1]
            base_dir = os.path.dirname(existing_layer_id).replace('\\', '/')
            logging.debug(f"Base Directory from Layer ID: {base_dir}")

            for mesh_path in mesh_paths:
                segments = mesh_path.strip('/').split('/')
                if len(segments) >= 3:
                    mesh_name = segments[2]
                    relative_usd_path = f"meshes/{mesh_name}.usd"
                    logging.debug(f"Relative USD Path: {relative_usd_path}")

                    usd_file = os.path.join(base_dir, relative_usd_path).replace('\\', '/')
                    logging.debug(f"Constructed USD File Path: {usd_file}")
                else:
                    logging.warning(f"Mesh path '{mesh_path}' does not have expected format.")
                    continue

                mesh_object_name = os.path.splitext(os.path.basename(usd_file))[0]
                existing_obj = bpy.data.objects.get(mesh_object_name)

                if existing_obj:
                    logging.info(f"Mesh '{mesh_object_name}' already exists in the scene. Skipping import.")
                    self.report({'INFO'}, f"Mesh '{mesh_object_name}' already exists. Skipping import.")
                    continue
                else:
                    logging.info(f"Mesh '{mesh_object_name}' does not exist. Proceeding with import.")
                    self.report({'INFO'}, f"Importing mesh '{mesh_object_name}'.")

                try:
                    bpy.ops.wm.usd_import(filepath=usd_file)
                    logging.info(f"Imported USD file: {usd_file}")

                    import_scale = addon_prefs.remix_import_scale
                    if import_scale != 1.0:
                        for obj in bpy.context.selected_objects:
                            obj.scale *= import_scale
                            obj.scale = tuple(round(s, 6) for s in obj.scale)
                            logging.debug(f"Applied import scale {import_scale} to object: {obj.name}")
                            print(f"Applied import scale {import_scale} to object: {obj.name}")

                    bpy.context.view_layer.update()

                    current_imported_objects = [obj for obj in bpy.context.selected_objects if obj.type == 'MESH']
                    imported_objects.extend(current_imported_objects)
                    logging.debug(f"Imported Objects: {[obj.name for obj in current_imported_objects]}")

                    if addon_prefs.mirror_import:
                        for obj in current_imported_objects:
                            logging.info(f"Mirroring object: {obj.name}")
                            print(f"Mirroring object: {obj.name}")
                            mirror_object(obj)

                    if addon_prefs.flip_normals_import:
                        for obj in current_imported_objects:
                            flip_normals_api(obj)
                            logging.debug(f"Flipped normals for imported object: {obj.name}")
                            print(f"Flipped normals for imported object: {obj.name}")
                        logging.info("Normals flipped for imported objects during import as per user setting.")
                        print("Normals flipped for imported objects during import as per user setting.")
                    else:
                        logging.info("Normals not flipped during import as per user setting.")
                        print("Normals not flipped during import as per user setting.")

                except Exception as e:
                    self.report({'ERROR'}, f"USD Import failed for '{mesh_object_name}': {e}")
                    logging.error(f"USD Import failed for '{mesh_object_name}': {e}")
                    continue

            if addon_prefs.remix_import_original_textures:
                logging.info("Import Original Textures option is enabled. Attaching original textures.")
                print("Import Original Textures option is enabled. Attaching original textures.")
                attach_original_textures(imported_objects, context, base_dir)

            self.report({'INFO'}, "USD import process completed successfully.")
            logging.info("USD import process completed successfully.")
            print("USD import process completed successfully.")
            return {'FINISHED'}

        except Exception as e:
            logging.error(f"Unexpected error during USD import: {e}")
            self.report({'ERROR'}, f"Unexpected error: {e}")
            return {'CANCELLED'}

        finally:
            remix_import_lock = False
            logging.debug("Lock released for USD import process.")
            
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
            export_scale = addon_prefs.remix_export_scale * 2.0

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

        usd_filename = os.path.splitext(os.path.basename(obj_path))[0] + ".usd"
        usd_output_path = os.path.join(meshes_subdir, usd_filename).replace('\\', '/')
        logging.debug(f"USD Output Path: {usd_output_path}")

        payload = {
            "executor": 1,
            "name": "Model(s)",
            "context_plugin": {
                "name": "AssetImporter",
                "data": {
                    "context_name": "ingestcraft",
                    "input_files": [abs_obj_path],
                    "output_directory": meshes_subdir,
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
            "check_plugins": [
                {
                    "name": "ClearUnassignedMaterial",
                    "selector_plugins": [
                        {
                            "name": "AllMeshes",
                            "data": {"include_geom_subset": True}
                        }
                    ],
                    "data": {},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "DefaultMaterial",
                    "selector_plugins": [
                        {"name": "AllMeshes", "data": {}}
                    ],
                    "data": {},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "MaterialShaders",
                    "selector_plugins": [
                        {"name": "AllMaterials", "data": {}}
                    ],
                    "data": {"shader_subidentifiers": {"AperturePBR_Translucent": "translucent|glass|trans", "AperturePBR_Opacity": ".*"}},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "ValueMapping",
                    "selector_plugins": [
                        {"name": "AllShaders", "data": {}}
                    ],
                    "data": {"attributes": {"inputs:emissive_intensity": [{"operator": "=", "input_value": 10000, "output_value": 1}]}},
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "ConvertToOctahedral",
                    "selector_plugins": [
                        {"name": "AllShaders", "data": {}}
                    ],
                    "resultor_plugins": [
                        {"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}}
                    ],
                    "data": {"data_flows": [{"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"}]},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "ConvertToDDS",
                    "selector_plugins": [
                        {"name": "AllShaders", "data": {}}
                    ],
                    "resultor_plugins": [
                        {"name": "FileCleanup", "data": {"channel": "cleanup_files", "cleanup_output": False}}
                    ],
                    "data": {
                        "data_flows": [
                            {"name": "InOutData", "push_input_data": True, "push_output_data": True, "channel": "cleanup_files"},
                            {"name": "InOutData", "push_output_data": True, "channel": "write_metadata"}
                        ]
                    },
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "RelativeAssetPaths",
                    "selector_plugins": [
                        {"name": "AllPrims", "data": {}}
                    ],
                    "data": {},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "RelativeReferences",
                    "selector_plugins": [
                        {"name": "AllPrims", "data": {}}
                    ],
                    "data": {},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "DependencyIterator",
                        "data": {"save_all_layers_on_exit": True, "close_dependency_between_round": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "WrapRootPrims",
                    "selector_plugins": [
                        {"name": "Nothing", "data": {}}
                    ],
                    "data": {"wrap_prim_name": "XForms"},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "CurrentStage",
                        "data": {"save_on_exit": True, "close_stage_on_exit": False}
                    }
                },
                {
                    "name": "WrapRootPrims",
                    "selector_plugins": [
                        {"name": "Nothing", "data": {}}
                    ],
                    "data": {"wrap_prim_name": "ReferenceTarget"},
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "CurrentStage",
                        "data": {"save_on_exit": True, "close_stage_on_exit": False}
                    }
                }
            ],
            "resultor_plugins": [
                {
                    "name": "FileCleanup",
                    "data": {"channel": "cleanup_files", "cleanup_output": False}
                },
                {
                    "name": "FileMetadataWritter",
                    "data": {"channel": "write_metadata"}
                }
            ]
        }

        logging.info(f"Uploading OBJ to {url}")
        # Limit retries to 1 to avoid duplicate attempts.
        response = make_request_with_retries('POST', url, json_payload=payload, verify=addon_prefs.remix_verify_ssl, retries=1)

        if response is None:
            logging.error("Failed to upload OBJ: No response from server.")
            return None

        if response.status_code == 500:
            try:
                response_data = response.json()
                detail = response_data.get("detail", "")
            except Exception:
                detail = ""
            if "The validation did not complete successfully" in detail:
                error_msg = "Please change the Ingest Directory to inside the Project folder."
                logging.error(error_msg)
                print("DEBUG:", error_msg)  # Debug line printed to console
                bpy.ops.object.show_popup('INVOKE_DEFAULT', message=error_msg, success=False)
                return None

        if response.status_code != 200:
            logging.error(f"Failed to upload OBJ. Status: {response.status_code}, Response: {response.text}")
            return None

        response_data = response.json()
        completed_schemas = response_data.get("completed_schemas", [])
        if not completed_schemas:
            logging.error("No completed schemas found in response.")
            return None

        output_files = completed_schemas[0].get("context_plugin", {}).get("data", {}).get("output_files", {})
        if output_files:
            usd_path_relative = next(iter(output_files.values()))
            usd_path = os.path.join(meshes_subdir, os.path.basename(usd_path_relative)).replace('\\', '/')
            logging.debug(f"Uploaded USD Path: {usd_path}")
            return usd_path
        else:
            logging.error("No USD path found in the response.")
            return None
    finally:
        pass

def check_blend_file_in_prims(blend_name, context):
    addon_prefs = context.preferences.addons[__name__].preferences
    try:
        server_url = addon_prefs.remix_server_url.rstrip('/')
        get_url = f"{server_url}/assets/?selection=false&filter_session_assets=false&exists=true"
        headers = {'accept': 'application/lightspeed.remix.service+json; version=1.0'}

        logging.info(f"Fetching prims from: {get_url}")
        response = make_request_with_retries('GET', get_url, headers=headers, verify=addon_prefs.remix_verify_ssl)

        if not response or response.status_code != 200:
            logging.error("Failed to fetch prims from Remix server.")
            return None, None

        asset_paths = response.json().get("asset_paths", [])
        logging.debug(f"Retrieved asset paths: {asset_paths}")

        if addon_prefs.remix_use_custom_name and addon_prefs.remix_use_selection_only and addon_prefs.remix_base_obj_name:
            base_name = addon_prefs.remix_base_obj_name
            logging.debug(f"Using custom base OBJ name for prim search: {base_name}")
        else:
            base_name = extract_base_name(blend_name)
            logging.debug(f"Using blend file base name for prim search: {base_name}")

        for path in asset_paths:
            segments = path.strip('/').split('/')
            if any(base_name.lower() in segment.lower() for segment in segments):
                logging.info(f"Prim with base name found: {path}")
                print(f"Prim with base name found: {path}")

                prim_path = '/' + '/'.join(segments)

                reference_prim_path = None
                for i, segment in enumerate(segments):
                    if segment.lower().startswith('ref_'):
                        reference_prim_path = '/' + '/'.join(segments[:i + 1])
                        break

                if reference_prim_path:
                    logging.info(f"Reference prim identified: {reference_prim_path}")
                    print(f"Reference prim identified: {reference_prim_path}")
                    return prim_path, reference_prim_path
                else:
                    logging.warning(f"No 'ref_' segment found in path: {path}")
                    print(f"No 'ref_' segment found in path: {path}")

        logging.info(f"No reference prim found with base name '{base_name}'.")
        return None, None

    except Exception as e:
        logging.error(f"Error checking prims: {e}")
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
        export_box.operator("object.export_and_ingest", text="Export and Ingest")

        import_box = layout.box()
        import_box.label(text="USD Import", icon='IMPORT')
        import_box.prop(addon_prefs, "mirror_import", text="Mirror on Import")
        import_box.prop(addon_prefs, "flip_normals_import", text="Flip Normals During Import")
        import_box.prop(addon_prefs, "remix_import_scale", text="Import Scale")
        import_box.prop(addon_prefs, "remix_import_original_textures", text="Import Original Textures")
        import_box.operator("object.import_usd_from_remix", text="Import USD from Remix")

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
    OBJECT_OT_reset_options,
    OBJECT_OT_show_popup,
    VIEW3D_PT_remix_ingestor,
    OBJECT_OT_info_operator,
    OBJECT_OT_toggle_info_display,
    AssetNumberItem,
    CustomSettingsBackup
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
