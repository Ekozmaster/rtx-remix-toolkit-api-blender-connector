bl_info = {
    "name": "Remix Asset Ingestor",
    "blender": (4, 3, 0),
    "category": "Object",
    "version": (1, 0, 0),
    "author": "Your Name",
    "description": "Export mesh assets as OBJ, ingest into Remix with versioning, and handle textures.",
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
from bpy.props import BoolProperty, StringProperty
from bpy.types import Operator, Panel, PropertyGroup
from bpy.props import CollectionProperty, IntProperty
import urllib.parse

# Initialize global variables
log_file_path = ""
export_lock = False  # To prevent concurrent exports

class AssetNumberItem(PropertyGroup):
    blend_name: StringProperty(name="Blend File Name")
    asset_number: IntProperty(name="Asset Number", default=1)

def setup_logger():
    """Set up the logger to avoid duplicate handlers."""
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
            level=logging.DEBUG  # Set to DEBUG for detailed logs
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

def get_blend_filename():
    """Return the name of the current .blend file without extension."""
    blend_file = bpy.path.basename(bpy.data.filepath)
    blend_name, _ = os.path.splitext(blend_file)
    return blend_name if blend_name else "untitled"

def get_asset_number(context):
    """Retrieve and increment the asset number for the current blend file."""
    blend_name = get_blend_filename()

    # Initialize asset number for the blend file if not present
    for item in context.scene.remix_asset_number:
        if item.blend_name == blend_name:
            asset_number = item.asset_number
            item.asset_number += 1
            logging.debug(f"Asset number for blend '{blend_name}': {asset_number}")
            return asset_number

    # If blend_name not found, add a new entry
    new_item = context.scene.remix_asset_number.add()
    new_item.blend_name = blend_name
    new_item.asset_number = 2  # Next asset will be 2
    logging.debug(f"Asset number for blend '{blend_name}': 1")
    return 1

def write_obj(filepath, objects, use_selection=True):
    """Export selected objects to an OBJ file."""
    try:
        filepath = os.path.abspath(filepath)
        logging.debug(f"Writing OBJ file to: {filepath}")

        with open(filepath, 'w') as f:
            vertex_offset = 0
            for obj in objects:
                if use_selection and not obj.select_get():
                    continue
                if obj.type != 'MESH':
                    continue
                mesh = obj.data
                f.write(f'o {obj.name}\n')
                for vert in mesh.vertices:
                    transformed_coord = obj.matrix_world @ vert.co
                    rotated_x = transformed_coord.x
                    rotated_y = transformed_coord.z
                    rotated_z = -transformed_coord.y
                    f.write(f'v {rotated_x} {rotated_y} {rotated_z}\n')
                for poly in mesh.polygons:
                    vertices = [v + 1 + vertex_offset for v in poly.vertices]
                    face = ' '.join(map(str, vertices))
                    f.write(f'f {face}\n')
                vertex_offset += len(mesh.vertices)
        logging.info(f"OBJ file written successfully at {filepath}.")
        return True
    except IOError as e:
        logging.error(f"Failed to write OBJ file at {filepath}: {e}")
        return False
    except Exception as e:
        logging.error(f"Unexpected error while writing OBJ file: {e}")
        return False

def make_request_with_retries(method, url, headers=None, data=None, json_payload=None, retries=3, delay=5, **kwargs):
    """Make an HTTP request with retry logic."""
    for attempt in range(1, retries + 1):
        try:
            if method.upper() == 'GET':
                response = requests.get(url, headers=headers, timeout=60, **kwargs)
            elif method.upper() == 'POST':
                response = requests.post(url, headers=headers, data=data, json=json_payload, timeout=60, **kwargs)
            elif method.upper() == 'PUT':
                response = requests.put(url, headers=headers, data=data, json=json_payload, timeout=60, **kwargs)
            else:
                logging.error(f"Unsupported HTTP method: {method}")
                return None

            if response.status_code == 200:
                return response
            else:
                logging.warning(f"Attempt {attempt} failed with status code {response.status_code}. Response: {response.text}")
        except requests.exceptions.RequestException as e:
            logging.warning(f"Attempt {attempt} encountered an exception: {e}")

        if attempt < retries:
            logging.info(f"Retrying in {delay} seconds...")
            time.sleep(delay)

    logging.error(f"All {retries} attempts failed for {method} {url}")
    return None

def upload_to_api(filepath, ingest_directory, context):
    """Upload the OBJ file to the Remix API and return the prim path based on the file name."""
    try:
        url = context.scene.remix_export_url.rstrip('/')
        payload = {
            "executor": 1,
            "name": os.path.basename(filepath),
            "context_plugin": {
                "name": "AssetImporter",
                "data": {
                    "context_name": "ingestcraft",
                    "input_files": [os.path.abspath(filepath)],
                    "output_directory": os.path.abspath(ingest_directory),
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
                    "name": "MaterialShaders",
                    "selector_plugins": [
                        {
                            "name": "AllMaterials",
                            "data": {}
                        }
                    ],
                    "data": {
                        "shader_subidentifiers": {
                            "AperturePBR_Opacity": ".*"
                        }
                    },
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "CurrentStage",
                        "data": {}
                    }
                }
            ],
            "resultor_plugins": [
                {
                    "name": "FileMetadataWritter",
                    "data": {
                        "channel": "write_metadata"
                    }
                }
            ]
        }

        logging.info(f"Uploading OBJ {filepath} to {url} with payload: {payload}")
        response = make_request_with_retries('POST', url, json_payload=payload, verify=context.scene.remix_verify_ssl)

        if response is None or response.status_code != 200:
            logging.error(f"Failed to upload OBJ. Status code: {response.status_code if response else 'No Response'}, Response: {response.text if response else 'No Response'}")
            return False

        # Log the full API response for debugging
        try:
            response_data = response.json()
            logging.debug(f"Full OBJ upload response: {response_data}")
        except Exception as e:
            logging.error(f"Failed to parse OBJ upload response as JSON: {e}")
            return False

        # Extract the prim path from the response
        try:
            completed_schemas = response_data.get("completed_schemas", [])
            if not completed_schemas:
                logging.error("No completed schemas found in OBJ upload response.")
                return False

            # Inspect the first schema for prim path details
            obj_schema = completed_schemas[0]
            
            # Extract the output USD file path from 'context_plugin.data.output_files'
            context_plugin = obj_schema.get("context_plugin", {})
            data = context_plugin.get("data", {})
            output_files = data.get("output_files", {})
            if not output_files:
                logging.error("Output files not found in OBJ upload response.")
                return False

            # Assuming only one input-output pair
            output_usd_path = list(output_files.values())[0]
            output_usd_filename = os.path.basename(output_usd_path)  # e.g., 'Bridge.usd'

            # Construct the prim path using the file name
            prim_path = f"/RootNode/meshes/{output_usd_filename}"
            logging.info(f"Constructed OBJ prim path: {prim_path}")
            return prim_path  # Return the full prim path

        except Exception as e:
            logging.error(f"Error extracting prim path from OBJ upload response: {e}")
            return False

    except Exception as e:
        logging.error(f"Error during OBJ API upload: {e}")
        return False

def attach_mesh_reference(selected_mesh_path, ingested_mesh_path):
    """Attach the ingested mesh as a reference to the selected mesh in Remix."""
    try:
        # Ensure the base URL ends with a slash
        base_url = "http://127.0.0.1:8011/stagecraft/assets/"
        # Encode the entire prim path including the leading '/'
        encoded_prim_path = urllib.parse.quote(selected_mesh_path)
        mesh_url = f"{base_url}{encoded_prim_path}/file-paths"

        payload = {
            "force": False,
            "references": [ingested_mesh_path]  # Assuming the API accepts a list of prim paths to reference
        }

        logging.info(f"Attaching mesh reference to: {mesh_url} with payload: {payload}")
        headers = {
            'accept': 'application/lightspeed.remix.service+json; version=1.0',
            'Content-Type': 'application/lightspeed.remix.service+json; version=1.0'
        }
        response = make_request_with_retries('PUT', mesh_url, json_payload=payload, headers=headers, verify=True)

        if response is None or response.status_code != 200:
            logging.error(f"Failed to attach mesh reference. Status code: {response.status_code if response else 'No Response'}, Response: {response.text if response else 'No Response'}")
            return False
        logging.info("Mesh reference attached successfully.")
        return True
    except Exception as e:
        logging.error(f"Error attaching mesh reference: {e}")
        return False

def upload_texture_to_api(texture_path, ingest_directory, context):
    """Upload a single texture file to the Remix API and return its prim path based on the file name."""
    try:
        url = "http://127.0.0.1:8011/ingestcraft/mass-validator/queue/material"

        texture_name = os.path.basename(texture_path)
        texture_type = determine_texture_type(texture_name)

        payload = {
            "executor": 1,
            "name": texture_name,
            "context_plugin": {
                "name": "TextureImporter",
                "data": {
                    "context_name": "ingestcraft",
                    "input_files": [(os.path.abspath(texture_path), texture_type)],  # Use a tuple
                    "output_directory": os.path.abspath(ingest_directory),
                    "allow_empty_input_files_list": True,
                    "data_flows": [
                        {
                            "name": "InOutData",
                            "push_input_data": True
                        }
                    ],
                    "hide_context_ui": True,
                    "create_context_if_not_exist": True,
                    "expose_mass_ui": True,
                    "cook_mass_template": True
                }
            },
            "check_plugins": [
                {
                    "name": "MaterialShaders",
                    "selector_plugins": [
                        {
                            "name": "AllMaterials",
                            "data": {}
                        }
                    ],
                    "data": {
                        "shader_subidentifiers": {
                            "AperturePBR_Opacity": ".*"
                        }
                    },
                    "stop_if_fix_failed": True,
                    "context_plugin": {
                        "name": "CurrentStage",
                        "data": {}
                    }
                }
            ],
            "resultor_plugins": [
                {
                    "name": "FileMetadataWritter",
                    "data": {
                        "channel": "write_metadata"
                    }
                }
            ]
        }

        logging.info(f"Uploading texture {texture_path} to {url} with payload: {payload}")
        response = make_request_with_retries('POST', url, json_payload=payload, verify=context.scene.remix_verify_ssl)

        if response is None or response.status_code != 200:
            logging.error(f"Failed to upload texture {texture_path}. Status code: {response.status_code if response else 'No Response'}, Response: {response.text if response else 'No Response'}")
            return False

        # Log the full API response for debugging
        try:
            response_data = response.json()
            logging.debug(f"Full texture upload response: {response_data}")
        except Exception as e:
            logging.error(f"Failed to parse texture upload response as JSON: {e}")
            return False

        # Extract the prim path from the response
        try:
            completed_schemas = response_data.get("completed_schemas", [])
            if not completed_schemas:
                logging.error("No completed schemas found in texture upload response.")
                return False

            # Inspect the first schema for prim path details
            texture_schema = completed_schemas[0]
            # The 'name_tooltip' contains the full path to the texture file
            name_tooltip = texture_schema.get("data", {}).get("name_tooltip")
            if not name_tooltip:
                logging.error("name_tooltip not found in texture upload response.")
                return False

            # Extract the file name from 'name_tooltip'
            texture_filename = os.path.basename(name_tooltip)  # e.g., 'DiamondPlate008C_2K-PNG_Color.png'

            # Construct the prim path using the file name
            prim_path = f"/RootNode/textures/{texture_filename}"
            logging.info(f"Constructed texture prim path: {prim_path}")
            return prim_path  # Return the full prim path

        except Exception as e:
            logging.error(f"Error extracting prim path from texture upload response: {e}")
            return False

    except Exception as e:
        logging.error(f"Error during texture API upload: {e}")
        return False

def determine_texture_type(texture_name):
    """Determine the texture type based on the texture name."""
    texture_name = texture_name.lower()
    if 'color' in texture_name or 'diffuse' in texture_name:
        return 'DIFFUSE'
    elif 'roughness' in texture_name:
        return 'ROUGHNESS'
    elif 'normal' in texture_name:
        return 'NORMAL_OGL'
    elif 'metallic' in texture_name:
        return 'METALLIC'
    elif 'emissive' in texture_name:
        return 'EMISSIVE'
    elif 'height' in texture_name or 'displacement' in texture_name:
        return 'HEIGHT'
    elif 'transmittance' in texture_name:
        return 'TRANSMITTANCE'
    else:
        return 'OTHER'

def attach_textures_to_mesh(selected_mesh_path, texture_prim_paths):
    """Attach textures to the mesh using the provided prim path."""
    try:
        base_url = "http://127.0.0.1:8011/stagecraft/assets/"
        encoded_prim_path = urllib.parse.quote(selected_mesh_path)
        texture_url = f"{base_url}{encoded_prim_path}/file-paths"

        payload = {
            "force": False,
            "textures": []
        }

        for texture_name, prim_path in texture_prim_paths.items():
            texture_type = determine_texture_type(texture_name)
            payload["textures"].append({
                "asset_file_path": prim_path,
                "type": texture_type
            })

        logging.info(f"Attaching textures to: {texture_url} with payload: {payload}")
        headers = {
            'accept': 'application/lightspeed.remix.service+json; version=1.0',
            'Content-Type': 'application/lightspeed.remix.service+json; version=1.0'
        }
        response = make_request_with_retries('PUT', texture_url, json_payload=payload, headers=headers, verify=True)

        if response is None or response.status_code != 200:
            logging.error(f"Failed to attach textures. Status code: {response.status_code if response else 'No Response'}, Response: {response.text if response else 'No Response'}")
            return False
        logging.info("Textures attached successfully.")
        return True
    except Exception as e:
        logging.error(f"Error attaching textures to mesh: {e}")
        return False

def ingest_textures(mesh_objects, ingest_directory, context):
    """Ingest textures associated with the mesh objects."""
    try:
        texture_prim_paths = {}  # Dictionary to store texture name to prim path mapping

        for obj in mesh_objects:
            for slot in obj.material_slots:
                if slot.material and slot.material.use_nodes:
                    for node in slot.material.node_tree.nodes:
                        if node.type == 'TEX_IMAGE' and node.image:
                            texture_path = bpy.path.abspath(node.image.filepath)
                            if not os.path.exists(texture_path):
                                logging.warning(f"Texture file does not exist: {texture_path}")
                                continue

                            logging.info(f"Ingesting texture from: {texture_path}")
                            prim_path = upload_texture_to_api(texture_path, ingest_directory, context)
                            if prim_path:
                                texture_name = os.path.basename(texture_path)
                                texture_prim_paths[texture_name] = prim_path
                                logging.info(f"Successfully ingested texture: {texture_path}")
                            else:
                                logging.error(f"Failed to ingest texture: {texture_path}")
        logging.info("Texture ingestion completed.")
        return texture_prim_paths  # Return the mapping for later use
    except Exception as e:
        logging.error(f"Error during texture ingestion: {e}")
        return {}

class OBJECT_OT_export_and_ingest(Operator):
    bl_idname = "object.export_and_ingest"
    bl_label = "Export and Ingest Selected Objects"
    bl_options = {'REGISTER', 'UNDO'}

    use_selection: BoolProperty(
        name="Selection Only",
        description="Export only selected objects",
        default=True
    )

    def execute(self, context):
        global export_lock
        if export_lock:
            self.report({'INFO'}, "Another export is already in progress.")
            logging.info("Another export is already in progress.")
            return {'CANCELLED'}

        export_lock = True
        logging.debug("Lock acquired for export process.")

        try:
            blend_name = get_blend_filename()
            ingest_directory = bpy.path.abspath(context.scene.remix_ingest_directory)

            if not ingest_directory:
                self.report({'ERROR'}, "Ingest Directory is not set.")
                logging.error("Ingest Directory is not set.")
                export_lock = False
                return {'CANCELLED'}

            if not os.path.exists(ingest_directory):
                self.report({'ERROR'}, f"Ingest Directory does not exist: {ingest_directory}")
                logging.error(f"Ingest Directory does not exist: {ingest_directory}")
                export_lock = False
                return {'CANCELLED'}

            asset_number = get_asset_number(context)
            obj_name = f"{blend_name}_{asset_number}.obj"

            temp_dir = tempfile.gettempdir()
            temp_filepath = os.path.join(temp_dir, obj_name)
            logging.info(f"Temporary OBJ filepath: {temp_filepath}")

            if self.use_selection:
                objects = context.selected_objects
            else:
                objects = context.scene.objects

            mesh_objects = [obj for obj in objects if obj.type == 'MESH']

            if not mesh_objects:
                self.report({'WARNING'}, "No mesh objects found to export.")
                logging.warning("No mesh objects found to export.")
                export_lock = False
                return {'CANCELLED'}

            success = write_obj(temp_filepath, mesh_objects, self.use_selection)
            if not success:
                self.report({'ERROR'}, "Failed to export OBJ. Check the log for details.")
                logging.error("Failed to export OBJ.")
                export_lock = False
                return {'CANCELLED'}

            self.report({'INFO'}, f"Exported OBJ to temporary file: {temp_filepath}")
            logging.info(f"Exported OBJ to temporary file: {temp_filepath}")

            # Upload the OBJ and get the full prim path
            ingested_mesh_prim_path = upload_to_api(temp_filepath, ingest_directory, context)
            if not ingested_mesh_prim_path:
                self.report({'ERROR'}, "Failed to ingest OBJ into Remix.")
                logging.error("Failed to ingest OBJ into Remix.")
                export_lock = False
                return {'CANCELLED'}

            # Ingest textures and get their prim paths
            texture_prim_paths = ingest_textures(mesh_objects, ingest_directory, context)

            # Now, attach the ingested mesh as a reference using the correct prim path
            mesh_attachment_success = attach_mesh_reference(ingested_mesh_prim_path, ingested_mesh_prim_path)
            if not mesh_attachment_success:
                self.report({'ERROR'}, "Failed to attach ingested mesh as a reference.")
                logging.error("Failed to attach ingested mesh as a reference.")

            if texture_prim_paths:
                textures_attachment_success = attach_textures_to_mesh(ingested_mesh_prim_path, texture_prim_paths)
                if not textures_attachment_success:
                    self.report({'WARNING'}, "Failed to attach some or all textures to the mesh.")
                    logging.warning("Failed to attach some or all textures to the mesh.")
            else:
                logging.warning("No textures to attach.")

            try:
                os.remove(temp_filepath)
                logging.info(f"Deleted temporary OBJ file: {temp_filepath}")
            except Exception as e:
                logging.error(f"Failed to delete temporary OBJ file: {temp_filepath}. Error: {e}")

            self.report({'INFO'}, "Export and Ingest process completed.")
            return {'FINISHED'}

        except Exception as e:
            logging.error(f"Unexpected error during export and ingest: {e}")
            self.report({'ERROR'}, f"Unexpected error: {e}")
            return {'CANCELLED'}

        finally:
            export_lock = False
            logging.debug("Lock released for export process.")

class VIEW3D_PT_remix_ingestor(Panel):
    bl_label = "Remix Asset Ingestor"
    bl_idname = "VIEW3D_PT_remix_ingestor"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'Remix Ingestor'

    def draw(self, context):
        layout = self.layout
        scene = context.scene

        box = layout.box()
        box.label(text="Server Configuration", icon='WORLD')
        box.prop(scene, "remix_server_url", text="Server URL")
        box.prop(scene, "remix_export_url", text="Export API URL")
        box.prop(scene, "remix_verify_ssl", text="Verify SSL Certificates")

        box = layout.box()
        box.label(text="Ingest Settings", icon='EXPORT')
        box.prop(scene, "remix_use_selection_only", text="Export Selected Objects Only")
        box.prop(scene, "remix_ingest_directory", text="Ingest Directory")
        box.operator(OBJECT_OT_export_and_ingest.bl_idname, text="Export and Ingest Selected Objects")

        box = layout.box()
        box.label(text="Logging", icon='FILE_SCRIPT')
        row = box.row()
        row.label(text="Log File:")
        row.label(text=log_file_path, icon='FILE_TEXT')

def register():
    global log_file_path

    setup_logger()

    bpy.utils.register_class(AssetNumberItem)

    classes = [
        OBJECT_OT_export_and_ingest,
        VIEW3D_PT_remix_ingestor,
    ]

    for cls in classes:
        bpy.utils.register_class(cls)

    bpy.types.Scene.remix_asset_number = CollectionProperty(type=AssetNumberItem)

    bpy.types.Scene.remix_server_url = StringProperty(
        name="Server URL",
        description="URL of the Remix server (e.g., http://localhost:8011/stagecraft). Do not include '/assets/' at the end.",
        default="http://localhost:8011/stagecraft",
        subtype='NONE'
    )
    bpy.types.Scene.remix_export_url = StringProperty(
        name="Export API URL",
        description="URL of the Export API (e.g., http://localhost:8011/ingestcraft/mass-validator/queue/model).",
        default="http://localhost:8011/ingestcraft/mass-validator/queue/model",
        subtype='NONE'
    )
    bpy.types.Scene.remix_verify_ssl = BoolProperty(
        name="Verify SSL",
        description="Verify SSL certificates when connecting to the server",
        default=True
    )
    bpy.types.Scene.remix_use_selection_only = BoolProperty(
        name="Export Selected Objects Only",
        description="Export only selected objects",
        default=True
    )
    bpy.types.Scene.remix_ingest_directory = StringProperty(
        name="Ingest Directory",
        description="Directory on the server to ingest assets and textures (e.g., /LegoStarWars/ProjectFolder/testExport/test)",
        default="/LegoStarWars/ProjectFolder/testExport/test",
        subtype='DIR_PATH'
    )

def unregister():
    classes = [
        VIEW3D_PT_remix_ingestor,
        OBJECT_OT_export_and_ingest,
    ]
    for cls in classes:
        bpy.utils.unregister_class(cls)

    bpy.utils.unregister_class(AssetNumberItem)

    del bpy.types.Scene.remix_server_url
    del bpy.types.Scene.remix_export_url
    del bpy.types.Scene.remix_verify_ssl
    del bpy.types.Scene.remix_use_selection_only
    del bpy.types.Scene.remix_ingest_directory
    del bpy.types.Scene.remix_asset_number

if __name__ == "__main__":
    register()