--- START OF FILE usd_scanner.py ---

# FILE 1: usd_scanner.py (High-Performance Worker Module)
# This module contains a "pure" worker function that does NOT import `bpy`.
# It is designed to be called by `multiprocessing` from the main addon.

import numpy as np

try:
    # These libraries are imported in the separate lightweight worker process.
    from pxr import Usd, UsdGeom, Gf, UsdShade
except ImportError:
    # This allows the main addon to import the file without error, even if the
    # user doesn't have the USD SDK installed in Blender's python yet.
    # The error will be gracefully handled during the import process itself.
    Usd = None

def scan_and_extract_data_for_file(usd_file_path):
    """
    WORKER (PURE): Scans a single USD file, finds valid meshes, and returns
    their full geometry data (as numpy arrays) and metadata in a list.
    This function must NOT use the `bpy` API.
    """
    if Usd is None:
        # This message will appear in the console if the worker process fails to import pxr
        print(f"FATAL WORKER ERROR: The 'pxr' library could not be imported in the worker process for file {usd_file_path}.")
        return []

    extracted_data = []
    try:
        stage = Usd.Stage.Open(usd_file_path)
        if not stage:
            return []

        for prim in stage.TraverseAll():
            # Standard visibility and purpose filtering
            if not prim.IsA(UsdGeom.Mesh): continue
            imageable = UsdGeom.Imageable(prim)
            if imageable.ComputeVisibility(Usd.TimeCode.Default()) == UsdGeom.Tokens.invisible: continue
            purpose = imageable.ComputePurpose()
            if purpose != UsdGeom.Tokens.default_ and purpose != UsdGeom.Tokens.render: continue

            mesh = UsdGeom.Mesh(prim)
            vertices_attr = mesh.GetPointsAttr().Get()
            if not vertices_attr: continue

            face_indices_attr = mesh.GetFaceVertexIndicesAttr().Get()
            face_counts_attr = mesh.GetFaceVertexCountsAttr().Get()
            if not face_indices_attr or not face_counts_attr: continue

            # --- Data Extraction into NumPy arrays ---
            verts_co_np = np.array(vertices_attr, dtype=np.float32)
            loop_verts_np = np.array(face_indices_attr, dtype=np.int32)
            face_counts_np = np.array(face_counts_attr, dtype=np.int32)

            # Efficiently calculate loop starts
            loop_starts_np = np.zeros(len(face_counts_np), dtype=np.int32)
            np.cumsum(face_counts_np, out=loop_starts_np)
            # Shift the array to get the correct start indices
            loop_starts_np[1:] = loop_starts_np[:-1]
            loop_starts_np[0] = 0

            xformable = UsdGeom.Xformable(prim)
            world_transform_matrix = xformable.ComputeLocalToWorldTransform(Usd.TimeCode.Default())

            # Extract material binding if available
            material_path_str = ""
            try:
                material_binding_api = UsdShade.MaterialBindingAPI(prim)
                material = material_binding_api.GetDirectBinding().GetMaterial()
                if material:
                    material_path_str = str(material.GetPath())
            except Exception:
                pass # Silently ignore if no material is bound

            # Package all data. NumPy arrays will be sent efficiently back to the main process.
            extracted_data.append({
                "name": prim.GetName(),
                "matrix_world": [list(row) for row in world_transform_matrix],
                "material_path": material_path_str,
                "counts": {
                    "verts": len(verts_co_np),
                    "faces": len(face_counts_np),
                    "loops": len(loop_verts_np),
                },
                "verts_co": verts_co_np,
                "loop_verts": loop_verts_np,
                "loop_starts": loop_starts_np,
                "loop_totals": face_counts_np,
            })
    except Exception as e:
        print(f"Error processing file {usd_file_path} in worker: {e}")
        pass

    return extracted_data