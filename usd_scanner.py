# THIS IS THE CORRECTED CONTENT FOR YOUR 'usd_scanner.py' FILE

import numpy as np
import sys
import traceback
import hashlib

try:
    from pxr import Usd, UsdGeom, Gf, UsdShade
except ImportError:
    Usd = None

def scan_and_extract_data_for_file(usd_file_path):
    """
    WORKER (V14 - DEDUPLICATION HASH): This version calculates a unique hash for
    each mesh based on its geometry, transform, and material. This allows the
    main addon to detect and skip importing duplicate meshes.
    """
    if Usd is None:
        print(f"FATAL WORKER ERROR: The 'pxr' library could not be imported.", file=sys.stderr)
        return None, []

    extracted_data = []
    up_axis = None
    try:
        stage = Usd.Stage.Open(usd_file_path)
        if not stage:
            print(f"WORKER ERROR: Could not open USD stage for file {usd_file_path}", file=sys.stderr)
            return None, []

        up_axis = stage.GetMetadata('upAxis')

        for prim in stage.TraverseAll():
            if not prim.IsA(UsdGeom.Mesh):
                continue

            imageable = UsdGeom.Imageable(prim)
            if imageable.ComputeVisibility(Usd.TimeCode.Default()) == UsdGeom.Tokens.invisible:
                continue
            
            purpose = imageable.ComputePurpose()
            if purpose != UsdGeom.Tokens.default_ and purpose != UsdGeom.Tokens.render:
                continue

            parent_name = ""
            parent_prim = prim.GetParent()
            if parent_prim and parent_prim.IsValid() and not parent_prim.IsPseudoRoot():
                parent_name = parent_prim.GetName()

            uv_data_np = None
            found_uv_set = None
            uv_interpolation = None

            primvars_api = UsdGeom.PrimvarsAPI(prim)
            
            st_primvar = primvars_api.GetPrimvar("st")
            if st_primvar and st_primvar.IsDefined() and st_primvar.GetInterpolation() in [UsdGeom.Tokens.faceVarying, UsdGeom.Tokens.vertex]:
                found_uv_set = st_primvar
            else:
                for primvar in primvars_api.GetPrimvars():
                    if primvar.GetInterpolation() in [UsdGeom.Tokens.faceVarying, UsdGeom.Tokens.vertex] and "vec2f" in str(primvar.GetTypeName()).lower():
                        found_uv_set = primvar
                        break
            
            if found_uv_set:
                uv_interpolation = found_uv_set.GetInterpolation()
                uv_values = found_uv_set.Get()
                if uv_values:
                    uv_data_np = np.array(uv_values, dtype=np.float32)
                    if uv_data_np.ndim == 2 and uv_data_np.shape[1] >= 2:
                        uv_data_np[:, 1] = 1.0 - uv_data_np[:, 1]

            mesh = UsdGeom.Mesh(prim)
            vertices_attr = mesh.GetPointsAttr().Get()
            if not vertices_attr: continue
            face_indices_attr = mesh.GetFaceVertexIndicesAttr().Get()
            face_counts_attr = mesh.GetFaceVertexCountsAttr().Get()
            if not face_indices_attr or not face_counts_attr: continue

            verts_co_np = np.array(vertices_attr, dtype=np.float32)
            loop_verts_np = np.array(face_indices_attr, dtype=np.int32)
            face_counts_np = np.array(face_counts_attr, dtype=np.int32)
            loop_starts_np = np.zeros(len(face_counts_np), dtype=np.int32)
            np.cumsum(face_counts_np, out=loop_starts_np)
            loop_starts_np[1:] = loop_starts_np[:-1]
            loop_starts_np[0] = 0
            xformable = UsdGeom.Xformable(prim)
            world_transform_matrix = xformable.ComputeLocalToWorldTransform(Usd.TimeCode.Default())
            material_path_str = ""
            try:
                prim_to_check = prim
                if prim.IsInstance():
                    prototype = prim.GetPrototype()
                    if prototype: prim_to_check = prototype
                found_material = None
                current_prim = prim_to_check
                while current_prim and current_prim.IsValid():
                    binding_api = UsdShade.MaterialBindingAPI(current_prim)
                    binding = binding_api.GetDirectBinding()
                    material = binding.GetMaterial()
                    if material and material.GetPrim().IsValid():
                        found_material = material
                        break
                    current_prim = current_prim.GetParent()
                if found_material: material_path_str = str(found_material.GetPath())
            except Exception as e:
                print(f"[Worker DBG]   > !!! CRITICAL ERROR during material lookup for prim {prim.GetPath()}: {e}", file=sys.stderr)

            # --- NEW: Generate the unique content hash ---
            hasher = hashlib.md5()
            hasher.update(verts_co_np.tobytes())
            hasher.update(loop_verts_np.tobytes())
            hasher.update(np.array(world_transform_matrix).tobytes())
            hasher.update(material_path_str.encode('utf-8'))
            mesh_hash = hasher.hexdigest()
            # --- END NEW ---

            extracted_data.append({
                "mesh_hash": mesh_hash, # <-- NEW: Pass the hash back
                "name": prim.GetName(),
                "parent_name": parent_name,
                "prim_path": str(prim.GetPath()),
                "usd_file_path": usd_file_path,
                "matrix_world": [list(row) for row in world_transform_matrix],
                "material_path": material_path_str,
                "counts": { "verts": len(verts_co_np), "faces": len(face_counts_np), "loops": len(loop_verts_np)},
                "verts_co": verts_co_np, "loop_verts": loop_verts_np,
                "loop_starts": loop_starts_np, "loop_totals": face_counts_np,
                "uvs": uv_data_np,
                "uv_interpolation": uv_interpolation
            })
    except Exception as e:
        print(f"Error processing file {usd_file_path} in worker: {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
    return up_axis, extracted_data
