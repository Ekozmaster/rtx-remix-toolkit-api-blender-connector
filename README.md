# rtx-remix-toolkit-api-blender-connector
This addon speeds up transferring assets between Blender and Remix both ways. With the export function, your desired objects will be exported, ingested and added to your selected object in Remix with one button. There is an automatic versioning system so your old version will be replaced with your latest. All textures will be ingested and added to your meshes in Remix. There is an Import from Remix button which has the option of importing the original textures and applying them as well. You can select multiple objects in Remix to import them. This addon is designed so you don't have to do any transforms like scaling to flip normals or mirroring on import. Any problems feel free to message me or go to the community contributions thread!


Installation!!

Simply go to Edit-Preferences-Add-On-Install-from-Disk, then find SimpleRemix19.zip you downloaded. Done! Latest toolkit version from Github is needed for latest bug fixes as of 12/12/24.

Usage

Importing
Select all the meshes you want to import in Remix by holding shift. Press import.

Export
Select the mesh you want to attach the new mesh to. Press export. The add-on will export the OBJ, ingest it, add it as a reference, ingest any height textures, add them to the correct mesh in Remix.
If the mesh in Remix is a past version, it will be replaced instead. Make sure to name your meshes different names to others in your scene or they will be replaced instead!

![image](https://github.com/user-attachments/assets/d287cd8f-5c02-4255-97a0-7070c3d12896)
