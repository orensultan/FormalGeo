import os
import shutil


path = "."
destination_folder = os.path.join(".", "diagrams")
files_to_keep = []
for filename in os.listdir(path):
    if filename.endswith(".txt"):
        suffix = filename.split("problem_")[1]
        new_suffix = suffix.split(".txt")[0] + ".png"
        files_to_keep.append(new_suffix)

for filename in os.listdir(destination_folder):
    if filename not in files_to_keep:
        os.remove(os.path.join(destination_folder, filename))


