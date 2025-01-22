import os
import shutil

chosen_problems_by_level = {
    1: [2833, 1975, 1490, 1726, 178, 2669],
    2: [6523, 2141, 69, 2916, 358, 4473],
    3: [2999, 4187, 5244, 5062, 844, 1945],
    4: [2425, 2114, 464, 5510, 3272, 5230],
    5: [4908, 5440, 6485, 696, 847, 5563],
    6: [729, 4923, 3298, 759, 4910, 5805],
    7: [683, 3580, 4898, 6802, 6247, 449],
    8: [912, 3983, 2761, 2875, 3434, 6806],
    9: [5749, 4892, 5092, 5522, 4796, 3418]
}

diagrams_path = "../../formalgeo7k_v1/formalgeo7k_v1/diagrams/"
problems_path = "../../formalgeo7k_v1/formalgeo7k_v1/problems/"
diagrams_path_dest = "../../formalgeo7k_v1/formalgeo7k_v1/chosen_problems_diagrams/"
problems_path_dest = "../../formalgeo7k_v1/formalgeo7k_v1/chosen_problems/"
os.makedirs(diagrams_path_dest, exist_ok=True)

def copy_file(source_file, dest_file):
    if os.path.exists(source_file):
        shutil.copy(source_file, dest_file)
        print(f"Copied: {source_file} -> {dest_file}")
    else:
        print(f"File not found: {source_file}")


for level, problem_ids in chosen_problems_by_level.items():
    for pid in problem_ids:
        copy_file(os.path.join(diagrams_path, f"{pid}.png"), os.path.join(diagrams_path_dest, f"{pid}.png"))
        copy_file(os.path.join(problems_path, f"{pid}.json"), os.path.join(problems_path_dest, f"{pid}.json"))

