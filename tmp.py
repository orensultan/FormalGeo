import json

def count_theorems(json_path):
    """
    Count the number of theorems in the GDL json file, both with and without considering variations.
    
    Args:
        json_path (str): Path to the theorem_GDL.json file
        
    Returns:
        tuple: (base_count, variation_count) where
               base_count is the number of theorems without considering variations
               variation_count is the total number of theorem variations
    """
    # Read the JSON file
    with open(json_path, 'r') as f:
        theorems = json.load(f)
    
    # Count base theorems (each key is one theorem)
    base_count = len(theorems)
    
    # Count variations (sum up the number of numbered variations for each theorem)
    variation_count = sum(len(theorem) for theorem in theorems.values())
    
    return base_count, variation_count

if __name__ == "__main__":
    json_path = "/Users/osultan/PycharmProjects/FormalGeo/formalgeo7k_v1/gdl/theorem_GDL.json"
    base_count, variation_count = count_theorems(json_path)
    
    print(f"Number of base theorems: {base_count}")
    print(f"Number of theorems including variations: {variation_count}") 