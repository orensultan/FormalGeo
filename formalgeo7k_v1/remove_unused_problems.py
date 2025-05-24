import os
import json

def remove_fields_from_json(directory_path):
    """Remove specified fields from all JSON files in the given directory."""
    fields_to_remove = ["problem_text_cn", "problem_text_en", "annotation"]
    modified_count = 0
    
    for filename in os.listdir(directory_path):
        if filename.endswith('.json'):
            file_path = os.path.join(directory_path, filename)
            
            # Read the JSON file
            with open(file_path, 'r') as file:
                data = json.load(file)
            
            # Remove the specified fields if they exist
            modified = False
            for field in fields_to_remove:
                if field in data:
                    del data[field]
                    modified = True
            
            # Write back only if modifications were made
            if modified:
                with open(file_path, 'w') as file:
                    json.dump(data, file, indent=4, ensure_ascii=False)
                modified_count += 1
    
    return modified_count

def main():
    # Define the two directories to process
    directories = [
        "formalgeo7k_v1/problems",
        "formalgeo7k_v1/formalgeo7k_v1/problems"
    ]
    
    total_modified = 0
    for directory in directories:
        if os.path.exists(directory):
            print(f"Processing directory: {directory}")
            modified_count = remove_fields_from_json(directory)
            print(f"Modified {modified_count} files in {directory}")
            total_modified += modified_count
        else:
            print(f"Directory not found: {directory}")
    
    print(f"\nTotal files modified: {total_modified}")

if __name__ == "__main__":
    main()
