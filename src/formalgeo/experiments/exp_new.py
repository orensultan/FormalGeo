import os
import re
import matplotlib.pyplot as plt
import numpy as np
from collections import defaultdict

# Dictionary of problem IDs per level
LEVEL_PROBLEMS = {
    1: [1975, 1490, 1726, 178, 2614, 51, 2323, 192, 2624, 2669],
    2: [69, 144, 358, 991, 2410, 4473, 4523, 5645, 127, 4483],
    3: [844, 4187, 4476, 1945, 4099, 4254, 2200, 2765, 5062, 5244],
    4: [2114, 6155, 3272, 3634, 5230, 5399, 4797, 464, 6924, 5510],
    5: [6485, 437, 6660, 696, 532, 847, 5080, 5431, 5563, 5440]
}

def calculate_success_rate(level_dir, level):
    """
    Calculate success rate for a given level directory.
    A failure is when there's a run_2 file and #RETRIES equals 5.
    Otherwise, it's a success (no run_2 file or RETRIES < 5).
    """
    # Initialize counters for each variant
    variant_stats = {
        "variant_analogy_based_model_o1": {"failures": 0, "total": 0},
        "variant_random_all_theorems_model_o1": {"failures": 0, "total": 0}
    }
    
    # Track unique problems for each variant
    variant_problems = {
        "variant_analogy_based_model_o1": set(),
        "variant_random_all_theorems_model_o1": set()
    }
    
    # Track failed problems for each variant
    failed_problems = {
        "variant_analogy_based_model_o1": set(),
        "variant_random_all_theorems_model_o1": set()
    }
    
    # Get the list of problem IDs for this level
    level_problem_ids = set(LEVEL_PROBLEMS[level])
    
    # Process each file in the level directory
    for filename in os.listdir(level_dir):
        if not filename.endswith('.txt'):
            continue
            
        # Determine which variant this file belongs to
        variant = None
        for v in variant_stats.keys():
            if filename.startswith(v):
                variant = v
                break
                
        if variant is None:
            continue
            
        # Extract problem_id and run number
        match = re.search(r'problem_(\d+)_run_(\d+)', filename)
        if not match:
            continue
            
        problem_id = int(match.group(1))
        run_number = int(match.group(2))
        
        # Skip if this problem is not in our list for this level
        if problem_id not in level_problem_ids:
            continue
        
        # Add problem to the set of problems for this variant
        variant_problems[variant].add(problem_id)
        
        # Read the file to check for RETRIES
        file_path = os.path.join(level_dir, filename)
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Check if this is run_2
        if run_number == 2:
            # Look for RETRIES in the content
            retries_match = re.search(r'#RETRIES:\s*(\d+)', content)
            if retries_match:
                retries = int(retries_match.group(1))
                # If RETRIES is 5, it's a failure
                if retries == 5:
                    failed_problems[variant].add(problem_id)
                    print(f"Found failure in {filename}: RETRIES = {retries}")
    
    # Print failure logs
    print("\nFailure Log:")
    print("=" * 50)
    for variant, failed_problem_set in failed_problems.items():
        print(f"\n{variant}:")
        for problem_id in failed_problem_set:
            print(f"  Problem {problem_id} failed (run_2 with 5 retries)")
    
    # Calculate success rates based on unique problems
    success_rates = {}
    for variant in variant_stats.keys():
        total_problems = len(variant_problems[variant])
        if total_problems > 0:
            # Count failures
            variant_stats[variant]["failures"] = len(failed_problems[variant])
            # Calculate successes as (total - failures)
            successes = total_problems - variant_stats[variant]["failures"]
            success_rates[variant] = (successes / total_problems) * 100
            print(f"\n{variant}:")
            print(f"  Total problems: {total_problems}")
            print(f"  Failed problems: {variant_stats[variant]['failures']}")
            print(f"  Successful problems: {successes}")
            print(f"  Success rate: {success_rates[variant]:.1f}%")
        else:
            success_rates[variant] = 0
            
    return success_rates

def plot_success_rates(base_path):
    """
    Plot success rates for all levels (1-5) for both variants.
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Calculate success rates for each level
    success_rates = {variant: [] for variant in variants}
    for level in levels:
        print(f"\nProcessing Level {level}")
        print("=" * 50)
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            print(f"Level {level} directory not found")
            continue
            
        level_rates = calculate_success_rate(level_dir, level)
        for variant in variants:
            success_rates[variant].append(level_rates.get(variant, 0))
    
    # Create the plot
    plt.figure(figsize=(12, 7))
    
    # Plot lines for each variant
    plt.plot(levels, success_rates["variant_analogy_based_model_o1"], 'o-', 
             label='Analogy based', linewidth=2, markersize=8, color='blue')
    plt.plot(levels, success_rates["variant_random_all_theorems_model_o1"], 's-', 
             label='Random', linewidth=2, markersize=8, color='red')
    
    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Final Success Rate (%)', fontsize=12)
    plt.title('Final Success Rates by Level and Variant', fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10)
    plt.xticks(levels)
    plt.ylim(0, 110)
    plt.yticks(np.arange(0, 110, 10))
    
    # Add value labels on the points
    for i in range(len(levels)):
        plt.text(levels[i], success_rates["variant_analogy_based_model_o1"][i] + 2, 
                f'{success_rates["variant_analogy_based_model_o1"][i]:.1f}%', 
                ha='center', va='bottom', color='blue')
        plt.text(levels[i], success_rates["variant_random_all_theorems_model_o1"][i] - 2, 
                f'{success_rates["variant_random_all_theorems_model_o1"][i]:.1f}%', 
                ha='center', va='top', color='red')
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the plot
    plt.savefig(os.path.join(base_path, 'final_success_rates.png'), dpi=300, bbox_inches='tight')
    plt.close()

def calculate_ablation_success_rates(level_dir, level):
    """
    Calculate success rates for different stages:
    - First Try (FT): run_0 file with RETRIES = 0
    - First Run with Verifier (FRV): run_0 file with 0 < RETRIES < 5
    - Multiple Runs with Verifier (MRV): run_1 or run_2 file with RETRIES < 5
    """
    # Initialize counters for each variant
    variant_stats = {
        "variant_analogy_based_model_o1": {
            "ft": set(),  # First Try successes
            "frv": set(), # First Run with Verifier successes
            "mrv": set(), # Multiple Runs with Verifier successes
            "total": set(), # Total problems
            "has_mrv": False  # Track if variant has any MRV successes
        },
        "variant_random_all_theorems_model_o1": {
            "ft": set(),
            "frv": set(),
            "mrv": set(),
            "total": set(),
            "has_mrv": False
        }
    }
    
    # Get the list of problem IDs for this level
    level_problem_ids = set(LEVEL_PROBLEMS[level])
    
    # Process each file in the level directory
    for filename in os.listdir(level_dir):
        if not filename.endswith('.txt'):
            continue
            
        # Determine which variant this file belongs to
        variant = None
        for v in variant_stats.keys():
            if filename.startswith(v):
                variant = v
                break
                
        if variant is None:
            continue
            
        # Extract problem_id and run number
        match = re.search(r'problem_(\d+)_run_(\d+)', filename)
        if not match:
            continue
            
        problem_id = int(match.group(1))
        run_number = int(match.group(2))
        
        # Skip if this problem is not in our list for this level
        if problem_id not in level_problem_ids:
            continue
        
        # Add problem to total set
        variant_stats[variant]["total"].add(problem_id)
        
        # Read the file to check for RETRIES
        file_path = os.path.join(level_dir, filename)
        with open(file_path, 'r') as f:
            content = f.read()
            
        # Look for RETRIES in the content
        retries_match = re.search(r'#RETRIES:\s*(\d+)', content)
        if not retries_match:
            continue
            
        retries = int(retries_match.group(1))
        
        # Check for First Try success (run_0 and RETRIES = 0)
        if run_number == 0 and retries == 0:
            variant_stats[variant]["ft"].add(problem_id)
            
        # Check for First Run with Verifier success (run_0 and 0 < RETRIES < 5)
        if run_number == 0 and 0 < retries < 5:
            variant_stats[variant]["frv"].add(problem_id)
            
        # Check for Multiple Runs with Verifier success (run_1 or run_2 and RETRIES < 5)
        if (run_number == 1 or run_number == 2) and retries < 5:
            variant_stats[variant]["mrv"].add(problem_id)
            variant_stats[variant]["has_mrv"] = True
    
    # Calculate success rates
    success_rates = {}
    for variant in variant_stats.keys():
        total_problems = len(variant_stats[variant]["total"])
        if total_problems > 0:
            # Calculate base rates
            ft_rate = (len(variant_stats[variant]["ft"]) / total_problems) * 100
            frv_rate = (len(variant_stats[variant]["frv"]) / total_problems) * 100
            mrv_rate = (len(variant_stats[variant]["mrv"]) / total_problems) * 100 if variant_stats[variant]["has_mrv"] else 0
            
            # Make rates cumulative
            success_rates[variant] = {
                "ft": ft_rate,
                "frv": ft_rate + frv_rate,  # FRV includes FT
                "mrv": ft_rate + frv_rate + mrv_rate if variant_stats[variant]["has_mrv"] else 0  # MRV includes FRV and FT
            }
            
            print(f"\n{variant}:")
            print(f"  Total problems: {total_problems}")
            print(f"  First Try success: {len(variant_stats[variant]['ft'])} ({success_rates[variant]['ft']:.1f}%)")
            print(f"  First Run with Verifier success: {len(variant_stats[variant]['frv'])} ({success_rates[variant]['frv']:.1f}%)")
            if variant_stats[variant]["has_mrv"]:
                print(f"  Multiple Runs with Verifier success: {len(variant_stats[variant]['mrv'])} ({success_rates[variant]['mrv']:.1f}%)")
        else:
            success_rates[variant] = {"ft": 0, "frv": 0, "mrv": 0}
            
    return success_rates

def plot_ablation_study(base_path):
    """
    Plot cumulative success rates for different stages of the ablation study.
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Calculate success rates for each level
    success_rates = {variant: {"ft": [], "frv": [], "mrv": []} for variant in variants}
    has_mrv = {variant: [] for variant in variants}  # Track which levels have MRV successes
    
    for level in levels:
        print(f"\nProcessing Level {level}")
        print("=" * 50)
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            print(f"Level {level} directory not found")
            continue
            
        level_rates = calculate_ablation_success_rates(level_dir, level)
        for variant in variants:
            for stage in ["ft", "frv", "mrv"]:
                success_rates[variant][stage].append(level_rates[variant][stage])
            # Track if this level has MRV successes
            has_mrv[variant].append(level_rates[variant]["mrv"] > 0)
    
    # Create the plot
    plt.figure(figsize=(12, 7))
    
    # Plot lines for each variant and stage
    for variant in variants:
        color = 'blue' if 'analogy' in variant else 'red'
        
        # Plot FT
        plt.plot(levels, success_rates[variant]["ft"], 'o-', 
                label=f'{variant.replace("variant_", "").replace("_model_o1", "")} - First Try',
                linewidth=2, markersize=8, color=color)
        
        # Plot FRV
        plt.plot(levels, success_rates[variant]["frv"], 's--', 
                label=f'{variant.replace("variant_", "").replace("_model_o1", "")} - First Run + Verifier',
                linewidth=2, markersize=8, color=color)
        
        # Plot MRV only for levels where it exists
        mrv_data = []
        mrv_levels = []
        for i, (rate, has_mrv_success) in enumerate(zip(success_rates[variant]["mrv"], has_mrv[variant])):
            if has_mrv_success:  # Only plot if this level has MRV successes
                mrv_data.append(rate)
                mrv_levels.append(levels[i])
        
        if mrv_data:  # Only plot if there are any levels with MRV successes
            plt.plot(mrv_levels, mrv_data, '^:', 
                    label=f'{variant.replace("variant_", "").replace("_model_o1", "")} - Multiple Runs + Verifier',
                    linewidth=2, markersize=8, color=color)
    
    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Cumulative Success Rate (%)', fontsize=12)
    plt.title('Cumulative Success Rates by Level and Variant', fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10, bbox_to_anchor=(1.05, 1), loc='upper left')
    plt.xticks(levels)
    plt.ylim(0, 110)
    plt.yticks(np.arange(0, 110, 10))
    
    # Add value labels on the points
    for variant in variants:
        color = 'blue' if 'analogy' in variant else 'red'
        for stage in ["ft", "frv", "mrv"]:
            for i in range(len(levels)):
                rate = success_rates[variant][stage][i]
                if rate > 0:  # Only add labels for non-zero rates
                    plt.text(levels[i], rate + 2, 
                            f'{rate:.1f}%', 
                            ha='center', va='bottom', color=color)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the plot
    plt.savefig(os.path.join(base_path, 'success_rates_progression.png'), dpi=300, bbox_inches='tight')
    plt.close()

def calculate_analogy_stability(base_path):
    """
    Calculate stability of analogy-based approach by comparing success rates:
    1. For problems in the predefined list
    2. For all problems in the directory
    """
    levels = range(1, 6)
    variant = "variant_analogy_based_model_o1"
    
    # Store results for each level
    stability_results = {
        "listed": [],  # Success rates for problems in the list
        "all": [],     # Success rates for all problems
        "difference": []  # Difference between the two rates
    }
    
    for level in levels:
        print(f"\nProcessing Level {level}")
        print("=" * 50)
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            print(f"Level {level} directory not found")
            continue
            
        # Get the list of problem IDs for this level
        level_problem_ids = set(LEVEL_PROBLEMS[level])
        
        # Track failures for both sets
        listed_failures = set()
        all_failures = set()
        listed_total = set()
        all_total = set()
        
        # Process each file in the level directory
        for filename in os.listdir(level_dir):
            if not filename.endswith('.txt') or not filename.startswith(variant):
                continue
                
            # Extract problem_id and run number
            match = re.search(r'problem_(\d+)_run_(\d+)', filename)
            if not match:
                continue
                
            problem_id = int(match.group(1))
            run_number = int(match.group(2))
            
            # Add to all problems set
            all_total.add(problem_id)
            
            # Add to listed problems set if it's in the level's list
            if problem_id in level_problem_ids:
                listed_total.add(problem_id)
            
            # Read the file to check for RETRIES
            file_path = os.path.join(level_dir, filename)
            with open(file_path, 'r') as f:
                content = f.read()
                
            # Check if this is run_2
            if run_number == 2:
                # Look for RETRIES in the content
                retries_match = re.search(r'#RETRIES:\s*(\d+)', content)
                if retries_match:
                    retries = int(retries_match.group(1))
                    # If RETRIES is 5, it's a failure
                    if retries == 5:
                        all_failures.add(problem_id)
                        if problem_id in level_problem_ids:
                            listed_failures.add(problem_id)
        
        # Calculate success rates
        if len(listed_total) > 0:
            listed_success_rate = (1 - len(listed_failures) / len(listed_total)) * 100
        else:
            listed_success_rate = 0
            
        if len(all_total) > 0:
            all_success_rate = (1 - len(all_failures) / len(all_total)) * 100
        else:
            all_success_rate = 0
            
        # Store results
        stability_results["listed"].append(listed_success_rate)
        stability_results["all"].append(all_success_rate)
        stability_results["difference"].append(listed_success_rate - all_success_rate)
        
        print(f"\nLevel {level} Results:")
        print(f"  Listed Problems:")
        print(f"    Total: {len(listed_total)}")
        print(f"    Failures: {len(listed_failures)}")
        print(f"    Success Rate: {listed_success_rate:.1f}%")
        print(f"  All Problems:")
        print(f"    Total: {len(all_total)}")
        print(f"    Failures: {len(all_failures)}")
        print(f"    Success Rate: {all_success_rate:.1f}%")
        print(f"  Difference: {stability_results['difference'][-1]:.1f}%")
    
    # Create the plot
    plt.figure(figsize=(12, 7))
    
    # Plot success rates
    plt.plot(levels, stability_results["listed"], 'o-', 
             label='Samples 1-10', linewidth=2, markersize=8, color='blue')
    plt.plot(levels, stability_results["all"], 's--', 
             label='Samples 1-20', linewidth=2, markersize=8, color='red')
    
    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate (%)', fontsize=12)
    plt.title('Analogy-Based Stability: Listed vs All Problems', fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10)
    plt.xticks(levels)
    plt.ylim(0, 110)
    plt.yticks(np.arange(0, 110, 10))
    
    # Add value labels on the points
    for i in range(len(levels)):
        plt.text(levels[i], stability_results["listed"][i] + 2, 
                f'{stability_results["listed"][i]:.1f}%', 
                ha='center', va='bottom', color='blue')
        plt.text(levels[i], stability_results["all"][i] - 2, 
                f'{stability_results["all"][i]:.1f}%', 
                ha='center', va='top', color='red')
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the plot
    plt.savefig(os.path.join(base_path, 'analogy_stability.png'), dpi=300, bbox_inches='tight')
    plt.close()
    
    return stability_results

if __name__ == "__main__":
    base_path = "/Users/osultan/PycharmProjects/FormalGeo/results"
    plot_success_rates(base_path)
    plot_ablation_study(base_path)
    calculate_analogy_stability(base_path) 