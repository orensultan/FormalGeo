import os
import re
import matplotlib.pyplot as plt
import numpy as np
from collections import defaultdict
import pandas as pd
from statsmodels.sandbox.stats.runs import mcnemar
import math  # Add this import at the top of the file

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

def plot_confusion_matrix(table, stage, base_path):
    """
    Plot confusion matrix for McNemar test contingency table.
    Args:
        table: Contingency table from McNemar test
        stage: The stage being tested ('ft' or 'frv')
        base_path: Base path to save the plot
    """
    plt.figure(figsize=(8, 6))
    
    # Create heatmap
    plt.imshow(table, cmap='Blues')
    
    # Add text annotations
    for i in range(table.shape[0]):
        for j in range(table.shape[1]):
            plt.text(j, i, str(table.iloc[i, j]),
                    ha='center', va='center',
                    color='white' if table.iloc[i, j] > table.max().max()/2 else 'black')
    
    # Add labels
    plt.xlabel('Random Success', fontsize=12)
    plt.ylabel('Analogy Success', fontsize=12)
    plt.title(f'McNemar Test Contingency Table - {stage.upper()}', fontsize=14)
    
    # Add tick labels
    plt.xticks([0, 1], ['Failure (0)', 'Success (1)'])
    plt.yticks([0, 1], ['Failure (0)', 'Success (1)'])
    
    # Add colorbar
    plt.colorbar(label='Count')
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the plot
    plt.savefig(os.path.join(base_path, f'mcnemar_confusion_matrix_{stage}.png'), dpi=300, bbox_inches='tight')
    plt.close()

def perform_mcnemar_test(problem_status, stage, base_path):
    """
    Perform McNemar test to compare success rates between analogy-based and random approaches.
    Args:
        problem_status: Dictionary containing problem status for each variant and stage
        stage: The stage to test ('ft' or 'frv')
        base_path: Base path to save the confusion matrix plot
    """
    # Create a DataFrame with problem IDs and their success/failure status
    data = []
    for problem_id in sorted(set(problem_status["analogy_based"][stage].keys()) | set(problem_status["random"][stage].keys())):
        data.append({
            'problem_id': problem_id,
            'analogy_success': problem_status["analogy_based"][stage].get(problem_id, 0),
            'random_success': problem_status["random"][stage].get(problem_id, 0)
        })
    
    df = pd.DataFrame(data)
    
    # Create contingency table for McNemar test
    table = pd.crosstab(df['analogy_success'], df['random_success'])
    
    # Check if we have a valid 2x2 contingency table
    if table.shape != (2, 2):
        # If not, create a 2x2 table with zeros for missing categories
        full_table = pd.DataFrame([[0, 0], [0, 0]], 
                                index=[0, 1], 
                                columns=[0, 1])
        for i in table.index:
            for j in table.columns:
                full_table.loc[i, j] = table.loc[i, j]
        table = full_table
    
    # Perform McNemar test
    try:
        test_result = mcnemar(table)
        _, p_value = test_result
    except Exception as e:
        print(f"\nWarning: Could not perform McNemar test: {str(e)}")
        p_value = 1.0  # Default to non-significant result
    
    print(f"\nMcNemar Test Results for {stage.upper()}:")
    print("=" * 50)
    print("\nContingency Table:")
    print(table)
    print(f"\np-value: {p_value:.2e}")
    
    # Plot confusion matrix
    plot_confusion_matrix(table, stage, base_path)
    
    # Interpret results
    alpha = 0.05
    if p_value < alpha:
        print(f"\nThe difference in success rates between analogy-based and random approaches is statistically significant (p < {alpha})")
    else:
        print(f"\nThe difference in success rates between analogy-based and random approaches is not statistically significant (p >= {alpha})")
    
    return p_value

def plot_success_rates(base_path):
    """
    Plot success rates for all levels (1-5) for both variants.
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Calculate success rates for each level
    success_rates = {variant: [] for variant in variants}
    
    # Dictionary to store problem success/failure status
    problem_status = {
        "analogy_based": {
            "success": {}  # Overall success status
        },
        "random": {
            "success": {}  # Overall success status
        }
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
        
        # Track failures for each variant
        failed_problems = {
            "variant_analogy_based_model_o1": set(),
            "variant_random_all_theorems_model_o1": set()
        }
        
        # Process each file in the level directory
        for filename in os.listdir(level_dir):
            if not filename.endswith('.txt'):
                continue
                
            # Determine which variant this file belongs to
            variant = None
            for v in variants:
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
        
        # Calculate success rates and update problem status
        level_rates = {}
        for variant in variants:
            # Get the list of problems for this variant and level
            variant_problems = set()
            for filename in os.listdir(level_dir):
                if filename.startswith(variant) and filename.endswith('.txt'):
                    match = re.search(r'problem_(\d+)_run_(\d+)', filename)
                    if match:
                        problem_id = int(match.group(1))
                        if problem_id in level_problem_ids:
                            variant_problems.add(problem_id)
            
            if len(variant_problems) > 0:
                # Count failures
                failures = len(failed_problems[variant])
                # Calculate successes as (total - failures)
                successes = len(variant_problems) - failures
                level_rates[variant] = (successes / len(variant_problems)) * 100
                
                # Update problem status dictionary
                variant_key = "analogy_based" if "analogy" in variant else "random"
                for problem_id in variant_problems:
                    # Initialize success status
                    problem_status[variant_key]["success"][problem_id] = 0
                    # Set status based on whether it's a failure
                    if problem_id not in failed_problems[variant]:
                        problem_status[variant_key]["success"][problem_id] = 1
            else:
                level_rates[variant] = 0
        
        # Update success rates
        for variant in variants:
            success_rates[variant].append(level_rates.get(variant, 0))
    
    # Print problem status dictionary
    print("\nProblem Status Dictionary:")
    print("=" * 50)
    for variant, stages in problem_status.items():
        print(f"\n{variant}:")
        for stage, problems in stages.items():
            print(f"  {stage.upper()}:")
            for problem_id, status in sorted(problems.items()):
                print(f"    Problem {problem_id}: {'Success' if status == 1 else 'Failure'}")
    
    # Calculate and print percentage of successful problems (ones) for each variant
    print("\nPercentage of Successful Problems (Ones):")
    print("=" * 50)
    for variant_key in ["analogy_based", "random"]:
        total_problems = len(problem_status[variant_key]["success"])
        successful_problems = sum(1 for status in problem_status[variant_key]["success"].values() if status == 1)
        success_percentage = (successful_problems / total_problems) * 100
        print(f"\n{variant_key}:")
        print(f"  Total problems: {total_problems}")
        print(f"  Successful problems: {successful_problems}")
        print(f"  Success percentage: {success_percentage:.1f}%")
    
    # Create the plot
    plt.figure(figsize=(12, 7))
    
    # Plot lines for each variant
    plt.plot(levels, success_rates["variant_analogy_based_model_o1"], 'o-', 
             label='Analogy based', linewidth=2, markersize=8, color='blue')
    plt.plot(levels, success_rates["variant_random_all_theorems_model_o1"], 's-', 
             label='Random', linewidth=2, markersize=8, color='red')
    
    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate (%)', fontsize=12)
    plt.title('o1 Model Success Rates Per Level: Analogy-Based (ours) vs. Random (50 Samples)', fontsize=14)
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

def plot_ablation_study(base_path):
    """
    Plot cumulative success rates for different stages of the ablation study.
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Calculate success rates for each level
    success_rates = {variant: {"ft": [], "frv": [], "mrv": []} for variant in variants}
    has_mrv = {variant: [] for variant in variants}  # Track which levels have MRV successes
    
    # Dictionary to store problem status for each stage (accumulated across all levels)
    problem_status = {
        "analogy_based": {
            "ft": {},  # First Try status
            "frv": {},  # First Run with Verifier status
            "mrv": {},  # Multiple Runs with Verifier status
            "ft_union_frv": {},  # Union of FT and FRV status
            "ft_union_frv_union_mrv": {}  # Union of FT, FRV, and MRV status
        },
        "random": {
            "ft": {},
            "frv": {},
            "mrv": {},  # Multiple Runs with Verifier status
            "ft_union_frv": {},  # Union of FT and FRV status
            "ft_union_frv_union_mrv": {}  # Union of FT, FRV, and MRV status
        }
    }
    
    # First, initialize all problems as failures
    for level in levels:
        level_problem_ids = set(LEVEL_PROBLEMS[level])
        for variant in variants:
            variant_key = "analogy_based" if "analogy" in variant else "random"
            for problem_id in level_problem_ids:
                if problem_id not in problem_status[variant_key]["ft"]:
                    problem_status[variant_key]["ft"][problem_id] = 0
                    problem_status[variant_key]["frv"][problem_id] = 0
                    problem_status[variant_key]["mrv"][problem_id] = 0
                    problem_status[variant_key]["ft_union_frv"][problem_id] = 0
                    problem_status[variant_key]["ft_union_frv_union_mrv"][problem_id] = 0
    
    for level in levels:
        print(f"\nProcessing Level {level}")
        print("=" * 50)
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            print(f"Level {level} directory not found")
            continue
            
        level_rates = calculate_ablation_success_rates(level_dir, level, problem_status)
        for variant in variants:
            for stage in ["ft", "frv", "mrv"]:
                success_rates[variant][stage].append(level_rates[variant][stage])
            # Track if this level has MRV successes
            has_mrv[variant].append(level_rates[variant]["mrv"] > 0)
    
    # Print problem status dictionary for debugging
    print("\nProblem Status Dictionary (Accumulated across all levels):")
    print("=" * 50)
    for variant, stages in problem_status.items():
        print(f"\n{variant}:")
        for stage, problems in stages.items():
            print(f"  {stage.upper()}:")
            for problem_id, status in sorted(problems.items()):
                print(f"    Problem {problem_id}: {'Success' if status == 1 else 'Failure'}")
    
    # Calculate and print overall success rates across all levels
    print("\nOverall Success Rates (50 samples):")
    print("=" * 50)
    for variant in variants:
        variant_key = "analogy_based" if "analogy" in variant else "random"
        total_problems = len(problem_status[variant_key]["ft"])
        successful_problems = sum(1 for status in problem_status[variant_key]["ft_union_frv_union_mrv"].values() if status == 1)
        overall_rate = (successful_problems / total_problems) * 100
        print(f"\n{variant}:")
        print(f"  Total problems: {total_problems}")
        print(f"  Successful problems: {successful_problems}")
        print(f"  Overall success rate: {overall_rate:.1f}%")
        
        # Print successful problem IDs
        successful_ids = [pid for pid, status in problem_status[variant_key]["ft_union_frv_union_mrv"].items() if status == 1]
        print(f"  Successful problem IDs: {sorted(successful_ids)}")
    
    # Perform McNemar tests for the two specific comparisons
    print("\nPerforming McNemar Tests:")
    print("=" * 50)
    
    # First test: analogy-based first try vs random first try
    print("\nTest 1: Analogy-based First Try vs Random First Try")
    print("-" * 50)
    ft_vs_random_test = {
        "analogy_based": {"test": problem_status["analogy_based"]["ft"]},
        "random": {"test": problem_status["random"]["ft"]}
    }
    ft_vs_random_p_value = perform_mcnemar_test(ft_vs_random_test, "test", base_path)
    
    # Second test: analogy-based multiple runs with retries vs random first try
    print("\nTest 2: Analogy-based Multiple Runs with Retries vs Random First Try")
    print("-" * 50)
    mrv_vs_random_test = {
        "analogy_based": {"test": problem_status["analogy_based"]["ft_union_frv_union_mrv"]},
        "random": {"test": problem_status["random"]["ft"]}
    }
    mrv_vs_random_p_value = perform_mcnemar_test(mrv_vs_random_test, "test", base_path)
    
    # Third test: analogy-based first run with retries vs random first try
    print("\nTest 3: Analogy-based First Run with Retries vs Random First Try")
    print("-" * 50)
    frv_vs_random_test = {
        "analogy_based": {"test": problem_status["analogy_based"]["ft_union_frv"]},
        "random": {"test": problem_status["random"]["ft"]}
    }
    frv_vs_random_p_value = perform_mcnemar_test(frv_vs_random_test, "test", base_path)
    
    # Fourth test: analogy-based first run with retries vs random first run with retries
    print("\nTest 4: Analogy-based First Run with Retries vs Random First Run with Retries")
    print("-" * 50)
    frv_vs_frv_test = {
        "analogy_based": {"test": problem_status["analogy_based"]["ft_union_frv"]},
        "random": {"test": problem_status["random"]["ft_union_frv"]}
    }
    frv_vs_frv_p_value = perform_mcnemar_test(frv_vs_frv_test, "test", base_path)
    
    # Fifth test: analogy-based multiple runs with retries vs random multiple runs with retries
    print("\nTest 5: Analogy-based Multiple Runs with Retries vs Random Multiple Runs with Retries")
    print("-" * 50)
    mrv_vs_mrv_test = {
        "analogy_based": {"test": problem_status["analogy_based"]["ft_union_frv_union_mrv"]},
        "random": {"test": problem_status["random"]["ft_union_frv_union_mrv"]}
    }
    mrv_vs_mrv_p_value = perform_mcnemar_test(mrv_vs_mrv_test, "test", base_path)
    
    # Create the plot
    plt.figure(figsize=(12, 7))
    
    # Plot lines for each variant and stage
    for variant in variants:
        color = 'blue' if 'analogy' in variant else 'red'
        variant_label = variant.replace("variant_", "").replace("_model_o1", "").replace("random_all_theorems", "random")
        
        # Plot FT first
        plt.plot(levels, success_rates[variant]["ft"], 'o-', 
                label=f'{variant_label} - First attempt',
                linewidth=2, markersize=8, color=color)
        
        # Plot FRV second
        plt.plot(levels, success_rates[variant]["frv"], 's--', 
                label=f'{variant_label} - First run w. retries',
                linewidth=2, markersize=8, color=color)
        
        # Plot MRV last with solid triangles
        plt.plot(levels, success_rates[variant]["mrv"], '^:', 
                label=f'{variant_label} - Multiple runs w. retries',
                linewidth=2, markersize=10, color=color)
        
        # Add markers for MRV points that have the same value as FRV
        for i in range(len(levels)):
            if success_rates[variant]["mrv"][i] == success_rates[variant]["frv"][i]:
                plt.plot(levels[i], success_rates[variant]["mrv"][i], '^', 
                        color=color, markersize=10)
    
    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Cumulative Success Rate (%)', fontsize=12)
    plt.title('Our analogy-based method outperforms the random baseline\nin all o1 model ablations (50 samples)', fontsize=16)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=9, loc='upper right', bbox_to_anchor=(0.98, 0.98), framealpha=1.0)
    plt.xticks(levels)
    plt.ylim(0, 110)
    plt.yticks(np.arange(0, 110, 10))
    
    # Adjust x-axis limits to make the graph wider
    plt.xlim(0.5, 5.5)  # Extend x-axis limits slightly beyond the data points
    
    # Add value labels on the points
    for variant in variants:
        color = 'blue' if 'analogy' in variant else 'red'
        for stage in ["ft", "frv", "mrv"]:
            for i in range(len(levels)):
                rate = success_rates[variant][stage][i]
                if rate > 0:  # Only add labels for non-zero rates
                    # Skip MRV label if it has the same value as FRV
                    if stage == "mrv" and rate == success_rates[variant]["frv"][i]:
                        continue
                    # Adjust vertical position of labels to prevent overlap
                    offset = 2
                    plt.text(levels[i], rate + offset, 
                            f'{rate:.1f}%', 
                            ha='center', va='bottom', color=color)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the plot
    plt.savefig(os.path.join(base_path, 'success_rates_progression.png'), dpi=300, bbox_inches='tight')
    plt.close()

def calculate_ablation_success_rates(level_dir, level, problem_status):
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
        # Only process .txt files for o1_model variants
        if not (filename.endswith('.txt') and 
                (filename.startswith('variant_analogy_based_model_o1') or 
                 filename.startswith('variant_random_all_theorems_model_o1'))):
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
        
        # Get variant key for problem_status dictionary
        variant_key = "analogy_based" if "analogy" in variant else "random"
        
        # Check for First Try success (run_0 and RETRIES = 0)
        if run_number == 0 and retries == 0:
            variant_stats[variant]["ft"].add(problem_id)
            problem_status[variant_key]["ft"][problem_id] = 1
            problem_status[variant_key]["ft_union_frv"][problem_id] = 1
            problem_status[variant_key]["ft_union_frv_union_mrv"][problem_id] = 1
            
        # Check for First Run with Verifier success (run_0 and 0 < RETRIES < 5)
        if run_number == 0 and 0 < retries < 5:
            variant_stats[variant]["frv"].add(problem_id)
            problem_status[variant_key]["frv"][problem_id] = 1
            problem_status[variant_key]["ft_union_frv"][problem_id] = 1
            problem_status[variant_key]["ft_union_frv_union_mrv"][problem_id] = 1
            
        # Check for Multiple Runs with Verifier success (run_1 or run_2 and RETRIES < 5)
        if (run_number == 1 or run_number == 2) and retries < 5:
            variant_stats[variant]["mrv"].add(problem_id)
            variant_stats[variant]["has_mrv"] = True
            problem_status[variant_key]["mrv"][problem_id] = 1
            problem_status[variant_key]["ft_union_frv_union_mrv"][problem_id] = 1
    
    # Calculate success rates
    success_rates = {}
    for variant in variant_stats.keys():
        total_problems = len(variant_stats[variant]["total"])
        if total_problems > 0:
            # Calculate base rates
            ft_rate = (len(variant_stats[variant]["ft"]) / total_problems) * 100
            frv_rate = (len(variant_stats[variant]["frv"]) / total_problems) * 100
            mrv_rate = (len(variant_stats[variant]["mrv"]) / total_problems) * 100
            
            # Make rates cumulative
            success_rates[variant] = {
                "ft": ft_rate,
                "frv": ft_rate + frv_rate,  # FRV includes FT
                "mrv": ft_rate + frv_rate + mrv_rate  # MRV includes FRV and FT, even if no additional successes
            }
            
            print(f"\n{variant}:")
            print(f"  Total problems: {total_problems}")
            print(f"  First Try success: {len(variant_stats[variant]['ft'])} ({success_rates[variant]['ft']:.1f}%)")
            print(f"  First Run with Verifier success: {len(variant_stats[variant]['frv'])} ({success_rates[variant]['frv']:.1f}%)")
            print(f"  Multiple Runs with Verifier success: {len(variant_stats[variant]['mrv'])} ({success_rates[variant]['mrv']:.1f}%)")
            
            # Print MRV problems for debugging
            if variant_stats[variant]["mrv"]:
                print(f"  MRV problems: {sorted(variant_stats[variant]['mrv'])}")
                print(f"  MRV rate: {mrv_rate:.1f}%")
                print(f"  Total MRV rate: {success_rates[variant]['mrv']:.1f}%")
        else:
            success_rates[variant] = {"ft": 0, "frv": 0, "mrv": 0}
            
    return success_rates

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
             label='original samples', linewidth=2, markersize=8, color='blue')
    plt.plot(levels, stability_results["all"], 'o-',
             label='original + extended samples', linewidth=2, markersize=8, color='red')
    
    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate (%)', fontsize=12)
    plt.title('Performance of our method on the o1 model remains stable\nwhen increasing from 50 to 100 sampled problems (10 to 20 per level)', fontsize=16)
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

def analyze_answer_correctness(base_path):
    """
    Analyze which problems in the sample of 50 problems (10 per level) were solved correctly
    by comparing model answers with ground truth answers. A problem is considered incorrect
    only if all of its answers (including retries) are not equal to the ground truth answer.
    For floating-point comparisons, answers are considered equal if they differ by at most 0.01.
    For fractions, both the fraction form and decimal form are checked.
    """
    def evaluate_math_expression(expr):
        """Evaluate a mathematical expression safely."""
        try:
            # Convert to string if it's a number
            expr = str(expr)
            
            # First handle implicit multiplication
            expr = re.sub(r'(\d+)\s*√', r'\1*sqrt', expr)  # Handle 3√2 -> 3*sqrt
            expr = re.sub(r'(\d+)\s*sqrt', r'\1*sqrt', expr)  # Handle 3 sqrt -> 3*sqrt
            expr = re.sub(r'(\d+)\(', r'\1*(', expr)  # Handle 2(3)
            expr = re.sub(r'\)(\d+)', r')*\1', expr)  # Handle (2)3
            expr = re.sub(r'\)\s*\(', r')*(', expr)  # Handle (2)(3)
            
            # Then normalize mathematical functions and constants
            expr = re.sub(r'√(\d+)', r'sqrt(\1)', expr)  # Handle √6 -> sqrt(6)
            expr = re.sub(r'sqrt\s*\((\d+)\)', r'sqrt(\1)', expr)  # Handle sqrt(6)
            expr = re.sub(r'sqrt\s*(\d+)', r'sqrt(\1)', expr)  # Handle sqrt 6
            
            # Replace all variations of pi with math.pi
            expr = re.sub(r'(\d+)π', r'\1*math.pi', expr)  # Handle 2π
            expr = re.sub(r'(\d+)\s*pi', r'\1*math.pi', expr)  # Handle 2 pi
            expr = re.sub(r'π', r'math.pi', expr)  # Handle π alone
            expr = re.sub(r'pi', r'math.pi', expr)  # Handle pi alone
            
            # Add math. prefix to sqrt
            expr = re.sub(r'sqrt\(', r'math.sqrt(', expr)
            
            # Evaluate the expression
            return eval(expr)
        except Exception as e:
            print(f"Error evaluating expression '{expr}': {str(e)}")
            return None
    
    def parse_fraction(value):
        """Parse a value that could be a fraction or a number."""
        try:
            # Try to parse as a fraction (e.g., "41/63")
            if '/' in str(value):
                # Split on '/' and handle each part
                parts = str(value).split('/')
                if len(parts) != 2:
                    return None
                
                # Parse numerator and denominator
                num = parts[0].strip()
                denom = parts[1].strip()
                
                # Handle expressions in numerator or denominator
                try:
                    num_value = evaluate_math_expression(num)
                    denom_value = evaluate_math_expression(denom)
                    if num_value is not None and denom_value is not None:
                        return num_value / denom_value
                except:
                    pass
                
                # If expression evaluation fails, try direct integer division
                try:
                    return int(num) / int(denom)
                except:
                    return None
            
            # Try to evaluate as a math expression
            expr_value = evaluate_math_expression(value)
            if expr_value is not None:
                return expr_value
            
            # Try to parse as a regular number
            return float(value)
        except (ValueError, ZeroDivisionError):
            return None
    
    def is_answer_correct(answer, gt_answer):
        """Check if an answer is correct, handling integers, floating-point numbers, and fractions."""
        try:
            # Parse both values
            answer_value = parse_fraction(answer)
            gt_value = parse_fraction(gt_answer)
            
            if answer_value is None or gt_value is None:
                return False
            
            # Convert both values to float for comparison
            answer_float = float(answer_value)
            gt_float = float(gt_value)
            
            # If both are integers (after conversion to float), do exact comparison
            if answer_float.is_integer() and gt_float.is_integer():
                return int(answer_float) == int(gt_float)
            
            # For floating-point numbers, use epsilon comparison
            return abs(answer_float - gt_float) <= 0.01
        except (ValueError, TypeError):
            return False
    
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Dictionary to store aggregated statistics
    level_stats = {
        level: {
            variant: {
                "total_problems": 0,
                "problems_with_answers": 0,  # Problems that have at least one answer
                "all_incorrect_problems": set(),  # Problems where all provided answers are incorrect
            } for variant in variants
        } for level in levels
    }
    
    print("\nAnalyzing Answer Correctness:")
    print("=" * 50)
    
    for level in levels:
        print(f"\nLevel {level}:")
        print("-" * 30)
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            print(f"Level {level} directory not found")
            continue
            
        # Get the list of problem IDs for this level
        level_problem_ids = set(LEVEL_PROBLEMS[level])
        
        # Process each problem
        for problem_id in sorted(level_problem_ids):
            # First, get the ground truth answer from run_0
            gt_answer = None
            for variant in variants:
                run_0_file = os.path.join(level_dir, f"{variant}_problem_{problem_id}_run_0.txt")
                if os.path.exists(run_0_file):
                    with open(run_0_file, 'r') as f:
                        content = f.read()
                        gt_match = re.search(r'GT_ANSWER:\s*(.*?)(?:\n|$)', content)
                        if gt_match:
                            gt_expr = gt_match.group(1).strip()
                            if gt_expr:  # If there's a value after GT_ANSWER:
                                try:
                                    # First try to parse as integer
                                    gt_answer = int(gt_expr)
                                except ValueError:
                                    # If not an integer, try to evaluate as math expression
                                    gt_answer = evaluate_math_expression(gt_expr)
                                    if gt_answer is None:
                                        # If not a math expression, try to parse as fraction
                                        gt_answer = parse_fraction(gt_expr)
                                    if gt_answer is not None:
                                        print(f"Problem {problem_id} ground truth expression '{gt_expr}' evaluated to {gt_answer}")
                            break
            
            if gt_answer is None:
                if level == 5:  # Print missing problem for Level 5
                    print(f"\nProblem {problem_id} is missing ground truth answer or has invalid expression")
                continue
            
            # Check each variant's answers
            for variant in variants:
                all_answers = []  # Track all answers for this problem
                
                # Check all runs for this problem
                for run_num in range(3):  # Check run_0, run_1, and run_2
                    run_file = os.path.join(level_dir, f"{variant}_problem_{problem_id}_run_{run_num}.txt")
                    if os.path.exists(run_file):
                        with open(run_file, 'r') as f:
                            content = f.read()
                            
                            # Check ANSWER
                            answer_match = re.search(r'ANSWER:\s*(.*?)(?:\n|$)', content)
                            if answer_match:
                                answer = answer_match.group(1).strip()
                                all_answers.append(answer)
                            
                            # Check RETRY_ANSWER
                            retry_match = re.search(r'RETRY_ANSWER:\s*(.*?)(?:\n|$)', content)
                            if retry_match:
                                retry_answer = retry_match.group(1).strip()
                                all_answers.append(retry_answer)
                
                # Update statistics
                level_stats[level][variant]["total_problems"] += 1
                if all_answers:  # If we found any answers
                    level_stats[level][variant]["problems_with_answers"] += 1
                    # Check if all answers are incorrect using the epsilon comparison
                    if not any(is_answer_correct(answer, gt_answer) for answer in all_answers):
                        level_stats[level][variant]["all_incorrect_problems"].add(problem_id)
    
    # Print aggregated statistics
    print("\nAggregated Statistics:")
    print("=" * 50)
    for level in levels:
        print(f"\nLevel {level}:")
        print("-" * 30)
        for variant in variants:
            stats = level_stats[level][variant]
            if stats["total_problems"] > 0:
                all_incorrect_percentage = (len(stats["all_incorrect_problems"]) / stats["problems_with_answers"]) * 100 if stats["problems_with_answers"] > 0 else 0
                print(f"\n{variant}:")
                print(f"  Total problems: {stats['total_problems']}")
                print(f"  Problems with answers: {stats['problems_with_answers']}")
                print(f"  Problems with all incorrect answers: {len(stats['all_incorrect_problems'])} ({all_incorrect_percentage:.1f}%)")
                if stats["all_incorrect_problems"]:
                    print(f"  Problem IDs with all incorrect answers: {sorted(stats['all_incorrect_problems'])}")

if __name__ == "__main__":
    base_path = "/Users/osultan/PycharmProjects/FormalGeo/results"
    # plot_success_rates(base_path)
    # plot_ablation_study(base_path)
    # calculate_analogy_stability(base_path)
    analyze_answer_correctness(base_path)