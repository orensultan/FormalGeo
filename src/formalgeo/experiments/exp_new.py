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

# Dictionary to store problem status for each stage (accumulated across all levels)
GLOBAL_PROBLEM_STATUS = {
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
                     color='white' if table.iloc[i, j] > table.max().max() / 2 else 'black')

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
    for problem_id in sorted(
            set(problem_status["analogy_based"][stage].keys()) | set(problem_status["random"][stage].keys())):
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
        print(
            f"\nThe difference in success rates between analogy-based and random approaches is statistically significant (p < {alpha})")
    else:
        print(
            f"\nThe difference in success rates between analogy-based and random approaches is not statistically significant (p >= {alpha})")

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
    plt.xlabel('Level', fontsize=20)  # Increased from 12
    plt.ylabel('Success Rate (%)', fontsize=20)  # Increased from 12
    plt.title('o1 Model Success Rates Per Level: Analogy-Based (ours) vs. Random (50 Samples)', fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10)
    plt.xticks(levels, fontsize=16)  # Added fontsize for x-axis numbers
    plt.ylim(0, 110)
    plt.yticks(np.arange(0, 110, 10), fontsize=16)  # Added fontsize for y-axis numbers

    # Adjust layout
    plt.tight_layout()

    # Save the plot
    plt.savefig(os.path.join(base_path, 'final_success_rates.png'), dpi=300, bbox_inches='tight')
    plt.close()



def plot_ablation_study(base_path):
    """
    Plot cumulative success rates for different stages of the ablation study.
    Returns the problem status dictionary containing success/failure status for each problem.
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
    plt.figure(figsize=(24, 16))  # Increased width from 22 to 26

    # Set font sizes and style
    plt.rcParams['font.size'] = 24
    plt.rcParams['legend.fontsize'] = 24
    plt.rcParams['axes.linewidth'] = 1.5
    plt.rcParams['axes.edgecolor'] = 'black'

    # Define colors and styles
    colors = {
        'analogy': '#1f77b4',  # Blue
        'random': '#d62728'  # Red
    }

    # Plot lines for each variant and stage
    for variant in variants:
        color = colors['analogy'] if 'analogy' in variant else colors['random']
        variant_label = variant.replace("variant_", "").replace("_model_o1", "").replace("random_all_theorems", "random")

        # Plot FT first (solid line with circles)
        plt.plot(levels, success_rates[variant]["ft"], 'o-',
                label=f'{"Analogy-based" if "analogy" in variant else "Base model"} - 1 run, no retries',
                linewidth=3, markersize=14, color=color, alpha=0.9,
                markerfacecolor=color if 'analogy' in variant else 'white')  # Filled for analogy, hollow for base

        # Plot FRV second (dashed line with squares)
        plt.plot(levels, success_rates[variant]["frv"], 's--',
                label=f'{"Analogy-based" if "analogy" in variant else "Base model"} - 1 run, with verifier 5 retries',
                linewidth=3, markersize=14, color=color, alpha=0.9,
                markerfacecolor=color if 'analogy' in variant else 'white')  # Filled for analogy, hollow for base

        # Plot MRV last (dotted line with triangles)
        plt.plot(levels, success_rates[variant]["mrv"], '^:',
                label=f'{"Analogy-based" if "analogy" in variant else "Base model"} - 3 runs, with verifier 5 retries',
                linewidth=3, markersize=14, color=color, alpha=0.9,
                markerfacecolor=color if 'analogy' in variant else 'white')  # Filled for analogy, hollow for base

        # Add markers for MRV points that have the same value as FRV
        for i in range(len(levels)):
            if success_rates[variant]["mrv"][i] == success_rates[variant]["frv"][i]:
                plt.plot(levels[i], success_rates[variant]["mrv"][i], '^',
                        color=color, markersize=14, alpha=0.9,
                        markerfacecolor=color if 'analogy' in variant else 'white')  # Filled for analogy, hollow for base

    # Customize the plot
    plt.xlabel('Level', fontsize=28, fontweight='bold', labelpad=15)  # Added bold
    plt.ylabel('Correct Proofs (%)', fontsize=28, fontweight='bold', labelpad=15)  # Added bold
    plt.title('% correct proofs per level of difficulty',
             fontsize=36, fontweight='bold', pad=50)  # Increased pad to make room for legend

    # Customize grid
    plt.grid(True, linestyle='--', alpha=0.3, color='gray')
    
    # Add black horizontal and vertical lines
    # Horizontal lines at every 10%
    for y in range(0, 110, 10):
        plt.axhline(y=y, color='black', linewidth=0.8, alpha=0.3, zorder=1)
    
    # Vertical lines at each level
    for x in levels:
        plt.axvline(x=x, color='black', linewidth=0.8, alpha=0.3, zorder=1)

    # Customize legend - position it below the plot
    handles, labels = plt.gca().get_legend_handles_labels()
    legend = plt.legend(handles, labels,
                     fontsize=28,  # Increased from 24
                     loc='upper center',
                     bbox_to_anchor=(0.5, -0.15),  # Move legend below plot
                     frameon=True,
                     edgecolor='black',
                     fancybox=False,
                     borderpad=0.5,
                     handlelength=2.0,
                     handletextpad=0.5,
                     labelspacing=0.3,
                     ncol=2)
    
    # Make legend text bold
    for text in legend.get_texts():
        text.set_fontweight('bold')
    
    # Make axis numbers bold
    plt.xticks(levels, fontsize=28, fontweight='bold')  # Added fontweight='bold'
    plt.yticks(np.arange(0, 110, 10), fontsize=28, fontweight='bold')  # Added fontweight='bold'
    
    # Adjust layout with space for legend at bottom
    plt.tight_layout(rect=[0, 0.1, 1, 0.95])  # Adjusted to make room for legend at bottom

    # Make left and bottom spines thicker
    plt.gca().spines['left'].set_linewidth(1.5)
    plt.gca().spines['bottom'].set_linewidth(1.5)

    # Adjust layout with more padding
    plt.tight_layout(pad=2.0)

    # Save the plot with high DPI and white background
    plt.savefig(os.path.join(base_path, 'success_rates_progression.png'),
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.close()

    return problem_status

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
            "frv": set(),  # First Run with Verifier successes
            "mrv": set(),  # Multiple Runs with Verifier successes
            "total": set(),  # Total problems
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
            print(
                f"  First Run with Verifier success: {len(variant_stats[variant]['frv'])} ({success_rates[variant]['frv']:.1f}%)")
            print(
                f"  Multiple Runs with Verifier success: {len(variant_stats[variant]['mrv'])} ({success_rates[variant]['mrv']:.1f}%)")

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
        "all": [],  # Success rates for all problems
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
    plt.title(
        'Performance of our method on the o1 model remains stable\nwhen increasing from 50 to 100 sampled problems (10 to 20 per level)',
        fontsize=16)
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


def evaluate_math_expression(expr):
    """Evaluate a mathematical expression safely."""
    import math
    import re

    # Store original symbolic form
    original_symbolic = str(expr).strip()

    # Remove whitespace
    expr = str(expr).strip()

    # Handle trig expressions with pi/180 conversion
    if 'sin(' in expr.lower() or 'cos(' in expr.lower() or 'tan(' in expr.lower():
        try:
            # Replace pi with math.pi
            modified_str = expr.replace('pi', 'math.pi')

            # Create a safe environment with only math functions
            safe_globals = {
                'math': math,
                'sin': math.sin,
                'cos': math.cos,
                'tan': math.tan,
                'sqrt': math.sqrt
            }

            # Try direct evaluation with math functions
            return float(eval(modified_str, {"__builtins__": {}}, safe_globals))
        except Exception as e:
            print(f"Error evaluating trig expression: {e}")
            # Continue to other methods if this fails

    # Handle √ symbol format: 6(√6-1)
    if '√' in expr:
        # Handle pattern like "6(√6-1)"
        pattern = r'(\d+)\(√(\d+)(-|\+)(\d+)\)'
        match = re.match(pattern, expr)
        if match:
            a, b, op, c = match.groups()
            a, b, c = float(a), float(b), float(c)
            if op == '-':
                return a * (math.sqrt(b) - c)
            else:  # op == '+'
                return a * (math.sqrt(b) + c)

        # Handle pattern like "2√13"
        pattern = r'(\d*)(√\d+)'
        match = re.match(pattern, expr)
        if match:
            coef, sqrt_part = match.groups()
            coef = 1 if coef == '' else float(coef)
            sqrt_str = sqrt_part.replace('√', 'math.sqrt(') + ')'
            try:
                sqrt_val = eval(sqrt_str, {"math": math})
                return coef * sqrt_val
            except Exception as e:
                print(f"Error evaluating {sqrt_str}: {e}")
                pass

        try:
            # General replacement of √ symbol
            modified_str = re.sub(r'(\d*)√(\d+)', r'\1*math.sqrt(\2)', expr)
            # Handle implicit multiplication
            modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
            return float(eval(modified_str, {"math": math}))
        except Exception as e:
            print(f"Error evaluating modified string '{modified_str}': {e}")
            pass

    if 'π' in expr:
        # Pattern for (aπ)/b format
        pattern = r'\((\d+)π\)/(\d+)'
        match = re.match(pattern, expr)
        if match:
            a, b = match.groups()
            a, b = float(a), float(b)
            return (a * math.pi) / b

        # Pattern for aπ/b format (without parentheses)
        pattern = r'(\d+)π/(\d+)'
        match = re.match(pattern, expr)
        if match:
            a, b = match.groups()
            a, b = float(a), float(b)
            return (a * math.pi) / b

        # Handle other π expressions with general replacement
        try:
            # Replace π with math.pi for evaluation
            modified_str = expr.replace('π', '*math.pi')
            # Handle implicit multiplication and edge cases
            modified_str = re.sub(r'(\d+)\(', r'\1*(', modified_str)
            return float(eval(modified_str, {"math": math}))
        except Exception as e:
            print(f"Error evaluating π expression '{modified_str}': {e}")
            pass

    # Standard eval with math functions
    try:
        safe_globals = {
            "pi": math.pi,
            "sqrt": math.sqrt,
            "sin": math.sin,
            "cos": math.cos,
            "tan": math.tan,
            "math": math
        }
        return float(eval(expr, {"__builtins__": {}}, safe_globals))
    except Exception as e:
        print(f"Error in standard eval: {e}")
        # Fall back to Fraction
        from fractions import Fraction
        try:
            return float(Fraction(expr))
        except Exception as e:
            print(f"Error with Fraction conversion: {e}")
            # Try numerical approximation for complex expressions
            try:
                # Replace mathematical functions with their math module equivalents
                expr = expr.replace('sin', 'math.sin')
                expr = expr.replace('cos', 'math.cos')
                expr = expr.replace('tan', 'math.tan')
                expr = expr.replace('pi', 'math.pi')

                # Evaluate with a safe environment
                result = eval(expr, {"__builtins__": {}}, {"math": math})
                return float(result)
            except Exception as e:
                print(f"Error with numerical approximation: {e}")
                try:
                    # Import sympy only when needed
                    from sympy import symbols, sympify, pi, N

                    # Replace symbols with SymPy-compatible notation
                    sympy_compatible = expr
                    sympy_compatible = sympy_compatible.replace('π', 'pi')
                    sympy_compatible = sympy_compatible.replace('√', 'sqrt')

                    # Parse with SymPy's powerful expression parser
                    expr = sympify(sympy_compatible)

                    # Convert to floating point
                    numeric_value = float(N(expr))

                    print(f"Successfully parsed with SymPy: {numeric_value}")
                    return numeric_value, original_symbolic
                except Exception as e:
                    print(f"Error parsing with SymPy: {e}")
                    # If SymPy also fails, give up and raise the exception
                    raise ValueError(f"Could not parse: {expr}")


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


def analyze_answer_correctness(base_path, problem_status):
    """
    Analyze which problems in the sample of 50 problems (10 per level) were solved correctly
    by comparing model answers with ground truth answers. A problem is considered incorrect
    only if all of its answers (including retries) are not equal to the ground truth answer.
    For floating-point comparisons, answers are considered equal if they differ by at most 0.01.
    For fractions, both the fraction form and decimal form are checked.

    Also creates a confusion matrix comparing answer correctness with proof correctness.
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]

    # Dictionary to store aggregated statistics
    level_stats = {
        level: {
            variant: {
                "total_problems": 0,
                "problems_with_answers": 0,  # Problems that have at least one answer
                "all_incorrect_problems": set(),  # Problems where all provided answers are incorrect
                "some_correct_problems": set(),  # Problems that have at least one correct answer
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
                                        print(
                                            f"Problem {problem_id} ground truth expression '{gt_expr}' evaluated to {gt_answer}")
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
                    else:
                        level_stats[level][variant]["some_correct_problems"].add(problem_id)

    # Print aggregated statistics
    print("\nAggregated Statistics:")
    print("=" * 50)
    for level in levels:
        print(f"\nLevel {level}:")
        print("-" * 30)
        for variant in variants:
            stats = level_stats[level][variant]
            if stats["total_problems"] > 0:
                all_incorrect_percentage = (len(stats["all_incorrect_problems"]) / stats[
                    "problems_with_answers"]) * 100 if stats["problems_with_answers"] > 0 else 0
                print(f"\n{variant}:")
                print(f"  Total problems: {stats['total_problems']}")
                print(f"  Problems with answers: {stats['problems_with_answers']}")
                print(
                    f"  Problems with all incorrect answers: {len(stats['all_incorrect_problems'])} ({all_incorrect_percentage:.1f}%)")
                if stats["all_incorrect_problems"]:
                    print(f"  Problem IDs with all incorrect answers: {sorted(stats['all_incorrect_problems'])}")
                if stats["some_correct_problems"]:
                    print(f"  Problem IDs with at least one correct answer: {sorted(stats['some_correct_problems'])}")

    # Create confusion matrix for each variant
    print("\nConfusion Matrix (Answer Correctness vs Proof Correctness):")
    print("=" * 70)
    for variant in variants:
        variant_key = "analogy_based" if "analogy" in variant else "random"
        print(f"\n{variant}:")
        print("-" * 30)

        # Initialize confusion matrix counters
        correct_answer_correct_proof = 0  # At least one correct answer and proof is correct
        correct_answer_incorrect_proof = 0  # At least one correct answer but proof is incorrect
        incorrect_answer_correct_proof = 0  # All answers incorrect but proof is correct
        incorrect_answer_incorrect_proof = 0  # All answers incorrect and proof is incorrect

        # Track problem IDs for each category
        correct_answer_correct_proof_ids = set()
        correct_answer_incorrect_proof_ids = set()
        incorrect_answer_correct_proof_ids = set()
        incorrect_answer_incorrect_proof_ids = set()

        # Process each level
        for level in levels:
            level_problem_ids = set(LEVEL_PROBLEMS[level])
            for problem_id in level_problem_ids:
                # Check if problem has at least one correct answer
                has_correct_answer = problem_id in level_stats[level][variant]["some_correct_problems"]
                # Check if proof is correct
                has_correct_proof = problem_status[variant_key]["ft_union_frv_union_mrv"].get(problem_id, 0) == 1

                # Update confusion matrix counters and track problem IDs
                if has_correct_answer and has_correct_proof:
                    correct_answer_correct_proof += 1
                    correct_answer_correct_proof_ids.add(problem_id)
                elif has_correct_answer and not has_correct_proof:
                    correct_answer_incorrect_proof += 1
                    correct_answer_incorrect_proof_ids.add(problem_id)
                elif not has_correct_answer and has_correct_proof:
                    incorrect_answer_correct_proof += 1
                    incorrect_answer_correct_proof_ids.add(problem_id)
                else:
                    incorrect_answer_incorrect_proof += 1
                    incorrect_answer_incorrect_proof_ids.add(problem_id)

        # Print confusion matrix
        print("\nConfusion Matrix:")
        print("                 Proof Correct | Proof Incorrect")
        print("Answer Correct   {:^14} | {:^15}".format(correct_answer_correct_proof, correct_answer_incorrect_proof))
        print(
            "Answer Incorrect {:^14} | {:^15}".format(incorrect_answer_correct_proof, incorrect_answer_incorrect_proof))

        # Calculate and print statistics
        total = correct_answer_correct_proof + correct_answer_incorrect_proof + incorrect_answer_correct_proof + incorrect_answer_incorrect_proof
        print(f"\nTotal problems: {total}")
        print(
            f"Problems with at least one correct answer: {correct_answer_correct_proof + correct_answer_incorrect_proof}")
        print(f"Problems with correct proof: {correct_answer_correct_proof + incorrect_answer_correct_proof}")
        print(f"Problems with both correct answer and proof: {correct_answer_correct_proof}")

        # Print problem IDs for each category
        print("\nProblem IDs by category:")
        print(f"Correct answer, correct proof: {sorted(correct_answer_correct_proof_ids)}")
        print(f"Correct answer, incorrect proof: {sorted(correct_answer_incorrect_proof_ids)}")
        print(f"Incorrect answer, correct proof: {sorted(incorrect_answer_correct_proof_ids)}")
        print(f"Incorrect answer, incorrect proof: {sorted(incorrect_answer_incorrect_proof_ids)}")

        # For analogy-based variant, specifically highlight problems with correct proof but incorrect answers
        if variant == "variant_analogy_based_model_o1":
            print("\nAnalogy-based problems with correct proof but incorrect answers:")
            print(f"Problem IDs: {sorted(incorrect_answer_correct_proof_ids)}")
            print(f"Count: {len(incorrect_answer_correct_proof_ids)}")


def analyze_proof_correctness(base_path):
    """
    Analyze proof correctness only for problems that have at least one correct answer.
    A problem is considered to have a correct answer if GT_ANSWER matches either ANSWER or RETRY_ANSWER.
    Also tracks and displays whether problems have any incorrect answers.
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]

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

    # Calculate success rates and update problem status
    for level in levels:
        print(f"\nProcessing Level {level}")
        print("=" * 50)
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            print(f"Level {level} directory not found")
            continue

        level_rates = calculate_ablation_success_rates(level_dir, level, problem_status)

    # Print statistics
    print("\nProof Correctness Statistics (for problems with at least one correct answer):")
    print("=" * 70)
    for level in levels:
        print(f"\nLevel {level}:")
        print("-" * 30)
        level_problem_ids = set(LEVEL_PROBLEMS[level])

        for variant in variants:
            variant_key = "analogy_based" if "analogy" in variant else "random"

            # Track problems with correct answers and their proof status
            problems_with_correct_answers = set()
            problems_with_correct_proofs = set()
            problems_with_incorrect_answers = set()  # Track problems with any incorrect answers

            # Process each problem
            for problem_id in sorted(level_problem_ids):
                # Check if this problem has at least one correct answer
                has_correct_answer = False
                has_incorrect_answer = False
                gt_answer = None

                # First get the ground truth answer
                run_0_file = os.path.join(level_dir, f"{variant}_problem_{problem_id}_run_0.txt")
                if os.path.exists(run_0_file):
                    with open(run_0_file, 'r') as f:
                        content = f.read()
                        gt_match = re.search(r'GT_ANSWER:\s*(.*?)(?:\n|$)', content)
                        if gt_match:
                            gt_expr = gt_match.group(1).strip()
                            if gt_expr:
                                try:
                                    gt_answer = int(gt_expr)
                                except ValueError:
                                    gt_answer = evaluate_math_expression(gt_expr)
                                    if gt_answer is None:
                                        gt_answer = parse_fraction(gt_expr)

                if gt_answer is not None:
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
                                    if is_answer_correct(answer, gt_answer):
                                        has_correct_answer = True
                                    else:
                                        has_incorrect_answer = True

                                # Check RETRY_ANSWER
                                retry_match = re.search(r'RETRY_ANSWER:\s*(.*?)(?:\n|$)', content)
                                if retry_match:
                                    retry_answer = retry_match.group(1).strip()
                                    if is_answer_correct(retry_answer, gt_answer):
                                        has_correct_answer = True
                                    else:
                                        has_incorrect_answer = True

                if has_correct_answer:
                    problems_with_correct_answers.add(problem_id)
                    if has_incorrect_answer:
                        problems_with_incorrect_answers.add(problem_id)
                    # Check if proof is correct (using ft_union_frv_union_mrv)
                    if problem_status[variant_key]["ft_union_frv_union_mrv"].get(problem_id, 0) == 1:
                        problems_with_correct_proofs.add(problem_id)

            # Print statistics for this variant
            if problems_with_correct_answers:
                proof_correct_percentage = (len(problems_with_correct_proofs) / len(
                    problems_with_correct_answers)) * 100
                print(f"\n{variant}:")
                print(f"  Problems with correct answers: {len(problems_with_correct_answers)}")
                print(f"  Problems with incorrect answers: {len(problems_with_incorrect_answers)}")
                print(f"  Problems with correct proofs: {len(problems_with_correct_proofs)}")
                print(f"  Proof correctness rate: {proof_correct_percentage:.1f}%")

                # Print details for problems with correct answers
                print("\n  Problem Details:")
                for problem_id in sorted(problems_with_correct_answers):
                    has_correct_proof = problem_id in problems_with_correct_proofs
                    has_incorrect = problem_id in problems_with_incorrect_answers
                    print(
                        f"    Problem {problem_id}: Answer ✓{' (with incorrect attempts)' if has_incorrect else ''}, Proof {'✓' if has_correct_proof else '✗'}")


def analyze_errors(base_path):
    """
    Analyze errors from the 50 problems (10 per level) in the predefined list.
    For each problem, gather all error messages that appear after "ERROR_TIER" in the result files.
    Also aggregates errors by their TIER number.
    
    Args:
        base_path (str): Base path to the results directory
        
    Returns:
        dict: Dictionary containing error analysis results per level
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Dictionary to store error analysis results
    error_analysis = {
        variant: {
            level: {
                "problems": {},  # problem_id -> list of error messages
                "error_frequency": {},  # error message -> count
                "tier_frequency": {1: 0, 2: 0, 3: 0},  # Initialize all tiers with 0
                "problems_with_errors": 0,  # count of problems that had any errors
                "total_problems": 0  # total number of problems analyzed
            } for level in levels
        } for variant in variants
    }
    
    for variant in variants:
        for level in levels:
            print(f"\nAnalyzing Errors for {variant} Level {level}")
            print("=" * 50)
            level_dir = os.path.join(base_path, f"level_{level}")
            if not os.path.exists(level_dir):
                print(f"Level {level} directory not found")
                continue
                
            # Get the list of problem IDs for this level
            level_problem_ids = set(LEVEL_PROBLEMS[level])
            error_analysis[variant][level]["total_problems"] = len(level_problem_ids)
            
            # Process each problem in the level's list
            for problem_id in sorted(level_problem_ids):
                problem_errors = []
                has_errors = False
                
                # Check all runs for this problem
                for run_number in range(3):  # Check runs 0, 1, and 2
                    file_path = os.path.join(level_dir, f"{variant}_problem_{problem_id}_run_{run_number}.txt")
                    if not os.path.exists(file_path):
                        continue
                        
                    with open(file_path, 'r') as f:
                        content = f.read()
                        
                    # Find all error messages after ERROR_TIER
                    error_sections = content.split("ERROR_TIER: ")
                    if len(error_sections) > 1:  # If there are any errors
                        has_errors = True
                        print(f"  Run {run_number}:")
                        for section in error_sections[1:]:  # Skip the first split which is before any ERROR_TIER
                            # Get the complete error message including all content after ERROR_TIER
                            error_msg = section.strip()
                            if error_msg:
                                print(f"    - {error_msg}")
                                problem_errors.append(error_msg)

                                # Update error frequency
                                if error_msg not in error_analysis[variant][level]["error_frequency"]:
                                    error_analysis[variant][level]["error_frequency"][error_msg] = 0
                                error_analysis[variant][level]["error_frequency"][error_msg] += 1

                                # Update tier frequency
                                if error_msg.startswith("TIER1_"):
                                    error_analysis[variant][level]["tier_frequency"][1] += 1
                                elif error_msg.startswith("TIER2_"):
                                    error_analysis[variant][level]["tier_frequency"][2] += 1
                                elif error_msg.startswith("TIER3_"):
                                    error_analysis[variant][level]["tier_frequency"][3] += 1

                # Store errors for this problem if any were found
                if has_errors:
                    error_analysis[variant][level]["problems"][problem_id] = problem_errors
                    error_analysis[variant][level]["problems_with_errors"] += 1
            
            # Print summary for this level
            print(f"\nLevel {level} Error Analysis:")
            print(f"Total Problems: {error_analysis[variant][level]['total_problems']}")
            print(f"Problems with Errors: {error_analysis[variant][level]['problems_with_errors']}")
            print(
                f"Error Rate: {(error_analysis[variant][level]['problems_with_errors'] / error_analysis[variant][level]['total_problems'] * 100):.1f}%")
            
            if error_analysis[variant][level]["error_frequency"]:
                print("\nMost Common Errors:")
                # Sort errors by frequency
                sorted_errors = sorted(error_analysis[variant][level]["error_frequency"].items(), 
                                     key=lambda x: x[1], reverse=True)
                for error_msg, count in sorted_errors[:5]:  # Show top 5 errors
                    print(f"  - {error_msg} (occurred {count} times)")
            
            if error_analysis[variant][level]["tier_frequency"]:
                print("\nError Distribution by Tier:")
                # Sort tiers by number
                sorted_tiers = sorted(error_analysis[variant][level]["tier_frequency"].items())
                for tier_num, count in sorted_tiers:
                    print(f"  - TIER_{tier_num}: {count} errors")
    
    # Create the plot
    plot_tier_error_distribution(error_analysis, base_path)
    
    return error_analysis


def plot_tier_error_distribution(error_analysis, base_path):
    """
    Create three subplots showing error counts by level for each tier.
    Each subplot represents one tier, comparing analogy-based and base model approaches.

    Args:
        error_analysis (dict): Dictionary containing error analysis results
        base_path (str): Base path to save the plot
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]

    # Create figure with white background and more height
    fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize=(15, 20), facecolor='white')  # Reduced height from 22 to 20
    axes = [ax1, ax2, ax3]

    # Width of each bar
    bar_width = 0.35

    # Define single color for each method
    analogy_color = '#2171b5'  # Blue
    base_model_color = '#cb181d'  # Red

    # Calculate positions for bars
    indices = np.arange(len(levels))

    # Plot data for each tier in separate subplots
    for tier, ax in enumerate(axes, 1):
        # Add light gray background to separate levels
        for i in indices:
            ax.axvspan(i - 0.5, i + 0.5, color='#f8f9fa', alpha=0.5)

        # Get data for both variants
        analogy_data = [error_analysis[variants[0]][level]["tier_frequency"][tier] for level in levels]
        random_data = [error_analysis[variants[1]][level]["tier_frequency"][tier] for level in levels]

        # Plot bars
        ax.bar(indices - bar_width / 2, analogy_data, bar_width,
               label='analogy-based', color=analogy_color,
               edgecolor='black', linewidth=1)
        
        # Create bars with white vertical lines for base model
        bars = ax.bar(indices + bar_width / 2, random_data, bar_width,
               label='base model', color=base_model_color,
               edgecolor='black', linewidth=1)
        
        # Add white vertical lines to base model bars
        for bar in bars:
            bar.set_hatch('|')  # Single vertical line
            bar.set_edgecolor('white')  # White hatch color
            bar.set_linewidth(2)  # Make the lines slightly thicker

        # Add grid lines
        ax.grid(True, linestyle='--', alpha=0.3, color='gray', zorder=0)
        
        # Add black horizontal lines at major y-ticks
        yticks = ax.get_yticks()
        for y in yticks:
            ax.axhline(y=y, color='black', linewidth=0.8, alpha=0.3, zorder=1)
        
        # Add black vertical lines at each level
        for x in indices:
            ax.axvline(x=x, color='black', linewidth=0.8, alpha=0.3, zorder=1)

        # Add "Lower is better" text with arrow inside each subplot
        max_value = max(max(analogy_data), max(random_data))
        text_y = max_value * 0.85  # Position text at 85% of max height
        arrow_start_y = max_value * 0.8  # Start arrow at 80% of max height
        arrow_end_y = max_value * 0.65  # End arrow at 65% of max height
        
        ax.text(0.5, text_y, 'Lower is better', fontsize=32, fontweight='bold',
                ha='center', va='bottom')
        ax.annotate('', xy=(0.5, arrow_end_y), xytext=(0.5, arrow_start_y),
                    arrowprops=dict(facecolor='black', width=2, headwidth=15, headlength=20))

        # Customize subplot
        if tier == 3:  # For the third subplot, adjust labelpad to bring "Level" closer to axis
            ax.set_xlabel('Level', fontsize=28, fontweight='bold', labelpad=35)
        else:
            ax.set_xlabel('Level', fontsize=28, fontweight='bold', labelpad=15)
        ax.set_ylabel('Number of Errors', fontsize=28, fontweight='bold', labelpad=15)
        ax.set_title(f'Tier {tier} Error Distribution',
                     fontsize=32, fontweight='bold', pad=20)

        # Set x-axis ticks
        ax.set_xticks(indices)
        ax.set_xticklabels(levels, fontsize=24, fontweight='bold')

        # Set dynamic y-axis limits and ticks based on actual data and tier
        max_value = max(max(analogy_data), max(random_data))
        
        # Add padding for the text and arrow
        y_max = max_value * 1.2

        # Round up y_max to the next multiple of 10
        y_max = math.ceil(y_max / 10.0) * 10

        # Set specific y_max limits based on tier
        if tier == 1:
            y_max = min(100, y_max)  # Cap at 100 for Tier 1
        elif tier == 3:
            y_max = min(30, y_max)   # Cap at 30 for Tier 3
        
        # Ensure minimum y_max is 10
        y_max = max(10, y_max)

        # Create ticks at every multiple of 10
        ticks = np.arange(0, y_max + 10, 10)
        
        ax.set_ylim(0, y_max)
        ax.set_yticks(ticks)
        ax.tick_params(axis='y', labelsize=24)

        # Make y-axis labels bold and black
        for label in ax.get_yticklabels():
            label.set_fontweight('bold')
            label.set_color('black')

        # Remove top and right spines
        ax.spines['top'].set_visible(False)
        ax.spines['right'].set_visible(False)

        # Make left and bottom spines thicker and black
        ax.spines['left'].set_linewidth(1.5)
        ax.spines['left'].set_color('black')
        ax.spines['bottom'].set_linewidth(1.5)
        ax.spines['bottom'].set_color('black')

    # Adjust subplot spacing
    plt.subplots_adjust(hspace=0.4)  # Reduced from default

    # Create a common legend for all subplots
    handles, labels = ax1.get_legend_handles_labels()
    legend = fig.legend(handles, labels,
                      fontsize=28,
                      loc='center',
                      bbox_to_anchor=(0.5, 0.02),  # Position legend just above the x-axis label of the third subplot
                      frameon=True,
                      edgecolor='black',
                      fancybox=False,
                      borderpad=0.4,
                      handlelength=2.0,
                      handletextpad=0.4,
                      labelspacing=0.2,
                      columnspacing=0.3,
                      ncol=2)

    # Make legend text bold
    for text in legend.get_texts():
        text.set_fontweight('bold')

    # Adjust layout with space for legend at bottom
    plt.tight_layout(rect=[0, 0.02, 1, 0.98])  # Adjusted to accommodate legend position

    # Save the plot
    plt.savefig(os.path.join(base_path, 'tier_error_distribution.png'),
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.close()

    return problem_status

def plot_retries_and_runs(base_path):
    """
    Plot average retries and runs per level for both variants.
    Creates two subplots: one for retries and one for runs.

    Args:
        base_path (str): Base path to the results directory
    """
    levels = range(1, 6)
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]

    # Store detailed data for each level
    level_data = {
        level: {
            variant: {
                "total_retries": 0,
                "total_runs": 0,
                "problem_count": 0,
                "avg_retries": 0,
                "avg_runs": 0,
                "problems_with_runs": set()
            } for variant in variants
        } for level in levels
    }

    # Initialize data lists for plotting
    retries_data = {variant: [] for variant in variants}
    runs_data = {variant: [] for variant in variants}

    # Calculate averages for each level and variant
    for level in levels:
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            continue

        for variant in variants:
            # Get the list of problem IDs for this level
            level_problem_ids = set(LEVEL_PROBLEMS[level])

            for problem_id in level_problem_ids:
                problem_has_runs = False
                for run_num in range(3):  # Check runs 0, 1, and 2
                    file_path = os.path.join(level_dir, f"{variant}_problem_{problem_id}_run_{run_num}.txt")
                    if os.path.exists(file_path):
                        problem_has_runs = True
                        level_data[level][variant]["total_runs"] += 1
                        with open(file_path, 'r') as f:
                            content = f.read()
                            retries_match = re.search(r'#RETRIES:\s*(\d+)', content)
                            if retries_match:
                                level_data[level][variant]["total_retries"] += int(retries_match.group(1))

                if problem_has_runs:
                    level_data[level][variant]["problem_count"] += 1
                    level_data[level][variant]["problems_with_runs"].add(problem_id)

            # Calculate averages
            if level_data[level][variant]["problem_count"] > 0:
                level_data[level][variant]["avg_retries"] = (
                        level_data[level][variant]["total_retries"] /
                        level_data[level][variant]["problem_count"]
                )
                level_data[level][variant]["avg_runs"] = (
                        level_data[level][variant]["total_runs"] /
                        level_data[level][variant]["problem_count"]
                )

            # Store data for plotting
            retries_data[variant].append(level_data[level][variant]["avg_retries"])
            runs_data[variant].append(level_data[level][variant]["avg_runs"])

    # Calculate averages across all levels
    print("\nAverages across all levels:")
    print("=" * 50)
    for variant in variants:
        variant_name = "Analogy-based" if "analogy" in variant else "Base model"
        avg_retries = sum(retries_data[variant]) / len(retries_data[variant])
        avg_runs = sum(runs_data[variant]) / len(runs_data[variant])
        print(f"\n{variant_name}:")
        print(f"  Average retries: {avg_retries:.2f}")
        print(f"  Average runs: {avg_runs:.2f}")

    # Create figure with two subplots - make it wider to accommodate legend
    fig = plt.figure(figsize=(26, 20), facecolor='white')  # Increased width to match other plots
    gs = plt.GridSpec(3, 1, height_ratios=[4, 1, 4], hspace=0.3)  # Reduced hspace from 0.5 to 0.3
    ax1 = fig.add_subplot(gs[0])  # Top subplot
    ax2 = fig.add_subplot(gs[2])  # Bottom subplot

    # Set the same aspect ratio and dimensions for both plots
    ax1.set_box_aspect(1 / 2.0)
    ax2.set_box_aspect(1 / 2.0)

    # Add "Lower is better" text with arrow for both plots - inside the plots
    # For the top subplot (retries)
    ax1.text(2.0, 13, 'Lower is better', fontsize=32, fontweight='bold',
             ha='center', va='bottom')
    ax1.annotate('', xy=(2.0, 11), xytext=(2.0, 12.5),
                 arrowprops=dict(facecolor='black', width=2, headwidth=15, headlength=20))

    # For the bottom subplot (runs)
    ax2.text(2.0, 2.6, 'Lower is better', fontsize=32, fontweight='bold',
             ha='center', va='bottom')
    ax2.annotate('', xy=(2.0, 2.2), xytext=(2.0, 2.5),
                 arrowprops=dict(facecolor='black', width=2, headwidth=15, headlength=20))

    # Add light gray background to alternate between levels
    for i in range(len(levels)):
        if i % 2 == 0:
            ax1.axvspan(i+0.5, i+1.5, color='#f8f9fa', alpha=0.5)
            ax2.axvspan(i+0.5, i+1.5, color='#f8f9fa', alpha=0.5)

    # Colors for variants
    variant_colors = {
        "variant_analogy_based_model_o1": '#2171b5',  # Blue
        "variant_random_all_theorems_model_o1": '#cb181d'  # Red
    }

    # Plot lines for both subplots
    lines = []
    for variant in variants:
        # Set marker face color - filled for analogy-based, hollow for base model
        marker_face_color = variant_colors[variant] if 'analogy' in variant else 'white'
        
        # Plot retries data
        line1 = ax1.plot(levels, retries_data[variant], 'o-',
                 color=variant_colors[variant],
                 linewidth=3, markersize=14,
                 markerfacecolor=marker_face_color,
                 markeredgewidth=2)[0]

        # Plot runs data
        ax2.plot(levels, runs_data[variant], 'o-',
                 color=variant_colors[variant],
                 linewidth=3, markersize=14,
                 markerfacecolor=marker_face_color,
                 markeredgewidth=2)
                 
        lines.append(line1)

    # Create legend in the middle
    fig.legend(lines,
               ["Analogy-based", "Base model"],
               loc='center',
               bbox_to_anchor=(0.5, 0.5),
               ncol=2,
               fontsize=32,
               prop={'weight': 'bold'},
               frameon=True,
               edgecolor='black',
               framealpha=1.0,
               borderpad=0.2,
               columnspacing=0.5,
               handletextpad=0.5,
               handlelength=1.0,
               borderaxespad=0.1)

    # Customize retries subplot
    ax1.set_xlabel('Level', fontsize=32, labelpad=15, fontweight='bold')
    ax1.set_ylabel('Average retries', fontsize=32, labelpad=15, fontweight='bold')
    ax1.set_title(
        'Average retries per problem (max = 15)',
        fontsize=36, pad=50, fontweight='bold')
    ax1.grid(True, linestyle='--', alpha=0.3)

    # Add horizontal dashed line at y=15
    ax1.axhline(y=15, color='gray', linestyle='--', alpha=0.8, linewidth=2.5)

    # Set y-axis ticks to multiples of 1 for retries subplot
    ax1.set_yticks(range(0, 16))  # 0 to 15 in steps of 1

    # Make y-axis numbers bold and bigger
    ax1.tick_params(axis='y', which='major', labelsize=28)
    for label in ax1.yaxis.get_ticklabels():
        label.set_fontweight('bold')

    ax1.set_xticks(levels)
    ax1.tick_params(axis='x', which='major', labelsize=28)
    for label in ax1.xaxis.get_ticklabels():
        label.set_fontweight('bold')

    # Remove top and right spines
    ax1.spines['top'].set_visible(False)
    ax1.spines['right'].set_visible(False)

    # Make left and bottom spines thicker
    ax1.spines['left'].set_linewidth(1.5)
    ax1.spines['bottom'].set_linewidth(1.5)

    # Customize runs subplot
    ax2.set_xlabel('Level', fontsize=32, labelpad=15, fontweight='bold')
    ax2.set_ylabel('Average runs', fontsize=32, labelpad=15, fontweight='bold')
    ax2.set_title('Average runs per problem (max = 3)',
                  fontsize=36, pad=30, fontweight='bold')
    ax2.grid(True, linestyle='--', alpha=0.3)

    # Add horizontal dashed line at y=3
    ax2.axhline(y=3, color='gray', linestyle='--', alpha=0.8, linewidth=2.5)

    # Set y-axis ticks to multiples of 1 for runs subplot
    ax2.set_yticks(range(0, 4))  # 0 to 3 in steps of 1

    ax2.set_xticks(levels)
    ax2.tick_params(axis='x', which='major', labelsize=28)
    for label in ax2.xaxis.get_ticklabels():
        label.set_fontweight('bold')

    # Make y-axis numbers bold and bigger for second subplot
    ax2.tick_params(axis='y', which='major', labelsize=28)
    for label in ax2.yaxis.get_ticklabels():
        label.set_fontweight('bold')

    # Remove top and right spines
    ax2.spines['top'].set_visible(False)
    ax2.spines['right'].set_visible(False)

    # Make left and bottom spines thicker
    ax2.spines['left'].set_linewidth(1.5)
    ax2.spines['bottom'].set_linewidth(1.5)

    # Adjust layout
    plt.tight_layout(rect=[0, 0, 1, 0.95])  # Give more space at top

    # Save the plot
    plt.savefig(os.path.join(base_path, 'retries_and_runs.png'),
                dpi=300, bbox_inches='tight', facecolor='white')
    plt.close()

def data_stats(base_path):
    """
    Analyze the GT_THEOREM_SEQUENCE lengths from run_0 files for problems in LEVEL_PROBLEMS.
    Counts the number of steps in each sequence and provides statistics.
    
    Args:
        base_path (str): Base path to the results directory
        
    Returns:
        dict: Dictionary containing statistics about sequence lengths
    """
    import numpy as np
    sequence_lengths = []
    
    print("\nAnalyzing GT_THEOREM_SEQUENCE lengths:")
    print("=" * 50)
    
    for level in sorted(LEVEL_PROBLEMS.keys()):
        print(f"\nLevel {level}:")
        print("-" * 20)
        for problem_id in sorted(LEVEL_PROBLEMS[level]):
            file_path = os.path.join(base_path, f"level_{level}/variant_analogy_based_model_o1_problem_{problem_id}_run_0.txt")
            try:
                with open(file_path, 'r') as f:
                    content = f.read()
                    # Find GT_THEOREM_SEQUENCE section
                    sequence_section = content.split('GT_THEOREM_SEQUENCE:')
                    if len(sequence_section) > 1:
                        # Get the lines after GT_THEOREM_SEQUENCE until next empty line
                        sequence_lines = sequence_section[1].strip().split('\n')
                        # Count non-empty lines until we hit an empty line
                        steps = 0
                        for line in sequence_lines:
                            if not line.strip():  # Stop at empty line
                                break
                            if line.strip():  # Count non-empty lines
                                steps += 1
                        sequence_lengths.append(steps)
                        print(f"Problem {problem_id}: {steps} steps")
                    else:
                        print(f"Problem {problem_id}: No GT_THEOREM_SEQUENCE found")
            except FileNotFoundError:
                print(f"Problem {problem_id}: File not found")
    
    # Calculate statistics
    stats = {}
    if sequence_lengths:
        stats['average'] = np.mean(sequence_lengths)
        stats['minimum'] = np.min(sequence_lengths)
        stats['maximum'] = np.max(sequence_lengths)
        stats['std_dev'] = np.std(sequence_lengths)
        stats['total_problems'] = len(sequence_lengths)
        
        print("\nStatistics:")
        print("-" * 20)
        print(f"Average steps: {stats['average']:.2f}")
        print(f"Minimum steps: {stats['minimum']}")
        print(f"Maximum steps: {stats['maximum']}")
        print(f"Standard deviation: {stats['std_dev']:.2f}")
        print(f"Total problems analyzed: {stats['total_problems']}")
    
    return stats

if __name__ == "__main__":
    base_path = "/Users/osultan/PycharmProjects/FormalGeo/results"
    # plot_success_rates(base_path)
    problem_status = plot_ablation_study(base_path)
    # calculate_analogy_stability(base_path)
    # analyze_answer_correctness(base_path, problem_status)
    # error_analysis = analyze_errors(base_path)
    plot_retries_and_runs(base_path)
    data_stats(base_path)