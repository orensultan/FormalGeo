import matplotlib.pyplot as plt
import numpy as np
import os
import re
from collections import defaultdict
import json
from src.formalgeo.config.config import MAX_RUNS, MAX_RETRIES_IN_RUN
def calculate_success_rates(base_path):
    results = defaultdict(lambda: defaultdict(dict))
    for level in range(1, 3):
        level_dir = os.path.join(base_path, f"level_{level}")
        if not os.path.exists(level_dir):
            continue

        # Initialize counters for each variant
        variant_stats = {
            "variant_analogy_based_model_o1": {
                "total_problems": 0,
                "successful_answers_first_try": 0,
                "successful_answers_with_retries": 0,
                "successful_theorems_first_try": 0,
                "successful_theorems_with_retries": 0
            },
            "variant_random_all_theorems_model_o1": {
                "total_problems": 0,
                "successful_answers_first_try": 0,
                "successful_answers_with_retries": 0,
                "successful_theorems_first_try": 0,
                "successful_theorems_with_retries": 0
            }
        }

        # Group files by variant and problem_id
        problem_groups = defaultdict(lambda: defaultdict(list))
        for result_file in os.listdir(level_dir):
            if not result_file.endswith('.txt'):
                continue
                
            # Extract variant and problem_id
            variant = None
            for v in variant_stats.keys():
                if result_file.startswith(v):
                    variant = v
                    break
            
            if variant is None:
                continue

            # Extract problem_id from filename
            problem_match = re.search(r'problem_(\d+)_run_', result_file)
            if not problem_match:
                continue
                
            problem_id = problem_match.group(1)
            problem_groups[variant][problem_id].append(result_file)

        # Process each problem group
        for variant, problems in problem_groups.items():
            for problem_id, files in problems.items():
                variant_stats[variant]["total_problems"] += 1
                
                # Track if any run succeeded for this problem
                any_answer_correct = False
                any_first_try_success = False
                any_theorem_success = False
                
                # Check if last run exists for this problem
                last_run = f"run_{MAX_RUNS-1}"
                has_last_run = any(last_run in f for f in files)
                theorem_with_retries_success = not has_last_run  # Success if no last run
                
                # Get GT_ANSWER from any file (they should all have the same GT_ANSWER)
                gt_answer = None
                for result_file in files:
                    file_path = os.path.join(level_dir, result_file)
                    with open(file_path, 'r') as f:
                        content = f.read()
                        gt_answer_match = re.search(r'GT_ANSWER:\s*\n(\d+)', content)
                        if gt_answer_match:
                            gt_answer = gt_answer_match.group(1)
                            break
                
                if gt_answer is None:
                    continue
                
                # Process all runs for this problem
                for result_file in files:
                    file_path = os.path.join(level_dir, result_file)
                    with open(file_path, 'r') as f:
                        content = f.read()

                        # Find the model response section
                        model_response_match = re.search(r'\*\*\*MODEL_RESPONSE_BEGIN\*\*\*(.*?)\*\*\*MODEL_RESPONSE_END\*\*\*', content, re.DOTALL)
                        if not model_response_match:
                            continue

                        model_response = model_response_match.group(1)

                        # Check both ANSWER and RETRY_ANSWER on new lines
                        answer_match = re.search(r'ANSWER:\s*\n(\d+)', model_response)
                        retry_answer_match = re.search(r'RETRY_ANSWER:\s*\n(\d+)', model_response)
                        retries_match = re.search(r'#RETRIES:\s*(\d+)', content)
                        runs_match = re.search(r'#RUNS:\s*(\d+)', content)

                        if (answer_match or retry_answer_match) and retries_match and runs_match:
                            # Parse retries and runs as integers
                            retries = int(retries_match.group(1))
                            runs = int(runs_match.group(1))
                            
                            # Check if any answer matches ground truth
                            answer_correct = False
                            if answer_match and answer_match.group(1) == gt_answer:
                                answer_correct = True
                            if retry_answer_match and retry_answer_match.group(1) == gt_answer:
                                answer_correct = True
                            
                            # First try success (both RETRIES and RUNS are 0)
                            is_first_try_success = retries == 0 and runs == 0
                            
                            # Update success flags for this problem
                            if answer_correct:
                                any_answer_correct = True
                                if is_first_try_success:
                                    any_first_try_success = True
                            
                            if is_first_try_success:
                                any_theorem_success = True
                            
                            # Check theorem sequence success with retries
                            if has_last_run and last_run in result_file:
                                if retries == MAX_RETRIES_IN_RUN:
                                    theorem_with_retries_success = False
                
                # Update counters based on problem-level success
                if any_answer_correct:
                    variant_stats[variant]["successful_answers_with_retries"] += 1
                    if any_first_try_success:
                        variant_stats[variant]["successful_answers_first_try"] += 1
                
                if any_theorem_success:
                    variant_stats[variant]["successful_theorems_first_try"] += 1
                
                if theorem_with_retries_success:
                    variant_stats[variant]["successful_theorems_with_retries"] += 1

        # Calculate and store success rates for each variant
        for variant, stats in variant_stats.items():
            total_problems = stats["total_problems"]
            
            # Answer success rates
            answer_success_rate_first_try = stats["successful_answers_first_try"] / total_problems if total_problems > 0 else 0
            answer_success_rate_with_retries = stats["successful_answers_with_retries"] / total_problems if total_problems > 0 else 0
            
            # Theorem sequence success rates
            theorem_success_rate_first_try = stats["successful_theorems_first_try"] / total_problems if total_problems > 0 else 0
            theorem_success_rate_with_retries = stats["successful_theorems_with_retries"] / total_problems if total_problems > 0 else 0

            results[f"level{level}"][variant] = {
                "success_rate_answer_first_try": answer_success_rate_first_try,
                "success_rate_answer_with_retries": answer_success_rate_with_retries,
                "success_rate_theorem_sequence_first_try": theorem_success_rate_first_try,
                "success_rate_theorem_sequence_with_retries": theorem_success_rate_with_retries
            }
    
    return results

def plot_success_rates(results):
    """Create two plots: one for answer success rates and one for theorem sequence success rates."""
    levels = [1, 2]
    variants = ["variant_analogy_based_model_o1", "variant_random_all_theorems_model_o1"]
    
    # Prepare data for plotting
    data = {
        'analogy_based': {
            'answer_first_try': [],
            'answer_with_retries': [],
            'theorem_first_try': [],
            'theorem_with_retries': []
        },
        'random': {
            'answer_first_try': [],
            'answer_with_retries': [],
            'theorem_first_try': [],
            'theorem_with_retries': []
        }
    }
    
    for level in levels:
        level_key = f"level{level}"
        if level_key in results:
            for variant in variants:
                if variant in results[level_key]:
                    if variant == "variant_analogy_based_model_o1":
                        data['analogy_based']['answer_first_try'].append(results[level_key][variant]["success_rate_answer_first_try"])
                        data['analogy_based']['answer_with_retries'].append(results[level_key][variant]["success_rate_answer_with_retries"])
                        data['analogy_based']['theorem_first_try'].append(results[level_key][variant]["success_rate_theorem_sequence_first_try"])
                        data['analogy_based']['theorem_with_retries'].append(results[level_key][variant]["success_rate_theorem_sequence_with_retries"])
                    else:
                        data['random']['answer_first_try'].append(results[level_key][variant]["success_rate_answer_first_try"])
                        data['random']['answer_with_retries'].append(results[level_key][variant]["success_rate_answer_with_retries"])
                        data['random']['theorem_first_try'].append(results[level_key][variant]["success_rate_theorem_sequence_first_try"])
                        data['random']['theorem_with_retries'].append(results[level_key][variant]["success_rate_theorem_sequence_with_retries"])
    
    # Create answer success rate plot
    plt.figure(figsize=(10, 6))
    # Random examples - both lines in blue
    plt.plot(levels, data['random']['answer_first_try'], 'o-', color='#1f77b4', label='Random examples (first try)', linewidth=2, markersize=8)
    plt.plot(levels, data['random']['answer_with_retries'], 's--', color='#1f77b4', label='Random examples (with verifier feedback)', linewidth=2, markersize=8)
    # Analogous examples - both lines in orange
    plt.plot(levels, data['analogy_based']['answer_first_try'], 'o-', color='#ff7f0e', label='Analogous examples (first try)', linewidth=2, markersize=8)
    plt.plot(levels, data['analogy_based']['answer_with_retries'], 's--', color='#ff7f0e', label='Analogous examples (with verifier feedback)', linewidth=2, markersize=8)
    
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate', fontsize=12)
    plt.title('o1 Model Answer Success Rate Comparison Across Levels', fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10)
    plt.gca().yaxis.set_major_formatter(plt.FuncFormatter(lambda y, _: '{:.0%}'.format(y)))
    plt.ylim(0, 1)
    plt.xticks(levels)
    plt.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    plt.tight_layout()
    plt.savefig('answer_success_rate.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    # Create theorem sequence success rate plot
    plt.figure(figsize=(10, 6))
    # Random examples - both lines in blue
    plt.plot(levels, data['random']['theorem_first_try'], 'o-', color='#1f77b4', label='Random examples (first try)', linewidth=2, markersize=8)
    plt.plot(levels, data['random']['theorem_with_retries'], 's--', color='#1f77b4', label='Random examples (with verifier feedback)', linewidth=2, markersize=8)
    # Analogous examples - both lines in orange
    plt.plot(levels, data['analogy_based']['theorem_first_try'], 'o-', color='#ff7f0e', label='Analogous examples (first try)', linewidth=2, markersize=8)
    plt.plot(levels, data['analogy_based']['theorem_with_retries'], 's--', color='#ff7f0e', label='Analogous examples (with verifier feedback)', linewidth=2, markersize=8)
    
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate', fontsize=12)
    plt.title('o1 Model Theorem Sequence Success Rate Comparison Across Levels', fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10)
    plt.gca().yaxis.set_major_formatter(plt.FuncFormatter(lambda y, _: '{:.0%}'.format(y)))
    plt.ylim(0, 1)
    plt.xticks(levels)
    plt.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    plt.tight_layout()
    plt.savefig('theorem_success_rate.png', dpi=300, bbox_inches='tight')
    plt.close()

if __name__ == "__main__":
    base_path = "../../../results"
    results = calculate_success_rates(base_path)

    print("\nSuccess Rates:")
    for level, variants in results.items():
        print(f"\n{level}:")
        for variant, rates in variants.items():
            print(f"  {variant}:")
            print(f"    Answer success rate (first try): {rates['success_rate_answer_first_try']:.2%}")
            print(f"    Answer success rate (with verifier feedback): {rates['success_rate_answer_with_retries']:.2%}")
            print(f"    Theorem sequence success rate (first try): {rates['success_rate_theorem_sequence_first_try']:.2%}")
            print(f"    Theorem sequence success rate (with verifier feedback): {rates['success_rate_theorem_sequence_with_retries']:.2%}")
    
    # Create plots
    plot_success_rates(results)
    print("\nPlots have been saved as 'answer_success_rate.png' and 'theorem_success_rate.png'")
