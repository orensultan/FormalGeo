import os
import matplotlib.pyplot as plt
import numpy as np

def calculate_success_rates(results_dir):
    success_rates = {
        'level_4': {'success': 0, 'total': 0}
    }
    
    level_dir = os.path.join(results_dir, 'level_4')
    if not os.path.exists(level_dir):
        return success_rates
            
    # Get all analogy-based files in level 4
    analogy_files = [f for f in os.listdir(level_dir) if f.startswith('variant_analogy_based_model_') and f.endswith('.txt')]
    
    # Group files by problem number
    problem_files = {}
    for file in analogy_files:
        problem_num = file.split('_problem_')[1].split('_')[0]
        if problem_num not in problem_files:
            problem_files[problem_num] = []
        problem_files[problem_num].append(file)
    
    # Process each problem
    for problem_num, files in problem_files.items():
        # Only count if there's exactly one file (run_0.txt)
        if len(files) == 1 and files[0].endswith('_run_0.txt'):
            file_path = os.path.join(level_dir, files[0])
            with open(file_path, 'r') as f:
                content = f.read()
            
            success_rates['level_4']['total'] += 1
            
            # Check if the file has RETRIES_MESSAGES section
            if 'RETRIES_MESSAGES:' in content:
                retries_section = content.split('RETRIES_MESSAGES:')[1].split('#RETRIES:')[1].strip()
                retries = int(retries_section.split('\n')[0].strip())
                runs_section = retries_section.split('#RUNS:')[1].strip()
                runs = int(runs_section.split('\n')[0].strip())
                
                # Count as success if both RETRIES and RUNS are 0
                if retries == 0 and runs == 0:
                    success_rates['level_4']['success'] += 1
    
    # Calculate percentage
    if success_rates['level_4']['total'] > 0:
        success_rates['level_4']['percentage'] = (success_rates['level_4']['success'] / success_rates['level_4']['total']) * 100
    else:
        success_rates['level_4']['percentage'] = 0
    
    return success_rates

def plot_success_rates(success_rates, output_file):
    fig, ax = plt.subplots(figsize=(8, 6))
    bar = ax.bar(['Level 4'], [success_rates['level_4']['percentage']])
    
    ax.set_ylabel('Success Rate (%)')
    ax.set_title('Theorem Sequence First Try Success Rate (Level 4, Analogy-based Model)')
    
    # Add percentage label on top of bar
    height = bar[0].get_height()
    ax.annotate(f'{height:.1f}%',
                xy=(bar[0].get_x() + bar[0].get_width() / 2, height),
                xytext=(0, 3),
                textcoords="offset points",
                ha='center', va='bottom')
    
    plt.tight_layout()
    plt.savefig(output_file)
    plt.close() 