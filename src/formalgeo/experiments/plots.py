import matplotlib.pyplot as plt
import numpy as np

# Data for cumulative progression
levels = [1, 2, 3, 4, 5]

# Analogy Based data (cumulative)
analogy_ft = [90, 80, 30, 20, 20]  # First try percentages
analogy_frv = [100, 100, 60, 50, 40]  # First try + First run + verifier
analogy_mrv = [100, 100, 70, 80, 60]  # First try + First run + verifier + Multiple runs

# Random data (cumulative)
random_ft = [40, 10, 0, 0, 0]  # First try percentages
random_frv = [70, 50, 30, 20, 20]  # First try + First run + verifier
random_mrv = [80, 100, 30, 40, 20]  # First try + First run + verifier + Multiple runs

# Data for final success rates
final_analogy = [100, 100, 70, 80, 60]
final_random = [80, 100, 30, 40, 20]

# Data for Analogy Based stability
analogy_10_samples = [100, 100, 70, 80, 60]  # Success rates for samples 1-10
analogy_20_samples = [95, 100, 70, 70, 55]   # Success rates for all 20 samples

# Create first figure for cumulative progression
plt.figure(figsize=(12, 7))

# Plot Analogy Based lines (all in blue)
plt.plot(levels, analogy_ft, 'o-', label='Analogy Based - First Try', linewidth=2, markersize=8, color='blue')
plt.plot(levels, analogy_frv, 's--', label='Analogy Based - First Run + Verifier', linewidth=2, markersize=8, color='blue')
plt.plot(levels, analogy_mrv, '^:', label='Analogy Based - Multiple Runs + Verifier', linewidth=2, markersize=8, color='blue')

# Plot Random lines (all in red)
plt.plot(levels, random_ft, 'o-', label='Random - First Try', linewidth=2, markersize=8, color='red')
plt.plot(levels, random_frv, 's--', label='Random - First Run + Verifier', linewidth=2, markersize=8, color='red')
plt.plot(levels, random_mrv, '^:', label='Random - Multiple Runs + Verifier', linewidth=2, markersize=8, color='red')

# Customize first plot
plt.xlabel('Level', fontsize=12)
plt.ylabel('Cumulative Success Rate (%)', fontsize=12)
plt.title('Cumulative Success Rates by Level and Variant', fontsize=14)
plt.grid(True, linestyle='--', alpha=0.7)
plt.legend(fontsize=10, bbox_to_anchor=(1.05, 1), loc='upper left')
plt.xticks(levels)
plt.ylim(0, 110)
plt.yticks(np.arange(0, 110, 10))

# Add value labels on the points for first plot
for i in range(len(levels)):
    # Analogy Based labels
    plt.text(levels[i], analogy_ft[i] + 2, f'{analogy_ft[i]}%', ha='center', va='bottom', color='blue')
    plt.text(levels[i], analogy_frv[i] + 2, f'{analogy_frv[i]}%', ha='center', va='bottom', color='blue')
    plt.text(levels[i], analogy_mrv[i] + 2, f'{analogy_mrv[i]}%', ha='center', va='bottom', color='blue')
    
    # Random labels
    plt.text(levels[i], random_ft[i] + 2, f'{random_ft[i]}%', ha='center', va='bottom', color='red')
    plt.text(levels[i], random_frv[i] + 2, f'{random_frv[i]}%', ha='center', va='bottom', color='red')
    plt.text(levels[i], random_mrv[i] + 2, f'{random_mrv[i]}%', ha='center', va='bottom', color='red')

# Adjust layout to prevent label cutoff
plt.tight_layout()

# Save first plot
plt.savefig('success_rates_progression.png', dpi=300, bbox_inches='tight')
plt.close()

# Create second figure for final success rates
plt.figure(figsize=(12, 7))

# Plot final success rates
plt.plot(levels, final_analogy, 'o-', label='Analogy based', linewidth=2, markersize=8, color='blue')
plt.plot(levels, final_random, 's-', label='Random', linewidth=2, markersize=8, color='red')

# Customize second plot
plt.xlabel('Level', fontsize=12)
plt.ylabel('Final Success Rate (%)', fontsize=12)
plt.title('Final Success Rates by Level and Variant', fontsize=14)
plt.grid(True, linestyle='--', alpha=0.7)
plt.legend(fontsize=10)
plt.xticks(levels)
plt.ylim(0, 110)
plt.yticks(np.arange(0, 110, 10))

# Add value labels on the points for second plot
for i in range(len(levels)):
    plt.text(levels[i], final_analogy[i] + 2, f'{final_analogy[i]}%', ha='center', va='bottom', color='blue')
    plt.text(levels[i], final_random[i] - 2, f'{final_random[i]}%', ha='center', va='top', color='red')

# Print final success rates
print("\nFinal Success Rates (50 samples):")
print("Analogy based: 41/50 (82%)")
print("Random: 27/50 (54%)")

# Save second plot
plt.savefig('final_success_rates.png', dpi=300, bbox_inches='tight')
plt.close()

# Create third figure for Analogy Based stability
plt.figure(figsize=(12, 7))

# Plot stability comparison
plt.plot(levels, analogy_10_samples, 'o-', label='Samples 1-10', linewidth=2, markersize=8, color='blue')
plt.plot(levels, analogy_20_samples, 's-', label='Samples 1-20', linewidth=2, markersize=8, color='green')

# Customize third plot
plt.xlabel('Level', fontsize=12)
plt.ylabel('Success Rate (%)', fontsize=12)
plt.title('Analogy based Stability: Success Rates 50 vs. 100 Samples', fontsize=14)
plt.grid(True, linestyle='--', alpha=0.7)
plt.legend(fontsize=10)
plt.xticks(levels)
plt.ylim(0, 110)
plt.yticks(np.arange(0, 110, 10))

# Add value labels on the points for third plot
for i in range(len(levels)):
    plt.text(levels[i], analogy_10_samples[i] + 2, f'{analogy_10_samples[i]}%', ha='center', va='bottom', color='blue')
    plt.text(levels[i], analogy_20_samples[i] - 2, f'{analogy_20_samples[i]}%', ha='center', va='top', color='green')

# Print final success rates for stability analysis
print("\nFinal Success Rates (100 samples):")
print("Analogy based: 78/100 (78%)")

# Save third plot
plt.savefig('analogy_based_stability.png', dpi=300, bbox_inches='tight')
plt.close()