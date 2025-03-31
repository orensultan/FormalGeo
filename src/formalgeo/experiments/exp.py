import matplotlib.pyplot as plt
import numpy as np
import os

# Data for each method across levels 1-5
levels = [1, 2, 3, 4, 5]

# Generate random success rates between 0 and 1
np.random.seed(42)  # For reproducibility

# Success rates for numeric answer
numeric_random = np.random.uniform(0.1, 0.3, 5)
numeric_random_verifier = np.random.uniform(0.2, 0.4, 5)
numeric_analogy = np.random.uniform(0.3, 0.5, 5)
numeric_analogy_verifier = np.random.uniform(0.4, 0.6, 5)

# Success rates for theorem sequence
theorem_random = np.random.uniform(0.05, 0.2, 5)  # Lower rates for theorem sequence
theorem_random_verifier = np.random.uniform(0.15, 0.3, 5)
theorem_analogy = np.random.uniform(0.25, 0.4, 5)
theorem_analogy_verifier = np.random.uniform(0.35, 0.5, 5)

# Sort arrays to show increasing trend with level
numeric_random.sort()
numeric_random_verifier.sort()
numeric_analogy.sort()
numeric_analogy_verifier.sort()
theorem_random.sort()
theorem_random_verifier.sort()
theorem_analogy.sort()
theorem_analogy_verifier.sort()

def create_plot(data, title, filename):
    plt.figure(figsize=(10, 6))
    
    # Plot each method with different markers
    plt.plot(levels, data[0], 'o-', label='Random examples', linewidth=2, markersize=8)
    plt.plot(levels, data[1], 's-', label='Random examples & Verifier feedback', linewidth=2, markersize=8)
    plt.plot(levels, data[2], '^-', label='Analogous examples', linewidth=2, markersize=8)
    plt.plot(levels, data[3], 'D-', label='Analogous examples & Verifier feedback', linewidth=2, markersize=8)

    # Customize the plot
    plt.xlabel('Level', fontsize=12)
    plt.ylabel('Success Rate', fontsize=12)
    plt.title(title, fontsize=14)
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(fontsize=10)

    # Set y-axis to show percentages and limit to 0-100%
    plt.gca().yaxis.set_major_formatter(plt.FuncFormatter(lambda y, _: '{:.0%}'.format(y)))
    plt.ylim(0, 1)

    # Set x-axis ticks to show all levels
    plt.xticks(levels)

    # Add a horizontal line at y=0 for reference
    plt.axhline(y=0, color='k', linestyle='-', alpha=0.3)

    # Adjust layout to prevent label cutoff
    plt.tight_layout()

    # Save the plot
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    plt.close()

# Create numeric answer plot
numeric_data = [numeric_random, numeric_random_verifier, numeric_analogy, numeric_analogy_verifier]
create_plot(numeric_data, 'o1 Model Success Rate Comparison Across Levels (Numeric Answer)', 'numeric_success_rate.png')

# Create theorem sequence plot
theorem_data = [theorem_random, theorem_random_verifier, theorem_analogy, theorem_analogy_verifier]
create_plot(theorem_data, 'o1 Model Success Rate Comparison Across Levels (Theorem Sequence)', 'theorem_success_rate.png')

print("Plots have been saved as 'numeric_success_rate.png' and 'theorem_success_rate.png'")
