import matplotlib.pyplot as plt
import matplotlib.image as mpimg
import os

def merge_plots():
    # Get the directory path
    dir_path = os.path.dirname(os.path.abspath(__file__))
    
    # Load the two images
    answer_plot = mpimg.imread(os.path.join(dir_path, 'answer_success_rate.png'))
    theorem_plot = mpimg.imread(os.path.join(dir_path, 'theorem_success_rate.png'))
    
    # Create a new figure with two subplots side by side
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(20, 8))
    
    # Display the images in the subplots
    ax1.imshow(answer_plot)
    ax1.axis('off')
    ax1.set_title('Answer Success Rate')
    
    ax2.imshow(theorem_plot)
    ax2.axis('off')
    ax2.set_title('Theorem Sequence Success Rate')
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the combined plot
    output_path = os.path.join(dir_path, 'success_rates_combined.png')
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    
    print(f"Combined plot has been saved as '{output_path}'")

if __name__ == "__main__":
    merge_plots() 