import os
import matplotlib.pyplot as plt
from PIL import Image

def display_image(problem_id):
    path = 'formalgeo7k_v1/diagrams/' + str(problem_id) + '.png'

    # Check if the file exists
    if not os.path.exists(path):
        print(f"File not found: {path}")
        return

    image = Image.open(path)

    plt.imshow(image)
    plt.axis('off')  # Hide the axis
    plt.show()
