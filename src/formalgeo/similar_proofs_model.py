import pandas as pd
import numpy as np
import torch
from torch.utils.data import DataLoader, TensorDataset
import torch.nn as nn
import torch.optim as optim
import argparse
from sklearn.model_selection import train_test_split

model_save_path = "similar_proofs_model.pth"

class SimpleNN(nn.Module):
    def __init__(self, input_size):
        super(SimpleNN, self).__init__()
        self.layer1 = nn.Linear(input_size, 128)
        self.layer2 = nn.Linear(128, 64)
        self.layer3 = nn.Linear(64, 1)  # Single output for regression

    def forward(self, x):
        x = torch.relu(self.layer1(x))
        x = torch.relu(self.layer2(x))
        x = self.layer3(x)
        return x


def load_model_and_predict(model_path, input_features):
    input_size = input_features.shape[1]
    model = SimpleNN(input_size)

    model.load_state_dict(torch.load(model_path))
    model.eval()

    input_tensor = torch.tensor(input_features, dtype=torch.float32)

    with torch.no_grad():
        prediction = model(input_tensor)

    return float(prediction.item())

def run_model_predictions():
    X_train, train_loader, X_test_tensor, y_test_tensor = data_preparation()
    model, criterion = train(X_train, train_loader)
    save_model(model)
    eval(model, X_test_tensor, y_test_tensor, criterion)

def data_preparation():
    data = pd.read_csv('results.csv')
    X = data.iloc[:, -4:-1]
    y = data.iloc[:, -1]

    bins = np.linspace(0, 1.0001, 6)  # Ensure it includes the value 1.0
    y_binned = np.digitize(y, bins) - 1

    data_indices = pd.DataFrame({'index': np.arange(len(y)), 'y_binned': y_binned})

    X_train, X_test, y_train_binned, y_test_binned, train_idx, test_idx = train_test_split(
        X, y_binned, data_indices.index, test_size=0.1, random_state=42, shuffle=True)

    y_train_continuous = y.iloc[train_idx].values
    y_test_continuous = y.iloc[test_idx].values

    print_bucket_ranges(y_train_continuous, bins, y_train_binned, "Distribution of label values before downsampling:")

    # Determine the size of the highest range bucket
    max_bucket_size = np.sum(y_train_binned == (len(bins) - 2))

    # Downsample each bucket to match the size of the highest range bucket with fixed seed
    downsampled_indices = []
    np.random.seed(42)  # Set seed for reproducibility

    for i in range(len(bins) - 1):
        bucket_indices = np.where(y_train_binned == i)[0]
        if len(bucket_indices) > max_bucket_size:
            downsampled_indices.extend(np.random.choice(bucket_indices, max_bucket_size, replace=False))
        else:
            downsampled_indices.extend(bucket_indices)

    X_train_downsampled = X_train.iloc[downsampled_indices]
    y_train_downsampled = y_train_continuous[downsampled_indices]  # Use the original continuous values

    print_bucket_ranges(y_train_downsampled, bins, np.digitize(y_train_downsampled, bins) - 1,
                        "\nDistribution of label values after downsampling:")

    X_train_tensor = torch.tensor(X_train_downsampled.values, dtype=torch.float32)
    y_train_tensor = torch.tensor(y_train_downsampled, dtype=torch.float32).view(-1, 1)
    X_test_tensor = torch.tensor(X_test.values, dtype=torch.float32)
    y_test_tensor = torch.tensor(y_test_continuous, dtype=torch.float32).view(-1, 1)

    train_dataset = TensorDataset(X_train_tensor, y_train_tensor)
    train_loader = DataLoader(train_dataset, batch_size=32, shuffle=True)
    return X_train, train_loader, X_test_tensor, y_test_tensor

def save_model(model):
    torch.save(model.state_dict(), model_save_path)
    print(f"Model saved to {model_save_path}")


def train(X_train, train_loader):
    input_size = X_train.shape[1]
    model = SimpleNN(input_size)

    criterion = nn.MSELoss()
    optimizer = optim.Adam(model.parameters(), lr=0.001)

    num_epochs = 10
    for epoch in range(num_epochs):
        for batch_X, batch_y in train_loader:
            optimizer.zero_grad()
            outputs = model(batch_X)
            loss = criterion(outputs, batch_y)
            loss.backward()
            optimizer.step()

        print(f'Epoch [{epoch + 1}/{num_epochs}], Loss: {loss.item():.4f}')

    return model, criterion

def eval(model, X_test_tensor, y_test_tensor, criterion):
    model.eval()
    with torch.no_grad():
        y_pred = model(X_test_tensor)
        test_loss = criterion(y_pred, y_test_tensor)
        print(f'Test Loss: {test_loss.item():.4f}')

        # Evaluate precision in the high range of predicted values
        predicted_high_threshold = torch.max(y_pred).item()
        ground_truth_high_threshold = 0.61

        high_value_indices = y_pred.view(-1) >= predicted_high_threshold
        y_pred_high = y_pred[high_value_indices]
        y_test_high = y_test_tensor[high_value_indices]

        if y_pred_high.size(0) > 0:
            precision_high = (y_test_high >= ground_truth_high_threshold).sum().item() / y_pred_high.size(0)
            print(
                f'High Predicted (>= {predicted_high_threshold}) Precision (Ground Truth >= {ground_truth_high_threshold}): {precision_high:.4f}')
        else:
            print(f'No high predicted values (>= {predicted_high_threshold}) to evaluate precision.')

        # Create a DataFrame for all predictions and ground truth values
        predictions_df = pd.DataFrame({
            'Ground Truth': y_test_tensor.view(-1).numpy(),
            'Predicted': y_pred.view(-1).numpy()
        })

        print(predictions_df)


def print_bucket_ranges(y, bins, y_binned, title):
    total_samples = len(y)
    print(title)
    for i in range(len(bins) - 1):
        bucket_indices = y_binned == i
        if bucket_indices.any():
            bucket_values = y[bucket_indices]
            percent_samples = len(bucket_values) / total_samples * 100
            print(
                f"Bucket {i}: {len(bucket_values)} samples, Range: min={bucket_values.min()}, max={bucket_values.max()}, Percent: {percent_samples:.2f}%")


def main():
    parser = argparse.ArgumentParser(description='Control model prediction execution.')
    parser.add_argument('--run-model-pred', type=int, choices=[0, 1],
                        help='Flag to run model predictions (1 to run, 0 to skip)')

    args = parser.parse_args()

    if args.run_model_pred == 1:
        run_model_predictions()

if __name__ == "__main__":
    main()