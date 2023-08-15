# COMP9417 Machine Learning Final Exam Part 1
# Write by Jinghan Wang, z5286124

import numpy as np
import matplotlib.pyplot as plt


f = lambda x: 0.3 * np.sin(x / 3)
sigma = 0.3
n = 20


x_samples = np.sort(np.random.uniform(0, 20, n))
y_samples = f(x_samples) + np.random.normal(0, sigma, n)


def kNN_regression(x, x_samples, y_samples, k):
    distances = np.abs(x_samples - x)
    k_nearest_indices = np.argsort(distances)[:k]

    return np.mean(y_samples[k_nearest_indices])


def q1_b_iv():
    x_values = np.linspace(0, 20, 400)
    k_values = list(range(1, 21))

    fig, axes = plt.subplots(5, 4, figsize=(14, 12))
    for ax, k in zip(axes.ravel(), k_values):
        y_pred = [kNN_regression(x, x_samples, y_samples, k) for x in x_values]

        ax.scatter(x_samples, y_samples, color='red', label='Samples', s=30)
        ax.plot(x_values, f(x_values), 'g-', label='True function')
        ax.plot(x_values, y_pred, 'b-', label='kNN Regression')
        ax.set_title(f"k = {k}")
        ax.set_xlim(0, 20)
        ax.set_ylim(-1, 1)
        if k in [1, 5, 9, 13, 17]:
            ax.set_ylabel('y')
        if k > 16:
            ax.set_xlabel('x')
        ax.legend(loc='upper left', fontsize='small')

    plt.tight_layout()
    plt.savefig('q1_b_iv.png', dpi=300)
    plt.show()


if __name__ == '__main__':
    q1_b_iv()

