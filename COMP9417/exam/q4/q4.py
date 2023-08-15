# COMP9417 Machine Learning Final Exam Part 4
# Write by Jinghan Wang, z5286124
import numpy as np
import matplotlib.pyplot as plt


def compute_sigma2_hat(X, Y, mu_i):
    n = len(X)
    total_sum = sum((X[i] - mu_i) ** 2 + (Y[i] - mu_i) ** 2 for i in range(n))
    return total_sum / (2 * n)


def q4_a_iv():
    mu_i = 1
    sigma2_true = 0.5
    sigma_true = np.sqrt(sigma2_true)
    sample_sizes = np.arange(10, 1001, 10)
    xi_values = []

    for n in sample_sizes:
        X = np.random.normal(mu_i, sigma_true, n)
        Y = np.random.normal(mu_i, sigma_true, n)
        sigma2_hat = compute_sigma2_hat(X, Y, mu_i)
        xi_n = abs(sigma2_hat - sigma2_true)
        xi_values.append(xi_n)

    plt.figure(figsize=(10, 6))
    plt.plot(sample_sizes, xi_values, label=r'$\xi_n$')
    plt.xlabel('Sample Size (n)')
    plt.ylabel(r'Deviation ($\xi_n$)')
    plt.title(r'Deviation ($\xi_n$) against Sample Size (n)')
    plt.legend()
    plt.grid(True)
    plt.savefig('q4_a_iv.png', dpi=300)
    plt.show()


if __name__ == '__main__':
    q4_a_iv()
