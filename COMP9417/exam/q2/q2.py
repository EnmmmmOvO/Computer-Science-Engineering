# COMP9417 Machine Learning Final Exam Part 2
# Write by Jinghan Wang, z5286124
from sklearn import datasets
import numpy as np
import matplotlib.pyplot as plt


def kmeans(X, initial_centers, num_iterations=10):
    global labels
    centers = initial_centers
    for _ in range(num_iterations):
        distances = np.linalg.norm(X[:, np.newaxis] - centers, axis=2)
        labels = np.argmin(distances, axis=1)

        new_centers = np.array([X[labels == i].mean(axis=0) for i in range(len(centers))])
        if np.all(centers == new_centers):
            break
        centers = new_centers
    return labels, centers


def q2_c():
    X, y = datasets.make_circles(n_samples=200, factor=0.4, noise=0.04, random_state=13)

    initial_centers = np.array([[0, 0], [1, 0]])
    labels, final_centers = kmeans(X, initial_centers, num_iterations=10)

    plt.scatter(X[:, 0], X[:, 1], s=20, color=np.array(['orange', 'blue'])[labels])
    plt.scatter(final_centers[:, 0], final_centers[:, 1], s=100, c='red', marker='X')
    plt.title("K-means Clustering after 10 Iterations")
    plt.grid(True)
    plt.savefig("q2_c.png", dpi=300)
    plt.show()


def phi_transform(X):
    x1_sq = X[:, 0] ** 2
    x2_sq = X[:, 1] ** 2
    x1_x2 = np.sqrt(2) * X[:, 0] * X[:, 1]
    return np.vstack((x1_sq, x2_sq, x1_x2)).T


def q2_d():
    X, y = datasets.make_circles(n_samples=200, factor=0.4, noise=0.04, random_state=13)
    X_transformed = phi_transform(X)
    initial_centers_transformed = np.array([[0, 0, 0], [1, 1, 0]])
    labels_transformed, final_centers_transformed = kmeans(X_transformed, initial_centers_transformed,
                                                           num_iterations=10)
    plt.scatter(X[:, 0], X[:, 1], s=20, color=np.array(['orange', 'blue'])[labels_transformed])
    plt.title("K-means Clustering on Transformed Data (Visualized in Original Space)")
    plt.grid(True)
    plt.savefig("q2_d.png", dpi=300)
    plt.show()


if __name__ == '__main__':
    q2_d()
