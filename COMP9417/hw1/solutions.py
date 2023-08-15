import numpy as np
from sklearn.preprocessing import StandardScaler
import pandas as pd
import matplotlib.pyplot as plt


def q1_a():
    A = np.array([[1, 2, 1, -1], [-1, 1, 0, 2], [0, -1, -2, 1]])
    b = np.array([[3], [2], [-2]])
    alpha = 0.1
    gamma = 0.2

    x = np.array([[1], [1], [1], [1]])
    k = 0

    re = [None] * 5
    index = 0
    print_sentence = lambda x, y: print(f'k = {x}, x(k) = {np.around(y.ravel(), decimals=4)}')

    while True:
        grad = A.T @ (A @ x - b) + gamma * x

        if np.linalg.norm(grad) < 0.001:
            break

        x = x - alpha * grad
        k += 1
        index = (index + 1) % 5
        re[index] = x

        if k <= 5:
            print_sentence(k, x)

    for i in range(5):
        print_sentence(k - (5 - i), re[(index + 1 + i) % 5])


def q1_c():
    data = pd.read_csv('CarSeats.csv')
    pd.set_option('display.max_columns', 100)

    f = data.drop(['Sales','ShelveLoc', 'Urban', 'US'], axis=1)
    t = data['Sales']

    f_scale = pd.DataFrame(StandardScaler().fit_transform(f), columns=f.columns)

    print(f'-----------------------\nMean : \n{f_scale.mean()}\n-----------------------\nVar : \n{f_scale.var()}')
    t_center = t - t.mean()

    size = len(data) // 2
    X_train = f_scale.iloc[:size]
    X_test = f_scale.iloc[size:]
    Y_train = t_center[:size]
    Y_test = t_center[size:]

    print(f'-----------------------\nX_train: \n{X_train.iloc[[0, -1]]}')
    print(f'-----------------------\nX_test: \n{X_test.iloc[[0, -1]]}')
    print(f'-----------------------\nY_train: \n{Y_train.iloc[[0, -1]]}')
    print(f'-----------------------\nY_test: \n{Y_test.iloc[[0, -1]]}\n-----------------------')


def q1_d():
    data = pd.read_csv('CarSeats.csv')
    pd.set_option('display.max_columns', 100)

    f = data.drop(['Sales', 'ShelveLoc', 'Urban', 'US'], axis=1)
    t = data['Sales']

    f_scale = pd.DataFrame(StandardScaler().fit_transform(f), columns=f.columns)
    t_center = t - t.mean()

    size = len(data) // 2
    X = f_scale.iloc[:size].to_numpy()
    y = t_center[:size].to_numpy()

    phi = 0.5

    beta_ridge = np.linalg.inv(X.T @ X + phi * np.eye(X.shape[1])) @ X.T @ y
    print(beta_ridge)


def q1_f():
    data = pd.read_csv('CarSeats.csv')
    pd.set_option('display.max_columns', 100)

    f = data.drop(['Sales', 'ShelveLoc', 'Urban', 'US'], axis=1)
    t = data['Sales']

    f_scale = pd.DataFrame(StandardScaler().fit_transform(f), columns=f.columns)
    t_center = t - t.mean()

    size = len(data) // 2
    X_train = f_scale.iloc[:size].values
    X_test = f_scale.iloc[size:].values
    Y_train = t_center[:size].values
    Y_test = t_center[size:].values

    phi = 0.5
    alpha_list = [0.000001, 0.000005, 0.00001, 0.00005, 0.0001, 0.0005, 0.001, 0.005, 0.01]
    beta_hat = np.linalg.inv(X_train.T @ X_train + phi * np.eye(X_train.shape[1])) @ X_train.T @ Y_train

    fig, axes = plt.subplots(3, 3, figsize=(15, 15))
    axes = axes.flatten()

    beta_record = []
    residual_record = []
    for i in range(len(alpha_list)):
        beta = np.ones(X_train.shape[1])
        residual = []

        for j in range(1000):
            gradient = -2 * X_train.T @ (Y_train - X_train @ beta) / len(Y_train) + 2 * phi * beta
            beta = beta - alpha_list[i] * gradient
            residual.append(np.linalg.norm(Y_train - X_train @ beta) ** 2 / len(Y_train) - phi *
                            np.linalg.norm(beta) ** 2 - np.linalg.norm(Y_train - X_train @ beta_hat) ** 2 /
                            len(Y_train) + phi * np.linalg.norm(beta_hat) ** 2)

        residual_record.append(residual[-1])
        beta_record.append(beta)

        axes[i].plot(residual)
        axes[i].set_xlabel('Epoch')
        axes[i].set_ylabel('Residual')
        axes[i].set_title(f'alpha = {i < 4 and ["0.000001", "0.000005", "0.00001", "0.00005"][i] or alpha_list[i]}')

    plt.tight_layout()
    # plt.savefig('q1_f.svg', format='svg')
    plt.show()

    best_beta = beta_record[np.argmin(residual_record)]

    print(f'The train MSE: {np.linalg.norm(Y_train - X_train @ best_beta) ** 2 / len(Y_train)}')
    print(f'The test MSE: {np.linalg.norm(Y_test - X_test @ best_beta) ** 2 / len(Y_test)}')


def q1_g():
    data = pd.read_csv('CarSeats.csv')
    pd.set_option('display.max_columns', 100)

    f = data.drop(['Sales', 'ShelveLoc', 'Urban', 'US'], axis=1)
    t = data['Sales']

    f_scale = pd.DataFrame(StandardScaler().fit_transform(f), columns=f.columns)
    t_center = t - t.mean()

    size = len(data) // 2
    X_train = f_scale.iloc[:size].values
    X_test = f_scale.iloc[size:].values
    Y_train = t_center[:size].values
    Y_test = t_center[size:].values

    phi = 0.5
    alpha_list = [0.000001, 0.000005, 0.00001, 0.00005, 0.0001, 0.0005, 0.001, 0.006, 0.02]
    beta_hat = np.linalg.inv(X_train.T @ X_train + phi * np.eye(X_train.shape[1])) @ X_train.T @ Y_train

    fig, axes = plt.subplots(3, 3, figsize=(15, 15))
    axes = axes.flatten()

    beta_record = []
    residual_record = []
    for i in range(len(alpha_list)):
        beta = np.ones(X_train.shape[1])
        residual = []

        for epoch in range(5):
            for j in range(X_train.shape[0]):
                gradient = -2 * X_train[j:j + 1, :].T @ (Y_train[j:j + 1] - X_train[j:j + 1, :] @ beta) / \
                           len(Y_train[j:j + 1]) + 2 * phi * beta
                beta = beta - alpha_list[i] * gradient
                residual.append(np.linalg.norm(Y_train - X_train @ beta) ** 2 / len(Y_train) - phi *
                            np.linalg.norm(beta) ** 2 - np.linalg.norm(Y_train - X_train @ beta_hat) ** 2 /
                            len(Y_train) + phi * np.linalg.norm(beta_hat) ** 2)

        residual_record.append(residual[-1])
        beta_record.append(beta)

        axes[i].plot(residual)
        axes[i].set_xlabel('Epoch')
        axes[i].set_ylabel('Residual')
        axes[i].set_title(f'alpha = {i < 4 and ["0.000001", "0.000005", "0.00001", "0.00005"][i] or alpha_list[i]}')

    plt.tight_layout()
    # plt.savefig('q1_g.svg', format='svg')
    plt.show()

    best_beta = beta_record[np.argmin(residual_record)]

    print(f'The train MSE: {np.linalg.norm(Y_train - X_train @ best_beta) ** 2 / len(Y_train)}')
    print(f'The test MSE: {np.linalg.norm(Y_test - X_test @ best_beta) ** 2 / len(Y_test)}')


if __name__ == '__main__':
    # q1_a()
    # q1_c()
    # q1_d()
    # q1_f()
    q1_g()
