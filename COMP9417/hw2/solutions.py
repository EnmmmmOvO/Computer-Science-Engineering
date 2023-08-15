from sklearn.tree import DecisionTreeRegressor
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits import mplot3d
from sympy import symbols, diff


def f_sampler(f, n=100, sigma=0.05):
    # sample points from function f with Gaussian noise (0,sigma**2)
    xvals = np.random.uniform(low=0, high=1, size=n)
    yvals = f(xvals) + sigma * np.random.normal(0, 1, size=n)

    return xvals, yvals


f = lambda x: np.sqrt(x * (1 - x)) * np.sin((2.1 * np.pi) / (x + 0.05))


def q1_c_fixed():
    np.random.seed(123)
    X, y = f_sampler(f, 160, sigma=0.2)
    X = X.reshape(-1, 1)

    base_learners = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50]
    fig, axs = plt.subplots(5, 2, figsize=(15, 25))

    for i, T in enumerate(base_learners):
        h = []
        n = len(y)
        f_pred = np.zeros(n)

        for t in range(T):
            dt = DecisionTreeRegressor(max_depth=1).fit(X, y - f_pred)
            h.append(dt)
            f_pred += 0.1 * dt.predict(X)

        pred = np.zeros(len(X))
        for dt in h:
            pred += 0.1 * dt.predict(X)

        ax = axs[i // 2, i % 2]
        ax.plot(np.linspace(0, 1, 1000), f(np.linspace(0, 1, 1000)), color='red', alpha=0.5, label='truth')
        ax.scatter(X, y, marker='x', color='blue', label='observed')
        ax.plot(np.sort(X, axis=0), pred[np.argsort(X, axis=0)], color='green', label='fixed')
        ax.set_title(f'{T} Base Learners')
        ax.legend()

    plt.tight_layout()
    # plt.savefig('q1_c_fixed.svg', format='svg')
    plt.show()


def q1_c_adaptive():
    np.random.seed(123)
    X, y = f_sampler(f, 160, sigma=0.2)
    X = X.reshape(-1, 1)

    base_learners = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50]
    fig, axs = plt.subplots(5, 2, figsize=(15, 25))

    for i, time in enumerate(base_learners):
        h = []
        n = len(y)
        f_pred = np.zeros(n)

        for _ in range(time):
            dt = DecisionTreeRegressor(max_depth=1).fit(X, y - f_pred)
            h.append(dt)
            h_t_x = dt.predict(X)
            denominator = np.sum(h_t_x ** 2)
            f_pred += (denominator != 0 and np.sum((y - f_pred) * h_t_x) / denominator or 0) * dt.predict(X)

        pred = np.zeros(len(X))
        for dt in h:
            pred += dt.predict(X)

        ax = axs[i // 2, i % 2]
        ax.plot(np.linspace(0, 1, 1000), f(np.linspace(0, 1, 1000)), color='red', alpha=0.5, label='truth')
        ax.scatter(X, y, marker='x', color='blue', label='observed')
        ax.plot(np.sort(X, axis=0), pred[np.argsort(X, axis=0)], color='green', label='adaptive')
        ax.set_title(f'{time} Base Learners')
        ax.legend()

    plt.tight_layout()
    # plt.savefig('q1_c_adaptive.svg', format='svg')
    plt.show()


def q1_d_fixed():
    np.random.seed(123)
    X, y = f_sampler(f, 160, sigma=0.2)
    X = X.reshape(-1, 1)

    base_learners = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50]
    fig, axs = plt.subplots(5, 2, figsize=(15, 25))

    for i, T in enumerate(base_learners):
        h = []
        n = len(y)
        f_pred = np.zeros(n)

        for t in range(T):
            dt = DecisionTreeRegressor(max_depth=2).fit(X, y - f_pred)
            h.append(dt)
            f_pred += 0.1 * dt.predict(X)

        pred = np.zeros(len(X))
        for dt in h:
            pred += 0.1 * dt.predict(X)

        ax = axs[i // 2, i % 2]
        ax.plot(np.linspace(0, 1, 1000), f(np.linspace(0, 1, 1000)), color='red', alpha=0.5, label='truth')
        ax.scatter(X, y, marker='x', color='blue', label='observed')
        ax.plot(np.sort(X, axis=0), pred[np.argsort(X, axis=0)], color='green', label='fixed')
        ax.set_title(f'{T} Base Learners')
        ax.legend()

    plt.tight_layout()
    # plt.savefig('q1_d_fixed.svg', format='svg')
    plt.show()


def q1_d_adaptive():
    np.random.seed(123)
    X, y = f_sampler(f, 160, sigma=0.2)
    X = X.reshape(-1, 1)

    base_learners = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50]
    fig, axs = plt.subplots(5, 2, figsize=(15, 25))

    for i, time in enumerate(base_learners):
        h = []
        n = len(y)
        f_pred = np.zeros(n)

        for _ in range(time):
            dt = DecisionTreeRegressor(max_depth=2).fit(X, y - f_pred)
            h.append(dt)
            h_t_x = dt.predict(X)
            denominator = np.sum(h_t_x ** 2)
            f_pred += (denominator != 0 and np.sum((y - f_pred) * h_t_x) / denominator or 0) * dt.predict(X)

        pred = np.zeros(len(X))
        for dt in h:
            pred += dt.predict(X)

        ax = axs[i // 2, i % 2]
        ax.plot(np.linspace(0, 1, 1000), f(np.linspace(0, 1, 1000)), color='red', alpha=0.5, label='truth')
        ax.scatter(X, y, marker='x', color='blue', label='observed')
        ax.plot(np.sort(X, axis=0), pred[np.argsort(X, axis=0)], color='green', label='adaptive')
        ax.set_title(f'{time} Base Learners')
        ax.legend()

    plt.tight_layout()
    # plt.savefig('q1_d_adaptive.svg', format='svg')
    plt.show()


def q3_b():
    x = np.linspace(-2, 2, 200)
    y = np.linspace(-2, 2, 200)
    x, y = np.meshgrid(x, y)

    fig = plt.figure(figsize=(7, 7))
    fig.add_subplot(111, projection='3d').plot_surface(x, y, 100 * (y - x ** 2) ** 2 + (1 - x) ** 2, cmap='viridis')
    # plt.savefig('q3_b.svg', format='svg')
    plt.show()

    x, y = symbols('x y')
    f = 100 * (y - x ** 2) ** 2 + (1 - x) ** 2
    print(f'Gradient: \ndf/dx={diff(f, x)}\ndf/dy={diff(f, y)}')
    print(f'Hessian: \n{np.array([[diff(f, x, x), diff(f, x, y)], [diff(f, y, x), diff(f, y, y)]])}')


def q3_c():
    gradient = lambda x: np.array([-400 * x[0] * (x[1] - x[0] ** 2) - 2 * (1 - x[0]), 200 * (x[1] - x[0] ** 2)])
    hessian = lambda x: np.array([[1200 * x[0] ** 2 - 400 * x[1] + 2, -400 * x[0]], [-400 * x[0], 200]])

    x = np.array([-1.2, 1.0])
    x_values = [x]
    while True:
        delta = np.linalg.inv(hessian(x)) @ gradient(x)

        if np.linalg.norm(delta) <= 1e-6:
            break

        x = x - delta
        x_values.append(x)

    for i, x in enumerate(x_values):
        print(f"x^{i} = {x}")


if __name__ == '__main__':
    q1_c_fixed()
    q1_c_adaptive()
    q1_d_fixed()
    q1_d_adaptive()
    q3_b()
    q3_c()
