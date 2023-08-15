
## Question 2

import matplotlib.pyplot as plt
import numpy as np
from sklearn import datasets

X, y = datasets.make_circles(n_samples=200, factor=0.4, noise=0.04, random_state=13)
colors = np.array(['orange', 'blue'])

np.random.seed(123)
random_labeling = np.random.choice([0,1], size=X.shape[0], )
plt.scatter(X[:, 0], X[:, 1], s=20, color=colors[random_labeling])
plt.title("Randomly Labelled Points")
plt.savefig("Randomly_Labeled.png")
plt.show()


## Question 3
import numpy as np
import matplotlib.pyplot as plt
t_var = np.load("../q3/t_var.npy")
y_var = np.load("../q3/y_var.npy")
plt.plot(t_var, y_var)
plt.show()

def create_W(p):
   ## generate W which is a p-2 x p matrix as defined in the question
   # your code here
   return W 

def loss(beta, y, W, L):
    ## compute loss for a given vector beta for data y, matrix W, regularization parameter L (lambda)
    # your code here 
    return loss_val

## your code here 
plt.plot(t_var, y_var, zorder=1, color='red', label='truth')
plt.plot(t_var, beta_hat, zorder=3, color='blue', 
            linewidth=2, linestyle='--', label='fit')
plt.legend(loc='best')
plt.title(f"L(beta_hat) = {loss(beta_hat, y, W, L)}")
plt.show()
