$$
\begin{align*}
&\LARGE {COMP 9417\ Machine\ Learning}
\end{align*}
$$

$$
\begin{align*}
\Large {Homework\ 1: Regularized\ Regression\ \&\ Numerical\ Optimization}
\end{align*}
$$

---

#### Question (1) Gradient Based Optimization

**(a).** 

The gradiant of $f(x)$:
$$
\nabla f(x) = A^T(Ax-b) + \gamma\ x
$$
Update the gradient descent:
$$
x^{(k+1)} = x^{(k)} - \alpha \nabla f(x^{(k)})
$$

```
# First 5 Lines
k = 1, x(k) = [0.98 0.98 0.98 0.98]
k = 2, x(k) = [0.9624 0.9804 0.9744 0.9584]
k = 3, x(k) = [0.9427 0.9824 0.9668 0.9433]
k = 4, x(k) = [0.9234 0.9866 0.9598 0.9295]
k = 5, x(k) = [0.9044 0.9916 0.9526 0.9169]

# Last 5 Lines
k = 271, x(k) = [0.0666 1.3366 0.4928 0.3251]
k = 272, x(k) = [0.0666 1.3366 0.4928 0.325 ]
k = 273, x(k) = [0.0665 1.3366 0.4927 0.325 ]
k = 274, x(k) = [0.0664 1.3367 0.4927 0.3249]
k = 275, x(k) = [0.0663 1.3367 0.4927 0.3249]
```

Codes in `solution.py`:  `def q1_a():`

**(b).**  

It means that the gradient of the function at this point is close to 0, the closer it is to the local minimum of the function.

If the value on the right side is reduced, the advantage is that it is closer to the local minimum of the function here, but the disadvantage is that it requires more iterations and more time, and at the same time, if there is no matching learning rate, it is possible that the gradiant cannot find a point which is less than the threshold, the local minimum is missed so that it cannot be converged.

**(c).**  

First read the csv file using `pandas`.  Since *ShelveLoc*, *Urban*, *US* are not values move them out and use `StandardScaler().fit_transform()` to normalize the remaining features. Next, subtract the mean value of the target variable (Sales) to obtain the centralized valueSet the first half of the values as the training set and the rest as the test set.

```
# the means and variances of features
-----------------------
Mean : 
CompPrice      3.819167e-16
Income         3.552714e-17
Advertising    2.664535e-17
Population     1.598721e-16
Price         -6.217249e-17
Age            1.287859e-16
Education     -1.332268e-16
dtype: float64
-----------------------
Var : 
CompPrice      1.002506
Income         1.002506
Advertising    1.002506
Population     1.002506
Price          1.002506
Age            1.002506
Education      1.002506
dtype: float64
-----------------------

# The first and last rows of the 4 requested objects
-----------------------
X_train: 
X_train: 
     CompPrice    Income  Advertising  Population     Price       Age  Education
0     0.850455  0.155361     0.657177    0.075819  0.177823 -0.699782   1.184449 
199  -0.194250  0.692014    -0.246159    0.476656  0.431555  0.659918   0.038208   
-----------------------
X_test: 
     CompPrice    Income  Advertising  Population     Price       Age  Education
200   1.242219  0.835121    -0.998939    0.571770  1.277326  0.536309  -0.725953 
399   0.589279 -1.132606    -0.998939   -1.615848  0.177823 -0.267150   0.802369 
-----------------------
Y_train: 
0      2.003675
199   -1.076325
Name: Sales, dtype: float64
-----------------------
Y_test: 
200   -1.936325
399    2.213675
Name: Sales, dtype: float64
-----------------------
```

Codes in `solution.py`:  `def q1_c():`

**(d).**  

```
[ 1.67491063  0.3687072   1.10976073  0.02080549 -2.32139218 -0.51939595 -0.14928172]
```

Codes in `solution.py`:  `def q1_d():`

**(e).** 

First, the squared error can be decomposed into the sum of the errors for each data point and the other part can be decomposed into the sum of the square of each elements 
$$
\begin{align*}
\frac{1}{n}||y-X\beta||^2_2&=\frac{1}{n}\sum_{i=1}^{n}(y_i-x_i^T\beta)^2\\
\phi||\beta||^2_2&=\phi\sum_{j=1}^{p}\beta_j^2\\
&=\frac{1}{n}n\ \phi\sum_{j=1}^{p}\beta_j^2\\
&=\frac{1}{n}\sum_{i=1}^{n}\phi\sum_{j=1}^{p}\beta_j^2\\
\end{align*}
$$
Second, Set the original loss function
$$
L(\beta) =\frac{1}{n}\sum_{i=1}^{n}L_i(\beta)= \frac{1}{n}\sum_{i=1}^n \left( (y_i-x_i^T\beta)^2+\phi\sum_{j=1}^{p}\beta_j^2 \right)
$$
Therefore, 
$$
L_i(\beta)=(y_1-x_i^T\beta)^2+\phi\sum_{j=1}^{p}\beta_j^2
$$
Third, count the gradiant of the $L_i(\beta)$
$$
\nabla L_i(\beta)=-2x_i(y_i-x_i^T\beta)+2\phi\beta
$$


**(f).**  

Since it is gradient descent, the residuals get smaller as the number of iterations increases, and each alpha sets the residual of the last one as the indicator, which will be closer to the minimum value.

```
The train MSE: 4.558906724365393
The  test MSE: 4.380429183271842
```

![q1_f](/Users/enmmmmovo/Documents/Study/COMP9417/Homework/hw1/q1_f.svg)

Codes in `solution.py`:  `def q1_f():`

**(g).**

When aplha is large, fluctuations exist because too large a step may "cross" the optimal solution, causing the solution to oscillate around the optimal solution and not stabilize.

```
The train MSE: 4.768090703691494
The  test MSE: 4.523807323802017
```

![q1_g](/Users/enmmmmovo/Documents/Study/COMP9417/Homework/hw1/q1_g.svg)

Codes in `solution.py`:  `def q1_g():`

**(h).**

First of all, from the public announcement, **SGD** only needs to compute on a part of data for each update, while **GD** needs to compute on all data sets for each update, so when there is more data, sgd is faster compared to **GD**.
Secondly, from the graph, we can see that when the alpha is small, **GD** and **SGD** are similar, but when the alpha is large, the result of **GD** is more stable and **SGD** will fluctuate a lot
Relatively speaking, I prefer**GD** because the number set here is not very large, they take about the same amount of time to implement, and the results are more stable.

**(i).**

According to the topic $X\beta = X_j\beta_j + X_{-j}\beta_{-j}$, The original $L(\beta)$ formula can be written as
$$
L(\beta)=\frac{1}{n}||y-X_j\beta_j - X_{-j}\beta_{-j}||^2_2+\phi||\beta||^2_2
$$
We take $\beta_j$ as a variable to derive it, $\beta_j$ is the result we want to solve, we can let $\beta_{-j}$ is normal value
$$
\frac{\partial L(\beta)}{\partial\beta_j}=-\frac{1}{n}X_j^T(y-X_j\beta_j - X_{-j}\beta_{-j})+2\phi\beta_j=0\\
\begin{align*}
\frac{1}{n}X_j^T(y-X_j\beta_j - X_{-j}\beta_{-j})&=2\phi\beta_j\\
X_j^T(y-X_j\beta_j - X_{-j}\beta_{-j})&=2\phi\beta_jn\\
X_j^Ty-X_j^TX_j\beta_j - X_j^TX_{-j}\beta_{-j}&=2\phi\beta_jn\\
2\phi\beta_jn+X_j^TX_j\beta_j&=X_j^Ty-X_j^TX_{-j}\beta_{-j}\\
\beta_j(2\phi n+X_j^TX_j)&=X_j^Ty-X_j^TX_{-j}\beta_{-j}\\
\beta_j&=\frac{X_j^T(y-X_{-j}\beta_{-j})}{2\phi n+X_j^TX_j}\\
\end{align*}
$$
**(j).**

#### Question (2) 

**(a).**
$$
\hat{\beta}=\Tau_\lambda(v):=\left\{
\begin{array}{ll}
    v- \lambda, & \text{if } v > \lambda \\
    0, & \text{if } |v| \leq \lambda \\
    v- \lambda, & \text{if } v < -\lambda
  \end{array}
\right.
$$
First, Let $f(\beta) = |\beta| + \frac{1}{2\lambda} (\beta - v)^2$

We can see, When $\beta$ is used as a variable, it is the absolute value that affects the minimum value, so it is discussed separately.

- When $\beta > 0$
  $$
  f(\beta)=\beta+\frac{1}{2\lambda}(\beta-v)^2\\
  f'(\beta)=1+\frac{1}{\lambda}(\beta-c)
  $$
  Let $f'(\beta) = 0$
  $$
  \begin{align*}
  1+\frac{1}{\lambda}(\beta-v)&=0\\
  \beta-v&=-\lambda\\
  \beta &= v-\lambda
  \end{align*}
  $$
  As we define $\beta>0$ before, Therefore
  $$
  v-\lambda>0\\
  v>\lambda
  $$

- When $\beta > 0$
  $$
  f(\beta)=-\beta+\frac{1}{2\lambda}(\beta-v)^2\\
  f'(\beta)=-1+\frac{1}{\lambda}(\beta-c)
  $$
  Let $f'(\beta) = 0$
  $$
  \begin{align*}
  -1+\frac{1}{\lambda}(\beta-v)&=0\\
  \beta-v&=\lambda\\
  \beta &= v+\lambda
  \end{align*}
  $$
  As we define $\beta<0$ before, Therefore
  $$
  v+\lambda<0\\
  v<-\lambda
  $$

- When $\beta=0$
  $$
  f(0)=\frac{v^2}{2 \lambda}
  $$
  Therefore, $|v|\leq\lambda$, $\beta = 0$

**(b).**

Let set the function $f(\beta)=||\beta||_1+\frac{1}{2\lambda}||\beta-v||^2_2$

According to the properties of matrix norm, it can write as
$$
f(\beta)=\sum_{i=1}^{p}|\beta_i|+\frac{1}{2\lambda}(\beta_i-v_i)^2
$$
We can get the minimum the function by counting each element $i=1,...,p$ . Now, for each element we can use the result above, 

- When $v_i>\lambda$, then $\beta_i=v_i-\lambda$
- When $v_i<-\lambda$, then $\beta_i=v_i+\lambda$
- When $|v_i|\leq \lambda$, then $\beta_i=0$

Therefore, we can solve the vector $\hat{\beta}$ by $\Tau_\lambda(v_1),\Tau_\lambda(v_2),...,\Tau_\lambda(v_p)$

**(c).**

- When $\lambda = 1$：$\Tau_1(v) = (0, 1, 3, -6, 1, 3, 0, 7, 3, -9, -4)$

- When $\lambda = 3$：$\Tau_3(v) = (0, 0, 1, -4, 0, 1, 0, 5, 1, -7, -2)$

- When $\lambda = 6$：$\Tau_6(v) = (0, 0, 0, -1, 0, 0, 0, 2, 0, -4, 0)$

- When $\lambda = 9$：$\Tau_9(v) = (0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0)$

We can observe that as $\lambda$ gets larger, there are many cases that fall into $|v_i| \leq \lambda$ case, and the number of resulting zeros increases, the solution becomes more sparse.