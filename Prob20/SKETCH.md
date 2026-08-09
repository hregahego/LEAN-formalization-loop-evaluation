# Problem 20 (Cahen–Fontana–Frisch–Glaz)

Let \(D\) be an integral domain and let

\[
\operatorname{Int}(D)
=
\{f\in K[X] : f(D)\subseteq D\},
\]

where \(K=\operatorname{Frac}(D)\).

For \(n\ge 1\), there is a canonical \(D\)-algebra homomorphism

\[
\theta_n:
\operatorname{Int}(D)^{\otimes_D n}
\longrightarrow
\operatorname{Int}(D^n)
\]

given by

\[
f_1\otimes\cdots\otimes f_n
\longmapsto
\prod_{i=1}^{n} f_i(X_i).
\]

**Problem 20.**
Is \(\theta_n\)

1. always injective?
2. always surjective?

---

# Main Result

The answer to **both questions is negative**.

There exists a one-dimensional Noetherian local domain \(D\) such that for every \(n\ge 2\),

\[
\theta_n:
\operatorname{Int}(D)^{\otimes_D n}
\to
\operatorname{Int}(D^n)
\]

is **neither injective nor surjective**.

---

# The Counterexample Domain

Let

\[
k=\mathbf F_2,
\qquad
A=k[t],
\]

and let

\[
S=A\setminus\bigl((t)\cup(t+1)\bigr).
\]

Define

\[
T=S^{-1}A,
\]

a semilocal PID with maximal ideals

\[
\mathfrak n_0=tT,
\qquad
\mathfrak n_1=(t+1)T.
\]

Set

\[
\pi=t(t+1),
\qquad
\mathfrak m=\pi T,
\]

and define the pullback domain

\[
D=k+\mathfrak m.
\]

Then

\[
D/\mathfrak m \cong \mathbf F_2,
\]

and

\[
K=\operatorname{Frac}(D)=\mathbf F_2(t).
\]

Write

\[
R=\operatorname{Int}(D).
\]

---

# Key Observation

Let

\[
p(X)=X^2+X.
\]

Since

\[
D/\mathfrak m \cong \mathbf F_2,
\]

we have

\[
p(d)\in \mathfrak m
\qquad
(d\in D).
\]

Hence

\[
p(D)\subseteq \mathfrak m.
\]

Because \(\mathfrak m\) is an ideal of \(T\),

\[
cp\in R
\qquad
(c\in T).
\]

In particular,

\[
p,\quad tp,\quad (t+1)p
\in R.
\]

A valuation argument shows

\[
p,\ tp,\ (t+1)p
\notin
\mathfrak mR.
\]

Therefore the residue classes

\[
\bar p,
\qquad
\overline{tp}
\]

are linearly independent in

\[
R/\mathfrak mR.
\]

---

# Failure of Injectivity

Consider

\[
\tau=(tp)\otimes p-p\otimes(tp)
\in
R\otimes_D R.
\]

Its image modulo \(\mathfrak mR\) is

\[
\overline{tp}\otimes\bar p
-
\bar p\otimes\overline{tp}.
\]

Since \(\bar p\) and \(\overline{tp}\) are linearly independent over

\[
D/\mathfrak m \cong \mathbf F_2,
\]

this tensor is nonzero.

Hence

\[
\tau\neq 0.
\]

However,

\[
\begin{aligned}
\theta_2(\tau)
&=
tp(X)p(Y)-p(X)tp(Y)\\
&=
t\,p(X)p(Y)-t\,p(X)p(Y)\\
&=0.
\end{aligned}
\]

Therefore

\[
\ker(\theta_2)\neq 0.
\]

So \(\theta_2\) is **not injective**.

Since

\[
\tau\otimes 1^{\otimes(n-2)}
\]

remains nonzero in

\[
R^{\otimes_D n},
\]

the map \(\theta_n\) is not injective for any \(n\ge2\).

---

# Failure of Surjectivity

Define

\[
q(X)=\frac{X^2+X}{\pi},
\]

and

\[
g(X)=q(X)^2+q(X).
\]

Since \(q(d)\in T\) for every \(d\in D\), and both residue fields of \(T\) are \(\mathbf F_2\),

\[
g(D)\subseteq \mathfrak m.
\]

Thus

\[
g\in R.
\]

Now define

\[
P(X,Y)=g(XY).
\]

Since \(xy\in D\) whenever \(x,y\in D\),

\[
P\in \operatorname{Int}(D^2).
\]

Suppose

\[
P\in \operatorname{im}(\theta_2).
\]

Then

\[
P(X,Y)
=
\sum_{i=1}^{r}
f_i(X)h_i(Y)
\]

for some \(f_i,h_i\in R\).

Using specially chosen elements

\[
u=\pi(t+1)^N
\]

with \(N\) large and applying a mixed finite-difference argument, one obtains

\[
P(u,u)-P(u,0)-P(0,u)+P(0,0)
\in
\mathfrak m^2.
\]

But the left-hand side equals

\[
g(u^2),
\]

and a direct valuation computation gives

\[
g(u^2)
\notin
\mathfrak m^2.
\]

This contradiction shows

\[
P(X,Y)
\notin
\operatorname{im}(\theta_2).
\]

Hence \(\theta_2\) is **not surjective**.

The same polynomial, viewed as independent of the remaining variables, shows that

\[
\theta_n
\]

is not surjective for every \(n\ge2\).

---

# Conclusion

For the domain

\[
D=\mathbf F_2+t(t+1)T,
\]

where

\[
T=
\mathbf F_2[t]_{\,\mathbf F_2[t]\setminus((t)\cup(t+1))},
\]

the canonical map

\[
\theta_n:
\operatorname{Int}(D)^{\otimes_D n}
\longrightarrow
\operatorname{Int}(D^n)
\]

satisfies

\[
\boxed{
\text{\(\theta_n\) is neither injective nor surjective for every } n\ge2.
}
\]

Therefore Problem 20 has a complete negative answer:

\[
\boxed{
\text{The canonical map is not always injective and not always surjective.}
}
\]
