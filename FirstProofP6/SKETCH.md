# Submission C — Solution to Problem 6

**Remark 1.** Throughout, the phrase "a single vertex" with $w(v) < d_T(v)$ is interpreted as saying that $v$ is the *unique* such vertex.

---

## Lemma 1 (Norm-one elements are irreducible)

Let $L$ be a positive definite integral lattice. If $x \in L$ satisfies $x^2 = 1$, then $x$ is irreducible.

**Proof.** Suppose $x = a + b$, where $a, b \in L$ are nonzero and $a \cdot b \geq 0$. Since $L$ is positive definite and integral, $a^2, b^2 \in \mathbb{Z}_{>0}$. Hence

$$1 = x^2 = a^2 + b^2 + 2a \cdot b \geq 1 + 1 = 2,$$

a contradiction. $\blacksquare$

---

Let $C$ be a rooted weighted tree with root $\rho$. Orient every edge away from $\rho$, and write $\mathrm{ch}_C(x)$ for the number of children of a vertex $x \in C$. We call $C$ **admissible** if its form is positive definite, every vertex weight is at least $2$, and

$$w(x) \geq \mathrm{ch}_C(x) + 1 \quad \text{for every } x \in C.$$

For $x = \sum_y n_y\, y \in L(C)$, write $x_y = n_y$ for the coefficient of the vertex $y$. For a positive definite rooted tree $C$, define its **capacity** by

$$\gamma(C) = \left(Q_C^{-1}\right)_{\rho\rho},$$

where $Q_C$ is the Gram matrix of $C$ in the vertex basis.

---

## Lemma 2 (Capacities of admissible rooted trees)

Let $C$ be an admissible rooted tree with root $\rho$. Then

$$0 < \gamma(C) < 1.$$

Moreover, if the root has children $\rho_1, \ldots, \rho_t$, and $C_i$ denotes the rooted subtree with root $\rho_i$, then

$$\gamma(C) = \frac{1}{w(\rho) - \sum_{i=1}^{t} \gamma(C_i)}.$$

**Proof.** Order the vertices so that $\rho$ comes first and the remaining vertices are grouped by the rooted subtrees $C_1, \ldots, C_t$. Then

$$Q_C = \begin{pmatrix} w(\rho) & c^T \\ c & Q_0 \end{pmatrix},$$

where $Q_0 = \bigoplus_i Q_{C_i}$, and $c$ has entry $-1$ in the coordinate corresponding to each child root $\rho_i$ and $0$ elsewhere. By the Schur complement formula,

$$\left(Q_C^{-1}\right)_{\rho\rho} = \frac{1}{w(\rho) - c^T Q_0^{-1} c} = \frac{1}{w(\rho) - \sum_i \gamma(C_i)}.$$

It remains to show that $\gamma(C) < 1$. This follows by induction on the number of vertices. If $C$ has one vertex, then $w(\rho) \geq 2$, so $\gamma(C) = 1/w(\rho) < 1$. Otherwise, by induction, $\gamma(C_i) < 1$ for every child subtree. If the root has $t$ children, then admissibility gives $w(\rho) \geq t + 1$. Hence

$$w(\rho) - \sum_i \gamma(C_i) > w(\rho) - t \geq 1,$$

so $\gamma(C) < 1$. $\blacksquare$

---

## Lemma 3 (A rooted estimate)

Let $C$ be an admissible rooted tree with root $\rho$ and capacity $\gamma = \gamma(C)$. Then, for every $x \in L(C)$ and every $k \in \mathbb{Z}$,

$$x^2 - (2k + 1)x_\rho + \gamma k(k + 1) \geq 0.$$

**Proof.** We prove the claim by induction on $|C|$.

If $C$ has one vertex, say $x = m\rho$, then $\gamma = 1/w(\rho)$. Let $W = w(\rho)$. Multiplying the desired inequality by $W$, we get

$$W\left(Wm^2 - (2k + 1)m + \frac{k(k + 1)}{W}\right) = (Wm - k)(Wm - k - 1).$$

Since $Wm - k \in \mathbb{Z}$, the product of the two consecutive integers $Wm - k$ and $Wm - k - 1$ is nonnegative. This proves the base case.

Now assume $|C| > 1$. Let the root be $\rho$, let its children be $\rho_1, \ldots, \rho_t$, and let $C_i$ be the rooted subtree with root $\rho_i$. Write

$$x = a\rho + \sum_i x_i, \quad x_i \in L(C_i),$$

and let $s_i = (x_i)_{\rho_i}$. Then

$$x^2 = w(\rho)a^2 - 2a\sum_i s_i + \sum_i x_i^2.$$

Let $\gamma_i = \gamma(C_i)$. By the induction hypothesis applied to $C_i$ with $k = a$, we have

$$x_i^2 - (2a + 1)s_i + \gamma_i a(a + 1) \geq 0,$$

so

$$x_i^2 - 2a s_i \geq s_i - \gamma_i a(a + 1).$$

Similarly, applying the induction hypothesis with $k = a - 1$, we obtain

$$x_i^2 - (2a - 1)s_i + \gamma_i a(a - 1) \geq 0,$$

so

$$x_i^2 - 2a s_i \geq -s_i - \gamma_i a(a - 1).$$

Taking the maximum of these two lower bounds gives

$$x_i^2 - 2a s_i \geq -\gamma_i a^2 + \left|s_i - \gamma_i a\right|.$$

Therefore, setting

$$D = \sum_i \left|s_i - \gamma_i a\right|,$$

we get

$$x^2 - (2k + 1)a + \gamma k(k + 1) \geq \left(w(\rho) - \sum_i \gamma_i\right)a^2 - (2k + 1)a + \gamma k(k + 1) + D.$$

By the capacity formula,

$$\gamma^{-1} = w(\rho) - \sum_i \gamma_i.$$

Thus, if $\tau = a/\gamma$, the preceding lower bound becomes

$$\gamma(\tau - k)(\tau - k - 1) + D.$$

If $\tau \notin (k, k + 1)$, then $(\tau - k)(\tau - k - 1) \geq 0$, and the result follows.

Suppose instead that $k < \tau < k + 1$. Put

$$\alpha = \tau - k, \quad \beta = k + 1 - \tau.$$

Then $0 < \alpha, \beta < 1$, $\alpha + \beta = 1$, and

$$\gamma(\tau - k)(\tau - k - 1) = -\gamma\alpha\beta.$$

Now

$$\tau = \frac{a}{\gamma} = \left(w(\rho) - \sum_i \gamma_i\right)a.$$

Since $w(\rho)a - \sum_i s_i \in \mathbb{Z}$, we have

$$D = \sum_i |s_i - \gamma_i a| \geq \mathrm{dist}(\tau, \mathbb{Z}) = \min\{\alpha, \beta\}.$$

Because $0 < \gamma < 1$ and $\alpha\beta \leq \min\{\alpha, \beta\}$, it follows that

$$D \geq \gamma\alpha\beta.$$

Hence

$$\gamma(\tau - k)(\tau - k - 1) + D \geq 0.$$

This completes the induction. $\blacksquare$

---

## Corollary 1

Let $C$ be an admissible rooted tree with root $\rho$. If $0 \neq x \in L(C)$, then

$$x^2 - x_\rho > 0.$$

**Proof.** Let $\gamma = \gamma(C)$. If $x_\rho \leq 0$, then $x^2 - x_\rho > 0$ because $C$ is positive definite and $x \neq 0$.

Assume $x_\rho > 0$. Let $\rho^\# \in L(C) \otimes \mathbb{Q}$ be the vector satisfying

$$\rho^\# \cdot y = y_\rho \quad \text{for all } y \in L(C).$$

Equivalently, the coefficient vector of $\rho^\#$ is $Q_C^{-1} e_\rho$. Thus

$$(\rho^\#)^2 = \gamma.$$

By Cauchy's inequality in the positive definite real vector space $L(C) \otimes \mathbb{R}$,

$$x_\rho^2 = (x \cdot \rho^\#)^2 \leq x^2 (\rho^\#)^2 = \gamma x^2.$$

Since $\gamma < 1$, we get

$$x^2 \geq \frac{x_\rho^2}{\gamma} > x_\rho^2 \geq x_\rho.$$

Therefore $x^2 - x_\rho > 0$. $\blacksquare$

---

## Theorem 1

Let $T$ be a finite weighted tree whose associated form is positive definite. Suppose that there is a unique vertex $v$ such that

$$w(v) < d_T(v).$$

Then $T$ contains a vertex that is irreducible in $L(T)$.

**Proof.** Since the form is positive definite, every vertex has positive square. Thus every vertex weight is a positive integer.

If some vertex $u$ has $w(u) = 1$, then $u^2 = 1$, and $u$ is irreducible by the first lemma. Hence we may assume from now on that every vertex weight is at least $2$.

Let $v$ be the unique vertex with $w(v) < d_T(v)$. We will prove that $v$ itself is irreducible.

Let $C_1, \ldots, C_m$ be the connected components of $T \setminus \{v\}$. For each $i$, let $\rho_i$ be the unique vertex of $C_i$ adjacent to $v$, and root $C_i$ at $\rho_i$. Because $v$ is the unique bad vertex, every vertex $x \in C_i$ satisfies

$$w(x) \geq d_T(x).$$

With the orientation away from $\rho_i$, each $x \in C_i$ has exactly one edge pointing toward $v$ or toward its parent, so

$$d_T(x) = \mathrm{ch}_{C_i}(x) + 1.$$

Therefore

$$w(x) \geq \mathrm{ch}_{C_i}(x) + 1.$$

Since all weights are at least $2$, each $C_i$ is admissible. Let

$$\gamma_i = \gamma(C_i).$$

By the Schur complement formula applied to the decomposition of $T$ into $v$ and the components $C_i$, positive definiteness of $T$ implies

$$w(v) - \sum_i \gamma_i > 0.$$

Write $W = w(v)$.

Suppose, toward a contradiction, that $v$ is reducible. Then there exist nonzero $a, b \in L(T)$ such that

$$v = a + b, \quad a \cdot b \geq 0.$$

Put $z = -b$. Then $a = v + z$, and

$$0 \leq a \cdot b = (v + z) \cdot (-z) = -(z^2 + v \cdot z).$$

Hence

$$z^2 + v \cdot z \leq 0.$$

Also $z \neq 0$ and $z \neq -v$, because $a, b \neq 0$.

Let $q$ be the coefficient of $v$ in $z$. If $q \leq -1$, replace $z$ by

$$z' = -v - z.$$

This replacement corresponds to interchanging $a$ and $b$, and

$$z' \cdot (z' + v) = z \cdot (z + v).$$

Moreover, the coefficient of $v$ in $z'$ is $-1 - q \geq 0$. Thus we may assume that the coefficient of $v$ in $z$ is a nonnegative integer $p$.

Write

$$z = pv + \sum_i y_i, \quad y_i \in L(C_i).$$

Let $s_i = (y_i)_{\rho_i}$. Since $v \cdot y_i = -s_i$, we compute

$$z^2 + v \cdot z = \left(Wp^2 - 2p\sum_i s_i + \sum_i y_i^2\right) + \left(Wp - \sum_i s_i\right) = Wp(p + 1) + \sum_i\left(y_i^2 - (2p + 1)s_i\right).$$

First suppose $p \geq 1$. Applying the rooted estimate to each $C_i$ with $k = p$, we get

$$y_i^2 - (2p + 1)s_i \geq -\gamma_i p(p + 1).$$

Therefore

$$z^2 + v \cdot z \geq \left(W - \sum_i \gamma_i\right)p(p + 1) > 0,$$

contradicting $z^2 + v \cdot z \leq 0$.

It remains to consider $p = 0$. Then

$$z^2 + v \cdot z = \sum_i (y_i^2 - s_i).$$

By the corollary, each term $y_i^2 - s_i$ is nonnegative, and it is strictly positive whenever $y_i \neq 0$. Since $z \neq 0$ and $p = 0$, at least one $y_i$ is nonzero. Hence

$$z^2 + v \cdot z > 0,$$

again contradicting $z^2 + v \cdot z \leq 0$.

Thus $v$ is irreducible. Consequently, $T$ contains an irreducible vertex. $\blacksquare$
