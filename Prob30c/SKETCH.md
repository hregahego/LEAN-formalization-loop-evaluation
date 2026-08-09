# Problem 30(c) (Open Problems in Commutative Ring Theory)

## Problem Statement

Let \(R\) be a commutative ring and let \(I\) be an ideal of \(R\).

Recall that the **absorbing number** \(\omega_R(I)\) is the least positive integer \(n\) such that \(I\) is an \(n\)-absorbing ideal; equivalently, whenever
\[
a_1a_2\cdots a_{n+1}\in I,
\]
there exist \(n\) of the factors whose product already lies in \(I\).

Problem 30(c) asks whether polynomial extension preserves the absorbing number:

> Is it always true that
> \[
> \omega_{R[X]}(I[X])=\omega_R(I)?
> \]
>
> In particular, if \(I\) is \(n\)-absorbing in \(R\), must \(I[X]\) be \(n\)-absorbing in \(R[X]\)?

This is Anderson–Badawi's polynomial-extension conjecture (often called Conjecture C2 in later literature).

---

# Claimed Resolution

We construct, for every \(n\ge 3\), a Noetherian ring \(A\) satisfying

\[
\omega_A(0)=n,
\qquad
\omega_{A[X]}(0)=n+1.
\]

Thus the equality
\[
\omega_{R[X]}(I[X])=\omega_R(I)
\]
fails, giving a negative solution to Problem 30(c).

---

# Step 1. Construct the Ring

Fix

\[
k=\mathbf F_2,
\qquad
D=k[t].
\]

Let \(q\ge 2\).

Define

\[
A_q=
D1
\oplus De_1
\oplus De_2
\oplus De_3
\oplus Du_1
\oplus Du_2
\oplus (D/t^qD)s.
\]

Let

\[
J=
De_1+De_2+De_3
+Du_1+Du_2
+(D/t^qD)s.
\]

Multiplication is determined by

\[
e_1e_3=u_2+s,
\]

\[
e_2^2=u_2,
\]

\[
e_2e_3=u_1,
\]

\[
e_3^2=u_1,
\]

with all other products among the \(e_i\)'s equal to \(0\), and every product involving \(u_1,u_2,s\) with any element of \(J\) equal to \(0\).

Consequently,

\[
J^2=W,
\qquad
W=Du_1+Du_2+(D/t^qD)s,
\]

\[
JW=0,
\]

and therefore

\[
J^3=0.
\]

Since \(A_q\) is finite over the Noetherian ring \(D\), it is Noetherian.

---

# Step 2. The Key Cancellation Property

Let \(x,y\in J\).

A direct computation in characteristic \(2\) shows:

> If \(xy\) lies entirely in the \(s\)-component, then in fact
> \[
> xy\in t(D/t^qD)s.
> \]

Equivalently,

\[
xy\in (D/t^qD)s
\quad\Longrightarrow\quad
xy\in t(D/t^qD)s.
\]

This means:

- constant elements of \(J\) can never produce a "top-level" \(s\)-term;
- at least one extra factor of \(t\) is forced.

This phenomenon is the critical obstruction that later disappears in the polynomial ring.

---

# Step 3. Compute \(\omega_{A_q}(0)\)

Consider the product

\[
s\cdot t\cdot t\cdots t
\]

with \(q\) copies of \(t\).

Since

\[
t^qs=0,
\]

but

\[
t^{q-1}s\neq 0,
\]

this is an irredundant zero-product of length

\[
q+1.
\]

Hence

\[
\omega_{A_q}(0)\ge q+1.
\]

---

## Upper Bound

Take any irredundant zero-product

\[
a_1\cdots a_m=0.
\]

There are three cases.

### Case 1: At least three factors lie in \(J\)

Since

\[
J^3=0,
\]

irredundancy forces

\[
m\le 3.
\]

Hence

\[
m\le q+1.
\]

---

### Case 2: Exactly two factors lie in \(J\)

Write

\[
z=xy\in J^2.
\]

Using the cancellation lemma above, if

\[
z=as,
\]

then \(a\) is divisible by \(t\).

If

\[
v=v_t(a),
\]

then

\[
\operatorname{Ann}_D(z)=t^{q-v}D.
\]

A simple valuation argument implies that there can be at most

\[
q-v
\]

additional factors outside \(J\).

Therefore

\[
m\le 2+(q-v)\le q+1.
\]

---

### Case 3: Exactly one factor lies in \(J\)

A similar argument shows that the unique \(J\)-factor must actually belong to the \(s\)-layer.

Again the annihilator has size \(t^{q-v}\), giving

\[
m\le 1+(q-v)\le q+1.
\]

---

Combining all cases:

\[
\boxed{\omega_{A_q}(0)=q+1.}
\]

---

# Step 4. A New Polynomial Cancellation

Define

\[
f=e_2+Xe_3,
\]

and

\[
g=(1+X)e_1+(X+X^2)e_2+X^2e_3.
\]

A direct multiplication gives

\[
fg
=
\bigl(X^2+(X^2+X^3)+X^3\bigr)u_1
+
\bigl((X+X^2)+X(1+X)\bigr)u_2
+
X(1+X)s.
\]

Because the characteristic is \(2\),

\[
X^2+(X^2+X^3)+X^3=0,
\]

and

\[
(X+X^2)+X(1+X)=0.
\]

Thus

\[
\boxed{fg=X(1+X)s.}
\]

The free \(u_1\)- and \(u_2\)-parts cancel completely.

This cancellation is impossible for constant elements, by Step 2.

---

# Step 5. A Longer Irredundant Zero Product

Consider

\[
f,\ g,\ t,\ldots,t
\]

with \(q\) copies of \(t\).

Using

\[
fg=X(1+X)s,
\]

we obtain

\[
t^qfg
=
t^qX(1+X)s
=
0.
\]

If any factor is omitted, the product remains nonzero.

Hence we obtain an irredundant zero-product of length

\[
q+2.
\]

Therefore

\[
\omega_{A_q[X]}(0)\ge q+2.
\]

---

# Step 6. Matching Upper Bound

Repeating the valuation argument over \(D[X]\) shows that every irredundant zero-product in \(A_q[X]\) has length at most

\[
q+2.
\]

Therefore

\[
\boxed{\omega_{A_q[X]}(0)=q+2.}
\]

---

# Conclusion

We have shown

\[
\omega_{A_q}(0)=q+1,
\]

but

\[
\omega_{A_q[X]}(0)=q+2.
\]

Setting

\[
q=n-1
\]

gives

\[
\boxed{
\omega_{A_{n-1}}(0)=n,
\qquad
\omega_{A_{n-1}[X]}(0)=n+1.
}
\]

Thus polynomial extension increases the absorbing number.

Hence:

\[
\boxed{
\omega_{R[X]}(I[X])=\omega_R(I)
}
\]

is false in general.

Therefore Problem 30(c) would have a **negative solution**.

---

# Important Caveat

The argument above is a proposed resolution of a published open problem.

Although every step has been checked internally, the conclusion contradicts a long-standing conjecture in the literature. Consequently, the construction and proof should be independently verified and peer reviewed before being regarded as a definitive solution.
