# Counterexample to Problem 27(b)
Problem 27b. In [107], it is conjectured that Int(A) is always a ring when
D has finite residue rings. Prove this conjecture or give a counterexample in
this case.

Let

\[
D=\mathbf F_2[\pi],
\qquad
K=\mathbf F_2(\pi).
\]

Then \(D\) has finite residue rings.

We construct a finite \(\mathbf F_2\)-algebra \(R\) such that the right null-polynomial set
\(K(R)\) is not a right ideal. This immediately yields a counterexample to
\(\operatorname{Int}(A)\) being a ring.

---

## Step 1. Construct a finite ring \(R\)

Take the path algebra over \(\mathbf F_2\) of the quiver

\[
e \xrightarrow{u} f \xrightarrow{v} e
\]

truncated by all paths of length \(\ge 4\).

Basis:

\[
e,f,u,v,p=uv,q=vu,s=uvu,w=vuv.
\]

Multiplication is path concatenation whenever possible,
and \(0\) otherwise.

Thus \(R\) is a finite noncommutative ring of size \(2^8\).

---

## Step 2. A null polynomial

Define

\[
F(X)
=
uX^2
+
eX^3
+
(e+u)X^4
+
eX^5
+
eX^6.
\]

For any

\[
r=
\alpha e+\beta f+\gamma u+\delta v
+\eta p+\theta q+\lambda s+\mu w,
\]

one computes

\[
F(r)
=
e(r^3+r^4+r^5+r^6)
+
u(r^2+r^4).
\]

A direct calculation in the truncated path algebra gives

\[
e(r^3+r^4+r^5+r^6)
=
u(r^2+r^4)
=
\gamma\delta\, s
\]

whenever \((\alpha,\beta)=(0,0)\) or \((1,1)\),
and both sides vanish when
\((\alpha,\beta)=(1,0)\) or \((0,1)\).

Since the characteristic is \(2\),

\[
F(r)=0
\]

for every \(r\in R\).

Hence

\[
F\in K(R),
\]

the set of right null-polynomials of \(R\).

---

## Step 3. \(K(R)\) is not a right ideal

Multiply \(F\) on the right by the constant polynomial \(e\).

Because

\[
ue=0,
\qquad
(e+u)e=e,
\]

we get

\[
F(X)e
=
eX^3+eX^4+eX^5+eX^6.
\]

Now set

\[
a=u+v.
\]

Then

\[
a^2=p+q,
\qquad
a^3=s+w,
\qquad
a^4=0.
\]

Therefore

\[
(F e)(a)
=
e(s+w)
=
s
\neq 0.
\]

So

\[
F\in K(R),
\qquad
Fe\notin K(R).
\]

Hence

\[
K(R)
\]

is **not** a right ideal of \(R[X]\).

---

## Step 4. Lift to an integer-valued polynomial counterexample

Let

\[
A=D\otimes_{\mathbf F_2}R.
\]

Then

* \(A\) is finite free over \(D\),
* \(A\) is torsion-free,
* \(D\) has finite residue rings,
* \(A/\pi A \cong R\).

Lift \(F\) to

\[
\widetilde F(X)\in A[X].
\]

Since \(F\) is null modulo \(\pi\),

\[
\widetilde F(a)\in \pi A
\qquad
(\forall a\in A).
\]

Hence

\[
P(X)
=
\frac{\widetilde F(X)}{\pi}
\]

belongs to

\[
\operatorname{Int}(A).
\]

The constant polynomial \(e\) also belongs to
\(\operatorname{Int}(A)\).

---

## Step 5. Product is not integer-valued

Evaluate at

\[
a=u+v.
\]

Since

\[
(\widetilde F e)(a)=s,
\]

we obtain

\[
(Pe)(a)
=
\frac{s}{\pi}.
\]

Because \(A\) is a free \(D\)-module with basis

\[
e,f,u,v,p,q,s,w,
\]

the element \(s\) is not divisible by \(\pi\) in \(A\).

Thus

\[
\frac{s}{\pi}\notin A.
\]

Therefore

\[
Pe\notin \operatorname{Int}(A).
\]

---

## Conclusion

We have

\[
P\in \operatorname{Int}(A),
\qquad
e\in \operatorname{Int}(A),
\qquad
Pe\notin \operatorname{Int}(A).
\]

Hence

\[
\operatorname{Int}(A)
\]

is not closed under multiplication.

Therefore Problem 27(b) is false.
