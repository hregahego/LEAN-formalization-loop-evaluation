# An entropy bound of 1196/3125 = 0.38272 for union-closed families

A finite family $\mathcal F$ of finite sets is **union-closed** if $A \cup B \in \mathcal F$
whenever $A, B \in \mathcal F$. Frankl's union-closed sets conjecture asks whether every such
family other than $\{\varnothing\}$ has an element belonging to at least half of its members.
This problem proves the currently best explicit constant by the entropy method: **every
nonempty finite union-closed family $\mathcal F \ne \{\varnothing\}$ has an element belonging
to at least a $1196/3125 = 0.38272$ fraction of its members.**

The proof is the one in `frankl_038272_readability_v4.tex` (companion certificate:
`frankl_038272_certificate.py`, recorded output `certificate_output.txt`). It combines
Gilmer-style independent sampling with a shared-sign, conditionally-i.i.d. coupling, and
reduces everything to one two-variable scalar entropy inequality, which in turn splits into a
diagonal estimate and an off-diagonal estimate. Four assertions were originally
computer-certified (two exact rational polynomial certificates, two interval-arithmetic
covers of one-dimensional transcendental inequalities); **all four must become proved lemmas
in the formalization**. This sketch states all of them with exact data.

## Global definitions (to be frozen in `Defs.lean`)

All of these are used by the theorem statement or pervasively in the proof. Fix them exactly
as written.

**Combinatorics.**
- $\mathcal F$ : a finite family of finite sets (Lean: `F : Finset (Finset α)` for a decidable-eq
  type, or concretely `Finset (Finset ℕ)`).
- `UnionClosed F` : $\forall A \in \mathcal F,\ \forall B \in \mathcal F,\ A \cup B \in \mathcal F$.
- The **frequency** of an element $x$ is $|\{A \in \mathcal F : x \in A\}| / |\mathcal F|$. In the
  frozen statement avoid real division: use
  $3125 \cdot |\{A \in \mathcal F : x \in A\}| \ge 1196 \cdot |\mathcal F|$.

**Rational constants.** (All exact rationals; never floating point.)
- $c = 1196/3125 = 0.38272$ — the headline constant.
- $\lambda = 9/10$, so $\lambda^2 = 81/100$ — the coupling strength.
- $\beta = 1/10$ — the mixing weight ($9/10$ on the independent coupling, $1/10$ on the shared one).
- $C = 81001/50000 = 1.62002$ — the scalar-inequality constant.
- Strict margin: $C(1-c) - 1 = 929/156250000 > 0$ (exact rational identity; note
  $1 - c = 1929/3125$ and $81001 \cdot 1929 = 156250929$).

**Analysis.** Throughout, $\log$ is the natural logarithm; entropies in the paper use base 2.
For formalization it is simplest to work with **natural-log entropy everywhere** (see Step 8
for the natural-log form of the scalar inequality); Mathlib's `Real.binEntropy` already is
the natural-log binary entropy.
- $H_{\mathrm{nat}}(z) = -z\log z - (1-z)\log(1-z)$ for $z \in [0,1]$, with $0\log 0 = 0$
  (this is `Real.binEntropy`). Base-2 entropy: $h(z) = H_{\mathrm{nat}}(z)/\log 2$.
- $e_{\mathrm{nat}}(s) = H_{\mathrm{nat}}(s)/s$ for $0 < s \le 1$; equivalently
  $e_{\mathrm{nat}}(s) = -\log s - \frac{1-s}{s}\log(1-s)$. (Base-2 version: $e(s) = h(s)/s$.)
- The coupling kernel
  $$q(s,t) = st\bigl(1 + \tfrac{81}{100}(1-s)(1-t)\bigr).$$
- The coupling profile
  $$g(s) = 2\sqrt{\bigl(1 + \tfrac{81}{100}(1-s)^2\bigr)\Bigl(1 - s^2\bigl(1 + \tfrac{81}{100}(1-s)^2\bigr)\Bigr)}.$$

**Probability.** Every probability space in the proof is **finite with rational
probabilities**; no measure theory beyond finitely supported distributions (PMFs / weighted
Finset sums) is needed. Entropy of a finitely supported random variable $Z$:
$H_{\mathrm{nat}}(Z) = \sum_z \Pr(Z = z)\,(-\log \Pr(Z=z))$.

---

# Theorem

Let $\mathcal F$ be a finite union-closed family of finite sets with $\mathcal F \ne \varnothing$
and $\mathcal F \ne \{\varnothing\}$. Then there exists an element $x$ with
$$3125 \cdot \bigl|\{A \in \mathcal F : x \in A\}\bigr| \;\ge\; 1196 \cdot |\mathcal F|,$$
i.e. some element belongs to at least a $1196/3125 = 0.38272$ fraction of the members of
$\mathcal F$.

---

# Proof Sketch

Dependency order: Steps 1–2 are elementary toolboxes; Steps 3–5 are the certified analytic
facts; Steps 6–7 are the two halves of the scalar inequality, assembled in Step 8; Steps 9–11
are the probabilistic/entropy side; Step 12 concludes. Steps 3–8 are pure real analysis with
no probability; Steps 9–12 are finite probability with no hard analysis.

## Step 1. Rational constants and elementary logarithm bounds

Prove the following exact facts.

**(1a) Strict margin.** $C(1-c) - 1 = \frac{81001}{50000}\cdot\frac{1929}{3125} - 1 = \frac{929}{156250000} > 0.$ (Pure `norm_num`.)

**(1b) Logarithm bounds** (all used later; proofs are short explicit series estimates):
$$2 < \log 10 < \tfrac{12}{5}, \qquad \log 2 < \tfrac{25}{36}.$$
- $\log 10 > 2$: from the exponential series, $e < 3$ (e.g. $e = \sum_k 1/k! < 1 + \sum_{k\ge1} 2^{-(k-1)} = 3$), hence $e^2 < 9 < 10$.
- $\log 10 < 12/5$: $e^{12/5} > \sum_{k=0}^{5} \frac{(12/5)^k}{k!} = \frac{166093}{15625} > 10$
  (the partial sum of the exponential series with denominators cleared; each term is rational).
- $\log 2 < 25/36$: from $\log 2 = 2\,\mathrm{artanh}(1/3) = 2\sum_{j\ge0}\frac{1}{(2j+1)3^{2j+1}}$
  (i.e. $\log\frac{1+1/3}{1-1/3} = \log 2$), keep the $j=0,1$ terms and bound the tail:
  $$\log 2 \le \frac{2}{3} + \frac{2}{81} + \underbrace{\frac{2}{5\cdot 3^5}\cdot\frac{1}{1 - 1/9}}_{=1/540} = \frac{1123}{1620} < \frac{1125}{1620} = \frac{25}{36}.$$
  (Tail: for $j \ge 2$, $\frac{2}{(2j+1)3^{2j+1}} \le \frac{2}{5\cdot 3^5}\,9^{-(j-2)}$, geometric sum $\le \frac{2}{5\cdot243}\cdot\frac98 = \frac{1}{540}$.)

Also record the derived inequality $\frac{123}{65} > \frac{10}{9}C$ (cross-multiplied:
$123 \cdot 45000 = 5\,535\,000 > 5\,265\,065 = 81001 \cdot 65$), used in Step 7.

*Formalization notes.* Mathlib may already provide adequate numeric bounds on `Real.log 2`
and `Real.log 10` (e.g. via `Real.exp_one_lt_d9` and friends, or `norm_num` extensions for
`Real.log`); if so, use them — the exact bounds above are what the later steps consume.

## Step 2. Binary-entropy toolbox: elementary bounds and series identities

All statements are about real functions on $[0,1]$; all series below have nonnegative terms
dominated by $\frac{1}{k(k+1)}$ (telescoping, summable), so `tsum` convergence is easy.

**(2a) Parabola lower bound.** For $0 \le z \le 1$:
$$H_{\mathrm{nat}}(z) \ \ge\ (4\log 2)\, z(1-z), \qquad\text{equivalently } h(z) \ge 4z(1-z).$$
Proof: write $z = (1-u)/2$, $u \in [-1,1]$. The series identity
$$\log 2 - H_{\mathrm{nat}}\Bigl(\frac{1-u}{2}\Bigr) = \sum_{k\ge1} \frac{u^{2k}}{2k(2k-1)}$$
(equivalently $H_{\mathrm{nat}}(\frac{1-u}{2}) = \log 2 - \frac12[(1+u)\log(1+u) + (1-u)\log(1-u)]$
combined with identity (2f) below at $z=u$), together with
$\sum_{k\ge1} \frac{1}{2k(2k-1)} = 1 - \frac12 + \frac13 - \cdots = \log 2$, gives
$\log 2 - H_{\mathrm{nat}}(z) \le u^2 \log 2$, and $4z(1-z) = 1 - u^2$.

**(2b) Elementary logarithm/entropy bounds.** For $0 \le z < 1$:
$z \le -\log(1-z) \le \frac{z}{1-z}$. Consequences, for $0 < z < 1$:
$$z\bigl(\log(1/z) + 1 - z\bigr) \ \le\ H_{\mathrm{nat}}(z) \ \le\ z\bigl(\log(1/z) + 1\bigr),
\qquad 0 \ \le\ -\frac{1-s}{s}\log(1-s) \ \le\ 1 .$$
(For the two-sided $H_{\mathrm{nat}}$ bound: $-(1-z)\log(1-z) \in [z(1-z),\, z]$.)

**(2c) The auxiliary series $f$.** For $0 < z \le 1$ define
$f(z) = \sum_{k\ge1} \frac{z^k}{k(k+1)}$; then
$$f(z) = 1 + \frac{1-z}{z}\log(1-z) \quad (0<z<1), \qquad f(1) = 1.$$
(Proof: $\sum \frac{z^k}{k(k+1)} = \sum\frac{z^k}{k} - \sum\frac{z^k}{k+1}
= -\log(1-z) - \frac1z(-\log(1-z) - z)$.)

**(2d) Series expansion of $e_{\mathrm{nat}}$.** For $0 < z \le 1$:
$$e_{\mathrm{nat}}(z) = -\log z + 1 - f(z).$$
(Immediate from $e_{\mathrm{nat}}(z) = -\log z - \frac{1-z}{z}\log(1-z)$ and (2c); at $z=1$
both sides are $0$.)

**(2e) Sum-of-squares identity.** For $0 < s, t \le 1$:
$$2e_{\mathrm{nat}}(st) - e_{\mathrm{nat}}(s^2) - e_{\mathrm{nat}}(t^2)
 = \sum_{k\ge1} \frac{(s^k - t^k)^2}{k(k+1)} .$$
(From (2d): the $\log$ terms cancel because $-2\log(st) + \log s^2 + \log t^2 = 0$, and
$f(s^2) + f(t^2) - 2f(st) = \sum \frac{(s^k-t^k)^2}{k(k+1)}$ termwise.)

**(2f) The function $Q$ and its series.** For $0 < z < 1$ define
$$Q(z) = \frac{(1+z)\log(1+z) + (1-z)\log(1-z)}{z^2}
\qquad\text{and note}\qquad
Q(z) = \sum_{j\ge0} \frac{z^{2j}}{(j+1)(2j+1)} .$$
Extend by the series to $z \in [0,1]$: $Q(0) = 1$, $Q(1) = 2\log 2$. Facts needed later:
$Q(z) \ge 1$; $Q(z) \ge 1 + z^2/6$ (first two series terms); $Q$ is increasing with
$$0 \ \le\ Q'(z) = \sum_{j\ge1} \frac{2j\,z^{2j-1}}{(j+1)(2j+1)} \ \le\ \sum_{j\ge1} z^{2j-1} = \frac{z}{1-z^2},
\qquad Q'(z) \ \le\ \sum_{j\ge1}\frac{z^{2j-1}}{j} = \frac{-\log(1-z^2)}{z},$$
using the coefficient bounds $\frac{2j}{(j+1)(2j+1)} \le 1$ and $\frac{2j}{(j+1)(2j+1)} \le \frac1j$
(both because $(j+1)(2j+1) = 2j^2 + 3j + 1 \ge 2j^2$).

**(2g) The function $A$ and its closed form.** For $u \in [0,1]$, with $z = 1 - u^2$, define
$$A(u) = \Bigl(\sum_{k\ge1} \frac{\bigl(1 - (1-u^2)^k\bigr)^2}{k(k+1)}\Bigr)^{1/2}
\qquad\text{and prove}\qquad
A(u) = u\,\sqrt{Q(1-u^2)} .$$
Equivalently: $\sum_{k\ge1}\frac{(1-z^k)^2}{k(k+1)} = (1-z)\,Q(z)$ for $z \in [0,1]$. Proof:
the left side is $1 - 2f(z) + f(z^2)$; substitute (2c) and simplify —
$$1 - 2f(z) + f(z^2) = \frac{1-z}{z^2}\bigl[(1-z)\log(1-z) + (1+z)\log(1+z)\bigr] = (1-z)Q(z).$$
Boundary values: $A(0) = 0$, $A(1) = 1$.

**(2h) Derivative of $A$.** For $0 < u < 1$ (so $0 < z < 1$, $z = 1-u^2$, $dz/du = -2u$):
$$A'(u) = \frac{Q(z) - (1-z)\,Q'(z)}{\sqrt{Q(z)}} .$$
(Chain rule on $A(u) = u\sqrt{Q(z)}$; $Q(z) \ge 1 > 0$ so the square root is smooth.)

**(2i) The polynomial $P$ and the profile.** Define the degree-5 polynomial
$$P(z) = \Bigl(1 + \tfrac{81}{100}(1-z)^2\Bigr)\Bigl(1 + z - \tfrac{81}{100}z^2(1-z)\Bigr),$$
in the power basis
$P(z) = \tfrac{181}{100} + \tfrac{19}{100}z - \tfrac{22761}{10000}z^2 + \tfrac{35883}{10000}z^3 - \tfrac{19683}{10000}z^4 + \tfrac{6561}{10000}z^5$.
Prove:
- $P(z) > 0$ on $[0,1]$ (both factors are $\ge 1$ there: the second is
  $1 + z - \frac{81}{100}z^2(1-z) \ge 1 + z - z^2(1-z) \ge 1$ since $z^2(1-z) \le z$).
- **Profile factorization**: for $s \in [0,1]$ and $u = \sqrt{1-s}$ (so $s = 1-u^2$, $z := s$),
  $$g(s)^2 = 4\,(1-s)\,P(s), \qquad\text{i.e.}\qquad g(1-u^2) = 2u\,\sqrt{P(1-u^2)} .$$
  (Pure algebra: $1 - s^2(1+\frac{81}{100}(1-s)^2) = (1-s)\bigl[1 + s - \frac{81}{100}s^2(1-s)\bigr]$.)
  In particular the expression under the square root in $g$'s definition is nonnegative on
  $[0,1]$, $g \ge 0$, $g(1) = 0$, and $g(0) = 2\sqrt{181/100} = \sqrt{181}/5$.
- Derivative: for $0 < u < 1$, with $z = 1-u^2$,
  $$\frac{d}{du}\,g(1-u^2) = \frac{2\bigl(P(z) - (1-z)P'(z)\bigr)}{\sqrt{P(z)}} .$$

*Formalization notes.* State every series fact with `tsum` over `ℕ` (index shifted to start
at $k=1$ or reindexed from $0$); summability always by comparison with the telescoping
$\sum 1/(k(k+1)) = 1$. The identities (2c)–(2g) can be proved by manipulating the standard
power series $-\log(1-z) = \sum z^k/k$ (Mathlib: `Real.log`, `hasSum` versions exist for
$|z|<1$); the boundary points $z \in \{0,1\}$ are handled separately by direct evaluation and
continuity (Abel-type limits can be avoided: at $z=1$ every identity is a finite statement
like $f(1)=1$, $\sum 1/(k(k+1)) = 1$).

## Step 3. The rank-one product lower bound: $h(q(s,t)) \ge s\,t\,g(s)\,g(t)$

This is Proposition 3.1 (`prop:rank-one`) of the paper and the first computer-certified
assertion. Everything here is exact rational polynomial algebra plus (2a).

**(3a) Sign-average identity and range of $q$.** For $s, t \in [0,1]$:
$$q(s,t) = \tfrac12\bigl(s + \lambda s(1-s)\bigr)\bigl(t + \lambda t(1-t)\bigr)
         + \tfrac12\bigl(s - \lambda s(1-s)\bigr)\bigl(t - \lambda t(1-t)\bigr), \qquad \lambda = \tfrac{9}{10}.$$
(Ring identity; the cross terms cancel and $\lambda^2 = 81/100$.) Since
$0 \le s - \lambda s(1-s)$ and $s + \lambda s(1-s) \le s(2-s) \le 1$ (because
$s - \lambda s(1-s) \ge s - s(1-s) = s^2 \ge 0$ and $1 - s(2-s) = (1-s)^2 \ge 0$), each of
the four factors lies in $[0,1]$, hence $q(s,t) \in [0,1]$. This identity is also exactly the
probabilistic computation used in Step 11 (average over a uniform sign $U \in \{\pm1\}$ of
the product of the two modified zero-probabilities).

**(3b) Diagonal normalization.** With $q(s,s) = s^2\bigl(1 + \frac{81}{100}(1-s)^2\bigr)$:
$$s\,g(s) = 2\sqrt{q(s,s)\bigl(1 - q(s,s)\bigr)} \qquad (s \in [0,1]).$$
(Square both sides; pure ring identity given $g^2$'s definition, since
$s^2 g(s)^2 = 4 s^2(1+\tfrac{81}{100}(1-s)^2)(1 - s^2(1+\tfrac{81}{100}(1-s)^2))$.)

**(3c) Determinant factorization with explicit quotient $R$.** Define the symmetric
bivariate polynomial $R(s,t)$ of degree 4 in each variable by its power-basis coefficients
$R = \sum_{i,j} r_{ij} s^i t^j$ (denominators are powers of 10; $r_{ij} = r_{ji}$):

| $r_{ij}$ | $j=0$ | $j=1$ | $j=2$ | $j=3$ | $j=4$ |
|---|---|---|---|---|---|
| $i=0$ | $\frac{5119741}{1000000}$ | $-\frac{2653641}{250000}$ | $\frac{5028723}{500000}$ | $-\frac{1187541}{250000}$ | $\frac{1187541}{1000000}$ |
| $i=1$ | $-\frac{2653641}{250000}$ | $\frac{11244987}{500000}$ | $-\frac{8719569}{500000}$ | $\frac{662661}{100000}$ | $-\frac{531441}{500000}$ |
| $i=2$ | $\frac{5028723}{500000}$ | $-\frac{8719569}{500000}$ | $\frac{8070597}{1000000}$ | $\frac{124659}{250000}$ | $-\frac{1187541}{1000000}$ |
| $i=3$ | $-\frac{1187541}{250000}$ | $\frac{662661}{100000}$ | $\frac{124659}{250000}$ | $-\frac{2250423}{500000}$ | $\frac{531441}{250000}$ |
| $i=4$ | $\frac{1187541}{1000000}$ | $-\frac{531441}{500000}$ | $-\frac{1187541}{1000000}$ | $\frac{531441}{250000}$ | $-\frac{531441}{500000}$ |

Prove the **exact polynomial identity** (checkable by `ring` / `polyrith` after clearing
denominators; degree $\le 8$ in each variable):
$$\bigl[q(s,t)\bigl(1-q(s,t)\bigr)\bigr]^2
 - q(s,s)\bigl(1-q(s,s)\bigr)\,q(t,t)\bigl(1-q(t,t)\bigr)
 = s^2 t^2 (s-t)^2\, R(s,t).$$

**(3d) Positivity of $R$ via Bernstein expansion.** Prove the **exact identity**
$$R(s,t) = \sum_{k=0}^{4}\sum_{\ell=0}^{4} c_{k\ell}\, B_k(s)\, B_\ell(t),
\qquad B_k(x) = \binom{4}{k} x^k (1-x)^{4-k},$$
with the explicit symmetric coefficient matrix ($c_{k\ell} = c_{\ell k}$):

| $c_{k\ell}$ | $\ell=0$ | $\ell=1$ | $\ell=2$ | $\ell=3$ | $\ell=4$ |
|---|---|---|---|---|---|
| $k=0$ | $\frac{5119741}{1000000}$ | $\frac{24661}{10000}$ | $\frac{14887}{10000}$ | $1$ | $1$ |
| $k=1$ | $\frac{24661}{10000}$ | $\frac{9744659}{8000000}$ | $\frac{36787}{40000}$ | $\frac{319}{400}$ | $1$ |
| $k=2$ | $\frac{14887}{10000}$ | $\frac{36787}{40000}$ | $\frac{3191251}{4000000}$ | $\frac{31387}{40000}$ | $1$ |
| $k=3$ | $1$ | $\frac{319}{400}$ | $\frac{31387}{40000}$ | $\frac{319}{400}$ | $1$ |
| $k=4$ | $1$ | $1$ | $1$ | $1$ | $1$ |

All 25 coefficients are positive; the smallest is $c_{23} = 31387/40000$. Since each
$B_k(x) \ge 0$ on $[0,1]$ and $\sum_k B_k(x) = 1$ (binomial theorem), conclude
$$R(s,t) \ \ge\ \frac{31387}{40000} \ >\ 0 \qquad \text{on } [0,1]^2 .$$
(In Lean it may be cleanest to *define* $R$ by the Bernstein expansion, prove (3c) by `ring`,
and get positivity for free; the power-basis table is then a redundant cross-check.)

**(3e) The product lower bound.** For all $s, t \in [0,1]$:
$$h\bigl(q(s,t)\bigr) \ \ge\ s\,t\,g(s)\,g(t),
\qquad\text{equivalently}\qquad
H_{\mathrm{nat}}\bigl(q(s,t)\bigr) \ \ge\ (\log 2)\, s\,t\,g(s)\,g(t).$$
Proof: by (3c) + (3d), $[q(1-q)]^2 \ge q(s,s)(1-q(s,s))\cdot q(t,t)(1-q(t,t)) \ge 0$, so
taking square roots ($q(1-q) \ge 0$ by (3a)),
$q(s,t)(1-q(s,t)) \ge \sqrt{q(s,s)(1-q(s,s))}\sqrt{q(t,t)(1-q(t,t))}$. Then by (2a) and (3b),
$$h(q(s,t)) \ \ge\ 4\,q(s,t)(1-q(s,t)) \ \ge\ 4\cdot\frac{s\,g(s)}{2}\cdot\frac{t\,g(t)}{2} = s\,t\,g(s)\,g(t).$$

## Step 4. Profile speed bound: $\bigl|\frac{d}{du} g(1-u^2)\bigr| \le \frac{16}{5}$, hence $|g(s)-g(t)| \le \frac{16}{5}\,|u-v|$

Second computer-certified assertion; again exact rational polynomial algebra.

**(4a) The certificate polynomial.** Let $N(z) = P(z) - (1-z)P'(z)$ (degree 5):
$$N(z) = \tfrac{81}{50} + \tfrac{24661}{5000}z - \tfrac{43983}{2500}z^2 + \tfrac{27783}{1250}z^3 - \tfrac{6561}{500}z^4 + \tfrac{19683}{5000}z^5 ,$$
and let $G(z) = 64\,P(z) - 25\,N(z)^2$ (degree 10):
$$G(z) = \tfrac{5023}{100} - \tfrac{1936741}{5000}z + \tfrac{671213879}{1000000}z^2 + \tfrac{691992963}{250000}z^3 - \tfrac{614117943}{50000}z^4 + \tfrac{5627704311}{250000}z^5 - \tfrac{2486402487}{100000}z^6 + \tfrac{4511402649}{250000}z^7 - \tfrac{2169873603}{250000}z^8 + \tfrac{129140163}{50000}z^9 - \tfrac{387420489}{1000000}z^{10}.$$

**(4b) Positivity of $G$ on $[0,1]$** via degree-10 Bernstein expansions on the two halves.
With $B^{10}_k(x) = \binom{10}{k}x^k(1-x)^{10-k}$, prove the exact identities
$G(x/2) = \sum_{k=0}^{10} b_k B^{10}_k(x)$ and $G(1/2 + x/2) = \sum_{k=0}^{10} b'_k B^{10}_k(x)$
with

$$b = \Bigl(\tfrac{5023}{100},\ \tfrac{3086259}{100000},\ \tfrac{2740346279}{180000000},\ \tfrac{1487513279}{240000000},\ \tfrac{2530002779}{840000000},\ \tfrac{8124178271}{2016000000},\ \tfrac{10339753661}{1344000000},\ \tfrac{49104267221}{3840000000},\ \tfrac{53149568879}{2880000000},\ \tfrac{30879396079}{1280000000},\ \tfrac{30120271679}{1024000000}\Bigr),$$
$$b' = \Bigl(\tfrac{30120271679}{1024000000},\ \tfrac{88842566237}{2560000000},\ \tfrac{456352242227}{11520000000},\ \tfrac{168042175337}{3840000000},\ \tfrac{157752434729}{3360000000},\ \tfrac{282661663}{5760000},\ \tfrac{419806997}{8400000},\ \tfrac{1850591}{37500},\ \tfrac{837863}{18000},\ \tfrac{10077}{250},\ 28\Bigr).$$

All 22 coefficients are positive (smallest: $b_4 = 2530002779/840000000 \approx 3.01$).
Hence $G(z) > 0$ for all $z \in [0,1]$ (cover $[0,1]$ by the two affine images; Bernstein
polynomials are nonnegative and sum to 1).

**(4c) Speed bound.** From $G > 0$: $25\,N(z)^2 < 64\,P(z)$, so
$|N(z)|/\sqrt{P(z)} < 8/5$ on $[0,1]$, and by (2i)
$$\Bigl|\frac{d}{du}\,g(1-u^2)\Bigr| = \frac{2\,|N(1-u^2)|}{\sqrt{P(1-u^2)}} \ \le\ \frac{16}{5}
\qquad (0 < u < 1).$$
Integrating (mean value theorem; $u \mapsto g(1-u^2)$ is continuous on $[0,1]$,
differentiable on $(0,1)$): **for all $s, t \in [0,1]$, with $u = \sqrt{1-s}$,
$v = \sqrt{1-t}$:**
$$|g(s) - g(t)| \ \le\ \frac{16}{5}\,|u - v| .$$

## Step 5. Entropy speed bound: $A'(u) \ge \frac{8}{9}$, hence $\Bigl(\sum_{k\ge1}\frac{(s^k-t^k)^2}{k(k+1)}\Bigr)^{1/2} \ge \frac{8}{9}\,|u-v|$

Third certified assertion — the transcendental one-variable inequality
$A'(u) - 8/9 \ge 0$. Split by the value of $z = 1-u^2$ into three ranges.

**(5a) Small $z$: $0 < z \le \frac{1}{100}$.** By (2h) and the bounds in (2f)
($\sqrt{Q} \ge 1$, $0 \le Q' \le \frac{z}{1-z^2}$, $0 \le 1-z \le 1$):
$$A'(u) = \sqrt{Q(z)} - \frac{(1-z)Q'(z)}{\sqrt{Q(z)}} \ \ge\ 1 - Q'(z) \ \ge\ 1 - \frac{z}{1-z^2} \ \ge\ 1 - \frac{100}{9999} \ >\ \frac{8}{9}.$$
(Last step: $\frac{z}{1-z^2}$ is increasing; at $z = 1/100$ it is $\frac{100}{9999} < \frac19$.)
*Note for formalization:* this elementary argument actually works for all $z \le 1/10$
(since $\frac{1/10}{1-1/100} = \frac{10}{99} < \frac19$), so the interval-arithmetic range in
(5c) may be shrunk to $[1/10,\, 99999/100000]$ if convenient. This is advisable: the Arb run
needed its deepest subdivisions near $z \approx 0.01$ only because the closed form of $Q$
suffers catastrophic cancellation for small $z$ — use the series (2f) there instead.

**(5b) Large $z$: $\frac{99999}{100000} \le z < 1$.** Write $\varepsilon = 1-z \le 10^{-5}$.
Then $Q(z) \ge 1 + z^2/6 > (27/25)^2$ (exact: $z^2 > 624/625$ suffices, and
$z \ge 99999/100000$ gives $z^2 \ge (99999/100000)^2 > 624/625$), so $\sqrt{Q} > 27/25$. Also,
using $Q' \le -\log(1-z^2)/z$ from (2f), $-\log(1-z^2) = \log\frac{1}{\varepsilon} - \log(1+z) \le \log\frac1\varepsilon$, and $\sqrt{Q}\ge1$:
$$\frac{(1-z)\,Q'(z)}{\sqrt{Q(z)}} \ \le\ \frac{\varepsilon \log(1/\varepsilon)}{z}
\ \le\ \frac{10^{-5}\cdot 5\log 10}{99999/100000} \ \le\ \frac{12}{99999},$$
using that $\varepsilon\log(1/\varepsilon)$ is increasing for $\varepsilon \le 10^{-5} < 1/e$
and $\log 10 < 12/5$ (Step 1b). Hence
$A'(u) > \frac{27}{25} - \frac{12}{99999} > \frac{8}{9}$
(exact rational comparison; $\frac{27}{25} - \frac89 = \frac{43}{225} \approx 0.191$).

**(5c) Middle range: $\frac{1}{100} \le z \le \frac{99999}{100000}$ — INTERVAL-ARITHMETIC OBLIGATION.**
Prove
$$\frac{Q(z) - (1-z)\,Q'(z)}{\sqrt{Q(z)}} \ \ge\ \frac{8}{9}
\qquad\text{on } z \in \Bigl[\frac{1}{100},\, \frac{99999}{100000}\Bigr].$$
The paper certifies this by recursive bisection at exact rational midpoints with 256-bit
directed (Arb) ball arithmetic: 285,621 box evaluations, maximum depth 25 (recorded output).
In Lean this is a finite computation: cover the interval with rational subintervals; on each,
bound $Q$, $Q'$ from above/below using monotonicity ((2f): $Q$ and $Q'$ are increasing and
nonnegative) and certified rational enclosures of $\log$ at rational points (e.g. via the
$\mathrm{artanh}$ series with explicit geometric tail bounds, as in Step 1b, or an available
verified-interval tactic). Equivalent square-free form, given $Q, N_Q := Q - (1-z)Q' > 0$:
$81\,N_Q(z)^2 \ge 64\,Q(z)$. The true minimum of $A'(u) - 8/9$ on this range is comfortably
bounded away from $0$ (the tiny recorded per-box margins occur only near $z \approx 0.01$
from cancellation in the closed form of $Q$, see (5a) note); the minimum of $A'(u) - 8/9$
over this range is $\approx 0.032$, attained at an interior dip near $z \approx 0.49$, so a
fairly coarse cover suffices once $Q$ is evaluated stably (series form for $z \le 1/2$,
closed form for $z \ge 1/2$).

**(5d) Conclusion of the entropy speed bound.** For $0 < u < 1$, $A'(u) \ge 8/9$ by
(5a)–(5c). By the mean value theorem and continuity of $A$ on $[0,1]$,
$|A(u) - A(v)| \ge \frac89 |u-v|$ for $u, v \in [0,1]$. Next, the reverse triangle
inequality in $\ell^2$: with
$$a_k = \frac{1 - s^k}{\sqrt{k(k+1)}}, \qquad b_k = \frac{1 - t^k}{\sqrt{k(k+1)}},$$
(square-summable; $\|a\|_2 = A(u)$, $\|b\|_2 = A(v)$ by (2g), where $s = 1-u^2$,
$t = 1-v^2$),
$$\Bigl(\sum_{k\ge1} \frac{(s^k - t^k)^2}{k(k+1)}\Bigr)^{1/2} = \|a - b\|_2 \ \ge\ \bigl|\,\|a\|_2 - \|b\|_2\,\bigr| = |A(u) - A(v)| \ \ge\ \frac{8}{9}\,|u - v| .$$
(For Lean: either use `lp 2` / `EuclideanSpace`-style Minkowski, or prove it for finite
partial sums — $\|(a-b)_{\le M}\|_2 \ge \|a_{\le M}\|_2 - \|b_{\le M}\|_2$ — and pass to the
limit $M \to \infty$.)

## Step 6. The off-diagonal estimate

**Claim (Lemma 4.3, `lem:off-diagonal`).** For all $0 < s, t \le 1$:
$$2e(st) - e(s^2) - e(t^2) \ \ge\ \frac{1}{9}\bigl(g(s) - g(t)\bigr)^2,$$
equivalently in natural-log form
$$2e_{\mathrm{nat}}(st) - e_{\mathrm{nat}}(s^2) - e_{\mathrm{nat}}(t^2) \ \ge\ \frac{\log 2}{9}\bigl(g(s) - g(t)\bigr)^2 .$$

Proof: let $u = \sqrt{1-s}$, $v = \sqrt{1-t}$. By the sum-of-squares identity (2e) and
Step 5d, then Step 4c:
$$2e_{\mathrm{nat}}(st) - e_{\mathrm{nat}}(s^2) - e_{\mathrm{nat}}(t^2)
 = \sum_{k\ge1}\frac{(s^k - t^k)^2}{k(k+1)}
 \ \ge\ \frac{64}{81}(u-v)^2
 \ \ge\ \frac{64}{81}\cdot\frac{25}{256}\bigl(g(s)-g(t)\bigr)^2
 = \frac{25}{324}\bigl(g(s)-g(t)\bigr)^2,$$
and $\frac{25}{324} > \frac{\log 2}{9}$ because $\log 2 < \frac{25}{36}$ (Step 1b). Dividing
by $\log 2$ gives the base-2 form.

## Step 7. The diagonal estimate

**Claim (Lemma 4.2, `lem:diagonal`).** For all $0 < s \le 1$:
$$D(s) := \frac{9}{10}\,e_{\mathrm{nat}}(s^2) - C\,e_{\mathrm{nat}}(s) + \frac{\log 2}{10}\,g(s)^2 \ \ge\ 0,$$
equivalently (dividing by $\log 2$) $\frac{9}{10}e(s^2) + \frac{1}{10}g(s)^2 \ge C\,e(s)$.

Four ranges. Throughout, $e_{\mathrm{nat}} > 0$ on $(0,1)$ and $g^2 \ge 0$.

**(7a) $s = 1$:** $e_{\mathrm{nat}}(1) = 0$ and $g(1) = 0$, so $D(1) = 0$.

**(7b) Small $s$: $0 < s \le 10^{-6}$.** By (2b),
$e_{\mathrm{nat}}(s^2) \ge -\log(s^2) = 2(-\log s)$ (discarding the nonnegative second term)
and $e_{\mathrm{nat}}(s) \le -\log s + 1$. Hence, discarding $g^2 \ge 0$,
$$D(s) \ \ge\ \Bigl(\frac{9}{5} - C\Bigr)(-\log s) - C = \frac{8999}{50000}(-\log s) - \frac{81001}{50000} \ >\ 0,$$
because $-\log s \ge 6\log 10 > 12$ (Step 1b) and $\frac{8999}{50000}\cdot 12 = \frac{107988}{50000} > \frac{81001}{50000}$.

**(7c) Large $s$: $s = 1-\varepsilon$ with $0 < \varepsilon \le 10^{-6}$.** Put
$\delta = 1 - s^2 = \varepsilon(2-\varepsilon)$ and $L = \log(1/\varepsilon) > 12$
(from $\varepsilon \le 10^{-6}$ and $\log 10 > 2$). By symmetry
$H_{\mathrm{nat}}(s^2) = H_{\mathrm{nat}}(\delta)$ and $H_{\mathrm{nat}}(s) = H_{\mathrm{nat}}(\varepsilon)$, so with (2b):
$$\frac{e_{\mathrm{nat}}(s^2)}{e_{\mathrm{nat}}(s)}
 = \frac{H_{\mathrm{nat}}(\delta)}{s\,H_{\mathrm{nat}}(\varepsilon)}
 \ \ge\ \frac{2-\varepsilon}{1-\varepsilon}\cdot\frac{L - \log(2-\varepsilon) + 1 - \delta}{L + 1}
 \ \ge\ 2\,\frac{L + 3/10}{L + 1}
 \ >\ \frac{123}{65} \ >\ \frac{10}{9}\,C .$$
Justifications: $\log(1/\delta) = L - \log(2-\varepsilon)$; $\frac{2-\varepsilon}{1-\varepsilon} \ge 2$;
$1 - \delta - \log(2-\varepsilon) > 1 - \frac{1}{500000} - \frac{25}{36} > \frac{3}{10}$
(since $\delta = \varepsilon(2-\varepsilon) < 2\varepsilon \le 2\cdot 10^{-6} = \frac{1}{500000}$, and $\log(2-\varepsilon) \le \log 2 < \frac{25}{36}$);
$2\frac{L+3/10}{L+1} > \frac{123}{65} \iff 130(L + \tfrac{3}{10}) > 123(L+1) \iff 7L > 84 \iff L > 12$;
and $\frac{123}{65} > \frac{10}{9}C$ from Step 1. Hence
$\frac{9}{10}e_{\mathrm{nat}}(s^2) - C\,e_{\mathrm{nat}}(s) > 0$, and $\frac{\log2}{10}g^2 \ge 0$.

**(7d) Middle range: $10^{-6} \le s \le 1 - 10^{-6}$ — INTERVAL-ARITHMETIC OBLIGATION.**
Prove $D(s) > 0$ there. Note $g(s)^2 = 4(1-s)P(s)$ is a polynomial (Step 2i), so
$$D(s) = \frac{9}{10}\,e_{\mathrm{nat}}(s^2) - \frac{81001}{50000}\,e_{\mathrm{nat}}(s) + \frac{\log 2}{10}\cdot 4(1-s)P(s),$$
a combination of $\log s$, $\log(1-s)$, $\log(1-s^2)$, rational functions, and $\log 2$. The
paper certifies positivity by rational-midpoint bisection with 256-bit Arb balls: 29,701 box
evaluations, depth $\le 25$. **Warning: this is the tightest inequality in the proof** — the
true pointwise minimum of $D$ is $\approx 6.1\cdot10^{-5}$ (natural-log units) near
$s \approx 0.686$; the constant $C$ was optimized against this constraint. (The far smaller
recorded per-box certified lower bound $\approx 5.6\cdot10^{-9}$, on a box of width
$\approx 7.6\cdot10^{-6}$ near $s \approx 0.6745$, is ball-arithmetic slack, not analytic
slack.) The margin also decays toward the right endpoint, since $D(1) = 0$ (7a):
$D(1 - 10^{-6}) \approx 2\cdot10^{-6}$, and the hand argument (7c) takes over only past
$1 - 10^{-6}$. The formalization therefore needs subdivision fine enough to resolve a
$\sim 10^{-4}$ margin (with correspondingly tight $\log$ enclosures) near the interior
minimum, increasingly fine boxes approaching $s = 1 - 10^{-6}$, and can be much coarser
elsewhere. Strategy as in (5c): rational
bisection; on each box bound each monotone piece by its endpoint values, with certified
rational enclosures of the logarithms (artanh-series enclosures at rational points with
geometric tail bounds, or a verified interval tactic if available).

## Step 8. The pointwise inequality and the scalar inequality

**(8a) Decomposition identity.** For $0 < s, t \le 1$ define (all in natural-log units)
$$\Phi(s,t) := 2\Bigl[\frac{9}{10}\,e_{\mathrm{nat}}(st) + \frac{\log 2}{10}\,g(s)g(t)\Bigr] - C\bigl(e_{\mathrm{nat}}(s) + e_{\mathrm{nat}}(t)\bigr).$$
Then, **exactly** (a two-line ring computation, using $\frac{9}{10}\cdot\frac19 = \frac{1}{10}$):
$$\Phi(s,t) = D(s) + D(t)
 + \frac{9}{10}\Bigl[2e_{\mathrm{nat}}(st) - e_{\mathrm{nat}}(s^2) - e_{\mathrm{nat}}(t^2) - \frac{\log 2}{9}\bigl(g(s)-g(t)\bigr)^2\Bigr],$$
where $D$ is the diagonal slack of Step 7. By Step 7 ($D \ge 0$) and Step 6 (bracket
$\ge 0$): $\Phi(s,t) \ge 0$.

**(8b) Un-normalized pointwise form.** Multiplying $\Phi(s,t) \ge 0$ by $st > 0$ and using
$s\,e_{\mathrm{nat}}(s) = H_{\mathrm{nat}}(s)$: for $0 < s, t \le 1$,
$$2\Bigl[\frac{9}{10}\,H_{\mathrm{nat}}(st) + \frac{\log 2}{10}\,st\,g(s)g(t)\Bigr]
 \ \ge\ C\bigl(s\,H_{\mathrm{nat}}(t) + t\,H_{\mathrm{nat}}(s)\bigr).$$
For $s = 0$ or $t = 0$ both sides vanish ($H_{\mathrm{nat}}(0) = 0$), so this holds for
**all** $s, t \in [0,1]$.

**(8c) Scalar inequality (Proposition 4.1, `prop:scalar`), natural-log form.** Let $S$ be
a finitely supported random variable with values in $[0,1]$ and $T$ an independent copy.
Then
$$\frac{9}{10}\,\mathbb E\,H_{\mathrm{nat}}(ST) + \frac{\log 2}{10}\bigl(\mathbb E[S\,g(S)]\bigr)^2
 \ \ge\ C\;\mathbb E S \cdot \mathbb E\,H_{\mathrm{nat}}(S).$$
Proof: take the expectation of (8b) over independent $(S,T)$ and divide by 2. Use
$\mathbb E[ST\,g(S)g(T)] = \mathbb E[S g(S)]\,\mathbb E[T g(T)] = (\mathbb E[S g(S)])^2$ and
$\mathbb E[S\,H_{\mathrm{nat}}(T)] = \mathbb E S\cdot\mathbb E H_{\mathrm{nat}}(S)$ (independence,
identical distribution). Finite support makes all expectations finite `Finset` sums — state
it that way (e.g. for a probability weight function $w :$ `Finset`-supported $\to \mathbb Q_{\ge0}$
or over a `PMF` with finite support) to avoid integrability side conditions.

## Step 9. Finitary probabilistic setup: prefix entropies of the uniform member

From here on, fix the union-closed family $\mathcal F$, let $n = |\bigcup \mathcal F|$ and
identify members of $\mathcal F$ with vectors in $\{0,1\}^n$ (an injection
$\mathcal F \hookrightarrow \{0,1\}^n$ via indicator vectors on an enumeration of the ground
set; union of sets = coordinatewise max/or of vectors). Let $X = (X_1,\dots,X_n)$ be
**uniform on $\mathcal F$** (a finitely supported distribution with rational point masses
$1/|\mathcal F|$).

Definitions (all finite sums; "supported prefix" means positive probability):
- For $1 \le i \le n$ and a prefix $v \in \{0,1\}^{i-1}$ with $\Pr(X_{<i} = v) > 0$:
  $$p_i(v) = \Pr(X_i = 0 \mid X_{<i} = v) \in [0,1] \cap \mathbb Q .$$
- $S_i = p_i(X_{<i})$, a $[0,1]$-valued finitely supported random variable;
  $\mathbb E\,\phi(S_i) = \sum_{v} \Pr(X_{<i}=v)\,\phi(p_i(v))$ over supported prefixes $v$.
- $H_i = \mathbb E\,H_{\mathrm{nat}}(S_i) = H_{\mathrm{nat}}(X_i \mid X_{<i})$
  (conditional entropy as the average over supported prefixes of the binary entropy of the
  conditional bit).

Prove the standard facts (finite chain-rule computations):
- **(9a) Chain rule / total entropy.** $H_{\mathrm{nat}}(X) = \sum_{i=1}^n H_i = \log|\mathcal F|$.
- **(9b) Frequency identity.** $\Pr(X_i = 1) = 1 - \mathbb E S_i$, and
  $\Pr(X_i = 1) = |\{A \in \mathcal F : x_i \in A\}| / |\mathcal F|$ is exactly the frequency of the
  $i$-th ground element.
- **(9c) Maximum entropy.** If $Z$ is any random variable supported on (a subset of)
  $\mathcal F$, then $H_{\mathrm{nat}}(Z) \le \log|\mathcal F|$ (Gibbs / Jensen for the finite
  uniform distribution).
- **(9d) Conditioning reduces entropy.** For finitely supported $(A, W)$ and any function
  $f$: $H_{\mathrm{nat}}(A \mid f(W)) \ge H_{\mathrm{nat}}(A \mid W)$, and the chain rule
  $H_{\mathrm{nat}}(Z) = \sum_i H_{\mathrm{nat}}(Z_i \mid Z_{<i})$ for a random vector $Z$.
  (Concavity of $x \mapsto -x\log x$ / Jensen; all sums finite.)

*Formalization notes.* Check whether Mathlib's information-theory development (the
PFR-derived entropy API, `ProbabilityTheory` entropy of random variables) is usable here; if
its measure-theoretic framing is heavier than helpful, an entirely self-contained finitary
development over `Finset`-weighted sums is perfectly feasible and keeps every probability
rational. The only analytic ingredient is concavity of $x\mapsto -x\log x$ on $[0,1]$.

## Step 10. The independent coupling: $H_{\mathrm{nat}}(Z_{\mathrm{ind}}) \ge \sum_i \mathbb E\,H_{\mathrm{nat}}(S_i T_i)$

Let $X', Y'$ be independent copies of $X$ and $Z_{\mathrm{ind}} = X' \vee Y'$
(coordinatewise or). **Union-closedness gives $Z_{\mathrm{ind}} \in \mathcal F$ always.** Set
$S_i = p_i(X'_{<i})$, $T_i = p_i(Y'_{<i})$; for each fixed $i$ these are independent copies
of $p_i(X_{<i})$.

Prove:
$$H_{\mathrm{nat}}(Z_{\mathrm{ind}})
 = \sum_{i=1}^n H_{\mathrm{nat}}\bigl((Z_{\mathrm{ind}})_i \mid (Z_{\mathrm{ind}})_{<i}\bigr)
 \ \ge\ \sum_{i=1}^n H_{\mathrm{nat}}\bigl((Z_{\mathrm{ind}})_i \mid X'_{<i}, Y'_{<i}\bigr)
 = \sum_{i=1}^n \mathbb E\,H_{\mathrm{nat}}(S_i\,T_i).$$
- First equality: chain rule (9d).
- Inequality: $(Z_{\mathrm{ind}})_{<i} = X'_{<i} \vee Y'_{<i}$ is a function of the pair
  $(X'_{<i}, Y'_{<i})$, so conditioning on the pair conditions on at least as much (9d).
- Last equality: given $X'_{<i} = v$, $Y'_{<i} = w$ (supported), the bits $X'_i, Y'_i$ are
  independent with zero-probabilities $p_i(v), p_i(w)$; the union bit is $0$ iff both are
  $0$, so its conditional zero-probability is $p_i(v)\,p_i(w)$, and its conditional entropy
  is $H_{\mathrm{nat}}(p_i(v) p_i(w))$. Average over $(v,w)$.

## Step 11. The shared-sign coupling: $H_{\mathrm{nat}}(Z_{\mathrm{sh}}) \ge (\log 2)\sum_i \bigl(\mathbb E[S_i\,g(S_i)]\bigr)^2$

**(11a) Construction.** Let $U = (U_1,\dots,U_n)$ be i.i.d. uniform signs in $\{\pm 1\}$.
Conditional on the full sign vector $U = u$, let $\widetilde X$ and $\widetilde Y$ be
**i.i.d.**, each generated coordinate-by-coordinate by the *modified* transition rule: from a
supported prefix $v$ (supported for the original $X$), with $s = p_i(v)$, the next bit is $0$
with probability
$$s + u_i\,\lambda\, s(1-s) \qquad (\lambda = 9/10),$$
which lies in $[0,1]$ by the factor bounds of Step 3a. Concretely, define the joint finitely
supported distribution of $(U, \widetilde X, \widetilde Y)$ by the explicit product formula:
for $u \in \{\pm1\}^n$ and $x, y$ in the support,
$$\Pr(U=u,\ \widetilde X = x,\ \widetilde Y = y) = 2^{-n} \prod_{i=1}^n \pi_i(x_{<i}, x_i; u_i)\,\prod_{i=1}^n \pi_i(y_{<i}, y_i; u_i),$$
where $\pi_i(v, 0; \sigma) = p_i(v) + \sigma\lambda p_i(v)(1-p_i(v))$ and
$\pi_i(v, 1; \sigma) = 1 - \pi_i(v, 0;\sigma)$. Transitions with $p_i(v) \in \{0,1\}$ are
unchanged, so $\widetilde X, \widetilde Y$ never leave the support of $X$ — in particular
they take values in $\mathcal F$, and (union-closedness) $Z_{\mathrm{sh}} := \widetilde X \vee \widetilde Y \in \mathcal F$.

**(11b) Marginal uniformity.** $\widetilde X$ (and likewise $\widetilde Y$) is marginally
uniform on $\mathcal F$. Proof: for a fixed $x$, average the product formula over
$u \in \{\pm1\}^n$; the factors for distinct coordinates involve distinct independent signs,
so the average factorizes, and $\tfrac12[\pi_i(v,b;+1) + \pi_i(v,b;-1)] = \Pr(X_i = b \mid X_{<i}=v)$
for each $b$. Induction on prefix length (or direct product manipulation) gives
$\Pr(\widetilde X = x) = \Pr(X = x)$. Consequently $S_i := p_i(\widetilde X_{<i})$ has the
same distribution as $p_i(X_{<i})$, and $T_i := p_i(\widetilde Y_{<i})$ likewise.

**(11c) Entropy lower bound via the kernel $q$.** Writing $U_{<i} = (U_1,\dots,U_{i-1})$:
$$H_{\mathrm{nat}}(Z_{\mathrm{sh}})
 \ \ge\ \sum_{i=1}^n H_{\mathrm{nat}}\bigl((Z_{\mathrm{sh}})_i \mid \widetilde X_{<i}, \widetilde Y_{<i}, U_{<i}\bigr)
 = \sum_{i=1}^n \mathbb E\,H_{\mathrm{nat}}\bigl(q(S_i, T_i)\bigr).$$
The inequality is chain rule + conditioning-on-more (9d), since $(Z_{\mathrm{sh}})_{<i}$ is a
function of $(\widetilde X_{<i}, \widetilde Y_{<i})$. For the equality: condition on
$(\widetilde X_{<i}, \widetilde Y_{<i}, U_{<i}) = (v, w, u_{<i})$; the fresh sign $U_i$ is
uniform and independent of this conditioning; given also $U_i = \sigma$, the two current
bits are independent with zero-probabilities $s + \sigma\lambda s(1-s)$ and
$t + \sigma\lambda t(1-t)$ where $s = p_i(v)$, $t = p_i(w)$; averaging the product over
$\sigma = \pm1$ gives the both-zero probability — this is **exactly the sign-average
identity (3a)** — namely $q(s,t) = st(1 + \lambda^2(1-s)(1-t))$. The union bit is $0$ iff
both bits are $0$.

**(11d) Rank-one bound, conditional i.i.d. structure, and Jensen.** By Step 3e applied
pointwise inside the expectation:
$$\mathbb E\,H_{\mathrm{nat}}\bigl(q(S_i,T_i)\bigr) \ \ge\ (\log 2)\;\mathbb E\bigl[S_i g(S_i)\; T_i g(T_i)\bigr].$$
Conditional on $U_{<i}$, the prefixes $\widetilde X_{<i}$ and $\widetilde Y_{<i}$ are i.i.d.
(the product formula factorizes given the signs), hence so are $S_i$ and $T_i$; therefore
$$\mathbb E\bigl[S_i g(S_i)\,T_i g(T_i) \mid U_{<i}\bigr] = \bigl(\mathbb E[S_i g(S_i) \mid U_{<i}]\bigr)^2 .$$
Taking the expectation over $U_{<i}$ and applying Jensen ($\mathbb E[W^2] \ge (\mathbb E W)^2$,
i.e. nonnegativity of variance, a finite-sum Cauchy–Schwarz) with the tower property
$\mathbb E\bigl[\mathbb E[S_i g(S_i) \mid U_{<i}]\bigr] = \mathbb E[S_i g(S_i)]$:
$$\mathbb E\bigl[S_i g(S_i)\,T_i g(T_i)\bigr] \ \ge\ \bigl(\mathbb E[S_i g(S_i)]\bigr)^2 .$$
By (11b), $\mathbb E[S_i g(S_i)]$ here equals the same expectation computed for the original
chain, $\mathbb E[p_i(X_{<i})\,g(p_i(X_{<i}))]$. Combining:
$$H_{\mathrm{nat}}(Z_{\mathrm{sh}}) \ \ge\ (\log 2)\sum_{i=1}^n \bigl(\mathbb E[S_i\,g(S_i)]\bigr)^2 .$$

## Step 12. Assembly: the contradiction

Assume, for contradiction, that **every** element has frequency $\le c = 1196/3125$, i.e.
$\Pr(X_i = 1) \le c$ for every $i$. By (9b), $\mathbb E S_i \ge 1 - c$ for every $i$.

Both $Z_{\mathrm{ind}}$ and $Z_{\mathrm{sh}}$ take values in $\mathcal F$
(union-closedness, Steps 10, 11a), so by maximum entropy (9c):
$H_{\mathrm{nat}}(Z_{\mathrm{ind}}) \le H_{\mathrm{nat}}(X)$ and
$H_{\mathrm{nat}}(Z_{\mathrm{sh}}) \le H_{\mathrm{nat}}(X)$. Therefore
$$H_{\mathrm{nat}}(X) \ \ge\ \frac{9}{10}H_{\mathrm{nat}}(Z_{\mathrm{ind}}) + \frac{1}{10}H_{\mathrm{nat}}(Z_{\mathrm{sh}})
 \ \ge\ \sum_{i=1}^n \Bigl[\frac{9}{10}\,\mathbb E\,H_{\mathrm{nat}}(S_i T_i) + \frac{\log 2}{10}\bigl(\mathbb E[S_i g(S_i)]\bigr)^2\Bigr],$$
using Steps 10 and 11 (note the $\log 2$ placement matches the natural-log scalar
inequality). For each $i$, apply the scalar inequality (8c) with $S = S_i$ (finitely
supported, values in $[0,1]$; in Step 10's bound $T_i$ is an independent copy of $S_i$,
exactly as (8c) requires), then $\mathbb E S_i \ge 1-c$:
$$\frac{9}{10}\,\mathbb E\,H_{\mathrm{nat}}(S_i T_i) + \frac{\log 2}{10}\bigl(\mathbb E[S_i g(S_i)]\bigr)^2
 \ \ge\ C\,\mathbb E S_i\cdot \mathbb E H_{\mathrm{nat}}(S_i) \ =\ C\,\mathbb E S_i\, H_i \ \ge\ C(1-c)\,H_i .$$
Summing over $i$ and using the chain rule (9a):
$$H_{\mathrm{nat}}(X) \ \ge\ C(1-c) \sum_{i=1}^n H_i = C(1-c)\,H_{\mathrm{nat}}(X)
 = \Bigl(1 + \frac{929}{156250000}\Bigr) H_{\mathrm{nat}}(X).$$
Since $H_{\mathrm{nat}}(X) = \log|\mathcal F| \ge 0$, this forces $H_{\mathrm{nat}}(X) = 0$,
i.e. $|\mathcal F| = 1$. So $\mathcal F = \{A\}$ for a single set $A$; the hypothesis
$\mathcal F \ne \{\varnothing\}$ gives $A \ne \varnothing$, and then any $x \in A$ has
frequency $1 > c$ — contradicting the assumption that every frequency is $\le c$.

Hence some element $x$ has frequency $> c$; in particular
$3125\,|\{A \in \mathcal F : x \in A\}| \ge 1196\,|\mathcal F|$. $\blacksquare$

*(Edge cases absorbed above: if $\mathcal F$ is a singleton the assembly's contradiction
already appears at the last paragraph without any entropy; if the ground set is empty then
$\mathcal F \subseteq \{\varnothing\}$ and the hypotheses force a contradiction directly.
A formalization may prefer to dispatch $|\mathcal F| = 1$ as a separate case first, then
assume $|\mathcal F| \ge 2$, i.e. $H_{\mathrm{nat}}(X) > 0$, throughout Steps 9–12.)*

---

# Conclusion

Assembling Steps 1–12: for every finite union-closed family
$\mathcal F \notin \{\varnothing, \{\varnothing\}\}$, some ground element belongs to at least
$1196/3125 = 0.38272$ of the members of $\mathcal F$. The headline frozen theorem certifies
exactly this:
`∀ F : Finset (Finset α), UnionClosed F → F.Nonempty → F ≠ {∅} → ∃ x, 1196 * F.card ≤ 3125 * (F.filter (fun A => x ∈ A)).card`.

The load-bearing components are: the rank-one product bound
$h(q(s,t)) \ge st\,g(s)g(t)$ (Step 3, exact Bernstein certificate with 25 explicit rational
coefficients, min $31387/40000$); the profile speed bound $|g(s)-g(t)| \le \frac{16}{5}|u-v|$
(Step 4, exact Bernstein certificate with 22 explicit rational coefficients, min
$2530002779/840000000$); the entropy speed bound
$\bigl(\sum(s^k-t^k)^2/(k(k+1))\bigr)^{1/2} \ge \frac89|u-v|$ (Step 5, elementary at the
ends, one finite interval-arithmetic cover in the middle); the diagonal estimate
$\frac{9}{10}e(s^2) + \frac{1}{10}g(s)^2 \ge C e(s)$ (Step 7, elementary at the ends, one
finite interval-arithmetic cover in the middle, nearly tight near $s \approx 0.6745$); their
combination into the scalar inequality via an exact algebraic decomposition (Step 8); and
the two entropy couplings (Steps 10–11) whose mixture beats $H(X)$ by the strict factor
$C(1-c) = 1 + 929/156250000$ unless some element has frequency exceeding $1196/3125$
(Step 12). The two interval-arithmetic obligations (5c) and (7d) are the only steps that are
not either finite exact-rational algebra or short elementary analysis; both are
one-dimensional, over explicitly stated rational ranges, with all needed monotonicity and
series tools provided in Step 2.
