# Blueprint: an entropy bound of 1196/3125 = 0.38272 for union-closed families

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
The proof is Gilmer-style entropy compression sharpened by a *shared-sign*
coupling. Fix a finite union-closed family `F`, let `X` be uniform on `F` viewed
as a subset of the Boolean cube, and build two couplings whose coordinatewise
`or` again lands in `F`: the **independent** one `X' ∨ Y'` and the **shared-sign**
one `X̃ ∨ Ỹ`, where the two chains are conditionally i.i.d. given a common random
sign vector that perturbs each conditional zero-probability `s` to
`s ± λ s(1-s)` with `λ = 9/10`. Maximum entropy caps both couplings by
`H(X) = log|F|`; the `9/10 : 1/10` mixture of the two lower bounds is controlled
by a single **two-variable scalar entropy inequality**, which splits into a
diagonal estimate and an off-diagonal estimate. If every element had frequency
`≤ c = 1196/3125` the mixture would force `H(X) ≥ C(1-c) H(X)` with
`C(1-c) = 1 + 929/156250000 > 1`, hence `H(X) = 0`, hence `|F| = 1`, which the
hypothesis `F ≠ {∅}` contradicts.

- **Headline target (frozen theorem `frankl_038272`).** For every
  `F : Finset (Finset α)` over a `DecidableEq` type with `UnionClosed F`,
  `F.Nonempty` and `F ≠ {∅}`, there is `x : α` with
  `1196 * F.card ≤ 3125 * (F.filter (fun A => x ∈ A)).card`.
  The predicate `UnionClosed` is frozen in `Defs.lean`; the headline is
  transported from its cube form, the companion frozen theorem `frankl_cube`,
  which states the same conclusion for `G : Finset (Fin n → Bool)` under
  `UnionClosedCube G`. Both are frozen on their own: `frankl_cube` is where the
  entropy argument lives, `frankl_038272` is the statement a reader cites.
- **Recommended intermediate milestone (prove first):** the **scalar inequality**
  `scalar_inequality` (Step 8c) — for any finitely supported `[0,1]`-valued `S`
  with an independent copy `T`,
  `C · E S · E H(S) ≤ (9/10) E H(S T) + (log 2 / 10) (E[S g(S)])²`.
  It is the mathematical heart: everything before it (Steps 1–8) is real analysis
  on `[0,1]`, everything after it (Steps 9–12) is bookkeeping with finite sums.
  Once it is proved, the probabilistic assembly is routine chain-rule work; and
  the inequality is citable on its own.
- **Setting / ground assumptions:** real analysis over `ℝ` (`Real.log`,
  `Real.sqrt`, `tsum` over `ℕ`, `HasDerivAt`, MVT) plus **finite** probability —
  every distribution in Steps 9–12 is a nonnegative weight function on a
  `Fintype` summing to `1`, every expectation is a `Finset.sum`. Explicitly *not*
  involved: measure theory, `MeasureTheory.Integral`, `ProbabilityTheory`'s
  measure-theoretic entropy, `PMF`, infinite families, any floating point. All
  numeric constants are exact rationals.

> **Why this is tractable.** Steps 1–4 and 6–8 are *finite exact rational
> algebra*: two Bernstein certificates (25 and 22 explicit positive rationals)
> reduce two polynomial positivity claims to `norm_num`, and the assembly
> identity of Step 8a is a `ring` computation. Steps 9–12 need no analysis beyond
> concavity of `x ↦ -x log x`; modelled over `Fin n → Bool` with `Finset` sums
> they are elementary. The real risk is threefold. (i) **Two genuine
> interval-arithmetic obligations** — `Ader_lower_middle` (5c) and
> `diagonal_middle` (7d) — are finite but expensive; `diagonal_middle` is the
> *tightest inequality in the whole proof* (true minimum ≈ 6.1·10⁻⁵ near
> `s ≈ 0.686`) and a coarse cover will simply fail. (ii) **Mis-modeling the
> shared-sign coupling**: if `X̃` and `Ỹ` are not conditionally i.i.d. *given the
> full sign vector*, Step 11d's `E[W²] ≥ (E W)²` collapses and the whole gain
> disappears. (iii) **Over-reach**: assuming `H(X) > 0`, assuming the family has a
> nonempty member, or quietly restricting to `n ≥ 1`, each of which turns the
> headline into a weaker theorem. There is no deep mathematics here — only
> exactness.

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is to produce a compiling skeleton in which **every
`Definition` and every `Theorem` statement is written and frozen**, with all
proofs `:= sorry`. Once frozen, `Defs.lean` and `Theorems.lean` are **never
edited again** during the proving phase. Everything proved later lives in
support files and may not change a single character of the frozen statements.

### 1. Create the Lean project

```bash
cd /Users/siyua/dev/opensource-validation-runs/EntropyBound-refactors
lake +leanprover/lean4:v4.31.0 new EntropyBound math   # toolchain pinned in lean-toolchain
# pin Mathlib in lakefile + lake-manifest to the rev matching v4.31.0, then:
lake exe cache get
lake build            # must succeed on the bare skeleton before anything else
```

If `lake new … math` scaffolds into a nested directory, flatten it so that the
source directory `EntropyBound/` sits at the repo root next to `SKETCH.md`.
Record the exact `lean-toolchain` string and the exact Mathlib rev from
`lake-manifest.json` in the first `PROGRESS.md` entry — later agents must not
bump either.

Layout (every project follows this shape):

```
EntropyBound-refactors/
  EntropyBound/
    Defs.lean          -- FROZEN after this stage: every object the proof needs
    Theorems.lean      -- FROZEN after this stage: the frozen theorem statements (sorry)
    Proofs/
      Constants/       -- Stage A: exact rational constants + numeric log bounds (Step 1)
      Toolbox/         -- Stage B: binary-entropy / series / polynomial toolbox (Step 2)
      RankOne/         -- Stage C: rank-one product bound h(q(s,t)) ≥ s t g(s) g(t) (Step 3)
      ProfileSpeed/    -- Stage D: |g(s) - g(t)| ≤ (16/5)|u - v| (Step 4)
      EntropySpeed/    -- Stage E: A'(u) ≥ 8/9 and the ℓ² speed bound (Step 5)
      OffDiagonal/     -- Stage F: the off-diagonal estimate (Step 6)
      Diagonal/        -- Stage G: the diagonal estimate D(s) ≥ 0 (Step 7)
      Scalar/          -- Stage H: decomposition + pointwise + scalar inequality (Step 8)
      FiniteEntropy/   -- Stage I: finitary entropy toolbox, chain rule, max entropy (Step 9)
      IndepCoupling/   -- Stage J: the independent coupling bound (Step 10)
      SharedCoupling/  -- Stage K: the shared-sign coupling bound (Step 11)
      Assembly/        -- Stage L: the contradiction and the headline (Step 12)
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `EntropyBound.Solution`, proven (clean names)
  EntropyBound.lean    -- imports everything
  SKETCH.md            -- the problem + NL proof sketch (math source of truth)
  BLUEPRINT.md         -- this file
  USER_NOTES.md        -- user's special instructions / permitted assumed-axioms
  PROGRESS.md          -- append-only work log (workers write here; see §4)
  TASKS.md             -- append-only delegation log (the Plan agent writes here; see §5)
  REVIEW.md            -- append-only audit log (the Review agent writes here; see §5)
  scripts/
    verify.py          -- the verification harness
    harness.json       -- project / problem / frozen-theorem-name configuration
    frozen.sha256      -- SHA-256 pins of Defs.lean + Theorems.lean
    ALLOWED_AXIOMS.txt -- axiom allowlist init.py derives from USER_NOTES.md
```

All support declarations live in `namespace EntropyBound` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface;
`Solution.lean` re-exposes each as `EntropyBound.Solution.<name>` after it is
proven, and `Discharge.lean` machine-checks that each proof has *exactly* the
frozen type (`@Frozen = @Proof := rfl`).

`USER_NOTES.md` for this problem says **"None — no assumed axioms."** So
`scripts/ALLOWED_AXIOMS.txt` is empty, no `axiom` declaration may appear
anywhere in the project, and every solved theorem must print exactly
`{propext, Classical.choice, Quot.sound}` (or a subset). In particular **the two
interval-arithmetic obligations (5c) and (7d) must be genuinely proved**, not
assumed.

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.** For each
definition record the Lean rendering and the **MODELING DECISION**.

Everything below lives in `namespace EntropyBound`. Ordering: combinatorics →
constants → scalar analysis → certificate data → finitary probability.

#### Combinatorics

- **`UnionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=`**
  `∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F`.
  *MODELING DECISION.* The textbook predicate verbatim, over an arbitrary
  `DecidableEq` type, **not** over `ℕ` and **not** with `Finset.sup`/closure
  surrogates. `α` is arbitrary (no `Fintype α`): the ground set is finite
  automatically because `F` is a `Finset` of `Finset`s. Rejected: bundling `F`
  with a `Fintype α` instance (an added hypothesis, forbidden); rejected:
  `∀ A B ∈ F, A ∪ B ∈ F` phrased as a closure of a lattice (needs order API for
  no gain).

- **`orVec {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool := fun i => x i || y i`**.
  *MODELING DECISION.* The union on the cube is coordinatewise `||` on `Bool`,
  not `⊔` on `Prop` or on `Fin n → Prop`. `Bool` keeps every intermediate
  `DecidableEq` + `Fintype` and keeps `unifW`, `pcond`, `wsh` computable-shaped.

- **`UnionClosedCube {n : ℕ} (G : Finset (Fin n → Bool)) : Prop :=`**
  `∀ x ∈ G, ∀ y ∈ G, orVec x y ∈ G`.
  *MODELING DECISION.* The cube-side mirror of `UnionClosed`. The transfer
  `Finset (Finset α) → Finset (Fin n → Bool)` is **not** frozen as a definition;
  it is built inside Stage L as support code, so a mis-built transfer can never
  silently weaken a frozen statement — the frozen cube statement and the frozen
  set statement are each independently faithful.

- **`pref {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin n → Bool :=`**
  `fun j => if (j : ℕ) < i then x j else false`.
  *MODELING DECISION.* Prefixes are represented as **masked full vectors**, not
  as `Fin i → Bool`. This avoids all dependent-type transport when `i` varies in
  a `∑ i : Fin n` and makes `pref i` literally a function of `x`, which is
  exactly what "conditioning on a function of the data" (9d) needs.

#### Exact rational constants (as reals)

- **`cval : ℝ := 1196 / 3125`** — the headline frequency constant `c`.
- **`Cval : ℝ := 81001 / 50000`** — the scalar-inequality constant `C`.
- **`lam  : ℝ := 9 / 10`** — the coupling strength `λ`.
  *MODELING DECISION.* Constants are `ℝ`-valued rational literals, never
  `Float`, never `Rat`-coerced-late. `norm_num` closes every arithmetic fact
  about them. `β = 1/10` is **not** given a name: it appears only as the literal
  weight `1/10` next to `9/10`, and naming it would invite a later agent to
  "tune" it.

#### Scalar analysis: entropy, kernel, profile

- **`Hnat (z : ℝ) : ℝ := -z * Real.log z - (1 - z) * Real.log (1 - z)`**.
  *MODELING DECISION.* We define natural-log binary entropy **directly from
  `Real.log`** rather than `abbrev Hnat := Real.binEntropy`. Reason: the frozen
  file must not depend on the exact spelling/availability of Mathlib's
  `Real.binEntropy` in the pinned rev, and `Real.log 0 = 0` in Mathlib already
  gives the junk-value convention `0 log 0 = 0`, so `Hnat 0 = Hnat 1 = 0`
  definitionally-after-`simp`. A **support** lemma `Hnat_eq_binEntropy :`
  `Hnat = Real.binEntropy` is proved once in `Proofs/Toolbox/` to import
  Mathlib's derivative/concavity API. Rejected: `Real.negMulLog`-based spelling
  (equivalent, but one more name to depend on).
- **`enat (s : ℝ) : ℝ := Hnat s / s`**.
  *MODELING DECISION.* Total function; `enat 0 = 0` by Lean's `x / 0 = 0`. Every
  frozen statement about `enat` carries `0 < s` explicitly, so the junk value is
  never load-bearing.
- **`qker (s t : ℝ) : ℝ := s * t * (1 + (81/100) * (1 - s) * (1 - t))`** — the
  coupling kernel `q(s,t)`. Written with the literal `81/100 = λ²`, so `ring`
  sees a polynomial.
- **`gprof (s : ℝ) : ℝ :=`**
  `2 * Real.sqrt ((1 + (81/100)*(1-s)^2) * (1 - s^2 * (1 + (81/100)*(1-s)^2)))`
  — the coupling profile `g(s)`.
  *MODELING DECISION.* Defined by the square root of the *product form* exactly
  as in `SKETCH.md`, not by `2*Real.sqrt ((1-s) * Ppoly s)`. The factorization
  `gprof s ^ 2 = 4 * (1-s) * Ppoly s` is then a **theorem**
  (`gprofile_sq_eq`), which is the honest direction: it forces someone to prove
  the algebraic identity instead of defining the answer.

#### Series objects (all `tsum` over `ℕ`, reindexed to start at `0`)

- **`fser (z : ℝ) : ℝ := ∑' m : ℕ, z ^ (m+1) / ((m+1) * (m+2))`**   — `f(z) = Σ_{k≥1} zᵏ/(k(k+1))`.
- **`Qser (z : ℝ) : ℝ := ∑' j : ℕ, z ^ (2*j) / ((j+1) * (2*j+1))`**  — `Q(z)`.
- **`Qder (z : ℝ) : ℝ := ∑' m : ℕ, (2*(m+1)) * z ^ (2*m+1) / ((m+2) * (2*m+3))`** — the termwise derivative `Q'(z)`.
- **`Aser (u : ℝ) : ℝ := Real.sqrt (∑' m : ℕ, (1 - (1 - u^2) ^ (m+1))^2 / ((m+1) * (m+2)))`** — `A(u)`.
  *MODELING DECISION.* `Q` is **defined by its series**, not by the closed form
  `((1+z)log(1+z)+(1-z)log(1-z))/z²`. The series is the numerically stable and
  boundary-safe object (`Qser 0 = 1`, `Qser 1 = 2 log 2` come out right, and
  Step 5a/5c explicitly need the series near `z ≈ 0` where the closed form has
  catastrophic cancellation). The closed form is the theorem
  `Qser_closed_form`. Likewise `Qder` is defined as the termwise series and
  `Qser_hasDerivAt` is the theorem that it really is `Q'`. Reindexing:
  every sum starts at `m = 0`; the `+1`/`+2` shifts in the denominators are part
  of the frozen text and must not be "simplified" later.
  All four series have nonnegative terms dominated by `1/((m+1)(m+2))`, whose
  telescoping sum is `1`; summability is therefore a one-line comparison.

#### Certificate polynomials and Bernstein data

- **`Ppoly (z : ℝ) : ℝ := (1 + (81/100)*(1-z)^2) * (1 + z - (81/100)*z^2*(1-z))`**.
  *MODELING DECISION.* Defined in **factored** form (both factors are visibly
  `≥ 1` on `[0,1]`, so `Ppoly_pos` is easy); the power basis
  `181/100 + 19/100 z - 22761/10000 z² + 35883/10000 z³ - 19683/10000 z⁴ + 6561/10000 z⁵`
  is recovered by `ring_nf`/`norm_num` when needed.
- **`Npoly (z : ℝ) : ℝ :=`**
  `81/50 + (24661/5000)*z - (43983/2500)*z^2 + (27783/1250)*z^3 - (6561/500)*z^4 + (19683/5000)*z^5`.
  *MODELING DECISION.* Defined by the **explicit power basis from `SKETCH.md`
  (4a)**, *not* as `Ppoly z - (1-z) * deriv Ppoly z`. Reason: as a literal
  polynomial it is `ring`/`norm_num`-friendly and `Gpoly` stays a polynomial.
  The link to the derivative is the frozen theorem `Npoly_eq_deriv_form`; that
  is where the transcription of the sketch's coefficients is *checked*, so a typo
  cannot survive.
- **`Gpoly (z : ℝ) : ℝ := 64 * Ppoly z - 25 * (Npoly z)^2`** (degree 10).
- **`bern (m k : ℕ) (x : ℝ) : ℝ := (m.choose k : ℝ) * x^k * (1-x)^(m-k)`**.
  *MODELING DECISION.* Our own Bernstein basis over `ℝ` with `ℕ`-subtraction in
  the exponent (safe: only used with `k ≤ m`). Rejected: Mathlib's
  `bernsteinPolynomial` (lives in `ℤ[X]`/`Polynomial`, would force
  `Polynomial.eval` plumbing for no benefit).
- **`cR : ℕ → ℕ → ℝ`** — the 5×5 symmetric Bernstein coefficient matrix of
  Step 3d, written out by `match` on `(k, ℓ)` with the 25 exact rationals
  (`5119741/1000000, 24661/10000, 14887/10000, 1, 1; 9744659/8000000, 36787/40000,
  319/400, 1; 3191251/4000000, 31387/40000, 1; 319/400, 1; 1` on and above the
  diagonal, mirrored below), `0` outside `[0,4]²`.
- **`Rpoly (s t : ℝ) : ℝ :=`**
  `∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, cR k l * bern 4 k s * bern 4 l t`.
  *MODELING DECISION (important).* `R` is **defined by its Bernstein expansion**,
  following the explicit advice in `SKETCH.md` (3d). Then positivity
  (`Rpoly_lower_bound`) is free from `bern ≥ 0` and `∑ₖ bern 4 k x = 1`, and the
  power-basis table of (3c) becomes the frozen *cross-check*
  `Rpoly_power_basis`. Rejected: defining `R` by the power basis and proving
  positivity — that would require re-deriving the Bernstein identity as a
  25-term `ring` obligation with a much larger normal form.
- **`bGl : ℕ → ℝ`** and **`bGr : ℕ → ℝ`** — the two degree-10 Bernstein
  coefficient vectors `b` and `b'` of Step 4b, by `match` on `k ∈ [0,10]`, `0`
  outside. Exact rationals as printed in `SKETCH.md`; `bGl 10 = bGr 0 =
  30120271679/1024000000` (the shared midpoint value) is a useful transcription
  check.

#### Step 7/8 scalar functions

- **`Dfun (s : ℝ) : ℝ := (9/10) * enat (s^2) - Cval * enat s + (Real.log 2 / 10) * (gprof s)^2`** — the diagonal slack `D(s)`.
- **`Phi (s t : ℝ) : ℝ := 2 * ((9/10) * enat (s*t) + (Real.log 2 / 10) * (gprof s * gprof t)) - Cval * (enat s + enat t)`** — `Φ(s,t)`.
  *MODELING DECISION.* Both are in **natural-log units** throughout the project
  (`SKETCH.md` sanctions this explicitly). The base-2 forms `h`, `e` never
  appear; every `log 2` in a frozen statement is the conversion factor written
  out. Mixing the two conventions is the single easiest way to produce a
  statement that is off by `log 2` and still "looks right".

#### Finitary probability

Everything is a nonnegative weight function on a `Fintype` summing to `1`. There
is **no** `PMF`, no measure, no `ℝ≥0∞`.

- **`entropyW {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ := ∑ i, -(w i) * Real.log (w i)`**.
- **`law {ι β : Type*} [Fintype ι] [DecidableEq β] (w : ι → ℝ) (Z : ι → β) : β → ℝ :=`**
  `fun b => ∑ i, if Z i = b then w i else 0`.
- **`Hrv {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β] (w : ι → ℝ) (Z : ι → β) : ℝ := entropyW (law w Z)`**.
- **`condHrv (w : ι → ℝ) (Z : ι → β) (W : ι → γ) : ℝ := Hrv w (fun i => (Z i, W i)) - Hrv w W`**
  (with the obvious `Fintype`/`DecidableEq` instances on `β`, `γ`).
  *MODELING DECISION.* Random variables are **functions out of a finite index
  type** carrying a weight vector, and entropy is the entropy of the pushforward
  `law`. Conditional entropy is *defined* as the difference `H(Z,W) - H(W)`, so
  the pair chain rule is definitional and the content sits in
  `condHrv_le_of_comp` (9d). Rejected: Mathlib's `ProbabilityTheory` /
  PFR-derived `measureEntropy` — its measure-theoretic framing would force
  `Measure`, `IsProbabilityMeasure`, and `Measurable` side conditions on every
  one of Steps 9–12 for zero mathematical gain here. This decision is binding:
  no stage may re-introduce a measure-theoretic entropy.
- **`unifW {n : ℕ} (G : Finset (Fin n → Bool)) : (Fin n → Bool) → ℝ :=`**
  `fun x => if x ∈ G then 1 / (G.card : ℝ) else 0` — `X` uniform on `G`, as a
  weight vector on the **whole cube** (not on the subtype `↥G`).
  *MODELING DECISION.* Indexing by the whole cube makes `X`, `X'`, `Y'`, `X̃`,
  `Ỹ` all live on the same index type, so products and `orVec` need no coercion.
- **`pcond {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) : ℝ :=`**
  the conditional probability that coordinate `i` is `false`, given that the
  prefix agrees with `v`:
  `let A := G.filter (fun x => pref i.val x = pref i.val v);`
  `let B := A.filter (fun x => x i = false);`
  `if A.card = 0 then 0 else (B.card : ℝ) / (A.card : ℝ)`.
  *MODELING DECISION.* `p_i(v)` is a **total** function of a full vector `v`
  that only reads `pref i v`; unsupported prefixes get the junk value `0`, and
  every frozen statement quantifies in a way that only ever evaluates it on
  supported prefixes (because it is always weighted by `unifW`). This is what
  makes `S i = pcond G i` literally "a function of the prefix", which is what
  Steps 10/11 condition on.
- **`HiFun (G) (i) : ℝ := ∑ x, unifW G x * Hnat (pcond G i x)`** — `H_i`.
- **`ESfun (G) (i) : ℝ := ∑ x, unifW G x * pcond G i x`** — `E S_i`.
- **`Egfun (G) (i) : ℝ := ∑ x, unifW G x * (pcond G i x * gprof (pcond G i x))`** — `E[S_i g(S_i)]`.
- **`windW {n} (G) : ((Fin n → Bool) × (Fin n → Bool)) → ℝ := fun p => unifW G p.1 * unifW G p.2`**
  — the independent coupling's weights (Step 10).
- **`pmod (G) (i : Fin n) (σ : Bool) (v : Fin n → Bool) : ℝ :=`**
  `pcond G i v + (if σ then (9:ℝ)/10 else -((9:ℝ)/10)) * (pcond G i v * (1 - pcond G i v))`
  — the sign-modified zero-probability `s ± λ s(1-s)`.
- **`kern (G) (i) (σ : Bool) (v : Fin n → Bool) (b : Bool) : ℝ :=`**
  `if b = false then pmod G i σ v else 1 - pmod G i σ v`.
- **`wshW {n} (G) : ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) → ℝ :=`**
  `fun p => (1/2 : ℝ)^n * (∏ i, kern G i (p.1 i) p.2.1 (p.2.1 i)) * (∏ i, kern G i (p.1 i) p.2.2 (p.2.2 i))`
  — the shared-sign coupling of Step 11a, with `p.1 = u` (the sign vector, `true ↦ +1`),
  `p.2.1 = X̃`, `p.2.2 = Ỹ`.
  *MODELING DECISION (the most consequential one).* The joint law of
  `(U, X̃, Ỹ)` is given by the **explicit product formula** of Step 11a, not by
  an abstract "conditionally i.i.d." construction. Two things this buys, both
  load-bearing: (a) `X̃` and `Ỹ` are *manifestly* i.i.d. given `u` — the weight
  literally factors as `2⁻ⁿ · (∏ …x…) · (∏ …y…)` — which is exactly what Step 11d's
  `E[W²] ≥ (E W)²` needs; (b) signs are `Bool` with `true ↦ +9/10`,
  `false ↦ -9/10`, so `2⁻ⁿ` is the uniform weight on `Fin n → Bool`. Note
  `kern` reads the prefix of the *same* vector it is evaluated on
  (`pcond G i p.2.1` uses `pref i p.2.1`), which is what makes the product a
  genuine sequential chain. Rejected: defining the coupling by a `Kernel`/`PMF`
  bind — it hides the factorization that (a) depends on.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook
> notion**, quantified exactly as the source states it. Specifically here:
> `UnionClosed` must be `∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F` over an arbitrary
> `DecidableEq α` — not over a fixed `α := ℕ`, not with `Fintype α` bolted on,
> not weakened to "closed under unions of *disjoint* pairs" or to a
> `Finset.sup`-closure. `Hnat` must be the two-term natural-log expression, not
> `-z log z` alone. `qker` must carry the exact coefficient `81/100` (it is
> `λ²`, not `λ`). `gprof` must be defined by the square root of the product form,
> so that `gprofile_sq_eq` remains a proof obligation. `Qser`/`Aser`/`fser` must
> be the honest infinite `tsum`s — replacing any of them by a finite partial sum
> or by a closed form silently changes the object and can make Step 5 vacuous.
> The certificate tables `cR`, `bGl`, `bGr` must be transcribed **exactly** from
> `SKETCH.md`; they are checked by the frozen theorems
> `Rpoly_power_basis`, `Gpoly_bernstein_left`, `Gpoly_bernstein_right`, so a
> typo shows up as an unprovable goal, never as a silently weaker result.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each statement must render a claim of
`SKETCH.md` faithfully and minimally, have a stable binding name, and typecheck.

Below, `I01 := Set.Icc (0:ℝ) 1`. Statements are written in blueprint shorthand;
`init.py` renders them as Lean with the exact names given. **The names are
binding** (`verify.py`, `Discharge.lean`, `Solution.lean` and
`scripts/harness.json` all use them).

**Stage A — constants and logarithm bounds (Step 1).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 1 | `strict_margin` | `Cval * (1 - cval) - 1 = 929 / 156250000` | 1a |
| 2 | `log_ten_lower` | `(2:ℝ) < Real.log 10` | 1b |
| 3 | `log_ten_upper` | `Real.log 10 < 12 / 5` | 1b |
| 4 | `log_two_upper` | `Real.log 2 < 25 / 36` | 1b |
| 5 | `C_lt_ratio_123_65` | `(10 / 9) * Cval < 123 / 65` | 1 (derived) |

**Stage B — entropy / series / polynomial toolbox (Step 2).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 6 | `binEntropy_parabola_lower` | `∀ z ∈ I01, 4 * Real.log 2 * (z * (1 - z)) ≤ Hnat z` | 2a |
| 7 | `binEntropy_two_sided` | `∀ z, 0 < z → z < 1 → z * (Real.log (1/z) + 1 - z) ≤ Hnat z ∧ Hnat z ≤ z * (Real.log (1/z) + 1)` | 2b |
| 8 | `fser_closed_form` | `(∀ z, 0 < z → z < 1 → fser z = 1 + (1 - z)/z * Real.log (1 - z)) ∧ fser 1 = 1` | 2c |
| 9 | `enat_series_form` | `∀ z, 0 < z → z ≤ 1 → enat z = -Real.log z + 1 - fser z` | 2d |
| 10 | `enat_sum_of_squares` | `∀ s t, 0 < s → s ≤ 1 → 0 < t → t ≤ 1 → 2 * enat (s*t) - enat (s^2) - enat (t^2) = ∑' m : ℕ, (s^(m+1) - t^(m+1))^2 / ((m+1)*(m+2))` | 2e |
| 11 | `Qser_closed_form` | `∀ z, 0 < z → z < 1 → Qser z = ((1+z) * Real.log (1+z) + (1-z) * Real.log (1-z)) / z^2` | 2f |
| 12 | `Qser_lower_bounds` | `∀ z ∈ I01, 1 ≤ Qser z ∧ 1 + z^2/6 ≤ Qser z` | 2f |
| 13 | `Qser_hasDerivAt` | `∀ z, 0 ≤ z → z < 1 → HasDerivAt Qser (Qder z) z` | 2f |
| 14 | `Qder_upper_bounds` | `∀ z, 0 ≤ z → z < 1 → 0 ≤ Qder z ∧ Qder z ≤ z / (1 - z^2) ∧ (0 < z → Qder z ≤ -Real.log (1 - z^2) / z)` | 2f |
| 15 | `Aser_closed_form` | `∀ u ∈ I01, Aser u = u * Real.sqrt (Qser (1 - u^2))` | 2g |
| 16 | `Aser_hasDerivAt` | `∀ u, 0 < u → u < 1 → HasDerivAt Aser ((Qser (1-u^2) - (u^2) * Qder (1-u^2)) / Real.sqrt (Qser (1-u^2))) u` | 2h |
| 17 | `Ppoly_pos` | `∀ z ∈ I01, 0 < Ppoly z` | 2i |
| 18 | `Npoly_eq_deriv_form` | `∀ z, Npoly z = Ppoly z - (1 - z) * deriv Ppoly z` | 2i / 4a |
| 19 | `gprofile_sq_eq` | `∀ s ∈ I01, (gprof s)^2 = 4 * (1 - s) * Ppoly s` | 2i |
| 20 | `gprofile_hasDerivAt` | `∀ u, 0 < u → u < 1 → HasDerivAt (fun u => gprof (1 - u^2)) (2 * Npoly (1-u^2) / Real.sqrt (Ppoly (1-u^2))) u` | 2i |

Note on #16: `1 - z = u²` when `z = 1 - u²`, so `(u^2) * Qder (1-u^2)` **is**
`(1-z) Q'(z)`; it is written in `u` to avoid a definitional detour.

**Stage C — the rank-one product bound (Step 3).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 21 | `q_sign_average` | `∀ s t, qker s t = (1/2) * ((s + lam*s*(1-s)) * (t + lam*t*(1-t))) + (1/2) * ((s - lam*s*(1-s)) * (t - lam*t*(1-t)))` | 3a |
| 22 | `q_mem_Icc` | `∀ s ∈ I01, ∀ t ∈ I01, qker s t ∈ I01` | 3a |
| 23 | `diag_normalization` | `∀ s ∈ I01, s * gprof s = 2 * Real.sqrt (qker s s * (1 - qker s s))` | 3b |
| 24 | `Rpoly_power_basis` | `∀ s t, Rpoly s t = 5119741/1000000 - (2653641/250000)*(s + t) + (5028723/500000)*(s^2 + t^2) - (1187541/250000)*(s^3 + t^3) + (1187541/1000000)*(s^4 + t^4) + (11244987/500000)*(s*t) - (8719569/500000)*(s*t^2 + s^2*t) + (662661/100000)*(s*t^3 + s^3*t) - (531441/500000)*(s*t^4 + s^4*t) + (8070597/1000000)*(s^2*t^2) + (124659/250000)*(s^2*t^3 + s^3*t^2) - (1187541/1000000)*(s^2*t^4 + s^4*t^2) - (2250423/500000)*(s^3*t^3) + (531441/250000)*(s^3*t^4 + s^4*t^3) - (531441/500000)*(s^4*t^4)` | 3c |
| 25 | `Rpoly_determinant_identity` | `∀ s t, (qker s t * (1 - qker s t))^2 - qker s s * (1 - qker s s) * (qker t t * (1 - qker t t)) = s^2 * t^2 * (s - t)^2 * Rpoly s t` | 3c |
| 26 | `Rpoly_lower_bound` | `∀ s ∈ I01, ∀ t ∈ I01, 31387/40000 ≤ Rpoly s t` | 3d |
| 27 | `rank_one_product_bound` | `∀ s ∈ I01, ∀ t ∈ I01, Real.log 2 * (s * t * gprof s * gprof t) ≤ Hnat (qker s t)` | 3e |

**Stage D — the profile speed bound (Step 4).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 28 | `Gpoly_bernstein_left` | `∀ x, Gpoly (x/2) = ∑ k ∈ Finset.range 11, bGl k * bern 10 k x` | 4b |
| 29 | `Gpoly_bernstein_right` | `∀ x, Gpoly (1/2 + x/2) = ∑ k ∈ Finset.range 11, bGr k * bern 10 k x` | 4b |
| 30 | `Gpoly_pos` | `∀ z ∈ I01, 0 < Gpoly z` | 4b |
| 31 | `gprofile_speed_le` | `∀ z ∈ I01, |2 * Npoly z / Real.sqrt (Ppoly z)| ≤ 16/5` | 4c |
| 32 | `gprofile_lipschitz` | `∀ s ∈ I01, ∀ t ∈ I01, |gprof s - gprof t| ≤ (16/5) * |Real.sqrt (1 - s) - Real.sqrt (1 - t)|` | 4c |

**Stage E — the entropy speed bound (Step 5).**

Write `Ader z := (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)` in the table
below; in `Theorems.lean` this expression is written out in full (it is *not* a
frozen definition — keeping it inline forces each range lemma to be about the
same syntactic object as `Aser_hasDerivAt`).

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 33 | `Ader_lower_small` | `∀ z, 0 < z → z ≤ 1/10 → 8/9 ≤ Ader z` | 5a (+ its note) |
| 34 | `Ader_lower_large` | `∀ z, 99999/100000 ≤ z → z < 1 → 8/9 ≤ Ader z` | 5b |
| 35 | `Ader_lower_middle` | `∀ z, 1/10 ≤ z → z ≤ 99999/100000 → 8/9 ≤ Ader z` | 5c |
| 36 | `Ader_lower_bound` | `∀ z, 0 < z → z < 1 → 8/9 ≤ Ader z` | 5a–c |
| 37 | `Aser_lipschitz_lower` | `∀ u ∈ I01, ∀ v ∈ I01, (8/9) * |u - v| ≤ |Aser u - Aser v|` | 5d |
| 38 | `entropy_speed_bound` | `∀ u ∈ I01, ∀ v ∈ I01, (8/9) * |u - v| ≤ Real.sqrt (∑' m : ℕ, ((1-u^2)^(m+1) - (1-v^2)^(m+1))^2 / ((m+1)*(m+2)))` | 5d |

*MODELING DECISION (range split).* `SKETCH.md` (5a) proves the small range for
`z ≤ 1/100` but explicitly notes the same elementary argument works for all
`z ≤ 1/10`, and advises shrinking the interval-arithmetic range accordingly. We
take that option: `Ader_lower_small` covers `(0, 1/10]` (**stronger** than 5a)
and `Ader_lower_middle` covers `[1/10, 99999/100000]` (a **sub**interval of 5c's
range). The three ranges still cover `(0,1)`, so `Ader_lower_bound` — the only
thing any later stage consumes — is exactly the sketch's (5d) hypothesis, with
no weakening anywhere. This is recorded here so no later agent "restores" the
`1/100` split and then wonders why (5a) does not close.

**Stage F — the off-diagonal estimate (Step 6).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 39 | `off_diagonal_estimate` | `∀ s, 0 < s → s ≤ 1 → ∀ t, 0 < t → t ≤ 1 → (Real.log 2 / 9) * (gprof s - gprof t)^2 ≤ 2 * enat (s*t) - enat (s^2) - enat (t^2)` | 6 |

**Stage G — the diagonal estimate (Step 7).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 40 | `diagonal_at_one` | `Dfun 1 = 0` | 7a |
| 41 | `diagonal_small` | `∀ s, 0 < s → s ≤ 1/1000000 → 0 < Dfun s` | 7b |
| 42 | `diagonal_large` | `∀ s, 1 - 1/1000000 ≤ s → s < 1 → 0 < Dfun s` | 7c |
| 43 | `diagonal_middle` | `∀ s, 1/1000000 ≤ s → s ≤ 1 - 1/1000000 → 0 < Dfun s` | 7d |
| 44 | `diagonal_estimate` | `∀ s, 0 < s → s ≤ 1 → 0 ≤ Dfun s` | 7 |

**Stage H — the scalar inequality (Step 8).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 45 | `Phi_decomposition` | `∀ s t, Phi s t = Dfun s + Dfun t + (9/10) * (2 * enat (s*t) - enat (s^2) - enat (t^2) - (Real.log 2 / 9) * (gprof s - gprof t)^2)` | 8a |
| 46 | `pointwise_inequality` | `∀ s ∈ I01, ∀ t ∈ I01, Cval * (s * Hnat t + t * Hnat s) ≤ 2 * ((9/10) * Hnat (s*t) + (Real.log 2 / 10) * (s * t * gprof s * gprof t))` | 8b |
| 47 | `scalar_inequality` | `∀ {ι : Type} [Fintype ι] (w S : ι → ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i = 1) → (∀ i, S i ∈ I01) → Cval * (∑ i, w i * S i) * (∑ i, w i * Hnat (S i)) ≤ (9/10) * (∑ i, ∑ j, w i * w j * Hnat (S i * S j)) + (Real.log 2 / 10) * (∑ i, w i * (S i * gprof (S i)))^2` | 8c |

*MODELING DECISION (#47).* A "finitely supported `[0,1]`-valued random variable
with an independent copy" is rendered as: a `Fintype ι`, a nonnegative weight
vector `w` summing to `1`, and a value function `S : ι → I01`. The independent
copy is the **product weight on `ι × ι`**, written out as the double sum
`∑ i, ∑ j, w i * w j * …` rather than as a second variable. This is exactly the
shape produced by `indep_coupling_bound`, so Step 12 applies it with no glue.
Note `Phi` and `Dfun` do *not* appear in #47 — the scalar inequality is stated
in the un-normalized `Hnat` form, which is the form Step 12 consumes.

**Stage I — the finitary entropy toolbox (Step 9).**

Throughout, `w : Ω → ℝ` with `[Fintype Ω]`, `hw : ∀ ω, 0 ≤ w ω`, `hw1 : ∑ ω, w ω = 1`.

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 48 | `entropy_chain_rule` | `∀ {Ω} [Fintype Ω] {n} (w : Ω → ℝ), (∀ ω, 0 ≤ w ω) → (∑ ω, w ω = 1) → ∀ X : Ω → (Fin n → Bool), Hrv w X = ∑ i : Fin n, condHrv w (fun ω => X ω i) (fun ω => pref i.val (X ω))` | 9d |
| 49 | `condHrv_le_of_comp` | `∀ {Ω} [Fintype Ω] {β γ δ} … (w) (hw) (hw1) (Z : Ω → β) (W : Ω → γ) (f : γ → δ), condHrv w Z (fun ω => f (W ω)) ≥ condHrv w Z W` | 9d |
| 50 | `entropy_le_log_card` | `∀ {Ω} [Fintype Ω] {n} (w) (hw) (hw1) (Z : Ω → (Fin n → Bool)) (G : Finset (Fin n → Bool)), (∀ ω, w ω ≠ 0 → Z ω ∈ G) → Hrv w Z ≤ Real.log G.card` | 9c |
| 51 | `uniform_entropy_eq_log_card` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → Hrv (unifW G) id = Real.log G.card` | 9a |
| 52 | `prefix_entropy_decomposition` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → ∑ i : Fin n, HiFun G i = Real.log G.card` | 9a |
| 53 | `freq_eq_one_sub_ES` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → ∀ i : Fin n, ((G.filter (fun x => x i = true)).card : ℝ) / (G.card : ℝ) = 1 - ESfun G i` | 9b |

**Stage J — the independent coupling (Step 10).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 54 | `indep_support_mem` | `∀ {n} (G : Finset (Fin n → Bool)), UnionClosedCube G → ∀ p, windW G p ≠ 0 → orVec p.1 p.2 ∈ G` | 10 |
| 55 | `indep_coupling_bound` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → ∑ i : Fin n, (∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y)) ≤ Hrv (windW G) (fun p => orVec p.1 p.2)` | 10 |

**Stage K — the shared-sign coupling (Step 11).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 56 | `shared_isDist` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → (∀ p, 0 ≤ wshW G p) ∧ ∑ p, wshW G p = 1` | 11a |
| 57 | `shared_support_mem` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → UnionClosedCube G → ∀ p, wshW G p ≠ 0 → orVec p.2.1 p.2.2 ∈ G` | 11a |
| 58 | `shared_marginal_uniform` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → ∀ x, (∑ u, ∑ y, wshW G (u, x, y)) = unifW G x` | 11b |
| 59 | `shared_coupling_bound` | `∀ {n} (G : Finset (Fin n → Bool)), G.Nonempty → Real.log 2 * (∑ i : Fin n, (Egfun G i)^2) ≤ Hrv (wshW G) (fun p => orVec p.2.1 p.2.2)` | 11c–d |

**Stage L — assembly and the headline (Step 12).**

| # | Name | Statement | Sketch |
| - | ---- | --------- | ------ |
| 60 | `frankl_cube` | `∀ {n} (G : Finset (Fin n → Bool)), UnionClosedCube G → G.Nonempty → (∃ x ∈ G, x ≠ fun _ => false) → ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card` | 12 |
| 61 | `frankl_038272` | `∀ {α : Type*} [DecidableEq α] (F : Finset (Finset α)), UnionClosed F → F.Nonempty → F ≠ {∅} → ∃ x : α, 1196 * F.card ≤ 3125 * (F.filter (fun A => x ∈ A)).card` | 12 / Conclusion |

**Why these 61.** Stages A–B are *support*: numeric and series infrastructure
that every later inequality consumes. Stages C–E are the **three certified
assertions** of the paper (an exact Bernstein certificate each for C and D, and
the transcendental one-variable bound for E); together with Stages F–G (the
off-diagonal and diagonal estimates, G containing the second and hardest
interval-arithmetic obligation) they feed Stage H. **`scalar_inequality` (#47)
is the milestone** — the mathematical heart, and the last statement that
mentions no probability. Stages I–K are the finitary entropy machinery and the
two couplings; each is elementary but bulky. Stage L is the **payoff**:
`frankl_cube` runs the Step-12 contradiction and `frankl_038272` is the headline
a reader cites. The two "easy converse / sanity" statements that keep the
headline airtight are `q_mem_Icc` (#22 — without it `Hnat (qker s t)` could be
evaluated outside `[0,1]` where it is negative) and `shared_marginal_uniform`
(#58 — without it the `Egfun` in `shared_coupling_bound` would not be the same
quantity as the one in `scalar_inequality`, and the assembly would be a
non-sequitur that still typechecks).

**Re-build gate.** After freezing, `lake build` must succeed (everything is
`sorry`, but the *statements* must typecheck). Do not write a line of proof until
the skeleton compiles. Record the SHA-256 of `Defs.lean` and `Theorems.lean`
into `scripts/frozen.sha256`, then log a PROGRESS entry: "SETUP frozen, skeleton
builds, pins recorded."

### 4. Progress logging (`PROGRESS.md`, append-only — MANDATORY)

There is a single shared log at the repo root, **`PROGRESS.md`**. It is the
project's memory: it is read by an auditor (see below) and by freshly launched
agents that have **no prior context** and must figure out, from the log alone,
what is done, what is in progress, and where they should start. Treat it as the
first thing you read and the last thing you write.

**Inviolable rules (read before doing anything):**

- **APPEND ONLY. NEVER delete, edit, overwrite, reword, or "tidy up" any
  existing entry — not your own, not anyone else's, not ever.** The log is an
  immutable history. If something you wrote earlier turns out to be wrong, do
  **not** remove it: append a *new* entry that corrects it (`📝 decision`,
  noting "supersedes the entry at <timestamp>"). Deleting or rewriting history
  is itself treated as a cheating signal in the audit.
- **Every entry is timestamped and stage-annotated.** Get the real UTC time with
  `date -u +"%Y-%m-%dT%H:%M:%SZ"` — do not invent or approximate timestamps.
- **One entry per event, newest appended at the bottom**, in this exact format.
  Write every line flush left, exactly as shown. The `Agent:` label must contain
  `agent-iter<N>` so the entry can be attributed to its iteration, and lemma or
  definition names on the `Next:` line must be wrapped in `backticks` — the
  recurring-crux stall guard counts backticked identifiers:

```
## <UTC timestamp> — <stage/item, e.g. "Stage C · <lemma name>">
Agent: agent-iter<N>-<k>
Status: ✅ proved | ⚠️ blocked | 🔧 in progress | 📝 decision
Check: <#print axioms result, lake build result, or n/a>
Note: <one or two lines — what you did, key lemma used, or exactly what blocks you>
Next: <for a ✅/⚠️ entry: what work this unblocks or what a follow-up agent should do next, with exact lemma/file names to build on; "n/a" only if truly terminal>
```

- **The `Next:` line is mandatory on every `✅` and `⚠️` entry.** Point the next
  agent at the related work: which stage is now unblocked, the exact names of the
  lemmas/defs you produced that they will consume, and any gotcha you hit. A fresh
  agent with no context should be able to read the latest entries and know exactly
  where to start — this is what makes sessions resumable.

- **Log at least when you:** (a) start work on a stage (`🔧 in progress`, so two
  agents don't collide on the same lemma), (b) finish/close a lemma or stage
  (`✅`, with the `#print axioms` output as `Check:`), (c) hit a blocker (`⚠️` —
  write the *exact* failing goal/error, then move to the next independent
  target rather than thrashing), or (d) make a non-obvious modeling or proof
  decision (`📝`). Append a prominent entry at each milestone.
- **Never fake a `✅`.** Only mark proved what compiles with a clean
  `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`; no
  `sorryAx`, no `native_decide`/`Lean.ofReduceBool`). A `✅` that does not match
  the actual build state is the most serious audit failure.
- **Do not stop to ask for confirmation between stages — work straight through**,
  logging as you go.

**Why this matters (do not skip):** `PROGRESS.md` is the input to a
**faithfulness / cheating audit conducted by the orchestrator, not by you.** The
auditor cross-checks every `✅` entry against the actual Lean source and axiom
output, and checks that no frozen file or earlier log entry was tampered with.
An accurate, complete, append-only log protects your work from being thrown out;
a log with gaps, edited history, or unsupported `✅`s causes the whole stage to
be re-audited or discarded.

### 5. The iteration loop & agent-onboarding protocol

After SETUP, the project is driven by an **orchestrator** that runs repeated
iterations. Each iteration has three phases, executed by short-lived agents that
share **no memory** beyond the files on disk — they coordinate entirely through
`TASKS.md`, `PROGRESS.md`, and `REVIEW.md` (all append-only):

1. **PLAN** — one agent reads `REVIEW.md` (the auditor's prior findings — its
   "Required follow-ups" are top priority), `PROGRESS.md` (what is `✅`/`🔧`/`⚠️`/
   `📝`), `SKETCH.md`, and `BLUEPRINT.md`. It chooses the most valuable batch of
   work that respects the dependency graph, splits it across **up to 4 parallel
   workers with NON-OVERLAPPING files**, and **appends a `## Iteration N` block to
   `TASKS.md`** with one `Agent k:` line per active worker (inactive workers
   omitted). It writes no proofs.
2. **WORKERS** — up to 4 agents run **in parallel**, one per `Agent k:` line.
   Each owns only the files its line assigns (this is what makes parallelism
   collision-free).
3. **REVIEW** — one independent, adversarial auditor re-runs the build, `#print
   axioms`, and `scripts/verify.py`, checks faithfulness against `SKETCH.md`/
   `BLUEPRINT.md`, and **appends a `## Review — Iteration N` block to `REVIEW.md`**
   ending in `Verdict: COMPLETE | INCOMPLETE`. Every 5th iteration is a full-
   project audit. The loop ends when a verdict is `COMPLETE` and a final full
   audit confirms it.

**Worker onboarding ritual — do this BEFORE writing any code:**

1. **Read `TASKS.md`**, find `## Iteration N`, then your own `Agent k:` line.
   *That line is your assignment* — the files you own and the lemmas to produce.
   Ignore the other agents' lines (they are running right now in parallel).
2. **Read `PROGRESS.md` end to end.** Respect every `✅` (done — reuse, don't
   redo), `🔧` (another agent holds it — do not touch), `⚠️` (blocked), and `📝`
   (a fixed modeling/proof decision you must follow).
3. **Read the `BLUEPRINT.md` stage(s) your task names — including the Cheat-watch
   box — and the cited `SKETCH.md` step(s).** Do not work from the stage title
   alone; the cheat-watch boxes are binding.
4. **Append a `🔧 in progress` entry** to `PROGRESS.md` claiming your work, then
   work only on your assigned files, then append `✅`/`⚠️` as you go.

**Dependency discipline.** Respect the order graph in "Suggested formalization
order"; the Plan agent must never assign work whose prerequisites are not yet
`✅`. Workers must **never edit the frozen `Defs.lean`/`Theorems.lean`** and must
**never weaken a frozen statement** (see the cardinal cheat rule below) — if a
task seems to need that, append a `⚠️` entry describing the obstacle and stop,
rather than touching a frozen file.

---

## Part 0 — What Mathlib already gives you (reuse, do not rebuild)

| Need                                              | Mathlib handle                                                                     |
| ------------------------------------------------- | ---------------------------------------------------------------------------------- |
| natural logarithm, `log 0 = 0` junk value         | `Real.log`, `Real.log_zero`, `Real.log_one`, `Real.log_le_sub_one_of_pos`           |
| numeric bounds on `log 2`, `log 10`               | `Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`, `Real.log_lt_iff`, `Real.lt_log_iff_exp_lt`, the `norm_num` extension `Mathlib.Analysis.SpecialFunctions.Log.Basic` bounds |
| `-log(1-z) = ∑ zᵏ/k` for `|z| < 1`                | `Real.hasSum_log_sub_log_of_abs_lt_one`, `Real.abs_log_sub_add_sum_range_le`        |
| `∑ zᵏ/k` / geometric series & tails               | `hasSum_geometric_of_lt_one`, `tsum_geometric_of_lt_one`, `Summable.tsum_le_tsum`   |
| `artanh` series for `log 2 = 2 artanh(1/3)`       | `Real.log_le_sub_one_of_pos` + the two-term-plus-geometric-tail estimate by hand    |
| binary entropy API (concavity, derivative)        | `Real.binEntropy`, `Real.binEntropy_nonneg`, `Real.strictConcaveOn_binEntropy`, `Real.deriv_binEntropy` (bridge via the support lemma `Hnat_eq_binEntropy`) |
| `x ↦ -x log x` concavity/continuity               | `Real.negMulLog`, `Real.strictConcaveOn_negMulLog`, `Real.continuous_negMulLog`     |
| square roots, monotonicity, `sqrt_le_sqrt`        | `Real.sqrt`, `Real.sqrt_le_sqrt`, `Real.sq_sqrt`, `Real.sqrt_mul_self`, `Real.sqrt_mul`, `Real.sqrt_lt_sqrt` |
| `tsum` summability by comparison                  | `Summable.of_nonneg_of_le`, `summable_one_div_nat_mul_nat_add_one`-style telescoping, `Summable.tsum_eq` |
| differentiation, chain rule, `HasDerivAt`         | `HasDerivAt.comp`, `HasDerivAt.mul`, `HasDerivAt.div`, `Real.hasDerivAt_sqrt`, `HasDerivAt.tsum` / `hasDerivAt_tsum_of_summable_deriv` (uniform-on-compacts version) |
| mean value theorem / derivative ⇒ Lipschitz       | `Convex.inner_le_nnorm…`, `norm_image_sub_le_of_norm_deriv_le_segment'`, `StrictMonoOn_of_deriv_pos`, `Convex.inner_smul_le…`; the usable one here is `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` |
| reverse triangle inequality in `ℓ²`               | `EuclideanSpace`/`lp` Minkowski, or finite-partial-sum `Finset.inner_mul_le_norm_mul_norm` + limit (see Stage E) |
| binomial identity `∑ₖ C(m,k) xᵏ(1-x)^(m-k) = 1`   | `add_pow` / `Commute.add_pow`, `Finset.sum_range_choose_mul_pow`                    |
| `Finset` sums, products, filters, `Fintype.sum`   | `Finset.sum_comm`, `Finset.sum_congr`, `Finset.prod_congr`, `Fintype.sum_prod_type`, `Finset.sum_filter` |
| `Fin n → Bool` is a `Fintype` with `DecidableEq`  | `Pi.fintype`, `instDecidableEqPi`, `Fintype.card_fun`                               |
| Jensen / `E[W²] ≥ (E W)²` on finite sums          | `inner_mul_le_norm_mul_norm`, `Finset.inner_mul_le_norm_mul_norm`, `Finset.sum_div_pow_mul_fract…`; simplest is `Finset.sum_mul_sq_le_sq_mul_sq` (finite Cauchy–Schwarz) |
| concavity ⇒ `∑ w f(x) ≤ f(∑ w x)`                 | `ConcaveOn.le_map_sum` / `inner_le_weight_mul_Lp_of_norm_le`; use `ConcaveOn.smul_le_sum` |

**The one or two nontrivial dependencies.** (i) `Real.binEntropy` plus its
concavity/derivative API — only used through the bridge `Hnat_eq_binEntropy`, so
if the pinned Mathlib rev spells it differently, only one support lemma changes,
not the frozen files. (ii) A `HasDerivAt` theorem for a `tsum` of power series
(`Qser_hasDerivAt`): if the general Mathlib machinery is awkward, prove it
directly — on `[0, r]` with `r < 1` the series and its termwise derivative are
both dominated by geometric series, and `hasDerivAt_of_tendstoUniformlyOn` closes
it.

**Machinery you can avoid.** The sketch mentions probability spaces and
conditional entropy; **do not** import `MeasureTheory` or
`ProbabilityTheory.Kernel`. Every object of Steps 9–12 is a `Finset` sum of
rationals-as-reals, and the entire information-theoretic content is three
lemmas (`entropy_chain_rule`, `condHrv_le_of_comp`, `entropy_le_log_card`). The
sketch also mentions `lp 2` for the reverse triangle inequality in Step 5d; the
finite-partial-sum route (`√(∑_{m<M}) ≥ √(∑_{m<M} a²) - √(∑_{m<M} b²)`, then
`M → ∞`) avoids `lp` entirely and is recommended.

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #   | Object                                 | Role                                                              |
| --- | -------------------------------------- | ----------------------------------------------------------------- |
| D1  | `UnionClosed : Finset (Finset α) → Prop` | union-closedness, textbook form; hypothesis of the headline       |
| D2  | `orVec : (Fin n → Bool) → … → …`       | coordinatewise boolean `or`; the cube's union                      |
| D3  | `UnionClosedCube`                      | cube mirror of D1; hypothesis of `frankl_cube`                    |
| D4  | `pref : ℕ → (Fin n → Bool) → (Fin n → Bool)` | masked prefix; the thing Steps 9–11 condition on            |
| D5  | `cval, Cval, lam : ℝ`                  | `c = 1196/3125`, `C = 81001/50000`, `λ = 9/10`                    |
| D6  | `Hnat : ℝ → ℝ`                         | natural-log binary entropy `-z log z - (1-z) log(1-z)`            |
| D7  | `enat : ℝ → ℝ`                         | `Hnat s / s`, the normalized entropy `e(s)`                       |
| D8  | `qker : ℝ → ℝ → ℝ`                     | coupling kernel `q(s,t) = st(1 + (81/100)(1-s)(1-t))`             |
| D9  | `gprof : ℝ → ℝ`                        | coupling profile `g(s)`                                           |
| D10 | `fser : ℝ → ℝ`                         | `∑_{k≥1} zᵏ/(k(k+1))`; bridges `enat` to a series                 |
| D11 | `Qser : ℝ → ℝ`                         | `∑_{j≥0} z^{2j}/((j+1)(2j+1))`; the `A`-profile's core            |
| D12 | `Qder : ℝ → ℝ`                         | termwise derivative of `Qser`                                     |
| D13 | `Aser : ℝ → ℝ`                         | `A(u) = ‖(1 - (1-u²)ᵏ)/√(k(k+1))‖₂`; the entropy-speed profile    |
| D14 | `Ppoly : ℝ → ℝ`                        | degree-5 profile polynomial, factored form                        |
| D15 | `Npoly : ℝ → ℝ`                        | `P - (1-z)P'` by explicit power basis (Step 4a certificate)       |
| D16 | `Gpoly : ℝ → ℝ`                        | `64 P - 25 N²`; positivity is the Step-4 certificate              |
| D17 | `bern : ℕ → ℕ → ℝ → ℝ`                 | Bernstein basis `C(m,k) xᵏ(1-x)^{m-k}`                            |
| D18 | `cR : ℕ → ℕ → ℝ`                       | 5×5 positive Bernstein certificate matrix (Step 3d)               |
| D19 | `Rpoly : ℝ → ℝ → ℝ`                    | determinant quotient, **defined by** its Bernstein expansion      |
| D20 | `bGl, bGr : ℕ → ℝ`                     | the two degree-10 Bernstein certificate vectors (Step 4b)         |
| D21 | `Dfun : ℝ → ℝ`                         | diagonal slack `D(s)` (Step 7)                                    |
| D22 | `Phi : ℝ → ℝ → ℝ`                      | the two-variable functional `Φ(s,t)` (Step 8a)                    |
| D23 | `entropyW : (ι → ℝ) → ℝ`               | Shannon entropy of a finite weight vector                         |
| D24 | `law : (ι → ℝ) → (ι → β) → (β → ℝ)`    | pushforward law of a random variable                              |
| D25 | `Hrv`, `condHrv`                       | entropy / conditional entropy of finite random variables          |
| D26 | `unifW : Finset (Fin n → Bool) → …`    | uniform weight vector on the family `G`                           |
| D27 | `pcond : … → Fin n → … → ℝ`            | `p_i(v)`, conditional zero-probability given a prefix             |
| D28 | `HiFun, ESfun, Egfun`                  | `H_i`, `E S_i`, `E[S_i g(S_i)]` — the three per-coordinate scalars |
| D29 | `windW`                                | weights of the independent coupling `(X', Y')` (Step 10)          |
| D30 | `pmod, kern, wshW`                     | the shared-sign coupling's modified kernel and joint law (Step 11) |

---

## Part 2 — Theorems and lemmas to prove (in order)

Twelve stages, one per `Proofs/<Stage>/` directory, mirroring Steps 1–12 of
`SKETCH.md`. **Every stage ends with a Cheat-watch box; those boxes are binding.**

### Stage A — exact constants and numeric log bounds (`Proofs/Constants/`)

Goal: frozen theorems #1–#5. Pure numerics; unblocks everything.

**A1 — `strict_margin`.** `Cval * (1 - cval) - 1 = 929/156250000`. Unfold both
constants and `norm_num`. (Cross-check the sketch's arithmetic: `1 - c =
1929/3125` and `81001 * 1929 = 156250929`.)

**A2 — `log_ten_lower`.** `2 < Real.log 10`. Route: `Real.exp_one_lt_d9` gives
`exp 1 < 2.7182818286`, hence `exp 2 < 7.39 < 10`, then
`Real.lt_log_iff_exp_lt`. If a `norm_num` extension for `Real.log` exists in the
pinned rev, use it directly.

**A3 — `log_ten_upper`.** `Real.log 10 < 12/5`. Route: `10 < exp (12/5)` via the
degree-5 Taylor lower bound `∑_{k≤5} (12/5)ᵏ/k! = 166093/15625 > 10` together
with `Real.sum_le_exp_of_nonneg` (or `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`
— whichever partial-sum-≤-`exp` lemma the rev provides), then
`Real.log_lt_iff`.

**A4 — `log_two_upper`.** `Real.log 2 < 25/36`. Route as in `SKETCH.md` 1b:
`log 2 = 2 artanh(1/3) = 2 ∑_{j≥0} 1/((2j+1) 3^{2j+1})`; keep `j = 0, 1` and
bound the tail by `2/(5·3⁵) · (1/(1-1/9)) = 1/540`, giving
`log 2 ≤ 1123/1620 < 1125/1620 = 25/36`. Implement via
`Real.log ((1+1/3)/(1-1/3)) = Real.log 2` and Mathlib's
`Real.abs_log_sub_add_sum_range_le` (explicit remainder for the `log(1-x)`
series) applied at `x = ±1/3`.

**A5 — `C_lt_ratio_123_65`.** `(10/9) * Cval < 123/65`, i.e.
`81001 * 65 = 5265065 < 5535000 = 123 * 45000`. `norm_num`.

> **Cheat watch (Stage A).** The bounds must be on `Real.log`, **not** on a
> rational surrogate: do not introduce a `logApprox : ℚ → ℚ` and prove facts
> about that. Do not prove `2 ≤ Real.log 10` where `<` is stated (Step 7b needs
> the strict form to get `-log s ≥ 6 log 10 > 12`). Do not weaken `25/36` to a
> larger bound "that norm_num can do" — Step 6 needs exactly
> `25/324 > log 2 / 9`, i.e. `log 2 < 25/36`, with no slack to spare. Guardrail:
> `example : (25:ℝ)/324 > Real.log 2 / 9 := by …` must compile from A4 alone.

### Stage B — binary-entropy, series and polynomial toolbox (`Proofs/Toolbox/`)

Goal: frozen theorems #6–#20 — the analytic vocabulary Stages C–H consume.
Start with the support lemma `Hnat_eq_binEntropy : Hnat = Real.binEntropy` and
the summability lemma `summable_inv_mul_succ : Summable (fun m : ℕ => 1/((m+1)*(m+2)))`
(telescoping, sum `= 1`); every `tsum` below is dominated by it.

**B1 — `binEntropy_parabola_lower` (2a).** Substitute `z = (1-u)/2`,
`u ∈ [-1,1]`. Prove `log 2 - Hnat ((1-u)/2) = ∑_{k≥1} u^{2k}/(2k(2k-1))` from
the `log(1±u)` series, then bound each coefficient by `1/(2k(2k-1))` and use
`∑ 1/(2k(2k-1)) = log 2` (alternating harmonic). Conclude
`log 2 - Hnat z ≤ u² log 2` and `4z(1-z) = 1 - u²`.

**B2 — `binEntropy_two_sided` (2b).** From `z ≤ -log(1-z) ≤ z/(1-z)`
(`Real.add_one_le_exp` / `Real.log_le_sub_one_of_pos`), get
`-(1-z) log(1-z) ∈ [z(1-z), z]` and add `-z log z = z log(1/z)`.

**B3 — `fser_closed_form` (2c).** `∑ zᵏ/(k(k+1)) = ∑ zᵏ/k - ∑ zᵏ/(k+1)`, both
from `-log(1-z) = ∑ zᵏ/k`. At `z = 1` evaluate directly: `∑ 1/(k(k+1)) = 1`
(telescoping), no Abel limit needed.

**B4 — `enat_series_form` (2d).** Immediate from B3 and
`enat z = -log z - ((1-z)/z) log(1-z)` (which itself needs `Hnat z / z` unfolded;
handle `z = 1` separately, both sides `0`).

**B5 — `enat_sum_of_squares` (2e).** From B4 the `log` terms cancel
(`-2 log(st) + log s² + log t² = 0`), leaving
`f(s²) + f(t²) - 2f(st) = ∑ (sᵏ - tᵏ)²/(k(k+1))` termwise. Prove the termwise
identity then `tsum_sub`/`tsum_add` with summability from `summable_inv_mul_succ`.

**B6 — `Qser_closed_form`, `Qser_lower_bounds` (2f).** Closed form from the two
`log(1±z)` series; `Q ≥ 1` and `Q ≥ 1 + z²/6` by dropping all but the first one
or two nonnegative terms (`tsum_le_tsum_of_nonneg` after
`Finset.sum_le_tsum`).

**B7 — `Qser_hasDerivAt`, `Qder_upper_bounds` (2f).** Termwise differentiation
on `[0, r]`, `r < 1`, by uniform convergence of the derivative series
(dominated by `∑ 2j r^{2j-1}`). The two bounds come from the coefficient
estimates `2j/((j+1)(2j+1)) ≤ 1` and `≤ 1/j`, both from
`(j+1)(2j+1) = 2j² + 3j + 1 ≥ 2j²`, then `∑ z^{2j-1} = z/(1-z²)` and
`∑ z^{2j-1}/j = -log(1-z²)/z`.

**B8 — `Aser_closed_form`, `Aser_hasDerivAt` (2g,2h).** First prove
`∑_{k≥1} (1-zᵏ)²/(k(k+1)) = (1-z) Q(z)` via `1 - 2f(z) + f(z²)` and B3; then
`A(u) = u √(Q(1-u²))` and the chain rule (`Q ≥ 1 > 0` so `√Q` is differentiable).
Boundary values `A 0 = 0`, `A 1 = 1` are support lemmas.

**B9 — `Ppoly_pos`, `Npoly_eq_deriv_form`, `gprofile_sq_eq`,
`gprofile_hasDerivAt` (2i).** `Ppoly_pos`: both factors `≥ 1` on `[0,1]`
(`z²(1-z) ≤ z`), `nlinarith`. `Npoly_eq_deriv_form`: compute `deriv Ppoly` with
`simp [Ppoly]` + `deriv` simp set (or `HasDerivAt` explicitly), then `ring_nf` and
`norm_num` — this is where the sketch's coefficients get validated.
`gprofile_sq_eq`: `Real.sq_sqrt` needs the radicand `≥ 0`, which follows from the
algebraic identity `1 - s²(1+(81/100)(1-s)²) = (1-s)(1 + s - (81/100)s²(1-s))`
plus `Ppoly_pos`. `gprofile_hasDerivAt`: chain rule on
`u ↦ 2u √(Ppoly (1-u²))` using `Npoly_eq_deriv_form`.

> **Cheat watch (Stage B).** Do not replace any `tsum` by a finite partial sum
> "for tractability" — the frozen statements are about the honest series. Do not
> prove `Qser_hasDerivAt` only on a subinterval and then quantify over `[0,1)`
> anyway: the hypothesis is `0 ≤ z < 1` and it must be discharged for every such
> `z` (an `r < 1` argument is fine, but you must instantiate `r` from `z`). Do
> not prove `binEntropy_parabola_lower` only for `z ∈ [1/4, 3/4]` where
> `nlinarith` succeeds. Do not use `Real.binEntropy`'s API to *restate* `Hnat`
> facts with different constants — the bridge lemma must be an equality of
> functions, checked once. `gprofile_sq_eq` must not be proved by *redefining*
> `gprof`; `Defs.lean` is frozen. Guardrails: `example : Aser 0 = 0`,
> `example : Aser 1 = 1`, `example : Qser 0 = 1` must all compile.

### Stage C — the rank-one product bound (`Proofs/RankOne/`) · CERTIFICATE 1

Goal: frozen theorems #21–#27, culminating in
`h(q(s,t)) ≥ s t g(s) g(t)` (Step 3e). Depends on Stage B (B1, B9).

**C1 — `q_sign_average` (3a).** Pure `ring` after unfolding `qker` and `lam`
(the cross terms cancel; `lam² = 81/100`).

**C2 — `q_mem_Icc` (3a).** Each of the four factors lies in `[0,1]`:
`s - λs(1-s) ≥ s - s(1-s) = s² ≥ 0` and `s + λs(1-s) ≤ s(2-s) ≤ 1` since
`1 - s(2-s) = (1-s)² ≥ 0`. Then C1 exhibits `qker s t` as a convex combination of
two products of `[0,1]` numbers. `nlinarith` per factor.

**C3 — `diag_normalization` (3b).** Square both sides. `s * gprof s ≥ 0` and
`2√(q(s,s)(1-q(s,s))) ≥ 0`, so it suffices to match squares:
`s² gprof(s)² = 4 q(s,s)(1 - q(s,s))` — `ring` after `gprofile_sq_eq` (or after
`Real.sq_sqrt` on `gprof`'s radicand).

**C4 — `Rpoly_power_basis` (3c table).** `Rpoly` is a double sum of 25 terms;
`simp [Rpoly, cR, bern, Finset.sum_range_succ]` then `ring_nf` + `norm_num`. This
validates the 25-entry Bernstein table against the sketch's power-basis table.

**C5 — `Rpoly_determinant_identity` (3c).** After C4, both sides are explicit
polynomials of degree ≤ 8 in each variable; `ring` (or `ring_nf; norm_num`).
Budget compile time — this is the largest `ring` call in the project; if it is
slow, prove it via `Rpoly_power_basis` rewritten first so `ring` sees the power
basis, not `bern`.

**C6 — `Rpoly_lower_bound` (3d).** `bern 4 k x ≥ 0` on `[0,1]`; `∑ₖ bern 4 k x = 1`
by `add_pow`/`Finset.sum_range_choose_mul_pow` with `x + (1-x) = 1`. Then
`Rpoly s t = ∑ₖ ∑_ℓ cR k ℓ B_k(s) B_ℓ(t) ≥ (min cR) · ∑ₖ∑_ℓ B_k(s)B_ℓ(t) = 31387/40000`.
The minimum over the 25 explicit rationals is `norm_num`-checked (`c 2 3 = 31387/40000`).

**C7 — `rank_one_product_bound` (3e).** From C5 + C6,
`(q(1-q))² ≥ q(s,s)(1-q(s,s)) q(t,t)(1-q(t,t)) ≥ 0`; take square roots using
`q(1-q) ≥ 0` (from C2) and `Real.sqrt_le_sqrt`/`Real.le_sqrt`. Then
`Hnat (q s t) ≥ 4 log 2 · q(1-q)` by B1, and `4 · (s g(s)/2) · (t g(t)/2) =
s t g(s) g(t)` by C3.

> **Cheat watch (Stage C).** The determinant identity #25 must be proved for
> **all real `s, t`** (no `s, t ∈ [0,1]` hypothesis) — it is a ring identity, and
> adding an interval hypothesis would be an added hypothesis on a frozen
> statement. `Rpoly_lower_bound` must give the stated constant `31387/40000`, not
> merely `0 < Rpoly` (Step 3e itself only needs `≥ 0`, but the constant is the
> sketch's certified claim and is what makes a transcription error detectable).
> Do **not** "prove" #26 by `decide` on a finite grid of `(s,t)` — that is a
> sampling argument, not a proof. Do not drop the `s²t²(s-t)²` factor or replace
> `=` by `≥` in #25. Guardrails: `example : Rpoly 0 0 = 5119741/1000000`,
> `example : Rpoly 1 1 = 1`, and `example : qker (1/2) (1/2) = …` must compile
> and `norm_num` to the tabulated values.

### Stage D — the profile speed bound (`Proofs/ProfileSpeed/`) · CERTIFICATE 2

Goal: frozen theorems #28–#32. Depends on Stage B (B9). Independent of Stage C.

**D1 — `Gpoly_bernstein_left/right` (4b).** Expand `Gpoly (x/2)` and
`Gpoly (1/2 + x/2)` as degree-10 polynomials in `x` and match against
`∑ₖ bGl k · bern 10 k x`. `simp [Gpoly, Ppoly, Npoly, bern, bGl,
Finset.sum_range_succ]; ring_nf; norm_num`. These are big but purely mechanical;
if `ring_nf` times out, prove coefficient-by-coefficient after
`Polynomial`-free `linear_combination`.

**D2 — `Gpoly_pos` (4b).** All 22 coefficients are positive (`norm_num` on the
`match`), `bern 10 k x ≥ 0` on `[0,1]` and `∑ₖ bern 10 k x = 1`; hence
`Gpoly (x/2) ≥ min b > 0` and `Gpoly (1/2 + x/2) ≥ min b' > 0` for `x ∈ [0,1]`.
Every `z ∈ [0,1]` is `z = x/2` with `x = 2z ∈ [0,1]` (if `z ≤ 1/2`) or
`z = 1/2 + x/2` with `x = 2z - 1 ∈ [0,1]` (if `z ≥ 1/2`) — do the case split on
`z ≤ 1/2` explicitly.

**D3 — `gprofile_speed_le` (4c).** From `Gpoly z > 0`: `25 N(z)² < 64 P(z)`.
With `Ppoly z > 0` (B9), `|N(z)|/√(P(z)) < 8/5` follows from
`Real.lt_sqrt`/`Real.div_lt_iff` and `(√P)² = P`. Multiply by 2.

**D4 — `gprofile_lipschitz` (4c).** Apply the MVT/derivative-bound lemma
(`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) to
`φ : u ↦ gprof (1 - u²)` on `[0,1]`, with `HasDerivAt` from B9
(`gprofile_hasDerivAt`) on `(0,1)` and `|φ'| ≤ 16/5` from D3. Continuity at the
endpoints: `gprof` is continuous (composition of `Real.sqrt` with a polynomial
whose radicand is `≥ 0` on `[0,1]`). Finally rewrite `s = 1 - u²` with
`u = √(1-s)`, i.e. use `Real.sq_sqrt` to see `gprof s = φ (√(1-s))`.

> **Cheat watch (Stage D).** #31 must be `∀ z ∈ [0,1]`, not "for `z` in the
> finitely many Bernstein nodes". Do not prove `Gpoly_pos` by evaluating `Gpoly`
> at sample points and appealing to continuity — the Bernstein certificate is the
> proof, and it is why the coefficient tables are frozen. Do not replace the
> Lipschitz constant `16/5` by a larger one that is easier to get: Step 6 uses
> `(64/81)·(25/256) = 25/324` and any slack breaks the `25/324 > log 2 / 9`
> margin. Do not prove #32 only for `s ≤ t` and call it symmetric without
> actually deriving the other case. Guardrails:
> `example : Gpoly 0 = 5023/100` and `example : Gpoly 1 = 28` (the endpoint
> Bernstein coefficients `bGl 0` and `bGr 10`) must `norm_num`.

### Stage E — the entropy speed bound (`Proofs/EntropySpeed/`) · OBLIGATION 1

Goal: frozen theorems #33–#38. Depends on Stage A (A3) and Stage B (B6, B7, B8).
Independent of Stages C, D. **This stage contains the first of the two
interval-arithmetic obligations (#35) and is the second-hardest engineering
after Stage G.**

**E1 — `Ader_lower_small` (5a, extended range).** For `0 < z ≤ 1/10`:
`√Q ≥ 1` and `0 ≤ Q'(z) ≤ z/(1-z²) ≤ (1/10)/(1-1/100) = 10/99 < 1/9` (B6, B7,
plus monotonicity of `z ↦ z/(1-z²)`), so
`Ader z ≥ √Q - (1-z)Q'/√Q ≥ 1 - Q' > 8/9`.

**E2 — `Ader_lower_large` (5b).** For `99999/100000 ≤ z < 1`, set `ε = 1-z`.
`Q(z) ≥ 1 + z²/6 > (27/25)²` so `√Q > 27/25`. And
`(1-z)Q'/√Q ≤ ε·(-log(1-z²))/z ≤ ε log(1/ε)/z ≤ (10⁻⁵ · 5 log 10)/(99999/100000)
≤ 12/99999` using `log 10 < 12/5` (A3) and monotonicity of `ε log(1/ε)` on
`(0, 1/e)`. Conclude `Ader z > 27/25 - 12/99999 > 8/9`.

**E3 — `Ader_lower_middle` (5c) — INTERVAL-ARITHMETIC OBLIGATION.** Prove
`Ader z ≥ 8/9` on `[1/10, 99999/100000]`. Recommended engineering:

- Work with the **square-free form** `81 · N_Q(z)² ≥ 64 · Q(z)` where
  `N_Q(z) := Q(z) - (1-z)Q'(z)`, valid because `Q > 0` and (on this range)
  `N_Q > 0`. This eliminates every `Real.sqrt`.
- Build a **reusable enclosure API** as support lemmas in
  `Proofs/EntropySpeed/Enclose.lean`: for rationals `a ≤ b`,
  `Qlo a ≤ Q z ≤ Qhi b` and `0 ≤ Q' z ≤ Qderhi b` for `z ∈ [a,b]`, using
  monotonicity of `Q` and `Q'` (B6, B7) — this is the key simplification: **both
  are increasing**, so the enclosure on a box is just the pair of endpoint
  values, and no Taylor remainder is needed for the *shape*, only for the
  *numbers*.
- Numbers at rational endpoints: on `z ≤ 1/2` evaluate `Q` by its **series**
  (partial sum + explicit geometric tail bound, since
  `∑_{j>J} z^{2j}/((j+1)(2j+1)) ≤ z^{2J+2}/(1-z²)`); on `z ≥ 1/2` use the closed
  form `Qser_closed_form` with certified rational `log` enclosures at the
  endpoints (artanh series with geometric tail, exactly as in A4). This is the
  `SKETCH.md` (5c) recommendation and avoids the cancellation that forced the
  paper's Arb run to depth 25.
- Cover `[1/10, 99999/100000]` by a **finite, explicitly listed** partition. The
  true margin here is ≈ `0.032` (minimum near `z ≈ 0.49`), so a coarse uniform
  grid suffices — start with ~64 boxes on `[1/10, 1/2]` and ~64 on
  `[1/2, 99999/100000]` and refine only where a box fails. Drive the per-box
  check with `decide`-free `norm_num`/`interval_cases`-style iteration over an
  explicit `List ℚ` of breakpoints, proving one `∀ z ∈ [aⱼ, aⱼ₊₁]` lemma per box
  by `nlinarith` from the endpoint enclosures.
- **Budget:** expect this to be the longest-compiling file in the project after
  Stage G. Split it across several files (`Enclose.lean`, `BoxesLow.lean`,
  `BoxesHigh.lean`, `Middle.lean`) so parallel workers do not collide and so a
  single slow `nlinarith` does not block the whole build.

**E4 — `Ader_lower_bound` (5a–c).** Case split `z ≤ 1/10`, `1/10 ≤ z ≤ 99999/100000`,
`z ≥ 99999/100000`; apply E1/E3/E2.

**E5 — `Aser_lipschitz_lower` (5d, first half).** `A` is continuous on `[0,1]`
(B8) and `A' ≥ 8/9 > 0` on `(0,1)` (E4 via `Aser_hasDerivAt`), so `A` is strictly
monotone and `|A u - A v| ≥ (8/9)|u - v|` by the MVT
(`exists_hasDerivAt_eq_slope` on the closed interval between `u` and `v`, then
handle `u = v` trivially and the endpoints `0`, `1` by continuity/limits).

**E6 — `entropy_speed_bound` (5d, second half).** With
`a m = (1 - s^{m+1})/√((m+1)(m+2))` and `b m = (1 - t^{m+1})/√((m+1)(m+2))`,
`‖a‖₂ = Aser u`, `‖b‖₂ = Aser v` (B8) and `‖a - b‖₂` is the stated square root
(note `a m - b m = (t^{m+1} - s^{m+1})/√(…)`, and the square kills the sign).
Prove the reverse triangle inequality on **finite partial sums**
(`√(∑_{m<M}(a-b)²) ≥ √(∑_{m<M}a²) - √(∑_{m<M}b²)`, i.e. finite Minkowski via
`Finset.sum_mul_sq_le_sq_mul_sq`), then pass to the limit with
`Summable.tendsto_sum_tsum_nat` and `Real.sqrt`'s continuity. Combine with E5.

> **Cheat watch (Stage E).** #35 is a genuine proof obligation, not an
> assumption: `USER_NOTES.md` permits **no** axioms, so `axiom`, `sorry`, and
> `native_decide` are all banned here (`native_decide` would also dirty
> `#print axioms`). Do **not** "verify" the middle range by evaluating `Ader` at
> the grid points only — you must bound it on each *closed box*. Do not shrink
> the middle range beyond `[1/10, 99999/100000]` without correspondingly widening
> E1/E2 and re-proving them; the three ranges must still cover `(0,1)`, and
> `Ader_lower_bound` (#36) is what checks that. Do not weaken `8/9` — Step 6
> needs exactly `(8/9)² = 64/81`. In E6, do not silently replace the `tsum` by a
> partial sum, and do not assume `s ≥ t` to drop an absolute value.

### Stage F — the off-diagonal estimate (`Proofs/OffDiagonal/`)

Goal: frozen theorem #39. Depends on Stages A (A4), B (B5), D (D4), E (E6).

**F1 — `off_diagonal_estimate` (6).** Put `u = √(1-s)`, `v = √(1-t)` (so
`s = 1-u²`, `t = 1-v²` by `Real.sq_sqrt`, using `s, t ≤ 1`). Chain:
`2e(st) - e(s²) - e(t²) = ∑ (sᵏ-tᵏ)²/(k(k+1))` (B5)
`≥ (64/81)(u-v)²` (E6, squaring both sides — legitimate since both sides ≥ 0)
`≥ (64/81)(25/256)(g(s)-g(t))²` (D4, squared: `(u-v)² ≥ (25/256)(g s - g t)²`)
`= (25/324)(g(s)-g(t))² ≥ (log 2 / 9)(g(s)-g(t))²` by A4 (`log 2 < 25/36`).

> **Cheat watch (Stage F).** The hypotheses are exactly `0 < s ≤ 1`,
> `0 < t ≤ 1` — do not add `s ≠ t`, do not add `s ≤ t`, do not exclude `s = 1`.
> Do not replace `log 2 / 9` by `25/324` in the conclusion (that would be a
> *different, stronger* statement, but Step 8a's `Phi_decomposition` is written
> with `log 2 / 9` and would then not match — and more importantly the frozen
> text is frozen). Squaring D4 requires both sides nonnegative — discharge that,
> do not `nlinarith` your way past it.

### Stage G — the diagonal estimate (`Proofs/Diagonal/`) · OBLIGATION 2 · HARDEST

Goal: frozen theorems #40–#44. Depends on Stages A (A2, A3, A4, A5) and B (B2,
B9). Independent of C–F. **This is the tightest inequality in the proof and the
single hardest engineering task in the project — budget accordingly.**

**G1 — `diagonal_at_one` (7a).** `enat 1 = Hnat 1 / 1 = 0` and `gprof 1 = 0`
(radicand `= 0` at `s = 1` since `1 - 1·(1+0) = 0`). `norm_num` after unfolding.

**G2 — `diagonal_small` (7b).** For `0 < s ≤ 10⁻⁶`: `enat (s²) ≥ -log(s²) =
2(-log s)` and `enat s ≤ -log s + 1` (B2), and `(log 2/10) g² ≥ 0`. So
`Dfun s ≥ (9/5 - C)(-log s) - C = (8999/50000)(-log s) - 81001/50000 > 0`
because `-log s ≥ 6 log 10 > 12` (A2) and `(8999/50000)·12 > 81001/50000`.

**G3 — `diagonal_large` (7c).** For `s = 1-ε`, `0 < ε ≤ 10⁻⁶`: put
`δ = 1 - s² = ε(2-ε)`, `L = log(1/ε) > 12` (A2). Use `Hnat (s²) = Hnat δ`,
`Hnat s = Hnat ε` (symmetry `Hnat z = Hnat (1-z)`, a support lemma), and B2 to
get
`enat(s²)/enat(s) ≥ ((2-ε)/(1-ε)) · (L - log(2-ε) + 1 - δ)/(L+1) ≥ 2(L + 3/10)/(L+1) > 123/65 > (10/9)C`
using `log(2-ε) ≤ log 2 < 25/36` (A4), `δ < 1/500000`, and A5. Then
`(9/10)enat(s²) - C·enat s > 0` and `(log 2/10) g² ≥ 0`.

**G4 — `diagonal_middle` (7d) — INTERVAL-ARITHMETIC OBLIGATION.** Prove
`0 < Dfun s` on `[10⁻⁶, 1 - 10⁻⁶]`. Engineering plan:

- Use `gprofile_sq_eq` to replace `(gprof s)²` by the **polynomial**
  `4(1-s)Ppoly s`, so `Dfun s = (9/10) enat(s²) - (81001/50000) enat s +
  (log 2/10)·4(1-s)Ppoly s` — a combination of `log s`, `log(1-s)`, `log(1-s²)`,
  rational functions and `log 2`. No `sqrt` remains.
- Build a certified rational `log` enclosure API as support lemmas
  (`Proofs/Diagonal/LogEnclose.lean`): `logLo, logHi : ℚ → ℚ` with
  `logLo a ≤ Real.log a ≤ logHi a` for positive rational `a`, via
  `log a = 2 artanh((a-1)/(a+1))` and the explicit geometric tail bound (same
  machinery as A4 — **share it with Stage E's enclosure file** rather than
  writing it twice; the Plan agent should assign the shared file to exactly one
  worker).
- On each box `[a, b]` bound each monotone piece by its endpoint values.
  `s ↦ enat s` is decreasing on `(0,1]` and `s ↦ (1-s)Ppoly s` is bounded by
  endpoint evaluation of an explicit degree-6 polynomial; `s ↦ enat (s²)` is
  decreasing too. So the per-box bound is
  `Dfun ≥ (9/10)·enatLo(b²) - C·enatHi(a) + (log2Lo/10)·4·polyLo`.
- **Cover with a graded partition.** The true minimum is ≈ `6.1·10⁻⁵` near
  `s ≈ 0.686` and the margin decays to ≈ `2·10⁻⁶` at the right endpoint
  `s = 1 - 10⁻⁶`. So: coarse boxes on `[10⁻⁶, 0.5]`, boxes of width ~`10⁻³` on
  `[0.5, 0.9]` (resolving the `~10⁻⁴` interior minimum), and **geometrically
  refining** boxes on `[0.9, 1 - 10⁻⁶]` (e.g. breakpoints
  `1 - 10^{-k}` and dyadic refinements between them) so the box width shrinks
  faster than the margin. Do **not** attempt a uniform grid on `[0.9, 1-10⁻⁶]` —
  it would need ~10⁶ boxes.
- Generate the box list as an explicit `List ℚ` in a Lean file and prove one
  lemma per box; split across several files (`BoxesA.lean`, …) so workers can
  parallelize and the build stays incremental. Log the exact partition in
  `PROGRESS.md` so a later agent can refine it locally instead of restarting.

**G5 — `diagonal_estimate` (7).** Case split `s = 1` (G1), `s ≤ 10⁻⁶` (G2),
`s ≥ 1 - 10⁻⁶` and `s < 1` (G3), else G4. Note the conclusion is `0 ≤ Dfun s`
(non-strict) because of `s = 1`.

> **Cheat watch (Stage G).** This is the stage most likely to be quietly
> weakened. Forbidden: proving `0 ≤ Dfun s` only for `s` in a finite grid;
> proving it with `C` replaced by anything smaller than `81001/50000` (the
> constant is optimized against this very inequality — a smaller `C` makes G4
> easy and makes `strict_margin` false); enlarging the "small"/"large" ranges
> beyond `10⁻⁶` without re-proving G2/G3 at the new endpoints (G2 needs
> `-log s > 12`, i.e. `s < e⁻¹²`, and `10⁻⁶` is *not* far inside that — check
> the arithmetic, do not eyeball it); using `native_decide` for the box checks;
> and stating #43 with a strict `<` on the *hypotheses* (`10⁻⁶ < s`) instead of
> `≤`, which would leave a gap at the endpoint that #44's case split cannot
> close. Guardrails: `example : Dfun 1 = 0` (G1) and a spot check
> `example : 0 < Dfun (686/1000)` proved *by the same box machinery* — if the
> machinery cannot resolve the known minimum, it will not resolve the range.

### Stage H — the scalar inequality (`Proofs/Scalar/`) · MILESTONE

Goal: frozen theorems #45–#47. Depends on Stages F and G.

**H1 — `Phi_decomposition` (8a).** Unfold `Phi` and `Dfun` and `ring`. The only
content is `(9/10)·(1/9) = 1/10` and
`g(s)² + g(t)² - (g(s)-g(t))² = 2 g(s) g(t)`. Holds for **all** reals (no
hypotheses) — keep it that way.

**H2 — `Phi_nonneg` (support lemma).** `∀ s ∈ (0,1], ∀ t ∈ (0,1], 0 ≤ Phi s t`,
from H1 + `diagonal_estimate` (G5) + `off_diagonal_estimate` (F1).

**H3 — `pointwise_inequality` (8b).** Multiply H2 by `st > 0` and use
`s · enat s = Hnat s` (support lemma, needs `s ≠ 0`) and
`(st) · enat (st) = Hnat (st)`. Then handle `s = 0` or `t = 0` separately: both
sides are `0` because `Hnat 0 = 0` and the products vanish. This is why #46 is
stated on the **closed** `[0,1]²` while #45/H2 are on `(0,1]²`.

**H4 — `scalar_inequality` (8c).** Take `∑ i ∑ j w i w j (·)` of H3 at
`(S i, S j)` and divide by 2. The three algebraic facts needed:
`∑ᵢ∑ⱼ wᵢwⱼ (Sᵢ Sⱼ g(Sᵢ) g(Sⱼ)) = (∑ᵢ wᵢ Sᵢ g(Sᵢ))²` (`Finset.sum_mul_sum`),
`∑ᵢ∑ⱼ wᵢwⱼ (Sᵢ Hnat(Sⱼ)) = (∑ wS)(∑ w Hnat S)` (same), and symmetry of the
`s Hnat t + t Hnat s` term under swapping `i, j` (`Finset.sum_comm`). Use `hw1`
to see `∑ᵢ wᵢ = 1` where needed.

> **Cheat watch (Stage H).** #47 must quantify over **an arbitrary `Fintype ι`
> and an arbitrary weight vector**, not over a fixed `ι := Fin 2` or a uniform
> `w`. Do not add `0 < w i` (nonnegativity is what is stated, and Step 12
> instantiates with `unifW G`, which *is* `0` off `G`). Do not add
> `∀ i, 0 < S i`: the hypothesis is `S i ∈ [0,1]` and the `S i = 0` case is
> genuinely used (a coordinate can be deterministic). Do not replace the double
> sum by a second independent variable with an extra independence hypothesis —
> the product form *is* the independence, and Step 12 supplies exactly that
> shape. Guardrail: `example` instantiating #47 at `ι := Fin 1`, `w := 1`,
> `S := fun _ => 1/2` must compile.

### Stage I — the finitary entropy toolbox (`Proofs/FiniteEntropy/`)

Goal: frozen theorems #48–#53. Independent of Stages A–H — **start it in
iteration 1 in parallel with Stage A/B.**

**I1 — support lemmas.** `entropyW_nonneg` (each term `-w log w ≥ 0` for
`w ∈ [0,1]`); `law_nonneg`, `law_sum_eq_one`; `Hrv_le_log_card_of_support`
(Gibbs: `∑ pᵢ log(1/pᵢ) ≤ log N` by concavity of `log`, via
`Real.add_one_le_exp` or `ConcaveOn.le_map_sum`).

**I2 — `entropy_chain_rule` (#48).** Induct on the number of coordinates using
the definitional `H(Z,W) = H(W) + condHrv Z W` and the observation that
`pref n x = x` and `pref 0 x = fun _ => false`. The bookkeeping lemma is
`Hrv w (fun ω => pref (i+1) (X ω)) = Hrv w (fun ω => pref i (X ω)) +
condHrv w (fun ω => X ω i) (fun ω => pref i (X ω))`, which follows from
`law`-level injectivity of `(pref i x, x i) ↦ pref (i+1) x`.

**I3 — `condHrv_le_of_comp` (#49).** The information-theoretic core:
`H(Z | f(W)) ≥ H(Z | W)`. Prove via
`H(Z,W) - H(W) ≤ H(Z,f(W)) - H(f(W))`, i.e. submodularity, which reduces to
concavity of `Real.negMulLog` and Jensen on the finite conditional laws. Use
`Real.strictConcaveOn_negMulLog` / `ConcaveOn.le_map_sum`.

**I4 — `entropy_le_log_card` (#50).** From I1 (Gibbs) applied to `law w Z`
supported in `G`.

**I5 — `uniform_entropy_eq_log_card` (#51).** `law (unifW G) id = unifW G`, and
`entropyW (unifW G) = ∑_{x ∈ G} (1/N) log N = log N`.

**I6 — `prefix_entropy_decomposition` (#52).** Combine #48 (at `X := id`,
`w := unifW G`) with #51, plus the support lemma
`condHrv (unifW G) (fun x => x i) (fun x => pref i.val x) = HiFun G i` —
computing the conditional entropy as the prefix-weighted average of
`Hnat (pcond G i v)`. This last identity is the real work of the stage; it is
where `pcond`'s definition earns its keep.

**I7 — `freq_eq_one_sub_ES` (#53).** `∑ₓ unifW G x · pcond G i x` telescopes
over prefix classes to `Pr(Xᵢ = false) = 1 - Pr(Xᵢ = true)`, and
`Pr(Xᵢ = true) = |{x ∈ G : x i = true}|/|G|`. `Finset.sum_fiberwise`-style
grouping by `pref i.val`.

> **Cheat watch (Stage I).** Do not import `MeasureTheory` and re-derive these
> from Mathlib's measure-theoretic entropy — the frozen statements are about
> `Hrv`/`condHrv` as defined, and a "bridge" would have to be proved anyway.
> #49 must hold for an **arbitrary** `f`, not just for `f` injective (the whole
> point is that `orVec` is non-injective). #50 must not assume `G.Nonempty`
> implicitly by dividing by `G.card` — state and use the support hypothesis as
> frozen. Do not prove #52 only for `n ≥ 1`. Guardrails:
> `example : Hrv (unifW ({fun _ => false} : Finset (Fin 1 → Bool))) id = 0` and
> `example : Hrv (unifW (Finset.univ : Finset (Fin 1 → Bool))) id = Real.log 2`
> must compile.

### Stage J — the independent coupling (`Proofs/IndepCoupling/`)

Goal: frozen theorems #54–#55. Depends on Stage I.

**J1 — `indep_support_mem` (#54).** `windW G p ≠ 0` forces `unifW G p.1 ≠ 0` and
`unifW G p.2 ≠ 0`, hence `p.1, p.2 ∈ G`; then `UnionClosedCube` gives
`orVec p.1 p.2 ∈ G`.

**J2 — `indep_coupling_bound` (#55).** Chain:
`Hrv windW Z = ∑ᵢ condHrv windW (Zᵢ) (pref i ∘ Z)` (#48)
`≥ ∑ᵢ condHrv windW (Zᵢ) (fun p => (pref i p.1, pref i p.2))` (#49, since
`pref i (orVec x y) = orVec (pref i x) (pref i y)` is a function of the pair —
prove this `pref`/`orVec` commutation as a support lemma)
`= ∑ᵢ ∑ₓ ∑_y unifW x · unifW y · Hnat (pcond i x · pcond i y)` — the conditional
law of the union bit given both prefixes is Bernoulli with zero-probability
`pcond i x · pcond i y`, because the two bits are conditionally independent under
the product weight.

> **Cheat watch (Stage J).** The last equality is the load-bearing one: the
> union bit is `false` **iff both** bits are `false`, so the zero-probability is
> the *product*. Do not write `pcond i x + pcond i y - …` or any other
> "inclusion–exclusion" variant. Do not assume `G` union-closed in #55 — it is
> not needed there and adding it would be an added hypothesis. Do not assume
> `pcond` is nonzero. The commutation `pref i (orVec x y) = orVec (pref i x)
> (pref i y)` must be proved, not `sorry`-ed past — it is what makes #49
> applicable.

### Stage K — the shared-sign coupling (`Proofs/SharedCoupling/`)

Goal: frozen theorems #56–#59. Depends on Stages C (C1/C2), I, and — for the
final assembly of #59 — Stage C's `rank_one_product_bound`.

**K1 — `shared_isDist` (#56).** Nonnegativity: each `kern` value lies in `[0,1]`
by the factor bounds of C2 (`0 ≤ s ± λs(1-s) ≤ 1`), which requires
`pcond G i v ∈ [0,1]` (support lemma: it is a ratio of cardinalities).
Sum-to-one: `∑_{u,x,y} = 2⁻ⁿ ∑_u (∑_x ∏ᵢ kern …)(∑_y ∏ᵢ kern …)` and each inner
sum is `1` by induction on coordinates (`Finset.prod_range_succ` +
`∑_{b : Bool} kern … b = 1`).

**K2 — `shared_support_mem` (#57).** If `wshW G p ≠ 0` then every factor is
nonzero; by induction on coordinates the modified chain never leaves `G`'s
support (transitions with `pcond ∈ {0,1}` are unchanged, since
`s ± λ s(1-s) = s` there — this is the crux and deserves its own support lemma
`pmod_eq_of_mem_endpoints`). Hence `p.2.1, p.2.2 ∈ G` and `UnionClosedCube`
finishes.

**K3 — `shared_marginal_uniform` (#58).** Average the product formula over
`u ∈ (Fin n → Bool)`: distinct coordinates use distinct independent signs, so the
average factorizes (`Finset.prod_sum`/`Fintype.sum_prod_piFinset`), and
`(1/2)(kern … true b + kern … false b) = Pr(Xᵢ = b | X_{<i})`. Induct on prefix
length. Conclude `∑_u ∑_y wshW (u,x,y) = unifW G x`.
**Consequence (support lemma, needed by K4):** the law of `pcond G i ∘ (·.2.1)`
under `wshW` equals its law under `unifW`, so `∑_p wshW p · φ(pcond G i p.2.1) =
∑_x unifW G x · φ(pcond G i x)` for every `φ`; in particular `Egfun` computed on
the shared chain *is* `Egfun G i`.

**K4 — `shared_coupling_bound` (#59).** Chain:
`Hrv wshW Z ≥ ∑ᵢ condHrv wshW (Zᵢ) (fun p => (pref i p.2.1, pref i p.2.2, pref i p.1))`
(#48 + #49, `Z_{<i}` being a function of the two prefixes)
`= ∑ᵢ 𝔼 Hnat (qker Sᵢ Tᵢ)` — here the fresh sign `Uᵢ` is uniform and independent
of the conditioning, and averaging the product of the two modified
zero-probabilities over `σ = ±1` is **exactly `q_sign_average` (C1)**
`≥ ∑ᵢ log 2 · 𝔼[Sᵢ g(Sᵢ) · Tᵢ g(Tᵢ)]` (C7, pointwise inside the expectation)
`≥ ∑ᵢ log 2 · (𝔼[Sᵢ g(Sᵢ)])²` — conditionally on `U_{<i}` the two prefixes are
i.i.d. (the weight factorizes), so the conditional expectation of the product is
the square of the conditional expectation; then `𝔼[W²] ≥ (𝔼W)²`
(`Finset.sum_mul_sq_le_sq_mul_sq` with `hw1`) and the tower property
`= (Egfun G i)²` by K3.

> **Cheat watch (Stage K).** The `E[W²] ≥ (E W)²` step is where a wrong model
> silently gives a *false* theorem: if `X̃` and `Ỹ` are made independent
> unconditionally, or the sign is refreshed per coordinate *independently for the
> two chains*, the identity `E[S g(S) T g(T) | U_{<i}] = (E[S g(S) | U_{<i}])²`
> fails and the whole `1/10` term is unearned. Prove the conditional-i.i.d.
> factorization explicitly from `wshW`'s definition; do not hand-wave it.
> Also: #58 is not decorative — without it the `Egfun G i` in #59 would be a
> *different* quantity from the one Step 12 feeds to `scalar_inequality`, and the
> assembly would typecheck while proving nothing. Do not weaken #59 to
> `≥ 0`. Do not add a hypothesis `UnionClosedCube` to #56/#58/#59 beyond what is
> frozen (#57 has it because it genuinely needs it; #59 does not).

### Stage L — assembly and the headline (`Proofs/Assembly/`) · HEADLINE

Goal: frozen theorems #60–#61. Depends on Stages H, I, J, K.

**L1 — `frankl_cube` (#60).** Suppose for contradiction every `i` has
`3125 · |{x ∈ G : x i = true}| < 1196 · |G|`, i.e. frequency `< c`. By #53,
`ESfun G i > 1 - c` for every `i`. Then:
- `Hrv (windW G) Zind ≤ log |G|` by #54 + #50; likewise
  `Hrv (wshW G) Zsh ≤ log |G|` by #57 + #50 + #56.
- Hence `log |G| ≥ (9/10) Hrv windW Zind + (1/10) Hrv wshW Zsh`
  `≥ ∑ᵢ [(9/10) ∑ₓ∑_y unifW x unifW y Hnat(pcond i x · pcond i y) +
  (log 2/10)(Egfun G i)²]` by #55 and #59.
- For each `i` apply `scalar_inequality` (#47) with `ι := Fin n → Bool`,
  `w := unifW G`, `S := pcond G i` (hypotheses: `unifW ≥ 0`, `∑ unifW = 1` from
  `G.Nonempty`, `pcond ∈ [0,1]`), then `ESfun G i ≥ 1 - c`:
  the `i`-th bracket is `≥ Cval · ESfun G i · HiFun G i ≥ Cval(1-cval) · HiFun G i`
  (uses `HiFun G i ≥ 0`, a support lemma from `Hnat ≥ 0` on `[0,1]`).
- Sum over `i` and use #52: `log |G| ≥ Cval(1-cval) log |G| =
  (1 + 929/156250000) log |G|` by `strict_margin` (#1). Since `log |G| ≥ 0`, this
  forces `log |G| = 0`, i.e. `|G| = 1`.
- `G = {x₀}` with `x₀ ≠ fun _ => false` by hypothesis, so some `i` has
  `x₀ i = true`, giving frequency `1 > c` — contradicting the assumption at that
  `i`. (Also handles `n = 0`: then the hypothesis `∃ x ∈ G, x ≠ fun _ => false`
  is unsatisfiable, so the theorem is vacuous — do not case on `n` before
  noticing this.)

**L2 — the transfer (support code).** Enumerate the ground set
`U := F.sup id : Finset α` and let `n := U.card`, with an equiv
`ε : Fin n ≃ ↥U` from `U.equivFin`. Map `A ↦ (fun i => decide (ε i ∈ A))` and
push `F` forward to `G : Finset (Fin n → Bool)` via `Finset.image`. Prove as
support lemmas: (i) the map is injective on `F` (two members of `F` are subsets
of `U`, so they agree iff their indicator vectors agree); (ii) `G.card = F.card`;
(iii) `UnionClosed F → UnionClosedCube G` (`orVec` corresponds to `∪`);
(iv) `(G.filter (fun x => x i = true)).card = (F.filter (fun A => ε i ∈ A)).card`;
(v) `F.Nonempty → G.Nonempty`; (vi) `F ≠ {∅} ∧ F.Nonempty → ∃ x ∈ G, x ≠ fun _ => false`.

**L3 — `frankl_038272` (#61).** Apply #60 to the transferred `G`, obtain `i`, and
take `x := (ε i : α)`. Rewrite the cardinalities by L2(ii),(iv).

> **Cheat watch (Stage L).** The headline must be stated for an **arbitrary**
> `α` with `[DecidableEq α]` and an arbitrary `F` — not for `α := ℕ`, not with
> `[Fintype α]`, not with an extra `F ⊆ powerset U` hypothesis. The three
> hypotheses are exactly `UnionClosed F`, `F.Nonempty`, `F ≠ {∅}`; adding
> `2 ≤ F.card` (to dodge the `|F| = 1` endgame) or `∅ ∈ F` (a common convenience
> that is *not* in the sketch) is the cardinal cheat and will be caught. The
> conclusion is `1196 * F.card ≤ 3125 * (F.filter …).card` over `ℕ` — do not
> restate it as a real-number inequality about frequencies, and do not flip the
> constants. In L2, the injectivity of the indicator map must be **proved**; if it
> were wrong, `G.card < F.card` and the whole bound would be about a different
> family. Guardrail: `example : frankl_038272 ({{0}, {0,1}} : Finset (Finset ℕ)) …`
> instantiated at a small concrete union-closed family should produce a witness
> and the numeric inequality should `decide` — a cheap end-to-end sanity check.

### Discharge & Solution (after the frozen theorems are proved)

In `EntropyBound/Solution.lean`, restate each of the 61 frozen theorems
**verbatim** in `namespace EntropyBound.Solution` and set it `:= <name>_proof`
(the sorry-free declaration from `Proofs/`). In `EntropyBound/Discharge.lean`,
for each pair write `example : @<Frozen> = @<Proof> := rfl` — this compiles
**iff** the proof has *exactly* the frozen proposition (machine-checked
no-drift). `verify.py` checks both modules build and that
`#print axioms EntropyBound.Solution.<name>` is clean for every frozen name.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems, skeleton builds, pins recorded)
      │
      ├──────────────────────────────┐
      ▼                              ▼
Stage A (constants, Step 1)     Stage I (finitary entropy, Step 9)
      │                              │
      ▼                              ├──► Stage J (indep coupling, Step 10)
Stage B (toolbox, Step 2)            │
      │                              │
      ├──► Stage C (rank-one, Step 3) ───────────────► Stage K (shared coupling, Step 11)
      ├──► Stage D (profile speed, Step 4) ──┐        │
      └──► Stage E (entropy speed, Step 5) ──┤        │
                                             ▼        │
                                   Stage F (off-diag, Step 6)
      Stage G (diagonal, Step 7) ────────────┐        │
                                             ▼        │
                              Stage H  ⟵ MILESTONE (scalar inequality, Step 8)
                                             │        │
                                             └────┬───┘
                                                  ▼
                                   Stage L (assembly + HEADLINE, Step 12)
                                        (#print axioms clean)
                                                  │
                                                  ▼
                                  Discharge.lean + Solution.lean
```

**Parallelism.** Two long independent tracks exist from the very first
iteration: the **analysis track** (A → B → {C, D, E} → F, plus G) and the
**probability track** (I → {J, K}). With 4 workers, a good iteration-1 split is
`A`, `B` (first half), `I` (first half), and the shared enclosure API that both
E and G need. Once B lands, `C`, `D`, `E`, `G` are mutually independent and are
the natural 4-way split; `G` alone deserves a worker for many iterations.

**Milestone.** `scalar_inequality` (#47, end of Stage H) is the point at which a
citable, purely analytic result exists. Everything after it is bookkeeping.

**Hardest engineering, in order:** (1) **Stage G** (`diagonal_middle`) — the
tightest inequality, a graded box cover, and the log-enclosure API; (2)
**Stage E** (`Ader_lower_middle`) — same machinery, much more slack; (3)
**Stage K** — no hard analysis but the most intricate finite bookkeeping
(the conditional-i.i.d. factorization); (4) **Stage D** (`Gpoly_bernstein_*`) —
two enormous but mechanical `ring_nf` calls; watch compile times.

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them, and append any problem-
specific traps below them.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem must be hypothesis-free wherever the source claim is unconditional.
  Forbidden moves: adding `(h : …)` to a frozen statement; proving a `∀ x`
  (or `∀ x y`) claim only for generators / a finite subset and claiming the
  general case; replacing an equality with a one-sided inclusion. If a sub-proof
  seems to need an assumption, **derive it or restructure** — do not weaken the
  statement. (Downstream stages typically instantiate these at *arbitrary*
  elements, so a quiet weakening breaks the assembly silently.)

- **Keep every predicate the textbook definition — do not soften it.** Quantifiers
  must match the source exactly (e.g. "for all finite families" must not become
  "for `n ≤ 2`" or "for one fixed family"); genuine union-closedness must not be
  replaced by a cardinality-bounded or "I-couldn't-find-it" surrogate. A softened
  predicate can make the headline vacuous.

- **Get the modeling right once, in SETUP, and freeze it.** A dropped or extra
  relation/hypothesis in a frozen definition silently changes the object and can
  break the proof downstream. Validate the core modeling facts *before* freezing,
  with small guardrail `example`s (the ones named in each Cheat-watch box).

- **Discharge structural obligations once — never `sorry` them.** Inherit from
  Mathlib (`Fintype`, `DecidableEq`, `Finset.sum` API) rather than hand-rolling.
  If you feel the urge to `sorry` summability or a `Fintype` instance, you
  modeled the object wrong.

- **Keep the two entropy conventions distinct.** Everything in this project is
  **natural-log**. The base-2 quantities `h` and `e` of the paper appear only as
  `Hnat`/`enat` divided by `log 2`, and every frozen statement writes the
  `log 2` factor out. Mixing conventions produces statements that are off by
  `log 2` and still typecheck — the most likely *silent* error in Stages F–H.

- **`decide` budget — and `native_decide` is BANNED.** Small finite identities
  over `Bool`/`Fin n` are kernel-`decide`-able; a `∀` over `Fin n → Bool` with
  symbolic `n` is not. All the box checks in Stages E and G must be `norm_num`/
  `nlinarith` from explicit rational enclosures, never `decide` over a float
  grid. `native_decide` adds a compiler-trust axiom and would dirty
  `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen during proving (pinned in `scripts/frozen.sha256`). If a
  *definition* seems missing, it belongs in a `Proofs/` support file. If a
  *statement* seems wrong, stop and re-read `SKETCH.md` — the frozen statements
  are deliberately the minimal faithful rendering of the sketch, so a mismatch
  means a modeling bug to fix *before* re-freezing, not a hypothesis to bolt on.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no `native_decide`/
  `ofReduceBool`. `USER_NOTES.md` for this problem permits **no** assumed
  axioms, so `scripts/ALLOWED_AXIOMS.txt` is empty and **no `axiom` declaration
  may appear anywhere in the project.** In particular, the two
  interval-arithmetic obligations `Ader_lower_middle` (#35) and
  `diagonal_middle` (#43) must be genuinely proved. This is checked per theorem
  by `verify.py` (checks 2 and 4).

- **Assumed certificates go in as `axiom`s, never as hypotheses.** Not
  applicable here (none are permitted), but the rule stands: a certificate is
  never bolted onto a frozen theorem as a hypothesis `(h : …)`.

- **Problem-specific traps.**
  - **The `1/10` is unearned without conditional i.i.d.** The entire improvement
    over Gilmer's bound comes from the shared-sign term. If `wshW` is modeled so
    that `X̃, Ỹ` are independent *unconditionally*, Step 11d's Jensen step
    becomes an equality with the wrong quantity and the mixture no longer beats
    `H(X)`. Check the factorization explicitly (Stage K cheat watch).
  - **`λ` vs `λ²`.** `qker` carries `81/100 = λ²`; `pmod` carries `9/10 = λ`.
    Writing `9/10` in `qker` or `81/100` in `pmod` produces a plausible-looking
    but wrong kernel, and `q_sign_average` is the only thing that catches it.
  - **`C` is optimized against `diagonal_middle`.** There is no slack: the true
    minimum of `Dfun` is ≈ `6.1·10⁻⁵`. Any "simplification" that loses
    `10⁻⁴` of margin makes Stage G unprovable. Do not round `81001/50000`.
  - **The `s = 1` / `|F| = 1` boundary.** `diagonal_estimate` is `0 ≤ Dfun`, not
    `0 < Dfun` (equality at `s = 1`), and Step 12's contradiction genuinely needs
    the `|G| = 1` endgame with the `F ≠ {∅}` hypothesis. Do not "fix" the
    non-strictness by adding `s < 1`, and do not dodge the endgame by assuming
    `2 ≤ F.card`.
  - **`pcond` on unsupported prefixes.** It is `0` there by the junk-value
    convention. That is harmless *only* because it is always multiplied by
    `unifW G x` which is `0` off `G`. Any lemma that evaluates `pcond` outside a
    weighted sum is suspect.
  - **The ground-set transfer (L2).** If the indicator map is not injective on
    `F`, `G.card` shrinks and `frankl_cube` proves a statement about the wrong
    family while `frankl_038272` still typechecks. Injectivity is the one
    genuinely load-bearing lemma of the transfer — prove it, and guard it with
    the concrete `example` named in the Stage L cheat watch.
  - **Series index shifts.** Every `tsum` in `Defs.lean` starts at `m = 0` with
    shifted denominators. An off-by-one in `fser`, `Qser`, `Qder` or `Aser`
    changes the constants `1`, `2 log 2`, `8/9` and will surface only deep in
    Stage E. The guardrail `example`s (`Qser 0 = 1`, `Aser 1 = 1`, `fser 1 = 1`)
    catch all of them cheaply — run them in SETUP, before freezing.
