# Blueprint: Erdős Problem 477 — the thirteenth powers have a tiling complement in ℤ

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
Let `B = {m¹³ : m ∈ ℤ}` and `D = B − B`. The proof builds a set `A ⊆ ℤ` greedily:
enumerate `ℤ` as `n₁, n₂, …`; at step `j`, if `n_j` is not yet covered by `A + B`,
add `a_j := n_j − b_j` for a **good shift** `b_j = t₀¹³ ∈ B`, i.e. one for which no
already-chosen translate `a + B` can meet `a_j + B`. The single idea that makes it
work is that good shifts are abundant: for `c ∉ B`, the "bad" shifts `t` with
`|t| ≤ T` and `t¹³ − c ∈ D` number only `O_c(T^{5/6}) = o(T)`, because each bad `t`
produces an integer point on the diagonal surface `x¹³ + y¹³ + z¹³ = −c` inside a box
of side `≍ T^{13/12}` (the degree-12 cofactor `Q` in `u¹³ − v¹³ = (u−v)Q(u,v)` forces
`max(|u|,|v|) ≪_c T^{13/12}`), and Heath-Brown's determinant-method bound counts all
such points as `O_c(X^{10/13})` — legitimately, because the surface carries **no**
nonconstant rational parametrization over `ℚ` (Brownawell–Masser over function fields).
Since finitely many constraints exclude only `o(T)` of the `2T + 1` candidate shifts,
a good shift always exists.

- **Headline target (frozen theorem `erdos_477`).** `∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
  p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n` — every integer is *uniquely* `a + m¹³` with `a ∈ A`,
  `m ∈ ℤ`. Uniqueness is over the **pair** `(a, m)`; it is assembled from
  `greedy_tiling` (uniqueness of the `(a, b)`-representation with `b ∈ B`) plus
  `pow13_inj` (injectivity of `m ↦ m¹³`). Every object it mentions — `Bset`, `Dset` —
  is frozen in `Defs.lean`. The companion frozen theorems that supply the witness are
  `greedy_tiling` (the construction of `A`) and `good_shift_exists` (verification of
  the greedy criterion for `B`).
- **Recommended intermediate milestone (prove first):** `greedy_tiling` (Stage F).
  It is **pure combinatorics with zero number theory**, depends on nothing else, is
  a citable result on its own, and it is the only stage that can be closed on day one
  — which makes it the right de-risking first target. The *mathematical heart* is
  Stage C (function-field exclusion, Route A); the *hardest engineering* is also
  Stage C, followed by Stage D (the Heath-Brown bridge).
- **Setting / ground assumptions:** ambient ring `ℤ` for the arithmetic;
  inequalities are real (`ℝ`, with `Real.rpow` for the exponents `10/13`, `13/12`,
  `5/6`); the function-field layer lives over an algebraically closed field of
  characteristic zero (`RatFunc k`, and concretely `k = ℂ` when base-changing
  `ℚ`-forms). There is **no measure theory, no topology, no compactness**: the
  sketch deliberately replaces the paper's compactness constant `κ` by the explicit
  `κ = 1/2` (L1.1). Everything counted is a `Finset` or a `Set` with `Set.ncard`.
  Two — and exactly two — external results are **assumed as `axiom`s**, as mandated
  by `USER_NOTES.md`; nothing else may be assumed.

> **Why this is tractable.** Everything above the two axioms is elementary in
> substance: an explicit polynomial inequality (L1.1), a box-counting composition of
> exponents (`(T^{13/12})^{10/13} = T^{5/6}`), a pigeonhole (`o(T) < 2T + 1`), and a
> recursion on `ℕ` with two invariants (L4.1). The real risk is **not** deep
> mathematics; it is (i) **mis-stating the two axioms** — `USER_NOTES.md` demands
> that they be exact transcriptions of the paper's Theorems 2.1 and 2.2 in *full
> generality*, so every convenient specialization the proofs want must be *derived*
> in Lean, not assumed; (ii) **silently taking Route B** — the elementary Vandermonde
> exclusion of degree-≤1 parametrizations is much easier than the paper's
> function-field argument, and a proof that quietly uses it will compile and look
> correct while being unfaithful (this is exactly what the `mandatory_axioms` check
> 4b exists to catch); and (iii) **exponent slack** — replacing the box side
> `X ≍ T^{13/12}` by anything as crude as `O(T²)` destroys `o(T)` and the whole
> argument collapses at Stage G, silently, only at the end.

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is to produce a compiling skeleton in which **every
`Definition` and every `Theorem` statement is written and frozen**, with all
proofs `:= sorry`. Once frozen, `Defs.lean` and `Theorems.lean` are **never
edited again** during the proving phase. Everything proved later lives in
support files and may not change a single character of the frozen statements.

### 1. Create the Lean project

```bash
cd <project-dir>
lake +leanprover/lean4:v4.31.0 new Erdos477 math
# pin Mathlib in lakefile + lake-manifest to the rev matching lean-toolchain v4.31.0
#   (edit lakefile.toml: require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "<rev>")
lake update -R mathlib      # only if the manifest needs regenerating
lake exe cache get
lake build                  # must succeed on the bare skeleton before anything else
```

`lean-toolchain` must contain exactly `leanprover/lean4:v4.31.0` and the Mathlib
rev must be the one whose own `lean-toolchain` matches it; if `lake exe cache get`
misses, the pin is wrong — fix the pin, never build Mathlib from source.

Layout:

```
<project-dir>/
  Erdos477/
    Defs.lean          -- FROZEN after this stage: every object the proof needs + the 2 axioms
    Theorems.lean      -- FROZEN after this stage: the 16 frozen theorem statements (sorry)
    Proofs/
      Elementary/      -- Stage A: L0.1–L0.6, the trivial-but-everywhere facts
      Cofactor/        -- Stage B: L1.1–L1.2, the explicit κ = 1/2 cofactor bound
      FunctionField/   -- Stage C: BM4-for-forms, Lemma 3.1, Cor 3.2, L2.1 (Route A)
      HeathBrown/      -- Stage D: the specialization bridge, axiom → diagonal count
      BadShift/        -- Stage E: Prop 4.1, |S_c(T)| ≤ K_c · T^{5/6}
      Greedy/          -- Stage F: Lemma 5.1, the greedy tiling criterion
      Assembly/        -- Stage G: Prop 5.2 and the headline
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `Erdos477.Solution`, proven (clean names)
  Erdos477.lean        -- imports everything
  SKETCH.md            -- the problem + NL proof sketch (math source of truth)
  BLUEPRINT.md         -- this file
  USER_NOTES.md        -- user's special instructions / permitted assumed-axioms
  PROGRESS.md          -- append-only work log (workers write here; see §4)
  TASKS.md             -- append-only delegation log (the Plan agent writes here; see §5)
  REVIEW.md            -- append-only audit log (the Review agent writes here; see §5)
  scripts/
    verify.py          -- the verification harness
    frozen.sha256      -- SHA-256 pins of Defs.lean + Theorems.lean
    ALLOWED_AXIOMS.txt -- axiom allowlist init.py derives from USER_NOTES.md
    harness.json       -- project / problem / frozen names / mandatory axioms
```

All support declarations live in `namespace Erdos477` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface;
`Solution.lean` re-exposes each as `Erdos477.Solution.<name>` after it is proven,
and `Discharge.lean` machine-checks that each proof has *exactly* the frozen type
(`@Frozen = @Proof := rfl`).

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.** For each
definition record the Lean rendering and the **MODELING DECISION**.

`Defs.lean` opens with

```lean
import Mathlib

namespace Erdos477

open scoped Classical
open MvPolynomial Polynomial
```

#### 2.1 The arithmetic objects

```lean
/-- `B` — the thirteenth powers. SKETCH §0. -/
def Bset : Set ℤ := {b | ∃ m : ℤ, b = m ^ 13}

/-- `D = B − B` — differences of thirteenth powers. SKETCH §0. -/
def Dset : Set ℤ := {d | ∃ u v : ℤ, d = u ^ 13 - v ^ 13}

/-- `Q(u,v) = ∑_{i=0}^{12} uⁱ v^{12−i}` — the degree-12 cofactor. SKETCH §4. -/
noncomputable def Qcof (u v : ℝ) : ℝ := ∑ i ∈ Finset.range 13, u ^ i * v ^ (12 - i)

/-- `S_c(T) = {t : |t| ≤ T ∧ t¹³ − c ∈ D}` — the bad shifts. SKETCH §0. -/
noncomputable def badShifts (c T : ℤ) : Finset ℤ :=
  (Finset.Icc (-T) T).filter (fun t => t ^ 13 - c ∈ Dset)

/-- Integer points of `x¹³ + y¹³ + z¹³ = M` in the box of side `X`. SKETCH §6 Step 4. -/
def diagSolutions (M : ℤ) (X : ℝ) : Set (ℤ × ℤ × ℤ) :=
  {v | v.1 ^ 13 + v.2.1 ^ 13 + v.2.2 ^ 13 = M ∧
       |(v.1 : ℝ)| ≤ X ∧ |(v.2.1 : ℝ)| ≤ X ∧ |(v.2.2 : ℝ)| ≤ X}
```

- **MODELING DECISION (`Bset`, `Dset`).** Both are `Set ℤ` given by the *existential*
  form of SKETCH §0, not by `Set.image` / `Set.sub`. Rejected: `Dset := Bset - Bset`
  (Mathlib's pointwise `Sub` on sets) — it is defeq-fragile and every downstream
  `obtain` would go through `Set.mem_sub`. The equivalence
  `Dset = {d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y}` is a **support lemma** in
  Stage A (`Dset_eq_sub_Bset`), needed to instantiate `greedy_tiling` at `B := Bset`.
- **MODELING DECISION (`Qcof` over `ℝ`).** `Q` is stated and proved over `ℝ` (L1.1 is
  a real inequality with `κ = 1/2`); integer instances arrive by casting. Rejected:
  a `ℤ`-valued `Q` — L1.1's proof divides by `u` (`s := v/u`), which needs a field.
  The exponent `12 - i` is **ℕ-subtraction**, safe because `i ∈ range 13`.
- **MODELING DECISION (`badShifts` as a `Finset`).** `Finset.filter` needs
  `DecidablePred (fun t => t ^ 13 - c ∈ Dset)`, which is not decidable; the file
  is compiled under `open scoped Classical`, so the instance is `Classical.dec`
  and `badShifts` is `noncomputable`. Rejected: `Set.ncard` of a `Set ℤ` — the
  pigeonhole in Stage G wants `Finset.card_lt_card` / `Finset.card_biUnion_le`,
  which are far smoother on `Finset`. Consequence a later stage must respect:
  never `decide` anything about `badShifts`; membership is unfolded via
  `Finset.mem_filter` + `Finset.mem_Icc`.
- **MODELING DECISION (`diagSolutions` on `ℤ × ℤ × ℤ`, box in `ℝ`).** The box
  condition is stated on the **real** casts so that the non-integer bound
  `X = C_c · T^{13/12}` can be used directly with no floor/ceiling bookkeeping.

#### 2.2 The Heath-Brown objects (needed to state Axiom 1 in full generality)

```lean
/-- A nonsingular ternary form of degree `k`: homogeneous of degree `k`, and its
    gradient vanishes only at the origin (tested over `ℂ`, an algebraically closed
    field of characteristic 0). Paper Thm 2.2 / SKETCH §3. -/
def IsNonsingularTernaryForm (F : MvPolynomial (Fin 3) ℤ) (k : ℕ) : Prop :=
  F.IsHomogeneous k ∧
    ∀ z : Fin 3 → ℂ, (∀ i, MvPolynomial.aeval z (MvPolynomial.pderiv i F) = 0) → z = 0

/-- `x` lies on a nonconstant polynomial parametrization of `F = N` of degree ≤ `d`.
    Paper Thm 2.2 ("a solution *lies on* it if it equals `(p₁(t),p₂(t),p₃(t))`"). -/
def LiesOnPolyParam (F : MvPolynomial (Fin 3) ℤ) (N : ℤ) (d : ℕ) (x : Fin 3 → ℤ) : Prop :=
  ∃ p : Fin 3 → Polynomial ℤ,
    (¬ ∀ i, (p i).natDegree = 0) ∧                       -- not all constant
    (∀ i, (p i).natDegree ≤ d) ∧                          -- degree at most d
    MvPolynomial.aeval p F = Polynomial.C N ∧             -- F(p₁,p₂,p₃) = N identically
    ∃ t : ℤ, ∀ i, (p i).eval t = x i                      -- x lies on it

/-- The set Heath-Brown counts: solutions in the box that do NOT lie on such a
    parametrization. -/
def hbSolutions (F : MvPolynomial (Fin 3) ℤ) (N : ℤ) (d : ℕ) (X : ℝ) : Set (Fin 3 → ℤ) :=
  {x | MvPolynomial.eval x F = N ∧ (∀ i, |(x i : ℝ)| ≤ X) ∧ ¬ LiesOnPolyParam F N d x}
```

- **MODELING DECISION (nonsingularity via the gradient over `ℂ`).** "Nonsingular
  ternary form" = the projective plane curve `F = 0` is smooth = the only common
  zero of `∂F/∂X₁, ∂F/∂X₂, ∂F/∂X₃` over an algebraically closed field of char 0 is
  the origin. `ℂ` is that field. Rejected: `AlgebraicClosure ℚ` (same content, worse
  API), and "the Jacobian ideal is `(X₁,X₂,X₃)`-primary" (equivalent, unusable).
  Note Euler's relation makes "`F` also vanishes" automatic in char 0, so we do not
  add it — adding it would be a (harmless but non-minimal) extra condition.
- **MODELING DECISION (`natDegree` as "degree", `natDegree = 0` as "constant").**
  `Polynomial.natDegree 0 = 0`, so the zero polynomial counts as constant — exactly
  the convention SKETCH §9.5(7) fixes. "Not all constant" is
  `¬ ∀ i, (p i).natDegree = 0`.
- **MODELING DECISION (`aeval` for substitution).** `MvPolynomial.aeval p F` with
  `p : Fin 3 → Polynomial ℤ` is the substitution `F(p₁,p₂,p₃) : Polynomial ℤ`; the
  identity "`= N` identically" is `= Polynomial.C N`. For integer points,
  `MvPolynomial.eval x F : ℤ`.
- **MODELING DECISION (`Fin 3 → ℤ` for `hbSolutions`, `ℤ × ℤ × ℤ` for
  `diagSolutions`).** The axiom is about a general ternary form, so its natural
  index type is `Fin 3`; the downstream arithmetic wants the triple. Stage D owns
  the transport lemma (`hbSolutions_diag_equiv`) between them. **Do not conflate
  them** — this is the most likely silent bug in Stage D.

#### 2.3 The function-field objects (needed to state Axiom 2 in full generality)

```lean
/-- Points of `ℙ¹_k`: `some a` is `[a : 1]`, `none` is the point at infinity `[1 : 0]`. -/
abbrev P1Point (k : Type*) := Option k

/-- `ord_P f` for `f ∈ k(t)^×`: at a finite point the difference of root
    multiplicities of numerator and denominator; at infinity `−intDegree`. -/
noncomputable def ordP {k : Type*} [Field k] : P1Point k → RatFunc k → ℤ
  | none,   f => - f.intDegree
  | some a, f => (f.num.rootMultiplicity a : ℤ) - (f.denom.rootMultiplicity a : ℤ)

/-- `f` is constant. -/
def IsConstRF {k : Type*} [Field k] (f : RatFunc k) : Prop := ∃ a : k, f = RatFunc.C a

/-- `f` is an `S`-unit: nonzero, with all zeros and poles inside `S`. -/
def IsSUnitOn {k : Type*} [Field k] (S : Finset (P1Point k)) (f : RatFunc k) : Prop :=
  f ≠ 0 ∧ ∀ P ∉ S, ordP P f = 0

/-- `min_{1 ≤ i ≤ r} ord_P(uᵢ)`. -/
noncomputable def minOrd {k : Type*} [Field k] {r : ℕ}
    (u : Fin r → RatFunc k) (P : P1Point k) : ℤ :=
  if h : (Finset.univ : Finset (Fin r)).Nonempty then
    Finset.univ.inf' h (fun i => ordP P (u i)) else 0

/-- The projective height `H(u₁ : ⋯ : u_r) = − ∑_{P ∈ ℙ¹_k} min_i ord_P(uᵢ)`. -/
noncomputable def projHeight {k : Type*} [Field k] {r : ℕ} (u : Fin r → RatFunc k) : ℤ :=
  - ∑ᶠ P : P1Point k, minOrd u P
```

- **MODELING DECISION (`P1Point k := Option k`).** `k` is algebraically closed in
  every use, so the closed points of `ℙ¹_k` are exactly `k ∪ {∞}`. Rejected:
  `Projectivization k (Fin 2 → k)` (correct but every `ord_P` computation would go
  through a quotient) and "monic irreducible polynomials + ∞" (needs
  `IsAlgClosed.monic_irreducible_iff` gymnastics). The `Option` model makes `ordP`
  a two-line definition and makes `Finset (P1Point k)` a usable `S`.
- **MODELING DECISION (`ordP` via `num`/`denom`/`intDegree`).** `RatFunc.num` and
  `RatFunc.denom` are the coprime normalized representatives, so
  `rootMultiplicity` differences give the true order; `RatFunc.intDegree f =
  f.num.natDegree − f.denom.natDegree`, so `ord_∞ = −intDegree`. This chart
  convention (`some a ↔ [a : 1]`, `none ↔ [1 : 0]`) **must** be the same one used by
  `IsProjZero` below — Stage C's height computation breaks silently otherwise.
- **MODELING DECISION (`minOrd` guarded by `dif`).** `ℤ` has no `⊤`, so
  `Finset.inf` is unavailable and `Finset.inf'` needs nonemptiness. The `dif`
  makes `minOrd` total, with junk value `0` only at `r = 0`, which every use
  excludes (`3 ≤ r`). Rejected: an `[NeZero r]` instance binder (would pollute the
  axiom statement) and `sInf` on `ℤ` (relies on a different junk convention).
- **MODELING DECISION (`∑ᶠ` in `projHeight`).** The height is written as the sum
  over **all** of `ℙ¹_k`, exactly as the paper displays it; `finsum` is the honest
  rendering (it is `0` on a non-finitely-supported summand, which the `S`-unit
  hypothesis rules out). Stage C's first support lemma is
  `projHeight_eq_sum_over_S : (∀ i, IsSUnitOn S (u i)) → projHeight u = - ∑ P ∈ S, minOrd u P`.
  Rejected: defining the height as a sum over `S` — that would bake a hypothesis
  into the definition and make the axiom weaker than the paper's.

#### 2.4 Binary forms on `ℙ¹` (needed for the derived BM4-for-forms lemma)

```lean
/-- `P` is a projective zero of a binary form. Same chart convention as `ordP`. -/
def IsProjZero {k : Type*} [Field k] (Φ : MvPolynomial (Fin 2) k) : P1Point k → Prop
  | none   => MvPolynomial.eval ![1, 0] Φ = 0
  | some a => MvPolynomial.eval ![a, 1] Φ = 0

/-- The number of distinct projective zeros of a binary form. -/
noncomputable def projZeroCount {k : Type*} [Field k] (Φ : MvPolynomial (Fin 2) k) : ℕ :=
  {P : P1Point k | IsProjZero Φ P}.ncard

/-- The forms have no common zero away from the origin. -/
def NoCommonProjZero {k : Type*} [Field k] {n : ℕ} (A : Fin n → MvPolynomial (Fin 2) k) : Prop :=
  ∀ v : Fin 2 → k, (∀ i, MvPolynomial.eval v (A i) = 0) → v = 0

/-- All the forms are scalar multiples of one common form — i.e. `[A₀ : ⋯ : A_{n−1}]`
    is a *constant* map `ℙ¹ → ℙⁿ⁻¹`. -/
def IsConstantFamily {K : Type*} [Field K] {n : ℕ} (A : Fin n → MvPolynomial (Fin 2) K) : Prop :=
  ∃ (a : Fin n → K) (Φ : MvPolynomial (Fin 2) K), ∀ i, A i = MvPolynomial.C (a i) * Φ

/-- `[A₀ : A₁ : A₂ : A₃] : ℙ¹_ℚ → ℙ³_ℚ` is a morphism landing in
    `X_N : X¹³ + Y¹³ + Z¹³ = N·W¹³`. SKETCH §5.2.2 setup. -/
def IsParamOfXN (N : ℚ) (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ) : Prop :=
  1 ≤ e ∧ (∀ i, (A i).IsHomogeneous e) ∧
    NoCommonProjZero (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (A i)) ∧
    A 0 ^ 13 + A 1 ^ 13 + A 2 ^ 13 = MvPolynomial.C N * A 3 ^ 13
```

- **MODELING DECISION (binary forms as `MvPolynomial (Fin 2) k` + `IsHomogeneous`).**
  Rejected: `Polynomial k` with an implicit homogenization (would force degree
  bookkeeping by hand at `∞`) and `⨁ homogeneousSubmodule` (heavier API for no gain).
- **MODELING DECISION ("no common zero" tested over `ℂ` for `ℚ`-forms).** A morphism
  `ℙ¹_ℚ → ℙ³` must have no common zero **over `ℚ̄`**, not over `ℚ`; testing over `ℂ`
  is the same condition and gives an `IsAlgClosed` + `CharZero` field with the best
  Mathlib support. The base change is written explicitly as
  `MvPolynomial.map (algebraMap ℚ ℂ)` — a reviewer must be able to see it.
  **Do not** weaken this to "no common zero over `ℚ`": that is a strictly weaker
  hypothesis and would make `IsParamOfXN` admit non-morphisms.
- **MODELING DECISION (`IsConstantFamily` for "constant morphism" and for "all
  ratios constant").** For forms of a common degree with no common zero, "the
  morphism is constant" and "all ratios `Aᵢ/Aⱼ` are constant" are the same
  condition, and both are `IsConstantFamily`. One predicate serves both the
  BM4-for-forms lemma (paper Thm 2.1's "not all constant") and Lemma 3.1
  ("nonconstant morphism"), which keeps Stage C from drifting between two
  almost-identical notions.

#### 2.5 The two assumed axioms (permitted by `USER_NOTES.md`)

These are the **only** `axiom` declarations allowed anywhere in the project; their
fully-qualified names go into `scripts/ALLOWED_AXIOMS.txt`. Each is a transcription
of the cited theorem **in the paper's full generality** — no specialization, no
reformulation, no added or dropped hypotheses. Every specialized form the proofs
consume is a **proof obligation** downstream (Stages C and D), never an assumption.

```lean
/-- **Paper Theorem 2.1** (Brownawell–Masser on `ℙ¹`; genus-zero case of
    Brownawell–Masser 1986, height convention and constants as in Corvaja–Zannier
    2011). Stated for general `r ≥ 3`, as required by `USER_NOTES.md`; the name
    records that the four-term instance is the one Mathlib lacks. -/
axiom brownawell_masser_P1_four_term
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    (S : Finset (P1Point k)) (r : ℕ) (hr : 3 ≤ r) (u : Fin r → RatFunc k)
    (hunit : ∀ i, IsSUnitOn S (u i))
    (hnonconst : ¬ ∀ i, IsConstRF (u i))
    (hsum : ∑ i, u i = 0)
    (hsub : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, u i ≠ 0) :
    projHeight u ≤ (Nat.choose (r - 1) 2 : ℤ) * ((S.card : ℤ) - 2)

/-- **Paper Theorem 2.2** (Heath-Brown, *Sums and differences of three k-th powers*,
    J. Number Theory 129 (2009), Theorem 2). Stated for a general nonsingular ternary
    form of degree `k ≥ 3`, with the genuine "does not lie on a nonconstant polynomial
    parametrization of degree ≤ ⌊k/10⌋" exclusion, the side condition `|N| ≪_F X`
    (explicit constant `A`) and the conclusion `O_F(X^{10/k})` (explicit constant `C`,
    depending only on `F`, `k` and `A`). The determinant method is out of reach of
    current formalization technology. -/
axiom heath_brown_diagonal_13
    (F : MvPolynomial (Fin 3) ℤ) (k : ℕ) (hk : 3 ≤ k)
    (hF : IsNonsingularTernaryForm F k) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℤ, N ≠ 0 → ∀ X : ℝ, 1 ≤ X → |(N : ℝ)| ≤ A * X →
      ((hbSolutions F N (k / 10) X).ncard : ℝ) ≤ C * X ^ ((10 : ℝ) / (k : ℝ))
```

- **MODELING DECISION (asymptotics as explicit constants, in this quantifier
  order).** `USER_NOTES.md` fixes the meaning: "the implied constant of the
  conclusion may depend on `F` and on the implied constant assumed in `|N| ≪_F X`,
  and on nothing else". Hence `A` is bound **before** `∃ C`, and `N` and `X` are
  bound **after** it — `C` is uniform in `N` and `X`, which is exactly
  Heath-Brown's uniformity and exactly what Stage D needs. Swapping `∃ C` inside
  `∀ N` would be a *weakening* of the axiom (and, ironically, would also break the
  bridge). Reviewers: check this quantifier order first.
- **MODELING DECISION (`⌊k/10⌋ = k / 10`).** Natural-number division is floor
  division; `13 / 10 = 1` by `norm_num`.
- **MODELING DECISION (the axiom names).** Fixed verbatim by `USER_NOTES.md`:
  `Erdos477.heath_brown_diagonal_13` and
  `Erdos477.brownawell_masser_P1_four_term`. Despite the names, **neither is
  specialized** — `heath_brown_diagonal_13` is the general-form Theorem 2.2 and
  `brownawell_masser_P1_four_term` is the general `r ≥ 3` Theorem 2.1. Do not
  "fix" the names to match the statements; `harness.json`, `ALLOWED_AXIOMS.txt`
  and check 4b all key on them.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook notion**,
> quantified exactly as the source states it.
> — `IsNonsingularTernaryForm` must quantify over **all** of `ℂ³`, not over `ℚ³`
>   or over the projective points only; a nonsingularity test over `ℚ` would make
>   the axiom apply to singular forms and is a *strengthening of the axiom*, i.e.
>   an assumption of something false.
> — `LiesOnPolyParam` must keep **both** "not all constant" and the incidence
>   clause `∃ t, ∀ i, (p i).eval t = x i`. Dropping the incidence clause turns
>   `hbSolutions` into "all solutions" and makes the axiom false; dropping "not all
>   constant" makes every solution lie on a (constant) parametrization and makes
>   `hbSolutions` empty, i.e. the axiom vacuous.
> — `IsSUnitOn` must include `f ≠ 0` (an `S`-unit of `k(t)^×` is invertible).
> — `projHeight` must sum over **all** `P : P1Point k` (`∑ᶠ`), not over `S`.
> — `IsParamOfXN` must keep `1 ≤ e` (a morphism from `ℙ¹`, not a point) and the
>   `NoCommonProjZero` clause **over `ℂ`**.
> — Do **not** add a `Decidable`/`Fintype` hypothesis anywhere to make something
>   computable; classical logic is available and free.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each statement must render a claim of
`SKETCH.md` **faithfully and minimally** — no weakening, no added hypotheses, no
specializing a universal to examples, no proving a special case and naming it the
general one — and must carry a **stable, binding name** (referenced by
`verify.py`, `Discharge.lean`, `Solution.lean`, `harness.json` and `init.py`).

```lean
import Erdos477.Defs

namespace Erdos477

open scoped Classical
open MvPolynomial Polynomial

-- ===== Stage A — elementary layer (SKETCH §2) =====

/-- L0.1. -/
theorem zero_mem_Bset : (0 : ℤ) ∈ Bset := sorry

/-- L0.2 — `D` is symmetric. -/
theorem Dset_neg_mem (d : ℤ) (hd : d ∈ Dset) : -d ∈ Dset := sorry

/-- L0.3 — `m ↦ m¹³` is injective on `ℤ`. -/
theorem pow13_inj : Function.Injective (fun m : ℤ => m ^ 13) := sorry

/-- L0.4 — an integer with a rational 13th root is a 13th power. -/
theorem mem_Bset_of_rat_pow13 (c : ℤ) (q : ℚ) (h : q ^ 13 = (c : ℚ)) : c ∈ Bset := sorry

/-- L0.6 — membership reformulation for bad shifts. -/
theorem sub_pow13_mem_Dset_iff (c t : ℤ) : c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset := sorry

-- ===== Stage B — the cofactor bound (SKETCH §4) =====

/-- L1.1 — explicit cofactor bound with `κ = 1/2`. -/
theorem Qcof_ge_half_max_pow12 (u v : ℝ) : (1 / 2) * max |u| |v| ^ 12 ≤ Qcof u v := sorry

/-- L1.2 — gap bound for distinct integer 13th powers. -/
theorem abs_pow13_sub_pow13_ge (u v : ℤ) (h : u ≠ v) :
    (1 / 2) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := sorry

-- ===== Stage C — function-field exclusion, Route A (SKETCH §5.2) =====

/-- Brownawell–Masser for homogeneous binary forms, **derived** from
    `brownawell_masser_P1_four_term` via the height computation of SKETCH §5.2.1
    (`H(A₁ : ⋯ : A_r) = d` for common-degree-`d` forms with no common zero).
    Instantiated at `r = 4` (Case A) and `r = 3` (Case B) inside Lemma 3.1. -/
theorem bm_forms_height_bound {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (r d : ℕ) (hr : 3 ≤ r) (A : Fin r → MvPolynomial (Fin 2) k)
    (hA0 : ∀ i, A i ≠ 0) (hhom : ∀ i, (A i).IsHomogeneous d)
    (hcop : NoCommonProjZero A) (hsum : ∑ i, A i = 0)
    (hsub : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, A i ≠ 0)
    (hnc : ¬ IsConstantFamily A) :
    (d : ℤ) ≤ (Nat.choose (r - 1) 2 : ℤ) * ((projZeroCount (∏ i, A i) : ℤ) - 2) := sorry

/-- Paper Lemma 3.1, the half the development uses: if `N ∉ ℚ¹³` then `X_N` carries
    no nonconstant `ℚ`-rational parametrized curve. SKETCH §5.2.2. -/
theorem no_nonconstant_param_of_not_pow13 (N : ℚ) (hN : N ≠ 0)
    (hpow : ¬ ∃ d : ℚ, d ^ 13 = N) (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ)
    (hA : IsParamOfXN N e A) : IsConstantFamily A := sorry

/-- Paper Corollary 3.2: for `c ∉ B` the affine surface `u¹³ − v¹³ − t¹³ = −c` has no
    nonconstant rational parametrization over `ℚ`. SKETCH §5.2.3. -/
theorem no_rational_param_of_not_mem_Bset (c : ℤ) (hc : c ∉ Bset)
    (f g h : RatFunc ℚ) (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h := sorry

/-- L2.1 — the exclusion hypothesis Heath-Brown needs, obtained from Corollary 3.2
    by homogenizing (SKETCH §5.2.3, "derivation of L2.1"). -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) (p₁ p₂ p₃ : Polynomial ℤ)
    (hsum : p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c))
    (h₁ : p₁.natDegree ≤ 1) (h₂ : p₂.natDegree ≤ 1) (h₃ : p₃.natDegree ≤ 1) :
    p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := sorry

-- ===== Stage D — the Heath-Brown bridge (SKETCH §3, now a THEOREM) =====

/-- The sketch's "AXIOM HB" is **proved** here from the general
    `heath_brown_diagonal_13` (`USER_NOTES.md`: the specialization is a proof
    obligation, not an assumption). SKETCH §3, points 1–4. -/
theorem hb_diagonal_count (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ((diagSolutions M X).ncard : ℝ) ≤ K * X ^ ((10 : ℝ) / 13) := sorry

-- ===== Stage E — the bad-shift estimate (SKETCH §6) =====

/-- P3.1 = paper's Proposition 4.1: `|S_c(T)| ≤ K_c · T^{5/6}`. -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := sorry

-- ===== Stage F — the greedy tiling criterion (SKETCH §7) =====

/-- L4.1 = paper's Lemma 5.1, for an arbitrary `B ⊆ ℤ`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
      ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := sorry

-- ===== Stage G — assembly (SKETCH §8) =====

/-- P5.1 = paper's Proposition 5.2: `B` satisfies the greedy criterion. -/
theorem good_shift_exists (C : Finset ℤ) (hC : ∀ c ∈ C, c ∉ Bset) :
    ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := sorry

/-- **HEADLINE** — Theorem 1.1 / Erdős Problem 477. -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := sorry

end Erdos477
```

Mapping to `SKETCH.md`, one line each:

| Frozen theorem                        | SKETCH step |
| ------------------------------------- | ----------- |
| `zero_mem_Bset`                       | §2 L0.1 |
| `Dset_neg_mem`                        | §2 L0.2 |
| `pow13_inj`                           | §2 L0.3 |
| `mem_Bset_of_rat_pow13`               | §2 L0.4 |
| `sub_pow13_mem_Dset_iff`              | §2 L0.6 |
| `Qcof_ge_half_max_pow12`              | §4 L1.1 |
| `abs_pow13_sub_pow13_ge`              | §4 L1.2 |
| `bm_forms_height_bound`               | §5.2.1 (derived from Axiom 2) |
| `no_nonconstant_param_of_not_pow13`   | §5.2.2 Lemma 3.1 |
| `no_rational_param_of_not_mem_Bset`   | §5.2.3 Corollary 3.2 |
| `no_linear_param`                     | §5 L2.1 (via Route A) |
| `hb_diagonal_count`                   | §3 "AXIOM HB", derived from Axiom 1 |
| `badShift_bound`                      | §6 P3.1 |
| `greedy_tiling`                       | §7 L4.1 |
| `good_shift_exists`                   | §8.1 P5.1 |
| `erdos_477`                           | §8.2 Theorem 1.1 |

**Why these 16.** The *heart* is the pair `bm_forms_height_bound` →
`no_nonconstant_param_of_not_pow13`: it converts the paper's Theorem 2.1 into a
usable exclusion statement and is the only place where genuine function-field
mathematics happens. `hb_diagonal_count` and `badShift_bound` are the *analytic
spine*: they turn the axiom into the `o(T)` count, and every exponent in the
problem lives there. `greedy_tiling` is the *combinatorial engine*, independent of
everything else. `good_shift_exists` and `erdos_477` are the *payoff*: pigeonhole
plus assembly. Stages A and B are support lemmas, frozen because the sketch states
them as numbered lemmas and because `pow13_inj`, `Dset_neg_mem` and
`sub_pow13_mem_Dset_iff` are each used in three different stages — freezing them
prevents three incompatible ad-hoc versions.

Two deliberate scope calls, recorded here so no later agent "fixes" them:

1. **Lemma 3.1's classification half is not frozen.** SKETCH §5.2.2 also classifies
   the `N = d¹³` case (the three lines). Nothing downstream uses it; the frozen
   statement is the implication actually consumed by Corollary 3.2. The Case-D
   analysis that would prove it still appears as a *support* lemma inside Stage C,
   because Case D is part of the proof of the frozen half.
2. **`no_linear_param` keeps the degree hypotheses `h₁ h₂ h₃`** because SKETCH §5
   L2.1 and §9.2 state it that way, and because that is the exact shape
   `hb_diagonal_count` consumes. Route A actually proves the stronger
   hypothesis-free version; that is a bonus, not a licence to change the frozen
   statement. The hypotheses being unused in the final proof is expected and fine.

**Re-build gate.** After freezing, `lake build` must succeed (everything is
`sorry`, but the *statements* must typecheck). Do not write a line of proof until
the skeleton compiles. Record the SHA-256 of `Defs.lean` and `Theorems.lean` into
`scripts/frozen.sha256`, write both axiom names into `scripts/ALLOWED_AXIOMS.txt`,
then log a PROGRESS entry: "SETUP frozen, skeleton builds, pins recorded."

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
## <UTC timestamp> — <stage/item, e.g. "Stage C · no_nonconstant_param_of_not_pow13">
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
  `#print axioms` — for this project that means `propext`, `Classical.choice`,
  `Quot.sound` **plus, where the dependency graph genuinely reaches them**,
  `Erdos477.heath_brown_diagonal_13` and
  `Erdos477.brownawell_masser_P1_four_term`; no `sorryAx`, no
  `native_decide`/`Lean.ofReduceBool`, no other axiom. A `✅` that does not match
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
   `BLUEPRINT.md`/`USER_NOTES.md`, and **appends a `## Review — Iteration N` block
   to `REVIEW.md`** ending in `Verdict: COMPLETE | INCOMPLETE`. Every 5th iteration
   is a full-project audit. The loop ends when a verdict is `COMPLETE` and a final
   full audit confirms it.

**Worker onboarding ritual — do this BEFORE writing any code:**

1. **Read `TASKS.md`**, find `## Iteration N`, then your own `Agent k:` line.
   *That line is your assignment* — the files you own and the lemmas to produce.
   Ignore the other agents' lines (they are running right now in parallel).
2. **Read `PROGRESS.md` end to end.** Respect every `✅` (done — reuse, don't
   redo), `🔧` (another agent holds it — do not touch), `⚠️` (blocked), and `📝`
   (a fixed modeling/proof decision you must follow).
3. **Read the `BLUEPRINT.md` stage(s) your task names — including the Cheat-watch
   box — and the cited `SKETCH.md` step(s).** Do not work from the stage title
   alone; the cheat-watch boxes are binding. For this project also read
   `USER_NOTES.md`: the Route A requirement is an acceptance criterion.
4. **Append a `🔧 in progress` entry** to `PROGRESS.md` claiming your work, then
   work only on your assigned files, then append `✅`/`⚠️` as you go.

**Dependency discipline.** Respect the order graph in "Suggested formalization
order"; the Plan agent must never assign work whose prerequisites are not yet
`✅`. Workers must **never edit the frozen `Defs.lean`/`Theorems.lean`** and must
**never weaken a frozen statement** (see the cardinal cheat rule below) — if a
task seems to need that, append a `⚠️` entry describing the obstacle and stop,
rather than touching a frozen file. Workers must also **never add an `axiom`**:
the allowlist has exactly two entries and it is closed.

---

## Part 0 — What Mathlib already gives you (reuse, do not rebuild)

| Need                                              | Mathlib handle |
| ------------------------------------------------- | -------------- |
| `m ↦ mⁿ` strictly monotone / injective for odd `n` | `Odd.strictMono`, `Odd.pow_right_injective`, `Odd.pow_left_strictMono`, `Odd.pow_left_injective` (locate with `loogle`/`leansearch`) |
| `(−y)¹³ = −y¹³`                                    | `Odd.neg_pow` |
| Geometric sum `(1 − s)·∑_{j<n} sʲ = 1 − sⁿ`        | `geom_sum_mul`, `mul_geom_sum`, `geom_series_def` |
| `aⁿ − bⁿ = (a − b)·∑ aⁱ b^{n−1−i}`                 | `Commute.geom_sum₂_mul`, `geom_sum₂_mul_comm`, `sub_dvd_pow_sub_pow` |
| Rational with integral 13th power is integral      | `Rat.den_pow` + `Nat.pow_eq_one` (elementary; **no** rational-root machinery needed) |
| Rational functions `k(t)`                          | `RatFunc k`, `RatFunc.C`, `RatFunc.X`, `RatFunc.num`, `RatFunc.denom`, `RatFunc.intDegree`, `RatFunc.num_div_denom` |
| Root multiplicity / root counting                  | `Polynomial.rootMultiplicity`, `Polynomial.roots`, `Polynomial.card_roots_le_degree`, `Polynomial.roots_count_eq_rootMultiplicity` |
| Homogeneous multivariate polynomials               | `MvPolynomial.IsHomogeneous`, `MvPolynomial.IsHomogeneous.mul`, `MvPolynomial.IsHomogeneous.pow` |
| Substitution / evaluation                          | `MvPolynomial.aeval`, `MvPolynomial.eval`, `MvPolynomial.map`, `MvPolynomial.pderiv` |
| Algebraically closed field of char 0               | `Complex.isAlgClosed`, `Complex.charZero`, `IsAlgClosed`, `AlgebraicClosure` |
| Degree ≤ 1 polynomial normal form                  | `Polynomial.eq_X_add_C_of_natDegree_le_one`, `Polynomial.natDegree_le_one_iff_...` |
| Binomial theorem / coefficient extraction          | `add_pow`, `Polynomial.coeff_add`, `Polynomial.coeff_C_mul`, `Polynomial.coeff_X_pow` (only for the Route B *side* lemma) |
| Vandermonde determinant                            | `Matrix.vandermonde`, `Matrix.det_vandermonde` (only for the Route B *side* lemma) |
| Enumeration `ℕ ≃ ℤ`                                | `Denumerable ℤ`, `Denumerable.eqv`, `Equiv.intEquivNat` |
| Finset cardinality / pigeonhole                    | `Int.card_Icc`, `Finset.card_le_card_of_injOn`, `Finset.card_biUnion_le`, `Finset.card_lt_card`, `Finset.exists_of_ssubset`, `Finset.eq_of_subset_of_card_le` |
| `Set.ncard` and finiteness                         | `Set.ncard`, `Set.Finite`, `Set.ncard_le_ncard`, `Set.Finite.subset`, `Set.ncard_coe_Finset` |
| Real exponents                                     | `Real.rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_nonneg`, `Real.one_le_rpow_iff_of_pos` |
| Unconditional (`finsum`) sums                      | `finsum`, `finsum_mem_coe_finset`, `finsum_eq_sum_of_finite`, `finsum_eq_zero_of_forall_eq_zero` |
| Choice                                             | `Classical.choice`, `Exists.choose`, `Exists.choose_spec`, `Classical.dec` |

**The two nontrivial dependencies the whole proof hinges on** are `RatFunc` +
`Polynomial.rootMultiplicity` (they carry the entire `ord_P` calculus of Stage C)
and `Real.rpow` algebra (the exponent chain `(T^{13/12})^{10/13} = T^{5/6}` of
Stage E). Everything else is routine.

**Machinery you can avoid.** No compactness / `IsCompact.exists_isMinOn`: the
sketch replaces the paper's implicit `κ > 0` by the explicit `κ = 1/2`. No scheme
theory, no `Projectivization`, no `AlgebraicGeometry`: `ℙ¹` is modelled by
`Option k` and morphisms by tuples of binary forms. No `Polynomial.Chebyshev`,
no Wronskians: the generalized-Wronskian content is exactly what
`brownawell_masser_P1_four_term` assumes.

> **Do not use `Polynomial.abc` (Mathlib's Mason–Stothers) on the dependency path
> of `erdos_477`.** `USER_NOTES.md` is explicit: the three-term case must be an
> instance of `brownawell_masser_P1_four_term`, exactly as the paper invokes it.
> `Polynomial.abc` may appear only in a side lemma used for cross-checking.

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #   | Object                                   | Role |
| --- | ---------------------------------------- | ---- |
| D1  | `Bset : Set ℤ`                           | the thirteenth powers `B` |
| D2  | `Dset : Set ℤ`                           | the difference set `D = B − B` |
| D3  | `Qcof : ℝ → ℝ → ℝ`                       | the degree-12 cofactor `Q(u,v)` |
| D4  | `badShifts : ℤ → ℤ → Finset ℤ`           | `S_c(T)`, the bad shifts |
| D5  | `diagSolutions : ℤ → ℝ → Set (ℤ×ℤ×ℤ)`    | integer points of `x¹³+y¹³+z¹³ = M` in a box |
| D6  | `IsNonsingularTernaryForm`               | Heath-Brown's hypothesis on `F` |
| D7  | `LiesOnPolyParam`                        | "lies on a nonconstant parametrization of degree ≤ d" |
| D8  | `hbSolutions`                            | the set Heath-Brown's bound counts |
| D9  | `P1Point k := Option k`                  | closed points of `ℙ¹_k` (`none = ∞`) |
| D10 | `ordP : P1Point k → RatFunc k → ℤ`       | order of a rational function at a point |
| D11 | `IsConstRF`                              | "`f ∈ k(t)` is constant" |
| D12 | `IsSUnitOn`                              | "`f` is an `S`-unit" |
| D13 | `minOrd`                                 | `min_i ord_P(uᵢ)` |
| D14 | `projHeight`                             | `H(u₁ : ⋯ : u_r)`, the paper's height convention |
| D15 | `IsProjZero`, `projZeroCount`            | projective zeros of a binary form and their number |
| D16 | `NoCommonProjZero`                       | the forms define a morphism (no base locus) |
| D17 | `IsConstantFamily`                       | "the morphism `[A₀ : ⋯]` is constant" / "all ratios constant" |
| D18 | `IsParamOfXN`                            | a parametrized curve on `X_N ⊂ ℙ³_ℚ` |
| A1  | `heath_brown_diagonal_13` (**axiom**)    | paper Theorem 2.2, verbatim, general form |
| A2  | `brownawell_masser_P1_four_term` (**axiom**) | paper Theorem 2.1, verbatim, general `r ≥ 3` |

---

## Part 2 — Theorems and lemmas to prove (in order)

### Stage A — the elementary layer (`Proofs/Elementary/`)

Goal: the six trivial-but-ubiquitous facts of SKETCH §2, plus the two bridging
support lemmas the later stages need. Produces frozen `zero_mem_Bset`,
`Dset_neg_mem`, `pow13_inj`, `mem_Bset_of_rat_pow13`, `sub_pow13_mem_Dset_iff`.

**A1 — `zero_mem_Bset`.** `⟨0, by norm_num⟩`. Also record the support lemma
`zero_mem_Dset : (0:ℤ) ∈ Dset` (`⟨0, 0, by ring⟩`) — Stage F needs it for the
`a_j ∉ A_{j−1}` step (SKETCH §9.5(9)).

**A2 — `Dset_neg_mem`.** From `d = u¹³ − v¹³` produce `−d = v¹³ − u¹³`: swap `u`
and `v`, then `ring`. **No** odd-power sign manipulation.

**A3 — `pow13_inj`.** 13 is odd; use `Odd.strictMono`/`Odd.pow_right_injective`
on `ℤ`. Record the two corollaries as support lemmas:
`pow13_eq_neg : x¹³ = −y¹³ → x = −y` (rewrite `−y¹³ = (−y)¹³` by `Odd.neg_pow`)
and `pow13_inj_rat : Function.Injective (fun q : ℚ => q ^ 13)` (Stage C needs the
`ℚ` version for "no nontrivial 13th root of unity in `ℚ`").

**A4 — `mem_Bset_of_rat_pow13`.** From `q¹³ = (c : ℚ)` get `(q¹³).den = 1`; by
`Rat.den_pow` this is `q.den ^ 13 = 1`, hence `q.den = 1` (`Nat.pow_eq_one`), so
`q = (q.num : ℚ)` and `c = q.num ^ 13`. Elementary — do **not** reach for
`IsIntegrallyClosed`.

**A5 — `sub_pow13_mem_Dset_iff`.** Both directions from `Dset_neg_mem`, since
`−(c − t¹³) = t¹³ − c`.

**A6 — support: `Dset_eq_sub_Bset`.** `Dset = {d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x − y}`,
by `Set.ext` and unfolding. Stage G needs exactly this to instantiate
`greedy_tiling` at `B := Bset`.

> **Cheat watch (Stage A).** `pow13_inj` must be injectivity of `m ↦ m¹³` on **all
> of `ℤ`**, not on `ℕ` or on nonnegatives — the negative branch is where the odd
> exponent actually matters, and Stage G uses it at arbitrary integers.
> `mem_Bset_of_rat_pow13` must quantify over **all** `q : ℚ`, not over `q` already
> known to be an integer (that would make it vacuous and silently break Corollary
> 3.2's `c ∈ ℚ¹³ ↔ c ∈ B` step). `Dset_eq_sub_Bset` must be an **equality of
> sets**, not a one-sided inclusion — `greedy_tiling` consumes it in the `⊇`
> direction and `good_shift_exists` produces it in the `⊆` direction. Guardrail
> `example`s: `(0:ℤ) ∈ Dset`, `(-1:ℤ) ∈ Bset`, `((-1:ℤ))^13 = -1`, and
> `(2:ℤ) ∉ Bset` proved (not asserted) via a size argument.

### Stage B — the explicit cofactor bound (`Proofs/Cofactor/`)

Goal: SKETCH §4 with `κ = 1/2`. Produces frozen `Qcof_ge_half_max_pow12` and
`abs_pow13_sub_pow13_ge`.

**B1 — support: `Qcof_symm`.** `Qcof u v = Qcof v u` by reindexing the sum
`i ↦ 12 − i` (`Finset.sum_nybij'` / `Finset.sum_range_reflect`). Lets you WLOG
`|v| ≤ |u|`.

**B2 — support: `geom_q_ge_half`.** For `s : ℝ` with `|s| ≤ 1`,
`(1/2 : ℝ) ≤ ∑ j ∈ Finset.range 13, s ^ j`. Two cases exactly as SKETCH §4 step 4:
for `0 ≤ s ≤ 1` every summand is `≥ 0` and the `j = 0` one is `1`; for `−1 ≤ s < 0`
use `geom_sum_mul` in the form `(1 − s) · ∑_{j<13} sʲ = 1 − s¹³`, with `s¹³ < 0`
(odd power of a negative) so `1 − s¹³ ≥ 1`, and `0 < 1 − s ≤ 2`.

**B3 — `Qcof_ge_half_max_pow12`.** WLOG `|v| ≤ |u|` (B1). If `u = 0` then `v = 0`
and both sides are `0`. Otherwise set `s := v / u`; factor `u¹²` out of every term
(`Qcof u v = u ^ 12 * ∑ j ∈ range 13, s ^ j`, proved by `Finset.sum_congr` +
`field_simp`), note `u ^ 12 = |u| ^ 12 = max |u| |v| ^ 12` (even exponent), and
apply B2.

**B4 — `abs_pow13_sub_pow13_ge`.** Support lemma
`pow13_sub_factor : (u:ℝ)^13 − v^13 = (u − v) * Qcof u v` (from
`Commute.geom_sum₂_mul`, or directly by `ring` after `Finset.sum` expansion via
`decide`-free `simp [Finset.sum_range_succ]; ring`). For distinct integers
`|u − v| ≥ 1` (`Int.one_le_abs` on `u − v ≠ 0`, then cast), and `Qcof u v ≥ 0` by
B3, so `|u¹³ − v¹³| = |u − v| · Qcof u v ≥ 1 · (1/2)·max|u||v|¹²`.

> **Cheat watch (Stage B).** The bound must hold for **all** real `u, v` — do not
> restrict to `u, v ≥ 0`, to `|v| ≤ |u|` (that is a WLOG *inside* the proof, not a
> hypothesis on the statement), or to integers. The constant must be `1/2` or
> better: any *weaker* constant (e.g. `1/1000`) is fine mathematically but changes
> the frozen statement and is forbidden; a *stronger* one (e.g. the sharper
> all-integer `max(|u|,|v|)^12`, SKETCH §4 aside) is not what is frozen. Do **not**
> prove `Qcof u v ≥ 0` and call it the bound — the `max|u||v|¹²` factor is exactly
> what produces the `T^{13/12}` box in Stage E, and dropping it destroys the whole
> exponent chain while still compiling. Guardrail `example`s: `Qcof 1 1 = 13`,
> `Qcof 1 (-1) = 1`, `Qcof 0 0 = 0`, and `Qcof 2 (-1) ≥ (1/2) * 2 ^ 12`.

### Stage C — function-field exclusion, Route A (`Proofs/FunctionField/`) — **HARDEST**

Goal: SKETCH §5.2. Derive from **Axiom 2** the forms version of Brownawell–Masser,
then Lemma 3.1, then Corollary 3.2, then L2.1. Produces frozen
`bm_forms_height_bound`, `no_nonconstant_param_of_not_pow13`,
`no_rational_param_of_not_mem_Bset`, `no_linear_param`. This stage is the reason
the whole run must depend on `brownawell_masser_P1_four_term`.

**C0 — the `ord_P` calculus (support).** Build a small API before anything else;
everything downstream is unusable without it.
`ordP_mul : f ≠ 0 → g ≠ 0 → ordP P (f*g) = ordP P f + ordP P g`;
`ordP_pow : f ≠ 0 → ordP P (f^n) = n * ordP P f`;
`ordP_C : a ≠ 0 → ordP P (RatFunc.C a) = 0`;
`ordP_eq_zero_of_const : IsConstRF f → f ≠ 0 → ordP P f = 0`;
`ordP_ne_zero_finite : f ≠ 0 → {P | ordP P f ≠ 0}.Finite` (numerator/denominator
have finitely many roots; add `none`);
`suppFinset f : Finset (P1Point k)` — a concrete finite superset of the zeros and
poles, `insert none ((f.num.roots.toFinset ∪ f.denom.roots.toFinset).image some)`,
with `ordP P f ≠ 0 → P ∈ suppFinset f` and
`(suppFinset f).card ≤ f.num.natDegree + f.denom.natDegree + 1`;
`projHeight_eq_sum_over_S : (∀ i, IsSUnitOn S (u i)) → projHeight u = - ∑ P ∈ S, minOrd u P`
(the `∑ᶠ` collapses because `minOrd u P = 0` off `S`);
`sum_ordP_eq_zero : f ≠ 0 → ∑ᶠ P, ordP P f = 0` (degree formula on `ℙ¹`; this is
the one genuinely-content-bearing support lemma — prove it from
`Polynomial.roots` counting `natDegree` over an algebraically closed field).

**C1 — `bm_forms_height_bound`.** The BM4-for-forms reformulation demanded by
`USER_NOTES.md`, derived from the axiom, general in `r` so that Case A (`r = 4`,
coefficient `Nat.choose 3 2 = 3`) and Case B (`r = 3`, coefficient
`Nat.choose 2 2 = 1`) are **both instances of the single axiom**.
Route: dehomogenize by the second variable — for a form `A` homogeneous of degree
`d`, let `â : Polynomial k` be `A(X, 1)` and set `uᵢ := (âᵢ : RatFunc k) / (RatFunc.X)^0 …`;
concretely put `uᵢ := algebraMap (Polynomial k) (RatFunc k) âᵢ / (RatFunc.C 1)` and
work with the **normalized** family `uᵢ := âᵢ / T̂^d` where `T̂ := RatFunc.X`, i.e.
divide the whole homogeneous identity by the `d`-th power of the second coordinate.
Then:
- `∑ i, u i = 0` and the no-vanishing-sub-sum hypothesis transfer verbatim
  (dividing by a nonzero element).
- Each `uᵢ` is an `S`-unit for `S := {P | IsProjZero (∏ i, A i) P}` as a `Finset`
  (finite by C0 + root counting), because `ord_P uᵢ` at a finite point `a` is the
  multiplicity of `(X − a)` in `âᵢ`, and at `∞` it is `deg âᵢ − d ≤ 0` with
  equality-detection by the `IsProjZero` convention. Prove
  `ordP_of_form : IsProjZero (A i) P ↔ ordP P (u i) ≠ 0 ∨ P = none`-style bridge
  lemmas carefully — **the chart convention must match `IsProjZero`**.
- `¬ ∀ i, IsConstRF (u i)` from `¬ IsConstantFamily A`.
- **Height computation (SKETCH §5.2.1):** `projHeight u = d`. At each finite point
  the minimum of the orders is `0` because `NoCommonProjZero` says the forms do not
  all vanish there; the normalization by `T̂^d` contributes `−d` at `none`; total
  `H = d`. This is the crux lemma of C1 — isolate it as
  `projHeight_of_forms : … → projHeight u = (d : ℤ)`.
Then the axiom gives `d = projHeight u ≤ Nat.choose (r−1) 2 * (S.card − 2)` and
`S.card = projZeroCount (∏ i, A i)` (a form's projective zero set is the union of
its factors' zero sets: `IsProjZero_prod`).

**C2 — `no_nonconstant_param_of_not_pow13` (Lemma 3.1).** Given
`IsParamOfXN N e A` with `N ∉ ℚ¹³`, base-change `A` to `ℂ` and consider the four
terms `A₀¹³, A₁¹³, A₂¹³, −N·A₃¹³` (all homogeneous of common degree `13e`, summing
to `0`, no common zero). Case on how many are nonzero, **exactly** as SKETCH §5.2.2:
- *Case A (all four nonzero, no vanishing proper sub-sum):* apply C1 with `r = 4`,
  `d = 13e`. `projZeroCount (∏) ≤ 4e` because each `Aᵢ` is a form of degree `e`
  with at most `e` distinct projective zeros (support lemma
  `projZeroCount_le_of_isHomogeneous : Φ ≠ 0 → Φ.IsHomogeneous e → projZeroCount Φ ≤ e`).
  So `13e ≤ 3(4e − 2) = 12e − 6`, i.e. `e ≤ −6` — contradiction with `1 ≤ e`.
- *Case B (exactly three nonzero):* first show no proper sub-sum of the three
  vanishes (a minimal one has length ≤ 2; length 1 contradicts nonzeroness; length
  2 forces the complementary length-1 sub-sum to vanish). Apply C1 with `r = 3`,
  coefficient `1`: `13e ≤ 3e − 2` — contradiction.
- *Case C (at most two nonzero):* zero nonzero terms contradicts
  `NoCommonProjZero`; one is absurd; two forces `(P₁/P₂)¹³` to be a nonzero
  constant, hence (orders argument: `13·ord_P = 0` for all `P`) `P₁/P₂` constant
  and the other two coordinates `≡ 0`, so `A` is a constant family — which is the
  conclusion, so this case *closes the goal* rather than contradicting.
- *Case D (all four nonzero, some proper sub-sum vanishes):* lengths 1 and 3 are
  impossible, so the terms split into two vanishing pairs. Each pairing forces
  `N = d¹³` for some `d ∈ ℚ^×` via `ord_P(H/R) = 0` for all `P` (SKETCH display
  (3.2)) — contradicting `hpow`. The step "`(F/G)¹³ = −1` ⟹ `F = −G`" uses
  `pow13_inj_rat` from Stage A (13 is odd and `ℚ` has no nontrivial 13th root of
  unity).
Support lemma to isolate: `const_of_pow13_const : (f : RatFunc ℂ)¹³ = RatFunc.C a
→ a ≠ 0 → IsConstRF f` (the "a rational function with constant nonzero 13th power
is constant" argument, used in Cases C and D), plus its `ℚ`-descent
`ratfunc_const_descends`.

**C3 — `no_rational_param_of_not_mem_Bset` (Corollary 3.2).** Given
`f, g, h : RatFunc ℚ` with `f¹³ − g¹³ − h¹³ = C(−c)`, substitute `X := f`,
`Y := −g`, `Z := −h` (odd exponent) to get `X¹³ + Y¹³ + Z¹³ = C(−c)`. Homogenize:
write `f = F̃/R̃` etc. over a common denominator, clear to binary forms
`A₀, A₁, A₂, A₃` of a common degree `e` with `NoCommonProjZero` (divide out the
gcd), giving `IsParamOfXN (−c) e A`. Since 13 is odd, `−c ∈ ℚ¹³ ↔ c ∈ ℚ¹³`, and
for integer `c`, `c ∈ ℚ¹³ ↔ c ∈ Bset` by `mem_Bset_of_rat_pow13` (Stage A) — so
`hc : c ∉ Bset` gives `¬ ∃ d, d¹³ = −c`. Also `−c ≠ 0` because `c ∉ Bset` and
`0 ∈ Bset` (L0.5 / `zero_mem_Bset`). C2 then yields `IsConstantFamily A`, which
unwinds to `IsConstRF f ∧ IsConstRF g ∧ IsConstRF h`. Isolate the clearing-
denominators step as `exists_form_param_of_ratfunc` — it is fiddly and reusable.

**C4 — `no_linear_param` (L2.1).** Map `p₁ p₂ p₃ : Polynomial ℤ` into `RatFunc ℚ`
(`Polynomial.map (Int.castRingHom ℚ)` then `algebraMap (Polynomial ℚ) (RatFunc ℚ)`),
set `f := p̄₁`, `g := −p̄₂`, `h := −p̄₃`, so `f¹³ − g¹³ − h¹³ = C(−c)`. C3 gives all
three constant; since `algebraMap (Polynomial ℚ) (RatFunc ℚ)` is injective and
`Polynomial.map (Int.castRingHom ℚ)` preserves `natDegree` (leading coefficient
maps to a nonzero rational), each `pᵢ.natDegree = 0`. The hypotheses `h₁ h₂ h₃`
are not needed — that is expected (Route A proves more).

> **Cheat watch (Stage C).** This is where the run can silently become unfaithful.
> — **Route B is forbidden on the dependency path.** The elementary Vandermonde
>   proof of L2.1 (SKETCH §5.1) is much easier and would make `no_linear_param`
>   compile without ever touching `brownawell_masser_P1_four_term`. If you write
>   it, it must live in a clearly-marked side file that **nothing** imports on the
>   way to `erdos_477`. `verify.py` check 4b fails the whole run if
>   `#print axioms Erdos477.Solution.erdos_477` does not list **both** axioms.
> — **Do not weaken the axiom into the lemma.** `bm_forms_height_bound` must be
>   *derived*; it must not be restated as a second `axiom`, and its proof must
>   actually apply `brownawell_masser_P1_four_term` (grep for it).
> — **Do not skip a case of Lemma 3.1.** Cases B, C and D are each a real
>   argument; `exact absurd … (by tauto)` over an unproved case is a `sorry` in
>   disguise. Case C *closes* the goal (constant family) — do not "contradict" it.
> — **Do not replace `NoCommonProjZero` over `ℂ` by coprimality over `ℚ`** in C3's
>   homogenization; a common `ℚ̄`-zero would break the height computation.
> — **Do not specialize `no_nonconstant_param_of_not_pow13` to `e = 1`.** The
>   parametrization degree `e` is universally quantified; fixing it would make C3's
>   homogenization inapplicable and is exactly "proving a special case".
> — **Chart consistency.** `ordP` and `IsProjZero` must use the same
>   `some a ↔ [a : 1]`, `none ↔ [1 : 0]` convention. A mismatch makes
>   `projHeight_of_forms` off by the multiplicity at `∞` and the whole
>   `13e ≤ 12e − 6` contradiction evaporates — silently, since both sides still
>   typecheck.
> — Guardrail `example`s: `projZeroCount (X₀ * X₁ : MvPolynomial (Fin 2) ℂ) = 2`;
>   `ordP none (RatFunc.X : RatFunc ℂ) = -1`; `ordP (some 0) (RatFunc.X) = 1`;
>   `ordP P (RatFunc.C 5) = 0` for both charts.

### Stage D — the Heath-Brown bridge (`Proofs/HeathBrown/`)

Goal: SKETCH §3 points 1–4 — turn the general **Axiom 1** into the diagonal count.
Produces frozen `hb_diagonal_count`.

**D1 — support: `diagForm`.** `diagForm : MvPolynomial (Fin 3) ℤ :=
X 0 ^ 13 + X 1 ^ 13 + X 2 ^ 13`, with
`diagForm_isHomogeneous : diagForm.IsHomogeneous 13` and
`diagForm_nonsingular : IsNonsingularTernaryForm diagForm 13`. The latter: `pderiv i
diagForm = 13 * X i ^ 12`, so a common zero `z : Fin 3 → ℂ` has `13 * z i ^ 12 = 0`
for each `i`, hence `z i = 0` (`pow_eq_zero_iff`, and `(13:ℂ) ≠ 0`), i.e. `z = 0`
(`funext`). **No sign normalization `ε_c` is needed** — the paper's `ε_c` exists
only to match Heath-Brown's published sign convention, and Axiom 1 as transcribed
takes an arbitrary nonzero `N`. Record this as a `📝` PROGRESS entry.

**D2 — support: `aeval_diagForm`.** `MvPolynomial.eval x diagForm = x 0 ^ 13 + x 1
^ 13 + x 2 ^ 13` and `MvPolynomial.aeval p diagForm = p 0 ^ 13 + p 1 ^ 13 + p 2 ^ 13`
(`simp [diagForm]`).

**D3 — support: `not_liesOnPolyParam_of_hexcl`.** Under `hexcl`, for every
`x : Fin 3 → ℤ`, `¬ LiesOnPolyParam diagForm M 1 x`: a witness `p` would satisfy
`aeval p diagForm = C M` with all degrees `≤ 1`, so `hexcl` forces all
`natDegree = 0`, contradicting "not all constant". Note `13 / 10 = 1` in `ℕ`
(`by norm_num`) so the axiom's `k / 10` really is `1`.

**D4 — support: `hbSolutions_eq_diagSolutions`.** With D3, for every `X`,
`hbSolutions diagForm M 1 X` is the image of `diagSolutions M X` under the
equivalence `(ℤ × ℤ × ℤ) ≃ (Fin 3 → ℤ)`, hence
`(diagSolutions M X).ncard = (hbSolutions diagForm M 1 X).ncard`
(`Set.ncard_image_of_injective` / `Set.ncard_preimage_of_injective`, or
`Set.BijOn.ncard_eq`). **This is the step where the `Fin 3 → ℤ` / `ℤ × ℤ × ℤ`
mismatch bites — do it explicitly, do not `simp` past it.**

**D5 — `hb_diagonal_count`.** Apply Axiom 1 with `F := diagForm`, `k := 13`,
`A := 1`, obtaining `C > 0` uniform in `N` and `X`. For `X ≥ |M|` the side
condition `|M| ≤ 1 · X` holds, so the count is `≤ C · X^(10/13)`. For
`1 ≤ X < |M|` bound the count **trivially**: every solution has all coordinates in
`[−|M|, |M|]` (from `|xᵢ| ≤ X < |M|`), so `(diagSolutions M X).ncard ≤ (2|M|+1)^3`
(`Set.ncard_le_ncard` into a finite box; `Set.Finite.ofFinset`). Take
`K := max 1 (max C ((2|M|+1)^3))` and use `1 ≤ X^(10/13)` (`Real.one_le_rpow_iff_of_pos`)
to absorb the bounded range. Conclude `1 ≤ K` and the uniform bound.

> **Cheat watch (Stage D).** — **Do not re-axiomatize the specialization.**
> `hb_diagonal_count` must be a `theorem` whose proof calls
> `heath_brown_diagonal_13`; `USER_NOTES.md` explicitly revokes the sketch's advice
> to assume it. — **Do not drop `hexcl`.** Without it the statement is false; a
> proof that never uses `hexcl` means D3/D4 were faked. — **Do not weaken
> `∀ X ≥ 1` to `∀ X ≥ |M|`**: the bounded range is exactly the part that must be
> absorbed into `K`, and Stage E instantiates at `X = C_c·T^{13/12}` with no lower
> control relative to `|c|`. — **Do not let `K` depend on `X`** (a `∃ K` inside the
> `∀ X` would make Stage E's constant blow up and is a genuine weakening). —
> **Do not "prove" nonsingularity by `decide` or by checking finitely many `z`.**
> — Guardrail `example`s: `(13 : ℕ) / 10 = 1`; `MvPolynomial.eval ![1,1,1] diagForm
> = 3`; `¬ LiesOnPolyParam diagForm 3 1 ![1,1,1]` is *not* a guardrail (it needs
> `hexcl`) — instead check `IsNonsingularTernaryForm diagForm 13` compiles.

### Stage E — the bad-shift estimate (`Proofs/BadShift/`)

Goal: SKETCH §6 (paper Prop 4.1). Produces frozen `badShift_bound`. Depends on
Stages A, B, C, D.

**E1 — support: `Phi_inj`.** Fix `c ∉ Bset`. For `t ∈ badShifts c T` choose (via
`Exists.choose` on the `Dset` membership) a pair `(u_t, v_t)` with
`t¹³ − c = u_t¹³ − v_t¹³`, and set `Φ t := (u_t, −v_t, −t)`. Then
`Φ t ∈ diagSolutions (−c) X` (once E3 supplies the box bound) and `Φ` is
injective on `badShifts c T` because the third coordinate recovers `t`.

**E2 — support: `u_ne_v`.** `u_t ≠ v_t`: otherwise `t¹³ − c = 0`, so `c = t¹³ ∈ Bset`.
This is the only place `hc` is used at this level — SKETCH §9.5(3).

**E3 — support: `box_bound`.** From B4 (`abs_pow13_sub_pow13_ge`) and E2,
`(1/2)·max(|u_t|,|v_t|)¹² ≤ |u_t¹³ − v_t¹³| = |t¹³ − c| ≤ T¹³ + |c| ≤ (1+|c|)T¹³`
(using `|t| ≤ T`, `T ≥ 1`). Hence `max(|u_t|,|v_t|) ≤ C_c · T^{13/12}` with
`C_c := (2(1+|c|))^(1/12) ≥ 1`, and also `|t| ≤ T ≤ C_c·T^{13/12}`. Set
`X := C_c · (T:ℝ)^((13:ℝ)/12)`; note `1 ≤ X`.

**E4 — `badShift_bound`.** `no_linear_param c hc` (Stage C) supplies `hexcl` for
`M := −c` (nonzero by `zero_mem_Bset`), so `hb_diagonal_count` gives `K₀ ≥ 1` with
`(diagSolutions (−c) X).ncard ≤ K₀·X^(10/13)` for all `X ≥ 1`. By E1–E3,
`(badShifts c T).card ≤ (diagSolutions (−c) X).ncard`
(`Set.ncard_le_ncard` on the image of an injective map, or
`Finset.card_le_card_of_injOn` into a `Set.Finite.toFinset`). Compose the
exponents:
`X^(10/13) = C_c^(10/13) · (T^(13/12))^(10/13) = C_c^(10/13) · T^(5/6)` using
`Real.rpow_natCast`/`Real.rpow_mul` (needs `T ≥ 0`) and `(13/12)*(10/13) = 5/6`
(`norm_num`). Set `K := max 1 (K₀ · C_c^(10/13))`.

> **Cheat watch (Stage E).** — **The exponent must be exactly `5/6`.** Any crude
> box bound (`X = O(T²)` or `max(|u|,|v|) ≤ (1+|c|)T¹³`) still compiles and gives a
> bound of the form `K·T^α` with `α ≥ 1`, which is useless: Stage G's pigeonhole
> needs `α < 1`. SKETCH §9.5(10) warns about precisely this. — **`K` must not
> depend on `T`.** `∃ K, ∀ T` — not `∀ T, ∃ K`. — **Do not add a hypothesis
> `T ≥ T₀(c)`**; the frozen statement is `∀ T ≥ 1`. — **Do not replace
> `badShifts` by a subset** (e.g. only `t ≥ 0`): that halves the count and breaks
> Stage G's `2T + 1` comparison. — **Do not assume `Φ` is surjective onto
> `diagSolutions`** — only injectivity is true and only injectivity is needed. —
> Guardrail: `badShifts c 1 ⊆ {-1, 0, 1}` and `(badShifts c T).card ≤ 2*T.toNat+1`
> proved from `Int.card_Icc`, as a sanity check on the definition.

### Stage F — the greedy tiling criterion (`Proofs/Greedy/`) — **INDEPENDENT, prove first**

Goal: SKETCH §7 (paper Lemma 5.1). Pure combinatorics; depends on **nothing**
(not even Stage A). Produces frozen `greedy_tiling`.

**F1 — support: `Dsep`.** `Dsep B (A : Finset ℤ) : Prop := ∀ a ∈ A, ∀ a' ∈ A,
a ≠ a' → a - a' ∉ {d | ∃ x ∈ B, ∃ y ∈ B, d = x - y}`, with the translate-disjointness
lemma `(a + B) ∩ (a' + B) ≠ ∅ ↔ a − a' ∈ B − B`.

**F2 — support: `Aseq`.** `Aseq : ℕ → Finset ℤ` by `Nat.rec`, using the
enumeration `enum : ℕ ≃ ℤ` from `Denumerable ℤ`. At step `j`: if
`enum j ∈ Aseq j + B` (classical decidability) keep `Aseq j`; else apply `H` to
`C_j := (Aseq j).image (fun a => enum j - a)` (all its elements are `∉ B` exactly
because `enum j ∉ Aseq j + B`), choose `b_j` classically, and set
`Aseq (j+1) := insert (enum j - b_j) (Aseq j)`.

**F3 — support: `Aseq_mono`, `Aseq_dsep`, `Aseq_covers`.** Monotonicity
`i ≤ j → Aseq i ⊆ Aseq j` by induction; then the **combined** induction proving
`(I1) Dsep B (Aseq j)` and `(I2) ∀ i < j, enum i ∈ Aseq j + B` in one motive
(an `And`, as SKETCH §7 Lean notes advise). In Case 2 you must also prove
`a_j ∉ Aseq j` — from `0 ∈ D` (`b − b`, needs `B` nonempty, which comes from `H`
applied to `C = ∅`) — SKETCH §9.5(9).

**F4 — `greedy_tiling`.** `A := ⋃ j, ↑(Aseq j)`. Covering from (I2) + surjectivity
of `enum`. `D`-separatedness of `A`: two elements lie in `Aseq i`, `Aseq i'`, hence
both in `Aseq (max i i')` by `Aseq_mono`. Uniqueness: `a + b = a' + b'` with
`a ≠ a'` gives `a − a' = b' − b ∈ B − B`, contradicting separatedness; then
`b = b'` by cancellation. Package as `∃! ab : ℤ × ℤ, …` (`Prod.ext`).

> **Cheat watch (Stage F).** — **`B` is an arbitrary `Set ℤ`**, not `Bset`; do not
> specialize (the frozen statement is general, and specializing would be "proving a
> special case and claiming the general one"). — **The conclusion is `∃!`, over the
> pair.** Producing only existence, or uniqueness of `a` alone, is the classic
> weakening here. — **`H` must be used at arbitrary finite `C`**, including
> `C = ∅` (that is what gives `B ≠ ∅`); do not add `C.Nonempty`. — **Do not assume
> `0 ∈ B` or `B` symmetric** — neither is a hypothesis; `0 ∈ D` must be derived
> from `B ≠ ∅`. — **Do not build `A` as a `Finset` or as `Set.range` of something
> monotone-by-fiat**; the union-of-a-chain argument is the proof. — Guardrail: the
> statement instantiated at `B := Set.univ` should be provable in two lines and
> gives `A = {0}`-like behaviour — use it as a sanity check that the `∃!` is not
> accidentally vacuous.

### Stage G — assembly (`Proofs/Assembly/`)

Goal: SKETCH §8. Produces frozen `good_shift_exists` and the headline `erdos_477`.

**G1 — `good_shift_exists` (P5.1).** If `C = ∅` take `b := 0` (`zero_mem_Bset`).
Otherwise, for each `c ∈ C` get `K_c ≥ 1` from `badShift_bound`; set
`K := ∑ c ∈ C, K_c ≥ 1`. Choose an integer `T > K^6`, `T ≥ 1` (e.g.
`T := ⌈K⌉₊^6 + 1`). Then
`(C.biUnion (fun c => badShifts c T)).card ≤ ∑ c ∈ C, (badShifts c T).card
≤ K·T^{5/6} < T^{1/6}·T^{5/6} = T < 2T+1 = (Finset.Icc (−T) T).card`
(`Finset.card_biUnion_le`, `Int.card_Icc`; for the strict step use `K < T^{1/6}`,
equivalently `K^6 < T`, via `Real.rpow_natCast`/`Real.rpow_lt_rpow`). Pigeonhole
(`Finset.exists_mem_notMem`-style: `card_lt_card` on
`biUnion ∩ Icc ⊂ Icc` then `Finset.exists_of_ssubset`) gives `t₀` with `|t₀| ≤ T`
and `t₀ ∉ badShifts c T` for every `c ∈ C`; hence `t₀¹³ − c ∉ Dset`, hence
`c − t₀¹³ ∉ Dset` by `sub_pow13_mem_Dset_iff`. Take `b := t₀ ^ 13`.

**G2 — `erdos_477` (Theorem 1.1).** Feed `good_shift_exists` (rewritten through
`Dset_eq_sub_Bset`) as the hypothesis `H` of `greedy_tiling` at `B := Bset`,
obtaining `A` with a unique `(a, b)`-representation. Upgrade `(a, b) ↦ (a, m)`:
existence from the definition of `Bset` (`b = m¹³`); uniqueness from uniqueness of
`(a, b)` plus `pow13_inj`. Conclude `∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n`.
Then run `#print axioms Erdos477.Solution.erdos_477` and confirm it prints
**exactly** `propext`, `Classical.choice`, `Quot.sound`,
`Erdos477.heath_brown_diagonal_13`, `Erdos477.brownawell_masser_P1_four_term`.

> **Cheat watch (Stage G).** — **The pigeonhole must be strict.** `2T + 1`
> candidates vs `< T` bad shifts: an off-by-one that turns `<` into `≤` makes the
> good `t₀` fail to exist and tempts a later agent to "fix" it by adding a
> hypothesis. — **`T` must be chosen after `K`, uniformly in `C`** — the frozen
> statement quantifies over all finite `C`, so no `T` may leak into the statement.
> — **Do not prove `erdos_477` for a *specific* `A` you cannot exhibit, by
> `Classical.choice` on a false premise**; the witness comes from `greedy_tiling`
> and nowhere else. — **Do not replace `∃!` by `∃`,** and do not silently drop the
> `p.1 ∈ A` conjunct. — **Do not let `good_shift_exists` acquire a hypothesis like
> `C.Nonempty` or `0 ∉ C`** — the `C = ∅` case is real and easy. — Guardrail:
> `good_shift_exists ∅ (by simp)` should reduce to `⟨0, zero_mem_Bset, by simp⟩`.

### Discharge & Solution (after the frozen theorems are proved)

In `Erdos477/Solution.lean`, restate each of the 16 frozen theorems **verbatim** in
`namespace Erdos477.Solution` and set it `:= <name>_proof` (the sorry-free
declaration from `Proofs/`). In `Erdos477/Discharge.lean`, for each pair write
`example : @Erdos477.<name> = @Erdos477.Solution.<name> := rfl` — this compiles
**iff** the proof has *exactly* the frozen proposition (machine-checked no-drift).
`verify.py` checks both modules build and that
`#print axioms Erdos477.Solution.<name>` is within the allowlist for every frozen
name, and (check 4b) that `Erdos477.Solution.erdos_477` genuinely depends on both
mandatory axioms.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems + both axioms, skeleton builds, pins recorded)
      │
      ├──────────────────────────────► Stage F  (greedy_tiling)          [INDEPENDENT]
      │                                    │
      ▼                                    │
  Stage A (elementary L0.*)                │
      │                                    │
      ├──► Stage B (cofactor L1.1–L1.2) ─┐ │
      │                                  │ │
      └──► Stage C (Route A: BM4 ► L3.1 ►│ │
           Cor 3.2 ► L2.1)   [HARDEST]   │ │
                    │                    │ │
                    ▼                    │ │
              Stage D (HB bridge)        │ │
                    │                    │ │
                    └────────┬───────────┘ │
                             ▼             │
                        Stage E (badShift_bound)   ◄── MILESTONE (analytic spine done)
                             │             │
                             └──────┬──────┘
                                    ▼
                           Stage G (good_shift_exists ► erdos_477)   [HEADLINE]
                                    │   #print axioms = {propext, Classical.choice,
                                    │    Quot.sound, heath_brown_diagonal_13,
                                    │    brownawell_masser_P1_four_term}
                                    ▼
                        Discharge.lean + Solution.lean
```

- **Independent, run in parallel from day one:** Stage F (needs nothing), Stage A
  (needs nothing), Stage B (needs nothing beyond Mathlib). These three are the
  natural first `## Iteration 1` split across three workers; a fourth worker should
  start Stage C's `ord_P` calculus (C0), which also needs nothing.
- **Milestone:** Stage E. Once `badShift_bound` is `✅`, the analytic content is
  finished and Stage G is bookkeeping.
- **Hardest engineering, by a wide margin:** Stage C (budget the majority of the
  iterations here; C1's `projHeight_of_forms` and C2's four-case analysis are the
  two genuinely hard sub-goals). Second hardest: Stage D's `hbSolutions` /
  `diagSolutions` transport and the bounded-range absorption.
- Stage D depends on Stage C only through `no_linear_param`'s *shape*, not its
  proof — Stage D can be written and closed in parallel with Stage C, since
  `hb_diagonal_count` takes `hexcl` as a hypothesis. Exploit this: do not serialize
  D behind C.

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them, and see the
problem-specific traps at the end.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem must be hypothesis-free wherever the source claim is unconditional.
  Forbidden moves: adding `(h : …)` to a frozen statement; proving a `∀ x`
  (or `∀ x y`) claim only for generators / a finite subset and claiming the
  general case; replacing an equality with a one-sided inclusion. If a sub-proof
  seems to need an assumption, **derive it or restructure** — do not weaken the
  statement. (Downstream stages typically instantiate these at *arbitrary*
  elements, so a quiet weakening breaks the assembly silently.)

- **Keep every predicate the textbook definition — do not soften it.** Quantifiers
  must match the source exactly. Here that means, concretely: `greedy_tiling` over
  **all** `B : Set ℤ` and **all** finite `C`; `Qcof_ge_half_max_pow12` over **all**
  real `u, v`; `no_nonconstant_param_of_not_pow13` over **all** degrees `e ≥ 1`;
  `badShift_bound` over **all** `T ≥ 1`; the axioms over **all** nonsingular forms
  of degree `k ≥ 3` and **all** `r ≥ 3`.

- **Get the modeling right once, in SETUP, and freeze it.** The chart convention
  shared by `ordP` and `IsProjZero`, and the `Fin 3 → ℤ` vs `ℤ × ℤ × ℤ` split
  between `hbSolutions` and `diagSolutions`, are the two places where a wrong
  choice compiles and then silently invalidates a later stage. Validate them with
  the guardrail `example`s listed in the Stage C and Stage D cheat-watch boxes
  *before* freezing.

- **Discharge structural facts once — never `sorry` them.** Inherit ring/field
  structure from Mathlib (`RatFunc`, `MvPolynomial`, `Polynomial`); if you feel the
  urge to `sorry` a `ring`-shaped identity, you modeled the object wrong.

- **`decide` budget — and `native_decide` is BANNED.** Almost nothing here is
  decidable: `Bset`, `Dset`, `badShifts`, `IsProjZero` are all classical. Reserve
  `decide`/`norm_num` for numeric facts (`13 / 10 = 1`, `(13:ℂ) ≠ 0`,
  `(13/12)*(10/13) = 5/6`). `native_decide` adds a compiler-trust axiom and would
  dirty `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen during proving (pinned in `scripts/frozen.sha256`). If a
  *definition* seems missing, it belongs in a `Proofs/` support file. If a
  *statement* seems wrong, stop and re-read `SKETCH.md` — the frozen statements
  are deliberately the minimal faithful rendering of the sketch, so a mismatch
  means a modeling bug to fix *before* re-freezing, not a hypothesis to bolt on.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` **plus** the two allowlisted axioms
  `Erdos477.heath_brown_diagonal_13` and
  `Erdos477.brownawell_masser_P1_four_term` (recorded in
  `scripts/ALLOWED_AXIOMS.txt`). No `sorryAx`, no `native_decide`/`ofReduceBool`,
  no third axiom. Note that Stages A, B and F should print **no** custom axiom at
  all — if `greedy_tiling` depends on Heath-Brown, something is very wrong.

- **Assumed certificates go in as `axiom`s, never as hypotheses.** The two
  permitted axioms are declared in `Defs.lean` during SETUP and nowhere else.
  Never bolt either onto a frozen theorem as a hypothesis `(h : …)`; never
  introduce a third. This NEVER relaxes the cardinal rule above.

**Problem-specific traps.**

1. **The Route B temptation (the single biggest risk).** SKETCH §5.1 hands you a
   complete, elementary, Vandermonde proof of `no_linear_param` that needs no
   second axiom. `USER_NOTES.md` **forbids it on the dependency path**. A run in
   which every file compiles, `verify.py` checks 1–4 pass, and
   `#print axioms erdos_477` lists only `heath_brown_diagonal_13` is a **failed**
   run. Check 4b exists for this; do not try to satisfy it by adding a fake
   dependency (e.g. `have := brownawell_masser_P1_four_term …; clear this`) —
   that is fabrication and an audit failure of the most serious kind.
2. **Axiom drift.** Both axioms must be transcriptions of the paper's Theorems 2.1
   and 2.2 in *full generality*. It will be tempting, when Stage C stalls, to
   "adjust" the axiom to the forms version, or to hard-code `r = 4`, or to bake
   the height computation into it. That is assuming the proof obligation. The
   frozen `Defs.lean` SHA pin blocks it mechanically; do not work around the pin.
3. **Exponent slack.** The chain `max(|u|,|v|) ≲ T^{13/12}` then
   `count ≲ X^{10/13}` composes to exactly `T^{5/6}`. Every crude intermediate
   bound is fatal but compiles. SKETCH §9.5(10) and §9.4 warn about this twice.
4. **`0 ∈ B`.** Used three times (`c ∉ B → c ≠ 0` for `M ≠ 0` in Stage D/E; the
   `C = ∅` case of `good_shift_exists`; `−c ≠ 0` in Corollary 3.2). Easy to forget
   and produces a confusing failure far from its cause.
5. **Symmetry of `D`.** Used silently by the paper twice (L0.6 in Stage G,
   `a − a_j ∉ D` in Stage F). Must be explicit in Lean.
6. **The `(a, b)` → `(a, m)` uniqueness upgrade** needs `pow13_inj`. Dropping it
   gives a statement that is true for the pair `(a, b)` but *false* as stated for
   `(a, m)` — and the `∃!` will not notice.
7. **`Fin 3 → ℤ` vs `ℤ × ℤ × ℤ`.** Stage D's transport. Keep them distinct in your
   head and in the files; conflating them is the most likely *silent* modeling bug
   in the whole project.
8. **Real-exponent arithmetic.** `Real.rpow` needs nonnegativity side conditions
   (`Real.rpow_mul` wants `0 ≤ x`). Cast `T : ℤ` to `ℝ` once, prove `(0:ℝ) ≤ T`
   once, and reuse. SKETCH §9.4 offers a fully integer-only variant
   (`|S_c(T)|^156 ≤ K'_c·T^130`) — it is **not** what is frozen here, so do not
   switch routes mid-stage; use it only as a private sanity check.
