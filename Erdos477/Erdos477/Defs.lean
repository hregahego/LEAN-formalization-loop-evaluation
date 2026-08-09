import Mathlib

/-!
# Frozen definitions for Erdős Problem 477

Every object the formalization needs, in dependency order, together with the two
assumed certificates permitted by `USER_NOTES.md`.

**This file is FROZEN.** Its SHA-256 is pinned in `scripts/frozen.sha256`; no
later stage may change a single character of it. See `BLUEPRINT.md` Part −1 §2
for the modeling decisions behind each definition.
-/

namespace Erdos477

open scoped Classical

open MvPolynomial Polynomial

/-! ## The arithmetic objects -/

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

/-! ## The Heath-Brown objects (needed to state Axiom 1 in full generality) -/

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

/-! ## The function-field objects (needed to state Axiom 2 in full generality) -/

/-- Points of `ℙ¹_k`: `some a` is `[a : 1]`, `none` is the point at infinity `[1 : 0]`. -/
abbrev P1Point (k : Type*) := Option k

/-- `ord_P f` for `f ∈ k(t)^×`: at a finite point the difference of root
    multiplicities of numerator and denominator; at infinity `−intDegree`. -/
noncomputable def ordP {k : Type*} [Field k] : P1Point k → RatFunc k → ℤ
  | none,   f => - f.intDegree
  | some a, f => (Polynomial.rootMultiplicity a f.num : ℤ)
                  - (Polynomial.rootMultiplicity a f.denom : ℤ)

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

/-! ## Binary forms on `ℙ¹` (needed for the derived BM4-for-forms lemma) -/

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

/-! ## The two assumed axioms (permitted by `USER_NOTES.md`)

These are the **only** `axiom` declarations allowed anywhere in the project; their
fully-qualified names are recorded in `scripts/ALLOWED_AXIOMS.txt`. Each is a
transcription of the cited theorem in the paper's full generality — no
specialization, no reformulation, no added or dropped hypotheses. Every
specialized form the proofs consume is a proof obligation downstream. -/

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

end Erdos477
