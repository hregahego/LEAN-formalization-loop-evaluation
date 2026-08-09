/-
# Prob27b — Stage D support file

Stage D of `BLUEPRINT.md` Part 2: the arithmetic setting D, A, B, redPi.

This iteration covers **D2, D3, D4, D6, D7** (frozen 7, 8, 9, 11, 12):

* `A_isFreeOfRankEight : Nonempty (Module.Basis (Fin 8) D A)`
* `A_torsionFree : NoZeroSMulDivisors D A`
* `iota_injective : Function.Injective iota`
* `redPi_surjective : Function.Surjective redPi`
* `redPi_eq_zero_iff : ∀ x : A, redPi x = 0 ↔ ∃ y : A, x = pi • y`

`D1` (`D_hasFiniteResidueRings`) and `D5` (`B_fraction_algebra`) are deliberately
left for a later iteration.

Iteration 2 appends exactly those two remaining Stage-D leaves (frozen 6 and 10):

* `D_hasFiniteResidueRings : ∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)`
* `B_fraction_algebra : ∀ b : B, ∃ x d, d ≠ 0 ∧ (algebraMap D K d) • b = iota x`

Every support declaration lives in `namespace Prob27b.StageD` (namespace
discipline: `Prob27b.RAlg` belongs to Stage A), and this file imports only
`Prob27b.Defs`.
-/
import Prob27b.Defs

namespace Prob27b

namespace StageD

variable {k l : Type} [CommRing k] [CommRing l]

/-! ## Coordinate lemmas

`Defs.lean` keeps its coordinate lemmas `private`+`local`, and Stage A owns the
public `RAlg.coeff_mul_*` names, so Stage D proves its own *local* copies of the
handful of additive/scalar/functorial coordinate facts it needs. -/

@[local simp] theorem czero (i : Fin 8) : (0 : RAlg k).coeff i = 0 := by fin_cases i <;> rfl

@[local simp] theorem cadd (x y : RAlg k) (i : Fin 8) :
    (x + y).coeff i = x.coeff i + y.coeff i := rfl

@[local simp] theorem csmul (c : k) (x : RAlg k) (i : Fin 8) :
    (c • x).coeff i = c * x.coeff i := rfl

@[local simp] theorem cmap (φ : k →+* l) (x : RAlg k) (i : Fin 8) :
    (RAlg.map φ x).coeff i = φ (x.coeff i) := rfl

@[local simp] theorem csingle (i j : Fin 8) (c : k) :
    (RAlg.single i c).coeff j = if j = i then c else 0 := rfl

/-- Stage D's own copy of `RAlg.map_single` (Stage A owns the `RAlg` namespace
version this iteration). -/
theorem map_single (φ : k →+* l) (i : Fin 8) (c : k) :
    RAlg.map φ (RAlg.single i c) = RAlg.single i (φ c) := by
  refine RAlg.ext fun j => ?_
  by_cases h : j = i <;> simp [h]

/-! ## D2 support — the coordinate map as a linear equivalence -/

/-- `RAlg.equivFun` upgraded to a `k`-linear equivalence.  The `Module k (RAlg k)`
structure comes from `Algebra.toModule` and its `SMul` is definitionally
`RAlg.smul`, so `map_add'`/`map_smul'` are `rfl`. -/
def equivFunₗ (k : Type) [CommRing k] : RAlg k ≃ₗ[k] (Fin 8 → k) where
  toFun := RAlg.coeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := RAlg.mk
  left_inv _ := rfl
  right_inv _ := rfl

@[local simp] theorem equivFunₗ_apply (x : RAlg k) : equivFunₗ k x = x.coeff := rfl

end StageD

-- `local` attributes are scoped to the namespace they are set in, so the Stage D
-- coordinate lemmas have to be re-declared as `simp` for the rest of the file.
attribute [local simp]
  StageD.czero StageD.cadd StageD.csmul StageD.cmap StageD.csingle StageD.equivFunₗ_apply

/-! ## D2 — frozen 7 : `A` is free of rank `8` over `D` -/

/-- **Frozen 7.**  The coordinate equivalence `A ≃ₗ[D] (Fin 8 → D)` turns the
standard basis of `Fin 8 → D` into a `D`-basis of `A` indexed by `Fin 8`. -/
theorem A_isFreeOfRankEight_proof : Nonempty (Module.Basis (Fin 8) D A) :=
  ⟨Module.Basis.ofEquivFun (StageD.equivFunₗ D)⟩

/-! ## D3 — frozen 8 : `A` is torsion-free over `D` -/

/-- **Frozen 8.**  `d • x = 0` says `d * x.coeff i = 0` for every `i`; `D` is a
domain, so `d ≠ 0` forces every coordinate of `x` to vanish. -/
theorem A_torsionFree_proof : NoZeroSMulDivisors D A := by
  refine ⟨fun {d x} h => ?_⟩
  by_cases hd : d = 0
  · exact Or.inl hd
  · refine Or.inr (RAlg.ext fun i => ?_)
    rw [StageD.czero]
    have hi : d * x.coeff i = 0 := by
      have := congrArg (fun z : A => z.coeff i) h
      simpa using this
    exact (mul_eq_zero.mp hi).resolve_left hd

/-! ## D4 — frozen 9 : `A ↪ B` -/

/-- **Frozen 9.**  `algebraMap D K` is injective (`K` is the fraction field of the
domain `D`), and `RAlg.map` of an injective map is injective componentwise. -/
theorem iota_injective_proof : Function.Injective iota := by
  intro x y h
  have hinj : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  refine RAlg.ext fun i => hinj ?_
  have := congrArg (fun z : B => z.coeff i) h
  simpa [iota] using this

/-! ## D6 — frozen 11 : reduction mod `π` is onto -/

/-- **Frozen 11.**  `Polynomial.C` is a section of `Polynomial.evalRingHom 0`, so
`r` lifts coefficientwise to `⟨fun i => C (r.coeff i)⟩ : A`. -/
theorem redPi_surjective_proof : Function.Surjective redPi := by
  intro r
  refine ⟨⟨fun i => Polynomial.C (r.coeff i)⟩, RAlg.ext fun i => ?_⟩
  simp [redPi]

/-! ## D7 — frozen 12 : the kernel of reduction mod `π` is exactly `πA`

This is an **iff**; the `→` direction is the substantial one. -/

/-- **Frozen 12.**  `redPi x = 0 ↔ ∀ i, (x.coeff i).coeff 0 = 0 ↔ X ∣ x.coeff i`,
and the quotients are chosen componentwise by `Polynomial.divX`
(`Polynomial.X_mul_divX_add`), so no choice principle is needed. -/
theorem redPi_eq_zero_iff_proof : ∀ x : A, redPi x = 0 ↔ ∃ y : A, x = pi • y := by
  intro x
  constructor
  · intro h
    refine ⟨⟨fun i => (x.coeff i).divX⟩, RAlg.ext fun i => ?_⟩
    have h0 : (x.coeff i).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      have := congrArg (fun z : R => z.coeff i) h
      simpa [redPi] using this
    have hx : Polynomial.X * (x.coeff i).divX + Polynomial.C ((x.coeff i).coeff 0) = x.coeff i :=
      Polynomial.X_mul_divX_add (x.coeff i)
    rw [h0, map_zero, add_zero] at hx
    change x.coeff i = pi * (x.coeff i).divX
    rw [pi]
    exact hx.symm
  · rintro ⟨y, rfl⟩
    refine RAlg.ext fun i => ?_
    simp [redPi, pi]

/-! ## Guardrails (Stage D cheat watch) -/

/-- `redPi` really does send the `A`-side path `s` to the `R`-side path `s`. -/
theorem StageD.redPi_s : redPi (RAlg.s : A) = (RAlg.s : R) := by
  refine RAlg.ext fun i => ?_
  by_cases h : i = 6 <;> simp [redPi, RAlg.s, h]

example : redPi (RAlg.s : A) = (RAlg.s : R) := StageD.redPi_s

/-- The Step-5 divisibility fact in its `A`-side form: `s` is not divisible by `π`
in `A`.  This is exactly what the `→` direction of `redPi_eq_zero_iff` buys. -/
theorem StageD.s_not_dvd_pi : ¬ (∃ y : A, (RAlg.s : A) = pi • y) := by
  intro h
  have h0 : redPi (RAlg.s : A) = 0 := (redPi_eq_zero_iff_proof _).mpr h
  rw [StageD.redPi_s] at h0
  revert h0
  decide

example : ¬ (∃ y : A, (RAlg.s : A) = pi • y) := StageD.s_not_dvd_pi

/-! ## D1 — frozen 6 : `D = 𝔽₂[π]` has finite residue rings

This is the hypothesis of the conjecture being refuted, so it is quantified over
**all** nonzero ideals of `D` — never restricted to maximal ideals, to `(π)`, or
to ideals generated by a monic polynomial. -/

/-- **Frozen 6.**  `D = 𝔽₂[X]` is a Euclidean domain, hence a principal ideal
ring: a nonzero ideal `I` is `Ideal.span {g}` for some `g ≠ 0`, so `D ⧸ I` is
ring-isomorphic to `AdjoinRoot g`, which `AdjoinRoot.powerBasis` exhibits as a
finite-dimensional `ZMod 2`-vector space — and `ZMod 2` is finite. -/
theorem D_hasFiniteResidueRings_proof : ∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I) := by
  intro I hI
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal I
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hI (by rw [hg]; simp)
  have hfin : Finite (AdjoinRoot g) := by
    have pb := AdjoinRoot.powerBasis (K := ZMod 2) hg0
    have : Module.Finite (ZMod 2) (AdjoinRoot g) := Module.Finite.of_basis pb.basis
    exact Module.finite_of_finite (ZMod 2)
  have e : (D ⧸ I) ≃+* AdjoinRoot g := Ideal.quotEquivOfEq (by rw [hg])
  exact Finite.of_equiv _ e.toEquiv.symm

/-! ## D5 — frozen 10 : `B` is the fraction algebra of `A`

A **single** denominator `d ≠ 0`, valid for all eight coordinates at once, is
produced by `IsLocalization.exist_integer_multiples` applied to the whole
coefficient family `b.coeff : Fin 8 → K` over `Finset.univ`. -/

/-- **Frozen 10.**  Every `b : B` has a single nonzero common denominator in `D`:
`IsLocalization.exist_integer_multiples (nonZeroDivisors D) Finset.univ b.coeff`
yields one `d ∈ nonZeroDivisors D` clearing all eight coefficients, the integer
preimages assemble into `x : A` componentwise, and `d ≠ 0` because `D` is a
domain (`nonZeroDivisors.ne_zero`). -/
theorem B_fraction_algebra_proof :
    ∀ b : B, ∃ (x : A) (d : D), d ≠ 0 ∧ (algebraMap D K d) • b = iota x := by
  intro b
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors D)
      (Finset.univ : Finset (Fin 8)) b.coeff
  have hint : ∀ i : Fin 8, ∃ c : D, algebraMap D K c = (d : D) • b.coeff i :=
    fun i => hd i (Finset.mem_univ i)
  choose c hc using hint
  refine ⟨⟨c⟩, (d : D), nonZeroDivisors.ne_zero d.2, RAlg.ext fun i => ?_⟩
  rw [StageD.csmul, iota, StageD.cmap]
  exact ((hc i).trans (Algebra.smul_def _ _)).symm

end Prob27b

/-! ## The clean restatements (global rule (f)) -/

namespace Prob27b.Solution

/-- **Frozen 7.** `A` is finite free of rank `8` over `D` (Step 4). -/
theorem A_isFreeOfRankEight : Nonempty (Module.Basis (Fin 8) D A) :=
  Prob27b.A_isFreeOfRankEight_proof

/-- **Frozen 8.** `A` is torsion-free over `D` (Step 4). -/
theorem A_torsionFree : NoZeroSMulDivisors D A :=
  Prob27b.A_torsionFree_proof

/-- **Frozen 9.** `A ↪ B` (Step 4). -/
theorem iota_injective : Function.Injective iota :=
  Prob27b.iota_injective_proof

/-- **Frozen 11.** Reduction mod `π` is onto `R` (Step 4, `A/πA ≅ R`). -/
theorem redPi_surjective : Function.Surjective redPi :=
  Prob27b.redPi_surjective_proof

/-- **Frozen 12.** The kernel of reduction mod `π` is exactly `πA` (Step 4,
`A/πA ≅ R`).  This is an **iff**: the `←` direction alone is a silent weakening. -/
theorem redPi_eq_zero_iff : ∀ x : A, redPi x = 0 ↔ ∃ y : A, x = pi • y :=
  Prob27b.redPi_eq_zero_iff_proof

/-- **Frozen 6.** `D = 𝔽₂[π]` has finite residue rings — the hypothesis of the
conjecture being refuted (preamble and Step 4). -/
theorem D_hasFiniteResidueRings : ∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I) :=
  Prob27b.D_hasFiniteResidueRings_proof

/-- **Frozen 10.** `B` really is the fraction algebra `K ⊗_D A`: every element of
`B` has a single nonzero common denominator in `D` (Step 4). -/
theorem B_fraction_algebra :
    ∀ b : B, ∃ (x : A) (d : D), d ≠ 0 ∧ (algebraMap D K d) • b = iota x :=
  Prob27b.B_fraction_algebra_proof

end Prob27b.Solution
