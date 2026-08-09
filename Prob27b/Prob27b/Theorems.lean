/-
# Prob27b — FROZEN theorem statements

The seventeen frozen statements of `BLUEPRINT.md` Part −1 §3, in the order the
stages prove them (the same order as `scripts/harness.json`).  Every one is
`:= sorry` here; the proofs live in `Prob27b/Proofs/**` and are re-exported,
verbatim, from `Prob27b/Solution.lean`.

This file is **frozen** after SETUP: its SHA-256 is pinned in
`scripts/frozen.sha256` and it may never be edited during the proving phase.
`sorry` is permitted in this file and **nowhere else** in the project.
-/
import Prob27b.Defs

namespace Prob27b

/-! ## Step 1 — the finite noncommutative ring `R` -/

/-- **Frozen 1.** `R` has `2⁸` elements (Step 1, "size `2⁸`"). -/
theorem R_card_eq : Nat.card R = 2 ^ 8 := sorry

/-- **Frozen 2.** `R` is noncommutative (Step 1, "noncommutative"). -/
theorem R_not_commutative : ∃ x y : R, x * y ≠ y * x := sorry

/-! ## Step 2 — `F` is a right null polynomial -/

/-- **Frozen 3.** `F ∈ K(R)`: `F` vanishes at **every** element of `R` (Step 2). -/
theorem F_isNullPoly : IsNullPoly F := sorry

/-! ## Step 3 — `K(R)` is not a right ideal of `R[X]` -/

/-- **Frozen 4.** `(F·e)(u+v) ≠ 0` (Step 3). -/
theorem Fe_eval_ne_zero :
    (F * Polynomial.C (RAlg.e : R)).eval ((RAlg.u : R) + RAlg.v) ≠ 0 := sorry

/-- **Frozen 5.** `K(R)` is not a right ideal of `R[X]`: some null polynomial has a
right multiple by a constant that is not null (Step 3, conclusion). -/
theorem nullPoly_not_rightIdeal :
    ∃ (p : Polynomial R) (c : R), IsNullPoly p ∧ ¬ IsNullPoly (p * Polynomial.C c) := sorry

/-! ## Step 4 — the arithmetic setting `D`, `A`, `B` -/

/-- **Frozen 6.** `D = 𝔽₂[π]` has finite residue rings — the hypothesis of the
conjecture being refuted (preamble and Step 4). -/
theorem D_hasFiniteResidueRings : ∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I) := sorry

/-- **Frozen 7.** `A` is finite free of rank `8` over `D` (Step 4). -/
theorem A_isFreeOfRankEight : Nonempty (Module.Basis (Fin 8) D A) := sorry

/-- **Frozen 8.** `A` is torsion-free over `D` (Step 4). -/
theorem A_torsionFree : NoZeroSMulDivisors D A := sorry

/-- **Frozen 9.** `A ↪ B` (Step 4). -/
theorem iota_injective : Function.Injective iota := sorry

/-- **Frozen 10.** `B` really is the fraction algebra `K ⊗_D A`: every element of
`B` has a single nonzero common denominator in `D` (Step 4). -/
theorem B_fraction_algebra :
    ∀ b : B, ∃ (x : A) (d : D), d ≠ 0 ∧ (algebraMap D K d) • b = iota x := sorry

/-- **Frozen 11.** Reduction mod `π` is onto `R` (Step 4, `A/πA ≅ R`). -/
theorem redPi_surjective : Function.Surjective redPi := sorry

/-- **Frozen 12.** The kernel of reduction mod `π` is exactly `πA` (Step 4,
`A/πA ≅ R`).  This is an **iff**: the `←` direction alone is a silent weakening. -/
theorem redPi_eq_zero_iff : ∀ x : A, redPi x = 0 ↔ ∃ y : A, x = pi • y := sorry

/-- **Frozen 13.** `F̃(a) ∈ πA` for **every** `a ∈ A` (Step 4). -/
theorem Ftilde_eval_mem_pi : ∀ x : A, ∃ y : A, Ftilde.eval x = pi • y := sorry

/-- **Frozen 14.** `P = F̃/π ∈ Int(A)` (Step 4). -/
theorem P_integerValued : IsIntegerValued P := sorry

/-- **Frozen 15.** The constant polynomial `e` belongs to `Int(A)` (Step 4). -/
theorem constE_integerValued : IsIntegerValued (Polynomial.C (iota (RAlg.e : A))) := sorry

/-! ## Step 5 and the conclusion -/

/-- **Frozen 16.** `P·e ∉ Int(A)` (Step 5).  The order of the product is frozen:
the failure is one-sided. -/
theorem Pe_not_integerValued :
    ¬ IsIntegerValued (P * Polynomial.C (iota (RAlg.e : A))) := sorry

/-- **Frozen 17 (HEADLINE).** Problem 27(b) is false: `D` has finite residue
rings, `A` is finite free of rank `8` over `D` and torsion-free, and yet `Int(A)`
is not closed under multiplication. -/
theorem prob27b_counterexample :
    (∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)) ∧
    Nonempty (Module.Basis (Fin 8) D A) ∧
    NoZeroSMulDivisors D A ∧
    (∃ p q : Polynomial B,
        IsIntegerValued p ∧ IsIntegerValued q ∧ ¬ IsIntegerValued (p * q)) := sorry

end Prob27b
