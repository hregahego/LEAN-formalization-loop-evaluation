/-
Stage G -- the `ω` values, `gap_family`, and the refutation (G1-G4).

Assembly only: every ingredient below is proved elsewhere in `Prob30c/Proofs/**`.

* G1 `omegaAbs_A_proof`            -- `ω_{A_q}(0) = q+1`
* G2 `omegaAbs_polyExt_A_proof`    -- `ω_{A_q[X]}(0[X]) = q+2`
* G3 `gap_family_proof`            -- the whole family, for every `n ≥ 3`
* G4 `polyAbsorbingConj_false_proof` -- Problem 30(c) has a negative answer

Both `ω` values come from a matching *upper* and *lower* bound through
`omegaAbs_eq_succ_of`; nothing here unfolds the `sInf` of `omegaAbs`.
Nothing here edits `Defs.lean` or `Theorems.lean`.
-/
import Prob30c.Proofs.Absorbing.Basic
import Prob30c.Proofs.Model.Basic
import Prob30c.Proofs.Witnesses.Basic
import Prob30c.Proofs.Bound.Basic
import Prob30c.Proofs.Transfer.Basic

namespace Prob30c

/-! ## G1 — `ω_{A_q}(0) = q+1` -/

/-- Step 3 · `ω_{A_q}(0) = q+1`.  Upper bound: `isNAbsorbing_A_succ_q_proof`
    (Stage E).  Lower bound: `not_isNAbsorbing_A_q_proof` (Stage D). -/
theorem omegaAbs_A_proof (q : ℕ) (hq : 2 ≤ q) : omegaAbs (⊥ : Ideal (A q)) = q + 1 :=
  omegaAbs_eq_succ_of (isNAbsorbing_A_succ_q_proof q hq) (not_isNAbsorbing_A_q_proof q hq)

/-! ## G2 — `ω_{A_q[X]}(0[X]) = q+2` -/

/-- Step 6 · `ω_{A_q[X]}(0[X]) = q+2`.  Upper bound:
    `isNAbsorbing_polyExt_A_succ_succ_q_proof` (Stage F3, transported along
    `transferEquiv`).  Lower bound: `not_isNAbsorbing_polyExt_A_succ_q_proof`
    (Stage D).  Note `q + 2 = (q + 1) + 1`. -/
theorem omegaAbs_polyExt_A_proof (q : ℕ) (hq : 2 ≤ q) :
    omegaAbs (polyExt (⊥ : Ideal (A q))) = q + 2 :=
  omegaAbs_eq_succ_of (isNAbsorbing_polyExt_A_succ_succ_q_proof q hq)
    (not_isNAbsorbing_polyExt_A_succ_q_proof q hq)

/-! ## G3 — the whole family of counterexamples, for every `n ≥ 3` -/

/-- Conclusion · for every `n ≥ 3` the Noetherian ring `A (n-1)` has
    `ω_A(0) = n` and `ω_{A[X]}(0[X]) = n+1`. -/
theorem gap_family_proof (n : ℕ) (hn : 3 ≤ n) :
    IsNoetherianRing (A (n - 1)) ∧
      omegaAbs (⊥ : Ideal (A (n - 1))) = n ∧
      omegaAbs (polyExt (⊥ : Ideal (A (n - 1)))) = n + 1 := by
  have hq : 2 ≤ n - 1 := by omega
  refine ⟨isNoetherianRing_A_proof (n - 1), ?_, ?_⟩
  · rw [omegaAbs_A_proof (n - 1) hq]
    omega
  · rw [omegaAbs_polyExt_A_proof (n - 1) hq]
    omega

/-! ## G4 — the headline: Problem 30(c) is false -/

/-- HEADLINE · Problem 30(c) / Anderson–Badawi C2 has a negative answer: the
    Noetherian ring `A 2` satisfies `ω(0[X]) = 4 ≠ 3 = ω(0)`. -/
theorem polyAbsorbingConj_false_proof : ¬ PolyAbsorbingConj := by
  intro h
  have hspec : omegaAbs (polyExt (⊥ : Ideal (A 2))) = omegaAbs (⊥ : Ideal (A 2)) :=
    h (A 2) (⊥ : Ideal (A 2))
  rw [omegaAbs_polyExt_A_proof 2 (le_refl 2), omegaAbs_A_proof 2 (le_refl 2)] at hspec
  omega

end Prob30c
