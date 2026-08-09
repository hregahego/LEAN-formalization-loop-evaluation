/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Qseries
import EntropyBound.Proofs.Toolbox.Aseries

/-!
# Stage E items E1, E2 (and the E4 case split) — the two end ranges of `A' ≥ 8/9`

This file proves the frozen theorems

* `Ader_lower_small` (#33) on `(0, 1/10]` — BLUEPRINT E1 / `SKETCH.md` (5a);
* `Ader_lower_large` (#34) on `[99999/100000, 1)` — BLUEPRINT E2 / `SKETCH.md` (5b);

together with the E4 case split in *hypothesis form*,
`EntropyBound.EntropySpeed.Ader_lower_of_middle`, which derives the frozen conclusion of
`Ader_lower_bound` (#36) from the two ranges above plus the still-open middle range
(#35 `Ader_lower_middle`).  The hypothesis form is deliberate: `Ader_lower_middle` is
still `sorry` in `Theorems.lean`, and citing it would inject `sorryAx`.

All support lemmas live in `namespace EntropyBound.EntropySpeed`.
-/

namespace EntropyBound.EntropySpeed

noncomputable section

open Real

/-- The quantity `A'` is expressed through `Qser`/`Qder`; this is the shape of the frozen
statements #33–#36.  Abbreviated here only inside proofs. -/
theorem sqrt_Qser_ge_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (1 : ℝ) ≤ Real.sqrt (Qser z) := by
  have h1 : (1 : ℝ) ≤ Qser z := (EntropyBound.Qser_lower_bounds_proof z ⟨hz0, hz1⟩).1
  have := Real.sqrt_le_sqrt h1
  simpa using this

theorem sq_sqrt_Qser {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.sqrt (Qser z) ^ 2 = Qser z := by
  have h1 : (1 : ℝ) ≤ Qser z := (EntropyBound.Qser_lower_bounds_proof z ⟨hz0, hz1⟩).1
  exact Real.sq_sqrt (by linarith)

/-- The generic reduction used by both end ranges: if `√Q ≥ σ ≥ 8/9`, `Q = (√Q)²` and the
correction term `(1-z) Q'` is small, the quotient is `≥ 8/9`. -/
theorem ader_ge_of {z σ T : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : σ ≤ Real.sqrt (Qser z)) (hσ1 : (1 : ℝ) ≤ σ)
    (_hT0 : 0 ≤ (1 - z) * Qder z) (hT : (1 - z) * Qder z ≤ T)
    (hmargin : T ≤ σ * (σ - 8 / 9)) :
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  have hS1 : (1 : ℝ) ≤ Real.sqrt (Qser z) := sqrt_Qser_ge_one hz0 hz1
  have hSpos : 0 < Real.sqrt (Qser z) := by linarith
  have hSsq : Real.sqrt (Qser z) ^ 2 = Qser z := sq_sqrt_Qser hz0 hz1
  rw [le_div_iff₀ hSpos]
  nlinarith [hSsq, hS1, hσ, hσ1, _hT0, hT, hmargin]

end

end EntropyBound.EntropySpeed

namespace EntropyBound

noncomputable section

/-! ### E1 — `Ader_lower_small` (#33), the range `(0, 1/10]` -/

theorem Ader_lower_small_proof :
    ∀ z : ℝ, 0 < z → z ≤ 1 / 10 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  intro z hz0 hz1
  have hz0' : (0 : ℝ) ≤ z := le_of_lt hz0
  have hz1' : z ≤ 1 := by linarith
  have hz1'' : z < 1 := by linarith
  obtain ⟨hQd0, hQd1, -⟩ := EntropyBound.Qder_upper_bounds_proof z hz0' hz1''
  -- `Q' z ≤ z / (1 - z²) ≤ 10/99`
  have hden : (0 : ℝ) < 1 - z ^ 2 := by nlinarith
  have hQd : Qder z ≤ 10 / 99 := by
    refine hQd1.trans ?_
    rw [div_le_iff₀ hden]
    nlinarith
  have hT0 : 0 ≤ (1 - z) * Qder z := mul_nonneg (by linarith) hQd0
  have hT : (1 - z) * Qder z ≤ 10 / 99 := by nlinarith
  refine EntropySpeed.ader_ge_of hz0' hz1' (le_refl _) ?_ hT0 hT ?_
  · exact EntropySpeed.sqrt_Qser_ge_one hz0' hz1'
  · -- `σ = √Q ≥ 1`, so `σ (σ - 8/9) ≥ 1/9 > 10/99`
    have hS1 : (1 : ℝ) ≤ Real.sqrt (Qser z) := EntropySpeed.sqrt_Qser_ge_one hz0' hz1'
    nlinarith [hS1]

/-! ### E2 — `Ader_lower_large` (#34), the range `[99999/100000, 1)` -/

theorem Ader_lower_large_proof :
    ∀ z : ℝ, 99999 / 100000 ≤ z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  intro z hz0 hz1
  have hzpos : (0 : ℝ) < z := by linarith
  have hz0' : (0 : ℝ) ≤ z := le_of_lt hzpos
  have hz1' : z ≤ 1 := le_of_lt hz1
  -- `√Q ≥ 27/25` from `Q ≥ 1 + z²/6`
  have hQ2 : 1 + z ^ 2 / 6 ≤ Qser z := (EntropyBound.Qser_lower_bounds_proof z ⟨hz0', hz1'⟩).2
  have hQ729 : (729 : ℝ) / 625 ≤ Qser z := by nlinarith
  have hσ : (27 : ℝ) / 25 ≤ Real.sqrt (Qser z) := by
    have h := Real.sqrt_le_sqrt hQ729
    have hval : Real.sqrt ((729 : ℝ) / 625) = 27 / 25 := by
      rw [show (729 : ℝ) / 625 = (27 / 25) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rwa [hval] at h
  -- `Q' z ≤ -log (1 - z²) / z` and `-log (1 - z²) ≤ 2 / √(1 - z²)`
  obtain ⟨hQd0, -, hQd2⟩ := EntropyBound.Qder_upper_bounds_proof z hz0' hz1
  have hden : (0 : ℝ) < 1 - z ^ 2 := by nlinarith
  set r : ℝ := Real.sqrt (1 - z ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hden
  have hrsq : r ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (le_of_lt hden)
  have hlog : -Real.log (1 - z ^ 2) ≤ 2 / r := by
    have h := Real.log_le_sub_one_of_pos (x := r⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hlr : Real.log (1 - z ^ 2) = 2 * Real.log r := by
      rw [← hrsq, show r ^ 2 = r * r by ring, Real.log_mul (ne_of_gt hr0) (ne_of_gt hr0)]
      ring
    rw [hlr, show (2 : ℝ) / r = 2 * (1 / r) by ring]
    have hrinv : r⁻¹ = 1 / r := by rw [inv_eq_one_div]
    rw [hrinv] at h
    linarith
  -- `(1 - z) / r ≤ √(1 - z) ≤ 1/300`
  set q : ℝ := Real.sqrt (1 - z) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hqsq : q ^ 2 = 1 - z := Real.sq_sqrt (by linarith)
  have hqr : q ≤ r := by
    rw [hq, hr]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hq300 : q ≤ 1 / 300 := by
    rw [hq, show (1 : ℝ) / 300 = Real.sqrt ((1 / 300) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- assemble `(1 - z) * Q' z ≤ 1/100`
  have hT0 : 0 ≤ (1 - z) * Qder z := mul_nonneg (by linarith) hQd0
  have hT : (1 - z) * Qder z ≤ 1 / 100 := by
    have hstep : (1 - z) * Qder z ≤ (1 - z) * (-Real.log (1 - z ^ 2) / z) :=
      mul_le_mul_of_nonneg_left (hQd2 hzpos) (by linarith)
    have hstep2 : (1 - z) * (-Real.log (1 - z ^ 2) / z) ≤ (1 - z) * ((2 / r) / z) := by
      have hdiv : -Real.log (1 - z ^ 2) / z ≤ (2 / r) / z := by gcongr
      exact mul_le_mul_of_nonneg_left hdiv (by linarith)
    have hstep3 : (1 - z) * ((2 / r) / z) ≤ 1 / 100 := by
      have hkey : (1 - z) / r ≤ q := by
        rw [div_le_iff₀ hr0, ← hqsq]
        nlinarith
      have hexp : (1 - z) * ((2 / r) / z) = 2 * ((1 - z) / r) / z := by
        field_simp
      rw [hexp, div_le_iff₀ hzpos]
      nlinarith
    linarith
  refine EntropySpeed.ader_ge_of hz0' hz1' hσ (by norm_num) hT0 hT ?_
  norm_num

end

end EntropyBound

namespace EntropyBound.Solution

theorem Ader_lower_small :
    ∀ z : ℝ, 0 < z → z ≤ 1 / 10 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) :=
  EntropyBound.Ader_lower_small_proof

theorem Ader_lower_large :
    ∀ z : ℝ, 99999 / 100000 ≤ z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) :=
  EntropyBound.Ader_lower_large_proof

end EntropyBound.Solution

example : @EntropyBound.Ader_lower_small = @EntropyBound.Solution.Ader_lower_small := rfl
example : @EntropyBound.Ader_lower_large = @EntropyBound.Solution.Ader_lower_large := rfl

namespace EntropyBound.EntropySpeed

/-! ### E4 — the case split, in hypothesis form

`Ader_lower_middle` (#35) is still `sorry`, so it is taken as a hypothesis here rather than
cited; once Agent 2's `EntropySpeed/Middle.lean` lands, `Ader_lower_bound` (#36) becomes
`Ader_lower_of_middle EntropyBound.Ader_lower_middle_proof`. -/

theorem Ader_lower_of_middle
    (hmid : ∀ z : ℝ, 1 / 10 ≤ z → z ≤ 99999 / 100000 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)) :
    ∀ z : ℝ, 0 < z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  intro z hz0 hz1
  rcases le_or_gt z (1 / 10) with h | h
  · exact EntropyBound.Ader_lower_small_proof z hz0 h
  · rcases le_or_gt z (99999 / 100000) with h' | h'
    · exact hmid z (le_of_lt h) h'
    · exact EntropyBound.Ader_lower_large_proof z (le_of_lt h') hz1

end EntropyBound.EntropySpeed
