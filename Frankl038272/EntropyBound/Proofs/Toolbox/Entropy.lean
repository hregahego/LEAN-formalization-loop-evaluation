/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems

/-!
# Stage B preamble — the `Hnat` ↔ `Real.binEntropy` bridge, and the two-sided entropy bound

This file contains

* `EntropyBound.Toolbox.Hnat_eq_binEntropy`, the *single* bridge between the frozen `Hnat`
  of `Defs.lean` and Mathlib's `Real.binEntropy`, proved once as an equality of **functions**
  (BLUEPRINT Stage B preamble; the Cheat-watch box forbids restating `Hnat` facts through
  `Real.binEntropy`'s API with different constants);
* frozen theorem #7 `binEntropy_two_sided` (`SKETCH.md` (2b), BLUEPRINT B2).
-/

namespace EntropyBound.Toolbox

/-- **Bridge lemma.**  The frozen natural-log binary entropy `Hnat` *is* Mathlib's
`Real.binEntropy`, as an equality of functions on `ℝ` (junk values included). -/
theorem Hnat_eq_binEntropy : Hnat = Real.binEntropy := by
  funext z
  simp only [Hnat, Real.binEntropy, Real.log_inv]
  ring

/-- `z ≤ -log (1 - z)` for `z < 1`: the elementary lower half of `SKETCH.md` (2b). -/
theorem le_neg_log_one_sub {z : ℝ} (hz : z < 1) : z ≤ -Real.log (1 - z) := by
  have h : Real.log (1 - z) ≤ (1 - z) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  linarith

/-- `-(1 - z) * log (1 - z) ≤ z` for `z < 1`: the elementary upper half of `SKETCH.md` (2b),
in the multiplied-out form that avoids dividing by `1 - z`. -/
theorem neg_one_sub_mul_log_le {z : ℝ} (hz : z < 1) : -((1 - z) * Real.log (1 - z)) ≤ z := by
  have h1z : (0 : ℝ) < 1 - z := by linarith
  have h : Real.log (1 - z)⁻¹ ≤ (1 - z)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h
  have h' : (1 - z) * -Real.log (1 - z) ≤ (1 - z) * ((1 - z)⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left h h1z.le
  rw [mul_sub, mul_inv_cancel₀ (ne_of_gt h1z), mul_one] at h'
  linarith

end EntropyBound.Toolbox

namespace EntropyBound

/-- Frozen theorem #7 (`SKETCH.md` (2b), BLUEPRINT B2). -/
theorem binEntropy_two_sided_proof :
    ∀ z : ℝ, 0 < z → z < 1 →
      z * (Real.log (1 / z) + 1 - z) ≤ Hnat z ∧ Hnat z ≤ z * (Real.log (1 / z) + 1) := by
  intro z hz0 hz1
  have h1z : (0 : ℝ) < 1 - z := by linarith
  have hinv : Real.log (1 / z) = -Real.log z := by
    rw [one_div, Real.log_inv]
  have hlo : z * (1 - z) ≤ -((1 - z) * Real.log (1 - z)) := by
    have h := Toolbox.le_neg_log_one_sub hz1
    have := mul_le_mul_of_nonneg_left h h1z.le
    nlinarith [this]
  have hhi : -((1 - z) * Real.log (1 - z)) ≤ z := Toolbox.neg_one_sub_mul_log_le hz1
  constructor
  · simp only [Hnat, hinv]
    nlinarith [hlo]
  · simp only [Hnat, hinv]
    nlinarith [hhi]

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #7, restated verbatim. -/
theorem binEntropy_two_sided :
    ∀ z : ℝ, 0 < z → z < 1 →
      z * (Real.log (1 / z) + 1 - z) ≤ Hnat z ∧ Hnat z ≤ z * (Real.log (1 / z) + 1) :=
  EntropyBound.binEntropy_two_sided_proof

end EntropyBound.Solution

/-- No-drift gate for frozen theorem #7. -/
example : @EntropyBound.binEntropy_two_sided = @EntropyBound.Solution.binEntropy_two_sided := rfl
