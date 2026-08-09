/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Entropy
import EntropyBound.Proofs.Toolbox.Series
import EntropyBound.Proofs.Toolbox.Parabola

/-!
# Stage B — the series `Q` (`SKETCH.md` (2f), BLUEPRINT B6)

Frozen theorems #11 `Qser_closed_form` and #12 `Qser_lower_bounds`.

Both come straight from the `ψ`-series of `Parabola.lean`: since
`ψ z = ∑_{j ≥ 0} z^(2j+2)/((j+1)(2j+1))` for `|z| < 1`, dividing by `z²` gives
`Qser z = ψ z / z²`, which is the frozen closed form.  The lower bounds are the first one
resp. two nonnegative terms of the honest series (`Summable.sum_le_tsum` over
`Finset.range 1`/`Finset.range 2`) — no series is truncated, only bounded from below.
-/

open Filter Finset
open scoped Topology

namespace EntropyBound.Toolbox

/-- The `Qser` summand is summable on `[-1,1]`, by domination by `1/((j+1)(2j+1))`. -/
theorem summable_Qser_term {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun j : ℕ => z ^ (2 * j) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) summable_coeff
  have hp : z ^ (2 * j) ≤ 1 := pow_le_one₀ hz0 hz1
  gcongr

/-- The `Qser` series in closed form on `(0,1)`. -/
theorem hasSum_Qser {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ (2 * j) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)))
      (psi z / z ^ 2) := by
  have habs : |z| < 1 := by rw [abs_of_pos hz0]; exact hz1
  have hz : z ≠ 0 := ne_of_gt hz0
  refine hasSum_congr_fun ((hasSum_psi habs).div_const (z ^ 2)) fun j => ?_
  have hD : (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)) ≠ 0 := by positivity
  rw [pow_add]
  field_simp

end EntropyBound.Toolbox

namespace EntropyBound

/-- Frozen theorem #11 (`SKETCH.md` (2f), BLUEPRINT B6). -/
theorem Qser_closed_form_proof :
    ∀ z : ℝ, 0 < z → z < 1 →
      Qser z = ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / z ^ 2 := by
  intro z hz0 hz1
  have h := (Toolbox.hasSum_Qser hz0 hz1).tsum_eq
  simp only [Qser]
  rw [h, Toolbox.psi]

/-- Frozen theorem #12 (`SKETCH.md` (2f), BLUEPRINT B6). -/
theorem Qser_lower_bounds_proof :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 1 ≤ Qser z ∧ 1 + z ^ 2 / 6 ≤ Qser z := by
  intro z hz
  obtain ⟨hz0, hz1⟩ := hz
  have hsum := Toolbox.summable_Qser_term hz0 hz1
  have h2 : 1 + z ^ 2 / 6 ≤ Qser z := by
    have hle := hsum.sum_le_tsum (Finset.range 2) (fun i _ => by positivity)
    have hval : ∑ j ∈ Finset.range 2, z ^ (2 * j) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))
        = 1 + z ^ 2 / 6 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [hval] at hle
    exact hle
  refine ⟨?_, h2⟩
  have : (0 : ℝ) ≤ z ^ 2 / 6 := by positivity
  linarith

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #11, restated verbatim. -/
theorem Qser_closed_form :
    ∀ z : ℝ, 0 < z → z < 1 →
      Qser z = ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) / z ^ 2 :=
  EntropyBound.Qser_closed_form_proof

/-- Frozen theorem #12, restated verbatim. -/
theorem Qser_lower_bounds :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 1 ≤ Qser z ∧ 1 + z ^ 2 / 6 ≤ Qser z :=
  EntropyBound.Qser_lower_bounds_proof

end EntropyBound.Solution

/-- No-drift gates for frozen theorems #11 and #12. -/
example : @EntropyBound.Qser_closed_form = @EntropyBound.Solution.Qser_closed_form := rfl

example : @EntropyBound.Qser_lower_bounds = @EntropyBound.Solution.Qser_lower_bounds := rfl
