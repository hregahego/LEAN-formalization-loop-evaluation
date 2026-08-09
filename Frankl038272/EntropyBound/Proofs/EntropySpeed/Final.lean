/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Proofs.EntropySpeed.Middle
import EntropyBound.Proofs.EntropySpeed.Ends
import EntropyBound.Proofs.EntropySpeed.Lip

/-!
# Stage E — closing items E4, E5, E6 (#36, #37, #38)

This file contains no new mathematics.  It composes the three hypothesis-form lemmas

* `EntropyBound.EntropySpeed.Ader_lower_of_middle` (`EntropySpeed/Ends.lean`),
* `EntropyBound.EntropySpeed.Aser_lipschitz_lower_of` (`EntropySpeed/Lip.lean`),
* `EntropyBound.EntropySpeed.entropy_speed_bound_of` (`EntropySpeed/Lip.lean`),

with the now-proved `EntropyBound.Ader_lower_middle_proof` (#35, `EntropySpeed/Middle.lean`),
closing the last three frozen theorems of Stage E.
-/

noncomputable section

namespace EntropyBound

/-- BLUEPRINT E4 — frozen theorem #36. -/
theorem Ader_lower_bound_proof :
    ∀ z : ℝ, 0 < z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) :=
  EntropyBound.EntropySpeed.Ader_lower_of_middle EntropyBound.Ader_lower_middle_proof

/-- BLUEPRINT E5 — frozen theorem #37. -/
theorem Aser_lipschitz_lower_proof :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (8 / 9) * |u - v| ≤ |Aser u - Aser v| :=
  EntropyBound.EntropySpeed.Aser_lipschitz_lower_of Ader_lower_bound_proof

/-- BLUEPRINT E6 — frozen theorem #38. -/
theorem entropy_speed_bound_proof :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (8 / 9) * |u - v|
        ≤ Real.sqrt (∑' m : ℕ,
            ((1 - u ^ 2) ^ (m + 1) - (1 - v ^ 2) ^ (m + 1)) ^ 2 / ((m + 1) * (m + 2))) :=
  EntropyBound.EntropySpeed.entropy_speed_bound_of Ader_lower_bound_proof

end EntropyBound

namespace EntropyBound.Solution

theorem Ader_lower_bound :
    ∀ z : ℝ, 0 < z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) :=
  EntropyBound.Ader_lower_bound_proof

theorem Aser_lipschitz_lower :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (8 / 9) * |u - v| ≤ |Aser u - Aser v| :=
  EntropyBound.Aser_lipschitz_lower_proof

theorem entropy_speed_bound :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (8 / 9) * |u - v|
        ≤ Real.sqrt (∑' m : ℕ,
            ((1 - u ^ 2) ^ (m + 1) - (1 - v ^ 2) ^ (m + 1)) ^ 2 / ((m + 1) * (m + 2))) :=
  EntropyBound.entropy_speed_bound_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.Ader_lower_bound = @EntropyBound.Solution.Ader_lower_bound := rfl

example : @EntropyBound.Aser_lipschitz_lower = @EntropyBound.Solution.Aser_lipschitz_lower := rfl

example : @EntropyBound.entropy_speed_bound = @EntropyBound.Solution.entropy_speed_bound := rfl

end EntropyBound

end
