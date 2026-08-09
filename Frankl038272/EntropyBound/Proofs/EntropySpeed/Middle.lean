/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Proofs.EntropySpeed.BoxesHigh

/-!
# Stage E item E3 / OBLIGATION 1 — `Ader_lower_middle` (#35)

Chains the 22 closed-box certificates of
`EntropyBound/Proofs/EntropySpeed/Boxes{Low,High}.lean` into the frozen theorem

```
Ader_lower_middle : ∀ z : ℝ, 1 / 10 ≤ z → z ≤ 99999 / 100000 →
  8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)
```

The partition of `[1/10, 99999/100000]` is the explicit list

```
1/10, 3/20, 1/5, 1/4, 3/10, 7/20, 2/5, 9/20, 1/2, 11/20, 3/5, 13/20,
7/10, 3/4, 4/5, 17/20, 9/10, 19/20, 39/40, 99/100, 199/200, 999/1000, 99999/100000
```

Each `box_j` bounds `Ader` uniformly on the **closed** box `[p j, p (j+1)]` (via
`EntropyBound.EntropySpeed.box_bound`, i.e. by monotonicity of `Qser` and `Qder` together
with certified rational enclosures at the two endpoints), so the case split below is a
genuine cover, not a grid evaluation.
-/

noncomputable section

namespace EntropyBound

open EntropyBound.EntropySpeed

theorem Ader_lower_middle_proof :
    ∀ z : ℝ, 1 / 10 ≤ z → z ≤ 99999 / 100000 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  intro z h1 h2
  rcases le_or_gt z (3/20) with hc1 | hc1
  · exact box_0 z h1 hc1
  rcases le_or_gt z (1/5) with hc2 | hc2
  · exact box_1 z hc1.le hc2
  rcases le_or_gt z (1/4) with hc3 | hc3
  · exact box_2 z hc2.le hc3
  rcases le_or_gt z (3/10) with hc4 | hc4
  · exact box_3 z hc3.le hc4
  rcases le_or_gt z (7/20) with hc5 | hc5
  · exact box_4 z hc4.le hc5
  rcases le_or_gt z (2/5) with hc6 | hc6
  · exact box_5 z hc5.le hc6
  rcases le_or_gt z (9/20) with hc7 | hc7
  · exact box_6 z hc6.le hc7
  rcases le_or_gt z (1/2) with hc8 | hc8
  · exact box_7 z hc7.le hc8
  rcases le_or_gt z (11/20) with hc9 | hc9
  · exact box_8 z hc8.le hc9
  rcases le_or_gt z (3/5) with hc10 | hc10
  · exact box_9 z hc9.le hc10
  rcases le_or_gt z (13/20) with hc11 | hc11
  · exact box_10 z hc10.le hc11
  rcases le_or_gt z (7/10) with hc12 | hc12
  · exact box_11 z hc11.le hc12
  rcases le_or_gt z (3/4) with hc13 | hc13
  · exact box_12 z hc12.le hc13
  rcases le_or_gt z (4/5) with hc14 | hc14
  · exact box_13 z hc13.le hc14
  rcases le_or_gt z (17/20) with hc15 | hc15
  · exact box_14 z hc14.le hc15
  rcases le_or_gt z (9/10) with hc16 | hc16
  · exact box_15 z hc15.le hc16
  rcases le_or_gt z (19/20) with hc17 | hc17
  · exact box_16 z hc16.le hc17
  rcases le_or_gt z (39/40) with hc18 | hc18
  · exact box_17 z hc17.le hc18
  rcases le_or_gt z (99/100) with hc19 | hc19
  · exact box_18 z hc18.le hc19
  rcases le_or_gt z (199/200) with hc20 | hc20
  · exact box_19 z hc19.le hc20
  rcases le_or_gt z (999/1000) with hc21 | hc21
  · exact box_20 z hc20.le hc21
  exact box_21 z hc21.le h2

end EntropyBound

namespace EntropyBound.Solution

theorem Ader_lower_middle :
    ∀ z : ℝ, 1 / 10 ≤ z → z ≤ 99999 / 100000 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) :=
  EntropyBound.Ader_lower_middle_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.Ader_lower_middle = @EntropyBound.Solution.Ader_lower_middle := rfl

end EntropyBound

end
