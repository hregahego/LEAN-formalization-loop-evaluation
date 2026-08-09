/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Scalar.Pointwise
import EntropyBound.Proofs.Diagonal.Middle
import EntropyBound.Proofs.OffDiagonal.Estimate

/-!
# Stage H — the decomposition, pointwise and scalar inequalities (`SKETCH.md` Step 8)

This file contains item **H1** of `BLUEPRINT.md` Part 2 Stage H, i.e. the frozen
theorem `Phi_decomposition` (#45), which is `SKETCH.md` (8a), together with items **H2**
and **H3** — the ones that consume `Phi_decomposition_proof` and are therefore downstream of
it.  Item **H4** and the two Stage H support lemmas live in the sibling module
`EntropyBound/Proofs/Scalar/Pointwise.lean`, which this file imports (the import must go this
way round: the root `EntropyBound.lean` reaches only `Scalar/Basic.lean`).

The identity holds for **all** reals with no hypotheses whatsoever: after unfolding `Phi`
and `Dfun` it is a `ring` identity, whose only content is `(9/10) * (1/9) = 1/10` together
with `g s ^ 2 + g t ^ 2 - (g s - g t) ^ 2 = 2 * g s * g t`.

All declarations belong to `namespace EntropyBound` and must never shadow a frozen name.
-/

namespace EntropyBound

/-! ### H1 — the decomposition identity (`SKETCH.md` (8a)) -/

theorem Phi_decomposition_proof :
    ∀ s t : ℝ, Phi s t
      = Dfun s + Dfun t
        + (9 / 10) * (2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2)
          - (Real.log 2 / 9) * (gprof s - gprof t) ^ 2) := by
  intro s t
  simp only [Phi, Dfun]
  ring

end EntropyBound

namespace EntropyBound.Solution

theorem Phi_decomposition :
    ∀ s t : ℝ, Phi s t
      = Dfun s + Dfun t
        + (9 / 10) * (2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2)
          - (Real.log 2 / 9) * (gprof s - gprof t) ^ 2) :=
  EntropyBound.Phi_decomposition_proof

end EntropyBound.Solution

/-- No-drift gate: the `Solution` restatement is syntactically the frozen statement. -/
example : @EntropyBound.Phi_decomposition = @EntropyBound.Solution.Phi_decomposition := rfl

namespace EntropyBound.Scalar

open EntropyBound

/-! ### H2 — nonnegativity of `Φ` on `(0,1]²`

`BLUEPRINT.md` Stage H item H2.  The hypothesis `hoff` is the frozen statement of
`off_diagonal_estimate` (#39) VERBATIM; it is taken as a hypothesis because Stage F is being
proved concurrently. -/

/-- **H2.**  `Φ` is nonnegative on `(0,1]²`: `Phi_decomposition` (#45) writes it as
`D s + D t + (9/10) · bracket`, the two diagonal terms are `≥ 0` by `diagonal_estimate` (#44)
and the bracket is `≥ 0` by `hoff`. -/
theorem Phi_nonneg_of
    (hoff : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      (Real.log 2 / 9) * (gprof s - gprof t) ^ 2
        ≤ 2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2)) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ Phi s t := by
  intro s hs0 hs1 t ht0 ht1
  have hDs : 0 ≤ Dfun s := EntropyBound.diagonal_estimate_proof s hs0 hs1
  have hDt : 0 ≤ Dfun t := EntropyBound.diagonal_estimate_proof t ht0 ht1
  have hbr := hoff s hs0 hs1 t ht0 ht1
  rw [EntropyBound.Phi_decomposition_proof s t]
  linarith

/-! ### H3 — the pointwise inequality (#46), in `hoff` form

`BLUEPRINT.md` Stage H item H3, `SKETCH.md` (8b): multiply H2 by `st > 0` and use
`z · eₙₐₜ z = Hₙₐₜ z` at `z = s`, `z = t`, `z = st`.  The boundary cases `s = 0` and `t = 0`
are handled separately — both sides are then `0` — which is why the frozen statement lives on
the CLOSED square `[0,1]²`. -/

/-- **H3.**  With `hoff` the frozen statement of `off_diagonal_estimate` (#39), the conclusion
is the frozen statement of `pointwise_inequality` (#46), VERBATIM. -/
theorem pointwise_inequality_of
    (hoff : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      (Real.log 2 / 9) * (gprof s - gprof t) ^ 2
        ≤ 2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Cval * (s * Hnat t + t * Hnat s)
        ≤ 2 * ((9 / 10) * Hnat (s * t)
          + (Real.log 2 / 10) * (s * t * gprof s * gprof t)) := by
  intro s hs t ht
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le hs0 with hs0' | hs0'
  · -- boundary `s = 0`: both sides vanish
    subst hs0'
    simp [Hnat_zero]
  rcases eq_or_lt_of_le ht0 with ht0' | ht0'
  · -- boundary `t = 0`: both sides vanish
    subst ht0'
    simp [Hnat_zero]
  have hst : (0 : ℝ) < s * t := mul_pos hs0' ht0'
  have hes : s * enat s = Hnat s := mul_enat_eq_Hnat s (ne_of_gt hs0')
  have het : t * enat t = Hnat t := mul_enat_eq_Hnat t (ne_of_gt ht0')
  have hest : s * t * enat (s * t) = Hnat (s * t) := mul_enat_eq_Hnat _ (ne_of_gt hst)
  have hPhi : 0 ≤ Phi s t := Phi_nonneg_of hoff s hs0' hs1 t ht0' ht1
  have key : s * t * Phi s t
      = 2 * ((9 / 10) * Hnat (s * t)
          + (Real.log 2 / 10) * (s * t * gprof s * gprof t))
        - Cval * (s * Hnat t + t * Hnat s) := by
    simp only [Phi]
    rw [← hes, ← het, ← hest]
    ring
  have hmul : 0 ≤ s * t * Phi s t := mul_nonneg (le_of_lt hst) hPhi
  rw [key] at hmul
  linarith

end EntropyBound.Scalar

/-! ### The two frozen Stage H theorems

`EntropyBound.off_diagonal_estimate_proof` (#39, `Proofs/OffDiagonal/Estimate.lean`) is
available, so the `hoff` hypothesis of H3 is discharged and both frozen theorems close. -/

namespace EntropyBound

theorem pointwise_inequality_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Cval * (s * Hnat t + t * Hnat s)
        ≤ 2 * ((9 / 10) * Hnat (s * t)
          + (Real.log 2 / 10) * (s * t * gprof s * gprof t)) :=
  EntropyBound.Scalar.pointwise_inequality_of EntropyBound.off_diagonal_estimate_proof

theorem scalar_inequality_proof {ι : Type} [Fintype ι] (w S : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hS : ∀ i, S i ∈ Set.Icc (0 : ℝ) 1) :
    Cval * (∑ i, w i * S i) * (∑ i, w i * Hnat (S i))
      ≤ (9 / 10) * (∑ i, ∑ j, w i * w j * Hnat (S i * S j))
        + (Real.log 2 / 10) * (∑ i, w i * (S i * gprof (S i))) ^ 2 :=
  EntropyBound.Scalar.scalar_inequality_of pointwise_inequality_proof w S hw hw1 hS

end EntropyBound

namespace EntropyBound.Solution

theorem pointwise_inequality :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Cval * (s * Hnat t + t * Hnat s)
        ≤ 2 * ((9 / 10) * Hnat (s * t)
          + (Real.log 2 / 10) * (s * t * gprof s * gprof t)) :=
  EntropyBound.pointwise_inequality_proof

theorem scalar_inequality {ι : Type} [Fintype ι] (w S : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hS : ∀ i, S i ∈ Set.Icc (0 : ℝ) 1) :
    Cval * (∑ i, w i * S i) * (∑ i, w i * Hnat (S i))
      ≤ (9 / 10) * (∑ i, ∑ j, w i * w j * Hnat (S i * S j))
        + (Real.log 2 / 10) * (∑ i, w i * (S i * gprof (S i))) ^ 2 :=
  EntropyBound.scalar_inequality_proof w S hw hw1 hS

end EntropyBound.Solution

/-- No-drift gate: the `Solution` restatement is syntactically the frozen statement. -/
example : @EntropyBound.pointwise_inequality = @EntropyBound.Solution.pointwise_inequality := rfl

/-- No-drift gate: the `Solution` restatement is syntactically the frozen statement. -/
example : @EntropyBound.scalar_inequality = @EntropyBound.Solution.scalar_inequality := rfl

/-- Stage H cheat-watch guardrail: `scalar_inequality` (#47) instantiated at `ι := Fin 1`,
`w := fun _ => 1`, `S := fun _ => 1/2`. -/
example :
    EntropyBound.Cval * (1 * (1 / 2 : ℝ)) * (1 * EntropyBound.Hnat (1 / 2))
      ≤ (9 / 10) * (1 * 1 * EntropyBound.Hnat ((1 / 2 : ℝ) * (1 / 2)))
        + (Real.log 2 / 10)
          * (1 * ((1 / 2 : ℝ) * EntropyBound.gprof (1 / 2))) ^ 2 := by
  have h := EntropyBound.scalar_inequality_proof (ι := Fin 1) (fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ) / 2) (fun _ => zero_le_one) (by simp)
    (fun _ => Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simpa using h
