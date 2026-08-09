/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems

/-!
# Stage C · C1–C2 — the sign-average identity and the range of the kernel

`SKETCH.md` Step 3 (3a) / `BLUEPRINT.md` Stage C, items C1 and C2.

The kernel `q(s,t) = s t (1 + λ² (1-s)(1-t))` with `λ = 9/10` is exhibited as the average
over a uniform sign `U ∈ {±1}` of the product `(s + U λ s(1-s))(t + U λ t(1-t))`; the four
factors all lie in `[0,1]` when `s, t ∈ [0,1]`, so `q(s,t) ∈ [0,1]` as a convex combination.
-/

namespace EntropyBound.RankOne

open Set

/-- The "minus" factor `s - λ s (1-s)` is nonnegative on `[0,1]`: it equals
`s * (1/10 + (9/10) s)`. -/
theorem sub_factor_nonneg {s : ℝ} (hs0 : 0 ≤ s) :
    0 ≤ s - lam * s * (1 - s) := by
  have h : s - lam * s * (1 - s) = s * (1 / 10 + (9 / 10) * s) := by
    simp only [lam]; ring
  rw [h]
  nlinarith [hs0]

/-- The intermediate product `λ s (1-s)` is nonnegative on `[0,1]`. -/
theorem lam_mul_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (0 : ℝ) ≤ lam * s * (1 - s) := by
  simp only [lam]
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]

/-- The "plus" factor `s + λ s (1-s)` is at most `1` on `[0,1]`: it is bounded by
`s (2 - s) = 1 - (1-s)²`. -/
theorem add_factor_le_one {s : ℝ} (hs1 : s ≤ 1) :
    s + lam * s * (1 - s) ≤ 1 := by
  simp only [lam]
  nlinarith [sq_nonneg (1 - s), sub_nonneg.mpr hs1]

/-- The "plus" factor is nonnegative on `[0,1]`. -/
theorem add_factor_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ s + lam * s * (1 - s) := by
  have h := lam_mul_nonneg hs0 hs1
  linarith

/-- The "minus" factor is at most `1` on `[0,1]`, since it is dominated by the "plus"
factor. -/
theorem sub_factor_le_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s - lam * s * (1 - s) ≤ 1 := by
  have h := lam_mul_nonneg hs0 hs1
  have h' := add_factor_le_one hs1
  linarith

end EntropyBound.RankOne

namespace EntropyBound

/-- Frozen theorem #21 (`q_sign_average`). -/
theorem q_sign_average_proof :
    ∀ s t : ℝ, qker s t
      = (1 / 2) * ((s + lam * s * (1 - s)) * (t + lam * t * (1 - t)))
        + (1 / 2) * ((s - lam * s * (1 - s)) * (t - lam * t * (1 - t))) := by
  intro s t
  simp only [qker, lam]
  ring

/-- Frozen theorem #22 (`q_mem_Icc`). -/
theorem q_mem_Icc_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, qker s t ∈ Set.Icc (0 : ℝ) 1 := by
  rintro s ⟨hs0, hs1⟩ t ⟨ht0, ht1⟩
  have hsp0 := RankOne.add_factor_nonneg hs0 hs1
  have hsp1 := RankOne.add_factor_le_one hs1
  have hsm0 := RankOne.sub_factor_nonneg hs0
  have hsm1 := RankOne.sub_factor_le_one hs0 hs1
  have htp0 := RankOne.add_factor_nonneg ht0 ht1
  have htp1 := RankOne.add_factor_le_one ht1
  have htm0 := RankOne.sub_factor_nonneg ht0
  have htm1 := RankOne.sub_factor_le_one ht0 ht1
  have hplus : (s + lam * s * (1 - s)) * (t + lam * t * (1 - t)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hsp0 htp0, by nlinarith⟩
  have hminus : (s - lam * s * (1 - s)) * (t - lam * t * (1 - t)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hsm0 htm0, by nlinarith⟩
  rw [q_sign_average_proof s t]
  exact ⟨by linarith [hplus.1, hminus.1], by linarith [hplus.2, hminus.2]⟩

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #21, restated verbatim. -/
theorem q_sign_average :
    ∀ s t : ℝ, qker s t
      = (1 / 2) * ((s + lam * s * (1 - s)) * (t + lam * t * (1 - t)))
        + (1 / 2) * ((s - lam * s * (1 - s)) * (t - lam * t * (1 - t))) :=
  EntropyBound.q_sign_average_proof

/-- Frozen theorem #22, restated verbatim. -/
theorem q_mem_Icc :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, qker s t ∈ Set.Icc (0 : ℝ) 1 :=
  EntropyBound.q_mem_Icc_proof

end EntropyBound.Solution

example : @EntropyBound.q_sign_average = @EntropyBound.Solution.q_sign_average := rfl
example : @EntropyBound.q_mem_Icc = @EntropyBound.Solution.q_mem_Icc := rfl

/-- Guardrail: the tabulated value of `q` at the symmetric midpoint. -/
example : EntropyBound.qker (1 / 2) (1 / 2) = 481 / 1600 := by
  simp only [EntropyBound.qker]; norm_num
