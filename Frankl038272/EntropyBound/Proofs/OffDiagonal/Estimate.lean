/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Series
import EntropyBound.Proofs.ProfileSpeed.Basic
import EntropyBound.Proofs.Constants.Basic
import EntropyBound.Proofs.EntropySpeed.Final

/-!
# Stage F item F1 — the off-diagonal estimate (#39)

`SKETCH.md` Step 6 / BLUEPRINT F1.  With `u = √(1-s)`, `v = √(1-t)` (so `1 - u² = s` and
`1 - v² = t`) the chain is

```
2 e(st) - e(s²) - e(t²)  =  ∑' m, (s^(m+1) - t^(m+1))² / ((m+1)(m+2))   -- #10
                         ≥  (64/81) (u - v)²                             -- #38, squared
                         ≥  (64/81)(25/256) (g s - g t)²                 -- #32, squared
                         =  (25/324) (g s - g t)²
                         ≥  (log 2 / 9) (g s - g t)²                     -- #4
```

Both squaring steps are legitimate because both sides are nonnegative, and each such side
condition is discharged explicitly below.
-/

noncomputable section

namespace EntropyBound.OffDiagonal

open Real

/-- The frozen series of #10 / #38 is nonnegative: every term is a square over a positive
denominator. -/
theorem tsum_diff_nonneg (s t : ℝ) :
    0 ≤ ∑' m : ℕ, (s ^ (m + 1) - t ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  refine tsum_nonneg fun m => ?_
  have hd : (0 : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity
  exact div_nonneg (sq_nonneg _) hd.le

/-- `√(1-s) ∈ [0,1]` for `0 ≤ s` — the substitution domain of Step 6. -/
theorem sqrt_one_sub_mem {s : ℝ} (hs0 : 0 ≤ s) :
    Real.sqrt (1 - s) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have h : Real.sqrt (1 - s) ≤ Real.sqrt 1 :=
    Real.sqrt_le_sqrt (by linarith)
  simpa using h

/-- `1 - (√(1-s))² = s`. -/
theorem one_sub_sq_sqrt {s : ℝ} (hs1 : s ≤ 1) : 1 - (Real.sqrt (1 - s)) ^ 2 = s := by
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - s)]; ring

end EntropyBound.OffDiagonal

namespace EntropyBound

/-- BLUEPRINT F1 / SKETCH Step 6 — frozen theorem #39. -/
theorem off_diagonal_estimate_proof :
    ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      (Real.log 2 / 9) * (gprof s - gprof t) ^ 2
        ≤ 2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2) := by
  intro s hs0 hs1 t ht0 ht1
  set u : ℝ := Real.sqrt (1 - s) with hu_def
  set v : ℝ := Real.sqrt (1 - t) with hv_def
  have hu_mem : u ∈ Set.Icc (0 : ℝ) 1 := OffDiagonal.sqrt_one_sub_mem hs0.le
  have hv_mem : v ∈ Set.Icc (0 : ℝ) 1 := OffDiagonal.sqrt_one_sub_mem ht0.le
  have hus : 1 - u ^ 2 = s := OffDiagonal.one_sub_sq_sqrt hs1
  have hvt : 1 - v ^ 2 = t := OffDiagonal.one_sub_sq_sqrt ht1
  -- the frozen series, and its nonnegativity
  set T : ℝ := ∑' m : ℕ, (s ^ (m + 1) - t ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))
    with hT_def
  have hT0 : 0 ≤ T := OffDiagonal.tsum_diff_nonneg s t
  -- (1) #10: the left-hand side of the goal's right-hand side IS that series
  have h10 : 2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2) = T :=
    EntropyBound.enat_sum_of_squares_proof s t hs0 hs1 ht0 ht1
  -- (2) #38 at `u, v`, with `1 - u² = s` and `1 - v² = t`
  have h38 : 8 / 9 * |u - v| ≤ Real.sqrt T := by
    have h := EntropyBound.entropy_speed_bound_proof u hu_mem v hv_mem
    rwa [hus, hvt] at h
  -- square it: both sides are nonnegative
  have h38sq : (8 / 9) ^ 2 * (u - v) ^ 2 ≤ T := by
    have hnn : (0 : ℝ) ≤ 8 / 9 * |u - v| := by positivity
    have hsq : (8 / 9 * |u - v|) ^ 2 ≤ (Real.sqrt T) ^ 2 := by gcongr
    rwa [Real.sq_sqrt hT0, mul_pow, sq_abs] at hsq
  -- (3) #32, squared: `(u - v)² ≥ (25/256) (g s - g t)²`
  have h32 : |gprof s - gprof t| ≤ 16 / 5 * |u - v| :=
    EntropyBound.gprofile_lipschitz_proof s ⟨hs0.le, hs1⟩ t ⟨ht0.le, ht1⟩
  have h32sq : (gprof s - gprof t) ^ 2 ≤ (16 / 5) ^ 2 * (u - v) ^ 2 := by
    have hsq : |gprof s - gprof t| ^ 2 ≤ (16 / 5 * |u - v|) ^ 2 := by gcongr
    rwa [sq_abs, mul_pow, sq_abs] at hsq
  -- (4) `(64/81)(25/256) = 25/324` and `log 2 < 25/36` (#4)
  have hlog : Real.log 2 < 25 / 36 := EntropyBound.log_two_upper_proof
  have hgsq : (0 : ℝ) ≤ (gprof s - gprof t) ^ 2 := sq_nonneg _
  rw [h10]
  nlinarith [h38sq, h32sq, hlog, hgsq]

end EntropyBound

namespace EntropyBound.Solution

theorem off_diagonal_estimate :
    ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      (Real.log 2 / 9) * (gprof s - gprof t) ^ 2
        ≤ 2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2) :=
  EntropyBound.off_diagonal_estimate_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.off_diagonal_estimate = @EntropyBound.Solution.off_diagonal_estimate :=
  rfl

end EntropyBound

end
