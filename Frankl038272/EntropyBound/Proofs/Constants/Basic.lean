/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Constants.LogEnclose

/-!
# Stage A — exact rational constants and numeric logarithm bounds (`SKETCH.md` Step 1)

This module discharges the five frozen Stage A statements #1–#5:

* `strict_margin` (A1) — pure rational arithmetic;
* `log_ten_lower` (A2) and `log_ten_upper` (A3) — the two-sided enclosure `2 < log 10 < 12/5`,
  obtained from the certified `artanh` enclosure of `Constants/LogEnclose.lean` at `a = 10`,
  truncation depth `J = 4`;
* `log_two_upper` (A4) — `log 2 < 25/36`, from the same enclosure at `a = 2`, `J = 2`.  This
  reproduces `SKETCH.md` (1b) exactly: `logMid 2 2 = 56/81`, `logTail 2 2 = 1/540`, so
  `log 2 ≤ 1123/1620 < 1125/1620 = 25/36`;
* `C_lt_ratio_123_65` (A5) — pure rational arithmetic.

All bounds are statements about `Real.log` itself; `logLo`/`logHi` are *certificates*, never
surrogates (see the Stage A cheat-watch box of `BLUEPRINT.md`).

Support lemmas live in `namespace EntropyBound.Constants`.
-/

namespace EntropyBound.Constants

/-! ### Exact evaluation of the enclosure at `a = 2` and `a = 10` -/

theorem yOf_two : yOf 2 = 1 / 3 := by norm_num [yOf]

theorem yOf_ten : yOf 10 = 9 / 11 := by norm_num [yOf]

theorem logMid_two_two : logMid 2 2 = 56 / 81 := by
  simp only [logMid, yOf_two, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem logTail_two_two : logTail 2 2 = 1 / 540 := by
  rw [logTail_of_one_le 2 2 (by norm_num), yOf_two]
  norm_num

/-- `log 2 ≤ 1123/1620`, the exact `SKETCH.md` (1b) certificate. -/
theorem logHi_two_two : logHi 2 2 = 1123 / 1620 := by
  rw [logHi, logMid_two_two, logTail_two_two]
  norm_num

theorem logMid_ten_four : logMid 10 4 = 1512985536 / 682050985 := by
  simp only [logMid, yOf_ten, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem logTail_ten_four : logTail 10 4 = 43046721 / 389743420 := by
  rw [logTail_of_one_le 10 4 (by norm_num), yOf_ten]
  norm_num

theorem logLo_ten_four : logLo 10 4 = 5750615097 / 2728203940 := by
  rw [logLo, logMid_ten_four, logTail_ten_four]
  norm_num

theorem logHi_ten_four : logHi 10 4 = 6353269191 / 2728203940 := by
  rw [logHi, logMid_ten_four, logTail_ten_four]
  norm_num

/-- `Real.log 2 ≤ 1123/1620`. -/
theorem log_two_le : Real.log 2 ≤ 1123 / 1620 := by
  have h := le_logHi 2 2 (by norm_num)
  rw [logHi_two_two] at h
  norm_num at h
  exact h

/-- `5750615097/2728203940 ≤ Real.log 10`. -/
theorem log_ten_ge : (5750615097 : ℝ) / 2728203940 ≤ Real.log 10 := by
  have h := logLo_le 10 4 (by norm_num)
  rw [logLo_ten_four] at h
  norm_num at h
  exact h

/-- `Real.log 10 ≤ 6353269191/2728203940`. -/
theorem log_ten_le : Real.log 10 ≤ 6353269191 / 2728203940 := by
  have h := le_logHi 10 4 (by norm_num)
  rw [logHi_ten_four] at h
  norm_num at h
  exact h

end EntropyBound.Constants

namespace EntropyBound

/-! ### A1 — the strict margin -/

theorem strict_margin_proof : Cval * (1 - cval) - 1 = 929 / 156250000 := by
  simp only [Cval, cval]
  norm_num

/-! ### A2 — `2 < Real.log 10` -/

theorem log_ten_lower_proof : (2 : ℝ) < Real.log 10 := by
  have h := Constants.log_ten_ge
  have : (2 : ℝ) < (5750615097 : ℝ) / 2728203940 := by norm_num
  linarith

/-! ### A3 — `Real.log 10 < 12/5` -/

theorem log_ten_upper_proof : Real.log 10 < 12 / 5 := by
  have h := Constants.log_ten_le
  have : (6353269191 : ℝ) / 2728203940 < 12 / 5 := by norm_num
  linarith

/-! ### A4 — `Real.log 2 < 25/36` -/

theorem log_two_upper_proof : Real.log 2 < 25 / 36 := by
  have h := Constants.log_two_le
  have : (1123 : ℝ) / 1620 < 25 / 36 := by norm_num
  linarith

/-! ### A5 — `(10/9) C < 123/65` -/

theorem C_lt_ratio_123_65_proof : (10 / 9) * Cval < 123 / 65 := by
  simp only [Cval]
  norm_num

end EntropyBound

namespace EntropyBound.Solution

theorem strict_margin : Cval * (1 - cval) - 1 = 929 / 156250000 :=
  EntropyBound.strict_margin_proof

theorem log_ten_lower : (2 : ℝ) < Real.log 10 :=
  EntropyBound.log_ten_lower_proof

theorem log_ten_upper : Real.log 10 < 12 / 5 :=
  EntropyBound.log_ten_upper_proof

theorem log_two_upper : Real.log 2 < 25 / 36 :=
  EntropyBound.log_two_upper_proof

theorem C_lt_ratio_123_65 : (10 / 9) * Cval < 123 / 65 :=
  EntropyBound.C_lt_ratio_123_65_proof

end EntropyBound.Solution

/-! ### No-drift gates -/

example : @EntropyBound.strict_margin = @EntropyBound.Solution.strict_margin := rfl
example : @EntropyBound.log_ten_lower = @EntropyBound.Solution.log_ten_lower := rfl
example : @EntropyBound.log_ten_upper = @EntropyBound.Solution.log_ten_upper := rfl
example : @EntropyBound.log_two_upper = @EntropyBound.Solution.log_two_upper := rfl
example : @EntropyBound.C_lt_ratio_123_65 = @EntropyBound.Solution.C_lt_ratio_123_65 := rfl

/-! ### Stage A guardrail (`BLUEPRINT.md` cheat-watch box): Step 6's margin -/

example : (25 : ℝ) / 324 > Real.log 2 / 9 := by
  have h := EntropyBound.log_two_upper_proof
  linarith
