/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.EntropySpeed.Enclose

/-!
# Stage E item E3 — box certificates on `[1/10, 13/20]`

Certified endpoint enclosures and per-box lower bounds for
`Ader z = (Qser z - (1-z) * Qder z) / Real.sqrt (Qser z)` on `[1/10, 13/20]`.

Every number here is a **certificate**: the `Real.log` bounds come from
`EntropyBound.EntropySpeed.log_ge_of` / `.log_le_of` (the shared artanh series of
`EntropyBound.Constants.logLo`/`logHi` at depth `J = 14`, after a `2 ^ k` shift), the
`Qser`/`Qder` bounds from `EntropyBound.EntropySpeed.Qser_ge_of` / `.Qser_le_of` /
`.Qder_le_of`, and each `box_*` lemma from `EntropyBound.EntropySpeed.box_bound`, which
bounds `Ader` on the whole **closed** box — no grid evaluation anywhere.
-/

noncomputable section

namespace EntropyBound.EntropySpeed

open EntropyBound.Constants

/-! #### Certificates at `z = 1/10` -/

theorem lo1_0 : (0.09531017980432 : ℝ) ≤ Real.log (1 + 1/10) := by
  have h := log_ge_of (11/10) (0.09531017980432) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_0 : (-0.10536051565783 : ℝ) ≤ Real.log (1 - 1/10) := by
  have h := log_ge_of (9/10) (-0.10536051565783) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_0 : (1.00167336927050 : ℝ) ≤ Qser (1/10) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_0 lo2_0 (by norm_num)

/-! #### Certificates at `z = 3/20` -/

theorem lo1_1 : (0.13976194237515 : ℝ) ≤ Real.log (1 + 3/20) := by
  have h := log_ge_of (23/20) (0.13976194237515) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_1 : (-0.16251892949778 : ℝ) ≤ Real.log (1 - 3/20) := by
  have h := log_ge_of (17/20) (-0.16251892949778) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_1 : Real.log (1 + 3/20) ≤ (0.13976194237516 : ℝ) := by
  have h := log_le_of (23/20) (0.13976194237516) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_1 : Real.log (1 - 3/20) ≤ (-0.16251892949777 : ℝ) := by
  have h := log_le_of (17/20) (-0.16251892949777) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_1 : (1.00378416259153 : ℝ) ≤ Qser (3/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_1 lo2_1 (by norm_num)

theorem Qhi_1 : Qser (3/20) ≤ (1.00378416259243 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_1 hi2_1 (by norm_num)

theorem Dhi_1 : Qder (3/20) ≤ (0.05091658202089 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_1 lo2_1 (by norm_num)

/-! #### Certificates at `z = 1/5` -/

theorem lo1_2 : (0.18232155679395 : ℝ) ≤ Real.log (1 + 1/5) := by
  have h := log_ge_of (6/5) (0.18232155679395) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_2 : (-0.22314355131421 : ℝ) ≤ Real.log (1 - 1/5) := by
  have h := log_ge_of (4/5) (-0.22314355131421) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_2 : Real.log (1 + 1/5) ≤ (0.18232155679396 : ℝ) := by
  have h := log_le_of (6/5) (0.18232155679396) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_2 : Real.log (1 - 1/5) ≤ (-0.22314355131420 : ℝ) := by
  have h := log_le_of (4/5) (-0.22314355131420) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_2 : (1.00677567753430 : ℝ) ≤ Qser (1/5) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_2 lo2_2 (by norm_num)

theorem Qhi_2 : Qser (1/5) ≤ (1.00677567753480 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_2 hi2_2 (by norm_num)

theorem Dhi_2 : Qder (1/5) ≤ (0.06887092736100 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_2 lo2_2 (by norm_num)

/-! #### Certificates at `z = 1/4` -/

theorem lo1_3 : (0.22314355131420 : ℝ) ≤ Real.log (1 + 1/4) := by
  have h := log_ge_of (5/4) (0.22314355131420) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_3 : (-0.28768207245179 : ℝ) ≤ Real.log (1 - 1/4) := by
  have h := log_ge_of (3/4) (-0.28768207245179) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_3 : Real.log (1 + 1/4) ≤ (0.22314355131421 : ℝ) := by
  have h := log_le_of (5/4) (0.22314355131421) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_3 : Real.log (1 - 1/4) ≤ (-0.28768207245177 : ℝ) := by
  have h := log_le_of (3/4) (-0.28768207245177) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_3 : (1.01068615686252 : ℝ) ≤ Qser (1/4) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_3 lo2_3 (by norm_num)

theorem Qhi_3 : Qser (1/4) ≤ (1.01068615686296 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_3 hi2_3 (by norm_num)

theorem Dhi_3 : Qder (1/4) ≤ (0.08772072535568 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_3 lo2_3 (by norm_num)

/-! #### Certificates at `z = 3/10` -/

theorem lo1_4 : (0.26236426446749 : ℝ) ≤ Real.log (1 + 3/10) := by
  have h := log_ge_of (13/10) (0.26236426446749) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_4 : (-0.35667494393874 : ℝ) ≤ Real.log (1 - 3/10) := by
  have h := log_ge_of (7/10) (-0.35667494393874) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_4 : Real.log (1 + 3/10) ≤ (0.26236426446750 : ℝ) := by
  have h := log_le_of (13/10) (0.26236426446750) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_4 : Real.log (1 - 3/10) ≤ (-0.35667494393873 : ℝ) := by
  have h := log_le_of (7/10) (-0.35667494393873) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_4 : (1.01556758945132 : ℝ) ≤ Qser (3/10) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_4 lo2_4 (by norm_num)

theorem Qhi_4 : Qser (3/10) ≤ (1.01556758945155 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_4 hi2_4 (by norm_num)

theorem Dhi_4 : Qder (3/10) ≤ (0.10776283039375 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_4 lo2_4 (by norm_num)

/-! #### Certificates at `z = 7/20` -/

theorem lo1_5 : (0.30010459245033 : ℝ) ≤ Real.log (1 + 7/20) := by
  have h := log_ge_of (27/20) (0.30010459245033) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_5 : (-0.43078291609246 : ℝ) ≤ Real.log (1 - 7/20) := by
  have h := log_ge_of (13/20) (-0.43078291609246) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_5 : Real.log (1 + 7/20) ≤ (0.30010459245034 : ℝ) := by
  have h := log_le_of (27/20) (0.30010459245034) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_5 : Real.log (1 - 7/20) ≤ (-0.43078291609245 : ℝ) := by
  have h := log_le_of (13/20) (-0.43078291609245) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_5 : (1.02148819875793 : ℝ) ≤ Qser (7/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_5 lo2_5 (by norm_num)

theorem Qhi_5 : Qser (7/20) ≤ (1.02148819875810 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_5 hi2_5 (by norm_num)

theorem Dhi_5 : Qder (7/20) ≤ (0.12935321969175 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_5 lo2_5 (by norm_num)

/-! #### Certificates at `z = 2/5` -/

theorem lo1_6 : (0.33647223662121 : ℝ) ≤ Real.log (1 + 2/5) := by
  have h := log_ge_of (7/5) (0.33647223662121) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_6 : (-0.51082562376600 : ℝ) ≤ Real.log (1 - 2/5) := by
  have h := log_ge_of (3/5) (-0.51082562376600) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_6 : Real.log (1 + 2/5) ≤ (0.33647223662122 : ℝ) := by
  have h := log_le_of (7/5) (0.33647223662122) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_6 : Real.log (1 - 2/5) ≤ (-0.51082562376598 : ℝ) := by
  have h := log_le_of (3/5) (-0.51082562376598) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_6 : (1.02853598131308 : ℝ) ≤ Qser (2/5) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_6 lo2_6 (by norm_num)

theorem Qhi_6 : Qser (2/5) ≤ (1.02853598131325 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_6 hi2_6 (by norm_num)

theorem Dhi_6 : Qder (2/5) ≤ (0.15293172085463 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_6 lo2_6 (by norm_num)

/-! #### Certificates at `z = 9/20` -/

theorem lo1_7 : (0.37156355643248 : ℝ) ≤ Real.log (1 + 9/20) := by
  have h := log_ge_of (29/20) (0.37156355643248) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_7 : (-0.59783700075563 : ℝ) ≤ Real.log (1 - 9/20) := by
  have h := log_ge_of (11/20) (-0.59783700075563) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_7 : Real.log (1 + 9/20) ≤ (0.37156355643249 : ℝ) := by
  have h := log_le_of (29/20) (0.37156355643249) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_7 : Real.log (1 - 9/20) ≤ (-0.59783700075561 : ℝ) := by
  have h := log_le_of (11/20) (-0.59783700075561) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_7 : (1.03682373536542 : ℝ) ≤ Qser (9/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_7 lo2_7 (by norm_num)

theorem Qhi_7 : Qser (9/20) ≤ (1.03682373536556 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_7 hi2_7 (by norm_num)

theorem Dhi_7 : Qder (9/20) ≤ (0.17905775486037 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_7 lo2_7 (by norm_num)

/-! #### Certificates at `z = 1/2` -/

theorem lo1_8 : (0.40546510810816 : ℝ) ≤ Real.log (1 + 1/2) := by
  have h := log_ge_of (3/2) (0.40546510810816) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_8 : (-0.69314718055995 : ℝ) ≤ Real.log (1 - 1/2) := by
  have h := log_ge_of (1/2) (-0.69314718055995) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_8 : Real.log (1 + 1/2) ≤ (0.40546510810817 : ℝ) := by
  have h := log_le_of (3/2) (0.40546510810817) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_8 : Real.log (1 - 1/2) ≤ (-0.69314718055994 : ℝ) := by
  have h := log_le_of (1/2) (-0.69314718055994) 1 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_8 : (1.04649628752906 : ℝ) ≤ Qser (1/2) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_8 lo2_8 (by norm_num)

theorem Qhi_8 : Qser (1/2) ≤ (1.04649628752914 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_8 hi2_8 (by norm_num)

theorem Dhi_8 : Qder (1/2) ≤ (0.20846400455620 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_8 lo2_8 (by norm_num)

/-! #### Certificates at `z = 11/20` -/

theorem lo1_9 : (0.43825493093115 : ℝ) ≤ Real.log (1 + 11/20) := by
  have h := log_ge_of (31/20) (0.43825493093115) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_9 : (-0.79850769621778 : ℝ) ≤ Real.log (1 - 11/20) := by
  have h := log_ge_of (9/20) (-0.79850769621778) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_9 : Real.log (1 + 11/20) ≤ (0.43825493093116 : ℝ) := by
  have h := log_le_of (31/20) (0.43825493093116) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_9 : Real.log (1 - 11/20) ≤ (-0.79850769621776 : ℝ) := by
  have h := log_le_of (9/20) (-0.79850769621776) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_9 : (1.05774108973646 : ℝ) ≤ Qser (11/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_9 lo2_9 (by norm_num)

theorem Qhi_9 : Qser (11/20) ≤ (1.05774108973655 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_9 hi2_9 (by norm_num)

theorem Dhi_9 : Qder (11/20) ≤ (0.24214025930187 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_9 lo2_9 (by norm_num)

/-! #### Certificates at `z = 3/5` -/

theorem lo1_10 : (0.47000362924573 : ℝ) ≤ Real.log (1 + 3/5) := by
  have h := log_ge_of (8/5) (0.47000362924573) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_10 : (-0.91629073187416 : ℝ) ≤ Real.log (1 - 3/5) := by
  have h := log_ge_of (2/5) (-0.91629073187416) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_10 : Real.log (1 + 3/5) ≤ (0.47000362924574 : ℝ) := by
  have h := log_le_of (8/5) (0.47000362924574) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_10 : Real.log (1 - 3/5) ≤ (-0.91629073187415 : ℝ) := by
  have h := log_le_of (2/5) (-0.91629073187415) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_10 : (1.07080420567640 : ℝ) ≤ Qser (3/5) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_10 lo2_10 (by norm_num)

theorem Qhi_10 : Qser (3/5) ≤ (1.07080420567646 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_10 hi2_10 (by norm_num)

theorem Dhi_10 : Qder (3/5) ≤ (0.28147031752281 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_10 lo2_10 (by norm_num)

/-! #### Certificates at `z = 13/20` -/

theorem lo1_11 : (0.50077528791248 : ℝ) ≤ Real.log (1 + 13/20) := by
  have h := log_ge_of (33/20) (0.50077528791248) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_11 : (-1.04982212449868 : ℝ) ≤ Real.log (1 - 13/20) := by
  have h := log_ge_of (7/20) (-1.04982212449868) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_11 : Real.log (1 + 13/20) ≤ (0.50077528791249 : ℝ) := by
  have h := log_le_of (33/20) (0.50077528791249) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_11 : Real.log (1 - 13/20) ≤ (-1.04982212449867 : ℝ) := by
  have h := log_le_of (7/20) (-1.04982212449867) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qhi_11 : Qser (13/20) ≤ (1.08601534078361 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_11 hi2_11 (by norm_num)

theorem Dhi_11 : Qder (13/20) ≤ (0.32846738317760 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_11 lo2_11 (by norm_num)

/-! #### The per-box bounds -/

theorem box_0 : ∀ z : ℝ, 1/10 ≤ z → z ≤ 3/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 1/10) (b := 3/20) ?_ ?_ ?_ Qlo_0 Qhi_1 Dhi_1 ?_ ?_ <;>
    norm_num

theorem box_1 : ∀ z : ℝ, 3/20 ≤ z → z ≤ 1/5 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 3/20) (b := 1/5) ?_ ?_ ?_ Qlo_1 Qhi_2 Dhi_2 ?_ ?_ <;>
    norm_num

theorem box_2 : ∀ z : ℝ, 1/5 ≤ z → z ≤ 1/4 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 1/5) (b := 1/4) ?_ ?_ ?_ Qlo_2 Qhi_3 Dhi_3 ?_ ?_ <;>
    norm_num

theorem box_3 : ∀ z : ℝ, 1/4 ≤ z → z ≤ 3/10 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 1/4) (b := 3/10) ?_ ?_ ?_ Qlo_3 Qhi_4 Dhi_4 ?_ ?_ <;>
    norm_num

theorem box_4 : ∀ z : ℝ, 3/10 ≤ z → z ≤ 7/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 3/10) (b := 7/20) ?_ ?_ ?_ Qlo_4 Qhi_5 Dhi_5 ?_ ?_ <;>
    norm_num

theorem box_5 : ∀ z : ℝ, 7/20 ≤ z → z ≤ 2/5 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 7/20) (b := 2/5) ?_ ?_ ?_ Qlo_5 Qhi_6 Dhi_6 ?_ ?_ <;>
    norm_num

theorem box_6 : ∀ z : ℝ, 2/5 ≤ z → z ≤ 9/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 2/5) (b := 9/20) ?_ ?_ ?_ Qlo_6 Qhi_7 Dhi_7 ?_ ?_ <;>
    norm_num

theorem box_7 : ∀ z : ℝ, 9/20 ≤ z → z ≤ 1/2 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 9/20) (b := 1/2) ?_ ?_ ?_ Qlo_7 Qhi_8 Dhi_8 ?_ ?_ <;>
    norm_num

theorem box_8 : ∀ z : ℝ, 1/2 ≤ z → z ≤ 11/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 1/2) (b := 11/20) ?_ ?_ ?_ Qlo_8 Qhi_9 Dhi_9 ?_ ?_ <;>
    norm_num

theorem box_9 : ∀ z : ℝ, 11/20 ≤ z → z ≤ 3/5 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 11/20) (b := 3/5) ?_ ?_ ?_ Qlo_9 Qhi_10 Dhi_10 ?_ ?_ <;>
    norm_num

theorem box_10 : ∀ z : ℝ, 3/5 ≤ z → z ≤ 13/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 3/5) (b := 13/20) ?_ ?_ ?_ Qlo_10 Qhi_11 Dhi_11 ?_ ?_ <;>
    norm_num

end EntropyBound.EntropySpeed

end
