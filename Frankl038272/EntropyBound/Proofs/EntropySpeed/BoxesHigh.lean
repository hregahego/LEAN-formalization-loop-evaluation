/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.EntropySpeed.BoxesLow

/-!
# Stage E item E3 — box certificates on `[13/20, 99999/100000]`

Certified endpoint enclosures and per-box lower bounds for
`Ader z = (Qser z - (1-z) * Qder z) / Real.sqrt (Qser z)` on `[13/20, 99999/100000]`.

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

/-! #### Certificates at `z = 13/20` -/

theorem Qlo_11 : (1.08601534078355 : ℝ) ≤ Qser (13/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_11 lo2_11 (by norm_num)

/-! #### Certificates at `z = 7/10` -/

theorem lo1_12 : (0.53062825106217 : ℝ) ≤ Real.log (1 + 7/10) := by
  have h := log_ge_of (17/10) (0.53062825106217) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_12 : (-1.20397280432594 : ℝ) ≤ Real.log (1 - 7/10) := by
  have h := log_ge_of (3/10) (-1.20397280432594) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_12 : Real.log (1 + 7/10) ≤ (0.53062825106218 : ℝ) := by
  have h := log_le_of (17/10) (0.53062825106218) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_12 : Real.log (1 - 7/10) ≤ (-1.20397280432593 : ℝ) := by
  have h := log_le_of (3/10) (-1.20397280432593) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_12 : (1.10382895001613 : ℝ) ≤ Qser (7/10) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_12 lo2_12 (by norm_num)

theorem Qhi_12 : Qser (7/10) ≤ (1.10382895001618 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_12 hi2_12 (by norm_num)

theorem Dhi_12 : Qder (7/10) ≤ (0.38620515380719 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_12 lo2_12 (by norm_num)

/-! #### Certificates at `z = 3/4` -/

theorem lo1_13 : (0.55961578793542 : ℝ) ≤ Real.log (1 + 3/4) := by
  have h := log_ge_of (7/4) (0.55961578793542) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_13 : (-1.38629436111990 : ℝ) ≤ Real.log (1 - 3/4) := by
  have h := log_ge_of (1/4) (-1.38629436111990) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_13 : Real.log (1 + 3/4) ≤ (0.55961578793543 : ℝ) := by
  have h := log_le_of (7/4) (0.55961578793543) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_13 : Real.log (1 - 3/4) ≤ (-1.38629436111988 : ℝ) := by
  have h := log_le_of (1/4) (-1.38629436111988) 2 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_13 : (1.12489606863468 : ℝ) ≤ Qser (3/4) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_13 lo2_13 (by norm_num)

theorem Qhi_13 : Qser (3/4) ≤ (1.12489606863473 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_13 hi2_13 (by norm_num)

theorem Dhi_13 : Qder (3/4) ≤ (0.45967297085030 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_13 lo2_13 (by norm_num)

/-! #### Certificates at `z = 4/5` -/

theorem lo1_14 : (0.58778666490211 : ℝ) ≤ Real.log (1 + 4/5) := by
  have h := log_ge_of (9/5) (0.58778666490211) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_14 : (-1.60943791243411 : ℝ) ≤ Real.log (1 - 4/5) := by
  have h := log_ge_of (1/5) (-1.60943791243411) 3 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_14 : Real.log (1 + 4/5) ≤ (0.58778666490212 : ℝ) := by
  have h := log_le_of (9/5) (0.58778666490212) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_14 : Real.log (1 - 4/5) ≤ (-1.60943791243409 : ℝ) := by
  have h := log_le_of (1/5) (-1.60943791243409) 3 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_14 : (1.15020064740152 : ℝ) ≤ Qser (4/5) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_14 lo2_14 (by norm_num)

theorem Qhi_14 : Qser (4/5) ≤ (1.15020064740156 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_14 hi2_14 (by norm_num)

theorem Dhi_14 : Qder (4/5) ≤ (0.55766178358404 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_14 lo2_14 (by norm_num)

/-! #### Certificates at `z = 17/20` -/

theorem lo1_15 : (0.61518563909023 : ℝ) ≤ Real.log (1 + 17/20) := by
  have h := log_ge_of (37/20) (0.61518563909023) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_15 : (-1.89711998488589 : ℝ) ≤ Real.log (1 - 17/20) := by
  have h := log_ge_of (3/20) (-1.89711998488589) 3 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_15 : Real.log (1 + 17/20) ≤ (0.61518563909024 : ℝ) := by
  have h := log_le_of (37/20) (0.61518563909024) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_15 : Real.log (1 - 17/20) ≤ (-1.89711998488587 : ℝ) := by
  have h := log_le_of (3/20) (-1.89711998488587) 3 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_15 : (1.18135008246926 : ℝ) ≤ Qser (17/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_15 lo2_15 (by norm_num)

theorem Qhi_15 : Qser (17/20) ≤ (1.18135008246930 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_15 hi2_15 (by norm_num)

theorem Dhi_15 : Qder (17/20) ≤ (0.69759236509118 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_15 lo2_15 (by norm_num)

/-! #### Certificates at `z = 9/10` -/

theorem lo1_16 : (0.64185388617239 : ℝ) ≤ Real.log (1 + 9/10) := by
  have h := log_ge_of (19/10) (0.64185388617239) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_16 : (-2.30258509299405 : ℝ) ≤ Real.log (1 - 9/10) := by
  have h := log_ge_of (1/10) (-2.30258509299405) 4 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_16 : Real.log (1 + 9/10) ≤ (0.64185388617240 : ℝ) := by
  have h := log_le_of (19/10) (0.64185388617240) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_16 : Real.log (1 - 9/10) ≤ (-2.30258509299403 : ℝ) := by
  have h := log_le_of (1/10) (-2.30258509299403) 4 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_16 : (1.22131342521992 : ℝ) ≤ Qser (9/10) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_16 lo2_16 (by norm_num)

theorem Qhi_16 : Qser (9/10) ≤ (1.22131342521995 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_16 hi2_16 (by norm_num)

theorem Dhi_16 : Qder (9/10) ≤ (0.92108001700072 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_16 lo2_16 (by norm_num)

/-! #### Certificates at `z = 19/20` -/

theorem lo1_17 : (0.66782937257565 : ℝ) ≤ Real.log (1 + 19/20) := by
  have h := log_ge_of (39/20) (0.66782937257565) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_17 : (-2.99573227355400 : ℝ) ≤ Real.log (1 - 19/20) := by
  have h := log_ge_of (1/20) (-2.99573227355400) 5 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_17 : Real.log (1 + 19/20) ≤ (0.66782937257566 : ℝ) := by
  have h := log_le_of (39/20) (0.66782937257566) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_17 : Real.log (1 - 19/20) ≤ (-2.99573227355397 : ℝ) := by
  have h := log_le_of (1/20) (-2.99573227355397) 5 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_17 : (1.27698688403857 : ℝ) ≤ Qser (19/20) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_17 lo2_17 (by norm_num)

theorem Qhi_17 : Qser (19/20) ≤ (1.27698688403861 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_17 hi2_17 (by norm_num)

theorem Dhi_17 : Qder (19/20) ≤ (1.37095464427297 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_17 lo2_17 (by norm_num)

/-! #### Certificates at `z = 39/40` -/

theorem lo1_18 : (0.68056839835308 : ℝ) ≤ Real.log (1 + 39/40) := by
  have h := log_ge_of (79/40) (0.68056839835308) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_18 : (-3.68887945411394 : ℝ) ≤ Real.log (1 - 39/40) := by
  have h := log_ge_of (1/40) (-3.68887945411394) 6 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_18 : Real.log (1 + 39/40) ≤ (0.68056839835309 : ℝ) := by
  have h := log_le_of (79/40) (0.68056839835309) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_18 : Real.log (1 - 39/40) ≤ (-3.68887945411392 : ℝ) := by
  have h := log_le_of (1/40) (-3.68887945411392) 6 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_18 : (1.31692370850175 : ℝ) ≤ Qser (39/40) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_18 lo2_18 (by norm_num)

theorem Qhi_18 : Qser (39/40) ≤ (1.31692370850179 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_18 hi2_18 (by norm_num)

theorem Dhi_18 : Qder (39/40) ≤ (1.89501288193409 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_18 lo2_18 (by norm_num)

/-! #### Certificates at `z = 99/100` -/

theorem lo1_19 : (0.68813463873639 : ℝ) ≤ Real.log (1 + 99/100) := by
  have h := log_ge_of (199/100) (0.68813463873639) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_19 : (-4.60517018598810 : ℝ) ≤ Real.log (1 - 99/100) := by
  have h := log_ge_of (1/100) (-4.60517018598810) 7 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_19 : Real.log (1 + 99/100) ≤ (0.68813463873641 : ℝ) := by
  have h := log_le_of (199/100) (0.68813463873641) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_19 : Real.log (1 - 99/100) ≤ (-4.60517018598807 : ℝ) := by
  have h := log_le_of (1/100) (-4.60517018598807) 7 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_19 : (1.35020531499391 : ℝ) ≤ Qser (99/100) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_19 lo2_19 (by norm_num)

theorem Qhi_19 : Qser (99/100) ≤ (1.35020531499396 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_19 hi2_19 (by norm_num)

theorem Dhi_19 : Qder (99/100) ≤ (2.67309284872620 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_19 lo2_19 (by norm_num)

/-! #### Certificates at `z = 199/200` -/

theorem lo1_20 : (0.69064405034182 : ℝ) ≤ Real.log (1 + 199/200) := by
  have h := log_ge_of (399/200) (0.69064405034182) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_20 : (-5.29831736654804 : ℝ) ≤ Real.log (1 - 199/200) := by
  have h := log_ge_of (1/200) (-5.29831736654804) 8 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_20 : Real.log (1 + 199/200) ≤ (0.69064405034183 : ℝ) := by
  have h := log_le_of (399/200) (0.69064405034183) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_20 : Real.log (1 - 199/200) ≤ (-5.29831736654801 : ℝ) := by
  have h := log_le_of (1/200) (-5.29831736654801) 8 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_20 : (1.36495875720228 : ℝ) ≤ Qser (199/200) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_20 lo2_20 (by norm_num)

theorem Qhi_20 : Qser (199/200) ≤ (1.36495875720231 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_20 hi2_20 (by norm_num)

theorem Dhi_20 : Qder (199/200) ≤ (3.30566752360528 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_20 lo2_20 (by norm_num)

/-! #### Certificates at `z = 999/1000` -/

theorem lo1_21 : (0.69264705551826 : ℝ) ≤ Real.log (1 + 999/1000) := by
  have h := log_ge_of (1999/1000) (0.69264705551826) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_21 : (-6.90775527898214 : ℝ) ≤ Real.log (1 - 999/1000) := by
  have h := log_ge_of (1/1000) (-6.90775527898214) 10 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_21 : Real.log (1 + 999/1000) ≤ (0.69264705551827 : ℝ) := by
  have h := log_le_of (1999/1000) (0.69264705551827) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_21 : Real.log (1 - 999/1000) ≤ (-6.90775527898211 : ℝ) := by
  have h := log_le_of (1/1000) (-6.90775527898211) 10 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qlo_21 : (1.38045323471822 : ℝ) ≤ Qser (999/1000) :=
  Qser_ge_of (by norm_num) (by norm_num) lo1_21 lo2_21 (by norm_num)

theorem Qhi_21 : Qser (999/1000) ≤ (1.38045323471825 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_21 hi2_21 (by norm_num)

theorem Dhi_21 : Qder (999/1000) ≤ (4.85195583124005 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_21 lo2_21 (by norm_num)

/-! #### Certificates at `z = 99999/100000` -/

theorem lo1_22 : (0.69314218054744 : ℝ) ≤ Real.log (1 + 99999/100000) := by
  have h := log_ge_of (199999/100000) (0.69314218054744) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem lo2_22 : (-11.51292546497023 : ℝ) ≤ Real.log (1 - 99999/100000) := by
  have h := log_ge_of (1/100000) (-11.51292546497023) 17 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi1_22 : Real.log (1 + 99999/100000) ≤ (0.69314218054745 : ℝ) := by
  have h := log_le_of (199999/100000) (0.69314218054745) 0 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem hi2_22 : Real.log (1 - 99999/100000) ≤ (-11.51292546497019 : ℝ) := by
  have h := log_le_of (1/100000) (-11.51292546497019) 17 14 14 (by norm_num)
    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])
  norm_num at h ⊢
  linarith

theorem Qhi_22 : Qser (99999/100000) ≤ (1.38619002408031 : ℝ) :=
  Qser_le_of (by norm_num) (by norm_num) hi1_22 hi2_22 (by norm_num)

theorem Dhi_22 : Qder (99999/100000) ≤ (9.43390399829416 : ℝ) :=
  Qder_le_of (by norm_num) (by norm_num) lo1_22 lo2_22 (by norm_num)

/-! #### The per-box bounds -/

theorem box_11 : ∀ z : ℝ, 13/20 ≤ z → z ≤ 7/10 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 13/20) (b := 7/10) ?_ ?_ ?_ Qlo_11 Qhi_12 Dhi_12 ?_ ?_ <;>
    norm_num

theorem box_12 : ∀ z : ℝ, 7/10 ≤ z → z ≤ 3/4 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 7/10) (b := 3/4) ?_ ?_ ?_ Qlo_12 Qhi_13 Dhi_13 ?_ ?_ <;>
    norm_num

theorem box_13 : ∀ z : ℝ, 3/4 ≤ z → z ≤ 4/5 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 3/4) (b := 4/5) ?_ ?_ ?_ Qlo_13 Qhi_14 Dhi_14 ?_ ?_ <;>
    norm_num

theorem box_14 : ∀ z : ℝ, 4/5 ≤ z → z ≤ 17/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 4/5) (b := 17/20) ?_ ?_ ?_ Qlo_14 Qhi_15 Dhi_15 ?_ ?_ <;>
    norm_num

theorem box_15 : ∀ z : ℝ, 17/20 ≤ z → z ≤ 9/10 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 17/20) (b := 9/10) ?_ ?_ ?_ Qlo_15 Qhi_16 Dhi_16 ?_ ?_ <;>
    norm_num

theorem box_16 : ∀ z : ℝ, 9/10 ≤ z → z ≤ 19/20 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 9/10) (b := 19/20) ?_ ?_ ?_ Qlo_16 Qhi_17 Dhi_17 ?_ ?_ <;>
    norm_num

theorem box_17 : ∀ z : ℝ, 19/20 ≤ z → z ≤ 39/40 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 19/20) (b := 39/40) ?_ ?_ ?_ Qlo_17 Qhi_18 Dhi_18 ?_ ?_ <;>
    norm_num

theorem box_18 : ∀ z : ℝ, 39/40 ≤ z → z ≤ 99/100 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 39/40) (b := 99/100) ?_ ?_ ?_ Qlo_18 Qhi_19 Dhi_19 ?_ ?_ <;>
    norm_num

theorem box_19 : ∀ z : ℝ, 99/100 ≤ z → z ≤ 199/200 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 99/100) (b := 199/200) ?_ ?_ ?_ Qlo_19 Qhi_20 Dhi_20 ?_ ?_ <;>
    norm_num

theorem box_20 : ∀ z : ℝ, 199/200 ≤ z → z ≤ 999/1000 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 199/200) (b := 999/1000) ?_ ?_ ?_ Qlo_20 Qhi_21 Dhi_21 ?_ ?_ <;>
    norm_num

theorem box_21 : ∀ z : ℝ, 999/1000 ≤ z → z ≤ 99999/100000 →
    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  refine box_bound (a := 999/1000) (b := 99999/100000) ?_ ?_ ?_ Qlo_21 Qhi_22 Dhi_22 ?_ ?_ <;>
    norm_num

end EntropyBound.EntropySpeed

end
