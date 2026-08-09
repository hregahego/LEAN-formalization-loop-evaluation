/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Proofs.Diagonal.Deriv

/-!
# Stage G item G4 — box certificates for `diagonal_middle`, part A

Machine-generated per-box positivity certificates, boxes 0–44 of the partition of
`[1/8, 1 - 10^(-6)]`.  Each is an instance of `EntropyBound.Diagonal.Dfun_box_pos`, the
derivative-corrected mean-value box bound: on the CLOSED box `[a,b]`,
`Dfun s ≥ Dfun m - K * hh` where `K` certifiably bounds `|Dder|` on the whole box.  No
value of `Dfun` is ever sampled.  Every logarithm bound is a certified rational enclosure
coming from `EntropyBound.Constants.logLo_le` / `.le_logHi` through `Diagonal.logU` /
`Diagonal.logL`.  The exact partition is recorded in `PROGRESS.md`.
-/

noncomputable section

namespace EntropyBound.Diagonal

open EntropyBound


theorem box_000 {s : ℝ} (hs1 : (1 / 8) ≤ s) (hs2 : s ≤ (7 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (53 / 400) ≤ ((-3158082239931) / 1562500000000) :=
    logU (w := (53 / 400)) (c := (53 / 50))
      (q := (2913445406199 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-3158082239931) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-50529315838897) / 25000000000000) ≤ Real.log (53 / 400) :=
    logL (w := (53 / 400)) (c := (53 / 50))
      (q := (5826890812397 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-50529315838897) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-14213977974293) / 100000000000000) ≤ Real.log (1 - (53 / 400)) :=
    logL (w := (347 / 400)) (c := (347 / 200))
      (q := (27550370040851 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-14213977974293) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (53 / 400) ^ 2) ≤ ((-1771218757139) / 100000000000000) :=
    logU (w := (157191 / 160000)) (c := (157191 / 80000))
      (q := (13508699859771 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-1771218757139) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (1 / 8)) ≤ ((-13353139254379) / 100000000000000) :=
    logU (w := (7 / 8)) (c := (7 / 4))
      (q := (11192315760323 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-13353139254379) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-7541145002449) / 50000000000000) ≤ Real.log (1 - (7 / 50)) :=
    logL (w := (43 / 50)) (c := (43 / 25))
      (q := (54232428051097 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-7541145002449) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (1 / 8) ^ 2) ≤ ((-1574835570197) / 100000000000000) :=
    logU (w := (63 / 64)) (c := (63 / 32))
      (q := (67739882485797 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1574835570197) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1979477834421) / 100000000000000) ≤ Real.log (1 - (7 / 50) ^ 2) :=
    logL (w := (2451 / 2500)) (c := (2451 / 1250))
      (q := (33667620110787 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1979477834421) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (1 / 8) ≤ x → x ≤ (7 / 50) →
      (39547796514333 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (101326379685847 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (1 / 8)) (w := (3 / 200))
      (r1 := (739026147461 / 500000000000))
      (r2 := (13326849 / 1280000)) (r3 := (2604879 / 160000))
      (r4 := (85293 / 8000))
      (R := (1228444200007 / 50000000000000))
      (NL := (39547796514333 / 20000000000000)) (NU := (101326379685847 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (1 / 8)) (b := (7 / 50)) (m := (53 / 400))
    (hh := (3 / 400)) (K := (388391292867621 / 50000000000000))
    (bnd := (454671477985707 / 2500000000000000))
    (Lu := ((-3158082239931) / 1562500000000))
    (Ll := ((-50529315838897) / 25000000000000))
    (Ml := ((-14213977974293) / 100000000000000))
    (Nu := ((-1771218757139) / 100000000000000))
    (U1 := ((-13353139254379) / 100000000000000))
    (L1 := ((-7541145002449) / 50000000000000))
    (U2 := ((-1574835570197) / 100000000000000))
    (L2 := ((-1979477834421) / 100000000000000))
    (NL := (39547796514333 / 20000000000000))
    (NU := (101326379685847 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_001 {s : ℝ} (hs1 : (7 / 50) ≤ s) (hs2 : s ≤ (4 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (3 / 20) ≤ ((-94855999244293) / 50000000000000) :=
    logU (w := (3 / 20)) (c := (6 / 5))
      (q := (4558038919849 / 25000000000000)) (k := 3) (J := 6)
      (R := ((-94855999244293) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-189711998488591) / 100000000000000) ≤ Real.log (3 / 20) :=
    logL (w := (3 / 20)) (c := (6 / 5))
      (q := (9116077839697 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-189711998488591) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-2031486716837) / 12500000000000) ≤ Real.log (1 - (3 / 20)) :=
    logL (w := (17 / 20)) (c := (17 / 10))
      (q := (53062824321299 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2031486716837) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (3 / 20) ^ 2) ≤ ((-2275698603147) / 100000000000000) :=
    logU (w := (391 / 400)) (c := (391 / 200))
      (q := (67039019452847 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2275698603147) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (7 / 50)) ≤ ((-15082288968341) / 100000000000000) :=
    logU (w := (43 / 50)) (c := (43 / 25))
      (q := (54232429087653 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-15082288968341) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-697413572237) / 4000000000000) ≤ Real.log (1 - (4 / 25)) :=
    logL (w := (21 / 25)) (c := (42 / 25))
      (q := (5187937875007 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-697413572237) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (7 / 50) ^ 2) ≤ ((-989731308299) / 50000000000000) :=
    logU (w := (2451 / 2500)) (c := (2451 / 1250))
      (q := (16833813859849 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-989731308299) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-2593351698291) / 100000000000000) ≤ Real.log (1 - (4 / 25) ^ 2) :=
    logL (w := (609 / 625)) (c := (1218 / 625))
      (q := (8340170794713 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-2593351698291) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (7 / 50) ≤ x → x ≤ (4 / 25) →
      (12172278543 / 6103515625) ≤ Npoly x ∧
      Npoly x ≤ (1601075368177 / 781250000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (7 / 50)) (w := (1 / 50))
      (r1 := (7353441683 / 6250000000))
      (r2 := (605827431 / 62500000)) (r3 := (19562067 / 1250000))
      (r4 := (518319 / 50000))
      (R := (43023714673 / 1562500000000))
      (NL := (12172278543 / 6103515625)) (NU := (1601075368177 / 781250000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (7 / 50)) (b := (4 / 25)) (m := (3 / 20))
    (hh := (1 / 100)) (K := (803561126844397 / 100000000000000))
    (bnd := (326281431782839 / 2000000000000000))
    (Lu := ((-94855999244293) / 50000000000000))
    (Ll := ((-189711998488591) / 100000000000000))
    (Ml := ((-2031486716837) / 12500000000000))
    (Nu := ((-2275698603147) / 100000000000000))
    (U1 := ((-15082288968341) / 100000000000000))
    (L1 := ((-697413572237) / 4000000000000))
    (U2 := ((-989731308299) / 50000000000000))
    (L2 := ((-2593351698291) / 100000000000000))
    (NL := (12172278543 / 6103515625))
    (NU := (1601075368177 / 781250000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_002 {s : ℝ} (hs1 : (4 / 25) ≤ s) (hs2 : s ≤ (9 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (17 / 100) ≤ ((-5537365131037) / 3125000000000) :=
    logU (w := (17 / 100)) (c := (34 / 25))
      (q := (15374234987399 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-5537365131037) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-177195684193951) / 100000000000000) ≤ Real.log (17 / 100) :=
    logL (w := (17 / 100)) (c := (34 / 25))
      (q := (15374234987017 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-177195684193951) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-18632958260159) / 100000000000000) ≤ Real.log (1 - (17 / 100)) :=
    logL (w := (83 / 100)) (c := (83 / 50))
      (q := (12670439948959 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-18632958260159) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (17 / 100) ^ 2) ≤ ((-2932582843417) / 100000000000000) :=
    logU (w := (9711 / 10000)) (c := (9711 / 5000))
      (q := (66382135212577 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2932582843417) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (4 / 25)) ≤ ((-8717669355897) / 50000000000000) :=
    logU (w := (21 / 25)) (c := (42 / 25))
      (q := (259396896721 / 500000000000)) (k := 1) (J := 6)
      (R := ((-8717669355897) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-3969018839513) / 20000000000000) ≤ Real.log (1 - (9 / 50)) :=
    logL (w := (41 / 50)) (c := (41 / 25))
      (q := (4946962385843 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-3969018839513) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (4 / 25) ^ 2) ≤ ((-648334525177) / 25000000000000) :=
    logU (w := (609 / 625)) (c := (1218 / 625))
      (q := (33360689977643 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-648334525177) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1646830939459) / 50000000000000) ≤ Real.log (1 - (9 / 50) ^ 2) :=
    logL (w := (2419 / 2500)) (c := (2419 / 1250))
      (q := (66021056177077 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1646830939459) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (4 / 25) ≤ x → x ≤ (9 / 50) →
      (3159127021681 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (3220930987407 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (4 / 25)) (w := (1 / 50))
      (r1 := (315340673 / 390625000))
      (r2 := (68584563 / 7812500)) (r3 := (2318139 / 156250))
      (r4 := (124659 / 12500))
      (R := (30901982863 / 1562500000000))
      (NL := (3159127021681 / 1562500000000)) (NU := (3220930987407 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (4 / 25)) (b := (9 / 50)) (m := (17 / 100))
    (hh := (1 / 100)) (K := (63278633559653 / 10000000000000))
    (bnd := (144530709051719 / 1000000000000000))
    (Lu := ((-5537365131037) / 3125000000000))
    (Ll := ((-177195684193951) / 100000000000000))
    (Ml := ((-18632958260159) / 100000000000000))
    (Nu := ((-2932582843417) / 100000000000000))
    (U1 := ((-8717669355897) / 50000000000000))
    (L1 := ((-3969018839513) / 20000000000000))
    (U2 := ((-648334525177) / 25000000000000))
    (L2 := ((-1646830939459) / 50000000000000))
    (NL := (3159127021681 / 1562500000000))
    (NU := (3220930987407 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_003 {s : ℝ} (hs1 : (9 / 50) ≤ s) (hs2 : s ≤ (1 / 5)) :
    0 < Dfun s := by
  have hLu : Real.log (19 / 100) ≤ ((-166073120682047) / 100000000000000) :=
    logU (w := (19 / 100)) (c := (38 / 25))
      (q := (8374206697187 / 20000000000000)) (k := 3) (J := 6)
      (R := ((-166073120682047) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-83036560360787) / 50000000000000) ≤ Real.log (19 / 100) :=
    logL (w := (19 / 100)) (c := (38 / 25))
      (q := (41871033446411 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-83036560360787) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-21072103368497) / 100000000000000) ≤ Real.log (1 - (19 / 100)) :=
    logL (w := (81 / 100)) (c := (81 / 50))
      (q := (24121307343749 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-21072103368497) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (19 / 100) ^ 2) ≤ ((-1838386169297) / 50000000000000) :=
    logU (w := (9639 / 10000)) (c := (9639 / 5000))
      (q := (328189728587 / 500000000000)) (k := 1) (J := 6)
      (R := ((-1838386169297) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (9 / 50)) ≤ ((-19845093871043) / 100000000000000) :=
    logU (w := (41 / 50)) (c := (41 / 25))
      (q := (49469624184951 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-19845093871043) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-5578588825467) / 25000000000000) ≤ Real.log (1 - (1 / 5)) :=
    logL (w := (4 / 5)) (c := (8 / 5))
      (q := (47000362754127 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5578588825467) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (9 / 50) ^ 2) ≤ ((-411706242123) / 12500000000000) :=
    logU (w := (2419 / 2500)) (c := (2419 / 1250))
      (q := (6602106811901 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-411706242123) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1020552419259) / 25000000000000) ≤ Real.log (1 - (1 / 5) ^ 2) :=
    logL (w := (24 / 25)) (c := (48 / 25))
      (q := (65232508378959 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1020552419259) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (9 / 50) ≤ x → x ≤ (1 / 5) →
      (12461050799 / 6103515625) ≤ Npoly x ∧
      Npoly x ≤ (322987593739 / 156250000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (9 / 50)) (w := (1 / 50))
      (r1 := (2960040563 / 6250000000))
      (r2 := (494517393 / 62500000)) (r3 := (17567523 / 1250000))
      (r4 := (478953 / 50000))
      (R := (19923466423 / 1562500000000))
      (NL := (12461050799 / 6103515625)) (NU := (322987593739 / 156250000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (9 / 50)) (b := (1 / 5)) (m := (19 / 100))
    (hh := (1 / 100)) (K := (128379446662253 / 25000000000000))
    (bnd := (320654001588197 / 2500000000000000))
    (Lu := ((-166073120682047) / 100000000000000))
    (Ll := ((-83036560360787) / 50000000000000))
    (Ml := ((-21072103368497) / 100000000000000))
    (Nu := ((-1838386169297) / 50000000000000))
    (U1 := ((-19845093871043) / 100000000000000))
    (L1 := ((-5578588825467) / 25000000000000))
    (U2 := ((-411706242123) / 12500000000000))
    (L2 := ((-1020552419259) / 25000000000000))
    (NL := (12461050799 / 6103515625))
    (NU := (322987593739 / 156250000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_004 {s : ℝ} (hs1 : (1 / 5) ≤ s) (hs2 : s ≤ (11 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (21 / 100) ≤ ((-78032387411891) / 50000000000000) :=
    logU (w := (21 / 100)) (c := (42 / 25))
      (q := (259396896721 / 500000000000)) (k := 3) (J := 6)
      (R := ((-78032387411891) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-31212955083583) / 20000000000000) ≤ Real.log (21 / 100) :=
    logL (w := (21 / 100)) (c := (42 / 25))
      (q := (5187937875007 / 10000000000000)) (k := 3) (J := 6)
      (R := ((-31212955083583) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-11786116736531) / 50000000000000) ≤ Real.log (1 - (21 / 100)) :=
    logL (w := (79 / 100)) (c := (79 / 50))
      (q := (45742484582933 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-11786116736531) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (21 / 100) ^ 2) ≤ ((-112754933103) / 2500000000000) :=
    logU (w := (9559 / 10000)) (c := (9559 / 5000))
      (q := (32402260365937 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-112754933103) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (1 / 5)) ≤ ((-22314355130787) / 100000000000000) :=
    logU (w := (4 / 5)) (c := (8 / 5))
      (q := (47000362925207 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-22314355130787) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-6211534003609) / 25000000000000) ≤ Real.log (1 - (11 / 50)) :=
    logL (w := (39 / 50)) (c := (39 / 25))
      (q := (44468582041559 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-6211534003609) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (1 / 5) ^ 2) ≤ ((-2041099689127) / 50000000000000) :=
    logU (w := (24 / 25)) (c := (48 / 25))
      (q := (3261625933887 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-2041099689127) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-2480529353297) / 50000000000000) ≤ Real.log (1 - (11 / 50) ^ 2) :=
    logL (w := (2379 / 2500)) (c := (2379 / 1250))
      (q := (64353659349401 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2480529353297) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (1 / 5) ≤ x → x ≤ (11 / 50) →
      (3209952470967 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (3230009129033 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (1 / 5)) (w := (1 / 50))
      (r1 := (27137 / 156250))
      (r2 := (110808 / 15625)) (r3 := (166293 / 12500))
      (r4 := (45927 / 5000))
      (R := (10028329033 / 1562500000000))
      (NL := (3209952470967 / 1562500000000)) (NU := (3230009129033 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (1 / 5)) (b := (11 / 50)) (m := (21 / 100))
    (hh := (1 / 100)) (K := (426658663904637 / 100000000000000))
    (bnd := (113870189839471 / 1000000000000000))
    (Lu := ((-78032387411891) / 50000000000000))
    (Ll := ((-31212955083583) / 20000000000000))
    (Ml := ((-11786116736531) / 50000000000000))
    (Nu := ((-112754933103) / 2500000000000))
    (U1 := ((-22314355130787) / 100000000000000))
    (L1 := ((-6211534003609) / 25000000000000))
    (U2 := ((-2041099689127) / 50000000000000))
    (L2 := ((-2480529353297) / 50000000000000))
    (NL := (3209952470967 / 1562500000000))
    (NU := (3230009129033 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_005 {s : ℝ} (hs1 : (11 / 50) ≤ s) (hs2 : s ≤ (6 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (23 / 100) ≤ ((-29393519395589) / 20000000000000) :=
    logU (w := (23 / 100)) (c := (46 / 25))
      (q := (60976557190037 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-29393519395589) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-146967601448569) / 100000000000000) ≤ Real.log (23 / 100) :=
    logL (w := (23 / 100)) (c := (46 / 25))
      (q := (7622069089927 / 12500000000000)) (k := 3) (J := 6)
      (R := ((-146967601448569) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-26136476471669) / 100000000000000) ≤ Real.log (1 - (23 / 100)) :=
    logL (w := (77 / 100)) (c := (77 / 50))
      (q := (21589120792163 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-26136476471669) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (23 / 100) ^ 2) ≤ ((-5435059420407) / 100000000000000) :=
    logU (w := (9471 / 10000)) (c := (9471 / 5000))
      (q := (63879658635587 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5435059420407) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (11 / 50)) ≤ ((-776441747799) / 3125000000000) :=
    logU (w := (39 / 50)) (c := (39 / 25))
      (q := (22234291063213 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-776441747799) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-1715230288099) / 6250000000000) ≤ Real.log (1 - (6 / 25)) :=
    logL (w := (19 / 25)) (c := (38 / 25))
      (q := (41871033446411 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1715230288099) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (11 / 50) ^ 2) ≤ ((-2480524997307) / 50000000000000) :=
    logU (w := (2379 / 2500)) (c := (2379 / 1250))
      (q := (3217683403069 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-2480524997307) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-5932553779153) / 100000000000000) ≤ Real.log (1 - (6 / 25) ^ 2) :=
    logL (w := (589 / 625)) (c := (1178 / 625))
      (q := (31691082138421 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-5932553779153) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (11 / 50) ≤ x → x ≤ (6 / 25) →
      (321408590403 / 156250000000) ≤ Npoly x ∧
      Npoly x ≤ (807048472159 / 390625000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (11 / 50)) (w := (1 / 50))
      (r1 := (589489597 / 6250000000))
      (r2 := (394702227 / 62500000)) (r3 := (15730443 / 1250000))
      (r4 := (439587 / 50000))
      (R := (7053992303 / 1562500000000))
      (NL := (321408590403 / 156250000000)) (NU := (807048472159 / 390625000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (11 / 50)) (b := (6 / 25)) (m := (23 / 100))
    (hh := (1 / 100)) (K := (361350184070921 / 100000000000000))
    (bnd := (1010271235120283 / 10000000000000000))
    (Lu := ((-29393519395589) / 20000000000000))
    (Ll := ((-146967601448569) / 100000000000000))
    (Ml := ((-26136476471669) / 100000000000000))
    (Nu := ((-5435059420407) / 100000000000000))
    (U1 := ((-776441747799) / 3125000000000))
    (L1 := ((-1715230288099) / 6250000000000))
    (U2 := ((-2480524997307) / 50000000000000))
    (L2 := ((-5932553779153) / 100000000000000))
    (NL := (321408590403 / 156250000000))
    (NU := (807048472159 / 390625000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_006 {s : ℝ} (hs1 : (6 / 25) ≤ s) (hs2 : s ≤ (13 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (1 / 4) ≤ ((-34657359027997) / 25000000000000) :=
    logU (w := (1 / 4)) (c := 1)
      (q := 0) (k := 2) (J := 6)
      (R := ((-34657359027997) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-13862943611199) / 10000000000000) ≤ Real.log (1 / 4) :=
    logL (w := (1 / 4)) (c := 1)
      (q := 0) (k := 2) (J := 6)
      (R := ((-13862943611199) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-28768207271363) / 100000000000000) ≤ Real.log (1 - (1 / 4)) :=
    logL (w := (3 / 4)) (c := (3 / 2))
      (q := (5068313848079 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-28768207271363) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1 / 4) ^ 2) ≤ ((-6453852070427) / 100000000000000) :=
    logU (w := (15 / 16)) (c := (15 / 8))
      (q := (62860865985567 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-6453852070427) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (6 / 25)) ≤ ((-27443684570059) / 100000000000000) :=
    logU (w := (19 / 25)) (c := (38 / 25))
      (q := (8374206697187 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-27443684570059) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-3763813661931) / 12500000000000) ≤ Real.log (1 - (13 / 50)) :=
    logL (w := (37 / 50)) (c := (37 / 25))
      (q := (39204208760547 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-3763813661931) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (6 / 25) ^ 2) ≤ ((-1186509311937) / 20000000000000) :=
    logU (w := (589 / 625)) (c := (1178 / 625))
      (q := (63382171496309 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1186509311937) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-6999342995653) / 100000000000000) ≤ Real.log (1 - (13 / 50) ^ 2) :=
    logL (w := (2331 / 2500)) (c := (2331 / 1250))
      (q := (31157687530171 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-6999342995653) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (6 / 25) ≤ x → x ≤ (13 / 50) →
      (3200383351213 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (3228417753299 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (6 / 25)) (w := (1 / 50))
      (r1 := (129728407 / 390625000))
      (r2 := (43601247 / 7812500)) (r3 := (1858869 / 156250))
      (r4 := (26244 / 3125))
      (R := (14017201043 / 1562500000000))
      (NL := (3200383351213 / 1562500000000)) (NU := (3228417753299 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (6 / 25)) (b := (13 / 50)) (m := (1 / 4))
    (hh := (1 / 100)) (K := (310977446556411 / 100000000000000))
    (bnd := (111864161421731 / 1250000000000000))
    (Lu := ((-34657359027997) / 25000000000000))
    (Ll := ((-13862943611199) / 10000000000000))
    (Ml := ((-28768207271363) / 100000000000000))
    (Nu := ((-6453852070427) / 100000000000000))
    (U1 := ((-27443684570059) / 100000000000000))
    (L1 := ((-3763813661931) / 12500000000000))
    (U2 := ((-1186509311937) / 20000000000000))
    (L2 := ((-6999342995653) / 100000000000000))
    (NL := (3200383351213 / 1562500000000))
    (NU := (3228417753299 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_007 {s : ℝ} (hs1 : (13 / 50) ≤ s) (hs2 : s ≤ (7 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (27 / 100) ≤ ((-1047466655987) / 800000000000) :=
    logU (w := (27 / 100)) (c := (27 / 25))
      (q := (7696104113613 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-1047466655987) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-65466665999189) / 50000000000000) ≤ Real.log (27 / 100) :=
    logL (w := (27 / 100)) (c := (27 / 25))
      (q := (1924026028403 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-65466665999189) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-31471074494841) / 100000000000000) ≤ Real.log (1 - (27 / 100)) :=
    logL (w := (73 / 100)) (c := (73 / 50))
      (q := (18921821780577 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-31471074494841) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (27 / 100) ^ 2) ≤ ((-3784692201719) / 50000000000000) :=
    logU (w := (9271 / 10000)) (c := (9271 / 5000))
      (q := (15436333413139 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-3784692201719) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (13 / 50)) ≤ ((-30110509278347) / 100000000000000) :=
    logU (w := (37 / 50)) (c := (37 / 25))
      (q := (39204208777647 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-30110509278347) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-3285040670397) / 10000000000000) ≤ Real.log (1 - (7 / 25)) :=
    logL (w := (18 / 25)) (c := (36 / 25))
      (q := (1458572454081 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-3285040670397) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (13 / 50) ^ 2) ≤ ((-874917142979) / 12500000000000) :=
    logU (w := (2331 / 2500)) (c := (2331 / 1250))
      (q := (31157690456081 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-874917142979) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-8164403506207) / 100000000000000) ≤ Real.log (1 - (7 / 25) ^ 2) :=
    logL (w := (576 / 625)) (c := (1152 / 625))
      (q := (15287578637447 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-8164403506207) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (13 / 50) ≤ x → x ≤ (7 / 25) →
      (1590283632943 / 781250000000) ≤ Npoly x ∧
      Npoly x ≤ (402599294169 / 195312500000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (13 / 50)) (w := (1 / 50))
      (r1 := (3383328637 / 6250000000))
      (r2 := (305437149 / 62500000)) (r3 := (14050827 / 1250000))
      (r4 := (400221 / 50000))
      (R := (20113543733 / 1562500000000))
      (NL := (1590283632943 / 781250000000)) (NU := (402599294169 / 195312500000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (13 / 50)) (b := (7 / 25)) (m := (27 / 100))
    (hh := (1 / 100)) (K := (271098479458961 / 100000000000000))
    (bnd := (98851638846127 / 1250000000000000))
    (Lu := ((-1047466655987) / 800000000000))
    (Ll := ((-65466665999189) / 50000000000000))
    (Ml := ((-31471074494841) / 100000000000000))
    (Nu := ((-3784692201719) / 50000000000000))
    (U1 := ((-30110509278347) / 100000000000000))
    (L1 := ((-3285040670397) / 10000000000000))
    (U2 := ((-874917142979) / 12500000000000))
    (L2 := ((-8164403506207) / 100000000000000))
    (NL := (1590283632943 / 781250000000))
    (NU := (402599294169 / 195312500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_008 {s : ℝ} (hs1 : (7 / 25) ≤ s) (hs2 : s ≤ (3 / 10)) :
    0 < Dfun s := by
  have hLu : Real.log (29 / 100) ≤ ((-773671472501) / 625000000000) :=
    logU (w := (29 / 100)) (c := (29 / 25))
      (q := (3710500127957 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-773671472501) / 625000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-123787435600163) / 100000000000000) ≤ Real.log (29 / 100) :=
    logL (w := (29 / 100)) (c := (29 / 25))
      (q := (14842000511827 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-123787435600163) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-17124515449391) / 50000000000000) ≤ Real.log (1 - (29 / 100)) :=
    logL (w := (71 / 100)) (c := (71 / 50))
      (q := (35065687157213 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-17124515449391) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (29 / 100) ^ 2) ≤ ((-1098101129023) / 12500000000000) :=
    logU (w := (9159 / 10000)) (c := (9159 / 5000))
      (q := (6052990902381 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-1098101129023) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (7 / 25)) ≤ ((-32850406697187) / 100000000000000) :=
    logU (w := (18 / 25)) (c := (36 / 25))
      (q := (36464311358807 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-32850406697187) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-35667494396293) / 100000000000000) ≤ Real.log (1 - (3 / 10)) :=
    logL (w := (7 / 10)) (c := (7 / 5))
      (q := (16823611829851 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-35667494396293) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (7 / 25) ^ 2) ≤ ((-2041099718733) / 25000000000000) :=
    logU (w := (576 / 625)) (c := (1152 / 625))
      (q := (30575159590531 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2041099718733) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-943107149689) / 10000000000000) ≤ Real.log (1 - (3 / 10) ^ 2) :=
    logL (w := (91 / 100)) (c := (91 / 50))
      (q := (11976729311821 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-943107149689) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (7 / 25) ≤ x → x ≤ (3 / 10) →
      (3155457274899 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (641247873737 / 312500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (7 / 25)) (w := (1 / 50))
      (r1 := (70661773 / 97656250))
      (r2 := (16529103 / 3906250)) (r3 := (3317517 / 312500))
      (r4 := (190269 / 25000))
      (R := (25391046893 / 1562500000000))
      (NL := (3155457274899 / 1562500000000)) (NU := (641247873737 / 312500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (7 / 25)) (b := (3 / 10)) (m := (29 / 100))
    (hh := (1 / 100)) (K := (373279809691 / 156250000000))
    (bnd := (696578748922549 / 10000000000000000))
    (Lu := ((-773671472501) / 625000000000))
    (Ll := ((-123787435600163) / 100000000000000))
    (Ml := ((-17124515449391) / 50000000000000))
    (Nu := ((-1098101129023) / 12500000000000))
    (U1 := ((-32850406697187) / 100000000000000))
    (L1 := ((-35667494396293) / 100000000000000))
    (U2 := ((-2041099718733) / 25000000000000))
    (L2 := ((-943107149689) / 10000000000000))
    (NL := (3155457274899 / 1562500000000))
    (NU := (641247873737 / 312500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_009 {s : ℝ} (hs1 : (3 / 10) ≤ s) (hs2 : s ≤ (8 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (31 / 100) ≤ ((-117118298150293) / 100000000000000) :=
    logU (w := (31 / 100)) (c := (31 / 25))
      (q := (4302227592339 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-117118298150293) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3659946817197) / 3125000000000) ≤ Real.log (31 / 100) :=
    logL (w := (31 / 100)) (c := (31 / 25))
      (q := (10755568980843 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-3659946817197) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-7421273628093) / 20000000000000) ≤ Real.log (1 - (31 / 100)) :=
    logL (w := (69 / 100)) (c := (69 / 50))
      (q := (3220834991553 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-7421273628093) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (31 / 100) ^ 2) ≤ ((-2525913599873) / 25000000000000) :=
    logU (w := (9039 / 10000)) (c := (9039 / 5000))
      (q := (29605531828251 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2525913599873) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (3 / 10)) ≤ ((-8916873598467) / 25000000000000) :=
    logU (w := (7 / 10)) (c := (7 / 5))
      (q := (16823611831063 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-8916873598467) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-38566248081961) / 100000000000000) ≤ Real.log (1 - (8 / 25)) :=
    logL (w := (17 / 25)) (c := (34 / 25))
      (q := (15374234987017 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-38566248081961) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (3 / 10) ^ 2) ≤ ((-9431067925597) / 100000000000000) :=
    logU (w := (91 / 100)) (c := (91 / 50))
      (q := (59883650130397 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-9431067925597) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-2160615416529) / 20000000000000) ≤ Real.log (1 - (8 / 25) ^ 2) :=
    logL (w := (561 / 625)) (c := (1122 / 625))
      (q := (1170232819467 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-2160615416529) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (3 / 10) ≤ x → x ≤ (8 / 25) →
      (1562913670271 / 781250000000) ≤ Npoly x ∧
      Npoly x ≤ (796404522677 / 390625000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (3 / 10)) (w := (1 / 50))
      (r1 := (8803357 / 10000000))
      (r2 := (1806219 / 500000)) (r3 := (501147 / 50000))
      (r4 := (72171 / 10000))
      (R := (29895375083 / 1562500000000))
      (NL := (1562913670271 / 781250000000)) (NU := (796404522677 / 390625000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (3 / 10)) (b := (8 / 25)) (m := (31 / 100))
    (hh := (1 / 100)) (K := (6639208793723 / 3125000000000))
    (bnd := (611118762085927 / 10000000000000000))
    (Lu := ((-117118298150293) / 100000000000000))
    (Ll := ((-3659946817197) / 3125000000000))
    (Ml := ((-7421273628093) / 20000000000000))
    (Nu := ((-2525913599873) / 25000000000000))
    (U1 := ((-8916873598467) / 25000000000000))
    (L1 := ((-38566248081961) / 100000000000000))
    (U2 := ((-9431067925597) / 100000000000000))
    (L2 := ((-2160615416529) / 20000000000000))
    (NL := (1562913670271 / 781250000000))
    (NU := (796404522677 / 390625000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_010 {s : ℝ} (hs1 : (8 / 25) ≤ s) (hs2 : s ≤ (17 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (33 / 100) ≤ ((-110866262452159) / 100000000000000) :=
    logU (w := (33 / 100)) (c := (33 / 25))
      (q := (27763173659829 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-110866262452159) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-110866262452367) / 100000000000000) ≤ Real.log (33 / 100) :=
    logL (w := (33 / 100)) (c := (33 / 25))
      (q := (27763173659623 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-110866262452367) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-40047756660117) / 100000000000000) ≤ Real.log (1 - (33 / 100)) :=
    logL (w := (67 / 100)) (c := (67 / 50))
      (q := (14633480697939 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-40047756660117) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (33 / 100) ^ 2) ≤ ((-1441232802937) / 12500000000000) :=
    logU (w := (8911 / 10000)) (c := (8911 / 5000))
      (q := (28892427816249 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1441232802937) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (8 / 25)) ≤ ((-9641562020299) / 25000000000000) :=
    logU (w := (17 / 25)) (c := (34 / 25))
      (q := (15374234987399 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-9641562020299) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-10387886099093) / 25000000000000) ≤ Real.log (1 - (17 / 50)) :=
    logL (w := (33 / 50)) (c := (33 / 25))
      (q := (27763173659623 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-10387886099093) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (8 / 25) ^ 2) ≤ ((-2700768601493) / 25000000000000) :=
    logU (w := (561 / 625)) (c := (1122 / 625))
      (q := (29255821825011 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2700768601493) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-307114623337) / 2500000000000) ≤ Real.log (1 - (17 / 50) ^ 2) :=
    logL (w := (2211 / 2500)) (c := (2211 / 1250))
      (q := (11406026624503 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-307114623337) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (8 / 25) ≤ x → x ≤ (17 / 50) →
      (618481624501 / 312500000000) ≤ Npoly x ∧
      Npoly x ≤ (3159747784311 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (8 / 25)) (w := (1 / 50))
      (r1 := (395716207 / 390625000))
      (r2 := (23656779 / 7812500)) (r3 := (1478331 / 156250))
      (r4 := (85293 / 12500))
      (R := (33669830903 / 1562500000000))
      (NL := (618481624501 / 312500000000)) (NU := (3159747784311 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (8 / 25)) (b := (17 / 50)) (m := (33 / 100))
    (hh := (1 / 100)) (K := (19041282925461 / 10000000000000))
    (bnd := (26678084540641 / 500000000000000))
    (Lu := ((-110866262452159) / 100000000000000))
    (Ll := ((-110866262452367) / 100000000000000))
    (Ml := ((-40047756660117) / 100000000000000))
    (Nu := ((-1441232802937) / 12500000000000))
    (U1 := ((-9641562020299) / 25000000000000))
    (L1 := ((-10387886099093) / 25000000000000))
    (U2 := ((-2700768601493) / 25000000000000))
    (L2 := ((-307114623337) / 2500000000000))
    (NL := (618481624501 / 312500000000))
    (NU := (3159747784311 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_011 {s : ℝ} (hs1 : (17 / 50) ≤ s) (hs2 : s ≤ (9 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (7 / 20) ≤ ((-52491106224931) / 50000000000000) :=
    logU (w := (7 / 20)) (c := (7 / 5))
      (q := (16823611831063 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-52491106224931) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-1640347069567) / 1562500000000) ≤ Real.log (7 / 20) :=
    logL (w := (7 / 20)) (c := (7 / 5))
      (q := (16823611829851 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-1640347069567) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-8615658321869) / 20000000000000) ≤ Real.log (1 - (7 / 20)) :=
    logL (w := (13 / 20)) (c := (13 / 10))
      (q := (524728528933 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-8615658321869) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (7 / 20) ^ 2) ≤ ((-40836976111) / 312500000000) :=
    logU (w := (351 / 400)) (c := (351 / 200))
      (q := (28123442850237 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-40836976111) / 312500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (17 / 50)) ≤ ((-8310308879233) / 20000000000000) :=
    logU (w := (33 / 50)) (c := (33 / 25))
      (q := (27763173659829 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8310308879233) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-5578588782861) / 12500000000000) ≤ Real.log (1 - (9 / 25)) :=
    logL (w := (16 / 25)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5578588782861) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (17 / 50) ^ 2) ≤ ((-12284582989263) / 100000000000000) :=
    logU (w := (2211 / 2500)) (c := (2211 / 1250))
      (q := (57030135066731 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-12284582989263) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1388024164487) / 10000000000000) ≤ Real.log (1 - (9 / 25) ^ 2) :=
    logL (w := (544 / 625)) (c := (1088 / 625))
      (q := (443475811289 / 800000000000)) (k := 1) (J := 6)
      (R := ((-1388024164487) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (17 / 50) ≤ x → x ≤ (9 / 25) →
      (1527944669919 / 781250000000) ≤ Npoly x ∧
      Npoly x ≤ (97793751557 / 48828125000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (17 / 50)) (w := (1 / 50))
      (r1 := (7018861357 / 6250000000))
      (r2 := (154778121 / 62500000)) (r3 := (11163987 / 1250000))
      (r4 := (321489 / 50000))
      (R := (36755354993 / 1562500000000))
      (NL := (1527944669919 / 781250000000)) (NU := (97793751557 / 48828125000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (17 / 50)) (b := (9 / 25)) (m := (7 / 20))
    (hh := (1 / 100)) (K := (171800693348219 / 100000000000000))
    (bnd := (463199176291441 / 10000000000000000))
    (Lu := ((-52491106224931) / 50000000000000))
    (Ll := ((-1640347069567) / 1562500000000))
    (Ml := ((-8615658321869) / 20000000000000))
    (Nu := ((-40836976111) / 312500000000))
    (U1 := ((-8310308879233) / 20000000000000))
    (L1 := ((-5578588782861) / 12500000000000))
    (U2 := ((-12284582989263) / 100000000000000))
    (L2 := ((-1388024164487) / 10000000000000))
    (NL := (1527944669919 / 781250000000))
    (NU := (97793751557 / 48828125000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_012 {s : ℝ} (hs1 : (9 / 25) ≤ s) (hs2 : s ≤ (19 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (37 / 100) ≤ ((-99425227334341) / 100000000000000) :=
    logU (w := (37 / 100)) (c := (37 / 25))
      (q := (39204208777647 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-99425227334341) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-99425227351443) / 100000000000000) ≤ Real.log (37 / 100) :=
    logL (w := (37 / 100)) (c := (37 / 25))
      (q := (39204208760547 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-99425227351443) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-11550886489919) / 25000000000000) ≤ Real.log (1 - (37 / 100)) :=
    logL (w := (63 / 100)) (c := (63 / 50))
      (q := (23111172096319 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-11550886489919) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (37 / 100) ^ 2) ≤ ((-7361235985009) / 50000000000000) :=
    logU (w := (8631 / 10000)) (c := (8631 / 5000))
      (q := (6824030760747 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-7361235985009) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (9 / 25)) ≤ ((-44628710262841) / 100000000000000) :=
    logU (w := (16 / 25)) (c := (32 / 25))
      (q := (24686007793153 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-44628710262841) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-47803580094309) / 100000000000000) ≤ Real.log (1 - (19 / 50)) :=
    logL (w := (31 / 50)) (c := (31 / 25))
      (q := (10755568980843 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-47803580094309) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (9 / 25) ^ 2) ≤ ((-13880240281009) / 100000000000000) :=
    logU (w := (544 / 625)) (c := (1088 / 625))
      (q := (11086895554997 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-13880240281009) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-15595231093111) / 100000000000000) ≤ Real.log (1 - (19 / 50) ^ 2) :=
    logL (w := (2139 / 2500)) (c := (2139 / 1250))
      (q := (13429871740721 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-15595231093111) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (9 / 25) ≤ x → x ≤ (19 / 50) →
      (3016922132911 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (3095303184977 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (9 / 25)) (w := (1 / 50))
      (r1 := (118316503 / 97656250))
      (r2 := (3819717 / 1953125)) (r3 := (2635173 / 312500))
      (r4 := (150903 / 25000))
      (R := (39190526033 / 1562500000000))
      (NL := (3016922132911 / 1562500000000)) (NU := (3095303184977 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (9 / 25)) (b := (19 / 50)) (m := (37 / 100))
    (hh := (1 / 100)) (K := (2436004620803 / 1562500000000))
    (bnd := (99861316787187 / 2500000000000000))
    (Lu := ((-99425227334341) / 100000000000000))
    (Ll := ((-99425227351443) / 100000000000000))
    (Ml := ((-11550886489919) / 25000000000000))
    (Nu := ((-7361235985009) / 50000000000000))
    (U1 := ((-44628710262841) / 100000000000000))
    (L1 := ((-47803580094309) / 100000000000000))
    (U2 := ((-13880240281009) / 100000000000000))
    (L2 := ((-15595231093111) / 100000000000000))
    (NL := (3016922132911 / 1562500000000))
    (NU := (3095303184977 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_013 {s : ℝ} (hs1 : (19 / 50) ≤ s) (hs2 : s ≤ (2 / 5)) :
    0 < Dfun s := by
  have hLu : Real.log (39 / 100) ≤ ((-47080426992781) / 50000000000000) :=
    logU (w := (39 / 100)) (c := (39 / 25))
      (q := (22234291063213 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-47080426992781) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-94160854070431) / 100000000000000) ≤ Real.log (39 / 100) :=
    logL (w := (39 / 100)) (c := (39 / 25))
      (q := (44468582041559 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-94160854070431) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-24714816090741) / 50000000000000) ≤ Real.log (1 - (39 / 100)) :=
    logL (w := (61 / 100)) (c := (61 / 50))
      (q := (19885085874513 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-24714816090741) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (39 / 100) ^ 2) ≤ ((-2062407182967) / 12500000000000) :=
    logU (w := (8479 / 10000)) (c := (8479 / 5000))
      (q := (26407730296129 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2062407182967) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (19 / 50)) ≤ ((-47803580094299) / 100000000000000) :=
    logU (w := (31 / 50)) (c := (31 / 25))
      (q := (4302227592339 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-47803580094299) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-51082562376601) / 100000000000000) ≤ Real.log (1 - (2 / 5)) :=
    logL (w := (3 / 5)) (c := (6 / 5))
      (q := (9116077839697 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-51082562376601) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (19 / 50) ^ 2) ≤ ((-15595230172931) / 100000000000000) :=
    logU (w := (2139 / 2500)) (c := (2139 / 1250))
      (q := (53719487883063 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-15595230172931) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-697413572237) / 4000000000000) ≤ Real.log (1 - (2 / 5) ^ 2) :=
    logL (w := (21 / 25)) (c := (42 / 25))
      (q := (5187937875007 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-697413572237) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (19 / 50) ≤ x → x ≤ (2 / 5) →
      (1488060712687 / 781250000000) ≤ Npoly x ∧
      Npoly x ≤ (152907227343 / 78125000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (19 / 50)) (w := (1 / 50))
      (r1 := (7999123357 / 6250000000))
      (r2 := (91494603 / 62500000)) (r3 := (9956763 / 1250000))
      (r4 := (282123 / 50000))
      (R := (41011560743 / 1562500000000))
      (NL := (1488060712687 / 781250000000)) (NU := (152907227343 / 78125000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (19 / 50)) (b := (2 / 5)) (m := (39 / 100))
    (hh := (1 / 100)) (K := (142190399391269 / 100000000000000))
    (bnd := (170903382231547 / 5000000000000000))
    (Lu := ((-47080426992781) / 50000000000000))
    (Ll := ((-94160854070431) / 100000000000000))
    (Ml := ((-24714816090741) / 50000000000000))
    (Nu := ((-2062407182967) / 12500000000000))
    (U1 := ((-47803580094299) / 100000000000000))
    (L1 := ((-51082562376601) / 100000000000000))
    (U2 := ((-15595230172931) / 100000000000000))
    (L2 := ((-697413572237) / 4000000000000))
    (NL := (1488060712687 / 781250000000))
    (NU := (152907227343 / 78125000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_014 {s : ℝ} (hs1 : (2 / 5) ≤ s) (hs2 : s ≤ (21 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (41 / 100) ≤ ((-89159811927037) / 100000000000000) :=
    logU (w := (41 / 100)) (c := (41 / 25))
      (q := (49469624184951 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-89159811927037) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-2228995306339) / 2500000000000) ≤ Real.log (41 / 100) :=
    logL (w := (41 / 100)) (c := (41 / 25))
      (q := (4946962385843 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-2228995306339) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-26381637104119) / 50000000000000) ≤ Real.log (1 - (41 / 100)) :=
    logL (w := (59 / 100)) (c := (59 / 50))
      (q := (16551443847757 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-26381637104119) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (41 / 100) ^ 2) ≤ ((-18404303767191) / 100000000000000) :=
    logU (w := (8319 / 10000)) (c := (8319 / 5000))
      (q := (50910414288803 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-18404303767191) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (2 / 5)) ≤ ((-25541281188299) / 50000000000000) :=
    logU (w := (3 / 5)) (c := (6 / 5))
      (q := (4558038919849 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-25541281188299) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-6809089693021) / 12500000000000) ≤ Real.log (1 - (21 / 50)) :=
    logL (w := (29 / 50)) (c := (29 / 25))
      (q := (14842000511827 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-6809089693021) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (2 / 5) ^ 2) ≤ ((-8717669355897) / 50000000000000) :=
    logU (w := (21 / 25)) (c := (42 / 25))
      (q := (259396896721 / 500000000000)) (k := 1) (J := 6)
      (R := ((-8717669355897) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-19407030746213) / 100000000000000) ≤ Real.log (1 - (21 / 50) ^ 2) :=
    logL (w := (2059 / 2500)) (c := (2059 / 1250))
      (q := (24953843654891 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-19407030746213) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (2 / 5) ≤ x → x ≤ (21 / 50) →
      (2934068286117 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (3018572913883 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (2 / 5)) (w := (1 / 50))
      (r1 := (830647 / 625000))
      (r2 := (62451 / 62500)) (r3 := (47061 / 6250))
      (r4 := (6561 / 1250))
      (R := (42252313883 / 1562500000000))
      (NL := (2934068286117 / 1562500000000)) (NU := (3018572913883 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (2 / 5)) (b := (21 / 50)) (m := (41 / 100))
    (hh := (1 / 100)) (K := (65127323507127 / 50000000000000))
    (bnd := (463778013241 / 16000000000000))
    (Lu := ((-89159811927037) / 100000000000000))
    (Ll := ((-2228995306339) / 2500000000000))
    (Ml := ((-26381637104119) / 50000000000000))
    (Nu := ((-18404303767191) / 100000000000000))
    (U1 := ((-25541281188299) / 50000000000000))
    (L1 := ((-6809089693021) / 12500000000000))
    (U2 := ((-8717669355897) / 50000000000000))
    (L2 := ((-19407030746213) / 100000000000000))
    (NL := (2934068286117 / 1562500000000))
    (NU := (3018572913883 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_015 {s : ℝ} (hs1 : (21 / 50) ≤ s) (hs2 : s ≤ (11 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (43 / 100) ≤ ((-16879401404867) / 20000000000000) :=
    logU (w := (43 / 100)) (c := (43 / 25))
      (q := (54232429087653 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-16879401404867) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-84397008060893) / 100000000000000) ≤ Real.log (43 / 100) :=
    logL (w := (43 / 100)) (c := (43 / 25))
      (q := (54232428051097 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-84397008060893) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-11242378363071) / 20000000000000) ≤ Real.log (1 - (43 / 100)) :=
    logL (w := (57 / 100)) (c := (57 / 50))
      (q := (20473166001 / 156250000000)) (k := 1) (J := 6)
      (R := ((-11242378363071) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (43 / 100) ^ 2) ≤ ((-20444447387051) / 100000000000000) :=
    logU (w := (8151 / 10000)) (c := (8151 / 5000))
      (q := (48870270668943 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-20444447387051) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (21 / 50)) ≤ ((-27236358772083) / 50000000000000) :=
    logU (w := (29 / 50)) (c := (29 / 25))
      (q := (3710500127957 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-27236358772083) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-11596369905059) / 20000000000000) ≤ Real.log (1 - (11 / 25)) :=
    logL (w := (14 / 25)) (c := (28 / 25))
      (q := (113328685307 / 1000000000000)) (k := 1) (J := 6)
      (R := ((-11596369905059) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (21 / 50) ^ 2) ≤ ((-776281215253) / 4000000000000) :=
    logU (w := (2059 / 2500)) (c := (2059 / 1250))
      (q := (49907687674669 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-776281215253) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-21517538377263) / 100000000000000) ≤ Real.log (1 - (11 / 25) ^ 2) :=
    logL (w := (504 / 625)) (c := (1008 / 625))
      (q := (11949294919683 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-21517538377263) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (21 / 50) ≤ x → x ≤ (11 / 25) →
      (289131229123 / 156250000000) ≤ Npoly x ∧
      Npoly x ≤ (372150105967 / 195312500000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (21 / 50)) (w := (1 / 50))
      (r1 := (8500830877 / 6250000000))
      (r2 := (34982037 / 62500000)) (r3 := (8907003 / 1250000))
      (r4 := (242757 / 50000))
      (R := (42944278253 / 1562500000000))
      (NL := (289131229123 / 156250000000)) (NU := (372150105967 / 195312500000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (21 / 50)) (b := (11 / 25)) (m := (43 / 100))
    (hh := (1 / 100)) (K := (467915313227 / 390625000000))
    (bnd := (121620312661581 / 5000000000000000))
    (Lu := ((-16879401404867) / 20000000000000))
    (Ll := ((-84397008060893) / 100000000000000))
    (Ml := ((-11242378363071) / 20000000000000))
    (Nu := ((-20444447387051) / 100000000000000))
    (U1 := ((-27236358772083) / 50000000000000))
    (L1 := ((-11596369905059) / 20000000000000))
    (U2 := ((-776281215253) / 4000000000000))
    (L2 := ((-21517538377263) / 100000000000000))
    (NL := (289131229123 / 156250000000))
    (NU := (372150105967 / 195312500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_016 {s : ℝ} (hs1 : (11 / 25) ≤ s) (hs2 : s ≤ (23 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (9 / 20) ≤ ((-7985076960533) / 10000000000000) :=
    logU (w := (9 / 20)) (c := (9 / 5))
      (q := (29389333253329 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-7985076960533) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-79850772438131) / 100000000000000) ≤ Real.log (9 / 20) :=
    logL (w := (9 / 20)) (c := (9 / 5))
      (q := (58778663673859 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-79850772438131) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-59783700075563) / 100000000000000) ≤ Real.log (1 - (9 / 20)) :=
    logL (w := (11 / 20)) (c := (11 / 10))
      (q := (595688623777 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-59783700075563) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (9 / 20) ^ 2) ≤ ((-22627344431739) / 100000000000000) :=
    logU (w := (319 / 400)) (c := (319 / 200))
      (q := (9337474724851 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-22627344431739) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (11 / 25)) ≤ ((-57981849525293) / 100000000000000) :=
    logU (w := (14 / 25)) (c := (28 / 25))
      (q := (11332868530701 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-57981849525293) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-61618613942383) / 100000000000000) ≤ Real.log (1 - (23 / 50)) :=
    logL (w := (27 / 50)) (c := (27 / 25))
      (q := (1924026028403 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-61618613942383) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (11 / 25) ^ 2) ≤ ((-5379384541423) / 25000000000000) :=
    logU (w := (504 / 625)) (c := (1008 / 625))
      (q := (23898589945151 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-5379384541423) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-23774970484701) / 100000000000000) ≤ Real.log (1 - (23 / 50) ^ 2) :=
    logL (w := (1971 / 2500)) (c := (1971 / 1250))
      (q := (22769873785647 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-23774970484701) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (11 / 25) ≤ x → x ≤ (23 / 50) →
      (2848373885963 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (2934607055349 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (11 / 25)) (w := (1 / 50))
      (r1 := (134191693 / 97656250))
      (r2 := (560601 / 3906250)) (r3 := (2110293 / 312500))
      (r4 := (111537 / 25000))
      (R := (43116584693 / 1562500000000))
      (NL := (2848373885963 / 1562500000000)) (NU := (2934607055349 / 1562500000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (11 / 25)) (b := (23 / 50)) (m := (9 / 20))
    (hh := (1 / 100)) (K := (11054389714469 / 10000000000000))
    (bnd := (201618467821661 / 10000000000000000))
    (Lu := ((-7985076960533) / 10000000000000))
    (Ll := ((-79850772438131) / 100000000000000))
    (Ml := ((-59783700075563) / 100000000000000))
    (Nu := ((-22627344431739) / 100000000000000))
    (U1 := ((-57981849525293) / 100000000000000))
    (L1 := ((-61618613942383) / 100000000000000))
    (U2 := ((-5379384541423) / 25000000000000))
    (L2 := ((-23774970484701) / 100000000000000))
    (NL := (2848373885963 / 1562500000000))
    (NU := (2934607055349 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_017 {s : ℝ} (hs1 : (23 / 50) ≤ s) (hs2 : s ≤ (12 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (47 / 100) ≤ ((-15100451676351) / 20000000000000) :=
    logU (w := (47 / 100)) (c := (47 / 25))
      (q := (63127177730233 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-15100451676351) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-9437783156271) / 12500000000000) ≤ Real.log (47 / 100) :=
    logL (w := (47 / 100)) (c := (47 / 25))
      (q := (31563585430911 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-9437783156271) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-31743913621799) / 50000000000000) ≤ Real.log (1 - (47 / 100)) :=
    logL (w := (53 / 100)) (c := (53 / 50))
      (q := (5826890812397 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-31743913621799) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (47 / 100) ^ 2) ≤ ((-24961587164261) / 100000000000000) :=
    logU (w := (7791 / 10000)) (c := (7791 / 5000))
      (q := (44353130891733 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-24961587164261) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (23 / 50)) ≤ ((-61618613942381) / 100000000000000) :=
    logU (w := (27 / 50)) (c := (27 / 25))
      (q := (7696104113613 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-61618613942381) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-65392646740667) / 100000000000000) ≤ Real.log (1 - (12 / 25)) :=
    logL (w := (13 / 25)) (c := (26 / 25))
      (q := (30641182151 / 781250000000)) (k := 1) (J := 6)
      (R := ((-65392646740667) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (23 / 50) ^ 2) ≤ ((-11887485184979) / 50000000000000) :=
    logU (w := (1971 / 2500)) (c := (1971 / 1250))
      (q := (11384936921509 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-11887485184979) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-26188438020409) / 100000000000000) ≤ Real.log (1 - (12 / 25) ^ 2) :=
    logL (w := (481 / 625)) (c := (962 / 625))
      (q := (21563140017793 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-26188438020409) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (23 / 50) ≤ x → x ≤ (12 / 25) →
      (1402716329733 / 781250000000) ≤ Npoly x ∧
      Npoly x ≤ (361456604759 / 195312500000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (23 / 50)) (w := (1 / 50))
      (r1 := (8574372397 / 6250000000))
      (r2 := (15704361 / 62500000)) (r3 := (8014707 / 1250000))
      (r4 := (203391 / 50000))
      (R := (43110089303 / 1562500000000))
      (NL := (1402716329733 / 781250000000)) (NU := (361456604759 / 195312500000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (23 / 50)) (b := (12 / 25)) (m := (47 / 100))
    (hh := (1 / 100)) (K := (51171681991907 / 50000000000000))
    (bnd := (82350218212181 / 5000000000000000))
    (Lu := ((-15100451676351) / 20000000000000))
    (Ll := ((-9437783156271) / 12500000000000))
    (Ml := ((-31743913621799) / 50000000000000))
    (Nu := ((-24961587164261) / 100000000000000))
    (U1 := ((-61618613942381) / 100000000000000))
    (L1 := ((-65392646740667) / 100000000000000))
    (U2 := ((-11887485184979) / 50000000000000))
    (L2 := ((-26188438020409) / 100000000000000))
    (NL := (1402716329733 / 781250000000))
    (NU := (361456604759 / 195312500000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_018 {s : ℝ} (hs1 : (12 / 25) ≤ s) (hs2 : s ≤ (49 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (97 / 200) ≤ ((-7236063871199) / 10000000000000) :=
    logU (w := (97 / 200)) (c := (97 / 50))
      (q := (33134398699999 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-7236063871199) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-72360651217359) / 100000000000000) ≤ Real.log (97 / 200) :=
    logL (w := (97 / 200)) (c := (97 / 50))
      (q := (66268784894631 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-72360651217359) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-66358837831841) / 100000000000000) ≤ Real.log (1 - (97 / 200)) :=
    logL (w := (103 / 200)) (c := (103 / 100))
      (q := (1477940112077 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-66358837831841) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (97 / 200) ^ 2) ≤ ((-6704340151557) / 25000000000000) :=
    logU (w := (30591 / 40000)) (c := (30591 / 20000))
      (q := (21248678724883 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-6704340151557) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (12 / 25)) ≤ ((-13078529348133) / 20000000000000) :=
    logU (w := (13 / 25)) (c := (26 / 25))
      (q := (3922071315329 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-13078529348133) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-33667227663189) / 50000000000000) ≤ Real.log (1 - (49 / 100)) :=
    logL (w := (51 / 100)) (c := (51 / 50))
      (q := (1980262729617 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-33667227663189) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (12 / 25) ^ 2) ≤ ((-6547109490721) / 25000000000000) :=
    logU (w := (481 / 625)) (c := (962 / 625))
      (q := (4312628009311 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-6547109490721) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-27456843369891) / 100000000000000) ≤ Real.log (1 - (49 / 100) ^ 2) :=
    logL (w := (7599 / 10000)) (c := (7599 / 5000))
      (q := (5232234335763 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-27456843369891) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (12 / 25) ≤ x → x ≤ (49 / 100) →
      (89108446118341 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (90469607013947 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (12 / 25)) (w := (1 / 100))
      (r1 := (529016287 / 390625000))
      (r2 := (4894749 / 7812500)) (r3 := (953451 / 156250))
      (r4 := (45927 / 12500))
      (R := (680580447803 / 50000000000000))
      (NL := (89108446118341 / 50000000000000)) (NU := (90469607013947 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (12 / 25)) (b := (49 / 100)) (m := (97 / 200))
    (hh := (1 / 200)) (K := (6979219593467 / 12500000000000))
    (bnd := (69967961416623 / 5000000000000000))
    (Lu := ((-7236063871199) / 10000000000000))
    (Ll := ((-72360651217359) / 100000000000000))
    (Ml := ((-66358837831841) / 100000000000000))
    (Nu := ((-6704340151557) / 25000000000000))
    (U1 := ((-13078529348133) / 20000000000000))
    (L1 := ((-33667227663189) / 50000000000000))
    (U2 := ((-6547109490721) / 25000000000000))
    (L2 := ((-27456843369891) / 100000000000000))
    (NL := (89108446118341 / 50000000000000))
    (NU := (90469607013947 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_019 {s : ℝ} (hs1 : (49 / 100) ≤ s) (hs2 : s ≤ (1 / 2)) :
    0 < Dfun s := by
  have hLu : Real.log (99 / 200) ≤ ((-549373058583) / 781250000000) :=
    logU (w := (99 / 200)) (c := (99 / 50))
      (q := (17077421153341 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-549373058583) / 781250000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-35159884825879) / 50000000000000) ≤ Real.log (99 / 200) :=
    logL (w := (99 / 200)) (c := (99 / 50))
      (q := (8538708307529 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-35159884825879) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-68319684970679) / 100000000000000) ≤ Real.log (1 - (99 / 200)) :=
    logL (w := (101 / 200)) (c := (101 / 100))
      (q := (248758271329 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-68319684970679) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (99 / 200) ^ 2) ≤ ((-351338303579) / 1250000000000) :=
    logU (w := (30199 / 40000)) (c := (30199 / 20000))
      (q := (20603826884837 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-351338303579) / 1250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (49 / 100)) ≤ ((-8416806915797) / 12500000000000) :=
    logU (w := (51 / 100)) (c := (51 / 50))
      (q := (990131364809 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-8416806915797) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-13862943611199) / 20000000000000) ≤ Real.log (1 - (1 / 2)) :=
    logL (w := (1 / 2)) (c := 1)
      (q := 0) (k := 1) (J := 6)
      (R := ((-13862943611199) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (49 / 100) ^ 2) ≤ ((-27456843330523) / 100000000000000) :=
    logU (w := (7599 / 10000)) (c := (7599 / 5000))
      (q := (41857874725471 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-27456843330523) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-28768207271363) / 100000000000000) ≤ Real.log (1 - (1 / 2) ^ 2) :=
    logL (w := (3 / 4)) (c := (3 / 2))
      (q := (5068313848079 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-28768207271363) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (49 / 100) ≤ x → x ≤ (1 / 2) →
      (44220508650817 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (179579251977 / 100000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (49 / 100)) (w := (1 / 100))
      (r1 := (133993501117 / 100000000000))
      (r2 := (403712667 / 500000000)) (r3 := (29795283 / 5000000))
      (r4 := (347733 / 100000))
      (R := (674304343433 / 50000000000000))
      (NL := (44220508650817 / 25000000000000)) (NU := (179579251977 / 100000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (49 / 100)) (b := (1 / 2)) (m := (99 / 200))
    (hh := (1 / 200)) (K := (10720718488877 / 20000000000000))
    (bnd := (31189706791947 / 2500000000000000))
    (Lu := ((-549373058583) / 781250000000))
    (Ll := ((-35159884825879) / 50000000000000))
    (Ml := ((-68319684970679) / 100000000000000))
    (Nu := ((-351338303579) / 1250000000000))
    (U1 := ((-8416806915797) / 12500000000000))
    (L1 := ((-13862943611199) / 20000000000000))
    (U2 := ((-27456843330523) / 100000000000000))
    (L2 := ((-28768207271363) / 100000000000000))
    (NL := (44220508650817 / 25000000000000))
    (NU := (179579251977 / 100000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_020 {s : ℝ} (hs1 : (1 / 2) ≤ s) (hs2 : s ≤ (51 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (101 / 200) ≤ ((-68319684970677) / 100000000000000) :=
    logU (w := (101 / 200)) (c := (101 / 100))
      (q := (995033085317 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-68319684970677) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-68319684970679) / 100000000000000) ≤ Real.log (101 / 200) :=
    logL (w := (101 / 200)) (c := (101 / 100))
      (q := (248758271329 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-68319684970679) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-35159884825879) / 50000000000000) ≤ Real.log (1 - (101 / 200)) :=
    logL (w := (99 / 200)) (c := (99 / 50))
      (q := (8538708307529 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-35159884825879) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (101 / 200) ^ 2) ≤ ((-29440461821203) / 100000000000000) :=
    logU (w := (29799 / 40000)) (c := (29799 / 20000))
      (q := (39874256234791 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-29440461821203) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (1 / 2)) ≤ ((-34657359027997) / 50000000000000) :=
    logU (w := (1 / 2)) (c := 1)
      (q := 0) (k := 1) (J := 6)
      (R := ((-34657359027997) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-7133500377743) / 10000000000000) ≤ Real.log (1 - (51 / 100)) :=
    logL (w := (49 / 100)) (c := (49 / 25))
      (q := (420590202091 / 625000000000)) (k := 2) (J := 6)
      (R := ((-7133500377743) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (1 / 2) ^ 2) ≤ ((-5753641449021) / 20000000000000) :=
    logU (w := (3 / 4)) (c := (3 / 2))
      (q := (40546510810889 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5753641449021) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-7531005930511) / 25000000000000) ≤ Real.log (1 - (51 / 100) ^ 2) :=
    logL (w := (7399 / 10000)) (c := (7399 / 5000))
      (q := (39190694333951 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-7531005930511) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (1 / 2) ≤ x → x ≤ (51 / 100) →
      (87783467645067 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (89115907354933 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (1 / 2)) (w := (1 / 100))
      (r1 := (105761 / 80000))
      (r2 := (19683 / 20000)) (r3 := (58239 / 10000))
      (r4 := (6561 / 2000))
      (R := (666219854933 / 50000000000000))
      (NL := (87783467645067 / 50000000000000)) (NU := (89115907354933 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (1 / 2)) (b := (51 / 100)) (m := (101 / 200))
    (hh := (1 / 200)) (K := (1286974913903 / 2500000000000))
    (bnd := (27653373206401 / 2500000000000000))
    (Lu := ((-68319684970677) / 100000000000000))
    (Ll := ((-68319684970679) / 100000000000000))
    (Ml := ((-35159884825879) / 50000000000000))
    (Nu := ((-29440461821203) / 100000000000000))
    (U1 := ((-34657359027997) / 50000000000000))
    (L1 := ((-7133500377743) / 10000000000000))
    (U2 := ((-5753641449021) / 20000000000000))
    (L2 := ((-7531005930511) / 25000000000000))
    (NL := (87783467645067 / 50000000000000))
    (NU := (89115907354933 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_021 {s : ℝ} (hs1 : (51 / 100) ≤ s) (hs2 : s ≤ (13 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (103 / 200) ≤ ((-66358837831839) / 100000000000000) :=
    logU (w := (103 / 200)) (c := (103 / 100))
      (q := (591176044831 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-66358837831839) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-66358837831841) / 100000000000000) ≤ Real.log (103 / 200) :=
    logL (w := (103 / 200)) (c := (103 / 100))
      (q := (1477940112077 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-66358837831841) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-72360651217359) / 100000000000000) ≤ Real.log (1 - (103 / 200)) :=
    logL (w := (97 / 200)) (c := (97 / 50))
      (q := (66268784894631 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-72360651217359) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (103 / 200) ^ 2) ≤ ((-15409547454149) / 50000000000000) :=
    logU (w := (29391 / 40000)) (c := (29391 / 20000))
      (q := (2405976446731 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-15409547454149) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (51 / 100)) ≤ ((-7133498867253) / 10000000000000) :=
    logU (w := (49 / 100)) (c := (49 / 25))
      (q := (33647223719729 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-7133498867253) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-73396927733031) / 100000000000000) ≤ Real.log (1 - (13 / 25)) :=
    logL (w := (12 / 25)) (c := (48 / 25))
      (q := (65232508378959 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-73396927733031) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (51 / 100) ^ 2) ≤ ((-15062011852509) / 50000000000000) :=
    logU (w := (7399 / 10000)) (c := (7399 / 5000))
      (q := (306177299617 / 781250000000)) (k := 1) (J := 6)
      (R := ((-15062011852509) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-31525884032873) / 100000000000000) ≤ Real.log (1 - (13 / 25) ^ 2) :=
    logL (w := (456 / 625)) (c := (912 / 625))
      (q := (18894417011561 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-31525884032873) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (51 / 100) ≤ x → x ≤ (13 / 25) →
      (8713752286417 / 5000000000000) ≤ Npoly x ∧
      Npoly x ≤ (11056282535587 / 6250000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (51 / 100)) (w := (1 / 100))
      (r1 := (130059525517 / 100000000000))
      (r2 := (578469033 / 500000000)) (r3 := (28483083 / 5000000))
      (r4 := (308367 / 100000))
      (R := (656368710263 / 50000000000000))
      (NL := (8713752286417 / 5000000000000)) (NU := (11056282535587 / 6250000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (51 / 100)) (b := (13 / 25)) (m := (103 / 200))
    (hh := (1 / 200)) (K := (9890764829527 / 20000000000000))
    (bnd := (97470259109541 / 10000000000000000))
    (Lu := ((-66358837831839) / 100000000000000))
    (Ll := ((-66358837831841) / 100000000000000))
    (Ml := ((-72360651217359) / 100000000000000))
    (Nu := ((-15409547454149) / 50000000000000))
    (U1 := ((-7133498867253) / 10000000000000))
    (L1 := ((-73396927733031) / 100000000000000))
    (U2 := ((-15062011852509) / 50000000000000))
    (L2 := ((-31525884032873) / 100000000000000))
    (NL := (8713752286417 / 5000000000000))
    (NU := (11056282535587 / 6250000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_022 {s : ℝ} (hs1 : (13 / 25) ≤ s) (hs2 : s ≤ (53 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (21 / 40) ≤ ((-1288714032781) / 2000000000000) :=
    logU (w := (21 / 40)) (c := (21 / 20))
      (q := (304938526059 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-1288714032781) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-16108925409763) / 25000000000000) ≤ Real.log (21 / 40) :=
    logL (w := (21 / 40)) (c := (21 / 20))
      (q := (4879016416943 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-16108925409763) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-7444405587113) / 10000000000000) ≤ Real.log (1 - (21 / 40)) :=
    logL (w := (19 / 40)) (c := (19 / 10))
      (q := (3209269012043 / 5000000000000)) (k := 2) (J := 6)
      (R := ((-7444405587113) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (21 / 40) ^ 2) ≤ ((-4030575811099) / 12500000000000) :=
    logU (w := (1159 / 1600)) (c := (1159 / 800))
      (q := (18535055783601 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-4030575811099) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (13 / 25)) ≤ ((-9174614679281) / 12500000000000) :=
    logU (w := (12 / 25)) (c := (48 / 25))
      (q := (3261625933887 / 5000000000000)) (k := 2) (J := 6)
      (R := ((-9174614679281) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-9437783156271) / 12500000000000) ≤ Real.log (1 - (53 / 100)) :=
    logL (w := (47 / 100)) (c := (47 / 25))
      (q := (31563585430911 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-9437783156271) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (13 / 25) ^ 2) ≤ ((-1261035360887) / 4000000000000) :=
    logU (w := (456 / 625)) (c := (912 / 625))
      (q := (37788834033819 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1261035360887) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-6595096978769) / 20000000000000) ≤ Real.log (1 - (53 / 100) ^ 2) :=
    logL (w := (7191 / 10000)) (c := (7191 / 5000))
      (q := (726784663243 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-6595096978769) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (13 / 25) ≤ x → x ≤ (53 / 100) →
      (86504871670433 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (87794452221279 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (13 / 25)) (w := (1 / 100))
      (r1 := (124585903 / 97656250))
      (r2 := (2589894 / 1953125)) (r3 := (1742877 / 312500))
      (r4 := (72171 / 25000))
      (R := (644790275423 / 50000000000000))
      (NL := (86504871670433 / 50000000000000)) (NU := (87794452221279 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (13 / 25)) (b := (53 / 100)) (m := (21 / 40))
    (hh := (1 / 200)) (K := (47522585069329 / 100000000000000))
    (bnd := (85299092025171 / 10000000000000000))
    (Lu := ((-1288714032781) / 2000000000000))
    (Ll := ((-16108925409763) / 25000000000000))
    (Ml := ((-7444405587113) / 10000000000000))
    (Nu := ((-4030575811099) / 12500000000000))
    (U1 := ((-9174614679281) / 12500000000000))
    (L1 := ((-9437783156271) / 12500000000000))
    (U2 := ((-1261035360887) / 4000000000000))
    (L2 := ((-6595096978769) / 20000000000000))
    (NL := (86504871670433 / 50000000000000))
    (NU := (87794452221279 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_023 {s : ℝ} (hs1 : (53 / 100) ≤ s) (hs2 : s ≤ (27 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (107 / 200) ≤ ((-15637213302153) / 25000000000000) :=
    logU (w := (107 / 200)) (c := (107 / 100))
      (q := (3382932423691 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-15637213302153) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-31274426604307) / 50000000000000) ≤ Real.log (107 / 200) :=
    logL (w := (107 / 200)) (c := (107 / 100))
      (q := (6765864847381 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-31274426604307) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-76571792862481) / 100000000000000) ≤ Real.log (1 - (107 / 200)) :=
    logL (w := (93 / 200)) (c := (93 / 50))
      (q := (62057643249509 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-76571792862481) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (107 / 200) ^ 2) ≤ ((-674374984711) / 2000000000000) :=
    logU (w := (28551 / 40000)) (c := (28551 / 20000))
      (q := (8898992205111 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-674374984711) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (53 / 100)) ≤ ((-15100451676351) / 20000000000000) :=
    logU (w := (47 / 100)) (c := (47 / 25))
      (q := (63127177730233 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-15100451676351) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-38826441696287) / 50000000000000) ≤ Real.log (1 - (27 / 50)) :=
    logL (w := (23 / 50)) (c := (46 / 25))
      (q := (7622069089927 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-38826441696287) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (53 / 100) ^ 2) ≤ ((-16487742443677) / 50000000000000) :=
    logU (w := (7191 / 10000)) (c := (7191 / 5000))
      (q := (28390025913 / 78125000000)) (k := 1) (J := 6)
      (R := ((-16487742443677) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-275797098489) / 800000000000) ≤ Real.log (1 - (27 / 50) ^ 2) :=
    logL (w := (1771 / 2500)) (c := (1771 / 1250))
      (q := (3484008074487 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-275797098489) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (53 / 100) ≤ x → x ≤ (27 / 50) →
      (42943584066633 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (21787552810543 / 12500000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (53 / 100)) (w := (1 / 100))
      (r1 := (124757732077 / 100000000000))
      (r2 := (745824591 / 500000000)) (r3 := (27328347 / 5000000))
      (r4 := (269001 / 100000))
      (R := (631521554453 / 50000000000000))
      (NL := (42943584066633 / 25000000000000)) (NU := (21787552810543 / 12500000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (53 / 100)) (b := (27 / 50)) (m := (107 / 200))
    (hh := (1 / 200)) (K := (22840190423677 / 50000000000000))
    (bnd := (37035906341521 / 5000000000000000))
    (Lu := ((-15637213302153) / 25000000000000))
    (Ll := ((-31274426604307) / 50000000000000))
    (Ml := ((-76571792862481) / 100000000000000))
    (Nu := ((-674374984711) / 2000000000000))
    (U1 := ((-15100451676351) / 20000000000000))
    (L1 := ((-38826441696287) / 50000000000000))
    (U2 := ((-16487742443677) / 50000000000000))
    (L2 := ((-275797098489) / 800000000000))
    (NL := (42943584066633 / 25000000000000))
    (NU := (21787552810543 / 12500000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_024 {s : ℝ} (hs1 : (27 / 50) ≤ s) (hs2 : s ≤ (11 / 20)) :
    0 < Dfun s := by
  have hLu : Real.log (109 / 200) ≤ ((-3793559276993) / 6250000000000) :=
    logU (w := (109 / 200)) (c := (109 / 100))
      (q := (4308884812053 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-3793559276993) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-6069694843189) / 10000000000000) ≤ Real.log (109 / 200) :=
    logL (w := (109 / 200)) (c := (109 / 100))
      (q := (1723553924821 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-6069694843189) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-15749157910577) / 20000000000000) ≤ Real.log (1 - (109 / 200)) :=
    logL (w := (91 / 200)) (c := (91 / 50))
      (q := (11976729311821 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-15749157910577) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (109 / 200) ^ 2) ≤ ((-35243394968141) / 100000000000000) :=
    logU (w := (28119 / 40000)) (c := (28119 / 20000))
      (q := (34071323087853 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-35243394968141) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (27 / 50)) ≤ ((-77652878921951) / 100000000000000) :=
    logU (w := (23 / 50)) (c := (46 / 25))
      (q := (60976557190037 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-77652878921951) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-79850772438131) / 100000000000000) ≤ Real.log (1 - (11 / 20)) :=
    logL (w := (9 / 20)) (c := (9 / 5))
      (q := (58778663673859 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-79850772438131) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (27 / 50) ^ 2) ≤ ((-34474637307337) / 100000000000000) :=
    logU (w := (1771 / 2500)) (c := (1771 / 1250))
      (q := (34840080748657 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-34474637307337) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-9006319132693) / 25000000000000) ≤ Real.log (1 - (11 / 20) ^ 2) :=
    logL (w := (279 / 400)) (c := (279 / 200))
      (q := (33289441525223 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-9006319132693) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (27 / 50) ≤ x → x ≤ (11 / 20) →
      (85286034041959 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (3460769136833 / 2000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (27 / 50)) (w := (1 / 100))
      (r1 := (7600719997 / 6250000000))
      (r2 := (103377789 / 62500000)) (r3 := (6702507 / 1250000))
      (r4 := (124659 / 50000))
      (R := (616597189433 / 50000000000000))
      (NL := (85286034041959 / 50000000000000)) (NU := (3460769136833 / 2000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (27 / 50)) (b := (11 / 20)) (m := (109 / 200))
    (hh := (1 / 200)) (K := (8784568389919 / 20000000000000))
    (bnd := (12752142897861 / 2000000000000000))
    (Lu := ((-3793559276993) / 6250000000000))
    (Ll := ((-6069694843189) / 10000000000000))
    (Ml := ((-15749157910577) / 20000000000000))
    (Nu := ((-35243394968141) / 100000000000000))
    (U1 := ((-77652878921951) / 100000000000000))
    (L1 := ((-79850772438131) / 100000000000000))
    (U2 := ((-34474637307337) / 100000000000000))
    (L2 := ((-9006319132693) / 25000000000000))
    (NL := (85286034041959 / 50000000000000))
    (NU := (3460769136833 / 2000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_025 {s : ℝ} (hs1 : (11 / 20) ≤ s) (hs2 : s ≤ (14 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (111 / 200) ≤ ((-58878716523569) / 100000000000000) :=
    logU (w := (111 / 200)) (c := (111 / 100))
      (q := (417440061297 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-58878716523569) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-58878716523571) / 100000000000000) ≤ Real.log (111 / 200) :=
    logL (w := (111 / 200)) (c := (111 / 100))
      (q := (1304500191553 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-58878716523571) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-2530253184359) / 3125000000000) ≤ Real.log (1 - (111 / 200)) :=
    logL (w := (89 / 200)) (c := (89 / 50))
      (q := (28830667106251 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-2530253184359) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (111 / 200) ^ 2) ≤ ((-18410272559233) / 50000000000000) :=
    logU (w := (27679 / 40000)) (c := (27679 / 20000))
      (q := (4061771617191 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-18410272559233) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (11 / 20)) ≤ ((-7985076960533) / 10000000000000) :=
    logU (w := (9 / 20)) (c := (9 / 5))
      (q := (29389333253329 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-7985076960533) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-3283922277597) / 4000000000000) ≤ Real.log (1 - (14 / 25)) :=
    logL (w := (11 / 25)) (c := (44 / 25))
      (q := (11306275834413 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-3283922277597) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (11 / 20) ^ 2) ≤ ((-36025276528657) / 100000000000000) :=
    logU (w := (279 / 400)) (c := (279 / 200))
      (q := (33289441527337 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-36025276528657) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-37629473081959) / 100000000000000) ≤ Real.log (1 - (14 / 25) ^ 2) :=
    logL (w := (429 / 625)) (c := (858 / 625))
      (q := (7921311243509 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-37629473081959) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (11 / 20) ≤ x → x ≤ (14 / 25) →
      (42351530633821 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (1342236877947 / 781250000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (11 / 20)) (w := (1 / 100))
      (r1 := (189029677 / 160000000))
      (r2 := (7253793 / 4000000)) (r3 := (1053243 / 200000))
      (r4 := (45927 / 20000))
      (R := (600049460483 / 50000000000000))
      (NL := (42351530633821 / 25000000000000)) (NU := (1342236877947 / 781250000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (11 / 20)) (b := (14 / 25)) (m := (111 / 200))
    (hh := (1 / 200)) (K := (42246077895007 / 100000000000000))
    (bnd := (10867696249187 / 2000000000000000))
    (Lu := ((-58878716523569) / 100000000000000))
    (Ll := ((-58878716523571) / 100000000000000))
    (Ml := ((-2530253184359) / 3125000000000))
    (Nu := ((-18410272559233) / 50000000000000))
    (U1 := ((-7985076960533) / 10000000000000))
    (L1 := ((-3283922277597) / 4000000000000))
    (U2 := ((-36025276528657) / 100000000000000))
    (L2 := ((-37629473081959) / 100000000000000))
    (NL := (42351530633821 / 25000000000000))
    (NU := (1342236877947 / 781250000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_026 {s : ℝ} (hs1 : (14 / 25) ≤ s) (hs2 : s ≤ (57 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (113 / 200) ≤ ((-57092954783569) / 100000000000000) :=
    logU (w := (113 / 200)) (c := (113 / 100))
      (q := (488870530897 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-57092954783569) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-57092954783571) / 100000000000000) ≤ Real.log (113 / 200) :=
    logL (w := (113 / 200)) (c := (113 / 100))
      (q := (1527720409053 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-57092954783571) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-83240926132177) / 100000000000000) ≤ Real.log (1 - (113 / 200)) :=
    logL (w := (87 / 200)) (c := (87 / 50))
      (q := (55388509979813 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-83240926132177) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (113 / 200) ^ 2) ≤ ((-38452342390131) / 100000000000000) :=
    logU (w := (27231 / 40000)) (c := (27231 / 20000))
      (q := (30862375665863 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-38452342390131) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (14 / 25)) ≤ ((-82098055197631) / 100000000000000) :=
    logU (w := (11 / 25)) (c := (44 / 25))
      (q := (56531380914357 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-82098055197631) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-84397008060893) / 100000000000000) ≤ Real.log (1 - (57 / 100)) :=
    logL (w := (43 / 100)) (c := (43 / 25))
      (q := (54232428051097 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-84397008060893) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (14 / 25) ^ 2) ≤ ((-9407368270209) / 25000000000000) :=
    logU (w := (429 / 625)) (c := (858 / 625))
      (q := (15842622487579 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-9407368270209) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-39289445093993) / 100000000000000) ≤ Real.log (1 - (57 / 100) ^ 2) :=
    logL (w := (6751 / 10000)) (c := (6751 / 5000))
      (q := (15012636481001 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-39289445093993) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (14 / 25) ≤ x → x ≤ (57 / 100) →
      (16827962825049 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (85303630696771 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (14 / 25)) (w := (1 / 100))
      (r1 := (446717047 / 390625000))
      (r2 := (15391377 / 7812500)) (r3 := (809109 / 156250))
      (r4 := (6561 / 3125))
      (R := (581908285763 / 50000000000000))
      (NL := (16827962825049 / 10000000000000)) (NU := (85303630696771 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (14 / 25)) (b := (57 / 100)) (m := (113 / 200))
    (hh := (1 / 200)) (K := (40646633235817 / 100000000000000))
    (bnd := (45778112040027 / 10000000000000000))
    (Lu := ((-57092954783569) / 100000000000000))
    (Ll := ((-57092954783571) / 100000000000000))
    (Ml := ((-83240926132177) / 100000000000000))
    (Nu := ((-38452342390131) / 100000000000000))
    (U1 := ((-82098055197631) / 100000000000000))
    (L1 := ((-84397008060893) / 100000000000000))
    (U2 := ((-9407368270209) / 25000000000000))
    (L2 := ((-39289445093993) / 100000000000000))
    (NL := (16827962825049 / 10000000000000))
    (NU := (85303630696771 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_027 {s : ℝ} (hs1 : (57 / 100) ≤ s) (hs2 : s ≤ (29 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (23 / 40) ≤ ((-27669261909239) / 50000000000000) :=
    logU (w := (23 / 40)) (c := (23 / 20))
      (q := (3494048559379 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-27669261909239) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-691731547731) / 1250000000000) ≤ Real.log (23 / 40) :=
    logL (w := (23 / 40)) (c := (23 / 20))
      (q := (2795238847503 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-691731547731) / 1250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-85566611790691) / 100000000000000) ≤ Real.log (1 - (23 / 40)) :=
    logL (w := (17 / 40)) (c := (17 / 10))
      (q := (53062824321299 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-85566611790691) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (23 / 40) ^ 2) ≤ ((-40141083778011) / 100000000000000) :=
    logU (w := (1071 / 1600)) (c := (1071 / 800))
      (q := (29173634277983 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-40141083778011) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (57 / 100)) ≤ ((-16879401404867) / 20000000000000) :=
    logU (w := (43 / 100)) (c := (43 / 25))
      (q := (54232429087653 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-16879401404867) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-33886741157) / 39062500000) ≤ Real.log (1 - (29 / 50)) :=
    logL (w := (21 / 50)) (c := (42 / 25))
      (q := (5187937875007 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-33886741157) / 39062500000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (57 / 100) ^ 2) ≤ ((-39289445093429) / 100000000000000) :=
    logU (w := (6751 / 10000)) (c := (6751 / 5000))
      (q := (6005054592513 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-39289445093429) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-41007572066849) / 100000000000000) ≤ Real.log (1 - (29 / 50) ^ 2) :=
    logL (w := (1659 / 2500)) (c := (1659 / 1250))
      (q := (14153572994573 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-41007572066849) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (57 / 100) ≤ x → x ≤ (29 / 50) →
      (41798915867729 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (21180558544601 / 12500000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (57 / 100)) (w := (1 / 100))
      (r1 := (110264842717 / 100000000000))
      (r2 := (1062112419 / 500000000)) (r3 := (25491267 / 5000000))
      (r4 := (190269 / 100000))
      (R := (562201221473 / 50000000000000))
      (NL := (41798915867729 / 25000000000000)) (NU := (21180558544601 / 12500000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (57 / 100)) (b := (29 / 50)) (m := (23 / 40))
    (hh := (1 / 200)) (K := (7824289934493 / 20000000000000))
    (bnd := (19026425984413 / 5000000000000000))
    (Lu := ((-27669261909239) / 50000000000000))
    (Ll := ((-691731547731) / 1250000000000))
    (Ml := ((-85566611790691) / 100000000000000))
    (Nu := ((-40141083778011) / 100000000000000))
    (U1 := ((-16879401404867) / 20000000000000))
    (L1 := ((-33886741157) / 39062500000))
    (U2 := ((-39289445093429) / 100000000000000))
    (L2 := ((-41007572066849) / 100000000000000))
    (NL := (41798915867729 / 25000000000000))
    (NU := (21180558544601 / 12500000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_028 {s : ℝ} (hs1 : (29 / 50) ≤ s) (hs2 : s ≤ (59 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (117 / 200) ≤ ((-53614343175027) / 100000000000000) :=
    logU (w := (117 / 200)) (c := (117 / 100))
      (q := (15700374880967 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-53614343175027) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-53614343175029) / 100000000000000) ≤ Real.log (117 / 200) :=
    logL (w := (117 / 200)) (c := (117 / 100))
      (q := (7850187440483 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-53614343175029) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-43973838158077) / 50000000000000) ≤ Real.log (1 - (117 / 200)) :=
    logL (w := (83 / 200)) (c := (83 / 50))
      (q := (12670439948959 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-43973838158077) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (117 / 200) ^ 2) ≤ ((-20944617571109) / 50000000000000) :=
    logU (w := (26311 / 40000)) (c := (26311 / 20000))
      (q := (1714092682111 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-20944617571109) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (29 / 50)) ≤ ((-21687514191947) / 25000000000000) :=
    logU (w := (21 / 50)) (c := (42 / 25))
      (q := (259396896721 / 500000000000)) (k := 2) (J := 6)
      (R := ((-21687514191947) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-2228995306339) / 2500000000000) ≤ Real.log (1 - (59 / 100)) :=
    logL (w := (41 / 100)) (c := (41 / 25))
      (q := (4946962385843 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-2228995306339) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (29 / 50) ^ 2) ≤ ((-41007572066583) / 100000000000000) :=
    logU (w := (1659 / 2500)) (c := (1659 / 1250))
      (q := (28307145989411 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-41007572066583) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-42786410305279) / 100000000000000) ≤ Real.log (1 - (59 / 100) ^ 2) :=
    logL (w := (6519 / 10000)) (c := (6519 / 5000))
      (q := (6632076937679 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-42786410305279) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (29 / 50) ≤ x → x ≤ (59 / 100) →
      (83078630386691 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (84160537310397 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (29 / 50)) (w := (1 / 100))
      (r1 := (6616511677 / 6250000000))
      (r2 := (142254387 / 62500000)) (r3 := (6282603 / 1250000))
      (r4 := (85293 / 50000))
      (R := (540953461853 / 50000000000000))
      (NL := (83078630386691 / 50000000000000)) (NU := (84160537310397 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (29 / 50)) (b := (59 / 100)) (m := (117 / 200))
    (hh := (1 / 200)) (K := (37667833612863 / 100000000000000))
    (bnd := (31136127839989 / 10000000000000000))
    (Lu := ((-53614343175027) / 100000000000000))
    (Ll := ((-53614343175029) / 100000000000000))
    (Ml := ((-43973838158077) / 50000000000000))
    (Nu := ((-20944617571109) / 50000000000000))
    (U1 := ((-21687514191947) / 25000000000000))
    (L1 := ((-2228995306339) / 2500000000000))
    (U2 := ((-41007572066583) / 100000000000000))
    (L2 := ((-42786410305279) / 100000000000000))
    (NL := (83078630386691 / 50000000000000))
    (NU := (84160537310397 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_029 {s : ℝ} (hs1 : (59 / 100) ≤ s) (hs2 : s ≤ (599 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1189 / 2000) ≤ ((-52003456285129) / 100000000000000) :=
    logU (w := (1189 / 2000)) (c := (1189 / 1000))
      (q := (3462252354173 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-52003456285129) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-52003456285131) / 100000000000000) ≤ Real.log (1189 / 2000) :=
    logL (w := (1189 / 2000)) (c := (1189 / 1000))
      (q := (1081953860679 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-52003456285131) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-45131720393679) / 50000000000000) ≤ Real.log (1 - (1189 / 2000)) :=
    logL (w := (811 / 2000)) (c := (811 / 500))
      (q := (6045749415579 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-45131720393679) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1189 / 2000) ^ 2) ≤ ((-10901854948967) / 25000000000000) :=
    logU (w := (2586279 / 4000000)) (c := (2586279 / 2000000))
      (q := (12853649130063 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-10901854948967) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (59 / 100)) ≤ ((-89159811927037) / 100000000000000) :=
    logU (w := (41 / 100)) (c := (41 / 25))
      (q := (49469624184951 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-89159811927037) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-91379385349803) / 100000000000000) ≤ Real.log (1 - (599 / 1000)) :=
    logL (w := (401 / 1000)) (c := (401 / 250))
      (q := (47250050762187 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-91379385349803) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (59 / 100) ^ 2) ≤ ((-42786410305163) / 100000000000000) :=
    logU (w := (6519 / 10000)) (c := (6519 / 5000))
      (q := (26528307750831 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-42786410305163) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-22220770891213) / 50000000000000) ≤ Real.log (1 - (599 / 1000) ^ 2) :=
    logL (w := (641199 / 1000000)) (c := (641199 / 500000))
      (q := (24873176273569 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-22220770891213) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (59 / 100) ≤ x → x ≤ (599 / 1000) →
      (2065916473379 / 1250000000000) ≤ Npoly x ∧
      Npoly x ≤ (41783564268637 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (59 / 100)) (w := (9 / 1000))
      (r1 := (101161926637 / 100000000000))
      (r2 := (1212934257 / 500000000)) (r3 := (24808923 / 5000000))
      (r4 := (150903 / 100000))
      (R := (465234801057 / 50000000000000))
      (NL := (2065916473379 / 1250000000000)) (NU := (41783564268637 / 25000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (59 / 100)) (b := (599 / 1000)) (m := (1189 / 2000))
    (hh := (9 / 2000)) (K := (16636451360477 / 50000000000000))
    (bnd := (25290053038203 / 10000000000000000))
    (Lu := ((-52003456285129) / 100000000000000))
    (Ll := ((-52003456285131) / 100000000000000))
    (Ml := ((-45131720393679) / 50000000000000))
    (Nu := ((-10901854948967) / 25000000000000))
    (U1 := ((-89159811927037) / 100000000000000))
    (L1 := ((-91379385349803) / 100000000000000))
    (U2 := ((-42786410305163) / 100000000000000))
    (L2 := ((-22220770891213) / 50000000000000))
    (NL := (2065916473379 / 1250000000000))
    (NU := (41783564268637 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_030 {s : ℝ} (hs1 : (599 / 1000) ≤ s) (hs2 : s ≤ (607 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (603 / 1000) ≤ ((-25291904112747) / 50000000000000) :=
    logU (w := (603 / 1000)) (c := (603 / 500))
      (q := (37461819661 / 200000000000)) (k := 1) (J := 6)
      (R := ((-25291904112747) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-50583808225497) / 100000000000000) ≤ Real.log (603 / 1000) :=
    logL (w := (603 / 1000)) (c := (603 / 500))
      (q := (9365454915249 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-50583808225497) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-46190949984237) / 50000000000000) ≤ Real.log (1 - (603 / 1000)) :=
    logL (w := (397 / 1000)) (c := (397 / 250))
      (q := (11561884035879 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-46190949984237) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (603 / 1000) ^ 2) ≤ ((-706159569793) / 1562500000000) :=
    logU (w := (636391 / 1000000)) (c := (636391 / 500000))
      (q := (12060252794621 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-706159569793) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (599 / 1000)) ≤ ((-91379385166871) / 100000000000000) :=
    logU (w := (401 / 1000)) (c := (401 / 250))
      (q := (47250050945117 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-91379385166871) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-93394566816311) / 100000000000000) ≤ Real.log (1 - (607 / 1000)) :=
    logL (w := (393 / 1000)) (c := (393 / 250))
      (q := (45234869295679 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-93394566816311) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (599 / 1000) ^ 2) ≤ ((-22220770891187) / 50000000000000) :=
    logU (w := (641199 / 1000000)) (c := (641199 / 500000))
      (q := (1243658813681 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-22220770891187) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-45957658035773) / 100000000000000) ≤ Real.log (1 - (607 / 1000) ^ 2) :=
    logL (w := (631551 / 1000000)) (c := (631551 / 500000))
      (q := (11678530010111 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-45957658035773) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (599 / 1000) ≤ x → x ≤ (607 / 1000) →
      (164523308233937 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (20762921574491 / 12500000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (599 / 1000)) (w := (1 / 125))
      (r1 := (241688047663 / 250000000000))
      (r2 := (1279566003717 / 500000000000)) (r3 := (2455324083 / 500000000))
      (r4 := (1331883 / 1000000))
      (R := (158006436199 / 20000000000000))
      (NL := (164523308233937 / 100000000000000)) (NU := (20762921574491 / 12500000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (599 / 1000)) (b := (607 / 1000)) (m := (603 / 1000))
    (hh := (1 / 250)) (K := (29172727306569 / 100000000000000))
    (bnd := (20639144444287 / 10000000000000000))
    (Lu := ((-25291904112747) / 50000000000000))
    (Ll := ((-50583808225497) / 100000000000000))
    (Ml := ((-46190949984237) / 50000000000000))
    (Nu := ((-706159569793) / 1562500000000))
    (U1 := ((-91379385166871) / 100000000000000))
    (L1 := ((-93394566816311) / 100000000000000))
    (U2 := ((-22220770891187) / 50000000000000))
    (L2 := ((-45957658035773) / 100000000000000))
    (NL := (164523308233937 / 100000000000000))
    (NU := (20762921574491 / 12500000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_031 {s : ℝ} (hs1 : (607 / 1000) ≤ s) (hs2 : s ≤ (307 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (1221 / 2000) ≤ ((-49347698543137) / 100000000000000) :=
    logU (w := (1221 / 2000)) (c := (1221 / 1000))
      (q := (19967019512857 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-49347698543137) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-24673849271571) / 50000000000000) ≤ Real.log (1221 / 2000) :=
    logL (w := (1221 / 2000)) (c := (1221 / 1000))
      (q := (19967019512853 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-24673849271571) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-2357228536217) / 2500000000000) ≤ Real.log (1 - (1221 / 2000)) :=
    logL (w := (779 / 2000)) (c := (779 / 500))
      (q := (4434029466331 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-2357228536217) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1221 / 2000) ^ 2) ≤ ((-46634672388221) / 100000000000000) :=
    logU (w := (2509159 / 4000000)) (c := (2509159 / 2000000))
      (q := (22680045667773 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-46634672388221) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (607 / 1000)) ≤ ((-3735782668437) / 4000000000000) :=
    logU (w := (393 / 1000)) (c := (393 / 250))
      (q := (45234869401063 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-3735782668437) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-95191791014557) / 100000000000000) ≤ Real.log (1 - (307 / 500)) :=
    logL (w := (193 / 500)) (c := (193 / 125))
      (q := (43437645097433 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-95191791014557) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (607 / 1000) ^ 2) ≤ ((-45957658035749) / 100000000000000) :=
    logU (w := (631551 / 1000000)) (c := (631551 / 500000))
      (q := (4671412004049 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-45957658035749) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-23660116983483) / 50000000000000) ≤ Real.log (1 - (307 / 500) ^ 2) :=
    logL (w := (155751 / 250000)) (c := (155751 / 125000))
      (q := (21994484089029 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-23660116983483) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (607 / 1000) ≤ x → x ≤ (307 / 500) →
      (81947939851437 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (165217256296737 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (607 / 1000)) (w := (7 / 1000))
      (r1 := (23121647029 / 25000000000))
      (r2 := (1338248137869 / 500000000000)) (r3 := (2435273667 / 500000000))
      (r4 := (1174419 / 1000000))
      (R := (660688296931 / 100000000000000))
      (NL := (81947939851437 / 50000000000000)) (NU := (165217256296737 / 100000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (607 / 1000)) (b := (307 / 500)) (m := (1221 / 2000))
    (hh := (7 / 2000)) (K := (25324039093669 / 100000000000000))
    (bnd := (4244172293099 / 2500000000000000))
    (Lu := ((-49347698543137) / 100000000000000))
    (Ll := ((-24673849271571) / 50000000000000))
    (Ml := ((-2357228536217) / 2500000000000))
    (Nu := ((-46634672388221) / 100000000000000))
    (U1 := ((-3735782668437) / 4000000000000))
    (L1 := ((-95191791014557) / 100000000000000))
    (U2 := ((-45957658035749) / 100000000000000))
    (L2 := ((-23660116983483) / 50000000000000))
    (NL := (81947939851437 / 50000000000000))
    (NU := (165217256296737 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_032 {s : ℝ} (hs1 : (307 / 500) ≤ s) (hs2 : s ≤ (31 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (617 / 1000) ≤ ((-24144312753837) / 50000000000000) :=
    logU (w := (617 / 1000)) (c := (617 / 500))
      (q := (131413078427 / 625000000000)) (k := 1) (J := 6)
      (R := ((-24144312753837) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-24144312753841) / 50000000000000) ≤ Real.log (617 / 1000) :=
    logL (w := (617 / 1000)) (c := (617 / 500))
      (q := (21026092548313 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-24144312753841) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-19194405806013) / 20000000000000) ≤ Real.log (1 - (617 / 1000)) :=
    logL (w := (383 / 1000)) (c := (383 / 250))
      (q := (1706296283277 / 4000000000000)) (k := 2) (J := 6)
      (R := ((-19194405806013) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (617 / 1000) ^ 2) ≤ ((-47914770920651) / 100000000000000) :=
    logU (w := (619311 / 1000000)) (c := (619311 / 500000))
      (q := (21399947135343 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-47914770920651) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (307 / 500)) ≤ ((-9519179095153) / 10000000000000) :=
    logU (w := (193 / 500)) (c := (193 / 125))
      (q := (21718822580229 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-9519179095153) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-96758402665579) / 100000000000000) ≤ Real.log (1 - (31 / 50)) :=
    logL (w := (19 / 50)) (c := (38 / 25))
      (q := (41871033446411 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-96758402665579) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (307 / 500) ^ 2) ≤ ((-23660116983477) / 50000000000000) :=
    logU (w := (155751 / 250000)) (c := (155751 / 125000))
      (q := (274931051113 / 1250000000000)) (k := 1) (J := 6)
      (R := ((-23660116983477) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-48515787701747) / 100000000000000) ≤ Real.log (1 - (31 / 50) ^ 2) :=
    logL (w := (1539 / 2500)) (c := (1539 / 1250))
      (q := (2599866294281 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-48515787701747) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (307 / 500) ≤ x → x ≤ (31 / 50) →
      (163380328104841 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (5139517465421 / 3125000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (307 / 500)) (w := (3 / 500))
      (r1 := (443340263443 / 500000000000))
      (r2 := (173652874569 / 62500000000)) (r3 := (604949067 / 125000000))
      (r4 := (518319 / 500000))
      (R := (108423078863 / 20000000000000))
      (NL := (163380328104841 / 100000000000000)) (NU := (5139517465421 / 3125000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (307 / 500)) (b := (31 / 50)) (m := (617 / 1000))
    (hh := (3 / 1000)) (K := (10845133685203 / 50000000000000))
    (bnd := (14128198151829 / 10000000000000000))
    (Lu := ((-24144312753837) / 50000000000000))
    (Ll := ((-24144312753841) / 50000000000000))
    (Ml := ((-19194405806013) / 20000000000000))
    (Nu := ((-47914770920651) / 100000000000000))
    (U1 := ((-9519179095153) / 10000000000000))
    (L1 := ((-96758402665579) / 100000000000000))
    (U2 := ((-23660116983477) / 50000000000000))
    (L2 := ((-48515787701747) / 100000000000000))
    (NL := (163380328104841 / 100000000000000))
    (NU := (5139517465421 / 3125000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_033 {s : ℝ} (hs1 : (31 / 50) ≤ s) (hs2 : s ≤ (313 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (623 / 1000) ≤ ((-47320876019467) / 100000000000000) :=
    logU (w := (623 / 1000)) (c := (623 / 500))
      (q := (21993842036527 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-47320876019467) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-1183021900487) / 2500000000000) ≤ Real.log (623 / 1000) :=
    logL (w := (623 / 1000)) (c := (623 / 500))
      (q := (4398768407303 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-1183021900487) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-97551009184321) / 100000000000000) ≤ Real.log (1 - (623 / 1000)) :=
    logL (w := (377 / 1000)) (c := (377 / 250))
      (q := (41078426927669 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-97551009184321) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (623 / 1000) ^ 2) ≤ ((-24561690150083) / 50000000000000) :=
    logU (w := (611871 / 1000000)) (c := (611871 / 500000))
      (q := (5047834438957 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-24561690150083) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (31 / 50)) ≤ ((-96758402626053) / 100000000000000) :=
    logU (w := (19 / 50)) (c := (38 / 25))
      (q := (8374206697187 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-96758402626053) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-49174974090417) / 50000000000000) ≤ Real.log (1 - (313 / 500)) :=
    logL (w := (187 / 500)) (c := (187 / 125))
      (q := (10069871982789 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-49174974090417) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (31 / 50) ^ 2) ≤ ((-2425789385087) / 5000000000000) :=
    logU (w := (1539 / 2500)) (c := (1539 / 1250))
      (q := (10399465177127 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2425789385087) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-24868823522101) / 50000000000000) ≤ Real.log (1 - (313 / 500) ^ 2) :=
    logL (w := (152031 / 250000)) (c := (152031 / 125000))
      (q := (19577071011793 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-24868823522101) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (31 / 50) ≤ x → x ≤ (313 / 500) →
      (81439216092413 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (81961325900099 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (31 / 50)) (w := (3 / 500))
      (r1 := (5330108557 / 6250000000))
      (r2 := (179083953 / 62500000)) (r3 := (6020163 / 1250000))
      (r4 := (45927 / 50000))
      (R := (261054903843 / 50000000000000))
      (NL := (81439216092413 / 50000000000000)) (NU := (81961325900099 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (31 / 50)) (b := (313 / 500)) (m := (623 / 1000))
    (hh := (3 / 1000)) (K := (10549005098641 / 50000000000000))
    (bnd := (5880297292103 / 5000000000000000))
    (Lu := ((-47320876019467) / 100000000000000))
    (Ll := ((-1183021900487) / 2500000000000))
    (Ml := ((-97551009184321) / 100000000000000))
    (Nu := ((-24561690150083) / 50000000000000))
    (U1 := ((-96758402626053) / 100000000000000))
    (L1 := ((-49174974090417) / 50000000000000))
    (U2 := ((-2425789385087) / 5000000000000))
    (L2 := ((-24868823522101) / 50000000000000))
    (NL := (81439216092413 / 50000000000000))
    (NU := (81961325900099 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_034 {s : ℝ} (hs1 : (313 / 500) ≤ s) (hs2 : s ≤ (63 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (157 / 250) ≤ ((-46521511251393) / 100000000000000) :=
    logU (w := (157 / 250)) (c := (157 / 125))
      (q := (22793206804601 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-46521511251393) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-46521511251411) / 100000000000000) ≤ Real.log (157 / 250) :=
    logL (w := (157 / 250)) (c := (157 / 125))
      (q := (2849150850573 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-46521511251411) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-24721535622799) / 25000000000000) ≤ Real.log (1 - (157 / 250)) :=
    logL (w := (93 / 250)) (c := (186 / 125))
      (q := (19871646810397 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-24721535622799) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (157 / 250) ^ 2) ≤ ((-50150915712863) / 100000000000000) :=
    logU (w := (37851 / 62500)) (c := (37851 / 31250))
      (q := (19163802343131 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-50150915712863) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (313 / 500)) ≤ ((-98349948156693) / 100000000000000) :=
    logU (w := (187 / 500)) (c := (187 / 125))
      (q := (8055897591059 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-98349948156693) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-99425227351443) / 100000000000000) ≤ Real.log (1 - (63 / 100)) :=
    logL (w := (37 / 100)) (c := (37 / 25))
      (q := (39204208760547 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-99425227351443) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (313 / 500) ^ 2) ≤ ((-24868823522099) / 50000000000000) :=
    logU (w := (152031 / 250000)) (c := (152031 / 125000))
      (q := (4894267752949 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-24868823522099) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-25283612926261) / 50000000000000) ≤ Real.log (1 - (63 / 100) ^ 2) :=
    logL (w := (6031 / 10000)) (c := (6031 / 5000))
      (q := (18747492203473 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-25283612926261) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (313 / 500) ≤ x → x ≤ (63 / 100) →
      (162567351506677 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (81615594965829 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (313 / 500)) (w := (1 / 250))
      (r1 := (817913876171 / 1000000000000))
      (r2 := (184490230851 / 62500000000)) (r3 := (599437827 / 125000000))
      (r4 := (400221 / 500000))
      (R := (33191921249 / 10000000000000))
      (NL := (162567351506677 / 100000000000000)) (NU := (81615594965829 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (313 / 500)) (b := (63 / 100)) (m := (157 / 250))
    (hh := (1 / 500)) (K := (14862188175871 / 100000000000000))
    (bnd := (9975307639717 / 10000000000000000))
    (Lu := ((-46521511251393) / 100000000000000))
    (Ll := ((-46521511251411) / 100000000000000))
    (Ml := ((-24721535622799) / 25000000000000))
    (Nu := ((-50150915712863) / 100000000000000))
    (U1 := ((-98349948156693) / 100000000000000))
    (L1 := ((-99425227351443) / 100000000000000))
    (U2 := ((-24868823522099) / 50000000000000))
    (L2 := ((-25283612926261) / 50000000000000))
    (NL := (162567351506677 / 100000000000000))
    (NU := (81615594965829 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_035 {s : ℝ} (hs1 : (63 / 100) ≤ s) (hs2 : s ≤ (127 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (253 / 400) ≤ ((-9161501167609) / 20000000000000) :=
    logU (w := (253 / 400)) (c := (253 / 200))
      (q := (23507212217949 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-9161501167609) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-45807505838071) / 100000000000000) ≤ Real.log (253 / 400) :=
    logL (w := (253 / 400)) (c := (253 / 200))
      (q := (5876803054481 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-45807505838071) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-5005159802329) / 5000000000000) ≤ Real.log (1 - (253 / 400)) :=
    logL (w := (147 / 400)) (c := (147 / 100))
      (q := (3852624006541 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-5005159802329) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (253 / 400) ^ 2) ≤ ((-51091937816079) / 100000000000000) :=
    logU (w := (95991 / 160000)) (c := (95991 / 80000))
      (q := (3644556047983 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-51091937816079) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (63 / 100)) ≤ ((-99425227334341) / 100000000000000) :=
    logU (w := (37 / 100)) (c := (37 / 25))
      (q := (39204208777647 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-99425227334341) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-25196448137709) / 25000000000000) ≤ Real.log (1 - (127 / 200)) :=
    logL (w := (73 / 200)) (c := (73 / 50))
      (q := (18921821780577 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-25196448137709) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (63 / 100) ^ 2) ≤ ((-50567225852519) / 100000000000000) :=
    logU (w := (6031 / 10000)) (c := (6031 / 5000))
      (q := (749899688139 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-50567225852519) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-12905378026261) / 25000000000000) ≤ Real.log (1 - (127 / 200) ^ 2) :=
    logL (w := (23871 / 40000)) (c := (23871 / 20000))
      (q := (17693205950951 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-12905378026261) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (63 / 100) ≤ x → x ≤ (127 / 200) →
      (162172241092143 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (162981476487333 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (63 / 100)) (w := (1 / 200))
      (r1 := (79406914237 / 100000000000))
      (r2 := (1504657701 / 500000000)) (r3 := (23916627 / 5000000))
      (r4 := (72171 / 100000))
      (R := (80923539519 / 20000000000000))
      (NL := (162172241092143 / 100000000000000)) (NU := (162981476487333 / 100000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (63 / 100)) (b := (127 / 200)) (m := (253 / 400))
    (hh := (1 / 400)) (K := (3467312406609 / 20000000000000))
    (bnd := (8511521974329 / 10000000000000000))
    (Lu := ((-9161501167609) / 20000000000000))
    (Ll := ((-45807505838071) / 100000000000000))
    (Ml := ((-5005159802329) / 5000000000000))
    (Nu := ((-51091937816079) / 100000000000000))
    (U1 := ((-99425227334341) / 100000000000000))
    (L1 := ((-25196448137709) / 25000000000000))
    (U2 := ((-50567225852519) / 100000000000000))
    (L2 := ((-12905378026261) / 25000000000000))
    (NL := (162172241092143 / 100000000000000))
    (NU := (162981476487333 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_036 {s : ℝ} (hs1 : (127 / 200) ≤ s) (hs2 : s ≤ (16 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (51 / 80) ≤ ((-9004020038991) / 20000000000000) :=
    logU (w := (51 / 80)) (c := (51 / 40))
      (q := (24294617861039 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-9004020038991) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-45020100194993) / 100000000000000) ≤ Real.log (51 / 80) :=
    logL (w := (51 / 80)) (c := (51 / 40))
      (q := (12147308930501 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-45020100194993) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-20294616095469) / 20000000000000) ≤ Real.log (1 - (51 / 80)) :=
    logL (w := (29 / 80)) (c := (29 / 20))
      (q := (7431271126929 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-20294616095469) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (51 / 80) ^ 2) ≤ ((-52156011616013) / 100000000000000) :=
    logU (w := (3799 / 6400)) (c := (3799 / 3200))
      (q := (17158706439981 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-52156011616013) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (127 / 200)) ≤ ((-100785792539937) / 100000000000000) :=
    logU (w := (73 / 200)) (c := (73 / 50))
      (q := (37843643572051 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-100785792539937) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-20433024951993) / 20000000000000) ≤ Real.log (1 - (16 / 25)) :=
    logL (w := (9 / 25)) (c := (36 / 25))
      (q := (1458572454081 / 4000000000000)) (k := 2) (J := 6)
      (R := ((-20433024951993) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (127 / 200) ^ 2) ≤ ((-25810756052521) / 50000000000000) :=
    logU (w := (23871 / 40000)) (c := (23871 / 20000))
      (q := (2211650743869 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-25810756052521) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-52695500569589) / 100000000000000) ≤ Real.log (1 - (16 / 25) ^ 2) :=
    logL (w := (369 / 625)) (c := (738 / 625))
      (q := (8309608743203 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-52695500569589) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (127 / 200) ≤ x → x ≤ (16 / 25) →
      (80898918196251 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (32515395623399 / 20000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (127 / 200)) (w := (1 / 200))
      (r1 := (763617587499 / 1000000000000))
      (r2 := (12323847789 / 4000000000)) (r3 := (95397507 / 20000000))
      (r4 := (124659 / 200000))
      (R := (194785431123 / 50000000000000))
      (NL := (80898918196251 / 50000000000000)) (NU := (32515395623399 / 20000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (127 / 200)) (b := (16 / 25)) (m := (51 / 80))
    (hh := (1 / 400)) (K := (338025313593 / 2000000000000))
    (bnd := (7040893308797 / 10000000000000000))
    (Lu := ((-9004020038991) / 20000000000000))
    (Ll := ((-45020100194993) / 100000000000000))
    (Ml := ((-20294616095469) / 20000000000000))
    (Nu := ((-52156011616013) / 100000000000000))
    (U1 := ((-100785792539937) / 100000000000000))
    (L1 := ((-20433024951993) / 20000000000000))
    (U2 := ((-25810756052521) / 50000000000000))
    (L2 := ((-52695500569589) / 100000000000000))
    (NL := (80898918196251 / 50000000000000))
    (NU := (32515395623399 / 20000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_037 {s : ℝ} (hs1 : (16 / 25) ≤ s) (hs2 : s ≤ (161 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (321 / 500) ≤ ((-44316697529217) / 100000000000000) :=
    logU (w := (321 / 500)) (c := (321 / 250))
      (q := (24998020526777 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-44316697529217) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-5539587191159) / 12500000000000) ≤ Real.log (321 / 500) :=
    logL (w := (321 / 500)) (c := (321 / 250))
      (q := (24998020526723 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5539587191159) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-51361114631851) / 50000000000000) ≤ Real.log (1 - (321 / 500)) :=
    logL (w := (179 / 500)) (c := (179 / 125))
      (q := (1122100214009 / 3125000000000)) (k := 2) (J := 6)
      (R := ((-51361114631851) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (321 / 500) ^ 2) ≤ ((-53130728155119) / 100000000000000) :=
    logU (w := (146959 / 250000)) (c := (146959 / 125000))
      (q := (129471919207 / 800000000000)) (k := 1) (J := 6)
      (R := ((-53130728155119) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (16 / 25)) ≤ ((-102165124753181) / 100000000000000) :=
    logU (w := (9 / 25)) (c := (36 / 25))
      (q := (36464311358807 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-102165124753181) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-103282454817557) / 100000000000000) ≤ Real.log (1 - (161 / 250)) :=
    logL (w := (89 / 250)) (c := (178 / 125))
      (q := (35346981294433 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-103282454817557) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (16 / 25) ^ 2) ≤ ((-26347750284793) / 50000000000000) :=
    logU (w := (369 / 625)) (c := (738 / 625))
      (q := (2077402185801 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-26347750284793) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-53569225149613) / 100000000000000) ≤ Real.log (1 - (161 / 250) ^ 2) :=
    logL (w := (36579 / 62500)) (c := (36579 / 31250))
      (q := (7872746453191 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-53569225149613) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (16 / 25) ≤ x → x ≤ (161 / 250) →
      (16151530589893 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (81055707502119 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (16 / 25)) (w := (1 / 250))
      (r1 := (286113487 / 390625000))
      (r2 := (24628293 / 7812500)) (r3 := (743499 / 156250))
      (r4 := (6561 / 12500))
      (R := (149027276327 / 50000000000000))
      (NL := (16151530589893 / 10000000000000)) (NU := (81055707502119 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (16 / 25)) (b := (161 / 250)) (m := (321 / 500))
    (hh := (1 / 500)) (K := (13705456944899 / 100000000000000))
    (bnd := (14637203087 / 25000000000000))
    (Lu := ((-44316697529217) / 100000000000000))
    (Ll := ((-5539587191159) / 12500000000000))
    (Ml := ((-51361114631851) / 50000000000000))
    (Nu := ((-53130728155119) / 100000000000000))
    (U1 := ((-102165124753181) / 100000000000000))
    (L1 := ((-103282454817557) / 100000000000000))
    (U2 := ((-26347750284793) / 50000000000000))
    (L2 := ((-53569225149613) / 100000000000000))
    (NL := (16151530589893 / 10000000000000))
    (NU := (81055707502119 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_038 {s : ℝ} (hs1 : (161 / 250) ≤ s) (hs2 : s ≤ (81 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (323 / 500) ≤ ((-2730973594997) / 6250000000000) :=
    logU (w := (323 / 500)) (c := (323 / 250))
      (q := (12809570268021 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2730973594997) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-43695577520027) / 100000000000000) ≤ Real.log (323 / 500) :=
    logL (w := (323 / 500)) (c := (323 / 250))
      (q := (800598141749 / 3125000000000)) (k := 1) (J := 6)
      (R := ((-43695577520027) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-51922918294269) / 50000000000000) ≤ Real.log (1 - (323 / 500)) :=
    logL (w := (177 / 500)) (c := (177 / 125))
      (q := (8695899880863 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-51922918294269) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (323 / 500) ^ 2) ≤ ((-54011026359347) / 100000000000000) :=
    logU (w := (145671 / 250000)) (c := (145671 / 125000))
      (q := (15303691696647 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-54011026359347) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (161 / 250)) ≤ ((-103282454813) / 100000000000) :=
    logU (w := (89 / 250)) (c := (178 / 125))
      (q := (8836745324747 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-103282454813) / 100000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-26103102585351) / 25000000000000) ≤ Real.log (1 - (81 / 125)) :=
    logL (w := (44 / 125)) (c := (176 / 125))
      (q := (17108512885293 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-26103102585351) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (161 / 250) ^ 2) ≤ ((-53569225149611) / 100000000000000) :=
    logU (w := (36579 / 62500)) (c := (36579 / 31250))
      (q := (15745492906383 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-53569225149611) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-54456167189677) / 100000000000000) ≤ Real.log (1 - (81 / 125) ^ 2) :=
    logL (w := (9064 / 15625)) (c := (18128 / 15625))
      (q := (7429275433159 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-54456167189677) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (161 / 250) ≤ x → x ≤ (81 / 125) →
      (629833936831 / 390625000000) ≤ Npoly x ∧
      Npoly x ≤ (161813421283239 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (161 / 250)) (w := (1 / 250))
      (r1 := (353501440563 / 500000000000))
      (r2 := (25074018423 / 7812500000)) (r3 := (148457043 / 31250000))
      (r4 := (111537 / 250000))
      (R := (287966727251 / 100000000000000))
      (NL := (629833936831 / 390625000000)) (NU := (161813421283239 / 100000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (161 / 250)) (b := (81 / 125)) (m := (323 / 500))
    (hh := (1 / 500)) (K := (2677914008753 / 20000000000000))
    (bnd := (245399809713 / 500000000000000))
    (Lu := ((-2730973594997) / 6250000000000))
    (Ll := ((-43695577520027) / 100000000000000))
    (Ml := ((-51922918294269) / 50000000000000))
    (Nu := ((-54011026359347) / 100000000000000))
    (U1 := ((-103282454813) / 100000000000))
    (L1 := ((-26103102585351) / 25000000000000))
    (U2 := ((-53569225149611) / 100000000000000))
    (L2 := ((-54456167189677) / 100000000000000))
    (NL := (629833936831 / 390625000000))
    (NU := (161813421283239 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_039 {s : ℝ} (hs1 : (81 / 125) ≤ s) (hs2 : s ≤ (163 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (13 / 20) ≤ ((-10769572902311) / 25000000000000) :=
    logU (w := (13 / 20)) (c := (13 / 10))
      (q := (104945705787 / 400000000000)) (k := 1) (J := 6)
      (R := ((-10769572902311) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-8615658321869) / 20000000000000) ≤ Real.log (13 / 20) :=
    logL (w := (13 / 20)) (c := (13 / 10))
      (q := (524728528933 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-8615658321869) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-1640347069567) / 1562500000000) ≤ Real.log (1 - (13 / 20)) :=
    logL (w := (7 / 20)) (c := (7 / 5))
      (q := (16823611829851 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-1640347069567) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (13 / 20) ^ 2) ≤ ((-27452341829309) / 50000000000000) :=
    logU (w := (231 / 400)) (c := (231 / 200))
      (q := (225156787459 / 1562500000000)) (k := 1) (J := 6)
      (R := ((-27452341829309) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (81 / 125)) ≤ ((-104412410338397) / 100000000000000) :=
    logU (w := (44 / 125)) (c := (176 / 125))
      (q := (34217025773591 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-104412410338397) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-26388819980677) / 25000000000000) ≤ Real.log (1 - (163 / 250)) :=
    logL (w := (87 / 250)) (c := (174 / 125))
      (q := (16537078094641 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-26388819980677) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (81 / 125) ^ 2) ≤ ((-2178246687587) / 4000000000000) :=
    logU (w := (9064 / 15625)) (c := (18128 / 15625))
      (q := (14858550866319 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2178246687587) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-55356612410889) / 100000000000000) ≤ Real.log (1 - (163 / 250) ^ 2) :=
    logL (w := (35931 / 62500)) (c := (35931 / 31250))
      (q := (6979052822553 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-55356612410889) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (81 / 125) ≤ x → x ≤ (163 / 250) →
      (80485061305343 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (161525515300303 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (81 / 125)) (w := (1 / 250))
      (r1 := (340549582709 / 500000000000))
      (r2 := (797471082 / 244140625)) (r3 := (37063413 / 7812500))
      (r4 := (45927 / 125000))
      (R := (34712043101 / 12500000000000))
      (NL := (80485061305343 / 50000000000000)) (NU := (161525515300303 / 100000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (81 / 125)) (b := (163 / 250)) (m := (13 / 20))
    (hh := (1 / 500)) (K := (3270040342253 / 25000000000000))
    (bnd := (2030175120179 / 5000000000000000))
    (Lu := ((-10769572902311) / 25000000000000))
    (Ll := ((-8615658321869) / 20000000000000))
    (Ml := ((-1640347069567) / 1562500000000))
    (Nu := ((-27452341829309) / 50000000000000))
    (U1 := ((-104412410338397) / 100000000000000))
    (L1 := ((-26388819980677) / 25000000000000))
    (U2 := ((-2178246687587) / 4000000000000))
    (L2 := ((-55356612410889) / 100000000000000))
    (NL := (80485061305343 / 50000000000000))
    (NU := (161525515300303 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_040 {s : ℝ} (hs1 : (163 / 250) ≤ s) (hs2 : s ≤ (131 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (1307 / 2000) ≤ ((-8508254918357) / 20000000000000) :=
    logU (w := (1307 / 2000)) (c := (1307 / 1000))
      (q := (26773443464209 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8508254918357) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-8508254918383) / 20000000000000) ≤ Real.log (1307 / 2000) :=
    logL (w := (1307 / 2000)) (c := (1307 / 1000))
      (q := (334668043301 / 1250000000000)) (k := 1) (J := 6)
      (R := ((-8508254918383) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-105987246036859) / 100000000000000) ≤ Real.log (1 - (1307 / 2000)) :=
    logL (w := (693 / 2000)) (c := (693 / 500))
      (q := (32642190075131 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-105987246036859) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1307 / 2000) ^ 2) ≤ ((-27848910345623) / 50000000000000) :=
    logU (w := (2291751 / 4000000)) (c := (2291751 / 2000000))
      (q := (3404224341187 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-27848910345623) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (163 / 250)) ≤ ((-105555279920761) / 100000000000000) :=
    logU (w := (87 / 250)) (c := (174 / 125))
      (q := (33074156191227 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-105555279920761) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-5321054309823) / 5000000000000) ≤ Real.log (1 - (131 / 200)) :=
    logL (w := (69 / 200)) (c := (69 / 50))
      (q := (3220834991553 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-5321054309823) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (163 / 250) ^ 2) ≤ ((-55356612410887) / 100000000000000) :=
    logU (w := (35931 / 62500)) (c := (35931 / 31250))
      (q := (13958105645107 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-55356612410887) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-3502561582011) / 6250000000000) ≤ Real.log (1 - (131 / 200) ^ 2) :=
    logL (w := (22839 / 40000)) (c := (22839 / 20000))
      (q := (13273732743819 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-3502561582011) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (163 / 250) ≤ x → x ≤ (131 / 200) →
      (160781210146071 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (2014750771903 / 1250000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (163 / 250)) (w := (3 / 1000))
      (r1 := (654740004413 / 1000000000000))
      (r2 := (25963579701 / 7812500000)) (r3 := (148089627 / 31250000))
      (r4 := (72171 / 250000))
      (R := (49856450771 / 25000000000000))
      (NL := (160781210146071 / 100000000000000)) (NU := (2014750771903 / 1250000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (163 / 250)) (b := (131 / 200)) (m := (1307 / 2000))
    (hh := (3 / 2000)) (K := (502565936999 / 5000000000000))
    (bnd := (3398708163569 / 10000000000000000))
    (Lu := ((-8508254918357) / 20000000000000))
    (Ll := ((-8508254918383) / 20000000000000))
    (Ml := ((-105987246036859) / 100000000000000))
    (Nu := ((-27848910345623) / 50000000000000))
    (U1 := ((-105555279920761) / 100000000000000))
    (L1 := ((-5321054309823) / 5000000000000))
    (U2 := ((-55356612410887) / 100000000000000))
    (L2 := ((-3502561582011) / 6250000000000))
    (NL := (160781210146071 / 100000000000000))
    (NU := (2014750771903 / 1250000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_041 {s : ℝ} (hs1 : (131 / 200) ≤ s) (hs2 : s ≤ (329 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (1313 / 2000) ≤ ((-42083258523927) / 100000000000000) :=
    logU (w := (1313 / 2000)) (c := (1313 / 1000))
      (q := (27231459532067 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-42083258523927) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-42083258524089) / 100000000000000) ≤ Real.log (1313 / 2000) :=
    logL (w := (1313 / 2000)) (c := (1313 / 1000))
      (q := (13615729765953 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-42083258524089) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-21371363346627) / 20000000000000) ≤ Real.log (1 - (1313 / 2000)) :=
    logL (w := (687 / 2000)) (c := (687 / 500))
      (q := (6354523875771 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-21371363346627) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1313 / 2000) ^ 2) ≤ ((-56386122456191) / 100000000000000) :=
    logU (w := (2276031 / 4000000)) (c := (2276031 / 2000000))
      (q := (12928595599803 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-56386122456191) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (131 / 200)) ≤ ((-53210543097537) / 50000000000000) :=
    logU (w := (69 / 200)) (c := (69 / 50))
      (q := (16104174958457 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-53210543097537) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-4291778167717) / 4000000000000) ≤ Real.log (1 - (329 / 500)) :=
    logL (w := (171 / 500)) (c := (171 / 125))
      (q := (6266996383813 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-4291778167717) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (131 / 200) ^ 2) ≤ ((-28020492656087) / 50000000000000) :=
    logU (w := (22839 / 40000)) (c := (22839 / 20000))
      (q := (663686637191 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-28020492656087) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-14183312130161) / 25000000000000) ≤ Real.log (1 - (329 / 500) ^ 2) :=
    logL (w := (141759 / 250000)) (c := (141759 / 125000))
      (q := (12581469535351 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-14183312130161) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (131 / 200) ≤ x → x ≤ (329 / 500) →
      (160593773963667 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (80490330763081 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (131 / 200)) (w := (3 / 1000))
      (r1 := (634672055349 / 1000000000000))
      (r2 := (13463893953 / 4000000000)) (r3 := (94715163 / 20000000))
      (r4 := (45927 / 200000))
      (R := (193443781247 / 100000000000000))
      (NL := (160593773963667 / 100000000000000)) (NU := (80490330763081 / 50000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (131 / 200)) (b := (329 / 500)) (m := (1313 / 2000))
    (hh := (3 / 2000)) (K := (9838998459071 / 100000000000000))
    (bnd := (722531449243 / 2500000000000000))
    (Lu := ((-42083258523927) / 100000000000000))
    (Ll := ((-42083258524089) / 100000000000000))
    (Ml := ((-21371363346627) / 20000000000000))
    (Nu := ((-56386122456191) / 100000000000000))
    (U1 := ((-53210543097537) / 50000000000000))
    (L1 := ((-4291778167717) / 4000000000000))
    (U2 := ((-28020492656087) / 50000000000000))
    (L2 := ((-14183312130161) / 25000000000000))
    (NL := (160593773963667 / 100000000000000))
    (NU := (80490330763081 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_042 {s : ℝ} (hs1 : (329 / 500) ≤ s) (hs2 : s ≤ (33 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (659 / 1000) ≤ ((-20851587223981) / 50000000000000) :=
    logU (w := (659 / 1000)) (c := (659 / 500))
      (q := (862860737751 / 3125000000000)) (k := 1) (J := 6)
      (R := ((-20851587223981) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-8340634889631) / 20000000000000) ≤ Real.log (659 / 1000) :=
    logL (w := (659 / 1000)) (c := (659 / 500))
      (q := (172572147549 / 625000000000)) (k := 1) (J := 6)
      (R := ((-8340634889631) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-26896820042681) / 25000000000000) ≤ Real.log (1 - (659 / 1000)) :=
    logL (w := (341 / 1000)) (c := (341 / 250))
      (q := (15521077970633 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-26896820042681) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (659 / 1000) ^ 2) ≤ ((-5696577904903) / 10000000000000) :=
    logU (w := (565719 / 1000000)) (c := (565719 / 500000))
      (q := (3087234751741 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-5696577904903) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (329 / 500)) ≤ ((-2145889083839) / 2000000000000) :=
    logU (w := (171 / 500)) (c := (171 / 125))
      (q := (15667490960019 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-2145889083839) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-26970241534489) / 25000000000000) ≤ Real.log (1 - (33 / 50)) :=
    logL (w := (17 / 50)) (c := (34 / 25))
      (q := (15374234987017 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-26970241534489) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (329 / 500) ^ 2) ≤ ((-28366624260321) / 50000000000000) :=
    logU (w := (141759 / 250000)) (c := (141759 / 125000))
      (q := (1572683691919 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-28366624260321) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-57199205900349) / 100000000000000) ≤ Real.log (1 - (33 / 50) ^ 2) :=
    logL (w := (1411 / 2500)) (c := (1411 / 1250))
      (q := (6057756077823 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-57199205900349) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (329 / 500) ≤ x → x ≤ (33 / 50) →
      (501486316857 / 312500000000) ≤ Npoly x ∧
      Npoly x ≤ (6428963807369 / 4000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (329 / 500)) (w := (1 / 500))
      (r1 := (122869674431 / 200000000000))
      (r2 := (213036498387 / 62500000000)) (r3 := (591669603 / 125000000))
      (r4 := (85293 / 500000))
      (R := (7764805937 / 6250000000000))
      (NL := (501486316857 / 312500000000)) (NU := (6428963807369 / 4000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (329 / 500)) (b := (33 / 50)) (m := (659 / 1000))
    (hh := (1 / 1000)) (K := (1731381690207 / 25000000000000))
    (bnd := (2507024087003 / 10000000000000000))
    (Lu := ((-20851587223981) / 50000000000000))
    (Ll := ((-8340634889631) / 20000000000000))
    (Ml := ((-26896820042681) / 25000000000000))
    (Nu := ((-5696577904903) / 10000000000000))
    (U1 := ((-2145889083839) / 2000000000000))
    (L1 := ((-26970241534489) / 25000000000000))
    (U2 := ((-28366624260321) / 50000000000000))
    (L2 := ((-57199205900349) / 100000000000000))
    (NL := (501486316857 / 312500000000))
    (NU := (6428963807369 / 4000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_043 {s : ℝ} (hs1 : (33 / 50) ≤ s) (hs2 : s ≤ (331 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (661 / 1000) ≤ ((-10350035978261) / 25000000000000) :=
    logU (w := (661 / 1000)) (c := (661 / 500))
      (q := (558291482859 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-10350035978261) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-20700071956633) / 50000000000000) ≤ Real.log (661 / 1000) :=
    logL (w := (661 / 1000)) (c := (661 / 500))
      (q := (27914574142729 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-20700071956633) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-108175517160843) / 100000000000000) ≤ Real.log (1 - (661 / 1000)) :=
    logL (w := (339 / 1000)) (c := (339 / 250))
      (q := (30453918951147 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-108175517160843) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (661 / 1000) ^ 2) ≤ ((-14358383524263) / 25000000000000) :=
    logU (w := (563079 / 1000000)) (c := (563079 / 500000))
      (q := (5940591979471 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-14358383524263) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (33 / 50)) ≤ ((-10788096613719) / 10000000000000) :=
    logU (w := (17 / 50)) (c := (34 / 25))
      (q := (15374234987399 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-10788096613719) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-108470938350507) / 100000000000000) ≤ Real.log (1 - (331 / 500)) :=
    logL (w := (169 / 500)) (c := (169 / 125))
      (q := (30158497761483 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-108470938350507) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (33 / 50) ^ 2) ≤ ((-57199205900347) / 100000000000000) :=
    logU (w := (1411 / 2500)) (c := (1411 / 1250))
      (q := (12115512155647 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-57199205900347) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-57668768706587) / 100000000000000) ≤ Real.log (1 - (331 / 500) ^ 2) :=
    logL (w := (140439 / 250000)) (c := (140439 / 125000))
      (q := (363935917169 / 3125000000000)) (k := 1) (J := 6)
      (R := ((-57668768706587) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (33 / 50) ≤ x → x ≤ (331 / 500) →
      (32071369161703 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (160599865861117 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (33 / 50)) (w := (1 / 500))
      (r1 := (3754107757 / 6250000000))
      (r2 := (214811271 / 62500000)) (r3 := (5915187 / 1250000))
      (r4 := (6561 / 50000))
      (R := (121510026301 / 100000000000000))
      (NL := (32071369161703 / 20000000000000)) (NU := (160599865861117 / 100000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (33 / 50)) (b := (331 / 500)) (m := (661 / 1000))
    (hh := (1 / 1000)) (K := (679484090557 / 10000000000000))
    (bnd := (278360871773 / 1250000000000000))
    (Lu := ((-10350035978261) / 25000000000000))
    (Ll := ((-20700071956633) / 50000000000000))
    (Ml := ((-108175517160843) / 100000000000000))
    (Nu := ((-14358383524263) / 25000000000000))
    (U1 := ((-10788096613719) / 10000000000000))
    (L1 := ((-108470938350507) / 100000000000000))
    (U2 := ((-57199205900347) / 100000000000000))
    (L2 := ((-57668768706587) / 100000000000000))
    (NL := (32071369161703 / 20000000000000))
    (NU := (160599865861117 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_044 {s : ℝ} (hs1 : (331 / 500) ≤ s) (hs2 : s ≤ (83 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (663 / 1000) ≤ ((-20549014439813) / 50000000000000) :=
    logU (w := (663 / 1000)) (c := (663 / 500))
      (q := (1763543073523 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-20549014439813) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-41098028879881) / 100000000000000) ≤ Real.log (663 / 1000) :=
    logL (w := (663 / 1000)) (c := (663 / 500))
      (q := (14108344588057 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-41098028879881) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-54383617431751) / 50000000000000) ≤ Real.log (1 - (663 / 1000)) :=
    logL (w := (337 / 1000)) (c := (337 / 250))
      (q := (3732775156061 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-54383617431751) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (663 / 1000) ^ 2) ≤ ((-57904914841897) / 100000000000000) :=
    logU (w := (560431 / 1000000)) (c := (560431 / 500000))
      (q := (11409803214097 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-57904914841897) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (331 / 500)) ≤ ((-108470938349909) / 100000000000000) :=
    logU (w := (169 / 500)) (c := (169 / 125))
      (q := (30158497762079 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-108470938349909) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-21812882380471) / 20000000000000) ≤ Real.log (1 - (83 / 125)) :=
    logL (w := (42 / 125)) (c := (168 / 125))
      (q := (5913004841927 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-21812882380471) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (331 / 500) ^ 2) ≤ ((-11533753741317) / 20000000000000) :=
    logU (w := (140439 / 250000)) (c := (140439 / 125000))
      (q := (11645949349409 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-11533753741317) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-58141977661993) / 100000000000000) ≤ Real.log (1 - (83 / 125) ^ 2) :=
    logL (w := (8736 / 15625)) (c := (17472 / 15625))
      (q := (5586370197001 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-58141977661993) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (331 / 500) ≤ x → x ≤ (83 / 125) →
      (160240842523349 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (40119590851287 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (331 / 500)) (w := (1 / 500))
      (r1 := (117370507573 / 200000000000))
      (r2 := (216585649953 / 62500000000)) (r3 := (591407163 / 125000000))
      (r4 := (45927 / 500000))
      (R := (118760440899 / 100000000000000))
      (NL := (160240842523349 / 100000000000000)) (NU := (40119590851287 / 25000000000000))
      (by norm_num) hx1 (by linarith)
      (abs_le.mpr ⟨by simp only [NpolyD1]; norm_num,
        by simp only [NpolyD1]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD2]; norm_num,
        by simp only [NpolyD2]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD3]; norm_num,
        by simp only [NpolyD3]; norm_num⟩)
      (abs_le.mpr ⟨by simp only [NpolyD4]; norm_num,
        by simp only [NpolyD4]; norm_num⟩)
      (by norm_num) (by simp only [Npoly]; norm_num)
      (by simp only [Npoly]; norm_num)
  exact Dfun_box_pos (a := (331 / 500)) (b := (83 / 125)) (m := (663 / 1000))
    (hh := (1 / 1000)) (K := (6665512870497 / 100000000000000))
    (bnd := (123120623859 / 625000000000000))
    (Lu := ((-20549014439813) / 50000000000000))
    (Ll := ((-41098028879881) / 100000000000000))
    (Ml := ((-54383617431751) / 50000000000000))
    (Nu := ((-57904914841897) / 100000000000000))
    (U1 := ((-108470938349909) / 100000000000000))
    (L1 := ((-21812882380471) / 20000000000000))
    (U2 := ((-11533753741317) / 20000000000000))
    (L2 := ((-58141977661993) / 100000000000000))
    (NL := (160240842523349 / 100000000000000))
    (NU := (40119590851287 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2


end EntropyBound.Diagonal

end
