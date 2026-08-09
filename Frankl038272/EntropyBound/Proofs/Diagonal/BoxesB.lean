/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Proofs.Diagonal.Deriv

/-!
# Stage G item G4 — box certificates for `diagonal_middle`, part B

Machine-generated per-box positivity certificates, boxes 45–89 of the partition of
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


theorem box_045 {s : ℝ} (hs1 : (83 / 125) ≤ s) (hs2 : s ≤ (333 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (133 / 200) ≤ ((-40796823832627) / 100000000000000) :=
    logU (w := (133 / 200)) (c := (133 / 100))
      (q := (28517894223367 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-40796823832627) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-40796823832919) / 100000000000000) ≤ Real.log (133 / 200) :=
    logL (w := (133 / 200)) (c := (133 / 100))
      (q := (7129473555769 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-40796823832919) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-6835154669757) / 6250000000000) ≤ Real.log (1 - (133 / 200)) :=
    logL (w := (67 / 200)) (c := (67 / 50))
      (q := (14633480697939 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-6835154669757) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (133 / 200) ^ 2) ≤ ((-11675992474493) / 20000000000000) :=
    logU (w := (22311 / 40000)) (c := (22311 / 20000))
      (q := (10934755683529 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-11675992474493) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (83 / 125)) ≤ ((-109064411901891) / 100000000000000) :=
    logU (w := (42 / 125)) (c := (168 / 125))
      (q := (29565024210097 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-109064411901891) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-109661428600899) / 100000000000000) ≤ Real.log (1 - (333 / 500)) :=
    logL (w := (167 / 500)) (c := (167 / 125))
      (q := (28968007511091 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-109661428600899) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (83 / 125) ^ 2) ≤ ((-58141977661991) / 100000000000000) :=
    logU (w := (8736 / 15625)) (c := (17472 / 15625))
      (q := (11172740394003 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-58141977661991) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-366367963913) / 625000000000) ≤ Real.log (1 - (333 / 500) ^ 2) :=
    logL (w := (139111 / 250000)) (c := (139111 / 125000))
      (q := (2139168765983 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-366367963913) / 625000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (83 / 125) ≤ x → x ≤ (333 / 500) →
      (160127634245883 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (16035961053353 / 10000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (83 / 125)) (w := (1 / 500))
      (r1 := (114586856761 / 200000000000))
      (r2 := (1705935573 / 488281250)) (r3 := (36958437 / 7812500))
      (r4 := (6561 / 125000))
      (R := (115988143823 / 100000000000000))
      (NL := (160127634245883 / 100000000000000)) (NU := (16035961053353 / 10000000000000))
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
  exact Dfun_box_pos (a := (83 / 125)) (b := (333 / 500)) (m := (133 / 200))
    (hh := (1 / 1000)) (K := (3268772274193 / 50000000000000))
    (bnd := (1735933808353 / 10000000000000000))
    (Lu := ((-40796823832627) / 100000000000000))
    (Ll := ((-40796823832919) / 100000000000000))
    (Ml := ((-6835154669757) / 6250000000000))
    (Nu := ((-11675992474493) / 20000000000000))
    (U1 := ((-109064411901891) / 100000000000000))
    (L1 := ((-109661428600899) / 100000000000000))
    (U2 := ((-58141977661991) / 100000000000000))
    (L2 := ((-366367963913) / 625000000000))
    (NL := (160127634245883 / 100000000000000))
    (NU := (16035961053353 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_046 {s : ℝ} (hs1 : (333 / 500) ≤ s) (hs2 : s ≤ (167 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (667 / 1000) ≤ ((-809930466133) / 2000000000000) :=
    logU (w := (667 / 1000)) (c := (667 / 500))
      (q := (900568585917 / 3125000000000)) (k := 1) (J := 6)
      (R := ((-809930466133) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-40496523306983) / 100000000000000) ≤ Real.log (667 / 1000) :=
    logL (w := (667 / 1000)) (c := (667 / 500))
      (q := (7204548687253 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-40496523306983) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-85907249141) / 78125000000) ≤ Real.log (1 - (667 / 1000)) :=
    logL (w := (333 / 1000)) (c := (333 / 250))
      (q := (2866815721151 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-85907249141) / 78125000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (667 / 1000) ^ 2) ≤ ((-58858718523303) / 100000000000000) :=
    logU (w := (555111 / 1000000)) (c := (555111 / 500000))
      (q := (10455999532691 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-58858718523303) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (333 / 500)) ≤ ((-54830714300271) / 50000000000000) :=
    logU (w := (167 / 500)) (c := (167 / 125))
      (q := (14484003755723 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-54830714300271) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-110262031006837) / 100000000000000) ≤ Real.log (1 - (167 / 250)) :=
    logL (w := (83 / 250)) (c := (166 / 125))
      (q := (28367405105153 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-110262031006837) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (333 / 500) ^ 2) ≤ ((-29309437113039) / 50000000000000) :=
    logU (w := (139111 / 250000)) (c := (139111 / 125000))
      (q := (2673960957479 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-29309437113039) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-5909950061291) / 10000000000000) ≤ Real.log (1 - (167 / 250) ^ 2) :=
    logL (w := (34611 / 62500)) (c := (34611 / 31250))
      (q := (2043043488617 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-5909950061291) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (333 / 500) ≤ x → x ≤ (167 / 250) →
      (40004310920309 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (160243629958443 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (333 / 500)) (w := (1 / 500))
      (r1 := (558902492797 / 1000000000000))
      (r2 := (220133699271 / 62500000000)) (r3 := (591302187 / 125000000))
      (r4 := (6561 / 500000))
      (R := (113193138603 / 100000000000000))
      (NL := (40004310920309 / 25000000000000)) (NU := (160243629958443 / 100000000000000))
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
  exact Dfun_box_pos (a := (333 / 500)) (b := (167 / 250)) (m := (667 / 1000))
    (hh := (1 / 1000)) (K := (6410937981791 / 100000000000000))
    (bnd := (1524678629699 / 10000000000000000))
    (Lu := ((-809930466133) / 2000000000000))
    (Ll := ((-40496523306983) / 100000000000000))
    (Ml := ((-85907249141) / 78125000000))
    (Nu := ((-58858718523303) / 100000000000000))
    (U1 := ((-54830714300271) / 50000000000000))
    (L1 := ((-110262031006837) / 100000000000000))
    (U2 := ((-29309437113039) / 50000000000000))
    (L2 := ((-5909950061291) / 10000000000000))
    (NL := (40004310920309 / 25000000000000))
    (NU := (160243629958443 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_047 {s : ℝ} (hs1 : (167 / 250) ≤ s) (hs2 : s ≤ (67 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (669 / 1000) ≤ ((-40197121885389) / 100000000000000) :=
    logU (w := (669 / 1000)) (c := (669 / 500))
      (q := (5823519234121 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-40197121885389) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4019712188577) / 10000000000000) ≤ Real.log (669 / 1000) :=
    logL (w := (669 / 1000)) (c := (669 / 500))
      (q := (1164703846809 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-4019712188577) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-13820461295093) / 12500000000000) ≤ Real.log (1 - (669 / 1000)) :=
    logL (w := (331 / 1000)) (c := (331 / 250))
      (q := (14032872875623 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-13820461295093) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (669 / 1000) ^ 2) ≤ ((-59341225892537) / 100000000000000) :=
    logU (w := (552439 / 1000000)) (c := (552439 / 500000))
      (q := (9973492163457 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-59341225892537) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (167 / 250)) ≤ ((-110262031006563) / 100000000000000) :=
    logU (w := (83 / 250)) (c := (166 / 125))
      (q := (1134696204217 / 4000000000000)) (k := 2) (J := 6)
      (R := ((-110262031006563) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-110866262452367) / 100000000000000) ≤ Real.log (1 - (67 / 100)) :=
    logL (w := (33 / 100)) (c := (33 / 25))
      (q := (27763173659623 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-110866262452367) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (167 / 250) ^ 2) ≤ ((-14774875153227) / 25000000000000) :=
    logU (w := (34611 / 62500)) (c := (34611 / 31250))
      (q := (5107608721543 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-14774875153227) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-3723993738081) / 6250000000000) ≤ Real.log (1 - (67 / 100) ^ 2) :=
    logL (w := (5511 / 10000)) (c := (5511 / 5000))
      (q := (9730818246699 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-3723993738081) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (167 / 250) ≤ x → x ≤ (67 / 100) →
      (31981938706789 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (80065222194309 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (167 / 250)) (w := (1 / 500))
      (r1 := (272378585569 / 500000000000))
      (r2 := (27738450729 / 7812500000)) (r3 := (147827187 / 31250000))
      (r4 := (6561 / 250000))
      (R := (13796928417 / 12500000000000))
      (NL := (31981938706789 / 20000000000000)) (NU := (80065222194309 / 50000000000000))
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
  exact Dfun_box_pos (a := (167 / 250)) (b := (67 / 100)) (m := (669 / 1000))
    (hh := (1 / 1000)) (K := (3142847682133 / 50000000000000))
    (bnd := (1335944081677 / 10000000000000000))
    (Lu := ((-40197121885389) / 100000000000000))
    (Ll := ((-4019712188577) / 10000000000000))
    (Ml := ((-13820461295093) / 12500000000000))
    (Nu := ((-59341225892537) / 100000000000000))
    (U1 := ((-110262031006563) / 100000000000000))
    (L1 := ((-110866262452367) / 100000000000000))
    (U2 := ((-14774875153227) / 25000000000000))
    (L2 := ((-3723993738081) / 6250000000000))
    (NL := (31981938706789 / 20000000000000))
    (NU := (80065222194309 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_048 {s : ℝ} (hs1 : (67 / 100) ≤ s) (hs2 : s ≤ (84 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (671 / 1000) ≤ ((-9974653550261) / 25000000000000) :=
    logU (w := (671 / 1000)) (c := (671 / 500))
      (q := (588322077099 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-9974653550261) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-19949307100739) / 50000000000000) ≤ Real.log (671 / 1000) :=
    logL (w := (671 / 1000)) (c := (671 / 500))
      (q := (29416103854517 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-19949307100739) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-3474054775683) / 3125000000000) ≤ Real.log (1 - (671 / 1000)) :=
    logL (w := (329 / 1000)) (c := (329 / 250))
      (q := (13729841645067 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-3474054775683) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (671 / 1000) ^ 2) ≤ ((-1196550557207) / 2000000000000) :=
    logU (w := (549759 / 1000000)) (c := (549759 / 500000))
      (q := (2371797548911 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-1196550557207) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (67 / 100)) ≤ ((-110866262452159) / 100000000000000) :=
    logU (w := (33 / 100)) (c := (33 / 25))
      (q := (27763173659829 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-110866262452159) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-22294833411991) / 20000000000000) ≤ Real.log (1 - (84 / 125)) :=
    logL (w := (41 / 125)) (c := (164 / 125))
      (q := (5431053810407 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-22294833411991) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (67 / 100) ^ 2) ≤ ((-29791949904647) / 50000000000000) :=
    logU (w := (5511 / 10000)) (c := (5511 / 5000))
      (q := (97308182467 / 1000000000000)) (k := 1) (J := 6)
      (R := ((-29791949904647) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-60072115593549) / 100000000000000) ≤ Real.log (1 - (84 / 125) ^ 2) :=
    logL (w := (8569 / 15625)) (c := (17138 / 15625))
      (q := (4621301231223 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-60072115593549) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (67 / 100) ≤ x → x ≤ (84 / 125) →
      (159805006509677 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (160020076530647 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (67 / 100)) (w := (1 / 500))
      (r1 := (53049831757 / 100000000000))
      (r2 := (1789452729 / 500000000)) (r3 := (23654187 / 5000000))
      (r4 := (6561 / 100000))
      (R := (21507002097 / 20000000000000))
      (NL := (159805006509677 / 100000000000000)) (NU := (160020076530647 / 100000000000000))
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
  exact Dfun_box_pos (a := (67 / 100)) (b := (84 / 125)) (m := (671 / 1000))
    (hh := (1 / 1000)) (K := (1540454760389 / 25000000000000))
    (bnd := (584754622537 / 5000000000000000))
    (Lu := ((-9974653550261) / 25000000000000))
    (Ll := ((-19949307100739) / 50000000000000))
    (Ml := ((-3474054775683) / 3125000000000))
    (Nu := ((-1196550557207) / 2000000000000))
    (U1 := ((-110866262452159) / 100000000000000))
    (L1 := ((-22294833411991) / 20000000000000))
    (U2 := ((-29791949904647) / 50000000000000))
    (L2 := ((-60072115593549) / 100000000000000))
    (NL := (159805006509677 / 100000000000000))
    (NU := (160020076530647 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_049 {s : ℝ} (hs1 : (84 / 125) ≤ s) (hs2 : s ≤ (337 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (673 / 1000) ≤ ((-39600994933739) / 100000000000000) :=
    logU (w := (673 / 1000)) (c := (673 / 500))
      (q := (5942744624451 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-39600994933739) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-39600994934233) / 100000000000000) ≤ Real.log (673 / 1000) :=
    logL (w := (673 / 1000)) (c := (673 / 500))
      (q := (14856861560881 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-39600994934233) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-111779510808623) / 100000000000000) ≤ Real.log (1 - (673 / 1000)) :=
    logL (w := (327 / 1000)) (c := (327 / 250))
      (q := (26849925303367 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-111779510808623) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (673 / 1000) ^ 2) ≤ ((-60317668608019) / 100000000000000) :=
    logU (w := (547071 / 1000000)) (c := (547071 / 500000))
      (q := (359881977919 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-60317668608019) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (84 / 125)) ≤ ((-55737083529899) / 50000000000000) :=
    logU (w := (41 / 125)) (c := (164 / 125))
      (q := (2715526905219 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-55737083529899) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-112085789761659) / 100000000000000) ≤ Real.log (1 - (337 / 500)) :=
    logL (w := (163 / 500)) (c := (163 / 125))
      (q := (26543646350331 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-112085789761659) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (84 / 125) ^ 2) ≤ ((-60072115593547) / 100000000000000) :=
    logU (w := (8569 / 15625)) (c := (17138 / 15625))
      (q := (9242602462447 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-60072115593547) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-946315508669) / 1562500000000) ≤ Real.log (1 - (337 / 500) ^ 2) :=
    logL (w := (136431 / 250000)) (c := (136431 / 125000))
      (q := (8750525501179 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-946315508669) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (84 / 125) ≤ x → x ≤ (337 / 500) →
      (159703205316617 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (7995627454531 / 5000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (84 / 125)) (w := (1 / 500))
      (r1 := (20645036931 / 40000000000))
      (r2 := (3522746457 / 976562500)) (r3 := (18482499 / 3906250))
      (r4 := (6561 / 62500))
      (R := (104671887001 / 100000000000000))
      (NL := (159703205316617 / 100000000000000)) (NU := (7995627454531 / 5000000000000))
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
  exact Dfun_box_pos (a := (84 / 125)) (b := (337 / 500)) (m := (673 / 1000))
    (hh := (1 / 1000)) (K := (1509827878277 / 25000000000000))
    (bnd := (1025152627173 / 10000000000000000))
    (Lu := ((-39600994933739) / 100000000000000))
    (Ll := ((-39600994934233) / 100000000000000))
    (Ml := ((-111779510808623) / 100000000000000))
    (Nu := ((-60317668608019) / 100000000000000))
    (U1 := ((-55737083529899) / 50000000000000))
    (L1 := ((-112085789761659) / 100000000000000))
    (U2 := ((-60072115593547) / 100000000000000))
    (L2 := ((-946315508669) / 1562500000000))
    (NL := (159703205316617 / 100000000000000))
    (NU := (7995627454531 / 5000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_050 {s : ℝ} (hs1 : (337 / 500) ≤ s) (hs2 : s ≤ (27 / 40)) :
    0 < Dfun s := by
  have hLu : Real.log (1349 / 2000) ≤ ((-39378360333431) / 100000000000000) :=
    logU (w := (1349 / 2000)) (c := (1349 / 1000))
      (q := (29936357722563 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-39378360333431) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-19689180166987) / 50000000000000) ≤ Real.log (1349 / 2000) :=
    logL (w := (1349 / 2000)) (c := (1349 / 1000))
      (q := (29936357722021 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-19689180166987) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-112239281733459) / 100000000000000) ≤ Real.log (1 - (1349 / 2000)) :=
    logL (w := (651 / 2000)) (c := (651 / 500))
      (q := (26390154378531 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-112239281733459) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1349 / 2000) ^ 2) ≤ ((-30343910204069) / 50000000000000) :=
    logU (w := (2180199 / 4000000)) (c := (2180199 / 2000000))
      (q := (539181102991 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-30343910204069) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (337 / 500)) ≤ ((-112085789761541) / 100000000000000) :=
    logU (w := (163 / 500)) (c := (163 / 125))
      (q := (26543646350447 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-112085789761541) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-5619650483267) / 5000000000000) ≤ Real.log (1 - (27 / 40)) :=
    logL (w := (13 / 40)) (c := (13 / 10))
      (q := (524728528933 / 2000000000000)) (k := 2) (J := 6)
      (R := ((-5619650483267) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (337 / 500) ^ 2) ≤ ((-30282096277407) / 50000000000000) :=
    logU (w := (136431 / 250000)) (c := (136431 / 125000))
      (q := (437526275059 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-30282096277407) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-30405846568769) / 50000000000000) ≤ Real.log (1 - (27 / 40) ^ 2) :=
    logL (w := (871 / 1600)) (c := (871 / 800))
      (q := (8503024918457 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-30405846568769) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (337 / 500) ≤ x → x ≤ (27 / 40) →
      (159655570682421 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (39939156690049 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (337 / 500)) (w := (1 / 1000))
      (r1 := (125409992969 / 250000000000))
      (r2 := (227230270299 / 62500000000)) (r3 := (591564627 / 125000000))
      (r4 := (72171 / 500000))
      (R := (50528038887 / 100000000000000))
      (NL := (159655570682421 / 100000000000000)) (NU := (39939156690049 / 25000000000000))
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
  exact Dfun_box_pos (a := (337 / 500)) (b := (27 / 40)) (m := (1349 / 2000))
    (hh := (1 / 2000)) (K := (652990185151 / 20000000000000))
    (bnd := (931240420829 / 10000000000000000))
    (Lu := ((-39378360333431) / 100000000000000))
    (Ll := ((-19689180166987) / 50000000000000))
    (Ml := ((-112239281733459) / 100000000000000))
    (Nu := ((-30343910204069) / 50000000000000))
    (U1 := ((-112085789761541) / 100000000000000))
    (L1 := ((-5619650483267) / 5000000000000))
    (U2 := ((-30282096277407) / 50000000000000))
    (L2 := ((-30405846568769) / 50000000000000))
    (NL := (159655570682421 / 100000000000000))
    (NU := (39939156690049 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_051 {s : ℝ} (hs1 : (27 / 40) ≤ s) (hs2 : s ≤ (169 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (1351 / 2000) ≤ ((-19615106079093) / 50000000000000) :=
    logU (w := (1351 / 2000)) (c := (1351 / 1000))
      (q := (1880281618613 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-19615106079093) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-7846042431753) / 20000000000000) ≤ Real.log (1351 / 2000) :=
    logL (w := (1351 / 2000)) (c := (1351 / 1000))
      (q := (3008450589723 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-7846042431753) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-28136743570973) / 25000000000000) ≤ Real.log (1 - (1351 / 2000)) :=
    logL (w := (649 / 2000)) (c := (649 / 500))
      (q := (13041230914049 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-28136743570973) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1351 / 2000) ^ 2) ≤ ((-2437432458571) / 4000000000000) :=
    logU (w := (2174799 / 4000000)) (c := (2174799 / 2000000))
      (q := (8378906591719 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2437432458571) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (27 / 40)) ≤ ((-56196504832619) / 50000000000000) :=
    logU (w := (13 / 40)) (c := (13 / 10))
      (q := (104945705787 / 400000000000)) (k := 2) (J := 6)
      (R := ((-56196504832619) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-112701176319067) / 100000000000000) ≤ Real.log (1 - (169 / 250)) :=
    logL (w := (81 / 250)) (c := (162 / 125))
      (q := (25928259792923 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-112701176319067) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (27 / 40) ^ 2) ≤ ((-475091352637) / 781250000000) :=
    logU (w := (871 / 1600)) (c := (871 / 800))
      (q := (4251512459229 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-475091352637) / 781250000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-61060176112993) / 100000000000000) ≤ Real.log (1 - (169 / 250) ^ 2) :=
    logL (w := (33939 / 62500)) (c := (33939 / 31250))
      (q := (4127270971501 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-61060176112993) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (27 / 40) ≤ x → x ≤ (169 / 250) →
      (159606497863703 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79853049833969 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (27 / 40)) (w := (1 / 1000))
      (r1 := (494354405079 / 1000000000000))
      (r2 := (116796249 / 32000000)) (r3 := (3786507 / 800000))
      (r4 := (6561 / 40000))
      (R := (49800902117 / 100000000000000))
      (NL := (159606497863703 / 100000000000000)) (NU := (79853049833969 / 50000000000000))
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
  exact Dfun_box_pos (a := (27 / 40)) (b := (169 / 250)) (m := (1351 / 2000))
    (hh := (1 / 2000)) (K := (1603900016993 / 50000000000000))
    (bnd := (8754159629 / 100000000000000))
    (Lu := ((-19615106079093) / 50000000000000))
    (Ll := ((-7846042431753) / 20000000000000))
    (Ml := ((-28136743570973) / 25000000000000))
    (Nu := ((-2437432458571) / 4000000000000))
    (U1 := ((-56196504832619) / 50000000000000))
    (L1 := ((-112701176319067) / 100000000000000))
    (U2 := ((-475091352637) / 781250000000))
    (L2 := ((-61060176112993) / 100000000000000))
    (NL := (159606497863703 / 100000000000000))
    (NU := (79853049833969 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_052 {s : ℝ} (hs1 : (169 / 250) ≤ s) (hs2 : s ≤ (677 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1353 / 2000) ≤ ((-39082283137127) / 100000000000000) :=
    logU (w := (1353 / 2000)) (c := (1353 / 1000))
      (q := (30232434918867 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-39082283137127) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-39082283137743) / 100000000000000) ≤ Real.log (1353 / 2000) :=
    logL (w := (1353 / 2000)) (c := (1353 / 1000))
      (q := (7558108729563 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-39082283137743) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-56427808252099) / 50000000000000) ≤ Real.log (1 - (1353 / 2000)) :=
    logL (w := (647 / 2000)) (c := (647 / 500))
      (q := (1610863725487 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-56427808252099) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1353 / 2000) ^ 2) ≤ ((-61184787811703) / 100000000000000) :=
    logU (w := (2169391 / 4000000)) (c := (2169391 / 2000000))
      (q := (8129930244291 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-61184787811703) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (169 / 250)) ≤ ((-112701176318979) / 100000000000000) :=
    logU (w := (81 / 250)) (c := (162 / 125))
      (q := (25928259793009 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-112701176318979) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-56505147788011) / 50000000000000) ≤ Real.log (1 - (677 / 1000)) :=
    logL (w := (323 / 1000)) (c := (323 / 250))
      (q := (800598141749 / 3125000000000)) (k := 2) (J := 6)
      (R := ((-56505147788011) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (169 / 250) ^ 2) ≤ ((-61060176112991) / 100000000000000) :=
    logU (w := (33939 / 62500)) (c := (33939 / 31250))
      (q := (8254541943003 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-61060176112991) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-30654823645921) / 50000000000000) ≤ Real.log (1 - (677 / 1000) ^ 2) :=
    logL (w := (541671 / 1000000)) (c := (541671 / 500000))
      (q := (8005070764153 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-30654823645921) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (169 / 250) ≤ x → x ≤ (677 / 1000) →
      (159558157861253 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (39914074928147 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (169 / 250)) (w := (1 / 1000))
      (r1 := (487040439439 / 1000000000000))
      (r2 := (28625650047 / 7812500000)) (r3 := (147932163 / 31250000))
      (r4 := (45927 / 250000))
      (R := (49070925667 / 100000000000000))
      (NL := (159558157861253 / 100000000000000)) (NU := (39914074928147 / 25000000000000))
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
  exact Dfun_box_pos (a := (169 / 250)) (b := (677 / 1000)) (m := (1353 / 2000))
    (hh := (1 / 2000)) (K := (3150960448723 / 100000000000000))
    (bnd := (51561620883 / 625000000000000))
    (Lu := ((-39082283137127) / 100000000000000))
    (Ll := ((-39082283137743) / 100000000000000))
    (Ml := ((-56427808252099) / 50000000000000))
    (Nu := ((-61184787811703) / 100000000000000))
    (U1 := ((-112701176318979) / 100000000000000))
    (L1 := ((-56505147788011) / 50000000000000))
    (U2 := ((-61060176112991) / 100000000000000))
    (L2 := ((-30654823645921) / 50000000000000))
    (NL := (159558157861253 / 100000000000000))
    (NU := (39914074928147 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_053 {s : ℝ} (hs1 : (677 / 1000) ≤ s) (hs2 : s ≤ (339 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (271 / 400) ≤ ((-19467286311413) / 50000000000000) :=
    logU (w := (271 / 400)) (c := (271 / 200))
      (q := (1898759089573 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-19467286311413) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-38934572623481) / 100000000000000) ≤ Real.log (271 / 400) :=
    logL (w := (271 / 400)) (c := (271 / 200))
      (q := (15190072716257 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-38934572623481) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-1131652142747) / 1000000000000) ≤ Real.log (1 - (271 / 400)) :=
    logL (w := (129 / 400)) (c := (129 / 100))
      (q := (2546422183729 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-1131652142747) / 1000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (271 / 400) ^ 2) ≤ ((-3071737764413) / 5000000000000) :=
    logU (w := (86559 / 160000)) (c := (86559 / 80000))
      (q := (3939981383867 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-3071737764413) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (677 / 1000)) ≤ ((-56505147787973) / 50000000000000) :=
    logU (w := (323 / 1000)) (c := (323 / 250))
      (q := (12809570268021 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-56505147787973) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-113320373343837) / 100000000000000) ≤ Real.log (1 - (339 / 500)) :=
    logL (w := (161 / 500)) (c := (161 / 125))
      (q := (25309062768153 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-113320373343837) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (677 / 1000) ^ 2) ≤ ((-191592647787) / 312500000000) :=
    logU (w := (541671 / 1000000)) (c := (541671 / 500000))
      (q := (4002535382077 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-191592647787) / 312500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-7695014067409) / 12500000000000) ≤ Real.log (1 - (339 / 500) ^ 2) :=
    logL (w := (135079 / 250000)) (c := (135079 / 125000))
      (q := (7754605516723 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-7695014067409) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (677 / 1000) ≤ x → x ≤ (339 / 500) →
      (31902110703111 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (39901807433461 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (677 / 1000)) (w := (1 / 1000))
      (r1 := (95939614157 / 200000000000))
      (r2 := (1839142917639 / 500000000000)) (r3 := (2367301707 / 500000000))
      (r4 := (203391 / 1000000))
      (R := (6042263643 / 12500000000000))
      (NL := (31902110703111 / 20000000000000)) (NU := (39901807433461 / 25000000000000))
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
  exact Dfun_box_pos (a := (677 / 1000)) (b := (339 / 500)) (m := (271 / 400))
    (hh := (1 / 2000)) (K := (154721627689 / 5000000000000))
    (bnd := (779922419863 / 10000000000000000))
    (Lu := ((-19467286311413) / 50000000000000))
    (Ll := ((-38934572623481) / 100000000000000))
    (Ml := ((-1131652142747) / 1000000000000))
    (Nu := ((-3071737764413) / 5000000000000))
    (U1 := ((-56505147787973) / 50000000000000))
    (L1 := ((-113320373343837) / 100000000000000))
    (U2 := ((-191592647787) / 312500000000))
    (L2 := ((-7695014067409) / 12500000000000))
    (NL := (31902110703111 / 20000000000000))
    (NU := (39901807433461 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_054 {s : ℝ} (hs1 : (339 / 500) ≤ s) (hs2 : s ≤ (679 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1357 / 2000) ≤ ((-38787079970719) / 100000000000000) :=
    logU (w := (1357 / 2000)) (c := (1357 / 1000))
      (q := (1221105523411 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-38787079970719) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-38787079971417) / 100000000000000) ≤ Real.log (1357 / 2000) :=
    logL (w := (1357 / 2000)) (c := (1357 / 1000))
      (q := (15263819042289 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-38787079971417) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-22695154706101) / 20000000000000) ≤ Real.log (1 - (1357 / 2000)) :=
    logL (w := (643 / 2000)) (c := (643 / 500))
      (q := (5030732516297 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-22695154706101) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1357 / 2000) ^ 2) ≤ ((-1233714395733) / 2000000000000) :=
    logU (w := (2158551 / 4000000)) (c := (2158551 / 2000000))
      (q := (238406195917 / 3125000000000)) (k := 1) (J := 6)
      (R := ((-1233714395733) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (339 / 500)) ≤ ((-113320373343771) / 100000000000000) :=
    logU (w := (161 / 500)) (c := (161 / 125))
      (q := (25309062768217 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-113320373343771) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-113631415585267) / 100000000000000) ≤ Real.log (1 - (679 / 1000)) :=
    logL (w := (321 / 1000)) (c := (321 / 250))
      (q := (24998020526723 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-113631415585267) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (339 / 500) ^ 2) ≤ ((-6156011253927) / 10000000000000) :=
    logU (w := (135079 / 250000)) (c := (135079 / 125000))
      (q := (1938651379181 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-6156011253927) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-61811577775673) / 100000000000000) ≤ Real.log (1 - (679 / 1000) ^ 2) :=
    logL (w := (538959 / 1000000)) (c := (538959 / 500000))
      (q := (3751570140161 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-61811577775673) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (339 / 500) ≤ x → x ≤ (679 / 1000) →
      (159463687667579 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (9972430785737 / 6250000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (339 / 500)) (w := (1 / 1000))
      (r1 := (472327294471 / 1000000000000))
      (r2 := (230780681577 / 62500000000)) (r3 := (591932043 / 125000000))
      (r4 := (111537 / 500000))
      (R := (23801226053 / 50000000000000))
      (NL := (159463687667579 / 100000000000000)) (NU := (9972430785737 / 6250000000000))
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
  exact Dfun_box_pos (a := (339 / 500)) (b := (679 / 1000)) (m := (1357 / 2000))
    (hh := (1 / 2000)) (K := (189888546297 / 6250000000000))
    (bnd := (185049366497 / 2500000000000000))
    (Lu := ((-38787079970719) / 100000000000000))
    (Ll := ((-38787079971417) / 100000000000000))
    (Ml := ((-22695154706101) / 20000000000000))
    (Nu := ((-1233714395733) / 2000000000000))
    (U1 := ((-113320373343771) / 100000000000000))
    (L1 := ((-113631415585267) / 100000000000000))
    (U2 := ((-6156011253927) / 10000000000000))
    (L2 := ((-61811577775673) / 100000000000000))
    (NL := (159463687667579 / 100000000000000))
    (NU := (9972430785737 / 6250000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_055 {s : ℝ} (hs1 : (679 / 1000) ≤ s) (hs2 : s ≤ (17 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (1359 / 2000) ≤ ((-9659951134773) / 25000000000000) :=
    logU (w := (1359 / 2000)) (c := (1359 / 1000))
      (q := (15337456758451 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-9659951134773) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-38639804539833) / 100000000000000) ≤ Real.log (1359 / 2000) :=
    logL (w := (1359 / 2000)) (c := (1359 / 1000))
      (q := (15337456758081 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-38639804539833) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-7111706266387) / 6250000000000) ≤ Real.log (1 - (1359 / 2000)) :=
    logL (w := (641 / 2000)) (c := (641 / 500))
      (q := (12421067924899 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-7111706266387) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1359 / 2000) ^ 2) ≤ ((-61937687255119) / 100000000000000) :=
    logU (w := (2153119 / 4000000)) (c := (2153119 / 2000000))
      (q := (59016246407 / 800000000000)) (k := 1) (J := 6)
      (R := ((-61937687255119) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (679 / 1000)) ≤ ((-113631415585211) / 100000000000000) :=
    logU (w := (321 / 1000)) (c := (321 / 250))
      (q := (24998020526777 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-113631415585211) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-113943428318883) / 100000000000000) ≤ Real.log (1 - (17 / 25)) :=
    logL (w := (8 / 25)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-113943428318883) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (679 / 1000) ^ 2) ≤ ((-61811577775671) / 100000000000000) :=
    logU (w := (538959 / 1000000)) (c := (538959 / 500000))
      (q := (7503140280323 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-61811577775671) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-62064048977321) / 100000000000000) ≤ Real.log (1 - (17 / 25) ^ 2) :=
    logL (w := (336 / 625)) (c := (672 / 625))
      (q := (3625334539337 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-62064048977321) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (679 / 1000) ≤ x → x ≤ (17 / 25) →
      (15941756315883 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (31902258213393 / 20000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (679 / 1000)) (w := (1 / 1000))
      (r1 := (464928105379 / 1000000000000))
      (r2 := (1853349326037 / 500000000000)) (r3 := (2368194003 / 500000000))
      (r4 := (242757 / 1000000))
      (R := (46863954067 / 100000000000000))
      (NL := (15941756315883 / 10000000000000)) (NU := (31902258213393 / 20000000000000))
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
  exact Dfun_box_pos (a := (679 / 1000)) (b := (17 / 25)) (m := (1359 / 2000))
    (hh := (1 / 2000)) (K := (37278917613 / 1250000000000))
    (bnd := (141156615687 / 2000000000000000))
    (Lu := ((-9659951134773) / 25000000000000))
    (Ll := ((-38639804539833) / 100000000000000))
    (Ml := ((-7111706266387) / 6250000000000))
    (Nu := ((-61937687255119) / 100000000000000))
    (U1 := ((-113631415585211) / 100000000000000))
    (L1 := ((-113943428318883) / 100000000000000))
    (U2 := ((-61811577775671) / 100000000000000))
    (L2 := ((-62064048977321) / 100000000000000))
    (NL := (15941756315883 / 10000000000000))
    (NU := (31902258213393 / 20000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_056 {s : ℝ} (hs1 : (17 / 25) ≤ s) (hs2 : s ≤ (681 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1361 / 2000) ≤ ((-38492745689059) / 100000000000000) :=
    logU (w := (1361 / 2000)) (c := (1361 / 1000))
      (q := (6164394473387 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-38492745689059) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4811593211231) / 12500000000000) ≤ Real.log (1361 / 2000) :=
    logL (w := (1361 / 2000)) (c := (1361 / 1000))
      (q := (30821972366147 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-4811593211231) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-57049900258249) / 50000000000000) ≤ Real.log (1 - (1361 / 2000)) :=
    logL (w := (639 / 2000)) (c := (639 / 500))
      (q := (6132408898873 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-57049900258249) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1361 / 2000) ^ 2) ≤ ((-62190663698151) / 100000000000000) :=
    logU (w := (2147679 / 4000000)) (c := (2147679 / 2000000))
      (q := (7124054357843 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-62190663698151) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (17 / 25)) ≤ ((-22788685663767) / 20000000000000) :=
    logU (w := (8 / 25)) (c := (32 / 25))
      (q := (24686007793153 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-22788685663767) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-114256417619769) / 100000000000000) ≤ Real.log (1 - (681 / 1000)) :=
    logL (w := (319 / 1000)) (c := (319 / 250))
      (q := (24373018492221 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-114256417619769) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (17 / 25) ^ 2) ≤ ((-62064048977319) / 100000000000000) :=
    logU (w := (336 / 625)) (c := (672 / 625))
      (q := (290026763147 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-62064048977319) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-31158766088541) / 50000000000000) ≤ Real.log (1 - (681 / 1000) ^ 2) :=
    logL (w := (536239 / 1000000)) (c := (536239 / 500000))
      (q := (6997185878913 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-31158766088541) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (17 / 25) ≤ x → x ≤ (681 / 1000) →
      (79686091415699 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79732214030189 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (17 / 25)) (w := (1 / 1000))
      (r1 := (44677783 / 97656250))
      (r2 := (7267401 / 1953125)) (r3 := (1480437 / 312500))
      (r4 := (6561 / 25000))
      (R := (4612261449 / 10000000000000))
      (NL := (79686091415699 / 50000000000000)) (NU := (79732214030189 / 50000000000000))
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
  exact Dfun_box_pos (a := (17 / 25)) (b := (681 / 1000)) (m := (1361 / 2000))
    (hh := (1 / 2000)) (K := (2926722965939 / 100000000000000))
    (bnd := (338325610487 / 5000000000000000))
    (Lu := ((-38492745689059) / 100000000000000))
    (Ll := ((-4811593211231) / 12500000000000))
    (Ml := ((-57049900258249) / 50000000000000))
    (Nu := ((-62190663698151) / 100000000000000))
    (U1 := ((-22788685663767) / 20000000000000))
    (L1 := ((-114256417619769) / 100000000000000))
    (U2 := ((-62064048977319) / 100000000000000))
    (L2 := ((-31158766088541) / 50000000000000))
    (NL := (79686091415699 / 50000000000000))
    (NU := (79732214030189 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_057 {s : ℝ} (hs1 : (681 / 1000) ≤ s) (hs2 : s ≤ (341 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (1363 / 2000) ≤ ((-38345902784553) / 100000000000000) :=
    logU (w := (1363 / 2000)) (c := (1363 / 1000))
      (q := (30968815271441 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-38345902784553) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-38345902785391) / 100000000000000) ≤ Real.log (1363 / 2000) :=
    logL (w := (1363 / 2000)) (c := (1363 / 1000))
      (q := (7742203817651 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-38345902785391) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-114413280397029) / 100000000000000) ≤ Real.log (1 - (1363 / 2000)) :=
    logL (w := (637 / 2000)) (c := (637 / 500))
      (q := (24216155714961 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-114413280397029) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1363 / 2000) ^ 2) ≤ ((-15611163794293) / 25000000000000) :=
    logU (w := (2142231 / 4000000)) (c := (2142231 / 2000000))
      (q := (3435031439411 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-15611163794293) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (681 / 1000)) ≤ ((-7141026101233) / 6250000000000) :=
    logU (w := (319 / 1000)) (c := (319 / 250))
      (q := (1218650924613 / 5000000000000)) (k := 2) (J := 6)
      (R := ((-7141026101233) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-11457038962023) / 10000000000000) ≤ Real.log (1 - (341 / 500)) :=
    logL (w := (159 / 500)) (c := (159 / 125))
      (q := (300738081147 / 1250000000000)) (k := 2) (J := 6)
      (R := ((-11457038962023) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (681 / 1000) ^ 2) ≤ ((-1557938304427) / 2500000000000) :=
    logU (w := (536239 / 1000000)) (c := (536239 / 500000))
      (q := (3498592939457 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1557938304427) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-62572033465121) / 100000000000000) ≤ Real.log (1 - (341 / 500) ^ 2) :=
    logL (w := (133719 / 250000)) (c := (133719 / 125000))
      (q := (3371342295437 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-62572033465121) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (681 / 1000) ≤ x → x ≤ (341 / 500) →
      (19915943691 / 12500000000) ≤ Npoly x ∧
      Npoly x ≤ (159418306393587 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (681 / 1000)) (w := (1 / 1000))
      (r1 := (28127779127 / 62500000000))
      (r2 := (1867561560603 / 500000000000)) (r3 := (2369243763 / 500000000))
      (r4 := (282123 / 1000000))
      (R := (45378432793 / 100000000000000))
      (NL := (19915943691 / 12500000000)) (NU := (159418306393587 / 100000000000000))
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
  exact Dfun_box_pos (a := (681 / 1000)) (b := (341 / 500)) (m := (1363 / 2000))
    (hh := (1 / 2000)) (K := (2871445826663 / 100000000000000))
    (bnd := (65277381717 / 1000000000000000))
    (Lu := ((-38345902784553) / 100000000000000))
    (Ll := ((-38345902785391) / 100000000000000))
    (Ml := ((-114413280397029) / 100000000000000))
    (Nu := ((-15611163794293) / 25000000000000))
    (U1 := ((-7141026101233) / 6250000000000))
    (L1 := ((-11457038962023) / 10000000000000))
    (U2 := ((-1557938304427) / 2500000000000))
    (L2 := ((-62572033465121) / 100000000000000))
    (NL := (19915943691 / 12500000000))
    (NU := (159418306393587 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_058 {s : ℝ} (hs1 : (341 / 500) ≤ s) (hs2 : s ≤ (683 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (273 / 400) ≤ ((-381992751923) / 1000000000000) :=
    logU (w := (273 / 400)) (c := (273 / 200))
      (q := (15557721431847 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-381992751923) / 1000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3819927519319) / 10000000000000) ≤ Real.log (273 / 400) :=
    logL (w := (273 / 400)) (c := (273 / 200))
      (q := (6223088572561 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-3819927519319) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-11472774606497) / 10000000000000) ≤ Real.log (1 - (273 / 400)) :=
    logL (w := (127 / 400)) (c := (127 / 100))
      (q := (1195084502351 / 5000000000000)) (k := 2) (J := 6)
      (R := ((-11472774606497) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (273 / 400) ^ 2) ≤ ((-62699667811263) / 100000000000000) :=
    logU (w := (85471 / 160000)) (c := (85471 / 80000))
      (q := (6615050244731 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-62699667811263) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (341 / 500)) ≤ ((-57285194810097) / 50000000000000) :=
    logU (w := (159 / 500)) (c := (159 / 125))
      (q := (12029523245897 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-57285194810097) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-57442675255257) / 50000000000000) ≤ Real.log (1 - (683 / 1000)) :=
    logL (w := (317 / 1000)) (c := (317 / 250))
      (q := (5936021400369 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-57442675255257) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (341 / 500) ^ 2) ≤ ((-62572033465119) / 100000000000000) :=
    logU (w := (133719 / 250000)) (c := (133719 / 125000))
      (q := (53941476727 / 800000000000)) (k := 1) (J := 6)
      (R := ((-62572033465119) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-3141377949481) / 5000000000000) ≤ Real.log (1 - (683 / 1000) ^ 2) :=
    logL (w := (533511 / 1000000)) (c := (533511 / 500000))
      (q := (51897272531 / 800000000000)) (k := 1) (J := 6)
      (R := ((-3141377949481) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (341 / 500) ≤ x → x ≤ (683 / 1000) →
      (79641833046017 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (159372928908727 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (341 / 500)) (w := (1 / 1000))
      (r1 := (442560003179 / 1000000000000))
      (r2 := (234333769743 / 62500000000)) (r3 := (592456923 / 125000000))
      (r4 := (150903 / 500000))
      (R := (22315704173 / 50000000000000))
      (NL := (79641833046017 / 50000000000000)) (NU := (159372928908727 / 100000000000000))
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
  exact Dfun_box_pos (a := (341 / 500)) (b := (683 / 1000)) (m := (273 / 400))
    (hh := (1 / 2000)) (K := (704120603603 / 25000000000000))
    (bnd := (634122747397 / 10000000000000000))
    (Lu := ((-381992751923) / 1000000000000))
    (Ll := ((-3819927519319) / 10000000000000))
    (Ml := ((-11472774606497) / 10000000000000))
    (Nu := ((-62699667811263) / 100000000000000))
    (U1 := ((-57285194810097) / 50000000000000))
    (L1 := ((-57442675255257) / 50000000000000))
    (U2 := ((-62572033465119) / 100000000000000))
    (L2 := ((-3141377949481) / 5000000000000))
    (NL := (79641833046017 / 50000000000000))
    (NU := (159372928908727 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_059 {s : ℝ} (hs1 : (683 / 1000) ≤ s) (hs2 : s ≤ (171 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (1367 / 2000) ≤ ((-38052862281811) / 100000000000000) :=
    logU (w := (1367 / 2000)) (c := (1367 / 1000))
      (q := (31261855774183 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-38052862281811) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-9513215570689) / 25000000000000) ≤ Real.log (1367 / 2000) :=
    logL (w := (1367 / 2000)) (c := (1367 / 1000))
      (q := (31261855773239 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-9513215570689) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-115043203739817) / 100000000000000) ≤ Real.log (1 - (1367 / 2000)) :=
    logL (w := (633 / 2000)) (c := (633 / 500))
      (q := (23586232372173 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115043203739817) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1367 / 2000) ^ 2) ≤ ((-6295570777789) / 10000000000000) :=
    logU (w := (2131311 / 4000000)) (c := (2131311 / 2000000))
      (q := (794876284763 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-6295570777789) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (683 / 1000)) ≤ ((-28721337627621) / 25000000000000) :=
    logU (w := (317 / 1000)) (c := (317 / 250))
      (q := (742002675047 / 3125000000000)) (k := 2) (J := 6)
      (R := ((-28721337627621) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-115201306539547) / 100000000000000) ≤ Real.log (1 - (171 / 250)) :=
    logL (w := (79 / 250)) (c := (158 / 125))
      (q := (23428129572443 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115201306539547) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (683 / 1000) ^ 2) ≤ ((-31413779494809) / 50000000000000) :=
    logU (w := (533511 / 1000000)) (c := (533511 / 500000))
      (q := (810894883297 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-31413779494809) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-6308411495751) / 10000000000000) ≤ Real.log (1 - (171 / 250) ^ 2) :=
    logL (w := (33259 / 62500)) (c := (33259 / 31250))
      (q := (1246120619697 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-6308411495751) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (683 / 1000) ≤ x → x ≤ (171 / 250) →
      (159240535367617 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79664149224281 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (683 / 1000)) (w := (1 / 1000))
      (r1 := (217523551177 / 500000000000))
      (r2 := (1881780566121 / 500000000000)) (r3 := (2370450987 / 500000000))
      (r4 := (321489 / 1000000))
      (R := (5485192559 / 12500000000000))
      (NL := (159240535367617 / 100000000000000)) (NU := (79664149224281 / 50000000000000))
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
  exact Dfun_box_pos (a := (683 / 1000)) (b := (171 / 250)) (m := (1367 / 2000))
    (hh := (1 / 2000)) (K := (345229145049 / 12500000000000))
    (bnd := (310334924839 / 5000000000000000))
    (Lu := ((-38052862281811) / 100000000000000))
    (Ll := ((-9513215570689) / 25000000000000))
    (Ml := ((-115043203739817) / 100000000000000))
    (Nu := ((-6295570777789) / 10000000000000))
    (U1 := ((-28721337627621) / 25000000000000))
    (L1 := ((-115201306539547) / 100000000000000))
    (U2 := ((-31413779494809) / 50000000000000))
    (L2 := ((-6308411495751) / 10000000000000))
    (NL := (159240535367617 / 100000000000000))
    (NU := (79664149224281 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_060 {s : ℝ} (hs1 : (171 / 250) ≤ s) (hs2 : s ≤ (137 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (1369 / 2000) ≤ ((-37906663425361) / 100000000000000) :=
    logU (w := (1369 / 2000)) (c := (1369 / 1000))
      (q := (31408054630633 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-37906663425361) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-9476665856591) / 25000000000000) ≤ Real.log (1369 / 2000) :=
    logL (w := (1369 / 2000)) (c := (1369 / 1000))
      (q := (31408054629631 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-9476665856591) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-115359659700109) / 100000000000000) ≤ Real.log (1 - (1369 / 2000)) :=
    logL (w := (631 / 2000)) (c := (631 / 500))
      (q := (23269776411881 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115359659700109) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1369 / 2000) ^ 2) ≤ ((-63212781313639) / 100000000000000) :=
    logU (w := (2125839 / 4000000)) (c := (2125839 / 2000000))
      (q := (1220387348471 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-63212781313639) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (171 / 250)) ≤ ((-115201306539521) / 100000000000000) :=
    logU (w := (79 / 250)) (c := (158 / 125))
      (q := (23428129572467 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115201306539521) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-115518264015671) / 100000000000000) ≤ Real.log (1 - (137 / 200)) :=
    logL (w := (63 / 200)) (c := (63 / 50))
      (q := (23111172096319 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115518264015671) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (171 / 250) ^ 2) ≤ ((-15771028739377) / 25000000000000) :=
    logU (w := (33259 / 62500)) (c := (33259 / 31250))
      (q := (3115301549243 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-15771028739377) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-63341707635219) / 100000000000000) ≤ Real.log (1 - (137 / 200) ^ 2) :=
    logL (w := (21231 / 40000)) (c := (21231 / 20000))
      (q := (746626302597 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-63341707635219) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (171 / 250) ≤ x → x ≤ (137 / 200) →
      (39799540049911 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (159284417856537 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (171 / 250)) (w := (1 / 1000))
      (r1 := (213752878039 / 500000000000))
      (r2 := (29513951613 / 7812500000)) (r3 := (148194603 / 31250000))
      (r4 := (85293 / 250000))
      (R := (21564414223 / 50000000000000))
      (NL := (39799540049911 / 25000000000000)) (NU := (159284417856537 / 100000000000000))
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
  exact Dfun_box_pos (a := (171 / 250)) (b := (137 / 200)) (m := (1369 / 2000))
    (hh := (1 / 2000)) (K := (2707498503929 / 100000000000000))
    (bnd := (122477383771 / 2000000000000000))
    (Lu := ((-37906663425361) / 100000000000000))
    (Ll := ((-9476665856591) / 25000000000000))
    (Ml := ((-115359659700109) / 100000000000000))
    (Nu := ((-63212781313639) / 100000000000000))
    (U1 := ((-115201306539521) / 100000000000000))
    (L1 := ((-115518264015671) / 100000000000000))
    (U2 := ((-15771028739377) / 25000000000000))
    (L2 := ((-63341707635219) / 100000000000000))
    (NL := (39799540049911 / 25000000000000))
    (NU := (159284417856537 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_061 {s : ℝ} (hs1 : (137 / 200) ≤ s) (hs2 : s ≤ (343 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (1371 / 2000) ≤ ((-18880338998987) / 50000000000000) :=
    logU (w := (1371 / 2000)) (c := (1371 / 1000))
      (q := (1577702002901 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-18880338998987) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-37760677999039) / 100000000000000) ≤ Real.log (1371 / 2000) :=
    logL (w := (1371 / 2000)) (c := (1371 / 1000))
      (q := (7888510014239 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-37760677999039) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-115677120284183) / 100000000000000) ≤ Real.log (1 - (1371 / 2000)) :=
    logL (w := (629 / 2000)) (c := (629 / 500))
      (q := (22952315827807 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115677120284183) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1371 / 2000) ^ 2) ≤ ((-12694178942993) / 20000000000000) :=
    logU (w := (2120359 / 4000000)) (c := (2120359 / 2000000))
      (q := (5843823341029 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-12694178942993) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (137 / 200)) ≤ ((-115518264015649) / 100000000000000) :=
    logU (w := (63 / 200)) (c := (63 / 50))
      (q := (23111172096339 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115518264015649) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-57918114653703) / 50000000000000) ≤ Real.log (1 - (343 / 500)) :=
    logL (w := (157 / 500)) (c := (157 / 125))
      (q := (2849150850573 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-57918114653703) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (137 / 200) ^ 2) ≤ ((-63341707635217) / 100000000000000) :=
    logU (w := (21231 / 40000)) (c := (21231 / 20000))
      (q := (5973010420777 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-63341707635217) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-63600343349423) / 100000000000000) ≤ Real.log (1 - (343 / 500) ^ 2) :=
    logL (w := (132351 / 250000)) (c := (132351 / 125000))
      (q := (1428593676643 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-63600343349423) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (137 / 200) ≤ x → x ≤ (343 / 500) →
      (159156543433823 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79620644988409 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (137 / 200)) (w := (1 / 1000))
      (r1 := (419935956399 / 1000000000000))
      (r2 := (15168058299 / 4000000000)) (r3 := (94872627 / 20000000))
      (r4 := (72171 / 200000))
      (R := (42373271497 / 100000000000000))
      (NL := (159156543433823 / 100000000000000)) (NU := (79620644988409 / 50000000000000))
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
  exact Dfun_box_pos (a := (137 / 200)) (b := (343 / 500)) (m := (1371 / 2000))
    (hh := (1 / 2000)) (K := (8292121539 / 312500000000))
    (bnd := (304622852707 / 5000000000000000))
    (Lu := ((-18880338998987) / 50000000000000))
    (Ll := ((-37760677999039) / 100000000000000))
    (Ml := ((-115677120284183) / 100000000000000))
    (Nu := ((-12694178942993) / 20000000000000))
    (U1 := ((-115518264015649) / 100000000000000))
    (L1 := ((-57918114653703) / 50000000000000))
    (U2 := ((-63341707635217) / 100000000000000))
    (L2 := ((-63600343349423) / 100000000000000))
    (NL := (159156543433823 / 100000000000000))
    (NU := (79620644988409 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_062 {s : ℝ} (hs1 : (343 / 500) ≤ s) (hs2 : s ≤ (687 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1373 / 2000) ≤ ((-293866448261) / 781250000000) :=
    logU (w := (1373 / 2000)) (c := (1373 / 1000))
      (q := (15849906339293 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-293866448261) / 781250000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-18807452689269) / 50000000000000) ≤ Real.log (1373 / 2000) :=
    logL (w := (1373 / 2000)) (c := (1373 / 1000))
      (q := (31699812677457 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-18807452689269) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-28998897972733) / 25000000000000) ≤ Real.log (1 - (1373 / 2000)) :=
    logL (w := (627 / 2000)) (c := (627 / 500))
      (q := (11316922110529 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-28998897972733) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1373 / 2000) ^ 2) ≤ ((-31865027169479) / 50000000000000) :=
    logU (w := (2114871 / 4000000)) (c := (2114871 / 2000000))
      (q := (1396165929259 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-31865027169479) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (343 / 500)) ≤ ((-115836229307387) / 100000000000000) :=
    logU (w := (157 / 500)) (c := (157 / 125))
      (q := (22793206804601 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-115836229307387) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-116155208844213) / 100000000000000) ≤ Real.log (1 - (687 / 1000)) :=
    logL (w := (313 / 1000)) (c := (313 / 250))
      (q := (22474227267777 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-116155208844213) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (343 / 500) ^ 2) ≤ ((-63600343349421) / 100000000000000) :=
    logU (w := (132351 / 250000)) (c := (132351 / 125000))
      (q := (5714374706573 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-63600343349421) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-7982503560977) / 12500000000000) ≤ Real.log (1 - (687 / 1000) ^ 2) :=
    logL (w := (528031 / 1000000)) (c := (528031 / 500000))
      (q := (5454689568179 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-7982503560977) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (343 / 500) ≤ x → x ≤ (687 / 1000) →
      (15911568791673 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (31839783530869 / 20000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (343 / 500)) (w := (1 / 1000))
      (r1 := (103084423723 / 250000000000))
      (r2 := (237890479581 / 62500000000)) (r3 := (593139267 / 125000000))
      (r4 := (190269 / 500000))
      (R := (41614868807 / 100000000000000))
      (NL := (15911568791673 / 10000000000000)) (NU := (31839783530869 / 20000000000000))
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
  exact Dfun_box_pos (a := (343 / 500)) (b := (687 / 1000)) (m := (1373 / 2000))
    (hh := (1 / 2000)) (K := (1337823858369 / 50000000000000))
    (bnd := (122243583227 / 2000000000000000))
    (Lu := ((-293866448261) / 781250000000))
    (Ll := ((-18807452689269) / 50000000000000))
    (Ml := ((-28998897972733) / 25000000000000))
    (Nu := ((-31865027169479) / 50000000000000))
    (U1 := ((-115836229307387) / 100000000000000))
    (L1 := ((-116155208844213) / 100000000000000))
    (U2 := ((-63600343349421) / 100000000000000))
    (L2 := ((-7982503560977) / 12500000000000))
    (NL := (15911568791673 / 10000000000000))
    (NU := (31839783530869 / 20000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_063 {s : ℝ} (hs1 : (687 / 1000) ≤ s) (hs2 : s ≤ (86 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (11 / 16) ≤ ((-18734672472069) / 50000000000000) :=
    logU (w := (11 / 16)) (c := (11 / 8))
      (q := (1990335819491 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-18734672472069) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4683668118167) / 12500000000000) ≤ Real.log (11 / 16) :=
    logL (w := (11 / 16)) (c := (11 / 8))
      (q := (31845373110659 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-4683668118167) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-58157540490291) / 50000000000000) ≤ Real.log (1 - (11 / 16)) :=
    logL (w := (5 / 16)) (c := (5 / 4))
      (q := (1394647195713 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-58157540490291) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (11 / 16) ^ 2) ≤ ((-3999391662757) / 6250000000000) :=
    logU (w := (135 / 256)) (c := (135 / 128))
      (q := (2662225725941 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-3999391662757) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (687 / 1000)) ≤ ((-116155208844197) / 100000000000000) :=
    logU (w := (313 / 1000)) (c := (313 / 250))
      (q := (22474227267791 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-116155208844197) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-58237604558639) / 50000000000000) ≤ Real.log (1 - (86 / 125)) :=
    logL (w := (39 / 125)) (c := (156 / 125))
      (q := (2769278374339 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-58237604558639) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (687 / 1000) ^ 2) ≤ ((-31930014243907) / 50000000000000) :=
    logU (w := (528031 / 1000000)) (c := (528031 / 500000))
      (q := (272734478409 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-31930014243907) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-6412076949989) / 10000000000000) ≤ Real.log (1 - (86 / 125) ^ 2) :=
    logL (w := (8229 / 15625)) (c := (16458 / 15625))
      (q := (1038789711221 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-6412076949989) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (687 / 1000) ≤ x → x ≤ (86 / 125) →
      (79537798247929 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (1273258429879 / 800000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (687 / 1000)) (w := (1 / 1000))
      (r1 := (404710962661 / 1000000000000))
      (r2 := (1910242669149 / 500000000000)) (r3 := (2373337827 / 500000000))
      (r4 := (400221 / 1000000))
      (R := (10213404877 / 25000000000000))
      (NL := (79537798247929 / 50000000000000)) (NU := (1273258429879 / 800000000000))
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
  exact Dfun_box_pos (a := (687 / 1000)) (b := (86 / 125)) (m := (11 / 16))
    (hh := (1 / 2000)) (K := (2723896728649 / 100000000000000))
    (bnd := (309137606143 / 5000000000000000))
    (Lu := ((-18734672472069) / 50000000000000))
    (Ll := ((-4683668118167) / 12500000000000))
    (Ml := ((-58157540490291) / 50000000000000))
    (Nu := ((-3999391662757) / 6250000000000))
    (U1 := ((-116155208844197) / 100000000000000))
    (L1 := ((-58237604558639) / 50000000000000))
    (U2 := ((-31930014243907) / 50000000000000))
    (L2 := ((-6412076949989) / 10000000000000))
    (NL := (79537798247929 / 50000000000000))
    (NU := (1273258429879 / 800000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_064 {s : ℝ} (hs1 : (86 / 125) ≤ s) (hs2 : s ≤ (689 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1377 / 2000) ≤ ((-1866199804067) / 5000000000000) :=
    logU (w := (1377 / 2000)) (c := (1377 / 1000))
      (q := (15995360987327 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1866199804067) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3732399608261) / 10000000000000) ≤ Real.log (1377 / 2000) :=
    logL (w := (1377 / 2000)) (c := (1377 / 1000))
      (q := (6398144394677 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-3732399608261) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-4665423763019) / 4000000000000) ≤ Real.log (1 - (1377 / 2000)) :=
    logL (w := (623 / 2000)) (c := (623 / 500))
      (q := (4398768407303 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-4665423763019) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1377 / 2000) ^ 2) ≤ ((-64251537991113) / 100000000000000) :=
    logU (w := (2103871 / 4000000)) (c := (2103871 / 2000000))
      (q := (5063180064881 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-64251537991113) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (86 / 125)) ≤ ((-7279700569829) / 6250000000000) :=
    logU (w := (39 / 125)) (c := (156 / 125))
      (q := (5538556748681 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-7279700569829) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-116796236680301) / 100000000000000) ≤ Real.log (1 - (689 / 1000)) :=
    logL (w := (311 / 1000)) (c := (311 / 250))
      (q := (21833199431689 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-116796236680301) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (86 / 125) ^ 2) ≤ ((-4007548093743) / 6250000000000) :=
    logU (w := (8229 / 15625)) (c := (16458 / 15625))
      (q := (2596974278053 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-4007548093743) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-2575302915909) / 4000000000000) ≤ Real.log (1 - (689 / 1000) ^ 2) :=
    logL (w := (525279 / 1000000)) (c := (525279 / 500000))
      (q := (493214515827 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-2575302915909) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (86 / 125) ≤ x → x ≤ (689 / 1000) →
      (39759068004913 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (159116451065031 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (86 / 125)) (w := (1 / 1000))
      (r1 := (397055750337 / 1000000000000))
      (r2 := (3744851373 / 976562500)) (r3 := (18548109 / 3906250))
      (r4 := (6561 / 15625))
      (R := (40089522689 / 100000000000000))
      (NL := (39759068004913 / 25000000000000)) (NU := (159116451065031 / 100000000000000))
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
  exact Dfun_box_pos (a := (86 / 125)) (b := (689 / 1000)) (m := (1377 / 2000))
    (hh := (1 / 2000)) (K := (554378950117 / 20000000000000))
    (bnd := (315194604731 / 5000000000000000))
    (Lu := ((-1866199804067) / 5000000000000))
    (Ll := ((-3732399608261) / 10000000000000))
    (Ml := ((-4665423763019) / 4000000000000))
    (Nu := ((-64251537991113) / 100000000000000))
    (U1 := ((-7279700569829) / 6250000000000))
    (L1 := ((-116796236680301) / 100000000000000))
    (U2 := ((-4007548093743) / 6250000000000))
    (L2 := ((-2575302915909) / 4000000000000))
    (NL := (39759068004913 / 25000000000000))
    (NU := (159116451065031 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_065 {s : ℝ} (hs1 : (689 / 1000) ≤ s) (hs2 : s ≤ (69 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (1379 / 2000) ≤ ((-297430865399) / 800000000000) :=
    logU (w := (1379 / 2000)) (c := (1379 / 1000))
      (q := (32135859881119 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-297430865399) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-37178858176221) / 100000000000000) ≤ Real.log (1379 / 2000) :=
    logL (w := (1379 / 2000)) (c := (1379 / 1000))
      (q := (16067929939887 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-37178858176221) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-11695713776087) / 10000000000000) ≤ Real.log (1 - (1379 / 2000)) :=
    logL (w := (621 / 2000)) (c := (621 / 500))
      (q := (270903729389 / 1250000000000)) (k := 2) (J := 6)
      (R := ((-11695713776087) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1379 / 2000) ^ 2) ≤ ((-64513875043639) / 100000000000000) :=
    logU (w := (2098359 / 4000000)) (c := (2098359 / 2000000))
      (q := (960168602471 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-64513875043639) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (689 / 1000)) ≤ ((-116796236680289) / 100000000000000) :=
    logU (w := (311 / 1000)) (c := (311 / 250))
      (q := (21833199431699 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-116796236680289) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-3659946817197) / 3125000000000) ≤ Real.log (1 - (69 / 100)) :=
    logL (w := (31 / 100)) (c := (31 / 25))
      (q := (10755568980843 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-3659946817197) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (689 / 1000) ^ 2) ≤ ((-64382572897723) / 100000000000000) :=
    logU (w := (525279 / 1000000)) (c := (525279 / 500000))
      (q := (4932145158271 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-64382572897723) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-64645445256797) / 100000000000000) ≤ Real.log (1 - (69 / 100) ^ 2) :=
    logL (w := (5239 / 10000)) (c := (5239 / 5000))
      (q := (2334636399599 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-64645445256797) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (689 / 1000) ≤ x → x ≤ (69 / 100) →
      (6359908693503 / 4000000000000) ≤ Npoly x ∧
      Npoly x ≤ (3181527249847 / 2000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (689 / 1000)) (w := (1 / 1000))
      (r1 := (194686024039 / 500000000000))
      (r2 := (1924487656227 / 500000000000)) (r3 := (2375017443 / 500000000))
      (r4 := (439587 / 1000000))
      (R := (39322577387 / 100000000000000))
      (NL := (6359908693503 / 4000000000000)) (NU := (3181527249847 / 2000000000000))
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
  exact Dfun_box_pos (a := (689 / 1000)) (b := (69 / 100)) (m := (1379 / 2000))
    (hh := (1 / 2000)) (K := (2819641332871 / 100000000000000))
    (bnd := (647531477271 / 10000000000000000))
    (Lu := ((-297430865399) / 800000000000))
    (Ll := ((-37178858176221) / 100000000000000))
    (Ml := ((-11695713776087) / 10000000000000))
    (Nu := ((-64513875043639) / 100000000000000))
    (U1 := ((-116796236680289) / 100000000000000))
    (L1 := ((-3659946817197) / 3125000000000))
    (U2 := ((-64382572897723) / 100000000000000))
    (L2 := ((-64645445256797) / 100000000000000))
    (NL := (6359908693503 / 4000000000000))
    (NU := (3181527249847 / 2000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_066 {s : ℝ} (hs1 : (69 / 100) ≤ s) (hs2 : s ≤ (691 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1381 / 2000) ≤ ((-9258482653319) / 25000000000000) :=
    logU (w := (1381 / 2000)) (c := (1381 / 1000))
      (q := (16140393721359 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-9258482653319) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-18516965307351) / 50000000000000) ≤ Real.log (1381 / 2000) :=
    logL (w := (1381 / 2000)) (c := (1381 / 1000))
      (q := (32280787441293 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-18516965307351) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-117279718685757) / 100000000000000) ≤ Real.log (1 - (1381 / 2000)) :=
    logL (w := (619 / 2000)) (c := (619 / 500))
      (q := (21349717426233 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-117279718685757) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1381 / 2000) ^ 2) ≤ ((-64777284369167) / 100000000000000) :=
    logU (w := (2092839 / 4000000)) (c := (2092839 / 2000000))
      (q := (4537433686827 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-64777284369167) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (69 / 100)) ≤ ((-117118298150293) / 100000000000000) :=
    logU (w := (31 / 100)) (c := (31 / 25))
      (q := (4302227592339 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-117118298150293) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-117441400208447) / 100000000000000) ≤ Real.log (1 - (691 / 1000)) :=
    logL (w := (309 / 1000)) (c := (309 / 250))
      (q := (21188035903543 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-117441400208447) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (69 / 100) ^ 2) ≤ ((-12929089051359) / 20000000000000) :=
    logU (w := (5239 / 10000)) (c := (5239 / 5000))
      (q := (4669272799199 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-12929089051359) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-16227348304199) / 25000000000000) ≤ Real.log (1 - (691 / 1000) ^ 2) :=
    logL (w := (522519 / 1000000)) (c := (522519 / 500000))
      (q := (4405324839199 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-16227348304199) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (69 / 100) ≤ x → x ≤ (691 / 1000) →
      (79479967650069 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (15903704086533 / 10000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (69 / 100)) (w := (1 / 1000))
      (r1 := (38165984557 / 100000000000))
      (r2 := (1931614047 / 500000000)) (r3 := (23759163 / 5000000))
      (r4 := (45927 / 100000))
      (R := (9638195649 / 25000000000000))
      (NL := (79479967650069 / 50000000000000)) (NU := (15903704086533 / 10000000000000))
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
  exact Dfun_box_pos (a := (69 / 100)) (b := (691 / 1000)) (m := (1381 / 2000))
    (hh := (1 / 2000)) (K := (358392002771 / 12500000000000))
    (bnd := (334836768997 / 5000000000000000))
    (Lu := ((-9258482653319) / 25000000000000))
    (Ll := ((-18516965307351) / 50000000000000))
    (Ml := ((-117279718685757) / 100000000000000))
    (Nu := ((-64777284369167) / 100000000000000))
    (U1 := ((-117118298150293) / 100000000000000))
    (L1 := ((-117441400208447) / 100000000000000))
    (U2 := ((-12929089051359) / 20000000000000))
    (L2 := ((-16227348304199) / 25000000000000))
    (NL := (79479967650069 / 50000000000000))
    (NU := (15903704086533 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_067 {s : ℝ} (hs1 : (691 / 1000) ≤ s) (hs2 : s ≤ (173 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (1383 / 2000) ≤ ((-36889212787729) / 100000000000000) :=
    logU (w := (1383 / 2000)) (c := (1383 / 1000))
      (q := (6485101053653 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-36889212787729) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-36889212789239) / 100000000000000) ≤ Real.log (1383 / 2000) :=
    logL (w := (1383 / 2000)) (c := (1383 / 1000))
      (q := (8106376316689 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-36889212789239) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-117603343563677) / 100000000000000) ≤ Real.log (1 - (1383 / 2000)) :=
    logL (w := (617 / 2000)) (c := (617 / 500))
      (q := (21026092548313 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-117603343563677) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1383 / 2000) ^ 2) ≤ ((-32520886319903) / 50000000000000) :=
    logU (w := (2087311 / 4000000)) (c := (2087311 / 2000000))
      (q := (1068236354047 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-32520886319903) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (691 / 1000)) ≤ ((-58720700104219) / 50000000000000) :=
    logU (w := (309 / 1000)) (c := (309 / 250))
      (q := (423760718071 / 2000000000000)) (k := 2) (J := 6)
      (R := ((-58720700104219) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-117765549600863) / 100000000000000) ≤ Real.log (1 - (173 / 250)) :=
    logL (w := (77 / 250)) (c := (154 / 125))
      (q := (20863886511127 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-117765549600863) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (691 / 1000) ^ 2) ≤ ((-32454696608397) / 50000000000000) :=
    logU (w := (522519 / 1000000)) (c := (522519 / 500000))
      (q := (5506656049 / 125000000000)) (k := 1) (J := 6)
      (R := ((-32454696608397) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-32587211741227) / 50000000000000) ≤ Real.log (1 - (173 / 250) ^ 2) :=
    logL (w := (32571 / 62500)) (c := (32571 / 31250))
      (q := (4140294573541 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-32587211741227) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (691 / 1000) ≤ x → x ≤ (173 / 250) →
      (79461464379477 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158998489033477 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (691 / 1000)) (w := (1 / 1000))
      (r1 := (93479783007 / 250000000000))
      (r2 := (1938743193393 / 500000000000)) (r3 := (2376854523 / 500000000))
      (r4 := (478953 / 1000000))
      (R := (37780137261 / 100000000000000))
      (NL := (79461464379477 / 50000000000000)) (NU := (158998489033477 / 100000000000000))
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
  exact Dfun_box_pos (a := (691 / 1000)) (b := (173 / 250)) (m := (1383 / 2000))
    (hh := (1 / 2000)) (K := (58287567229 / 2000000000000))
    (bnd := (348393433547 / 5000000000000000))
    (Lu := ((-36889212787729) / 100000000000000))
    (Ll := ((-36889212789239) / 100000000000000))
    (Ml := ((-117603343563677) / 100000000000000))
    (Nu := ((-32520886319903) / 50000000000000))
    (U1 := ((-58720700104219) / 50000000000000))
    (L1 := ((-117765549600863) / 100000000000000))
    (U2 := ((-32454696608397) / 50000000000000))
    (L2 := ((-32587211741227) / 50000000000000))
    (NL := (79461464379477 / 50000000000000))
    (NU := (158998489033477 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_068 {s : ℝ} (hs1 : (173 / 250) ≤ s) (hs2 : s ≤ (693 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (277 / 400) ≤ ((-1837235204603) / 5000000000000) :=
    logU (w := (277 / 400)) (c := (277 / 200))
      (q := (16285006981967 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1837235204603) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-36744704093659) / 100000000000000) ≤ Real.log (277 / 400) :=
    logL (w := (277 / 400)) (c := (277 / 200))
      (q := (1017812936323 / 3125000000000)) (k := 1) (J := 6)
      (R := ((-36744704093659) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-117928019173563) / 100000000000000) ≤ Real.log (1 - (277 / 400)) :=
    logL (w := (123 / 400)) (c := (123 / 100))
      (q := (20701416938427 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-117928019173563) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (277 / 400) ^ 2) ≤ ((-32653673296563) / 50000000000000) :=
    logU (w := (83271 / 160000)) (c := (83271 / 80000))
      (q := (1001842865717 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-32653673296563) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (173 / 250)) ≤ ((-23553109920171) / 20000000000000) :=
    logU (w := (77 / 250)) (c := (154 / 125))
      (q := (20863886511133 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-23553109920171) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-236181506279) / 200000000000) ≤ Real.log (1 - (693 / 1000)) :=
    logL (w := (307 / 1000)) (c := (307 / 250))
      (q := (2053868297249 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-236181506279) / 200000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (173 / 250) ^ 2) ≤ ((-16293605870613) / 25000000000000) :=
    logU (w := (32571 / 62500)) (c := (32571 / 31250))
      (q := (2070147286771 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-16293605870613) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-13088108564879) / 20000000000000) ≤ Real.log (1 - (693 / 1000) ^ 2) :=
    logL (w := (519751 / 1000000)) (c := (519751 / 500000))
      (q := (9685438079 / 250000000000)) (k := 1) (J := 6)
      (R := ((-13088108564879) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (173 / 250) ≤ x → x ≤ (693 / 1000) →
      (19860837570849 / 12500000000000) ≤ Npoly x ∧
      Npoly x ≤ (158960709847351 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (173 / 250)) (w := (1 / 1000))
      (r1 := (178784129 / 488281250))
      (r2 := (30404300211 / 7812500000)) (r3 := (148614507 / 31250000))
      (r4 := (124659 / 250000))
      (R := (37004640279 / 100000000000000))
      (NL := (19860837570849 / 12500000000000)) (NU := (158960709847351 / 100000000000000))
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
  exact Dfun_box_pos (a := (173 / 250)) (b := (693 / 1000)) (m := (277 / 400))
    (hh := (1 / 2000)) (K := (148068394499 / 5000000000000))
    (bnd := (364421445687 / 5000000000000000))
    (Lu := ((-1837235204603) / 5000000000000))
    (Ll := ((-36744704093659) / 100000000000000))
    (Ml := ((-117928019173563) / 100000000000000))
    (Nu := ((-32653673296563) / 50000000000000))
    (U1 := ((-23553109920171) / 20000000000000))
    (L1 := ((-236181506279) / 200000000000))
    (U2 := ((-16293605870613) / 25000000000000))
    (L2 := ((-13088108564879) / 20000000000000))
    (NL := (19860837570849 / 12500000000000))
    (NU := (158960709847351 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_069 {s : ℝ} (hs1 : (693 / 1000) ≤ s) (hs2 : s ≤ (347 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (1387 / 2000) ≤ ((-36600403922721) / 100000000000000) :=
    logU (w := (1387 / 2000)) (c := (1387 / 1000))
      (q := (32714314133273 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-36600403922721) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-36600403924413) / 100000000000000) ≤ Real.log (1387 / 2000) :=
    logL (w := (1387 / 2000)) (c := (1387 / 1000))
      (q := (16357157065791 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-36600403924413) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-7390859522537) / 6250000000000) ≤ Real.log (1 - (1387 / 2000)) :=
    logL (w := (613 / 2000)) (c := (613 / 500))
      (q := (10187841875699 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-7390859522537) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1387 / 2000) ^ 2) ≤ ((-65574013033017) / 100000000000000) :=
    logU (w := (2076231 / 4000000)) (c := (2076231 / 2000000))
      (q := (3740705022977 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-65574013033017) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (693 / 1000)) ≤ ((-29522688284873) / 25000000000000) :=
    logU (w := (307 / 1000)) (c := (307 / 250))
      (q := (1283667685781 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-29522688284873) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-5920850885149) / 5000000000000) ≤ Real.log (1 - (347 / 500)) :=
    logL (w := (153 / 500)) (c := (153 / 125))
      (q := (2021241840901 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-5920850885149) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (693 / 1000) ^ 2) ≤ ((-65440542824393) / 100000000000000) :=
    logU (w := (519751 / 1000000)) (c := (519751 / 500000))
      (q := (3874175231601 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-65440542824393) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-6570775807999) / 10000000000000) ≤ Real.log (1 - (347 / 500) ^ 2) :=
    logL (w := (129591 / 250000)) (c := (129591 / 125000))
      (q := (721391995201 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-6570775807999) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (693 / 1000) ≤ x → x ≤ (347 / 500) →
      (15885125357761 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158923706158613 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (693 / 1000)) (w := (1 / 1000))
      (r1 := (358352126331 / 1000000000000))
      (r2 := (1953010225431 / 500000000000)) (r3 := (2378849067 / 500000000))
      (r4 := (518319 / 1000000))
      (R := (36226290501 / 100000000000000))
      (NL := (15885125357761 / 10000000000000)) (NU := (158923706158613 / 100000000000000))
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
  exact Dfun_box_pos (a := (693 / 1000)) (b := (347 / 500)) (m := (1387 / 2000))
    (hh := (1 / 2000)) (K := (601620828651 / 20000000000000))
    (bnd := (382906494789 / 5000000000000000))
    (Lu := ((-36600403922721) / 100000000000000))
    (Ll := ((-36600403924413) / 100000000000000))
    (Ml := ((-7390859522537) / 6250000000000))
    (Nu := ((-65574013033017) / 100000000000000))
    (U1 := ((-29522688284873) / 25000000000000))
    (L1 := ((-5920850885149) / 5000000000000))
    (U2 := ((-65440542824393) / 100000000000000))
    (L2 := ((-6570775807999) / 10000000000000))
    (NL := (15885125357761 / 10000000000000))
    (NU := (158923706158613 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_070 {s : ℝ} (hs1 : (347 / 500) ≤ s) (hs2 : s ≤ (139 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (1389 / 2000) ≤ ((-3645631167877) / 10000000000000) :=
    logU (w := (1389 / 2000)) (c := (1389 / 1000))
      (q := (4107300797153 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-3645631167877) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-36456311680559) / 100000000000000) ≤ Real.log (1389 / 2000) :=
    logL (w := (1389 / 2000)) (c := (1389 / 1000))
      (q := (8214601593859 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-36456311680559) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-118580550037053) / 100000000000000) ≤ Real.log (1 - (1389 / 2000)) :=
    logL (w := (611 / 2000)) (c := (611 / 500))
      (q := (20048886074937 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-118580550037053) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1389 / 2000) ^ 2) ≤ ((-65841778830551) / 100000000000000) :=
    logU (w := (2070679 / 4000000)) (c := (2070679 / 2000000))
      (q := (3472939225443 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-65841778830551) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (347 / 500)) ≤ ((-59208508851487) / 50000000000000) :=
    logU (w := (153 / 500)) (c := (153 / 125))
      (q := (10106209204507 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-59208508851487) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-118744350237477) / 100000000000000) ≤ Real.log (1 - (139 / 200)) :=
    logL (w := (61 / 200)) (c := (61 / 50))
      (q := (19885085874513 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-118744350237477) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (347 / 500) ^ 2) ≤ ((-16426939519997) / 25000000000000) :=
    logU (w := (129591 / 250000)) (c := (129591 / 125000))
      (q := (1803479988003 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-16426939519997) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-8247009519279) / 12500000000000) ≤ Real.log (1 - (139 / 200) ^ 2) :=
    logL (w := (20679 / 40000)) (c := (20679 / 20000))
      (q := (3338641901763 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8247009519279) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (347 / 500) ≤ x → x ≤ (139 / 200) →
      (19852073830827 / 12500000000000) ≤ Npoly x ∧
      Npoly x ≤ (6355499232803 / 4000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (347 / 500)) (w := (1 / 1000))
      (r1 := (175262905121 / 500000000000))
      (r2 := (245018543409 / 62500000000)) (r3 := (594976347 / 125000000))
      (r4 := (269001 / 500000))
      (R := (35445086729 / 100000000000000))
      (NL := (19852073830827 / 12500000000000)) (NU := (6355499232803 / 4000000000000))
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
  exact Dfun_box_pos (a := (347 / 500)) (b := (139 / 200)) (m := (1389 / 2000))
    (hh := (1 / 2000)) (K := (3054586653003 / 100000000000000))
    (bnd := (32306739627 / 400000000000000))
    (Lu := ((-3645631167877) / 10000000000000))
    (Ll := ((-36456311680559) / 100000000000000))
    (Ml := ((-118580550037053) / 100000000000000))
    (Nu := ((-65841778830551) / 100000000000000))
    (U1 := ((-59208508851487) / 50000000000000))
    (L1 := ((-118744350237477) / 100000000000000))
    (U2 := ((-16426939519997) / 25000000000000))
    (L2 := ((-8247009519279) / 12500000000000))
    (NL := (19852073830827 / 12500000000000))
    (NU := (6355499232803 / 4000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_071 {s : ℝ} (hs1 : (139 / 200) ≤ s) (hs2 : s ≤ (87 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (1391 / 2000) ≤ ((-36312426761859) / 100000000000000) :=
    logU (w := (1391 / 2000)) (c := (1391 / 1000))
      (q := (6600458258827 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-36312426761859) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4539053345469) / 12500000000000) ≤ Real.log (1391 / 2000) :=
    logL (w := (1391 / 2000)) (c := (1391 / 1000))
      (q := (33002291292243 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-4539053345469) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-59454209591611) / 50000000000000) ≤ Real.log (1 - (1391 / 2000)) :=
    logL (w := (609 / 2000)) (c := (609 / 500))
      (q := (38517611189 / 195312500000)) (k := 2) (J := 6)
      (R := ((-59454209591611) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1391 / 2000) ^ 2) ≤ ((-33055325462431) / 50000000000000) :=
    logU (w := (2065119 / 4000000)) (c := (2065119 / 2000000))
      (q := (801016782783 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-33055325462431) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (139 / 200)) ≤ ((-118744350237471) / 100000000000000) :=
    logU (w := (61 / 200)) (c := (61 / 50))
      (q := (19885085874517 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-118744350237471) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-23814551551519) / 20000000000000) ≤ Real.log (1 - (87 / 125)) :=
    logL (w := (38 / 125)) (c := (152 / 125))
      (q := (3911335670879 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-23814551551519) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (139 / 200) ^ 2) ≤ ((-6597607615423) / 10000000000000) :=
    logU (w := (20679 / 40000)) (c := (20679 / 20000))
      (q := (834660475441 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-6597607615423) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-66245504020621) / 100000000000000) ≤ Real.log (1 - (87 / 125) ^ 2) :=
    logL (w := (8056 / 15625)) (c := (16112 / 15625))
      (q := (1534607017687 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-66245504020621) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (139 / 200) ≤ x → x ≤ (87 / 125) →
      (31756542926061 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (39713009171437 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (139 / 200)) (w := (1 / 1000))
      (r1 := (342670935249 / 1000000000000))
      (r2 := (15738317577 / 4000000000)) (r3 := (95240043 / 20000000))
      (r4 := (111537 / 200000))
      (R := (34661027721 / 100000000000000))
      (NL := (31756542926061 / 20000000000000)) (NU := (39713009171437 / 25000000000000))
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
  exact Dfun_box_pos (a := (139 / 200)) (b := (87 / 125)) (m := (1391 / 2000))
    (hh := (1 / 2000)) (K := (1550407473557 / 50000000000000))
    (bnd := (854380673329 / 10000000000000000))
    (Lu := ((-36312426761859) / 100000000000000))
    (Ll := ((-4539053345469) / 12500000000000))
    (Ml := ((-59454209591611) / 50000000000000))
    (Nu := ((-33055325462431) / 50000000000000))
    (U1 := ((-118744350237471) / 100000000000000))
    (L1 := ((-23814551551519) / 20000000000000))
    (U2 := ((-6597607615423) / 10000000000000))
    (L2 := ((-66245504020621) / 100000000000000))
    (NL := (31756542926061 / 20000000000000))
    (NU := (39713009171437 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_072 {s : ℝ} (hs1 : (87 / 125) ≤ s) (hs2 : s ≤ (349 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (697 / 1000) ≤ ((-9024246705539) / 25000000000000) :=
    logU (w := (697 / 1000)) (c := (697 / 500))
      (q := (16608865616919 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-9024246705539) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-18048493412107) / 50000000000000) ≤ Real.log (697 / 1000) :=
    logL (w := (697 / 1000)) (c := (697 / 500))
      (q := (33217731231781 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-18048493412107) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-1492528091841) / 1250000000000) ≤ Real.log (1 - (697 / 1000)) :=
    logL (w := (303 / 1000)) (c := (303 / 250))
      (q := (1922718876471 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-1492528091841) / 1250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (697 / 1000) ^ 2) ≤ ((-66516048722067) / 100000000000000) :=
    logU (w := (514191 / 1000000)) (c := (514191 / 500000))
      (q := (2798669333927 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-66516048722067) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (87 / 125)) ≤ ((-11907275775759) / 10000000000000) :=
    logU (w := (38 / 125)) (c := (152 / 125))
      (q := (9778339177199 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-11907275775759) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-11973282616073) / 10000000000000) ≤ Real.log (1 - (349 / 500)) :=
    logL (w := (151 / 500)) (c := (151 / 125))
      (q := (944830497563 / 5000000000000)) (k := 2) (J := 6)
      (R := ((-11973282616073) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (87 / 125) ^ 2) ≤ ((-66245504020619) / 100000000000000) :=
    logU (w := (8056 / 15625)) (c := (16112 / 15625))
      (q := (24553712283 / 800000000000)) (k := 1) (J := 6)
      (R := ((-66245504020619) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-16696929342953) / 25000000000000) ≤ Real.log (1 - (349 / 500) ^ 2) :=
    logL (w := (128199 / 250000)) (c := (128199 / 125000))
      (q := (2527000684183 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-16696929342953) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (87 / 125) ≤ x → x ≤ (349 / 500) →
      (158714961641187 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (9928252709763 / 6250000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (87 / 125)) (w := (1 / 500))
      (r1 := (334787488203 / 1000000000000))
      (r2 := (1928158587 / 488281250)) (r3 := (37220877 / 7812500))
      (r4 := (72171 / 125000))
      (R := (6854085751 / 10000000000000))
      (NL := (158714961641187 / 100000000000000)) (NU := (9928252709763 / 6250000000000))
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
  exact Dfun_box_pos (a := (87 / 125)) (b := (349 / 500)) (m := (697 / 1000))
    (hh := (1 / 1000)) (K := (72166597833 / 1250000000000))
    (bnd := (23337306863 / 250000000000000))
    (Lu := ((-9024246705539) / 25000000000000))
    (Ll := ((-18048493412107) / 50000000000000))
    (Ml := ((-1492528091841) / 1250000000000))
    (Nu := ((-66516048722067) / 100000000000000))
    (U1 := ((-11907275775759) / 10000000000000))
    (L1 := ((-11973282616073) / 10000000000000))
    (U2 := ((-66245504020619) / 100000000000000))
    (L2 := ((-16696929342953) / 25000000000000))
    (NL := (158714961641187 / 100000000000000))
    (NU := (9928252709763 / 6250000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_073 {s : ℝ} (hs1 : (349 / 500) ≤ s) (hs2 : s ≤ (7 / 10)) :
    0 < Dfun s := by
  have hLu : Real.log (699 / 1000) ≤ ((-35810453674827) / 100000000000000) :=
    logU (w := (699 / 1000)) (c := (699 / 500))
      (q := (33504264381167 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-35810453674827) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-8952613419281) / 25000000000000) ≤ Real.log (699 / 1000) :=
    logL (w := (699 / 1000)) (c := (699 / 500))
      (q := (33504264378871 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8952613419281) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-120064501423329) / 100000000000000) ≤ Real.log (1 - (699 / 1000)) :=
    logL (w := (301 / 1000)) (c := (301 / 250))
      (q := (18564934688661 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-120064501423329) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (699 / 1000) ^ 2) ≤ ((-33530258577173) / 50000000000000) :=
    logU (w := (511399 / 1000000)) (c := (511399 / 500000))
      (q := (140887556353 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-33530258577173) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (349 / 500)) ≤ ((-4789313046429) / 4000000000000) :=
    logU (w := (151 / 500)) (c := (151 / 125))
      (q := (18896609951263 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-4789313046429) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-30099320108149) / 25000000000000) ≤ Real.log (1 - (7 / 10)) :=
    logL (w := (3 / 10)) (c := (6 / 5))
      (q := (9116077839697 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-30099320108149) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (349 / 500) ^ 2) ≤ ((-6678771737181) / 10000000000000) :=
    logU (w := (128199 / 250000)) (c := (128199 / 125000))
      (q := (315875085523 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-6678771737181) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-33667227663189) / 50000000000000) ≤ Real.log (1 - (7 / 10) ^ 2) :=
    logL (w := (51 / 100)) (c := (51 / 50))
      (q := (1980262729617 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-33667227663189) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (349 / 500) ≤ x → x ≤ (7 / 10) →
      (158652746592649 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79391755064601 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (349 / 500)) (w := (1 / 500))
      (r1 := (318934823001 / 1000000000000))
      (r2 := (248591786967 / 62500000000)) (r3 := (596131083 / 125000000))
      (r4 := (308367 / 500000))
      (R := (16345442069 / 25000000000000))
      (NL := (158652746592649 / 100000000000000)) (NU := (79391755064601 / 50000000000000))
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
  exact Dfun_box_pos (a := (349 / 500)) (b := (7 / 10)) (m := (699 / 1000))
    (hh := (1 / 1000)) (K := (5860079749433 / 100000000000000))
    (bnd := (1055703831553 / 10000000000000000))
    (Lu := ((-35810453674827) / 100000000000000))
    (Ll := ((-8952613419281) / 25000000000000))
    (Ml := ((-120064501423329) / 100000000000000))
    (Nu := ((-33530258577173) / 50000000000000))
    (U1 := ((-4789313046429) / 4000000000000))
    (L1 := ((-30099320108149) / 25000000000000))
    (U2 := ((-6678771737181) / 10000000000000))
    (L2 := ((-33667227663189) / 50000000000000))
    (NL := (158652746592649 / 100000000000000))
    (NU := (79391755064601 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_074 {s : ℝ} (hs1 : (7 / 10) ≤ s) (hs2 : s ≤ (351 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (701 / 1000) ≤ ((-35524739194749) / 100000000000000) :=
    logU (w := (701 / 1000)) (c := (701 / 500))
      (q := (6757995772249 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-35524739194749) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-35524739197309) / 100000000000000) ≤ Real.log (701 / 1000) :=
    logL (w := (701 / 1000)) (c := (701 / 500))
      (q := (16894989429343 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-35524739197309) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-120731170559147) / 100000000000000) ≤ Real.log (1 - (701 / 1000)) :=
    logL (w := (299 / 1000)) (c := (299 / 250))
      (q := (17898265552843 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-120731170559147) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (701 / 1000) ^ 2) ≤ ((-16902384804443) / 25000000000000) :=
    logU (w := (508599 / 1000000)) (c := (508599 / 500000))
      (q := (852589419111 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-16902384804443) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (7 / 10)) ≤ ((-7524830027037) / 6250000000000) :=
    logU (w := (3 / 10)) (c := (6 / 5))
      (q := (4558038919849 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-7524830027037) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-4842647169907) / 4000000000000) ≤ Real.log (1 - (351 / 500)) :=
    logL (w := (149 / 500)) (c := (149 / 125))
      (q := (3512651372863 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-4842647169907) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (7 / 10) ^ 2) ≤ ((-8416806915797) / 12500000000000) :=
    logU (w := (51 / 100)) (c := (51 / 50))
      (q := (990131364809 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-8416806915797) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-16971444058139) / 25000000000000) ≤ Real.log (1 - (351 / 500) ^ 2) :=
    logL (w := (126799 / 250000)) (c := (126799 / 125000))
      (q := (1428941823439 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-16971444058139) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (7 / 10) ≤ x → x ≤ (351 / 500) →
      (6343749456017 / 4000000000000) ≤ Npoly x ∧
      Npoly x ≤ (6348725439983 / 4000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (7 / 10)) (w := (1 / 500))
      (r1 := (3029677 / 10000000))
      (r2 := (2003049 / 500000)) (r3 := (238707 / 50000))
      (r4 := (6561 / 10000))
      (R := (2487991983 / 4000000000000))
      (NL := (6343749456017 / 4000000000000)) (NU := (6348725439983 / 4000000000000))
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
  exact Dfun_box_pos (a := (7 / 10)) (b := (351 / 500)) (m := (701 / 1000))
    (hh := (1 / 1000)) (K := (594593950989 / 10000000000000))
    (bnd := (1196822546449 / 10000000000000000))
    (Lu := ((-35524739194749) / 100000000000000))
    (Ll := ((-35524739197309) / 100000000000000))
    (Ml := ((-120731170559147) / 100000000000000))
    (Nu := ((-16902384804443) / 25000000000000))
    (U1 := ((-7524830027037) / 6250000000000))
    (L1 := ((-4842647169907) / 4000000000000))
    (U2 := ((-8416806915797) / 12500000000000))
    (L2 := ((-16971444058139) / 25000000000000))
    (NL := (6343749456017 / 4000000000000))
    (NU := (6348725439983 / 4000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_075 {s : ℝ} (hs1 : (351 / 500) ≤ s) (hs2 : s ≤ (88 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (703 / 1000) ≤ ((-35239838717141) / 100000000000000) :=
    logU (w := (703 / 1000)) (c := (703 / 500))
      (q := (34074879338853 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-35239838717141) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-35239838719991) / 100000000000000) ≤ Real.log (703 / 1000) :=
    logL (w := (703 / 1000)) (c := (703 / 500))
      (q := (8518719834001 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-35239838719991) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-60701157008973) / 50000000000000) ≤ Real.log (1 - (703 / 1000)) :=
    logL (w := (297 / 1000)) (c := (297 / 250))
      (q := (4306780523511 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-60701157008973) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (703 / 1000) ^ 2) ≤ ((-2130099182809) / 3125000000000) :=
    logU (w := (505791 / 1000000)) (c := (505791 / 500000))
      (q := (575772103053 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2130099182809) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (351 / 500)) ≤ ((-15133272405959) / 12500000000000) :=
    logU (w := (149 / 500)) (c := (149 / 125))
      (q := (4390814216079 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-15133272405959) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-121739582465809) / 100000000000000) ≤ Real.log (1 - (88 / 125)) :=
    logL (w := (37 / 125)) (c := (148 / 125))
      (q := (16889853646181 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-121739582465809) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (351 / 500) ^ 2) ≤ ((-33942888116277) / 50000000000000) :=
    logU (w := (126799 / 250000)) (c := (126799 / 125000))
      (q := (17861772793 / 1250000000000)) (k := 1) (J := 6)
      (R := ((-33942888116277) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-8555217453137) / 12500000000000) ≤ Real.log (1 - (88 / 125) ^ 2) :=
    logL (w := (7881 / 15625)) (c := (15762 / 15625))
      (q := (872978430899 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8555217453137) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (351 / 500) ≤ x → x ≤ (88 / 125) →
      (158537953991849 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (1586559438473 / 1000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (351 / 500)) (w := (1 / 500))
      (r1 := (28688599701 / 100000000000))
      (r2 := (252172431333 / 62500000000)) (r3 := (597443283 / 125000000))
      (r4 := (347733 / 500000))
      (R := (2359797109 / 4000000000000))
      (NL := (158537953991849 / 100000000000000)) (NU := (1586559438473 / 1000000000000))
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
  exact Dfun_box_pos (a := (351 / 500)) (b := (88 / 125)) (m := (703 / 1000))
    (hh := (1 / 1000)) (K := (1206180702253 / 20000000000000))
    (bnd := (339154036107 / 2500000000000000))
    (Lu := ((-35239838717141) / 100000000000000))
    (Ll := ((-35239838719991) / 100000000000000))
    (Ml := ((-60701157008973) / 50000000000000))
    (Nu := ((-2130099182809) / 3125000000000))
    (U1 := ((-15133272405959) / 12500000000000))
    (L1 := ((-121739582465809) / 100000000000000))
    (U2 := ((-33942888116277) / 50000000000000))
    (L2 := ((-8555217453137) / 12500000000000))
    (NL := (158537953991849 / 100000000000000))
    (NU := (1586559438473 / 1000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_076 {s : ℝ} (hs1 : (88 / 125) ≤ s) (hs2 : s ≤ (353 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (141 / 200) ≤ ((-1747787380849) / 5000000000000) :=
    logU (w := (141 / 200)) (c := (141 / 100))
      (q := (17179485219507 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1747787380849) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-699114952403) / 2000000000000) ≤ Real.log (141 / 200) :=
    logL (w := (141 / 200)) (c := (141 / 100))
      (q := (6871794087169 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-699114952403) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-122077992264233) / 100000000000000) ≤ Real.log (1 - (141 / 200)) :=
    logL (w := (59 / 200)) (c := (59 / 50))
      (q := (16551443847757 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-122077992264233) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (141 / 200) ^ 2) ≤ ((-68721481190683) / 100000000000000) :=
    logU (w := (20119 / 40000)) (c := (20119 / 20000))
      (q := (593236865311 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-68721481190683) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (88 / 125)) ≤ ((-60869791232903) / 50000000000000) :=
    logU (w := (37 / 125)) (c := (148 / 125))
      (q := (8444926823091 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-60869791232903) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-122417551164347) / 100000000000000) ≤ Real.log (1 - (353 / 500)) :=
    logL (w := (147 / 500)) (c := (147 / 125))
      (q := (16211884947643 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-122417551164347) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (88 / 125) ^ 2) ≤ ((-34220869812547) / 50000000000000) :=
    logU (w := (7881 / 15625)) (c := (15762 / 15625))
      (q := (8729784309 / 1000000000000)) (k := 1) (J := 6)
      (R := ((-34220869812547) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-34501203128699) / 50000000000000) ≤ Real.log (1 - (353 / 500) ^ 2) :=
    logL (w := (125391 / 250000)) (c := (125391 / 125000))
      (q := (312311798597 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-34501203128699) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (88 / 125) ≤ x → x ≤ (353 / 500) →
      (79242711160481 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158596956576029 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (88 / 125)) (w := (1 / 500))
      (r1 := (6767239607 / 25000000000))
      (r2 := (3968216001 / 976562500)) (r3 := (18692451 / 3906250))
      (r4 := (45927 / 62500))
      (R := (55767127533 / 100000000000000))
      (NL := (79242711160481 / 50000000000000)) (NU := (158596956576029 / 100000000000000))
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
  exact Dfun_box_pos (a := (88 / 125)) (b := (353 / 500)) (m := (141 / 200))
    (hh := (1 / 1000)) (K := (611496813401 / 10000000000000))
    (bnd := (1534851473391 / 10000000000000000))
    (Lu := ((-1747787380849) / 5000000000000))
    (Ll := ((-699114952403) / 2000000000000))
    (Ml := ((-122077992264233) / 100000000000000))
    (Nu := ((-68721481190683) / 100000000000000))
    (U1 := ((-60869791232903) / 50000000000000))
    (L1 := ((-122417551164347) / 100000000000000))
    (U2 := ((-34220869812547) / 50000000000000))
    (L2 := ((-34501203128699) / 50000000000000))
    (NL := (79242711160481 / 50000000000000))
    (NU := (158596956576029 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_077 {s : ℝ} (hs1 : (353 / 500) ≤ s) (hs2 : s ≤ (177 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (707 / 1000) ≤ ((-8668115327137) / 25000000000000) :=
    logU (w := (707 / 1000)) (c := (707 / 500))
      (q := (17321128373723 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-8668115327137) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3467246131207) / 10000000000000) ≤ Real.log (707 / 1000) :=
    logL (w := (707 / 1000)) (c := (707 / 500))
      (q := (1385690269757 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-3467246131207) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-122758266996509) / 100000000000000) ≤ Real.log (1 - (707 / 1000)) :=
    logL (w := (293 / 1000)) (c := (293 / 250))
      (q := (15871169115481 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-122758266996509) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (707 / 1000) ^ 2) ≤ ((-17321130653819) / 25000000000000) :=
    logU (w := (500151 / 1000000)) (c := (500151 / 500000))
      (q := (15097720359 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-17321130653819) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (353 / 500)) ≤ ((-15302193895543) / 12500000000000) :=
    logU (w := (147 / 500)) (c := (147 / 125))
      (q := (4052971236911 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-15302193895543) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-123100147671387) / 100000000000000) ≤ Real.log (1 - (177 / 250)) :=
    logL (w := (73 / 250)) (c := (146 / 125))
      (q := (15529288440603 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-123100147671387) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (353 / 500) ^ 2) ≤ ((-17250601564349) / 25000000000000) :=
    logU (w := (125391 / 250000)) (c := (125391 / 125000))
      (q := (156155899299 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-17250601564349) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-34783929364063) / 50000000000000) ≤ Real.log (1 - (177 / 250) ^ 2) :=
    logL (w := (31171 / 62500)) (c := (31171 / 15625))
      (q := (8632697172983 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-34783929364063) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (353 / 500) ≤ x → x ≤ (177 / 250) →
      (19804520546253 / 12500000000000) ≤ Npoly x ∧
      Npoly x ≤ (158541197114607 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (353 / 500)) (w := (1 / 500))
      (r1 := (254378324501 / 1000000000000))
      (r2 := (255761421291 / 62500000000)) (r3 := (598912947 / 125000000))
      (r4 := (387099 / 500000))
      (R := (52516372291 / 100000000000000))
      (NL := (19804520546253 / 12500000000000)) (NU := (158541197114607 / 100000000000000))
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
  exact Dfun_box_pos (a := (353 / 500)) (b := (177 / 250)) (m := (707 / 1000))
    (hh := (1 / 1000)) (K := (3099064867657 / 50000000000000))
    (bnd := (865647240739 / 5000000000000000))
    (Lu := ((-8668115327137) / 25000000000000))
    (Ll := ((-3467246131207) / 10000000000000))
    (Ml := ((-122758266996509) / 100000000000000))
    (Nu := ((-17321130653819) / 25000000000000))
    (U1 := ((-15302193895543) / 12500000000000))
    (L1 := ((-123100147671387) / 100000000000000))
    (U2 := ((-17250601564349) / 25000000000000))
    (L2 := ((-34783929364063) / 50000000000000))
    (NL := (19804520546253 / 12500000000000))
    (NU := (158541197114607 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_078 {s : ℝ} (hs1 : (177 / 250) ≤ s) (hs2 : s ≤ (71 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (709 / 1000) ≤ ((-537343363203) / 1562500000000) :=
    logU (w := (709 / 1000)) (c := (709 / 500))
      (q := (17462371405501 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-537343363203) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-34389975248899) / 100000000000000) ≤ Real.log (709 / 1000) :=
    logL (w := (709 / 1000)) (c := (709 / 500))
      (q := (4365592850887 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-34389975248899) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-61721600590533) / 50000000000000) ≤ Real.log (1 - (709 / 1000)) :=
    logL (w := (291 / 1000)) (c := (291 / 250))
      (q := (3796558732731 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-61721600590533) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (709 / 1000) ^ 2) ≤ ((-87315450763) / 125000000000) :=
    logU (w := (497319 / 1000000)) (c := (497319 / 250000))
      (q := (17194268875397 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-87315450763) / 125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (177 / 250)) ≤ ((-15387518458923) / 12500000000000) :=
    logU (w := (73 / 250)) (c := (146 / 125))
      (q := (3882322110151 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-15387518458923) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-123787435600163) / 100000000000000) ≤ Real.log (1 - (71 / 100)) :=
    logL (w := (29 / 100)) (c := (29 / 25))
      (q := (14842000511827 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-123787435600163) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (177 / 250) ^ 2) ≤ ((-69567837967879) / 100000000000000) :=
    logU (w := (31171 / 62500)) (c := (31171 / 15625))
      (q := (69061598144109 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-69567837967879) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-7013811715459) / 10000000000000) ≤ Real.log (1 - (71 / 100) ^ 2) :=
    logL (w := (4959 / 10000)) (c := (4959 / 2500))
      (q := (342456594787 / 500000000000)) (k := 2) (J := 6)
      (R := ((-7013811715459) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (177 / 250) ≤ x → x ≤ (71 / 100) →
      (158390203151023 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (15848868841859 / 10000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (177 / 250)) (w := (1 / 500))
      (r1 := (118976036403 / 500000000000))
      (r2 := (32194917639 / 7812500000)) (r3 := (149926707 / 31250000))
      (r4 := (203391 / 250000))
      (R := (49242633783 / 100000000000000))
      (NL := (158390203151023 / 100000000000000)) (NU := (15848868841859 / 10000000000000))
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
  exact Dfun_box_pos (a := (177 / 250)) (b := (71 / 100)) (m := (709 / 1000))
    (hh := (1 / 1000)) (K := (785048185979 / 12500000000000))
    (bnd := (972848093931 / 5000000000000000))
    (Lu := ((-537343363203) / 1562500000000))
    (Ll := ((-34389975248899) / 100000000000000))
    (Ml := ((-61721600590533) / 50000000000000))
    (Nu := ((-87315450763) / 125000000000))
    (U1 := ((-15387518458923) / 12500000000000))
    (L1 := ((-123787435600163) / 100000000000000))
    (U2 := ((-69567837967879) / 100000000000000))
    (L2 := ((-7013811715459) / 10000000000000))
    (NL := (158390203151023 / 100000000000000))
    (NU := (15848868841859 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_079 {s : ℝ} (hs1 : (71 / 100) ≤ s) (hs2 : s ≤ (713 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1423 / 2000) ≤ ((-34037986145213) / 100000000000000) :=
    logU (w := (1423 / 2000)) (c := (1423 / 1000))
      (q := (35276731910781 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-34037986145213) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-6807597229931) / 20000000000000) ≤ Real.log (1423 / 2000) :=
    logL (w := (1423 / 2000)) (c := (1423 / 1000))
      (q := (1763836595317 / 5000000000000)) (k := 1) (J := 6)
      (R := ((-6807597229931) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-621530096517) / 500000000000) ≤ Real.log (1 - (1423 / 2000)) :=
    logL (w := (577 / 2000)) (c := (577 / 500))
      (q := (1432341680859 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-621530096517) / 500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1423 / 2000) ^ 2) ≤ ((-70569001269131) / 100000000000000) :=
    logU (w := (1975071 / 4000000)) (c := (1975071 / 1000000))
      (q := (68060434842857 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-70569001269131) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (71 / 100)) ≤ ((-773671472501) / 625000000000) :=
    logU (w := (29 / 100)) (c := (29 / 25))
      (q := (3710500127957 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-773671472501) / 625000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-124827306322253) / 100000000000000) ≤ Real.log (1 - (713 / 1000)) :=
    logL (w := (287 / 1000)) (c := (287 / 250))
      (q := (13802129789737 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-124827306322253) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (71 / 100) ^ 2) ≤ ((-35069049200233) / 50000000000000) :=
    logU (w := (4959 / 10000)) (c := (4959 / 2500))
      (q := (34245668855761 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-35069049200233) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-71002700311479) / 100000000000000) ≤ Real.log (1 - (713 / 1000) ^ 2) :=
    logL (w := (491631 / 1000000)) (c := (491631 / 250000))
      (q := (67626735800511 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-71002700311479) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (71 / 100) ≤ x → x ≤ (713 / 1000) →
      (158323336628061 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158463678550871 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (71 / 100)) (w := (3 / 1000))
      (r1 := (22141067677 / 100000000000))
      (r2 := (2074877613 / 500000000)) (r3 := (24021603 / 5000000))
      (r4 := (85293 / 100000))
      (R := (14034192281 / 20000000000000))
      (NL := (158323336628061 / 100000000000000)) (NU := (158463678550871 / 100000000000000))
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
  exact Dfun_box_pos (a := (71 / 100)) (b := (713 / 1000)) (m := (1423 / 2000))
    (hh := (3 / 2000)) (K := (4477942704721 / 50000000000000))
    (bnd := (447726513063 / 2000000000000000))
    (Lu := ((-34037986145213) / 100000000000000))
    (Ll := ((-6807597229931) / 20000000000000))
    (Ml := ((-621530096517) / 500000000000))
    (Nu := ((-70569001269131) / 100000000000000))
    (U1 := ((-773671472501) / 625000000000))
    (L1 := ((-124827306322253) / 100000000000000))
    (U2 := ((-35069049200233) / 50000000000000))
    (L2 := ((-71002700311479) / 100000000000000))
    (NL := (158323336628061 / 100000000000000))
    (NU := (158463678550871 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_080 {s : ℝ} (hs1 : (713 / 1000) ≤ s) (hs2 : s ≤ (179 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (1429 / 2000) ≤ ((-33617228161209) / 100000000000000) :=
    logU (w := (1429 / 2000)) (c := (1429 / 1000))
      (q := (7139497978957 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-33617228161209) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-33617228166379) / 100000000000000) ≤ Real.log (1429 / 2000) :=
    logL (w := (1429 / 2000)) (c := (1429 / 1000))
      (q := (2231093118101 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-33617228166379) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-125351324988609) / 100000000000000) ≤ Real.log (1 - (1429 / 2000)) :=
    logL (w := (571 / 2000)) (c := (571 / 500))
      (q := (13278111123381 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-125351324988609) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1429 / 2000) ^ 2) ≤ ((-71439175583833) / 100000000000000) :=
    logU (w := (1957959 / 4000000)) (c := (1957959 / 1000000))
      (q := (13438052105631 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-71439175583833) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (713 / 1000)) ≤ ((-499309225289) / 400000000000) :=
    logU (w := (287 / 1000)) (c := (287 / 250))
      (q := (6901064894869 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-499309225289) / 400000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-25175620816419) / 20000000000000) ≤ Real.log (1 - (179 / 250)) :=
    logL (w := (71 / 250)) (c := (142 / 125))
      (q := (2550266405979 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-25175620816419) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (713 / 1000) ^ 2) ≤ ((-35501342132213) / 50000000000000) :=
    logU (w := (491631 / 1000000)) (c := (491631 / 250000))
      (q := (33813375923781 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-35501342132213) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-71878517544759) / 100000000000000) ≤ Real.log (1 - (179 / 250) ^ 2) :=
    logL (w := (30459 / 62500)) (c := (30459 / 15625))
      (q := (66750918567231 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-71878517544759) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (713 / 1000) ≤ x → x ≤ (179 / 250) →
      (39567032674861 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158393533590173 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (713 / 1000)) (w := (3 / 1000))
      (r1 := (24547791881 / 125000000000))
      (r2 := (2096520616251 / 500000000000)) (r3 := (2407455027 / 500000000))
      (r4 := (911979 / 1000000))
      (R := (15675361341 / 25000000000000))
      (NL := (39567032674861 / 25000000000000)) (NU := (158393533590173 / 100000000000000))
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
  exact Dfun_box_pos (a := (713 / 1000)) (b := (179 / 250)) (m := (1429 / 2000))
    (hh := (3 / 2000)) (K := (2267780295121 / 25000000000000))
    (bnd := (131304296189 / 500000000000000))
    (Lu := ((-33617228161209) / 100000000000000))
    (Ll := ((-33617228166379) / 100000000000000))
    (Ml := ((-125351324988609) / 100000000000000))
    (Nu := ((-71439175583833) / 100000000000000))
    (U1 := ((-499309225289) / 400000000000))
    (L1 := ((-25175620816419) / 20000000000000))
    (U2 := ((-35501342132213) / 50000000000000))
    (L2 := ((-71878517544759) / 100000000000000))
    (NL := (39567032674861 / 25000000000000))
    (NU := (158393533590173 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_081 {s : ℝ} (hs1 : (179 / 250) ≤ s) (hs2 : s ≤ (719 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (287 / 400) ≤ ((-16599116567411) / 50000000000000) :=
    logU (w := (287 / 400)) (c := (287 / 200))
      (q := (9029121230293 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-16599116567411) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-33198233140823) / 100000000000000) ≤ Real.log (287 / 400) :=
    logL (w := (287 / 400)) (c := (287 / 200))
      (q := (9029121228793 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-33198233140823) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-63203836419783) / 50000000000000) ≤ Real.log (1 - (287 / 400)) :=
    logL (w := (113 / 400)) (c := (113 / 100))
      (q := (1527720409053 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-63203836419783) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (287 / 400) ^ 2) ≤ ((-72320698234851) / 100000000000000) :=
    logU (w := (77631 / 160000)) (c := (77631 / 40000))
      (q := (66308737877137 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-72320698234851) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (179 / 250)) ≤ ((-31469526020523) / 25000000000000) :=
    logU (w := (71 / 250)) (c := (142 / 125))
      (q := (1593916503737 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-31469526020523) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-126940060964841) / 100000000000000) ≤ Real.log (1 - (719 / 1000)) :=
    logL (w := (281 / 1000)) (c := (281 / 250))
      (q := (11689375147149 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-126940060964841) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (179 / 250) ^ 2) ≤ ((-17969625968231) / 25000000000000) :=
    logU (w := (30459 / 62500)) (c := (30459 / 15625))
      (q := (8343866529883 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-17969625968231) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-36382899918041) / 50000000000000) ≤ Real.log (1 - (719 / 1000) ^ 2) :=
    logL (w := (483039 / 1000000)) (c := (483039 / 250000))
      (q := (16465909068977 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-36382899918041) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (179 / 250) ≤ x → x ≤ (719 / 1000) →
      (79110275085881 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (6333234328261 / 4000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (179 / 250)) (w := (3 / 1000))
      (r1 := (171093984993 / 1000000000000))
      (r2 := (33097076037 / 7812500000)) (r3 := (150819003 / 31250000))
      (r4 := (242757 / 250000))
      (R := (55154017381 / 100000000000000))
      (NL := (79110275085881 / 50000000000000)) (NU := (6333234328261 / 4000000000000))
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
  exact Dfun_box_pos (a := (179 / 250)) (b := (719 / 1000)) (m := (287 / 400))
    (hh := (3 / 2000)) (K := (229614853951 / 2500000000000))
    (bnd := (30519753183 / 100000000000000))
    (Lu := ((-16599116567411) / 50000000000000))
    (Ll := ((-33198233140823) / 100000000000000))
    (Ml := ((-63203836419783) / 50000000000000))
    (Nu := ((-72320698234851) / 100000000000000))
    (U1 := ((-31469526020523) / 25000000000000))
    (L1 := ((-126940060964841) / 100000000000000))
    (U2 := ((-17969625968231) / 25000000000000))
    (L2 := ((-36382899918041) / 50000000000000))
    (NL := (79110275085881 / 50000000000000))
    (NU := (6333234328261 / 4000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_082 {s : ℝ} (hs1 : (719 / 1000) ≤ s) (hs2 : s ≤ (361 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (1441 / 2000) ≤ ((-32780986354239) / 100000000000000) :=
    logU (w := (1441 / 2000)) (c := (1441 / 1000))
      (q := (7306746340351 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-32780986354239) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-32780986361189) / 100000000000000) ≤ Real.log (1441 / 2000) :=
    logL (w := (1441 / 2000)) (c := (1441 / 1000))
      (q := (18266865847403 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-32780986361189) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-1274752986387) / 1000000000000) ≤ Real.log (1 - (1441 / 2000)) :=
    logL (w := (559 / 2000)) (c := (559 / 500))
      (q := (1115413747329 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-1274752986387) / 1000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1441 / 2000) ^ 2) ≤ ((-73213803936359) / 100000000000000) :=
    logU (w := (1923519 / 4000000)) (c := (1923519 / 1000000))
      (q := (65415632175629 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-73213803936359) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (719 / 1000)) ≤ ((-63470030482419) / 50000000000000) :=
    logU (w := (281 / 1000)) (c := (281 / 250))
      (q := (233787502943 / 2000000000000)) (k := 2) (J := 6)
      (R := ((-63470030482419) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-128013416529151) / 100000000000000) ≤ Real.log (1 - (361 / 500)) :=
    logL (w := (139 / 500)) (c := (139 / 125))
      (q := (10616019582839 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-128013416529151) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (719 / 1000) ^ 2) ≤ ((-72765788240073) / 100000000000000) :=
    logU (w := (483039 / 1000000)) (c := (483039 / 250000))
      (q := (13172729574383 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-72765788240073) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-36832392824187) / 50000000000000) ≤ Real.log (1 - (361 / 500) ^ 2) :=
    logL (w := (119679 / 250000)) (c := (119679 / 62500))
      (q := (507536331747 / 781250000000)) (k := 2) (J := 6)
      (R := ((-36832392824187) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (719 / 1000) ≤ x → x ≤ (361 / 500) →
      (988629208221 / 625000000000) ≤ Npoly x ∧
      Npoly x ≤ (31655146063139 / 20000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (719 / 1000)) (w := (3 / 1000))
      (r1 := (145545016513 / 1000000000000))
      (r2 := (2139957551997 / 500000000000)) (r3 := (2419107363 / 500000000))
      (r4 := (1030077 / 1000000))
      (R := (47528500167 / 100000000000000))
      (NL := (988629208221 / 625000000000)) (NU := (31655146063139 / 20000000000000))
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
  exact Dfun_box_pos (a := (719 / 1000)) (b := (361 / 500)) (m := (1441 / 2000))
    (hh := (3 / 2000)) (K := (4648147017309 / 50000000000000))
    (bnd := (878872750337 / 2500000000000000))
    (Lu := ((-32780986354239) / 100000000000000))
    (Ll := ((-32780986361189) / 100000000000000))
    (Ml := ((-1274752986387) / 1000000000000))
    (Nu := ((-73213803936359) / 100000000000000))
    (U1 := ((-63470030482419) / 50000000000000))
    (L1 := ((-128013416529151) / 100000000000000))
    (U2 := ((-72765788240073) / 100000000000000))
    (L2 := ((-36832392824187) / 50000000000000))
    (NL := (988629208221 / 625000000000))
    (NU := (31655146063139 / 20000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_083 {s : ℝ} (hs1 : (361 / 500) ≤ s) (hs2 : s ≤ (363 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (181 / 250) ≤ ((-16148194329811) / 50000000000000) :=
    logU (w := (181 / 250)) (c := (181 / 125))
      (q := (9254582349093 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-16148194329811) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-16148194333923) / 50000000000000) ≤ Real.log (181 / 250) :=
    logL (w := (181 / 250)) (c := (181 / 125))
      (q := (37018329388149 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-16148194333923) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-257470882653) / 200000000000) ≤ Real.log (1 - (181 / 250)) :=
    logL (w := (69 / 250)) (c := (138 / 125))
      (q := (989399478549 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-257470882653) / 200000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (181 / 250) ^ 2) ≤ ((-1856768101039) / 2500000000000) :=
    logU (w := (29739 / 62500)) (c := (29739 / 15625))
      (q := (16089678017607 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-1856768101039) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (361 / 500)) ≤ ((-32003354132287) / 25000000000000) :=
    logU (w := (139 / 500)) (c := (139 / 125))
      (q := (265400489571 / 2500000000000)) (k := 2) (J := 6)
      (R := ((-32003354132287) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-8091419828713) / 6250000000000) ≤ Real.log (1 - (363 / 500)) :=
    logL (w := (137 / 500)) (c := (137 / 125))
      (q := (4583359426291 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-8091419828713) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (361 / 500) ^ 2) ≤ ((-73664775859053) / 100000000000000) :=
    logU (w := (119679 / 250000)) (c := (119679 / 62500))
      (q := (12992932050587 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-73664775859053) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-74882065691059) / 100000000000000) ≤ Real.log (1 - (363 / 500) ^ 2) :=
    logL (w := (118231 / 250000)) (c := (118231 / 62500))
      (q := (63747370420931 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-74882065691059) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (361 / 500) ≤ x → x ≤ (363 / 500) →
      (39533390173473 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158243245917681 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (361 / 500)) (w := (1 / 250))
      (r1 := (1870855957 / 15625000000))
      (r2 := (270219732723 / 62500000000)) (r3 := (606366243 / 125000000))
      (r4 := (544563 / 500000))
      (R := (27421305947 / 50000000000000))
      (NL := (39533390173473 / 25000000000000)) (NU := (158243245917681 / 100000000000000))
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
  exact Dfun_box_pos (a := (361 / 500)) (b := (363 / 500)) (m := (181 / 250))
    (hh := (1 / 500)) (K := (2994590057001 / 25000000000000))
    (bnd := (2051363444691 / 5000000000000000))
    (Lu := ((-16148194329811) / 50000000000000))
    (Ll := ((-16148194333923) / 50000000000000))
    (Ml := ((-257470882653) / 200000000000))
    (Nu := ((-1856768101039) / 2500000000000))
    (U1 := ((-32003354132287) / 25000000000000))
    (L1 := ((-8091419828713) / 6250000000000))
    (U2 := ((-73664775859053) / 100000000000000))
    (L2 := ((-74882065691059) / 100000000000000))
    (NL := (39533390173473 / 25000000000000))
    (NU := (158243245917681 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_084 {s : ℝ} (hs1 : (363 / 500) ≤ s) (hs2 : s ≤ (73 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (91 / 125) ≤ ((-31745423078521) / 100000000000000) :=
    logU (w := (91 / 125)) (c := (182 / 125))
      (q := (37569294977473 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-31745423078521) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-7936355772113) / 25000000000000) ≤ Real.log (91 / 125) :=
    logL (w := (91 / 125)) (c := (182 / 125))
      (q := (37569294967543 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-7936355772113) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-26039064253723) / 20000000000000) ≤ Real.log (1 - (91 / 125)) :=
    logL (w := (34 / 125)) (c := (136 / 125))
      (q := (67472918747 / 800000000000)) (k := 2) (J := 6)
      (R := ((-26039064253723) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (91 / 125) ^ 2) ≤ ((-9437356773043) / 12500000000000) :=
    logU (w := (7344 / 15625)) (c := (29376 / 15625))
      (q := (15782645481911 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-9437356773043) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (363 / 500)) ≤ ((-25892543451881) / 20000000000000) :=
    logU (w := (137 / 500)) (c := (137 / 125))
      (q := (9166718852583 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-25892543451881) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-65466665999189) / 50000000000000) ≤ Real.log (1 - (73 / 100)) :=
    logL (w := (27 / 100)) (c := (27 / 25))
      (q := (1924026028403 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-65466665999189) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (363 / 500) ^ 2) ≤ ((-18720514485071) / 25000000000000) :=
    logU (w := (118231 / 250000)) (c := (118231 / 62500))
      (q := (7968422271463 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-18720514485071) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-15224239437501) / 20000000000000) ≤ Real.log (1 - (73 / 100) ^ 2) :=
    logL (w := (4671 / 10000)) (c := (4671 / 2500))
      (q := (12501647784897 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-15224239437501) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (363 / 500) ≤ x → x ≤ (73 / 100) →
      (158106450555751 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (39547116407403 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (363 / 500)) (w := (1 / 250))
      (r1 := (84913526967 / 1000000000000))
      (r2 := (273864622401 / 62500000000)) (r3 := (608623227 / 125000000))
      (r4 := (583929 / 500000))
      (R := (4100753693 / 10000000000000))
      (NL := (158106450555751 / 100000000000000)) (NU := (39547116407403 / 25000000000000))
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
  exact Dfun_box_pos (a := (363 / 500)) (b := (73 / 100)) (m := (91 / 125))
    (hh := (1 / 500)) (K := (3029315839741 / 25000000000000))
    (bnd := (4833531621847 / 10000000000000000))
    (Lu := ((-31745423078521) / 100000000000000))
    (Ll := ((-7936355772113) / 25000000000000))
    (Ml := ((-26039064253723) / 20000000000000))
    (Nu := ((-9437356773043) / 12500000000000))
    (U1 := ((-25892543451881) / 20000000000000))
    (L1 := ((-65466665999189) / 50000000000000))
    (U2 := ((-18720514485071) / 25000000000000))
    (L2 := ((-15224239437501) / 20000000000000))
    (NL := (158106450555751 / 100000000000000))
    (NU := (39547116407403 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_085 {s : ℝ} (hs1 : (73 / 100) ≤ s) (hs2 : s ≤ (147 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (293 / 400) ≤ ((-31129193809061) / 100000000000000) :=
    logU (w := (293 / 400)) (c := (293 / 200))
      (q := (38185524246933 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-31129193809061) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-7782298455321) / 25000000000000) ≤ Real.log (293 / 400) :=
    logL (w := (293 / 400)) (c := (293 / 200))
      (q := (38185524234711 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-7782298455321) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-131863571264609) / 100000000000000) ≤ Real.log (1 - (293 / 400)) :=
    logL (w := (107 / 400)) (c := (107 / 100))
      (q := (6765864847381 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-131863571264609) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (293 / 400) ^ 2) ≤ ((-9613378252889) / 12500000000000) :=
    logU (w := (74151 / 160000)) (c := (74151 / 40000))
      (q := (15430602522219 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-9613378252889) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (73 / 100)) ≤ ((-1047466655987) / 800000000000) :=
    logU (w := (27 / 100)) (c := (27 / 25))
      (q := (7696104113613 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-1047466655987) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-132802545299593) / 100000000000000) ≤ Real.log (1 - (147 / 200)) :=
    logL (w := (53 / 200)) (c := (53 / 50))
      (q := (5826890812397 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-132802545299593) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (73 / 100) ^ 2) ≤ ((-76121191107447) / 100000000000000) :=
    logU (w := (4671 / 10000)) (c := (4671 / 2500))
      (q := (62508245004541 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-76121191107447) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-38850904179199) / 50000000000000) ≤ Real.log (1 - (147 / 200) ^ 2) :=
    logL (w := (18391 / 40000)) (c := (18391 / 10000))
      (q := (7615953469199 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-38850904179199) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (73 / 100) ≤ x → x ≤ (147 / 200) →
      (19760570033011 / 12500000000000) ≤ Npoly x ∧
      Npoly x ≤ (39539127337997 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (73 / 100)) (w := (1 / 200))
      (r1 := (4962483997 / 100000000000))
      (r2 := (2220188211 / 500000000)) (r3 := (24441507 / 5000000))
      (r4 := (124659 / 100000))
      (R := (719490879 / 2000000000000))
      (NL := (19760570033011 / 12500000000000)) (NU := (39539127337997 / 25000000000000))
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
  exact Dfun_box_pos (a := (73 / 100)) (b := (147 / 200)) (m := (293 / 400))
    (hh := (1 / 400)) (K := (7406674197827 / 50000000000000))
    (bnd := (2864713500341 / 5000000000000000))
    (Lu := ((-31129193809061) / 100000000000000))
    (Ll := ((-7782298455321) / 25000000000000))
    (Ml := ((-131863571264609) / 100000000000000))
    (Nu := ((-9613378252889) / 12500000000000))
    (U1 := ((-1047466655987) / 800000000000))
    (L1 := ((-132802545299593) / 100000000000000))
    (U2 := ((-76121191107447) / 100000000000000))
    (L2 := ((-38850904179199) / 50000000000000))
    (NL := (19760570033011 / 12500000000000))
    (NU := (39539127337997 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_086 {s : ℝ} (hs1 : (147 / 200) ≤ s) (hs2 : s ≤ (37 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (59 / 80) ≤ ((-30448919076777) / 100000000000000) :=
    logU (w := (59 / 80)) (c := (59 / 40))
      (q := (38865798979217 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-30448919076777) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3806114886511) / 12500000000000) ≤ Real.log (59 / 80) :=
    logL (w := (59 / 80)) (c := (59 / 40))
      (q := (38865798963907 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-3806114886511) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-133750419695047) / 100000000000000) ≤ Real.log (1 - (59 / 80)) :=
    logL (w := (21 / 80)) (c := (21 / 20))
      (q := (4879016416943 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-133750419695047) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (59 / 80) ^ 2) ≤ ((-78505689826557) / 100000000000000) :=
    logU (w := (2919 / 6400)) (c := (2919 / 1600))
      (q := (60123746285431 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-78505689826557) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (147 / 200)) ≤ ((-13280254529959) / 10000000000000) :=
    logU (w := (53 / 200)) (c := (53 / 50))
      (q := (2913445406199 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-13280254529959) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-67353682398331) / 50000000000000) ≤ Real.log (1 - (37 / 50)) :=
    logL (w := (13 / 50)) (c := (26 / 25))
      (q := (30641182151 / 781250000000)) (k := 2) (J := 6)
      (R := ((-67353682398331) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (147 / 200) ^ 2) ≤ ((-38850901966041) / 50000000000000) :=
    logU (w := (18391 / 40000)) (c := (18391 / 10000))
      (q := (30463816089953 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-38850901966041) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-79318856624131) / 100000000000000) ≤ Real.log (1 - (37 / 50) ^ 2) :=
    logL (w := (1131 / 2500)) (c := (1131 / 625))
      (q := (59310579487859 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-79318856624131) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (147 / 200) ≤ x → x ≤ (37 / 50) →
      (79046555679051 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158120657665933 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (147 / 200)) (w := (1 / 200))
      (r1 := (4853817549 / 1000000000000))
      (r2 := (18055571409 / 4000000000)) (r3 := (98284347 / 20000000))
      (r4 := (269001 / 200000))
      (R := (2754630783 / 20000000000000))
      (NL := (79046555679051 / 50000000000000)) (NU := (158120657665933 / 100000000000000))
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
  exact Dfun_box_pos (a := (147 / 200)) (b := (37 / 50)) (m := (59 / 80))
    (hh := (1 / 400)) (K := (3743899213997 / 25000000000000))
    (bnd := (68131218183 / 100000000000000))
    (Lu := ((-30448919076777) / 100000000000000))
    (Ll := ((-3806114886511) / 12500000000000))
    (Ml := ((-133750419695047) / 100000000000000))
    (Nu := ((-78505689826557) / 100000000000000))
    (U1 := ((-13280254529959) / 10000000000000))
    (L1 := ((-67353682398331) / 50000000000000))
    (U2 := ((-38850901966041) / 50000000000000))
    (L2 := ((-79318856624131) / 100000000000000))
    (NL := (79046555679051 / 50000000000000))
    (NU := (158120657665933 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_087 {s : ℝ} (hs1 : (37 / 50) ≤ s) (hs2 : s ≤ (149 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (297 / 400) ≤ ((-29773240830477) / 100000000000000) :=
    logU (w := (297 / 400)) (c := (297 / 200))
      (q := (39541477225517 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-29773240830477) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-29773240849551) / 100000000000000) ≤ Real.log (297 / 400) :=
    logL (w := (297 / 400)) (c := (297 / 200))
      (q := (9885369301611 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-29773240849551) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-33918388971959) / 25000000000000) ≤ Real.log (1 - (297 / 400)) :=
    logL (w := (103 / 400)) (c := (103 / 100))
      (q := (1477940112077 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-33918388971959) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (297 / 400) ^ 2) ≤ ((-10017683688409) / 12500000000000) :=
    logU (w := (71791 / 160000)) (c := (71791 / 40000))
      (q := (14621991651179 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-10017683688409) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (37 / 50)) ≤ ((-134707364796659) / 100000000000000) :=
    logU (w := (13 / 50)) (c := (26 / 25))
      (q := (3922071315329 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-134707364796659) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-136649173382373) / 100000000000000) ≤ Real.log (1 - (149 / 200)) :=
    logL (w := (51 / 200)) (c := (51 / 50))
      (q := (1980262729617 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-136649173382373) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (37 / 50) ^ 2) ≤ ((-39659426727641) / 50000000000000) :=
    logU (w := (1131 / 2500)) (c := (1131 / 625))
      (q := (29655291328353 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-39659426727641) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-4048686001607) / 5000000000000) ≤ Real.log (1 - (149 / 200) ^ 2) :=
    logL (w := (17799 / 40000)) (c := (17799 / 10000))
      (q := (1153114321597 / 2000000000000)) (k := 2) (J := 6)
      (R := ((-4048686001607) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (37 / 50) ≤ x → x ≤ (149 / 200) →
      (15808394526767 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79073831214549 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (37 / 50)) (w := (1 / 200))
      (r1 := (254089763 / 6250000000))
      (r2 := (286738299 / 62500000)) (r3 := (6177627 / 1250000))
      (r4 := (72171 / 50000))
      (R := (15929290357 / 50000000000000))
      (NL := (15808394526767 / 10000000000000)) (NU := (79073831214549 / 50000000000000))
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
  exact Dfun_box_pos (a := (37 / 50)) (b := (149 / 200)) (m := (297 / 400))
    (hh := (1 / 400)) (K := (15145867744401 / 100000000000000))
    (bnd := (319436862701 / 400000000000000))
    (Lu := ((-29773240830477) / 100000000000000))
    (Ll := ((-29773240849551) / 100000000000000))
    (Ml := ((-33918388971959) / 25000000000000))
    (Nu := ((-10017683688409) / 12500000000000))
    (U1 := ((-134707364796659) / 100000000000000))
    (L1 := ((-136649173382373) / 100000000000000))
    (U2 := ((-39659426727641) / 50000000000000))
    (L2 := ((-4048686001607) / 5000000000000))
    (NL := (15808394526767 / 10000000000000))
    (NU := (79073831214549 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_088 {s : ℝ} (hs1 : (149 / 200) ≤ s) (hs2 : s ≤ (3 / 4)) :
    0 < Dfun s := by
  have hLu : Real.log (299 / 400) ≤ ((-5820419474333) / 20000000000000) :=
    logU (w := (299 / 400)) (c := (299 / 200))
      (q := (40212620684329 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5820419474333) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-29102097395299) / 100000000000000) ≤ Real.log (299 / 400) :=
    logL (w := (299 / 400)) (c := (299 / 200))
      (q := (5026577582587 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-29102097395299) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-68817201513337) / 50000000000000) ≤ Real.log (1 - (299 / 400)) :=
    logL (w := (101 / 400)) (c := (101 / 100))
      (q := (248758271329 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-68817201513337) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (299 / 400) ^ 2) ≤ ((-81815783504037) / 100000000000000) :=
    logU (w := (70599 / 160000)) (c := (70599 / 40000))
      (q := (56813652607951 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-81815783504037) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (149 / 200)) ≤ ((-13664917338237) / 10000000000000) :=
    logU (w := (51 / 200)) (c := (51 / 50))
      (q := (990131364809 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-13664917338237) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-13862943611199) / 10000000000000) ≤ Real.log (1 - (3 / 4)) :=
    logL (w := (1 / 4)) (c := 1)
      (q := 0) (k := 2) (J := 6)
      (R := ((-13862943611199) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (149 / 200) ^ 2) ≤ ((-80973717804491) / 100000000000000) :=
    logU (w := (17799 / 40000)) (c := (17799 / 10000))
      (q := (57655718307497 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-80973717804491) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-41333929422771) / 50000000000000) ≤ Real.log (1 - (3 / 4) ^ 2) :=
    logL (w := (7 / 16)) (c := (7 / 4))
      (q := (3497598579153 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-41333929422771) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (149 / 200) ≤ x → x ≤ (3 / 4) →
      (2470195200421 / 1562500000000) ≤ Npoly x ∧
      Npoly x ≤ (158202832031251 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (149 / 200)) (w := (1 / 200))
      (r1 := (5431492597 / 62500000000))
      (r2 := (18648662967 / 4000000000)) (r3 := (99439083 / 20000000))
      (r4 := (308367 / 200000))
      (R := (55169602153 / 100000000000000))
      (NL := (2470195200421 / 1562500000000)) (NU := (158202832031251 / 100000000000000))
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
  exact Dfun_box_pos (a := (149 / 200)) (b := (3 / 4)) (m := (299 / 400))
    (hh := (1 / 400)) (K := (1531444374577 / 10000000000000))
    (bnd := (9243847460133 / 10000000000000000))
    (Lu := ((-5820419474333) / 20000000000000))
    (Ll := ((-29102097395299) / 100000000000000))
    (Ml := ((-68817201513337) / 50000000000000))
    (Nu := ((-81815783504037) / 100000000000000))
    (U1 := ((-13664917338237) / 10000000000000))
    (L1 := ((-13862943611199) / 10000000000000))
    (U2 := ((-80973717804491) / 100000000000000))
    (L2 := ((-41333929422771) / 50000000000000))
    (NL := (2470195200421 / 1562500000000))
    (NU := (158202832031251 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_089 {s : ℝ} (hs1 : (3 / 4) ≤ s) (hs2 : s ≤ (189 / 250)) :
    0 < Dfun s := by
  have hLu : Real.log (753 / 1000) ≤ ((-1418450255907) / 5000000000000) :=
    logU (w := (753 / 1000)) (c := (753 / 500))
      (q := (20472856468927 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1418450255907) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-14184502573943) / 50000000000000) ≤ Real.log (753 / 1000) :=
    logL (w := (753 / 1000)) (c := (753 / 500))
      (q := (40945712908109 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-14184502573943) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-139836711603337) / 100000000000000) ≤ Real.log (1 - (753 / 1000)) :=
    logL (w := (247 / 1000)) (c := (247 / 125))
      (q := (8513430320581 / 12500000000000)) (k := 3) (J := 6)
      (R := ((-139836711603337) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (753 / 1000) ^ 2) ≤ ((-83703833635351) / 100000000000000) :=
    logU (w := (432991 / 1000000)) (c := (432991 / 250000))
      (q := (54925602476637 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-83703833635351) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (3 / 4)) ≤ ((-34657359027997) / 25000000000000) :=
    logU (w := (1 / 4)) (c := 1)
      (q := 0) (k := 2) (J := 6)
      (R := ((-34657359027997) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-28211743855559) / 20000000000000) ≤ Real.log (1 - (189 / 250)) :=
    logL (w := (61 / 250)) (c := (244 / 125))
      (q := (6688543489019 / 10000000000000)) (k := 3) (J := 6)
      (R := ((-28211743855559) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (3 / 4) ^ 2) ≤ ((-82667857310373) / 100000000000000) :=
    logU (w := (7 / 16)) (c := (7 / 4))
      (q := (11192315760323 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-82667857310373) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-84754856796993) / 100000000000000) ≤ Real.log (1 - (189 / 250) ^ 2) :=
    logL (w := (26779 / 62500)) (c := (26779 / 15625))
      (q := (53874579314997 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-84754856796993) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (3 / 4) ≤ x → x ≤ (189 / 250) →
      (79052665535161 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (79150166496089 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (3 / 4)) (w := (3 / 500))
      (r1 := (171391 / 1280000))
      (r2 := (757917 / 160000)) (r3 := (200151 / 40000))
      (r4 := (6561 / 4000))
      (R := (3046905029 / 3125000000000))
      (NL := (79052665535161 / 50000000000000)) (NU := (79150166496089 / 50000000000000))
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
  exact Dfun_box_pos (a := (3 / 4)) (b := (189 / 250)) (m := (753 / 1000))
    (hh := (3 / 1000)) (K := (1127085000777 / 6250000000000))
    (bnd := (10720145170229 / 10000000000000000))
    (Lu := ((-1418450255907) / 5000000000000))
    (Ll := ((-14184502573943) / 50000000000000))
    (Ml := ((-139836711603337) / 100000000000000))
    (Nu := ((-83703833635351) / 100000000000000))
    (U1 := ((-34657359027997) / 25000000000000))
    (L1 := ((-28211743855559) / 20000000000000))
    (U2 := ((-82667857310373) / 100000000000000))
    (L2 := ((-84754856796993) / 100000000000000))
    (NL := (79052665535161 / 50000000000000))
    (NU := (79150166496089 / 50000000000000))
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
