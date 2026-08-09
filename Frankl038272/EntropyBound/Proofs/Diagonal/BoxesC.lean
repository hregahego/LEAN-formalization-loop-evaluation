/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Proofs.Diagonal.Deriv

/-!
# Stage G item G4 — box certificates for `diagonal_middle`, part C

Machine-generated per-box positivity certificates, boxes 90–133 of the partition of
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


theorem box_090 {s : ℝ} (hs1 : (189 / 250) ≤ s) (hs2 : s ≤ (19 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (379 / 500) ≤ ((-2770718933387) / 10000000000000) :=
    logU (w := (379 / 500)) (c := (379 / 250))
      (q := (10401882180531 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-2770718933387) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-13853594685173) / 50000000000000) ≤ Real.log (379 / 500) :=
    logL (w := (379 / 500)) (c := (379 / 250))
      (q := (41607528685649 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-13853594685173) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-70940883614207) / 50000000000000) ≤ Real.log (1 - (379 / 500)) :=
    logL (w := (121 / 500)) (c := (242 / 125))
      (q := (66062386939571 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-70940883614207) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (379 / 500) ^ 2) ≤ ((-85464075352413) / 100000000000000) :=
    logU (w := (106359 / 250000)) (c := (106359 / 62500))
      (q := (2126614430383 / 4000000000000)) (k := 2) (J := 6)
      (R := ((-85464075352413) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (189 / 250)) ≤ ((-70529352631651) / 50000000000000) :=
    logU (w := (61 / 250)) (c := (244 / 125))
      (q := (1672136222617 / 2500000000000)) (k := 3) (J := 6)
      (R := ((-70529352631651) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-71355822894513) / 50000000000000) ≤ Real.log (1 - (19 / 25)) :=
    logL (w := (6 / 25)) (c := (48 / 25))
      (q := (65232508378959 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-71355822894513) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (189 / 250) ^ 2) ≤ ((-10594356980369) / 12500000000000) :=
    logU (w := (26779 / 62500)) (c := (26779 / 15625))
      (q := (13468645067259 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-10594356980369) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-689442042699) / 800000000000) ≤ Real.log (1 - (19 / 25) ^ 2) :=
    logL (w := (264 / 625)) (c := (1056 / 625))
      (q := (10489836154923 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-689442042699) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (189 / 250) ≤ x → x ≤ (19 / 25) →
      (79108031432369 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158384603119617 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (189 / 250)) (w := (1 / 250))
      (r1 := (23910605517 / 125000000000))
      (r2 := (37714156227 / 7812500000)) (r3 := (157642443 / 31250000))
      (r4 := (439587 / 250000))
      (R := (84270127439 / 100000000000000))
      (NL := (79108031432369 / 50000000000000)) (NU := (158384603119617 / 100000000000000))
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
  exact Dfun_box_pos (a := (189 / 250)) (b := (19 / 25)) (m := (379 / 500))
    (hh := (1 / 500)) (K := (13116439627773 / 100000000000000))
    (bnd := (1517991482303 / 1250000000000000))
    (Lu := ((-2770718933387) / 10000000000000))
    (Ll := ((-13853594685173) / 50000000000000))
    (Ml := ((-70940883614207) / 50000000000000))
    (Nu := ((-85464075352413) / 100000000000000))
    (U1 := ((-70529352631651) / 50000000000000))
    (L1 := ((-71355822894513) / 50000000000000))
    (U2 := ((-10594356980369) / 12500000000000))
    (L2 := ((-689442042699) / 800000000000))
    (NL := (79108031432369 / 50000000000000))
    (NU := (158384603119617 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_091 {s : ℝ} (hs1 : (19 / 25) ≤ s) (hs2 : s ≤ (767 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1527 / 2000) ≤ ((-1686513464513) / 6250000000000) :=
    logU (w := (1527 / 2000)) (c := (1527 / 1000))
      (q := (21165251311893 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-1686513464513) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-13492107738807) / 50000000000000) ≤ Real.log (1527 / 2000) :=
    logL (w := (1527 / 2000)) (c := (1527 / 1000))
      (q := (42330502578381 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-13492107738807) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-72090357413387) / 50000000000000) ≤ Real.log (1 - (1527 / 2000)) :=
    logL (w := (473 / 2000)) (c := (473 / 250))
      (q := (63763439341211 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-72090357413387) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1527 / 2000) ^ 2) ≤ ((-87450660033417) / 100000000000000) :=
    logU (w := (1668271 / 4000000)) (c := (1668271 / 1000000))
      (q := (51178776078571 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-87450660033417) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (19 / 25)) ≤ ((-71355817745121) / 50000000000000) :=
    logU (w := (6 / 25)) (c := (48 / 25))
      (q := (3261625933887 / 5000000000000)) (k := 3) (J := 6)
      (R := ((-71355817745121) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-145671688305917) / 100000000000000) ≤ Real.log (1 - (767 / 1000)) :=
    logL (w := (233 / 1000)) (c := (233 / 125))
      (q := (15568116465517 / 25000000000000)) (k := 3) (J := 6)
      (R := ((-145671688305917) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (19 / 25) ^ 2) ≤ ((-43090127327931) / 50000000000000) :=
    logU (w := (264 / 625)) (c := (1056 / 625))
      (q := (26224590728063 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-43090127327931) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-3549734542771) / 4000000000000) ≤ Real.log (1 - (767 / 1000) ^ 2) :=
    logL (w := (411711 / 1000000)) (c := (411711 / 250000))
      (q := (9977214508543 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-3549734542771) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (19 / 25) ≤ x → x ≤ (767 / 1000) →
      (158199374164851 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (158569832074381 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (19 / 25)) (w := (7 / 1000))
      (r1 := (22475267 / 97656250))
      (r2 := (19094211 / 3906250)) (r3 := (1585413 / 312500))
      (r4 := (45927 / 25000))
      (R := (37045790953 / 20000000000000))
      (NL := (158199374164851 / 100000000000000)) (NU := (158569832074381 / 100000000000000))
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
  exact Dfun_box_pos (a := (19 / 25)) (b := (767 / 1000)) (m := (1527 / 2000))
    (hh := (7 / 2000)) (K := (10459415329471 / 50000000000000))
    (bnd := (172418325079 / 125000000000000))
    (Lu := ((-1686513464513) / 6250000000000))
    (Ll := ((-13492107738807) / 50000000000000))
    (Ml := ((-72090357413387) / 50000000000000))
    (Nu := ((-87450660033417) / 100000000000000))
    (U1 := ((-71355817745121) / 50000000000000))
    (L1 := ((-145671688305917) / 100000000000000))
    (U2 := ((-43090127327931) / 50000000000000))
    (L2 := ((-3549734542771) / 4000000000000))
    (NL := (158199374164851 / 100000000000000))
    (NU := (158569832074381 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_092 {s : ℝ} (hs1 : (767 / 1000) ≤ s) (hs2 : s ≤ (31 / 40)) :
    0 < Dfun s := by
  have hLu : Real.log (771 / 1000) ≤ ((-26006690541689) / 100000000000000) :=
    logU (w := (771 / 1000)) (c := (771 / 500))
      (q := (8661605502861 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-26006690541689) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-26006690602369) / 100000000000000) ≤ Real.log (771 / 1000) :=
    logL (w := (771 / 1000)) (c := (771 / 500))
      (q := (21654013726813 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-26006690602369) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-73701665803727) / 50000000000000) ≤ Real.log (1 - (771 / 1000)) :=
    logL (w := (229 / 1000)) (c := (229 / 125))
      (q := (60540822560531 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-73701665803727) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (771 / 1000) ^ 2) ≤ ((-90248891661751) / 100000000000000) :=
    logU (w := (405559 / 1000000)) (c := (405559 / 250000))
      (q := (48380544450237 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-90248891661751) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (767 / 1000)) ≤ ((-145671682503799) / 100000000000000) :=
    logU (w := (233 / 1000)) (c := (233 / 125))
      (q := (62272471664183 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-145671682503799) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-74582745247063) / 50000000000000) ≤ Real.log (1 - (31 / 40)) :=
    logL (w := (9 / 40)) (c := (9 / 5))
      (q := (58778663673859 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-74582745247063) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (767 / 1000) ^ 2) ≤ ((-22185840801593) / 25000000000000) :=
    logU (w := (411711 / 1000000)) (c := (411711 / 250000))
      (q := (3117879556601 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-22185840801593) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-22946361387113) / 25000000000000) ≤ Real.log (1 - (31 / 40) ^ 2) :=
    logL (w := (639 / 1600)) (c := (639 / 400))
      (q := (23421995281769 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-22946361387113) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (767 / 1000) ≤ x → x ≤ (31 / 40) →
      (158298136427471 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (15884152772129 / 10000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (767 / 1000)) (w := (1 / 125))
      (r1 := (37416091539 / 125000000000))
      (r2 := (2497605686829 / 500000000000)) (r3 := (2563344387 / 500000000))
      (r4 := (1974861 / 1000000))
      (R := (271695646909 / 100000000000000))
      (NL := (158298136427471 / 100000000000000)) (NU := (15884152772129 / 10000000000000))
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
  exact Dfun_box_pos (a := (767 / 1000)) (b := (31 / 40)) (m := (771 / 1000))
    (hh := (1 / 250)) (K := (23714533927829 / 100000000000000))
    (bnd := (16173692355537 / 10000000000000000))
    (Lu := ((-26006690541689) / 100000000000000))
    (Ll := ((-26006690602369) / 100000000000000))
    (Ml := ((-73701665803727) / 50000000000000))
    (Nu := ((-90248891661751) / 100000000000000))
    (U1 := ((-145671682503799) / 100000000000000))
    (L1 := ((-74582745247063) / 50000000000000))
    (U2 := ((-22185840801593) / 25000000000000))
    (L2 := ((-22946361387113) / 25000000000000))
    (NL := (158298136427471 / 100000000000000))
    (NU := (15884152772129 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_093 {s : ℝ} (hs1 : (31 / 40) ≤ s) (hs2 : s ≤ (39 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (311 / 400) ≤ ((-25167163492621) / 100000000000000) :=
    logU (w := (311 / 400)) (c := (311 / 200))
      (q := (44147554563373 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-25167163492621) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-629179089251) / 2500000000000) ≤ Real.log (311 / 400) :=
    logL (w := (311 / 400)) (c := (311 / 200))
      (q := (8829510897191 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-629179089251) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-150282819955483) / 100000000000000) ≤ Real.log (1 - (311 / 400)) :=
    logL (w := (89 / 400)) (c := (89 / 50))
      (q := (28830667106251 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-150282819955483) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (311 / 400) ^ 2) ≤ ((-46381014733807) / 50000000000000) :=
    logU (w := (63279 / 160000)) (c := (63279 / 40000))
      (q := (22933703322187 / 50000000000000)) (k := 2) (J := 6)
      (R := ((-46381014733807) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (31 / 40)) ≤ ((-37291371915331) / 25000000000000) :=
    logU (w := (9 / 40)) (c := (9 / 5))
      (q := (29389333253329 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-37291371915331) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-1892659687449) / 1250000000000) ≤ Real.log (1 - (39 / 50)) :=
    logL (w := (11 / 50)) (c := (44 / 25))
      (q := (11306275834413 / 20000000000000)) (k := 3) (J := 6)
      (R := ((-1892659687449) / 1250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (31 / 40) ^ 2) ≤ ((-91785445384429) / 100000000000000) :=
    logU (w := (639 / 1600)) (c := (639 / 400))
      (q := (46843990727559 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-91785445384429) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-93751436927579) / 100000000000000) ≤ Real.log (1 - (39 / 50) ^ 2) :=
    logL (w := (979 / 2500)) (c := (979 / 625))
      (q := (44877999184411 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-93751436927579) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (31 / 40) ≤ x → x ≤ (39 / 50) →
      (15863854482389 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (159044510618689 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (31 / 40)) (w := (1 / 200))
      (r1 := (47530070459 / 125000000000))
      (r2 := (163808973 / 32000000)) (r3 := (4153923 / 800000))
      (r4 := (85293 / 40000))
      (R := (202982897399 / 100000000000000))
      (NL := (15863854482389 / 10000000000000)) (NU := (159044510618689 / 100000000000000))
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
  exact Dfun_box_pos (a := (31 / 40)) (b := (39 / 50)) (m := (311 / 400))
    (hh := (1 / 400)) (K := (8131648819053 / 50000000000000))
    (bnd := (18348455837283 / 10000000000000000))
    (Lu := ((-25167163492621) / 100000000000000))
    (Ll := ((-629179089251) / 2500000000000))
    (Ml := ((-150282819955483) / 100000000000000))
    (Nu := ((-46381014733807) / 50000000000000))
    (U1 := ((-37291371915331) / 25000000000000))
    (L1 := ((-1892659687449) / 1250000000000))
    (U2 := ((-91785445384429) / 100000000000000))
    (L2 := ((-93751436927579) / 100000000000000))
    (NL := (15863854482389 / 10000000000000))
    (NU := (159044510618689 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_094 {s : ℝ} (hs1 : (39 / 50) ≤ s) (hs2 : s ≤ (789 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1569 / 2000) ≤ ((-4854174136113) / 20000000000000) :=
    logU (w := (1569 / 2000)) (c := (1569 / 1000))
      (q := (45043847375429 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-4854174136113) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-24270870780449) / 100000000000000) ≤ Real.log (1569 / 2000) :=
    logL (w := (1569 / 2000)) (c := (1569 / 1000))
      (q := (22521923637773 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-24270870780449) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-153479438031951) / 100000000000000) ≤ Real.log (1 - (1569 / 2000)) :=
    logL (w := (431 / 2000)) (c := (431 / 250))
      (q := (27232358068017 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-153479438031951) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1569 / 2000) ^ 2) ≤ ((-95565610548849) / 100000000000000) :=
    logU (w := (1538239 / 4000000)) (c := (1538239 / 1000000))
      (q := (43063825563139 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-95565610548849) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (39 / 50)) ≤ ((-1211302186029) / 800000000000) :=
    logU (w := (11 / 50)) (c := (44 / 25))
      (q := (56531380914357 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-1211302186029) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-155589715213757) / 100000000000000) ≤ Real.log (1 - (789 / 1000)) :=
    logL (w := (211 / 1000)) (c := (211 / 125))
      (q := (13088609738557 / 25000000000000)) (k := 3) (J := 6)
      (R := ((-155589715213757) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (39 / 50) ^ 2) ≤ ((-18750287366451) / 20000000000000) :=
    logU (w := (979 / 2500)) (c := (979 / 625))
      (q := (44877999279733 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-18750287366451) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-48712017065047) / 50000000000000) ≤ Real.log (1 - (789 / 1000) ^ 2) :=
    logL (w := (377479 / 1000000)) (c := (377479 / 250000))
      (q := (5150675247737 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-48712017065047) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (39 / 50) ≤ x → x ≤ (789 / 1000) →
      (31722678106427 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (159475630705241 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (39 / 50)) (w := (9 / 1000))
      (r1 := (2698883603 / 6250000000))
      (r2 := (324827577 / 62500000)) (r3 := (6545043 / 1250000))
      (r4 := (111537 / 50000))
      (R := (431120086553 / 100000000000000))
      (NL := (31722678106427 / 20000000000000)) (NU := (159475630705241 / 100000000000000))
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
  exact Dfun_box_pos (a := (39 / 50)) (b := (789 / 1000)) (m := (1569 / 2000))
    (hh := (9 / 2000)) (K := (26746968931157 / 100000000000000))
    (bnd := (2079495958007 / 1000000000000000))
    (Lu := ((-4854174136113) / 20000000000000))
    (Ll := ((-24270870780449) / 100000000000000))
    (Ml := ((-153479438031951) / 100000000000000))
    (Nu := ((-95565610548849) / 100000000000000))
    (U1 := ((-1211302186029) / 800000000000))
    (L1 := ((-155589715213757) / 100000000000000))
    (U2 := ((-18750287366451) / 20000000000000))
    (L2 := ((-48712017065047) / 50000000000000))
    (NL := (31722678106427 / 20000000000000))
    (NU := (159475630705241 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_095 {s : ℝ} (hs1 : (789 / 1000) ≤ s) (hs2 : s ≤ (799 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (397 / 500) ≤ ((-23067181772999) / 100000000000000) :=
    logU (w := (397 / 500)) (c := (397 / 250))
      (q := (9249507256599 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-23067181772999) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-23067181912479) / 100000000000000) ≤ Real.log (397 / 500) :=
    logL (w := (397 / 500)) (c := (397 / 250))
      (q := (11561884035879 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-23067181912479) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-31597582277419) / 20000000000000) ≤ Real.log (1 - (397 / 500)) :=
    logL (w := (103 / 500)) (c := (206 / 125))
      (q := (4995624278089 / 10000000000000)) (k := 3) (J := 6)
      (R := ((-31597582277419) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (397 / 500) ^ 2) ≤ ((-1555361478993) / 1562500000000) :=
    logU (w := (92391 / 250000)) (c := (92391 / 62500))
      (q := (9771575364109 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-1555361478993) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (789 / 1000)) ≤ ((-77794857273771) / 50000000000000) :=
    logU (w := (211 / 1000)) (c := (211 / 125))
      (q := (1308860990511 / 2500000000000)) (k := 3) (J := 6)
      (R := ((-77794857273771) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-160445037287063) / 100000000000000) ≤ Real.log (1 - (799 / 1000)) :=
    logL (w := (201 / 1000)) (c := (201 / 125))
      (q := (23749558440461 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-160445037287063) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (789 / 1000) ^ 2) ≤ ((-1522250532779) / 1562500000000) :=
    logU (w := (377479 / 1000000)) (c := (377479 / 250000))
      (q := (10301350503533 / 25000000000000)) (k := 2) (J := 6)
      (R := ((-1522250532779) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-101721941603363) / 100000000000000) ≤ Real.log (1 - (799 / 1000) ^ 2) :=
    logL (w := (361599 / 1000000)) (c := (361599 / 250000))
      (q := (36907494508627 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-101721941603363) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (789 / 1000) ≤ x → x ≤ (799 / 1000) →
      (158895048326041 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (4001405327111 / 2500000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (789 / 1000)) (w := (1 / 100))
      (r1 := (263325354497 / 500000000000))
      (r2 := (2669863499127 / 500000000000)) (r3 := (2659764843 / 500000000))
      (r4 := (2407887 / 1000000))
      (R := (580582379199 / 100000000000000))
      (NL := (158895048326041 / 100000000000000)) (NU := (4001405327111 / 2500000000000))
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
  exact Dfun_box_pos (a := (789 / 1000)) (b := (799 / 1000)) (m := (397 / 500))
    (hh := (1 / 200)) (K := (29685732481481 / 100000000000000))
    (bnd := (24266421055133 / 10000000000000000))
    (Lu := ((-23067181772999) / 100000000000000))
    (Ll := ((-23067181912479) / 100000000000000))
    (Ml := ((-31597582277419) / 20000000000000))
    (Nu := ((-1555361478993) / 1562500000000))
    (U1 := ((-77794857273771) / 50000000000000))
    (L1 := ((-160445037287063) / 100000000000000))
    (U2 := ((-1522250532779) / 1562500000000))
    (L2 := ((-101721941603363) / 100000000000000))
    (NL := (158895048326041 / 100000000000000))
    (NU := (4001405327111 / 2500000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_096 {s : ℝ} (hs1 : (799 / 1000) ≤ s) (hs2 : s ≤ (81 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (1609 / 2000) ≤ ((-2719178906777) / 12500000000000) :=
    logU (w := (1609 / 2000)) (c := (1609 / 1000))
      (q := (23780643400889 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-2719178906777) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-21753431452969) / 100000000000000) ≤ Real.log (1609 / 2000) :=
    logL (w := (1609 / 2000)) (c := (1609 / 1000))
      (q := (23780643301513 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-21753431452969) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-81609745023321) / 50000000000000) ≤ Real.log (1 - (1609 / 2000)) :=
    logL (w := (391 / 2000)) (c := (391 / 250))
      (q := (44724664121343 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-81609745023321) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1609 / 2000) ^ 2) ≤ ((-104191135445593) / 100000000000000) :=
    logU (w := (1411119 / 4000000)) (c := (1411119 / 1000000))
      (q := (6887660133279 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-104191135445593) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (799 / 1000)) ≤ ((-32089007418313) / 20000000000000) :=
    logU (w := (201 / 1000)) (c := (201 / 125))
      (q := (47499117076417 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-32089007418313) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-83036560360787) / 50000000000000) ≤ Real.log (1 - (81 / 100)) :=
    logL (w := (19 / 100)) (c := (38 / 25))
      (q := (41871033446411 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-83036560360787) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (799 / 1000) ^ 2) ≤ ((-101721941595447) / 100000000000000) :=
    logU (w := (361599 / 1000000)) (c := (361599 / 250000))
      (q := (36907494516541 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-101721941595447) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-106740436155609) / 100000000000000) ≤ Real.log (1 - (81 / 100) ^ 2) :=
    logL (w := (3439 / 10000)) (c := (3439 / 2500))
      (q := (31888999956381 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-106740436155609) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (799 / 1000) ≤ x → x ≤ (81 / 100) →
      (159290372161109 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (20102756750971 / 12500000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (799 / 1000)) (w := (11 / 1000))
      (r1 := (635050936243 / 1000000000000))
      (r2 := (2750398493517 / 500000000000)) (r3 := (2709890883 / 500000000))
      (r4 := (2604717 / 1000000))
      (R := (765840923329 / 100000000000000))
      (NL := (159290372161109 / 100000000000000)) (NU := (20102756750971 / 12500000000000))
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
  exact Dfun_box_pos (a := (799 / 1000)) (b := (81 / 100)) (m := (1609 / 2000))
    (hh := (11 / 2000)) (K := (4091502916137 / 12500000000000))
    (bnd := (28269854636401 / 10000000000000000))
    (Lu := ((-2719178906777) / 12500000000000))
    (Ll := ((-21753431452969) / 100000000000000))
    (Ml := ((-81609745023321) / 50000000000000))
    (Nu := ((-104191135445593) / 100000000000000))
    (U1 := ((-32089007418313) / 20000000000000))
    (L1 := ((-83036560360787) / 50000000000000))
    (U2 := ((-101721941595447) / 100000000000000))
    (L2 := ((-106740436155609) / 100000000000000))
    (NL := (159290372161109 / 100000000000000))
    (NU := (20102756750971 / 12500000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_097 {s : ℝ} (hs1 : (81 / 100) ≤ s) (hs2 : s ≤ (41 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (163 / 200) ≤ ((-2045671657301) / 10000000000000) :=
    logU (w := (163 / 200)) (c := (163 / 100))
      (q := (6107250185373 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-2045671657301) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-10228358426063) / 50000000000000) ≤ Real.log (163 / 200) :=
    logL (w := (163 / 200)) (c := (163 / 100))
      (q := (48858001203869 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-10228358426063) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-84369972703719) / 50000000000000) ≤ Real.log (1 - (163 / 200)) :=
    logL (w := (37 / 200)) (c := (37 / 25))
      (q := (39204208760547 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-84369972703719) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (163 / 200) ^ 2) ≤ ((-54565699309349) / 50000000000000) :=
    logU (w := (13431 / 40000)) (c := (13431 / 10000))
      (q := (2949803749329 / 10000000000000)) (k := 2) (J := 6)
      (R := ((-54565699309349) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (81 / 100)) ≤ ((-166073120682047) / 100000000000000) :=
    logU (w := (19 / 100)) (c := (38 / 25))
      (q := (8374206697187 / 20000000000000)) (k := 3) (J := 6)
      (R := ((-166073120682047) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-4286996070399) / 2500000000000) ≤ Real.log (1 - (41 / 50)) :=
    logL (w := (9 / 50)) (c := (36 / 25))
      (q := (1458572454081 / 4000000000000)) (k := 3) (J := 6)
      (R := ((-4286996070399) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (81 / 100) ^ 2) ≤ ((-26685109038597) / 25000000000000) :=
    logU (w := (3439 / 10000)) (c := (3439 / 2500))
      (q := (39861249947 / 125000000000)) (k := 2) (J := 6)
      (R := ((-26685109038597) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-111596192700469) / 100000000000000) ≤ Real.log (1 - (41 / 50) ^ 2) :=
    logL (w := (819 / 2500)) (c := (819 / 625))
      (q := (27033243411521 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-111596192700469) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (81 / 100) ≤ x → x ≤ (41 / 50) →
      (8000331564671 / 5000000000000) ≤ Npoly x ∧
      Npoly x ≤ (2525585573783 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (81 / 100)) (w := (1 / 100))
      (r1 := (75805000643 / 100000000000))
      (r2 := (2840796603 / 500000000)) (r3 := (27695763 / 5000000))
      (r4 := (282123 / 100000))
      (R := (407711357173 / 50000000000000))
      (NL := (8000331564671 / 5000000000000)) (NU := (2525585573783 / 1562500000000))
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
  exact Dfun_box_pos (a := (81 / 100)) (b := (41 / 50)) (m := (163 / 200))
    (hh := (1 / 200)) (K := (15291690450857 / 50000000000000))
    (bnd := (6480684775507 / 2000000000000000))
    (Lu := ((-2045671657301) / 10000000000000))
    (Ll := ((-10228358426063) / 50000000000000))
    (Ml := ((-84369972703719) / 50000000000000))
    (Nu := ((-54565699309349) / 50000000000000))
    (U1 := ((-166073120682047) / 100000000000000))
    (L1 := ((-4286996070399) / 2500000000000))
    (U2 := ((-26685109038597) / 25000000000000))
    (L2 := ((-111596192700469) / 100000000000000))
    (NL := (8000331564671 / 5000000000000))
    (NU := (2525585573783 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_098 {s : ℝ} (hs1 : (41 / 50) ≤ s) (hs2 : s ≤ (83 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (33 / 40) ≤ ((-19237189263143) / 100000000000000) :=
    logU (w := (33 / 40)) (c := (33 / 20))
      (q := (50077528792851 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-19237189263143) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3847437928797) / 20000000000000) ≤ Real.log (33 / 40) :=
    logL (w := (33 / 40)) (c := (33 / 20))
      (q := (5007752841201 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-3847437928797) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-174296930508283) / 100000000000000) ≤ Real.log (1 - (33 / 40)) :=
    logL (w := (7 / 40)) (c := (7 / 5))
      (q := (16823611829851 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-174296930508283) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (33 / 40) ^ 2) ≤ ((-22827786360483) / 20000000000000) :=
    logU (w := (511 / 1600)) (c := (511 / 400))
      (q := (24490504309573 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-22827786360483) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (41 / 50)) ≤ ((-6859193712367) / 4000000000000) :=
    logU (w := (9 / 50)) (c := (36 / 25))
      (q := (36464311358807 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-6859193712367) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-177195684193951) / 100000000000000) ≤ Real.log (1 - (83 / 100)) :=
    logL (w := (17 / 100)) (c := (34 / 25))
      (q := (15374234987017 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-177195684193951) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (41 / 50) ^ 2) ≤ ((-111596192700321) / 100000000000000) :=
    logU (w := (819 / 2500)) (c := (819 / 625))
      (q := (27033243411667 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-111596192700321) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-23352817501573) / 20000000000000) ≤ Real.log (1 - (83 / 100) ^ 2) :=
    logL (w := (3111 / 10000)) (c := (3111 / 2500))
      (q := (174922788833 / 800000000000)) (k := 2) (J := 6)
      (R := ((-23352817501573) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (41 / 50) ≤ x → x ≤ (83 / 100) →
      (80352528986943 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (81284947735169 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (41 / 50)) (w := (1 / 100))
      (r1 := (5458469363 / 6250000000))
      (r2 := (365593743 / 62500000)) (r3 := (7069923 / 1250000))
      (r4 := (150903 / 50000))
      (R := (466209374113 / 50000000000000))
      (NL := (80352528986943 / 50000000000000)) (NU := (81284947735169 / 50000000000000))
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
  exact Dfun_box_pos (a := (41 / 50)) (b := (83 / 100)) (m := (33 / 40))
    (hh := (1 / 200)) (K := (6210953974521 / 20000000000000))
    (bnd := (9104113916533 / 2500000000000000))
    (Lu := ((-19237189263143) / 100000000000000))
    (Ll := ((-3847437928797) / 20000000000000))
    (Ml := ((-174296930508283) / 100000000000000))
    (Nu := ((-22827786360483) / 20000000000000))
    (U1 := ((-6859193712367) / 4000000000000))
    (L1 := ((-177195684193951) / 100000000000000))
    (U2 := ((-111596192700321) / 100000000000000))
    (L2 := ((-23352817501573) / 20000000000000))
    (NL := (80352528986943 / 50000000000000))
    (NU := (81284947735169 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_099 {s : ℝ} (hs1 : (83 / 100) ≤ s) (hs2 : s ≤ (21 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (167 / 200) ≤ ((-18032355410861) / 100000000000000) :=
    logU (w := (167 / 200)) (c := (167 / 100))
      (q := (51282362645133 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-18032355410861) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-18032355924539) / 100000000000000) ≤ Real.log (167 / 200) :=
    logL (w := (167 / 200)) (c := (167 / 100))
      (q := (50080431769 / 97656250000)) (k := 1) (J := 6)
      (R := ((-18032355924539) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-90090490254181) / 50000000000000) ≤ Real.log (1 - (167 / 200)) :=
    logL (w := (33 / 200)) (c := (33 / 25))
      (q := (27763173659623 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-90090490254181) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (167 / 200) ^ 2) ≤ ((-119476532357501) / 100000000000000) :=
    logU (w := (12111 / 40000)) (c := (12111 / 10000))
      (q := (19152903754487 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-119476532357501) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (83 / 100)) ≤ ((-5537365131037) / 3125000000000) :=
    logU (w := (17 / 100)) (c := (34 / 25))
      (q := (15374234987399 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-5537365131037) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-91629073187439) / 50000000000000) ≤ Real.log (1 - (21 / 25)) :=
    logL (w := (4 / 25)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-91629073187439) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (83 / 100) ^ 2) ≤ ((-116764087507853) / 100000000000000) :=
    logU (w := (3111 / 10000)) (c := (3111 / 2500))
      (q := (4373069720827 / 20000000000000)) (k := 2) (J := 6)
      (R := ((-116764087507853) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-122281589212743) / 100000000000000) ≤ Real.log (1 - (21 / 25) ^ 2) :=
    logL (w := (184 / 625)) (c := (736 / 625))
      (q := (16347846899247 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-122281589212743) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (83 / 100) ≤ x → x ≤ (21 / 25) →
      (40379262431873 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (9986739576 / 6103515625) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (83 / 100)) (w := (1 / 100))
      (r1 := (99205414643 / 100000000000))
      (r2 := (3010514121 / 500000000)) (r3 := (28902987 / 5000000))
      (r4 := (321489 / 100000))
      (R := (526422871423 / 50000000000000))
      (NL := (40379262431873 / 25000000000000)) (NU := (9986739576 / 6103515625))
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
  exact Dfun_box_pos (a := (83 / 100)) (b := (21 / 25)) (m := (167 / 200))
    (hh := (1 / 200)) (K := (6312861191953 / 20000000000000))
    (bnd := (40458251428983 / 10000000000000000))
    (Lu := ((-18032355410861) / 100000000000000))
    (Ll := ((-18032355924539) / 100000000000000))
    (Ml := ((-90090490254181) / 50000000000000))
    (Nu := ((-119476532357501) / 100000000000000))
    (U1 := ((-5537365131037) / 3125000000000))
    (L1 := ((-91629073187439) / 50000000000000))
    (U2 := ((-116764087507853) / 100000000000000))
    (L2 := ((-122281589212743) / 100000000000000))
    (NL := (40379262431873 / 25000000000000))
    (NU := (9986739576 / 6103515625))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_100 {s : ℝ} (hs1 : (21 / 25) ≤ s) (hs2 : s ≤ (17 / 20)) :
    0 < Dfun s := by
  have hLu : Real.log (169 / 200) ≤ ((-16841865159329) / 100000000000000) :=
    logU (w := (169 / 200)) (c := (169 / 100))
      (q := (10494570579333 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-16841865159329) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-8420932922357) / 50000000000000) ≤ Real.log (169 / 200) :=
    logL (w := (169 / 200)) (c := (169 / 100))
      (q := (52472852211281 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8420932922357) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-186433016206299) / 100000000000000) ≤ Real.log (1 - (169 / 200)) :=
    logL (w := (31 / 200)) (c := (31 / 25))
      (q := (10755568980843 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-186433016206299) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (169 / 200) ^ 2) ≤ ((-62592544228519) / 50000000000000) :=
    logU (w := (11439 / 40000)) (c := (11439 / 10000))
      (q := (268886953099 / 2000000000000)) (k := 2) (J := 6)
      (R := ((-62592544228519) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (21 / 25)) ≤ ((-183258146374829) / 100000000000000) :=
    logU (w := (4 / 25)) (c := (32 / 25))
      (q := (24686007793153 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-183258146374829) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-189711998488591) / 100000000000000) ≤ Real.log (1 - (17 / 20)) :=
    logL (w := (3 / 20)) (c := (6 / 5))
      (q := (9116077839697 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-189711998488591) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (21 / 25) ^ 2) ≤ ((-6114079460637) / 5000000000000) :=
    logU (w := (184 / 625)) (c := (736 / 625))
      (q := (1021740431203 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-6114079460637) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-64096717289783) / 50000000000000) ≤ Real.log (1 - (17 / 20) ^ 2) :=
    logL (w := (111 / 400)) (c := (111 / 100))
      (q := (1304500191553 / 12500000000000)) (k := 2) (J := 6)
      (R := ((-64096717289783) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (21 / 25) ≤ x → x ≤ (17 / 20) →
      (81222980178809 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (26367923531 / 16000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (21 / 25)) (w := (1 / 100))
      (r1 := (108810737 / 97656250))
      (r2 := (12102372 / 1953125)) (r3 := (1847853 / 312500))
      (r4 := (85293 / 25000))
      (R := (588390427783 / 50000000000000))
      (NL := (81222980178809 / 50000000000000)) (NU := (26367923531 / 16000000000))
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
  exact Dfun_box_pos (a := (21 / 25)) (b := (17 / 20)) (m := (169 / 200))
    (hh := (1 / 200)) (K := (32121792079817 / 100000000000000))
    (bnd := (11120156736407 / 2500000000000000))
    (Lu := ((-16841865159329) / 100000000000000))
    (Ll := ((-8420932922357) / 50000000000000))
    (Ml := ((-186433016206299) / 100000000000000))
    (Nu := ((-62592544228519) / 50000000000000))
    (U1 := ((-183258146374829) / 100000000000000))
    (L1 := ((-189711998488591) / 100000000000000))
    (U2 := ((-6114079460637) / 5000000000000))
    (L2 := ((-64096717289783) / 50000000000000))
    (NL := (81222980178809 / 50000000000000))
    (NU := (26367923531 / 16000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_101 {s : ℝ} (hs1 : (17 / 20) ≤ s) (hs2 : s ≤ (43 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (171 / 200) ≤ ((-3916345250041) / 25000000000000) :=
    logU (w := (171 / 200)) (c := (171 / 100))
      (q := (5364933705583 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-3916345250041) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-979086369087) / 6250000000000) ≤ Real.log (171 / 200) :=
    logL (w := (171 / 200)) (c := (171 / 100))
      (q := (53649336150603 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-979086369087) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-96551076828079) / 50000000000000) ≤ Real.log (1 - (171 / 200)) :=
    logL (w := (29 / 200)) (c := (29 / 25))
      (q := (14842000511827 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-96551076828079) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (171 / 200) ^ 2) ≤ ((-26262736810043) / 20000000000000) :=
    logU (w := (10759 / 40000)) (c := (10759 / 10000))
      (q := (7315752061773 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-26262736810043) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (17 / 20)) ≤ ((-94855999244293) / 50000000000000) :=
    logU (w := (3 / 20)) (c := (6 / 5))
      (q := (4558038919849 / 25000000000000)) (k := 3) (J := 6)
      (R := ((-94855999244293) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-39322257127457) / 20000000000000) ≤ Real.log (1 - (43 / 50)) :=
    logL (w := (7 / 50)) (c := (28 / 25))
      (q := (113328685307 / 1000000000000)) (k := 3) (J := 6)
      (R := ((-39322257127457) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (17 / 20) ^ 2) ≤ ((-128193434579563) / 100000000000000) :=
    logU (w := (111 / 400)) (c := (111 / 100))
      (q := (417440061297 / 4000000000000)) (k := 2) (J := 6)
      (R := ((-128193434579563) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-67276818432387) / 50000000000000) ≤ Real.log (1 - (43 / 50) ^ 2) :=
    logL (w := (651 / 2500)) (c := (651 / 625))
      (q := (254737452951 / 6250000000000)) (k := 2) (J := 6)
      (R := ((-67276818432387) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (17 / 20) ≤ x → x ≤ (43 / 50) →
      (40873804025271 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (2595372313069 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (17 / 20)) (w := (1 / 100))
      (r1 := (198390083 / 160000000))
      (r2 := (25503579 / 4000000)) (r3 := (1210707 / 200000))
      (r4 := (72171 / 20000))
      (R := (652152983833 / 50000000000000))
      (NL := (40873804025271 / 25000000000000)) (NU := (2595372313069 / 1562500000000))
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
  exact Dfun_box_pos (a := (17 / 20)) (b := (43 / 50)) (m := (171 / 200))
    (hh := (1 / 200)) (K := (6547992168437 / 20000000000000))
    (bnd := (24215733257177 / 5000000000000000))
    (Lu := ((-3916345250041) / 25000000000000))
    (Ll := ((-979086369087) / 6250000000000))
    (Ml := ((-96551076828079) / 50000000000000))
    (Nu := ((-26262736810043) / 20000000000000))
    (U1 := ((-94855999244293) / 50000000000000))
    (L1 := ((-39322257127457) / 20000000000000))
    (U2 := ((-128193434579563) / 100000000000000))
    (L2 := ((-67276818432387) / 50000000000000))
    (NL := (40873804025271 / 25000000000000))
    (NU := (2595372313069 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_102 {s : ℝ} (hs1 : (43 / 50) ≤ s) (hs2 : s ≤ (87 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (173 / 200) ≤ ((-14502577199053) / 100000000000000) :=
    logU (w := (173 / 200)) (c := (173 / 100))
      (q := (54812140856941 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-14502577199053) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-14502578383237) / 100000000000000) ≤ Real.log (173 / 200) :=
    logL (w := (173 / 200)) (c := (173 / 100))
      (q := (27406069836379 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-14502578383237) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-200248050054373) / 100000000000000) ≤ Real.log (1 - (173 / 200)) :=
    logL (w := (27 / 200)) (c := (27 / 25))
      (q := (1924026028403 / 25000000000000)) (k := 3) (J := 6)
      (R := ((-200248050054373) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (173 / 200) ^ 2) ≤ ((-137921944744791) / 100000000000000) :=
    logU (w := (10071 / 40000)) (c := (10071 / 10000))
      (q := (707491367197 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-137921944744791) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (43 / 50)) ≤ ((-196611285637281) / 100000000000000) :=
    logU (w := (7 / 50)) (c := (28 / 25))
      (q := (11332868530701 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-196611285637281) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-204022082852657) / 100000000000000) ≤ Real.log (1 - (87 / 100)) :=
    logL (w := (13 / 100)) (c := (26 / 25))
      (q := (30641182151 / 781250000000)) (k := 3) (J := 6)
      (R := ((-204022082852657) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (43 / 50) ^ 2) ≤ ((-134553636864771) / 100000000000000) :=
    logU (w := (651 / 2500)) (c := (651 / 625))
      (q := (4075799247217 / 100000000000000)) (k := 2) (J := 6)
      (R := ((-134553636864771) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-70714126379939) / 50000000000000) ≤ Real.log (1 - (87 / 100) ^ 2) :=
    logL (w := (2431 / 10000)) (c := (2431 / 1250))
      (q := (66515901408107 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-70714126379939) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (43 / 50) ≤ x → x ≤ (87 / 100) →
      (16466832035207 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (83769667860381 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (43 / 50)) (w := (1 / 100))
      (r1 := (8558041283 / 6250000000))
      (r2 := (409981581 / 62500000)) (r3 := (7752267 / 1250000))
      (r4 := (190269 / 50000))
      (R := (717753842173 / 50000000000000))
      (NL := (16466832035207 / 10000000000000)) (NU := (83769667860381 / 50000000000000))
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
  exact Dfun_box_pos (a := (43 / 50)) (b := (87 / 100)) (m := (173 / 200))
    (hh := (1 / 200)) (K := (33435563128039 / 100000000000000))
    (bnd := (5225379083243 / 1000000000000000))
    (Lu := ((-14502577199053) / 100000000000000))
    (Ll := ((-14502578383237) / 100000000000000))
    (Ml := ((-200248050054373) / 100000000000000))
    (Nu := ((-137921944744791) / 100000000000000))
    (U1 := ((-196611285637281) / 100000000000000))
    (L1 := ((-204022082852657) / 100000000000000))
    (U2 := ((-134553636864771) / 100000000000000))
    (L2 := ((-70714126379939) / 50000000000000))
    (NL := (16466832035207 / 10000000000000))
    (NU := (83769667860381 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_103 {s : ℝ} (hs1 : (87 / 100) ≤ s) (hs2 : s ≤ (22 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (7 / 8) ≤ ((-13353139254379) / 100000000000000) :=
    logU (w := (7 / 8)) (c := (7 / 4))
      (q := (11192315760323 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-13353139254379) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-13353140789547) / 100000000000000) ≤ Real.log (7 / 8) :=
    logL (w := (7 / 8)) (c := (7 / 4))
      (q := (3497598579153 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-13353140789547) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-41588830833597) / 20000000000000) ≤ Real.log (1 - (7 / 8)) :=
    logL (w := (1 / 8)) (c := 1)
      (q := 0) (k := 3) (J := 6)
      (R := ((-41588830833597) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (7 / 8) ^ 2) ≤ ((-29016657636483) / 20000000000000) :=
    logU (w := (15 / 64)) (c := (15 / 8))
      (q := (62860865985567 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-29016657636483) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (87 / 100)) ≤ ((-204022082852653) / 100000000000000) :=
    logU (w := (13 / 100)) (c := (26 / 25))
      (q := (3922071315329 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-204022082852653) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-212026363845021) / 100000000000000) ≤ Real.log (1 - (22 / 25)) :=
    logL (w := (3 / 25)) (c := (48 / 25))
      (q := (65232508378959 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-212026363845021) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (87 / 100) ^ 2) ≤ ((-70714119834233) / 50000000000000) :=
    logU (w := (2431 / 10000)) (c := (2431 / 1250))
      (q := (16628978624879 / 25000000000000)) (k := 3) (J := 6)
      (R := ((-70714119834233) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-148899178915017) / 100000000000000) ≤ Real.log (1 - (22 / 25) ^ 2) :=
    logL (w := (141 / 625)) (c := (1128 / 625))
      (q := (7380621906621 / 12500000000000)) (k := 3) (J := 6)
      (R := ((-148899178915017) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (87 / 100) ≤ x → x ≤ (22 / 25) →
      (41492214596509 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (41286575453 / 24414062500) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (87 / 100)) (w := (1 / 100))
      (r1 := (150235667363 / 100000000000))
      (r2 := (3374041149 / 500000000)) (r3 := (31789827 / 5000000))
      (r4 := (400221 / 100000))
      (R := (785238667363 / 50000000000000))
      (NL := (41492214596509 / 25000000000000)) (NU := (41286575453 / 24414062500))
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
  exact Dfun_box_pos (a := (87 / 100)) (b := (22 / 25)) (m := (7 / 8))
    (hh := (1 / 200)) (K := (34231010093173 / 100000000000000))
    (bnd := (55884506620779 / 10000000000000000))
    (Lu := ((-13353139254379) / 100000000000000))
    (Ll := ((-13353140789547) / 100000000000000))
    (Ml := ((-41588830833597) / 20000000000000))
    (Nu := ((-29016657636483) / 20000000000000))
    (U1 := ((-204022082852653) / 100000000000000))
    (L1 := ((-212026363845021) / 100000000000000))
    (U2 := ((-70714119834233) / 50000000000000))
    (L2 := ((-148899178915017) / 100000000000000))
    (NL := (41492214596509 / 25000000000000))
    (NU := (41286575453 / 24414062500))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_104 {s : ℝ} (hs1 : (22 / 25) ≤ s) (hs2 : s ≤ (89 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (177 / 200) ≤ ((-2443352677323) / 20000000000000) :=
    logU (w := (177 / 200)) (c := (177 / 100))
      (q := (57097954669379 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-2443352677323) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-12216765359881) / 100000000000000) ≤ Real.log (177 / 200) :=
    logL (w := (177 / 200)) (c := (177 / 100))
      (q := (28548976348057 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-12216765359881) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-54070579876141) / 25000000000000) ≤ Real.log (1 - (177 / 200)) :=
    logL (w := (23 / 200)) (c := (46 / 25))
      (q := (7622069089927 / 12500000000000)) (k := 4) (J := 6)
      (R := ((-54070579876141) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (177 / 200) ^ 2) ≤ ((-76444766482761) / 50000000000000) :=
    logU (w := (8671 / 40000)) (c := (8671 / 5000))
      (q := (2752731060123 / 5000000000000)) (k := 3) (J := 6)
      (R := ((-76444766482761) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (22 / 25)) ≤ ((-53006588386559) / 25000000000000) :=
    logU (w := (3 / 25)) (c := (48 / 25))
      (q := (3261625933887 / 5000000000000)) (k := 4) (J := 6)
      (R := ((-53006588386559) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-44145498610383) / 20000000000000) ≤ Real.log (1 - (89 / 100)) :=
    logL (w := (11 / 100)) (c := (44 / 25))
      (q := (11306275834413 / 20000000000000)) (k := 4) (J := 6)
      (R := ((-44145498610383) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (22 / 25) ^ 2) ≤ ((-29779835183653) / 20000000000000) :=
    logU (w := (141 / 625)) (c := (1128 / 625))
      (q := (59044978249717 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-29779835183653) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-157069808874371) / 100000000000000) ≤ Real.log (1 - (89 / 100) ^ 2) :=
    logL (w := (2079 / 10000)) (c := (2079 / 1250))
      (q := (25437172646807 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-157069808874371) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (22 / 25) ≤ x → x ≤ (89 / 100) →
      (83700251041821 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (85409562013667 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (22 / 25)) (w := (1 / 100))
      (r1 := (640328873 / 390625000))
      (r2 := (54228609 / 7812500)) (r3 := (1019061 / 156250))
      (r4 := (13122 / 3125))
      (R := (854655485923 / 50000000000000))
      (NL := (83700251041821 / 50000000000000)) (NU := (85409562013667 / 50000000000000))
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
  exact Dfun_box_pos (a := (22 / 25)) (b := (89 / 100)) (m := (177 / 200))
    (hh := (1 / 200)) (K := (35156746220361 / 100000000000000))
    (bnd := (11850522385399 / 2000000000000000))
    (Lu := ((-2443352677323) / 20000000000000))
    (Ll := ((-12216765359881) / 100000000000000))
    (Ml := ((-54070579876141) / 25000000000000))
    (Nu := ((-76444766482761) / 50000000000000))
    (U1 := ((-53006588386559) / 25000000000000))
    (L1 := ((-44145498610383) / 20000000000000))
    (U2 := ((-29779835183653) / 20000000000000))
    (L2 := ((-157069808874371) / 100000000000000))
    (NL := (83700251041821 / 50000000000000))
    (NU := (85409562013667 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_105 {s : ℝ} (hs1 : (89 / 100) ≤ s) (hs2 : s ≤ (9 / 10)) :
    0 < Dfun s := by
  have hLu : Real.log (179 / 200) ≤ ((-11093156056399) / 100000000000000) :=
    logU (w := (179 / 200)) (c := (179 / 100))
      (q := (11644312399919 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-11093156056399) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-5546579286197) / 50000000000000) ≤ Real.log (179 / 200) :=
    logL (w := (179 / 200)) (c := (179 / 100))
      (q := (58221559483601 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5546579286197) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-22537949347391) / 10000000000000) ≤ Real.log (1 - (179 / 200)) :=
    logL (w := (21 / 200)) (c := (42 / 25))
      (q := (5187937875007 / 10000000000000)) (k := 4) (J := 6)
      (R := ((-22537949347391) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (179 / 200) ^ 2) ≤ ((-161457609028481) / 100000000000000) :=
    logU (w := (7959 / 40000)) (c := (7959 / 5000))
      (q := (46486545139501 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-161457609028481) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (89 / 100)) ≤ ((-220727491309619) / 100000000000000) :=
    logU (w := (11 / 100)) (c := (44 / 25))
      (q := (56531380914357 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-220727491309619) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-230258509469853) / 100000000000000) ≤ Real.log (1 - (9 / 10)) :=
    logL (w := (1 / 10)) (c := (8 / 5))
      (q := (47000362754127 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-230258509469853) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (89 / 100) ^ 2) ≤ ((-157069808409799) / 100000000000000) :=
    logU (w := (2079 / 10000)) (c := (2079 / 1250))
      (q := (50874345758183 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-157069808409799) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-83036560360787) / 50000000000000) ≤ Real.log (1 - (9 / 10) ^ 2) :=
    logL (w := (19 / 100)) (c := (38 / 25))
      (q := (41871033446411 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-83036560360787) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (89 / 100) ≤ x → x ≤ (9 / 10) →
      (42241753663667 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (863356167 / 500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (89 / 100)) (w := (1 / 100))
      (r1 := (178004074403 / 100000000000))
      (r2 := (3569740227 / 500000000)) (r3 := (33469443 / 5000000))
      (r4 := (439587 / 100000))
      (R := (926054686333 / 50000000000000))
      (NL := (42241753663667 / 25000000000000)) (NU := (863356167 / 500000000))
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
  exact Dfun_box_pos (a := (89 / 100)) (b := (9 / 10)) (m := (179 / 200))
    (hh := (1 / 200)) (K := (36255377258973 / 100000000000000))
    (bnd := (62277256313481 / 10000000000000000))
    (Lu := ((-11093156056399) / 100000000000000))
    (Ll := ((-5546579286197) / 50000000000000))
    (Ml := ((-22537949347391) / 10000000000000))
    (Nu := ((-161457609028481) / 100000000000000))
    (U1 := ((-220727491309619) / 100000000000000))
    (L1 := ((-230258509469853) / 100000000000000))
    (U2 := ((-157069808409799) / 100000000000000))
    (L2 := ((-83036560360787) / 50000000000000))
    (NL := (42241753663667 / 25000000000000))
    (NU := (863356167 / 500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_106 {s : ℝ} (hs1 : (9 / 10) ≤ s) (hs2 : s ≤ (91 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (181 / 200) ≤ ((-4991016754693) / 50000000000000) :=
    logU (w := (181 / 200)) (c := (181 / 100))
      (q := (3708292784163 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-4991016754693) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-9982036692953) / 100000000000000) ≤ Real.log (181 / 200) :=
    logL (w := (181 / 200)) (c := (181 / 100))
      (q := (29666340681521 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-9982036692953) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-235387838777569) / 100000000000000) ≤ Real.log (1 - (181 / 200)) :=
    logL (w := (19 / 200)) (c := (38 / 25))
      (q := (41871033446411 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-235387838777569) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (181 / 200) ^ 2) ≤ ((-10683727367517) / 6250000000000) :=
    logU (w := (7239 / 40000)) (c := (7239 / 5000))
      (q := (3700451628771 / 10000000000000)) (k := 3) (J := 6)
      (R := ((-10683727367517) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (9 / 10)) ≤ ((-230258509298769) / 100000000000000) :=
    logU (w := (1 / 10)) (c := (8 / 5))
      (q := (47000362925207 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-230258509298769) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-48158912174391) / 20000000000000) ≤ Real.log (1 - (91 / 100)) :=
    logL (w := (9 / 100)) (c := (36 / 25))
      (q := (1458572454081 / 4000000000000)) (k := 4) (J := 6)
      (R := ((-48158912174391) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (9 / 10) ^ 2) ≤ ((-166073120682047) / 100000000000000) :=
    logU (w := (19 / 100)) (c := (38 / 25))
      (q := (8374206697187 / 20000000000000)) (k := 3) (J := 6)
      (R := ((-166073120682047) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-176084236660537) / 100000000000000) ≤ Real.log (1 - (91 / 100) ^ 2) :=
    logL (w := (1719 / 10000)) (c := (1719 / 1250))
      (q := (3982489688431 / 12500000000000)) (k := 3) (J := 6)
      (R := ((-176084236660537) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (9 / 10) ≤ x → x ≤ (91 / 100) →
      (85336127680967 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (87335105719033 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (9 / 10)) (w := (1 / 100))
      (r1 := (19248563 / 10000000))
      (r2 := (3671487 / 500000)) (r3 := (343683 / 50000))
      (r4 := (45927 / 10000))
      (R := (999489019033 / 50000000000000))
      (NL := (85336127680967 / 50000000000000)) (NU := (87335105719033 / 50000000000000))
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
  exact Dfun_box_pos (a := (9 / 10)) (b := (91 / 100)) (m := (181 / 200))
    (hh := (1 / 200)) (K := (18793969184759 / 50000000000000))
    (bnd := (64863452669909 / 10000000000000000))
    (Lu := ((-4991016754693) / 50000000000000))
    (Ll := ((-9982036692953) / 100000000000000))
    (Ml := ((-235387838777569) / 100000000000000))
    (Nu := ((-10683727367517) / 6250000000000))
    (U1 := ((-230258509298769) / 100000000000000))
    (L1 := ((-48158912174391) / 20000000000000))
    (U2 := ((-166073120682047) / 100000000000000))
    (L2 := ((-176084236660537) / 100000000000000))
    (NL := (85336127680967 / 50000000000000))
    (NU := (87335105719033 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_107 {s : ℝ} (hs1 : (91 / 100) ≤ s) (hs2 : s ≤ (23 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (183 / 200) ≤ ((-8883121346109) / 100000000000000) :=
    logU (w := (183 / 200)) (c := (183 / 100))
      (q := (12086319341977 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-8883121346109) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4441562672641) / 50000000000000) ≤ Real.log (183 / 200) :=
    logL (w := (183 / 200)) (c := (183 / 100))
      (q := (60431592710713 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-4441562672641) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-123255201124973) / 50000000000000) ≤ Real.log (1 - (183 / 200)) :=
    logL (w := (17 / 200)) (c := (34 / 25))
      (q := (15374234987017 / 50000000000000)) (k := 4) (J := 6)
      (R := ((-123255201124973) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (183 / 200) ^ 2) ≤ ((-181538639985919) / 100000000000000) :=
    logU (w := (6511 / 40000)) (c := (6511 / 5000))
      (q := (26405514182063 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-181538639985919) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (91 / 100)) ≤ ((-240794560865169) / 100000000000000) :=
    logU (w := (9 / 100)) (c := (36 / 25))
      (q := (36464311358807 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-240794560865169) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-252572864430873) / 100000000000000) ≤ Real.log (1 - (23 / 25)) :=
    logL (w := (2 / 25)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-252572864430873) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (91 / 100) ^ 2) ≤ ((-176084236659329) / 100000000000000) :=
    logU (w := (1719 / 10000)) (c := (1719 / 1250))
      (q := (31859917508653 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-176084236659329) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-187340345826863) / 100000000000000) ≤ Real.log (1 - (23 / 25) ^ 2) :=
    logL (w := (96 / 625)) (c := (768 / 625))
      (q := (10301904170561 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-187340345826863) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (91 / 100) ≤ x → x ≤ (23 / 25) →
      (8626009212261 / 5000000000000) ≤ Npoly x ∧
      Npoly x ≤ (10792250893 / 6103515625) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (91 / 100)) (w := (1 / 100))
      (r1 := (207379644563 / 100000000000))
      (r2 := (3775989393 / 500000000)) (r3 := (35306523 / 5000000))
      (r4 := (478953 / 100000))
      (R := (1075013596423 / 50000000000000))
      (NL := (8626009212261 / 5000000000000)) (NU := (10792250893 / 6103515625))
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
  exact Dfun_box_pos (a := (91 / 100)) (b := (23 / 25)) (m := (183 / 200))
    (hh := (1 / 200)) (K := (19622542601199 / 50000000000000))
    (bnd := (66897848771817 / 10000000000000000))
    (Lu := ((-8883121346109) / 100000000000000))
    (Ll := ((-4441562672641) / 50000000000000))
    (Ml := ((-123255201124973) / 50000000000000))
    (Nu := ((-181538639985919) / 100000000000000))
    (U1 := ((-240794560865169) / 100000000000000))
    (L1 := ((-252572864430873) / 100000000000000))
    (U2 := ((-176084236659329) / 100000000000000))
    (L2 := ((-187340345826863) / 100000000000000))
    (NL := (8626009212261 / 5000000000000))
    (NU := (10792250893 / 6103515625))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_108 {s : ℝ} (hs1 : (23 / 25) ≤ s) (hs2 : s ≤ (93 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (37 / 40) ≤ ((-7796154115219) / 100000000000000) :=
    logU (w := (37 / 40)) (c := (37 / 20))
      (q := (2460742557631 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-7796154115219) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-487259944031) / 6250000000000) ≤ Real.log (37 / 40) :=
    logL (w := (37 / 40)) (c := (37 / 20))
      (q := (61518558951499 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-487259944031) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-129513358272293) / 50000000000000) ≤ Real.log (1 - (37 / 40)) :=
    logL (w := (3 / 40)) (c := (6 / 5))
      (q := (9116077839697 / 50000000000000)) (k := 4) (J := 6)
      (R := ((-129513358272293) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (37 / 40) ^ 2) ≤ ((-96767059885303) / 50000000000000) :=
    logU (w := (231 / 1600)) (c := (231 / 200))
      (q := (225156787459 / 1562500000000)) (k := 3) (J := 6)
      (R := ((-96767059885303) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (23 / 25)) ≤ ((-252572864430823) / 100000000000000) :=
    logU (w := (2 / 25)) (c := (32 / 25))
      (q := (24686007793153 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-252572864430823) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-1662037523083) / 625000000000) ≤ Real.log (1 - (93 / 100)) :=
    logL (w := (7 / 100)) (c := (28 / 25))
      (q := (113328685307 / 1000000000000)) (k := 4) (J := 6)
      (R := ((-1662037523083) / 625000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (23 / 25) ^ 2) ≤ ((-93670172913427) / 50000000000000) :=
    logU (w := (96 / 625)) (c := (768 / 625))
      (q := (2575476042641 / 12500000000000)) (k := 3) (J := 6)
      (R := ((-93670172913427) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-62554376063) / 31250000000) ≤ Real.log (1 - (93 / 100) ^ 2) :=
    logL (w := (1351 / 10000)) (c := (1351 / 1250))
      (q := (1554030153277 / 20000000000000)) (k := 3) (J := 6)
      (R := ((-62554376063) / 31250000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (23 / 25) ≤ x → x ≤ (93 / 100) →
      (87257433422593 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (89562805208319 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (23 / 25)) (w := (1 / 100))
      (r1 := (217477907 / 97656250))
      (r2 := (30338793 / 3906250)) (r3 := (2267757 / 312500))
      (r4 := (124659 / 25000))
      (R := (1152685892863 / 50000000000000))
      (NL := (87257433422593 / 50000000000000)) (NU := (89562805208319 / 50000000000000))
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
  exact Dfun_box_pos (a := (23 / 25)) (b := (93 / 100)) (m := (37 / 40))
    (hh := (1 / 200)) (K := (41367310494947 / 100000000000000))
    (bnd := (68240634921249 / 10000000000000000))
    (Lu := ((-7796154115219) / 100000000000000))
    (Ll := ((-487259944031) / 6250000000000))
    (Ml := ((-129513358272293) / 50000000000000))
    (Nu := ((-96767059885303) / 50000000000000))
    (U1 := ((-252572864430823) / 100000000000000))
    (L1 := ((-1662037523083) / 625000000000))
    (U2 := ((-93670172913427) / 50000000000000))
    (L2 := ((-62554376063) / 31250000000))
    (NL := (87257433422593 / 50000000000000))
    (NU := (89562805208319 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_109 {s : ℝ} (hs1 : (93 / 100) ≤ s) (hs2 : s ≤ (47 / 50)) :
    0 < Dfun s := by
  have hLu : Real.log (187 / 200) ≤ ((-672087492859) / 10000000000000) :=
    logU (w := (187 / 200)) (c := (187 / 100))
      (q := (15648460781851 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-672087492859) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-168022027813) / 2500000000000) ≤ Real.log (187 / 200) :=
    logL (w := (187 / 200)) (c := (187 / 100))
      (q := (2503753477739 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-168022027813) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-68334200227163) / 25000000000000) ≤ Real.log (1 - (187 / 200)) :=
    logL (w := (13 / 200)) (c := (26 / 25))
      (q := (30641182151 / 781250000000)) (k := 4) (J := 6)
      (R := ((-68334200227163) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (187 / 200) ^ 2) ≤ ((-207326068260473) / 100000000000000) :=
    logU (w := (5031 / 40000)) (c := (5031 / 5000))
      (q := (618085907509 / 100000000000000)) (k := 3) (J := 6)
      (R := ((-207326068260473) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (93 / 100)) ≤ ((-10637040147731) / 4000000000000) :=
    logU (w := (7 / 100)) (c := (28 / 25))
      (q := (11332868530701 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-10637040147731) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-35167635237627) / 12500000000000) ≤ Real.log (1 - (47 / 50)) :=
    logL (w := (3 / 50)) (c := (48 / 25))
      (q := (65232508378959 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-35167635237627) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (93 / 100) ^ 2) ≤ ((-50043500850399) / 25000000000000) :=
    logU (w := (1351 / 10000)) (c := (1351 / 1250))
      (q := (3885075383193 / 50000000000000)) (k := 3) (J := 6)
      (R := ((-50043500850399) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-215072280035179) / 100000000000000) ≤ Real.log (1 - (47 / 50) ^ 2) :=
    logL (w := (291 / 2500)) (c := (1164 / 625))
      (q := (62186592188801 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-215072280035179) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (93 / 100) ≤ x → x ≤ (47 / 50) →
      (44165119731823 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (2837355342281 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (93 / 100)) (w := (1 / 100))
      (r1 := (238450557683 / 100000000000))
      (r2 := (3993733431 / 500000000)) (r3 := (37301067 / 5000000))
      (r4 := (518319 / 100000))
      (R := (1232565744673 / 50000000000000))
      (NL := (44165119731823 / 25000000000000)) (NU := (2837355342281 / 1562500000000))
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
  exact Dfun_box_pos (a := (93 / 100)) (b := (47 / 50)) (m := (187 / 200))
    (hh := (1 / 200)) (K := (22092181520337 / 50000000000000))
    (bnd := (68713225787313 / 10000000000000000))
    (Lu := ((-672087492859) / 10000000000000))
    (Ll := ((-168022027813) / 2500000000000))
    (Ml := ((-68334200227163) / 25000000000000))
    (Nu := ((-207326068260473) / 100000000000000))
    (U1 := ((-10637040147731) / 4000000000000))
    (L1 := ((-35167635237627) / 12500000000000))
    (U2 := ((-50043500850399) / 25000000000000))
    (L2 := ((-215072280035179) / 100000000000000))
    (NL := (44165119731823 / 25000000000000))
    (NU := (2837355342281 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_110 {s : ℝ} (hs1 : (47 / 50) ≤ s) (hs2 : s ≤ (19 / 20)) :
    0 < Dfun s := by
  have hLu : Real.log (189 / 200) ≤ ((-5657035096903) / 100000000000000) :=
    logU (w := (189 / 200)) (c := (189 / 100))
      (q := (63657682959091 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-5657035096903) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-5657042713987) / 100000000000000) ≤ Real.log (189 / 200) :=
    logL (w := (189 / 200)) (c := (189 / 100))
      (q := (7957209417751 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-5657042713987) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-29004221110791) / 10000000000000) ≤ Real.log (1 - (189 / 200)) :=
    logL (w := (11 / 200)) (c := (44 / 25))
      (q := (11306275834413 / 20000000000000)) (k := 5) (J := 6)
      (R := ((-29004221110791) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (189 / 200) ^ 2) ≤ ((-223516011663439) / 100000000000000) :=
    logU (w := (4279 / 40000)) (c := (4279 / 2500))
      (q := (53742860560537 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-223516011663439) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (47 / 50)) ≤ ((-28134107160223) / 10000000000000) :=
    logU (w := (3 / 50)) (c := (48 / 25))
      (q := (3261625933887 / 5000000000000)) (k := 5) (J := 6)
      (R := ((-28134107160223) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-37446653440731) / 12500000000000) ≤ Real.log (1 - (19 / 20)) :=
    logL (w := (1 / 20)) (c := (8 / 5))
      (q := (47000362754127 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-37446653440731) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (47 / 50) ^ 2) ≤ ((-215072274331379) / 100000000000000) :=
    logU (w := (291 / 2500)) (c := (1164 / 625))
      (q := (62186597892597 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-215072274331379) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-232790290182421) / 100000000000000) ≤ Real.log (1 - (19 / 20) ^ 2) :=
    logL (w := (39 / 400)) (c := (39 / 25))
      (q := (44468582041559 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-232790290182421) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (47 / 50) ≤ x → x ≤ (19 / 20) →
      (89480655602859 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (29475227617 / 16000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (47 / 50)) (w := (1 / 100))
      (r1 := (15915711923 / 6250000000))
      (r2 := (513401409 / 62500000)) (r3 := (9589347 / 1250000))
      (r4 := (269001 / 50000))
      (R := (1314715350133 / 50000000000000))
      (NL := (89480655602859 / 50000000000000)) (NU := (29475227617 / 16000000000))
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
  exact Dfun_box_pos (a := (47 / 50)) (b := (19 / 20)) (m := (189 / 200))
    (hh := (1 / 200)) (K := (10110153469011 / 20000000000000))
    (bnd := (68077376534501 / 10000000000000000))
    (Lu := ((-5657035096903) / 100000000000000))
    (Ll := ((-5657042713987) / 100000000000000))
    (Ml := ((-29004221110791) / 10000000000000))
    (Nu := ((-223516011663439) / 100000000000000))
    (U1 := ((-28134107160223) / 10000000000000))
    (L1 := ((-37446653440731) / 12500000000000))
    (U2 := ((-215072274331379) / 100000000000000))
    (L2 := ((-232790290182421) / 100000000000000))
    (NL := (89480655602859 / 50000000000000))
    (NU := (29475227617 / 16000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_111 {s : ℝ} (hs1 : (19 / 20) ≤ s) (hs2 : s ≤ (24 / 25)) :
    0 < Dfun s := by
  have hLu : Real.log (191 / 200) ≤ ((-2302196892203) / 50000000000000) :=
    logU (w := (191 / 200)) (c := (191 / 100))
      (q := (16177581067897 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-2302196892203) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4604403111333) / 100000000000000) ≤ Real.log (191 / 200) :=
    logL (w := (191 / 200)) (c := (191 / 100))
      (q := (32355157472331 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-4604403111333) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-6202185578559) / 2000000000000) ≤ Real.log (1 - (191 / 200)) :=
    logL (w := (9 / 200)) (c := (36 / 25))
      (q := (1458572454081 / 4000000000000)) (k := 5) (J := 6)
      (R := ((-6202185578559) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (191 / 200) ^ 2) ≤ ((-1519189122359) / 625000000000) :=
    logU (w := (3519 / 40000)) (c := (3519 / 2500))
      (q := (4273576580817 / 12500000000000)) (k := 4) (J := 6)
      (R := ((-1519189122359) / 625000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (19 / 20)) ≤ ((-299573227354763) / 100000000000000) :=
    logU (w := (1 / 20)) (c := (8 / 5))
      (q := (47000362925207 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-299573227354763) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-80471895621717) / 25000000000000) ≤ Real.log (1 - (24 / 25)) :=
    logL (w := (1 / 25)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-80471895621717) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (19 / 20) ^ 2) ≤ ((-4655805801951) / 2000000000000) :=
    logU (w := (39 / 400)) (c := (39 / 25))
      (q := (22234291063213 / 50000000000000)) (k := 4) (J := 6)
      (R := ((-4655805801951) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-50918627032519) / 20000000000000) ≤ Real.log (1 - (24 / 25) ^ 2) :=
    logL (w := (49 / 625)) (c := (784 / 625))
      (q := (4533147412277 / 20000000000000)) (k := 4) (J := 6)
      (R := ((-50918627032519) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (19 / 20) ≤ x → x ≤ (24 / 25) →
      (45355443516821 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (22829415423 / 12207031250) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (19 / 20)) (w := (1 / 100))
      (r1 := (434100083 / 160000000))
      (r2 := (33791337 / 4000000)) (r3 := (1578123 / 200000))
      (r4 := (111537 / 20000))
      (R := (1399199269483 / 50000000000000))
      (NL := (45355443516821 / 25000000000000)) (NU := (22829415423 / 12207031250))
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
  exact Dfun_box_pos (a := (19 / 20)) (b := (24 / 25)) (m := (191 / 200))
    (hh := (1 / 200)) (K := (14938329114461 / 25000000000000))
    (bnd := (65997434013689 / 10000000000000000))
    (Lu := ((-2302196892203) / 50000000000000))
    (Ll := ((-4604403111333) / 100000000000000))
    (Ml := ((-6202185578559) / 2000000000000))
    (Nu := ((-1519189122359) / 625000000000))
    (U1 := ((-299573227354763) / 100000000000000))
    (L1 := ((-80471895621717) / 25000000000000))
    (U2 := ((-4655805801951) / 2000000000000))
    (L2 := ((-50918627032519) / 20000000000000))
    (NL := (45355443516821 / 25000000000000))
    (NU := (22829415423 / 12207031250))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_112 {s : ℝ} (hs1 : (24 / 25) ≤ s) (hs2 : s ≤ (97 / 100)) :
    0 < Dfun s := by
  have hLu : Real.log (193 / 200) ≤ ((-712543536331) / 20000000000000) :=
    logU (w := (193 / 200)) (c := (193 / 100))
      (q := (65752000374339 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-712543536331) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-3562729037879) / 100000000000000) ≤ Real.log (193 / 200) :=
    logL (w := (193 / 200)) (c := (193 / 100))
      (q := (16437997254529 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-3562729037879) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-13409628869971) / 4000000000000) ≤ Real.log (1 - (193 / 200)) :=
    logL (w := (7 / 200)) (c := (28 / 25))
      (q := (113328685307 / 1000000000000)) (k := 5) (J := 6)
      (R := ((-13409628869971) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (193 / 200) ^ 2) ≤ ((-267691497217147) / 100000000000000) :=
    logU (w := (2751 / 40000)) (c := (2751 / 2500))
      (q := (9567375006829 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-267691497217147) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (24 / 25)) ≤ ((-321887582486817) / 100000000000000) :=
    logU (w := (1 / 25)) (c := (32 / 25))
      (q := (24686007793153 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-321887582486817) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-350655799957011) / 100000000000000) ≤ Real.log (1 - (97 / 100)) :=
    logL (w := (3 / 100)) (c := (48 / 25))
      (q := (65232508378959 / 100000000000000)) (k := 6) (J := 6)
      (R := ((-350655799957011) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (24 / 25) ^ 2) ≤ ((-10183725406503) / 4000000000000) :=
    logU (w := (49 / 625)) (c := (784 / 625))
      (q := (22665737061401 / 100000000000000)) (k := 4) (J := 6)
      (R := ((-10183725406503) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-141426221557897) / 50000000000000) ≤ Real.log (1 - (97 / 100) ^ 2) :=
    logL (w := (591 / 10000)) (c := (1182 / 625))
      (q := (63721147164181 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-141426221557897) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (24 / 25) ≤ x → x ≤ (97 / 100) →
      (18404640229537 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (94995369997531 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (24 / 25)) (w := (1 / 100))
      (r1 := (1126746833 / 390625000))
      (r2 := (67874517 / 7812500)) (r3 := (1268379 / 156250))
      (r4 := (72171 / 12500))
      (R := (1486084424923 / 50000000000000))
      (NL := (18404640229537 / 10000000000000)) (NU := (94995369997531 / 50000000000000))
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
  exact Dfun_box_pos (a := (24 / 25)) (b := (97 / 100)) (m := (193 / 200))
    (hh := (1 / 200)) (K := (36961371909961 / 50000000000000))
    (bnd := (3872795361589 / 625000000000000))
    (Lu := ((-712543536331) / 20000000000000))
    (Ll := ((-3562729037879) / 100000000000000))
    (Ml := ((-13409628869971) / 4000000000000))
    (Nu := ((-267691497217147) / 100000000000000))
    (U1 := ((-321887582486817) / 100000000000000))
    (L1 := ((-350655799957011) / 100000000000000))
    (U2 := ((-10183725406503) / 4000000000000))
    (L2 := ((-141426221557897) / 50000000000000))
    (NL := (18404640229537 / 10000000000000))
    (NU := (94995369997531 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_113 {s : ℝ} (hs1 : (97 / 100) ≤ s) (hs2 : s ≤ (489 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (487 / 500) ≤ ((-164649839557) / 6250000000000) :=
    logU (w := (487 / 500)) (c := (487 / 250))
      (q := (33340160311541 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-164649839557) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-2634410927943) / 100000000000000) ≤ Real.log (487 / 500) :=
    logL (w := (487 / 500)) (c := (487 / 250))
      (q := (16670076782013 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-2634410927943) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-91241468641037) / 25000000000000) ≤ Real.log (1 - (487 / 500)) :=
    logL (w := (13 / 500)) (c := (208 / 125))
      (q := (25461216885911 / 50000000000000)) (k := 6) (J := 6)
      (R := ((-91241468641037) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (487 / 500) ^ 2) ≤ ((-4639994999899) / 1562500000000) :=
    logU (w := (12831 / 250000)) (c := (25662 / 15625))
      (q := (24806955143217 / 50000000000000)) (k := 5) (J := 6)
      (R := ((-4639994999899) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (97 / 100)) ≤ ((-21915986853639) / 6250000000000) :=
    logU (w := (3 / 100)) (c := (48 / 25))
      (q := (3261625933887 / 5000000000000)) (k := 6) (J := 6)
      (R := ((-21915986853639) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-47708910320673) / 12500000000000) ≤ Real.log (1 - (489 / 500)) :=
    logL (w := (11 / 500)) (c := (176 / 125))
      (q := (17108512885293 / 50000000000000)) (k := 6) (J := 6)
      (R := ((-47708910320673) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (97 / 100) ^ 2) ≤ ((-1767827721277) / 625000000000) :=
    logU (w := (591 / 10000)) (c := (1182 / 625))
      (q := (1274423097513 / 2000000000000)) (k := 5) (J := 6)
      (R := ((-1767827721277) / 625000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-156731329622151) / 50000000000000) ≤ Real.log (1 - (489 / 500) ^ 2) :=
    logL (w := (10879 / 250000)) (c := (21758 / 15625))
      (q := (33110931035673 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-156731329622151) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (97 / 100) ≤ x → x ≤ (489 / 500) →
      (187484574688661 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (192496905301463 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (97 / 100)) (w := (1 / 125))
      (r1 := (306068923523 / 100000000000))
      (r2 := (4467485259 / 500000000)) (r3 := (41762547 / 5000000))
      (r4 := (597051 / 100000))
      (R := (2506165306401 / 100000000000000))
      (NL := (187484574688661 / 100000000000000)) (NU := (192496905301463 / 100000000000000))
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
  exact Dfun_box_pos (a := (97 / 100)) (b := (489 / 500)) (m := (487 / 500))
    (hh := (1 / 250)) (K := (38838703275607 / 50000000000000))
    (bnd := (13993128400101 / 2500000000000000))
    (Lu := ((-164649839557) / 6250000000000))
    (Ll := ((-2634410927943) / 100000000000000))
    (Ml := ((-91241468641037) / 25000000000000))
    (Nu := ((-4639994999899) / 1562500000000))
    (U1 := ((-21915986853639) / 6250000000000))
    (L1 := ((-47708910320673) / 12500000000000))
    (U2 := ((-1767827721277) / 625000000000))
    (L2 := ((-156731329622151) / 50000000000000))
    (NL := (187484574688661 / 100000000000000))
    (NU := (192496905301463 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_114 {s : ℝ} (hs1 : (489 / 500) ≤ s) (hs2 : s ≤ (123 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (981 / 1000) ≤ ((-959140911969) / 50000000000000) :=
    logU (w := (981 / 1000)) (c := (981 / 500))
      (q := (8424554529007 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-959140911969) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-153463777) / 8000000000) ≤ Real.log (981 / 1000) :=
    logL (w := (981 / 1000)) (c := (981 / 500))
      (q := (13479284168699 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-153463777) / 8000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-15853265199263) / 4000000000000) ≤ Real.log (1 - (981 / 1000)) :=
    logL (w := (19 / 1000)) (c := (152 / 125))
      (q := (3911335670879 / 20000000000000)) (k := 6) (J := 6)
      (R := ((-15853265199263) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (981 / 1000) ^ 2) ≤ ((-13118858128397) / 4000000000000) :=
    logU (w := (37639 / 1000000)) (c := (37639 / 31250))
      (q := (3720427414009 / 20000000000000)) (k := 5) (J := 6)
      (R := ((-13118858128397) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (489 / 500)) ≤ ((-381671282562373) / 100000000000000) :=
    logU (w := (11 / 500)) (c := (176 / 125))
      (q := (34217025773591 / 100000000000000)) (k := 6) (J := 6)
      (R := ((-381671282562373) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-413516655674239) / 100000000000000) ≤ Real.log (1 - (123 / 125)) :=
    logL (w := (2 / 125)) (c := (128 / 125))
      (q := (2371652661731 / 100000000000000)) (k := 6) (J := 6)
      (R := ((-413516655674239) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (489 / 500) ^ 2) ≤ ((-313462659242323) / 100000000000000) :=
    logU (w := (10879 / 250000)) (c := (21758 / 15625))
      (q := (33110931037647 / 100000000000000)) (k := 5) (J := 6)
      (R := ((-313462659242323) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-34500515478797) / 10000000000000) ≤ Real.log (1 - (123 / 125) ^ 2) :=
    logL (w := (496 / 15625)) (c := (15872 / 15625))
      (q := (313687098401 / 20000000000000)) (k := 5) (J := 6)
      (R := ((-34500515478797) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (489 / 500) ≤ x → x ≤ (123 / 125) →
      (190540665179777 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (48613286355787 / 25000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (489 / 500)) (w := (3 / 500))
      (r1 := (3205264753549 / 1000000000000))
      (r2 := (571108973427 / 62500000000)) (r3 := (1068260643 / 125000000))
      (r4 := (3063987 / 500000))
      (R := (391248024337 / 20000000000000))
      (NL := (190540665179777 / 100000000000000)) (NU := (48613286355787 / 25000000000000))
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
  exact Dfun_box_pos (a := (489 / 500)) (b := (123 / 125)) (m := (981 / 1000))
    (hh := (3 / 1000)) (K := (39597570199091 / 50000000000000))
    (bnd := (24519128707 / 5000000000000))
    (Lu := ((-959140911969) / 50000000000000))
    (Ll := ((-153463777) / 8000000000))
    (Ml := ((-15853265199263) / 4000000000000))
    (Nu := ((-13118858128397) / 4000000000000))
    (U1 := ((-381671282562373) / 100000000000000))
    (L1 := ((-413516655674239) / 100000000000000))
    (U2 := ((-313462659242323) / 100000000000000))
    (L2 := ((-34500515478797) / 10000000000000))
    (NL := (190540665179777 / 100000000000000))
    (NU := (48613286355787 / 25000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_115 {s : ℝ} (hs1 : (123 / 125) ≤ s) (hs2 : s ≤ (989 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (1973 / 2000) ≤ ((-339798804861) / 25000000000000) :=
    logU (w := (1973 / 2000)) (c := (1973 / 1000))
      (q := (1359110456731 / 2000000000000)) (k := 1) (J := 6)
      (R := ((-339798804861) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-135921225093) / 10000000000000) ≤ Real.log (1973 / 2000) :=
    logL (w := (1973 / 2000)) (c := (1973 / 1000))
      (q := (13591101161013 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-135921225093) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-430506560501263) / 100000000000000) ≤ Real.log (1 - (1973 / 2000)) :=
    logL (w := (27 / 2000)) (c := (216 / 125))
      (q := (27348232945351 / 50000000000000)) (k := 7) (J := 6)
      (R := ((-430506560501263) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1973 / 2000) ^ 2) ≤ ((-45233641215211) / 12500000000000) :=
    logU (w := (107271 / 4000000)) (c := (107271 / 62500))
      (q := (13504794653569 / 25000000000000)) (k := 6) (J := 6)
      (R := ((-45233641215211) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (123 / 125)) ≤ ((-51689581959279) / 12500000000000) :=
    logU (w := (2 / 125)) (c := (128 / 125))
      (q := (592913165433 / 25000000000000)) (k := 6) (J := 6)
      (R := ((-51689581959279) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-450986000621379) / 100000000000000) ≤ Real.log (1 - (989 / 1000)) :=
    logL (w := (11 / 1000)) (c := (176 / 125))
      (q := (17108512885293 / 50000000000000)) (k := 7) (J := 6)
      (R := ((-450986000621379) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (123 / 125) ^ 2) ≤ ((-86251288696991) / 25000000000000) :=
    logU (w := (496 / 15625)) (c := (15872 / 15625))
      (q := (784217746003 / 50000000000000)) (k := 5) (J := 6)
      (R := ((-86251288696991) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-11944462519801) / 3125000000000) ≤ Real.log (1 - (989 / 1000) ^ 2) :=
    logL (w := (21879 / 1000000)) (c := (21879 / 15625))
      (q := (16832753851169 / 50000000000000)) (k := 6) (J := 6)
      (R := ((-11944462519801) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (123 / 125) ≤ x → x ≤ (989 / 1000) →
      (48192970274843 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (196134409746923 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (123 / 125)) (w := (1 / 200))
      (r1 := (1657922986861 / 500000000000))
      (r2 := (4537551393 / 488281250)) (r3 := (67926357 / 7812500))
      (r4 := (780759 / 125000))
      (R := (67250572951 / 4000000000000))
      (NL := (48192970274843 / 25000000000000)) (NU := (196134409746923 / 100000000000000))
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
  exact Dfun_box_pos (a := (123 / 125)) (b := (989 / 1000)) (m := (1973 / 2000))
    (hh := (1 / 400)) (K := (91600778340923 / 100000000000000))
    (bnd := (41487842230553 / 10000000000000000))
    (Lu := ((-339798804861) / 25000000000000))
    (Ll := ((-135921225093) / 10000000000000))
    (Ml := ((-430506560501263) / 100000000000000))
    (Nu := ((-45233641215211) / 12500000000000))
    (U1 := ((-51689581959279) / 12500000000000))
    (L1 := ((-450986000621379) / 100000000000000))
    (U2 := ((-86251288696991) / 25000000000000))
    (L2 := ((-11944462519801) / 3125000000000))
    (NL := (48192970274843 / 25000000000000))
    (NU := (196134409746923 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_116 {s : ℝ} (hs1 : (989 / 1000) ≤ s) (hs2 : s ≤ (124 / 125)) :
    0 < Dfun s := by
  have hLu : Real.log (1981 / 2000) ≤ ((-477270570059) / 50000000000000) :=
    logU (w := (1981 / 2000)) (c := (1981 / 1000))
      (q := (17090044228969 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-477270570059) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-23863986463) / 2500000000000) ≤ Real.log (1981 / 2000) :=
    logL (w := (1981 / 2000)) (c := (1981 / 1000))
      (q := (2734406343899 / 4000000000000)) (k := 1) (J := 6)
      (R := ((-23863986463) / 2500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-46564634803757) / 10000000000000) ≤ Real.log (1 - (1981 / 2000)) :=
    logL (w := (19 / 2000)) (c := (152 / 125))
      (q := (3911335670879 / 20000000000000)) (k := 7) (J := 6)
      (R := ((-46564634803757) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1981 / 2000) ^ 2) ≤ ((-396807761691737) / 100000000000000) :=
    logU (w := (75639 / 4000000)) (c := (75639 / 62500))
      (q := (19080546644227 / 100000000000000)) (k := 6) (J := 6)
      (R := ((-396807761691737) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (989 / 1000)) ≤ ((-450986000618367) / 100000000000000) :=
    logU (w := (11 / 1000)) (c := (176 / 125))
      (q := (34217025773591 / 100000000000000)) (k := 7) (J := 6)
      (R := ((-450986000618367) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-241415686865117) / 50000000000000) ≤ Real.log (1 - (124 / 125)) :=
    logL (w := (1 / 125)) (c := (128 / 125))
      (q := (2371652661731 / 100000000000000)) (k := 7) (J := 6)
      (R := ((-241415686865117) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (989 / 1000) ^ 2) ≤ ((-76444560126237) / 20000000000000) :=
    logU (w := (21879 / 1000000)) (c := (21879 / 15625))
      (q := (33665507704779 / 100000000000000)) (k := 6) (J := 6)
      (R := ((-76444560126237) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-413917457813993) / 100000000000000) ≤ Real.log (1 - (124 / 125) ^ 2) :=
    logL (w := (249 / 15625)) (c := (15936 / 15625))
      (q := (1970850521977 / 100000000000000)) (k := 6) (J := 6)
      (R := ((-413917457813993) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (989 / 1000) ≤ x → x ≤ (124 / 125) →
      (97551537482317 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (197165744529207 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (989 / 1000)) (w := (3 / 1000))
      (r1 := (681886050923 / 200000000000))
      (r2 := (4712132844927 / 500000000000)) (r3 := (4410239643 / 500000000))
      (r4 := (6344487 / 1000000))
      (R := (515667391143 / 50000000000000))
      (NL := (97551537482317 / 50000000000000)) (NU := (197165744529207 / 100000000000000))
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
  exact Dfun_box_pos (a := (989 / 1000)) (b := (124 / 125)) (m := (1981 / 2000))
    (hh := (3 / 2000)) (K := (82417233198473 / 100000000000000))
    (bnd := (133723766577 / 39062500000000))
    (Lu := ((-477270570059) / 50000000000000))
    (Ll := ((-23863986463) / 2500000000000))
    (Ml := ((-46564634803757) / 10000000000000))
    (Nu := ((-396807761691737) / 100000000000000))
    (U1 := ((-450986000618367) / 100000000000000))
    (L1 := ((-241415686865117) / 50000000000000))
    (U2 := ((-76444560126237) / 20000000000000))
    (L2 := ((-413917457813993) / 100000000000000))
    (NL := (97551537482317 / 50000000000000))
    (NU := (197165744529207 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_117 {s : ℝ} (hs1 : (124 / 125) ≤ s) (hs2 : s ≤ (199 / 200)) :
    0 < Dfun s := by
  have hLu : Real.log (1987 / 2000) ≤ ((-326060772703) / 50000000000000) :=
    logU (w := (1987 / 2000)) (c := (1987 / 1000))
      (q := (17165649127647 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-326060772703) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-8151761033) / 1250000000000) ≤ Real.log (1987 / 2000) :=
    logL (w := (1987 / 2000)) (c := (1987 / 1000))
      (q := (13732515434671 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-8151761033) / 1250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-251797655338069) / 50000000000000) ≤ Real.log (1 - (1987 / 2000)) :=
    logL (w := (13 / 2000)) (c := (208 / 125))
      (q := (25461216885911 / 50000000000000)) (k := 8) (J := 6)
      (R := ((-251797655338069) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1987 / 2000) ^ 2) ≤ ((-434606121422261) / 100000000000000) :=
    logU (w := (51831 / 4000000)) (c := (51831 / 31250))
      (q := (50596904969697 / 100000000000000)) (k := 7) (J := 6)
      (R := ((-434606121422261) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (124 / 125)) ≤ ((-241415686865113) / 50000000000000) :=
    logU (w := (1 / 125)) (c := (128 / 125))
      (q := (592913165433 / 25000000000000)) (k := 7) (J := 6)
      (R := ((-241415686865113) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-529831736654853) / 100000000000000) ≤ Real.log (1 - (199 / 200)) :=
    logL (w := (1 / 200)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 8) (J := 6)
      (R := ((-529831736654853) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (124 / 125) ^ 2) ≤ ((-206958728906993) / 50000000000000) :=
    logU (w := (249 / 15625)) (c := (15936 / 15625))
      (q := (985425260989 / 50000000000000)) (k := 6) (J := 6)
      (R := ((-206958728906993) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-57595916452583) / 12500000000000) ≤ Real.log (1 - (199 / 200) ^ 2) :=
    logL (w := (399 / 40000)) (c := (798 / 625))
      (q := (24435694771301 / 100000000000000)) (k := 7) (J := 6)
      (R := ((-57595916452583) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (124 / 125) ≤ x → x ≤ (199 / 200) →
      (196117302454579 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (99107093301917 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (124 / 125)) (w := (3 / 1000))
      (r1 := (1733107344247 / 500000000000))
      (r2 := (9281243817 / 976562500)) (r3 := (34753779 / 3906250))
      (r4 := (400221 / 62500))
      (R := (1048442074627 / 100000000000000))
      (NL := (196117302454579 / 100000000000000)) (NU := (99107093301917 / 50000000000000))
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
  exact Dfun_box_pos (a := (124 / 125)) (b := (199 / 200)) (m := (1987 / 2000))
    (hh := (3 / 2000)) (K := (2862206566013 / 2500000000000))
    (bnd := (3412027861387 / 1250000000000000))
    (Lu := ((-326060772703) / 50000000000000))
    (Ll := ((-8151761033) / 1250000000000))
    (Ml := ((-251797655338069) / 50000000000000))
    (Nu := ((-434606121422261) / 100000000000000))
    (U1 := ((-241415686865113) / 50000000000000))
    (L1 := ((-529831736654853) / 100000000000000))
    (U2 := ((-206958728906993) / 50000000000000))
    (L2 := ((-57595916452583) / 12500000000000))
    (NL := (196117302454579 / 100000000000000))
    (NU := (99107093301917 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_118 {s : ℝ} (hs1 : (199 / 200) ≤ s) (hs2 : s ≤ (997 / 1000)) :
    0 < Dfun s := by
  have hLu : Real.log (249 / 250) ≤ ((-400801977907) / 100000000000000) :=
    logU (w := (249 / 250)) (c := (249 / 125))
      (q := (68913916078087 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-400801977907) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-200411100361) / 50000000000000) ≤ Real.log (249 / 250) :=
    logL (w := (249 / 250)) (c := (249 / 125))
      (q := (68913895855273 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-200411100361) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-552146091786229) / 100000000000000) ≤ Real.log (1 - (249 / 250)) :=
    logL (w := (1 / 250)) (c := (128 / 125))
      (q := (2371652661731 / 100000000000000)) (k := 8) (J := 6)
      (R := ((-552146091786229) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (249 / 250) ^ 2) ≤ ((-483031573997293) / 100000000000000) :=
    logU (w := (499 / 62500)) (c := (15968 / 15625))
      (q := (434290478933 / 20000000000000)) (k := 7) (J := 6)
      (R := ((-483031573997293) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (199 / 200)) ≤ ((-529831736654799) / 100000000000000) :=
    logU (w := (1 / 200)) (c := (32 / 25))
      (q := (24686007793153 / 100000000000000)) (k := 8) (J := 6)
      (R := ((-529831736654799) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-580914299085337) / 100000000000000) ≤ Real.log (1 - (997 / 1000)) :=
    logL (w := (3 / 1000)) (c := (192 / 125))
      (q := (21459081709309 / 50000000000000)) (k := 9) (J := 6)
      (R := ((-580914299085337) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (199 / 200) ^ 2) ≤ ((-460767331620617) / 100000000000000) :=
    logU (w := (399 / 40000)) (c := (798 / 625))
      (q := (24435694771341 / 100000000000000)) (k := 7) (J := 6)
      (R := ((-460767331620617) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-255874846819811) / 50000000000000) ≤ Real.log (1 - (997 / 1000) ^ 2) :=
    logL (w := (5991 / 1000000)) (c := (23964 / 15625))
      (q := (21384025404169 / 50000000000000)) (k := 8) (J := 6)
      (R := ((-255874846819811) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (199 / 200) ≤ x → x ≤ (997 / 1000) →
      (39501129947299 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (19892272347117 / 10000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (199 / 200)) (w := (1 / 500))
      (r1 := (1761739780901 / 500000000000))
      (r2 := (38337652917 / 4000000000)) (r3 := (179483283 / 20000000))
      (r4 := (1292517 / 200000))
      (R := (708536867337 / 100000000000000))
      (NL := (39501129947299 / 20000000000000)) (NU := (19892272347117 / 10000000000000))
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
  exact Dfun_box_pos (a := (199 / 200)) (b := (997 / 1000)) (m := (249 / 250))
    (hh := (1 / 1000)) (K := (31686951637099 / 25000000000000))
    (bnd := (19959948724367 / 10000000000000000))
    (Lu := ((-400801977907) / 100000000000000))
    (Ll := ((-200411100361) / 50000000000000))
    (Ml := ((-552146091786229) / 100000000000000))
    (Nu := ((-483031573997293) / 100000000000000))
    (U1 := ((-529831736654799) / 100000000000000))
    (L1 := ((-580914299085337) / 100000000000000))
    (U2 := ((-460767331620617) / 100000000000000))
    (L2 := ((-255874846819811) / 50000000000000))
    (NL := (39501129947299 / 20000000000000))
    (NU := (19892272347117 / 10000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_119 {s : ℝ} (hs1 : (997 / 1000) ≤ s) (hs2 : s ≤ (499 / 500)) :
    0 < Dfun s := by
  have hLu : Real.log (399 / 400) ≤ ((-250312854847) / 100000000000000) :=
    logU (w := (399 / 400)) (c := (399 / 200))
      (q := (69064405201147 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-250312854847) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-250333625433) / 100000000000000) ≤ Real.log (399 / 400) :=
    logL (w := (399 / 400)) (c := (399 / 200))
      (q := (34532192215281 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-250333625433) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-9361663354857) / 1562500000000) ≤ Real.log (1 - (399 / 400)) :=
    logL (w := (1 / 400)) (c := (32 / 25))
      (q := (24686007793107 / 100000000000000)) (k := 9) (J := 6)
      (R := ((-9361663354857) / 1562500000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (399 / 400) ^ 2) ≤ ((-132489203711241) / 25000000000000) :=
    logU (w := (799 / 160000)) (c := (799 / 625))
      (q := (6140232400747 / 25000000000000)) (k := 8) (J := 6)
      (R := ((-132489203711241) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (997 / 1000)) ≤ ((-580914299031231) / 100000000000000) :=
    logU (w := (3 / 1000)) (c := (192 / 125))
      (q := (8583632694543 / 20000000000000)) (k := 9) (J := 6)
      (R := ((-580914299031231) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-38841300615139) / 6250000000000) ≤ Real.log (1 - (499 / 500)) :=
    logL (w := (1 / 500)) (c := (128 / 125))
      (q := (2371652661731 / 100000000000000)) (k := 9) (J := 6)
      (R := ((-38841300615139) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (997 / 1000) ^ 2) ≤ ((-15992177924621) / 3125000000000) :=
    logU (w := (5991 / 1000000)) (c := (23964 / 15625))
      (q := (534600635751 / 1250000000000)) (k := 8) (J := 6)
      (R := ((-15992177924621) / 3125000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-552246141819587) / 100000000000000) ≤ Real.log (1 - (499 / 500) ^ 2) :=
    logL (w := (999 / 250000)) (c := (15984 / 15625))
      (q := (2271602628373 / 100000000000000)) (k := 8) (J := 6)
      (R := ((-552246141819587) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (997 / 1000) ≤ x → x ≤ (499 / 500) →
      (198565566215371 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (99639940363483 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (997 / 1000)) (w := (1 / 1000))
      (r1 := (3561925111807 / 1000000000000))
      (r2 := (4819206815559 / 500000000000)) (r3 := (4513011147 / 500000000))
      (r4 := (6501951 / 1000000))
      (R := (357157255797 / 100000000000000))
      (NL := (198565566215371 / 100000000000000)) (NU := (99639940363483 / 50000000000000))
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
  exact Dfun_box_pos (a := (997 / 1000)) (b := (499 / 500)) (m := (399 / 400))
    (hh := (1 / 2000)) (K := (14178378567277 / 12500000000000))
    (bnd := (1444587028443 / 1000000000000000))
    (Lu := ((-250312854847) / 100000000000000))
    (Ll := ((-250333625433) / 100000000000000))
    (Ml := ((-9361663354857) / 1562500000000))
    (Nu := ((-132489203711241) / 25000000000000))
    (U1 := ((-580914299031231) / 100000000000000))
    (L1 := ((-38841300615139) / 6250000000000))
    (U2 := ((-15992177924621) / 3125000000000))
    (L2 := ((-552246141819587) / 100000000000000))
    (NL := (198565566215371 / 100000000000000))
    (NU := (99639940363483 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_120 {s : ℝ} (hs1 : (499 / 500) ≤ s) (hs2 : s ≤ (2497 / 2500)) :
    0 < Dfun s := by
  have hLu : Real.log (624 / 625) ≤ ((-80063983297) / 50000000000000) :=
    logU (w := (624 / 625)) (c := (1248 / 625))
      (q := (345772950447 / 500000000000)) (k := 1) (J := 6)
      (R := ((-80063983297) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-51247703) / 32000000000) ≤ Real.log (624 / 625) :=
    logL (w := (624 / 625)) (c := (1248 / 625))
      (q := (1728864224603 / 2500000000000)) (k := 1) (J := 6)
      (R := ((-51247703) / 32000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-128755033058167) / 20000000000000) ≤ Real.log (1 - (624 / 625)) :=
    logL (w := (1 / 625)) (c := (1024 / 625))
      (q := (9874403053823 / 20000000000000)) (k := 10) (J := 6)
      (R := ((-128755033058167) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (624 / 625) ^ 2) ≤ ((-287270239466723) / 50000000000000) :=
    logU (w := (1249 / 390625)) (c := (639488 / 390625))
      (q := (98583967141 / 200000000000)) (k := 9) (J := 6)
      (R := ((-287270239466723) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (499 / 500)) ≤ ((-310730404921107) / 50000000000000) :=
    logU (w := (1 / 500)) (c := (128 / 125))
      (q := (592913165433 / 25000000000000)) (k := 9) (J := 6)
      (R := ((-310730404921107) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-168135843054707) / 25000000000000) ≤ Real.log (1 - (2497 / 2500)) :=
    logL (w := (3 / 2500)) (c := (768 / 625))
      (q := (10301904170561 / 50000000000000)) (k := 10) (J := 6)
      (R := ((-168135843054707) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (499 / 500) ^ 2) ≤ ((-276123070909789) / 50000000000000) :=
    logU (w := (999 / 250000)) (c := (15984 / 15625))
      (q := (1135801314187 / 50000000000000)) (k := 8) (J := 6)
      (R := ((-276123070909789) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-150822168042509) / 25000000000000) ≤ Real.log (1 - (2497 / 2500) ^ 2) :=
    logL (w := (14991 / 6250000)) (c := (479712 / 390625))
      (q := (20543790333919 / 100000000000000)) (k := 9) (J := 6)
      (R := ((-150822168042509) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (499 / 500) ≤ x → x ≤ (2497 / 2500) →
      (19899276334581 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199566998108121 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (499 / 500)) (w := (1 / 1250))
      (r1 := (3581229043163 / 1000000000000))
      (r2 := (604095671817 / 62500000000)) (r3 := (1131508683 / 125000000))
      (r4 := (3260817 / 500000))
      (R := (57423476231 / 20000000000000))
      (NL := (19899276334581 / 10000000000000)) (NU := (199566998108121 / 100000000000000))
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
  exact Dfun_box_pos (a := (499 / 500)) (b := (2497 / 2500)) (m := (624 / 625))
    (hh := (1 / 2500)) (K := (138593430725939 / 100000000000000))
    (bnd := (10467666322081 / 10000000000000000))
    (Lu := ((-80063983297) / 50000000000000))
    (Ll := ((-51247703) / 32000000000))
    (Ml := ((-128755033058167) / 20000000000000))
    (Nu := ((-287270239466723) / 50000000000000))
    (U1 := ((-310730404921107) / 50000000000000))
    (L1 := ((-168135843054707) / 25000000000000))
    (U2 := ((-276123070909789) / 50000000000000))
    (L2 := ((-150822168042509) / 25000000000000))
    (NL := (19899276334581 / 10000000000000))
    (NU := (199566998108121 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_121 {s : ℝ} (hs1 : (2497 / 2500) ≤ s) (hs2 : s ≤ (9993 / 10000)) :
    0 < Dfun s := by
  have hLu : Real.log (19981 / 20000) ≤ ((-95044981197) / 100000000000000) :=
    logU (w := (19981 / 20000)) (c := (19981 / 10000))
      (q := (69219673074797 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-95044981197) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-95066331053) / 100000000000000) ≤ Real.log (19981 / 20000) :=
    logL (w := (19981 / 20000)) (c := (19981 / 10000))
      (q := (34609825862471 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-95066331053) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-695904870429901) / 100000000000000) ≤ Real.log (1 - (19981 / 20000)) :=
    logL (w := (19 / 20000)) (c := (1216 / 625))
      (q := (16639257046511 / 25000000000000)) (k := 11) (J := 6)
      (R := ((-695904870429901) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (19981 / 20000) ^ 2) ≤ ((-626637650468389) / 100000000000000) :=
    logU (w := (759639 / 400000000)) (c := (759639 / 390625))
      (q := (66509530091551 / 100000000000000)) (k := 10) (J := 6)
      (R := ((-626637650468389) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (2497 / 2500)) ≤ ((-168135843054703) / 25000000000000) :=
    logU (w := (3 / 2500)) (c := (768 / 625))
      (q := (2575476042641 / 12500000000000)) (k := 10) (J := 6)
      (R := ((-168135843054703) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-5811544178383) / 800000000000) ≤ Real.log (1 - (9993 / 10000)) :=
    logL (w := (7 / 10000)) (c := (896 / 625))
      (q := (3601887631807 / 10000000000000)) (k := 11) (J := 6)
      (R := ((-5811544178383) / 800000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (2497 / 2500) ^ 2) ≤ ((-301644336085011) / 50000000000000) :=
    logU (w := (14991 / 6250000)) (c := (479712 / 390625))
      (q := (5135947583481 / 25000000000000)) (k := 9) (J := 6)
      (R := ((-301644336085011) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-328581655184119) / 50000000000000) ≤ Real.log (1 - (9993 / 10000) ^ 2) :=
    logL (w := (139951 / 100000000)) (c := (559804 / 390625))
      (q := (1124495943491 / 3125000000000)) (k := 10) (J := 6)
      (R := ((-328581655184119) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (2497 / 2500) ≤ x → x ≤ (9993 / 10000) →
      (199386920248361 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (99873537983939 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (2497 / 2500)) (w := (1 / 2000))
      (r1 := (35967112857 / 10000000000))
      (r2 := (1210910097377 / 125000000000)) (r3 := (28353012147 / 3125000000))
      (r4 := (16343451 / 2500000))
      (R := (90038929879 / 50000000000000))
      (NL := (199386920248361 / 100000000000000)) (NU := (99873537983939 / 50000000000000))
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
  exact Dfun_box_pos (a := (2497 / 2500)) (b := (9993 / 10000)) (m := (19981 / 20000))
    (hh := (1 / 4000)) (K := (4733862576123 / 3125000000000))
    (bnd := (884445159489 / 1250000000000000))
    (Lu := ((-95044981197) / 100000000000000))
    (Ll := ((-95066331053) / 100000000000000))
    (Ml := ((-695904870429901) / 100000000000000))
    (Nu := ((-626637650468389) / 100000000000000))
    (U1 := ((-168135843054703) / 25000000000000))
    (L1 := ((-5811544178383) / 800000000000))
    (U2 := ((-301644336085011) / 50000000000000))
    (L2 := ((-328581655184119) / 50000000000000))
    (NL := (199386920248361 / 100000000000000))
    (NU := (99873537983939 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_122 {s : ℝ} (hs1 : (9993 / 10000) ≤ s) (hs2 : s ≤ (2499 / 2500)) :
    0 < Dfun s := by
  have hLu : Real.log (19989 / 20000) ≤ ((-27507478359) / 50000000000000) :=
    logU (w := (19989 / 20000)) (c := (19989 / 10000))
      (q := (17314925774819 / 25000000000000)) (k := 1) (J := 6)
      (R := ((-27507478359) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-27518229139) / 50000000000000) ≤ Real.log (19989 / 20000) :=
    logL (w := (19989 / 20000)) (c := (19989 / 10000))
      (q := (69259681597717 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-27518229139) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-750559227973781) / 100000000000000) ≤ Real.log (1 - (19989 / 20000)) :=
    logL (w := (11 / 20000)) (c := (704 / 625))
      (q := (2975667660541 / 25000000000000)) (k := 11) (J := 6)
      (R := ((-750559227973781) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (19989 / 20000) ^ 2) ≤ ((-681272013699719) / 100000000000000) :=
    logU (w := (439879 / 400000000)) (c := (439879 / 390625))
      (q := (11875166860221 / 100000000000000)) (k := 10) (J := 6)
      (R := ((-681272013699719) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (9993 / 10000)) ≤ ((-181610755573017) / 25000000000000) :=
    logU (w := (7 / 10000)) (c := (896 / 625))
      (q := (18009438161933 / 50000000000000)) (k := 11) (J := 6)
      (R := ((-181610755573017) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-31296184056113) / 4000000000000) ≤ Real.log (1 - (2499 / 2500)) :=
    logL (w := (1 / 2500)) (c := (1024 / 625))
      (q := (9874403053823 / 20000000000000)) (k := 12) (J := 6)
      (R := ((-31296184056113) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (9993 / 10000) ^ 2) ≤ ((-82145413795313) / 12500000000000) :=
    logU (w := (139951 / 100000000)) (c := (559804 / 390625))
      (q := (8995967549359 / 25000000000000)) (k := 10) (J := 6)
      (R := ((-82145413795313) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-713109885345481) / 100000000000000) ≤ Real.log (1 - (2499 / 2500) ^ 2) :=
    logL (w := (4999 / 6250000)) (c := (639872 / 390625))
      (q := (771125207351 / 1562500000000)) (k := 11) (J := 6)
      (R := ((-713109885345481) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (9993 / 10000) ≤ x → x ≤ (2499 / 2500) →
      (199638796474003 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (799421421847 / 400000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (9993 / 10000)) (w := (3 / 10000))
      (r1 := (450800671809 / 125000000000))
      (r2 := (4850450017919 / 500000000000)) (r3 := (454302424467 / 50000000000))
      (r4 := (65472219 / 10000000))
      (R := (108279493873 / 100000000000000))
      (NL := (199638796474003 / 100000000000000)) (NU := (799421421847 / 400000000000))
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
  exact Dfun_box_pos (a := (9993 / 10000)) (b := (2499 / 2500)) (m := (19989 / 20000))
    (hh := (3 / 20000)) (K := (163914525692533 / 100000000000000))
    (bnd := (2312082662637 / 5000000000000000))
    (Lu := ((-27507478359) / 50000000000000))
    (Ll := ((-27518229139) / 50000000000000))
    (Ml := ((-750559227973781) / 100000000000000))
    (Nu := ((-681272013699719) / 100000000000000))
    (U1 := ((-181610755573017) / 25000000000000))
    (L1 := ((-31296184056113) / 4000000000000))
    (U2 := ((-82145413795313) / 12500000000000))
    (L2 := ((-713109885345481) / 100000000000000))
    (NL := (199638796474003 / 100000000000000))
    (NU := (799421421847 / 400000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_123 {s : ℝ} (hs1 : (2499 / 2500) ≤ s) (hs2 : s ≤ (9997 / 10000)) :
    0 < Dfun s := by
  have hLu : Real.log (19993 / 20000) ≤ ((-17502975941) / 50000000000000) :=
    logU (w := (19993 / 20000)) (c := (19993 / 10000))
      (q := (4329982006507 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-17502975941) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-35027529637) / 100000000000000) ≤ Real.log (19993 / 20000) :=
    logL (w := (19993 / 20000)) (c := (19993 / 10000))
      (q := (34639845263179 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-35027529637) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-79575774035387) / 10000000000000) ≤ Real.log (1 - (19993 / 20000)) :=
    logL (w := (7 / 20000)) (c := (896 / 625))
      (q := (3601887631807 / 10000000000000)) (k := 12) (J := 6)
      (R := ((-79575774035387) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (19993 / 20000) ^ 2) ≤ ((-726460523823497) / 100000000000000) :=
    logU (w := (279951 / 400000000)) (c := (559902 / 390625))
      (q := (36001374792437 / 100000000000000)) (k := 11) (J := 6)
      (R := ((-726460523823497) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (2499 / 2500)) ≤ ((-782404601084321) / 100000000000000) :=
    logU (w := (1 / 2500)) (c := (1024 / 625))
      (q := (49372015587607 / 100000000000000)) (k := 12) (J := 6)
      (R := ((-782404601084321) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-405586404165409) / 50000000000000) ≤ Real.log (1 - (9997 / 10000)) :=
    logL (w := (3 / 10000)) (c := (768 / 625))
      (q := (10301904170561 / 50000000000000)) (k := 12) (J := 6)
      (R := ((-405586404165409) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (2499 / 2500) ^ 2) ≤ ((-713109885028601) / 100000000000000) :=
    logU (w := (4999 / 6250000)) (c := (639872 / 390625))
      (q := (49352013587333 / 100000000000000)) (k := 11) (J := 6)
      (R := ((-713109885028601) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-148374618279987) / 20000000000000) ≤ Real.log (1 - (9997 / 10000) ^ 2) :=
    logL (w := (59991 / 100000000)) (c := (479928 / 390625))
      (q := (2058880721601 / 10000000000000)) (k := 11) (J := 6)
      (R := ((-148374618279987) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (2499 / 2500) ≤ x → x ≤ (9997 / 10000) →
      (199819223468073 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (3123304491491 / 1562500000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (2499 / 2500)) (w := (1 / 10000))
      (r1 := (3612228368433 / 1000000000000))
      (r2 := (9709081016041 / 1000000000000)) (r3 := (28418464683 / 3125000000))
      (r4 := (16382817 / 2500000))
      (R := (1445279747 / 4000000000000))
      (NL := (199819223468073 / 100000000000000)) (NU := (3123304491491 / 1562500000000))
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
  exact Dfun_box_pos (a := (2499 / 2500)) (b := (9997 / 10000)) (m := (19993 / 20000))
    (hh := (1 / 20000)) (K := (62062515356777 / 50000000000000))
    (bnd := (805493169123 / 2500000000000000))
    (Lu := ((-17502975941) / 50000000000000))
    (Ll := ((-35027529637) / 100000000000000))
    (Ml := ((-79575774035387) / 10000000000000))
    (Nu := ((-726460523823497) / 100000000000000))
    (U1 := ((-782404601084321) / 100000000000000))
    (L1 := ((-405586404165409) / 50000000000000))
    (U2 := ((-713109885028601) / 100000000000000))
    (L2 := ((-148374618279987) / 20000000000000))
    (NL := (199819223468073 / 100000000000000))
    (NU := (3123304491491 / 1562500000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_124 {s : ℝ} (hs1 : (9997 / 10000) ≤ s) (hs2 : s ≤ (4999 / 5000)) :
    0 < Dfun s := by
  have hLu : Real.log (3999 / 4000) ≤ ((-25002950613) / 100000000000000) :=
    logU (w := (3999 / 4000)) (c := (3999 / 2000))
      (q := (69289715105381 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-25002950613) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-25024566553) / 100000000000000) ≤ Real.log (3999 / 4000) :=
    logL (w := (3999 / 4000)) (c := (3999 / 2000))
      (q := (34644846744721 / 50000000000000)) (k := 1) (J := 6)
      (R := ((-25024566553) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-829404964010209) / 100000000000000) ≤ Real.log (1 - (3999 / 4000)) :=
    logL (w := (1 / 4000)) (c := (128 / 125))
      (q := (2371652661731 / 100000000000000)) (k := 12) (J := 6)
      (R := ((-829404964010209) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (3999 / 4000) ^ 2) ≤ ((-760102746735517) / 100000000000000) :=
    logU (w := (7999 / 16000000)) (c := (15998 / 15625))
      (q := (2359151880417 / 100000000000000)) (k := 11) (J := 6)
      (R := ((-760102746735517) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (9997 / 10000)) ≤ ((-2027932020827) / 250000000000) :=
    logU (w := (3 / 10000)) (c := (768 / 625))
      (q := (2575476042641 / 12500000000000)) (k := 12) (J := 6)
      (R := ((-2027932020827) / 250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-42585965972941) / 5000000000000) ≤ Real.log (1 - (4999 / 5000)) :=
    logL (w := (1 / 5000)) (c := (1024 / 625))
      (q := (9874403053823 / 20000000000000)) (k := 13) (J := 6)
      (R := ((-42585965972941) / 5000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (9997 / 10000) ^ 2) ≤ ((-741873091399919) / 100000000000000) :=
    logU (w := (59991 / 100000000)) (c := (479928 / 390625))
      (q := (4117761443203 / 20000000000000)) (k := 11) (J := 6)
      (R := ((-741873091399919) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-15648292038041) / 2000000000000) ≤ Real.log (1 - (4999 / 5000) ^ 2) :=
    logL (w := (9999 / 25000000)) (c := (639936 / 390625))
      (q := (4936201476989 / 10000000000000)) (k := 12) (J := 6)
      (R := ((-15648292038041) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (9997 / 10000) ≤ x → x ≤ (4999 / 5000) →
      (12490958502383 / 6250000000000) ≤ Npoly x ∧
      Npoly x ≤ (199927638872719 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (9997 / 10000)) (w := (1 / 10000))
      (r1 := (90354261437 / 25000000000))
      (r2 := (4855904790939 / 500000000000)) (r3 := (454826517147 / 50000000000))
      (r4 := (65550951 / 10000000))
      (R := (7230283459 / 20000000000000))
      (NL := (12490958502383 / 6250000000000)) (NU := (199927638872719 / 100000000000000))
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
  exact Dfun_box_pos (a := (9997 / 10000)) (b := (4999 / 5000)) (m := (3999 / 4000))
    (hh := (1 / 20000)) (K := (37601072622299 / 25000000000000))
    (bnd := (2450221072029 / 10000000000000000))
    (Lu := ((-25002950613) / 100000000000000))
    (Ll := ((-25024566553) / 100000000000000))
    (Ml := ((-829404964010209) / 100000000000000))
    (Nu := ((-760102746735517) / 100000000000000))
    (U1 := ((-2027932020827) / 250000000000))
    (L1 := ((-42585965972941) / 5000000000000))
    (U2 := ((-741873091399919) / 100000000000000))
    (L2 := ((-15648292038041) / 2000000000000))
    (NL := (12490958502383 / 6250000000000))
    (NU := (199927638872719 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_125 {s : ℝ} (hs1 : (4999 / 5000) ≤ s) (hs2 : s ≤ (99989 / 100000)) :
    0 < Dfun s := by
  have hLu : Real.log (199969 / 200000) ≤ ((-3875256531) / 25000000000000) :=
    logU (w := (199969 / 200000)) (c := (199969 / 100000))
      (q := (6929921702987 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-3875256531) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-1940334799) / 12500000000000) ≤ Real.log (199969 / 200000) :=
    logL (w := (199969 / 200000)) (c := (199969 / 100000))
      (q := (69299195377603 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-1940334799) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-877208544104539) / 100000000000000) ≤ Real.log (1 - (199969 / 200000)) :=
    logL (w := (31 / 200000)) (c := (3968 / 3125))
      (q := (5970697655849 / 25000000000000)) (k := 13) (J := 6)
      (R := ((-877208544104539) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (199969 / 200000) ^ 2) ≤ ((-807901576348829) / 100000000000000) :=
    logU (w := (12399039 / 40000000000)) (c := (12399039 / 9765625))
      (q := (23875040323099 / 100000000000000)) (k := 12) (J := 6)
      (R := ((-807901576348829) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (4999 / 5000)) ≤ ((-170343863828063) / 20000000000000) :=
    logU (w := (1 / 5000)) (c := (1024 / 625))
      (q := (49372015587607 / 100000000000000)) (k := 13) (J := 6)
      (R := ((-170343863828063) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-113937877763569) / 12500000000000) ≤ Real.log (1 - (99989 / 100000)) :=
    logL (w := (11 / 100000)) (c := (5632 / 3125))
      (q := (29451515337689 / 50000000000000)) (k := 14) (J := 6)
      (R := ((-113937877763569) / 12500000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (4999 / 5000) ^ 2) ≤ ((-391207300792179) / 50000000000000) :=
    logU (w := (9999 / 25000000)) (c := (639936 / 390625))
      (q := (4936201508757 / 10000000000000)) (k := 12) (J := 6)
      (R := ((-391207300792179) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-842193804200457) / 100000000000000) ≤ Real.log (1 - (99989 / 100000) ^ 2) :=
    logL (w := (2199879 / 10000000000)) (c := (17599032 / 9765625))
      (q := (29448765263739 / 50000000000000)) (k := 13) (J := 6)
      (R := ((-842193804200457) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (4999 / 5000) ≤ x → x ≤ (99989 / 100000) →
      (99947542992723 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199960191759989 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (4999 / 5000)) (w := (9 / 100000))
      (r1 := (3616113092319 / 1000000000000))
      (r2 := (4857269467163 / 500000000000)) (r3 := (113739409683 / 12500000000))
      (r4 := (32785317 / 5000000))
      (R := (32552887271 / 100000000000000))
      (NL := (99947542992723 / 50000000000000)) (NU := (199960191759989 / 100000000000000))
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
  exact Dfun_box_pos (a := (4999 / 5000)) (b := (99989 / 100000)) (m := (199969 / 200000))
    (hh := (9 / 200000)) (K := (192193580074689 / 100000000000000))
    (bnd := (103135266187 / 625000000000000))
    (Lu := ((-3875256531) / 25000000000000))
    (Ll := ((-1940334799) / 12500000000000))
    (Ml := ((-877208544104539) / 100000000000000))
    (Nu := ((-807901576348829) / 100000000000000))
    (U1 := ((-170343863828063) / 20000000000000))
    (L1 := ((-113937877763569) / 12500000000000))
    (U2 := ((-391207300792179) / 50000000000000))
    (L2 := ((-842193804200457) / 100000000000000))
    (NL := (99947542992723 / 50000000000000))
    (NU := (199960191759989 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_126 {s : ℝ} (hs1 : (99989 / 100000) ≤ s) (hs2 : s ≤ (49997 / 50000)) :
    0 < Dfun s := by
  have hLu : Real.log (199983 / 200000) ≤ ((-8500185767) / 100000000000000) :=
    logU (w := (199983 / 200000)) (c := (199983 / 100000))
      (q := (69306217870227 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-8500185767) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4260932419) / 50000000000000) ≤ Real.log (199983 / 200000) :=
    logL (w := (199983 / 200000)) (c := (199983 / 100000))
      (q := (69306196191157 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-4260932419) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-468642965074689) / 50000000000000) ≤ Real.log (1 - (199983 / 200000)) :=
    logL (w := (17 / 200000)) (c := (4352 / 3125))
      (q := (4140015329319 / 12500000000000)) (k := 14) (J := 6)
      (R := ((-468642965074689) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (199983 / 200000) ^ 2) ≤ ((-173595092436341) / 20000000000000) :=
    logU (w := (6799711 / 40000000000)) (c := (13599422 / 9765625))
      (q := (33115872546217 / 100000000000000)) (k := 13) (J := 6)
      (R := ((-173595092436341) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (99989 / 100000)) ≤ ((-455751509600111) / 50000000000000) :=
    logU (w := (11 / 100000)) (c := (5632 / 3125))
      (q := (29451516791847 / 50000000000000)) (k := 14) (J := 6)
      (R := ((-455751509600111) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-194423323086513) / 20000000000000) ≤ Real.log (1 - (49997 / 50000)) :=
    logL (w := (3 / 50000)) (c := (6144 / 3125))
      (q := (13203936603 / 19531250000)) (k := 15) (J := 6)
      (R := ((-194423323086513) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (99989 / 100000) ^ 2) ≤ ((-421096900647753) / 50000000000000) :=
    logU (w := (2199879 / 10000000000)) (c := (17599032 / 9765625))
      (q := (1840547919763 / 3125000000000)) (k := 13) (J := 6)
      (R := ((-421096900647753) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-902804897412941) / 100000000000000) ≤ Real.log (1 - (49997 / 50000) ^ 2) :=
    logL (w := (299991 / 2500000000)) (c := (19199424 / 9765625))
      (q := (67601155370989 / 100000000000000)) (k := 14) (J := 6)
      (R := ((-902804897412941) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (99989 / 100000) ≤ x → x ≤ (49997 / 50000) →
      (49985525005243 / 25000000000000) ≤ Npoly x ∧
      Npoly x ≤ (39995656699801 / 20000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (99989 / 100000)) (w := (1 / 20000))
      (r1 := (723572386091 / 200000000000))
      (r2 := (9716996024277 / 1000000000000)) (r3 := (9101513636329 / 1000000000000))
      (r4 := (655883487 / 100000000))
      (R := (2261467377 / 12500000000000))
      (NL := (49985525005243 / 25000000000000)) (NU := (39995656699801 / 20000000000000))
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
  exact Dfun_box_pos (a := (99989 / 100000)) (b := (49997 / 50000)) (m := (199983 / 200000))
    (hh := (1 / 40000)) (K := (204200617316343 / 100000000000000))
    (bnd := (994812337581 / 10000000000000000))
    (Lu := ((-8500185767) / 100000000000000))
    (Ll := ((-4260932419) / 50000000000000))
    (Ml := ((-468642965074689) / 50000000000000))
    (Nu := ((-173595092436341) / 20000000000000))
    (U1 := ((-455751509600111) / 50000000000000))
    (L1 := ((-194423323086513) / 20000000000000))
    (U2 := ((-421096900647753) / 50000000000000))
    (L2 := ((-902804897412941) / 100000000000000))
    (NL := (49985525005243 / 25000000000000))
    (NU := (39995656699801 / 20000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_127 {s : ℝ} (hs1 : (49997 / 50000) ≤ s) (hs2 : s ≤ (99997 / 100000)) :
    0 < Dfun s := by
  have hLu : Real.log (199991 / 200000) ≤ ((-899985121) / 20000000000000) :=
    logU (w := (199991 / 200000)) (c := (199991 / 100000))
      (q := (69310218130389 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-899985121) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-4521620003) / 100000000000000) ≤ Real.log (199991 / 200000) :=
    logL (w := (199991 / 200000)) (c := (199991 / 100000))
      (q := (8663774554499 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-4521620003) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-40035392273381) / 4000000000000) ≤ Real.log (1 - (199991 / 200000)) :=
    logL (w := (9 / 200000)) (c := (4608 / 3125))
      (q := (194179820027 / 500000000000)) (k := 15) (J := 6)
      (R := ((-40035392273381) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (199991 / 200000) ^ 2) ≤ ((-232893084697167) / 25000000000000) :=
    logU (w := (3599919 / 40000000000)) (c := (14399676 / 9765625))
      (q := (2427107124703 / 6250000000000)) (k := 14) (J := 6)
      (R := ((-232893084697167) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (49997 / 50000)) ≤ ((-243029149862793) / 25000000000000) :=
    logU (w := (3 / 50000)) (c := (6144 / 3125))
      (q := (33802085694369 / 50000000000000)) (k := 15) (J := 6)
      (R := ((-243029149862793) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-13017891668607) / 1250000000000) ≤ Real.log (1 - (99997 / 100000)) :=
    logL (w := (3 / 100000)) (c := (6144 / 3125))
      (q := (13203936603 / 19531250000)) (k := 16) (J := 6)
      (R := ((-13017891668607) / 1250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (49997 / 50000) ^ 2) ≤ ((-902804881440257) / 100000000000000) :=
    logU (w := (299991 / 2500000000)) (c := (19199424 / 9765625))
      (q := (67601171343659 / 100000000000000)) (k := 14) (J := 6)
      (R := ((-902804881440257) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1944236230879) / 200000000000) ≤ Real.log (1 - (99997 / 100000) ^ 2) :=
    logL (w := (599991 / 10000000000)) (c := (19199712 / 9765625))
      (q := (2704106216017 / 4000000000000)) (k := 15) (J := 6)
      (R := ((-1944236230879) / 200000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (49997 / 50000) ≤ x → x ≤ (99997 / 100000) →
      (19996742612323 / 10000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199989140874777 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (49997 / 50000)) (w := (3 / 100000))
      (r1 := (1809416849161 / 500000000000))
      (r2 := (971836134971 / 100000000000)) (r3 := (4551412750859 / 500000000000))
      (r4 := (327990951 / 50000000))
      (R := (10857375773 / 100000000000000))
      (NL := (19996742612323 / 10000000000000)) (NU := (199989140874777 / 100000000000000))
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
  exact Dfun_box_pos (a := (49997 / 50000)) (b := (99997 / 100000)) (m := (199991 / 200000))
    (hh := (3 / 200000)) (K := (28829193365133 / 12500000000000))
    (bnd := (288187290071 / 5000000000000000))
    (Lu := ((-899985121) / 20000000000000))
    (Ll := ((-4521620003) / 100000000000000))
    (Ml := ((-40035392273381) / 4000000000000))
    (Nu := ((-232893084697167) / 25000000000000))
    (U1 := ((-243029149862793) / 25000000000000))
    (L1 := ((-13017891668607) / 1250000000000))
    (U2 := ((-902804881440257) / 100000000000000))
    (L2 := ((-1944236230879) / 200000000000))
    (NL := (19996742612323 / 10000000000000))
    (NU := (199989140874777 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_128 {s : ℝ} (hs1 : (99997 / 100000) ≤ s) (hs2 : s ≤ (49999 / 50000)) :
    0 < Dfun s := by
  have hLu : Real.log (39999 / 40000) ≤ ((-249985553) / 10000000000000) :=
    logU (w := (39999 / 40000)) (c := (39999 / 20000))
      (q := (4332013637529 / 6250000000000)) (k := 1) (J := 6)
      (R := ((-249985553) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-630389399) / 25000000000000) ≤ Real.log (39999 / 40000) :=
    logL (w := (39999 / 40000)) (c := (39999 / 20000))
      (q := (69312196498399 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-630389399) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-211932694725361) / 20000000000000) ≤ Real.log (1 - (39999 / 40000)) :=
    logL (w := (1 / 40000)) (c := (1024 / 625))
      (q := (9874403053823 / 20000000000000)) (k := 16) (J := 6)
      (R := ((-211932694725361) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (39999 / 40000) ^ 2) ≤ ((-247587501315029) / 25000000000000) :=
    logU (w := (79999 / 1600000000)) (c := (639992 / 390625))
      (q := (24685382789897 / 50000000000000)) (k := 15) (J := 6)
      (R := ((-247587501315029) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (99997 / 100000)) ≤ ((-520715658753583) / 50000000000000) :=
    logU (w := (3 / 100000)) (c := (6144 / 3125))
      (q := (33802085694369 / 50000000000000)) (k := 16) (J := 6)
      (R := ((-520715658753583) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-1081977828441183) / 100000000000000) ≤ Real.log (1 - (49999 / 50000)) :=
    logL (w := (1 / 50000)) (c := (4096 / 3125))
      (q := (27057660454737 / 100000000000000)) (k := 16) (J := 6)
      (R := ((-1081977828441183) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (99997 / 100000) ^ 2) ≤ ((-972118099462461) / 100000000000000) :=
    logU (w := (599991 / 10000000000)) (c := (19199712 / 9765625))
      (q := (67602671377449 / 100000000000000)) (k := 15) (J := 6)
      (R := ((-972118099462461) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-253166027597547) / 25000000000000) ≤ Real.log (1 - (49999 / 50000) ^ 2) :=
    logL (w := (99999 / 2500000000)) (c := (12799872 / 9765625))
      (q := (27056660449737 / 100000000000000)) (k := 15) (J := 6)
      (R := ((-253166027597547) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (99997 / 100000) ≤ x → x ≤ (49999 / 50000) →
      (199985521360757 / 100000000000000) ≤ Npoly x ∧
      Npoly x ≤ (99996380194397 / 50000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (99997 / 100000)) (w := (1 / 100000))
      (r1 := (1809708412291 / 500000000000))
      (r2 := (9719180639429 / 1000000000000)) (r3 := (910361271543 / 100000000000))
      (r4 := (656040951 / 100000000))
      (R := (1809757009 / 50000000000000))
      (NL := (199985521360757 / 100000000000000)) (NU := (99996380194397 / 50000000000000))
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
  exact Dfun_box_pos (a := (99997 / 100000)) (b := (49999 / 50000)) (m := (39999 / 40000))
    (hh := (1 / 200000)) (K := (191202176735067 / 100000000000000))
    (bnd := (345047726003 / 10000000000000000))
    (Lu := ((-249985553) / 10000000000000))
    (Ll := ((-630389399) / 25000000000000))
    (Ml := ((-211932694725361) / 20000000000000))
    (Nu := ((-247587501315029) / 25000000000000))
    (U1 := ((-520715658753583) / 50000000000000))
    (L1 := ((-1081977828441183) / 100000000000000))
    (U2 := ((-972118099462461) / 100000000000000))
    (L2 := ((-253166027597547) / 25000000000000))
    (NL := (199985521360757 / 100000000000000))
    (NU := (99996380194397 / 50000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_129 {s : ℝ} (hs1 : (49999 / 50000) ≤ s) (hs2 : s ≤ (99999 / 100000)) :
    0 < Dfun s := by
  have hLu : Real.log (199997 / 200000) ≤ ((-749917747) / 50000000000000) :=
    logU (w := (199997 / 200000)) (c := (199997 / 100000))
      (q := (138626436441 / 200000000000)) (k := 1) (J := 6)
      (R := ((-749917747) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-760770697) / 50000000000000) ≤ Real.log (199997 / 200000) :=
    logL (w := (199997 / 200000)) (c := (199997 / 100000))
      (q := (69313196514601 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-760770697) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-222149210308911) / 20000000000000) ≤ Real.log (1 - (199997 / 200000)) :=
    logL (w := (3 / 200000)) (c := (6144 / 3125))
      (q := (13203936603 / 19531250000)) (k := 17) (J := 6)
      (R := ((-222149210308911) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (199997 / 200000) ^ 2) ≤ ((-520716033754999) / 50000000000000) :=
    logU (w := (1199991 / 40000000000)) (c := (19199856 / 9765625))
      (q := (33801710692953 / 50000000000000)) (k := 16) (J := 6)
      (R := ((-520716033754999) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (49999 / 50000)) ≤ ((-1081977828441019) / 100000000000000) :=
    logU (w := (1 / 50000)) (c := (4096 / 3125))
      (q := (5411532090977 / 20000000000000)) (k := 16) (J := 6)
      (R := ((-1081977828441019) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-575646273248589) / 50000000000000) ≤ Real.log (1 - (99999 / 100000)) :=
    logL (w := (1 / 100000)) (c := (4096 / 3125))
      (q := (27057660454737 / 100000000000000)) (k := 17) (J := 6)
      (R := ((-575646273248589) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (49999 / 50000) ^ 2) ≤ ((-40506564415601) / 4000000000000) :=
    logU (w := (99999 / 2500000000)) (c := (12799872 / 9765625))
      (q := (5411332089977 / 20000000000000)) (k := 15) (J := 6)
      (R := ((-40506564415601) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1081978328442433) / 100000000000000) ≤ Real.log (1 - (99999 / 100000) ^ 2) :=
    logL (w := (199999 / 10000000000)) (c := (12799936 / 9765625))
      (q := (27057160453487 / 100000000000000)) (k := 16) (J := 6)
      (R := ((-1081978328442433) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (49999 / 50000) ≤ x → x ≤ (99999 / 100000) →
      (39997828136077 / 20000000000000) ≤ Npoly x ∧
      Npoly x ≤ (499990950243 / 250000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (49999 / 50000)) (w := (1 / 100000))
      (r1 := (1809805605463 / 500000000000))
      (r2 := (9719453751747 / 1000000000000)) (r3 := (9103875135747 / 1000000000000))
      (r4 := (328030317 / 50000000))
      (R := (3619708407 / 100000000000000))
      (NL := (39997828136077 / 20000000000000)) (NU := (499990950243 / 250000000000))
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
  exact Dfun_box_pos (a := (49999 / 50000)) (b := (99999 / 100000)) (m := (199997 / 200000))
    (hh := (1 / 200000)) (K := (10010713666139 / 4000000000000))
    (bnd := (109698653837 / 5000000000000000))
    (Lu := ((-749917747) / 50000000000000))
    (Ll := ((-760770697) / 50000000000000))
    (Ml := ((-222149210308911) / 20000000000000))
    (Nu := ((-520716033754999) / 50000000000000))
    (U1 := ((-1081977828441019) / 100000000000000))
    (L1 := ((-575646273248589) / 50000000000000))
    (U2 := ((-40506564415601) / 4000000000000))
    (L2 := ((-1081978328442433) / 100000000000000))
    (NL := (39997828136077 / 20000000000000))
    (NU := (499990950243 / 250000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_130 {s : ℝ} (hs1 : (99999 / 100000) ≤ s) (hs2 : s ≤ (199999 / 200000)) :
    0 < Dfun s := by
  have hLu : Real.log (399997 / 400000) ≤ ((-749827029) / 100000000000000) :=
    logU (w := (399997 / 400000)) (c := (399997 / 200000))
      (q := (13862793645793 / 20000000000000)) (k := 1) (J := 6)
      (R := ((-749827029) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-385767903) / 50000000000000) ≤ Real.log (399997 / 400000) :=
    logL (w := (399997 / 400000)) (c := (399997 / 200000))
      (q := (69313946520189 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-385767903) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-23601215392011) / 2000000000000) ≤ Real.log (1 - (399997 / 400000)) :=
    logL (w := (3 / 400000)) (c := (6144 / 3125))
      (q := (13203936603 / 19531250000)) (k := 18) (J := 6)
      (R := ((-23601215392011) / 2000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (399997 / 400000) ^ 2) ≤ ((-1110746410563873) / 100000000000000) :=
    logU (w := (2399991 / 160000000000)) (c := (19199928 / 9765625))
      (q := (2704151855521 / 4000000000000)) (k := 17) (J := 6)
      (R := ((-1110746410563873) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (99999 / 100000)) ≤ ((-1151292546497013) / 100000000000000) :=
    logU (w := (1 / 100000)) (c := (4096 / 3125))
      (q := (5411532090977 / 20000000000000)) (k := 17) (J := 6)
      (R := ((-1151292546497013) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-1220607264553173) / 100000000000000) ≤ Real.log (1 - (199999 / 200000)) :=
    logL (w := (1 / 200000)) (c := (4096 / 3125))
      (q := (27057660454737 / 100000000000000)) (k := 18) (J := 6)
      (R := ((-1220607264553173) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (99999 / 100000) ^ 2) ≤ ((-1081978328442269) / 100000000000000) :=
    logU (w := (199999 / 10000000000)) (c := (12799936 / 9765625))
      (q := (5411432090727 / 20000000000000)) (k := 16) (J := 6)
      (R := ((-1081978328442269) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1151292796497491) / 100000000000000) ≤ Real.log (1 - (199999 / 200000) ^ 2) :=
    logL (w := (399999 / 40000000000)) (c := (12799968 / 9765625))
      (q := (3382176306803 / 12500000000000)) (k := 17) (J := 6)
      (R := ((-1151292796497491) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (99999 / 100000) ≤ x → x ≤ (199999 / 200000) →
      (99997285085049 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199998190024301 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (99999 / 100000)) (w := (1 / 200000))
      (r1 := (904951400683 / 250000000000))
      (r2 := (9719726871937 / 1000000000000)) (r3 := (9104137563937 / 1000000000000))
      (r4 := (656080317 / 100000000))
      (R := (1809927101 / 100000000000000))
      (NL := (99997285085049 / 50000000000000)) (NU := (199998190024301 / 100000000000000))
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
  exact Dfun_box_pos (a := (99999 / 100000)) (b := (199999 / 200000)) (m := (399997 / 400000))
    (hh := (1 / 400000)) (K := (1313524374387 / 500000000000))
    (bnd := (117289304527 / 10000000000000000))
    (Lu := ((-749827029) / 100000000000000))
    (Ll := ((-385767903) / 50000000000000))
    (Ml := ((-23601215392011) / 2000000000000))
    (Nu := ((-1110746410563873) / 100000000000000))
    (U1 := ((-1151292546497013) / 100000000000000))
    (L1 := ((-1220607264553173) / 100000000000000))
    (U2 := ((-1081978328442269) / 100000000000000))
    (L2 := ((-1151292796497491) / 100000000000000))
    (NL := (99997285085049 / 50000000000000))
    (NU := (199998190024301 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_131 {s : ℝ} (hs1 : (199999 / 200000) ≤ s) (hs2 : s ≤ (999997 / 1000000)) :
    0 < Dfun s := by
  have hLu : Real.log (249999 / 250000) ≤ ((-99956251) / 25000000000000) :=
    logU (w := (249999 / 250000)) (c := (249999 / 125000))
      (q := (6931431823099 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-99956251) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-421535123) / 100000000000000) ≤ Real.log (249999 / 250000) :=
    logL (w := (249999 / 250000)) (c := (249999 / 125000))
      (q := (8664287065109 / 12500000000000)) (k := 1) (J := 6)
      (R := ((-421535123) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-1242921619684447) / 100000000000000) ≤ Real.log (1 - (249999 / 250000)) :=
    logL (w := (1 / 250000)) (c := (16384 / 15625))
      (q := (4743305323463 / 100000000000000)) (k := 18) (J := 6)
      (R := ((-1242921619684447) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (249999 / 250000) ^ 2) ≤ ((-586803550814317) / 50000000000000) :=
    logU (w := (499999 / 62500000000)) (c := (255999488 / 244140625))
      (q := (18527755169 / 390625000000)) (k := 17) (J := 6)
      (R := ((-586803550814317) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (199999 / 200000)) ≤ ((-1220607264553007) / 100000000000000) :=
    logU (w := (1 / 200000)) (c := (4096 / 3125))
      (q := (5411532090977 / 20000000000000)) (k := 18) (J := 6)
      (R := ((-1220607264553007) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-50867593081451) / 4000000000000) ≤ Real.log (1 - (999997 / 1000000)) :=
    logL (w := (3 / 1000000)) (c := (24576 / 15625))
      (q := (4528981602763 / 10000000000000)) (k := 19) (J := 6)
      (R := ((-50867593081451) / 4000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (199999 / 200000) ^ 2) ≤ ((-575646398248663) / 50000000000000) :=
    logU (w := (399999 / 40000000000)) (c := (12799968 / 9765625))
      (q := (6764352613643 / 25000000000000)) (k := 17) (J := 6)
      (R := ((-575646398248663) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-300593814745097) / 25000000000000) ≤ Real.log (1 - (999997 / 1000000) ^ 2) :=
    logL (w := (5999991 / 1000000000000)) (c := (383999424 / 244140625))
      (q := (22644833013761 / 50000000000000)) (k := 18) (J := 6)
      (R := ((-300593814745097) / 25000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (199999 / 200000) ≤ x → x ≤ (999997 / 1000000) →
      (3999949320797 / 2000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199998914008749 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (199999 / 200000)) (w := (1 / 500000))
      (r1 := (3619902800683 / 1000000000000))
      (r2 := (1943972686997 / 200000000000)) (r3 := (1820853756197 / 200000000000))
      (r4 := (1312180317 / 200000000))
      (R := (723984449 / 100000000000000))
      (NL := (3999949320797 / 2000000000000)) (NU := (199998914008749 / 100000000000000))
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
  exact Dfun_box_pos (a := (199999 / 200000)) (b := (999997 / 1000000)) (m := (249999 / 250000))
    (hh := (1 / 1000000)) (K := (48467871748357 / 20000000000000))
    (bnd := (16358851439 / 2500000000000000))
    (Lu := ((-99956251) / 25000000000000))
    (Ll := ((-421535123) / 100000000000000))
    (Ml := ((-1242921619684447) / 100000000000000))
    (Nu := ((-586803550814317) / 50000000000000))
    (U1 := ((-1220607264553007) / 100000000000000))
    (L1 := ((-50867593081451) / 4000000000000))
    (U2 := ((-575646398248663) / 50000000000000))
    (L2 := ((-300593814745097) / 25000000000000))
    (NL := (3999949320797 / 2000000000000))
    (NU := (199998914008749 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_132 {s : ℝ} (hs1 : (999997 / 1000000) ≤ s) (hs2 : s ≤ (499999 / 500000)) :
    0 < Dfun s := by
  have hLu : Real.log (399999 / 400000) ≤ ((-249824511) / 100000000000000) :=
    logU (w := (399999 / 400000)) (c := (399999 / 200000))
      (q := (69314468231483 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-249824511) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-54307041) / 20000000000000) ≤ Real.log (399999 / 400000) :=
    logL (w := (399999 / 400000)) (c := (399999 / 200000))
      (q := (6931444652079 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-54307041) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-80620123913073) / 6250000000000) ≤ Real.log (1 - (399999 / 400000)) :=
    logL (w := (1 / 400000)) (c := (4096 / 3125))
      (q := (27057660454737 / 100000000000000)) (k := 19) (J := 6)
      (R := ((-80620123913073) / 6250000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (399999 / 400000) ^ 2) ≤ ((-244121477910617) / 20000000000000) :=
    logU (w := (799999 / 160000000000)) (c := (12799984 / 9765625))
      (q := (27057535454807 / 100000000000000)) (k := 18) (J := 6)
      (R := ((-244121477910617) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (999997 / 1000000)) ≤ ((-635844913464619) / 50000000000000) :=
    logU (w := (3 / 1000000)) (c := (24576 / 15625))
      (q := (5661227016831 / 12500000000000)) (k := 19) (J := 6)
      (R := ((-635844913464619) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-656118168870221) / 50000000000000) ≤ Real.log (1 - (499999 / 500000)) :=
    logL (w := (1 / 500000)) (c := (16384 / 15625))
      (q := (4743305323463 / 100000000000000)) (k := 19) (J := 6)
      (R := ((-656118168870221) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (999997 / 1000000) ^ 2) ≤ ((-1202375258873357) / 100000000000000) :=
    logU (w := (5999991 / 1000000000000)) (c := (383999424 / 244140625))
      (q := (9057933226907 / 20000000000000)) (k := 18) (J := 6)
      (R := ((-1202375258873357) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-1242921719684497) / 100000000000000) ≤ Real.log (1 - (499999 / 500000) ^ 2) :=
    logL (w := (999999 / 250000000000)) (c := (255999744 / 244140625))
      (q := (4743205323413 / 100000000000000)) (k := 18) (J := 6)
      (R := ((-1242921719684497) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (999997 / 1000000) ≤ x → x ≤ (499999 / 500000) →
      (99999276006803 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199999276003889 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (999997 / 1000000)) (w := (1 / 1000000))
      (r1 := (1809970840123 / 500000000000))
      (r2 := (1943983612151 / 200000000000)) (r3 := (1820864253671 / 200000000000))
      (r4 := (6560940951 / 1000000000))
      (R := (361995141 / 100000000000000))
      (NL := (99999276006803 / 50000000000000)) (NU := (199999276003889 / 100000000000000))
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
  exact Dfun_box_pos (a := (999997 / 1000000)) (b := (499999 / 500000)) (m := (399999 / 400000))
    (hh := (1 / 2000000)) (K := (232559610496777 / 100000000000000))
    (bnd := (20845652197 / 5000000000000000))
    (Lu := ((-249824511) / 100000000000000))
    (Ll := ((-54307041) / 20000000000000))
    (Ml := ((-80620123913073) / 6250000000000))
    (Nu := ((-244121477910617) / 20000000000000))
    (U1 := ((-635844913464619) / 50000000000000))
    (L1 := ((-656118168870221) / 50000000000000))
    (U2 := ((-1202375258873357) / 100000000000000))
    (L2 := ((-1242921719684497) / 100000000000000))
    (NL := (99999276006803 / 50000000000000))
    (NU := (199999276003889 / 100000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hLu hLl hMl hNu hU1 hL1 hU2 hL2
    (by norm_num) (by norm_num)
    (fun x hx1 hx2 => (hN x hx1 hx2).1) (fun x hx1 hx2 => (hN x hx1 hx2).2)
    (by norm_num) (by simp only [log2Lo, Cval, Ppoly]; norm_num)
    (by simp only [log2Lo, Cval]; norm_num)
    (by simp only [log2Hi, Cval]; norm_num)
    (by norm_num) hs1 hs2

theorem box_133 {s : ℝ} (hs1 : (499999 / 500000) ≤ s) (hs2 : s ≤ (999999 / 1000000)) :
    0 < Dfun s := by
  have hLu : Real.log (1999997 / 2000000) ≤ ((-149824307) / 100000000000000) :=
    logU (w := (1999997 / 2000000)) (c := (1999997 / 1000000))
      (q := (69314568231687 / 100000000000000)) (k := 1) (J := 6)
      (R := ((-149824307) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hLl : ((-34307077) / 20000000000000) ≤ Real.log (1999997 / 2000000) :=
    logL (w := (1999997 / 2000000)) (c := (1999997 / 1000000))
      (q := (6931454652061 / 10000000000000)) (k := 1) (J := 6)
      (R := ((-34307077) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hMl : ((-134100454509227) / 10000000000000) ≤ Real.log (1 - (1999997 / 2000000)) :=
    logL (w := (3 / 2000000)) (c := (24576 / 15625))
      (q := (4528981602763 / 10000000000000)) (k := 20) (J := 6)
      (R := ((-134100454509227) / 10000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hNu : Real.log (1 - (1999997 / 2000000) ^ 2) ≤ ((-635844950964633) / 50000000000000) :=
    logU (w := (11999991 / 4000000000000)) (c := (383999712 / 244140625))
      (q := (2264487056731 / 5000000000000)) (k := 19) (J := 6)
      (R := ((-635844950964633) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hU1 : Real.log (1 - (499999 / 500000)) ≤ ((-656118168870211) / 50000000000000) :=
    logU (w := (1 / 500000)) (c := (16384 / 15625))
      (q := (592913165433 / 12500000000000)) (k := 19) (J := 6)
      (R := ((-656118168870211) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL1 : ((-1381551055796437) / 100000000000000) ≤ Real.log (1 - (999999 / 1000000)) :=
    logL (w := (1 / 1000000)) (c := (16384 / 15625))
      (q := (4743305323463 / 100000000000000)) (k := 20) (J := 6)
      (R := ((-1381551055796437) / 100000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hU2 : Real.log (1 - (499999 / 500000) ^ 2) ≤ ((-621460859842239) / 50000000000000) :=
    logU (w := (999999 / 250000000000)) (c := (255999744 / 244140625))
      (q := (2371602661707 / 50000000000000)) (k := 18) (J := 6)
      (R := ((-621460859842239) / 50000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logHi, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Lo]; norm_num)
  have hL2 : ((-262447277548091) / 20000000000000) ≤ Real.log (1 - (999999 / 1000000) ^ 2) :=
    logL (w := (1999999 / 1000000000000)) (c := (255999872 / 244140625))
      (q := (94865106469 / 2000000000000)) (k := 19) (J := 6)
      (R := ((-262447277548091) / 20000000000000))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [Constants.logLo, Constants.logMid,
            Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
      (by simp only [log2Hi]; norm_num)
  have hN : ∀ x : ℝ, (499999 / 500000) ≤ x → x ≤ (999999 / 1000000) →
      (99999457003401 / 50000000000000) ≤ Npoly x ∧
      Npoly x ≤ (199999638000973 / 100000000000000) := by
    intro x hx1 hx2
    exact Npoly_box_bounds (a := (499999 / 500000)) (w := (1 / 1000000))
      (r1 := (361996112011 / 100000000000))
      (r2 := (4859972686879 / 500000000000)) (r3 := (4552173756079 / 500000000000))
      (r4 := (3280480317 / 500000000))
      (R := (72399417 / 20000000000000))
      (NL := (99999457003401 / 50000000000000)) (NU := (199999638000973 / 100000000000000))
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
  exact Dfun_box_pos (a := (499999 / 500000)) (b := (999999 / 1000000)) (m := (1999997 / 2000000))
    (hh := (1 / 2000000)) (K := (29163798064901 / 10000000000000))
    (bnd := (12492742247 / 5000000000000000))
    (Lu := ((-149824307) / 100000000000000))
    (Ll := ((-34307077) / 20000000000000))
    (Ml := ((-134100454509227) / 10000000000000))
    (Nu := ((-635844950964633) / 50000000000000))
    (U1 := ((-656118168870211) / 50000000000000))
    (L1 := ((-1381551055796437) / 100000000000000))
    (U2 := ((-621460859842239) / 50000000000000))
    (L2 := ((-262447277548091) / 20000000000000))
    (NL := (99999457003401 / 50000000000000))
    (NU := (199999638000973 / 100000000000000))
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
