/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Series
import EntropyBound.Proofs.Toolbox.Poly
import EntropyBound.Proofs.Constants.LogEnclose
import EntropyBound.Proofs.Diagonal.Endpoints

/-!
# Stage G item G4 — machinery for `diagonal_middle` (`SKETCH.md` (7d))

This file builds the **box machinery** announced by `BLUEPRINT.md` Stage G item G4.  It does
*not* yet contain the frozen theorem `diagonal_middle` (#43); it contains the reusable
ingredients and the mandated spot check.

1. `Dfun_sqrt_free` — on `[0,1]` the `sqrt` in `Dfun` disappears:
   `Dfun s = (9/10) enat (s^2) - Cval enat s + (log 2 / 10) * (4 (1-s) Ppoly s)`,
   using frozen `gprofile_sq_eq` (#19).
2. `fser_mono` and `enat_antitone` — `s ↦ enat s` is antitone on `(0,1]`, the monotonicity
   that lets a box be bounded by its endpoints.  Proved from frozen `enat_series_form` (#9).
3. `le_enat_of` / `enat_le_of` — turn a rational enclosure of `Real.log z` and
   `Real.log (1-z)` into a rational enclosure of `enat z`.
4. `log_le_of_inv` / `le_log_of_inv` — the `a⁻¹ > 1` route into the shared certified
   enclosure API `EntropyBound.Constants.logLo_le` / `.le_logHi` (that file is owned by
   another agent this iteration and is only *read* here).
5. `Dfun_box_lower` — the per-box lower bound assembling 1–3.
6. The `BLUEPRINT.md` Stage G cheat-watch spot check `example : 0 < Dfun (686/1000)`,
   proved *by* `Dfun_box_lower` on a genuine positive-width rational box straddling the known
   near-minimum of `Dfun`.

All support lemmas live in `namespace EntropyBound.Diagonal`.
-/

noncomputable section

namespace EntropyBound.Diagonal

open EntropyBound

/-! ### 1. The `sqrt`-free form of `Dfun` -/

/-- On `[0,1]` the square root in `Dfun` is a polynomial: `g(s)^2 = 4 (1-s) P(s)` (#19). -/
theorem Dfun_sqrt_free {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Dfun s = 9 / 10 * enat (s ^ 2) - Cval * enat s
      + Real.log 2 / 10 * (4 * (1 - s) * Ppoly s) := by
  rw [Dfun, EntropyBound.gprofile_sq_eq_proof s ⟨hs0, hs1⟩]

/-! ### 2. `enat` is antitone on `(0,1]` -/

/-- `fser` is monotone on `[0,1]`: the series is termwise monotone in `z`. -/
theorem fser_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : fser x ≤ fser y := by
  simp only [fser]
  refine Summable.tsum_le_tsum (fun m => ?_) (Toolbox.summable_fser_term hx (hxy.trans hy))
    (Toolbox.summable_fser_term (hx.trans hxy) hy)
  gcongr

/-- **Monotonicity of the normalized entropy.**  `s ↦ enat s` is antitone on `(0,1]`. -/
theorem enat_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) : enat y ≤ enat x := by
  have hy0 : 0 < y := hx.trans_le hxy
  rw [EntropyBound.enat_series_form_proof x hx (hxy.trans hy),
    EntropyBound.enat_series_form_proof y hy0 hy]
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hf : fser x ≤ fser y := fser_mono hx.le hxy hy
  linarith

/-! ### 3. Rational enclosures for `enat` from rational enclosures of `Real.log` -/

/-- Lower bound for `enat z` from **upper** bounds on `Real.log z` and `Real.log (1-z)`. -/
theorem le_enat_of {z LU MU : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h1 : Real.log z ≤ LU) (h2 : Real.log (1 - z) ≤ MU) :
    (-(z * LU) - (1 - z) * MU) / z ≤ enat z := by
  have h3 : (0 : ℝ) < 1 - z := by linarith
  rw [enat, le_div_iff₀ hz0, div_mul_cancel₀ _ (ne_of_gt hz0)]
  simp only [Hnat]
  linarith [mul_le_mul_of_nonneg_left h1 hz0.le, mul_le_mul_of_nonneg_left h2 h3.le]

/-- Upper bound for `enat z` from **lower** bounds on `Real.log z` and `Real.log (1-z)`. -/
theorem enat_le_of {z LL ML : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h1 : LL ≤ Real.log z) (h2 : ML ≤ Real.log (1 - z)) :
    enat z ≤ (-(z * LL) - (1 - z) * ML) / z := by
  have h3 : (0 : ℝ) < 1 - z := by linarith
  rw [enat, div_le_div_iff_of_pos_right hz0]
  simp only [Hnat]
  linarith [mul_le_mul_of_nonneg_left h1 hz0.le, mul_le_mul_of_nonneg_left h2 h3.le]

/-! ### 4. The `a⁻¹ > 1` route into the certified rational log enclosure API

`EntropyBound/Proofs/Constants/LogEnclose.lean` evaluates most cheaply for arguments `≥ 1`
(its `logTail_of_one_le` strips the absolute value).  For `0 < x < 1` we therefore apply the
API at `x⁻¹ > 1` and use `Real.log_inv`. -/

/-- Certified rational **upper** bound for `Real.log x`, `0 < x`, routed through `x⁻¹`. -/
theorem log_le_of_inv (x : ℚ) (J : ℕ) (hx : 0 < x) :
    Real.log (x : ℝ) ≤ -((Constants.logLo x⁻¹ J : ℚ) : ℝ) := by
  have hinv : (0 : ℚ) < x⁻¹ := inv_pos.mpr hx
  have h := Constants.logLo_le x⁻¹ J hinv
  rw [Rat.cast_inv, Real.log_inv] at h
  linarith

/-- Certified rational **lower** bound for `Real.log x`, `0 < x`, routed through `x⁻¹`. -/
theorem le_log_of_inv (x : ℚ) (J : ℕ) (hx : 0 < x) :
    -((Constants.logHi x⁻¹ J : ℚ) : ℝ) ≤ Real.log (x : ℝ) := by
  have hinv : (0 : ℚ) < x⁻¹ := inv_pos.mpr hx
  have h := Constants.le_logHi x⁻¹ J hinv
  rw [Rat.cast_inv, Real.log_inv] at h
  linarith

/-! ### 5. The per-box lower bound

On a rational box `[a,b] ⊆ (0,1)` every piece of the `sqrt`-free `Dfun` is bounded by an
endpoint value: `enat (s^2) ≥ enat (b^2)` and `enat s ≤ enat a` by `enat_antitone`, and
`(1-s) * Ppoly s ≥ (1-b) * Pl` for any certified lower bound `Pl` of `Ppoly` on the box. -/

theorem Dfun_box_lower {a b lo hi Pl s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hlo : lo ≤ enat (b ^ 2)) (hhi : enat a ≤ hi) (hPl0 : 0 ≤ Pl)
    (hPl : ∀ x : ℝ, a ≤ x → x ≤ b → Pl ≤ Ppoly x)
    (hs1 : a ≤ s) (hs2 : s ≤ b) :
    9 / 10 * lo - Cval * hi + Real.log 2 / 10 * (4 * (1 - b) * Pl) ≤ Dfun s := by
  have hs0 : 0 < s := ha.trans_le hs1
  have hs1' : s < 1 := hs2.trans_lt hb
  have hb0 : 0 < b := ha.trans_le hab
  -- `enat (s^2) ≥ enat (b^2) ≥ lo`
  have hsq : enat (b ^ 2) ≤ enat (s ^ 2) := by
    refine enat_antitone (by positivity) (by nlinarith) (by nlinarith)
  -- `enat s ≤ enat a ≤ hi`
  have hen : enat s ≤ enat a := enat_antitone ha hs1 (hs2.trans hb.le)
  -- the profile term
  have hP : Pl ≤ Ppoly s := hPl s hs1 hs2
  have hprod : 4 * (1 - b) * Pl ≤ 4 * (1 - s) * Ppoly s := by
    have h1 : (0 : ℝ) ≤ 1 - b := by linarith
    nlinarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hCval : (0 : ℝ) < Cval := by simp only [Cval]; norm_num
  rw [Dfun_sqrt_free hs0.le hs1'.le]
  have h1 : 9 / 10 * lo ≤ 9 / 10 * enat (s ^ 2) := by linarith
  have h2 : Cval * enat s ≤ Cval * hi := by nlinarith
  have h3 : Real.log 2 / 10 * (4 * (1 - b) * Pl) ≤ Real.log 2 / 10 * (4 * (1 - s) * Ppoly s) := by
    have : (0 : ℝ) ≤ Real.log 2 / 10 := by linarith
    nlinarith
  linarith

/-! ### 6. Numeric interface to the certified enclosures

The two lemmas below are the shape actually used at a box endpoint: the caller supplies the
**reciprocal** `x = 1/z ≥ 1` (so that `Constants.logTail_of_one_le` strips the absolute value
and the whole enclosure evaluates by `norm_num`), together with the rational bound `r`. -/

/-- Certified rational **upper** bound for `Real.log X` where `X = 1/x`. -/
theorem log_inv_le_num {x r : ℚ} {J : ℕ} {X R : ℝ} (hx : 0 < x)
    (hX : X = ((x : ℝ))⁻¹) (hR : (r : ℝ) = R) (h : -(Constants.logLo x J) ≤ r) :
    Real.log X ≤ R := by
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hlo := Constants.logLo_le x J hx
  have hcast : ((-(Constants.logLo x J) : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  rw [hX, Real.log_inv, ← hR]
  linarith

/-- Certified rational **lower** bound for `Real.log X` where `X = 1/x`. -/
theorem num_le_log_inv {x r : ℚ} {J : ℕ} {X R : ℝ} (hx : 0 < x)
    (hX : X = ((x : ℝ))⁻¹) (hR : (r : ℝ) = R) (h : r ≤ -(Constants.logHi x J)) :
    R ≤ Real.log X := by
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hhi := Constants.le_logHi x J hx
  have hcast : ((r : ℚ) : ℝ) ≤ ((-(Constants.logHi x J) : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  rw [hX, Real.log_inv, ← hR]
  linarith

end EntropyBound.Diagonal

/-! ### 7. The mandated Stage G spot check

`BLUEPRINT.md`'s Stage G cheat-watch box requires `example : 0 < Dfun (686/1000)` proved *by
the box machinery* — the point `s ≈ 0.686` is where `Dfun` attains its true minimum
`≈ 6.1 · 10⁻⁵`, so if the machinery cannot resolve it, it cannot resolve the range.

The box used is the genuine positive-width rational box
`[685997/1000000, 686003/1000000]` (width `6 · 10⁻⁶`), which contains `686/1000`.  The
certified lower bound produced by `Dfun_box_lower` on it is `≈ 2.7 · 10⁻⁵ > 0`. -/

namespace EntropyBound.DiagonalSpotCheck

open EntropyBound EntropyBound.Diagonal

/-- Certified lower bound for `Ppoly` on the spot-check box, by monotone bounding of the two
factors of `Ppoly`: the first is decreasing, the second increasing. -/
theorem Ppoly_lower (x : ℝ) (hx1 : (685997 : ℝ) / 1000000 ≤ x)
    (hx2 : x ≤ (686003 : ℝ) / 1000000) : (16913 : ℝ) / 10000 ≤ Ppoly x := by
  have hf1 : (107986123 : ℝ) / 100000000 ≤ 1 + 81 / 100 * (1 - x) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 686003 / 1000000 - x)
      (by linarith : (0:ℝ) ≤ 2 - x - 686003 / 1000000)]
  have hf2 : (156630551 : ℝ) / 100000000 ≤ 1 + x - 81 / 100 * x ^ 2 * (1 - x) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 685997 / 1000000)
      (by nlinarith : (0:ℝ) ≤ 1 - 81 / 100 * (x + 685997 / 1000000)
        + 81 / 100 * (x ^ 2 + x * (685997 / 1000000) + (685997 / 1000000) ^ 2))]
  simp only [Ppoly]
  calc (16913 : ℝ) / 10000
      ≤ (107986123 / 100000000) * (156630551 / 100000000) := by norm_num
    _ ≤ (1 + 81 / 100 * (1 - x) ^ 2) * (1 + x - 81 / 100 * x ^ 2 * (1 - x)) :=
        mul_le_mul hf1 hf2 (by norm_num) (by nlinarith [sq_nonneg (1 - x)])

/-- **The Stage G cheat-watch spot check**, proved by `Dfun_box_lower` on the rational box
`[685997/1000000, 686003/1000000]`. -/
theorem Dfun_686_pos : 0 < Dfun (686 / 1000) := by
  -- upper bounds for `log (b^2)` and `log (1 - b^2)`
  have hU1 : Real.log (((686003 : ℝ) / 1000000) ^ 2) ≤ -7537459 / 10000000 :=
    log_inv_le_num (x := (1000000000000 / 470600116009 : ℚ))
      (r := (-7537459 / 10000000 : ℚ)) (J := 6) (by norm_num)
      (by push_cast; norm_num) (by push_cast; norm_num)
      (by rw [Constants.logLo, Constants.logMid,
              Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
  have hU2 : Real.log (1 - ((686003 : ℝ) / 1000000) ^ 2) ≤ -6360111 / 10000000 :=
    log_inv_le_num (x := (1000000000000 / 529399883991 : ℚ))
      (r := (-6360111 / 10000000 : ℚ)) (J := 6) (by norm_num)
      (by push_cast; norm_num) (by push_cast; norm_num)
      (by rw [Constants.logLo, Constants.logMid,
              Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
  -- lower bounds for `log a` and `log (1 - a)`
  have hL1 : (-3768821 : ℝ) / 10000000 ≤ Real.log ((685997 : ℝ) / 1000000) :=
    num_le_log_inv (x := (1000000 / 685997 : ℚ))
      (r := (-3768821 / 10000000 : ℚ)) (J := 5) (by norm_num)
      (by push_cast; norm_num) (by push_cast; norm_num)
      (by rw [Constants.logHi, Constants.logMid,
              Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
  have hL2 : (-11583528 : ℝ) / 10000000 ≤ Real.log (1 - (685997 : ℝ) / 1000000) :=
    num_le_log_inv (x := (1000000 / 314003 : ℚ))
      (r := (-11583528 / 10000000 : ℚ)) (J := 9) (by norm_num)
      (by push_cast; norm_num) (by push_cast; norm_num)
      (by rw [Constants.logHi, Constants.logMid,
              Constants.logTail_of_one_le _ _ (by norm_num)]
          norm_num [Constants.yOf, Finset.sum_range_succ])
  -- a certified lower bound for `Real.log 2`
  have hlog2 : (6931469 : ℝ) / 10000000 ≤ Real.log 2 := by
    have h := Constants.logLo_le 2 6 (by norm_num)
    have hnum : ((6931469 / 10000000 : ℚ) : ℝ) ≤ ((Constants.logLo 2 6 : ℚ) : ℝ) := by
      have : (6931469 / 10000000 : ℚ) ≤ Constants.logLo 2 6 := by
        rw [Constants.logLo, Constants.logMid,
          Constants.logTail_of_one_le _ _ (by norm_num)]
        norm_num [Constants.yOf, Finset.sum_range_succ]
      exact_mod_cast this
    push_cast at hnum
    norm_num at h
    linarith
  -- the two endpoint enclosures for `enat`
  have hlo := le_enat_of (z := ((686003 : ℝ) / 1000000) ^ 2) (by norm_num) (by norm_num) hU1 hU2
  have hhi := enat_le_of (z := (685997 : ℝ) / 1000000) (by norm_num) (by norm_num) hL1 hL2
  have hbox := Dfun_box_lower (a := (685997 : ℝ) / 1000000) (b := (686003 : ℝ) / 1000000)
    (Pl := (16913 : ℝ) / 10000) (s := (686 : ℝ) / 1000)
    (by norm_num) (by norm_num) (by norm_num) hlo hhi (by norm_num) Ppoly_lower
    (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) <
      9 / 10 * ((-(((686003 : ℝ) / 1000000) ^ 2 * (-7537459 / 10000000))
          - (1 - ((686003 : ℝ) / 1000000) ^ 2) * (-6360111 / 10000000))
        / ((686003 : ℝ) / 1000000) ^ 2)
      - Cval * ((-((685997 : ℝ) / 1000000 * (-3768821 / 10000000))
          - (1 - (685997 : ℝ) / 1000000) * (-11583528 / 10000000))
        / ((685997 : ℝ) / 1000000))
      + (6931469 : ℝ) / 10000000 / 10
        * (4 * (1 - (686003 : ℝ) / 1000000) * ((16913 : ℝ) / 10000)) := by
    simp only [Cval]
    norm_num
  linarith

end EntropyBound.DiagonalSpotCheck

/-- The `BLUEPRINT.md` Stage G cheat-watch guardrail. -/
example : 0 < EntropyBound.Dfun (686 / 1000) := EntropyBound.DiagonalSpotCheck.Dfun_686_pos

end
