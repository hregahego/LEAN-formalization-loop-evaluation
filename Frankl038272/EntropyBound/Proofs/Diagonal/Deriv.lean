/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Poly
import EntropyBound.Proofs.Diagonal.Enclose

/-!
# Stage G item G4 — the derivative of `Dfun` and the derivative-corrected box bound

`REVIEW.md` iteration 2 requires a **derivative-corrected** per-box lower bound for `Dfun`:
the endpoint-monotone certificate `EntropyBound.Diagonal.Dfun_box_lower` of
`Proofs/Diagonal/Enclose.lean` loses `≈ 8 (b-a)` near the interior minimum, which is
prohibitive.  This file provides the ingredients.

All support lemmas live in `namespace EntropyBound.Diagonal`.
-/

noncomputable section

namespace EntropyBound.Diagonal

open EntropyBound

/-! ### 1. The derivative of `enat` and of `Dfun` -/

/-- The explicit elementary derivative of `Dfun` on `(0,1)`. -/
def Dder (s : ℝ) : ℝ :=
  9 / 5 * Real.log (1 - s ^ 2) / s ^ 3 - Cval * Real.log (1 - s) / s ^ 2
    - (2 * Real.log 2 / 5) * Npoly s

/-- `Hnat' z = log (1 - z) - log z` on `(0,1)`. -/
theorem hasDerivAt_Hnat {z : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    HasDerivAt Hnat (Real.log (1 - z) - Real.log z) z := by
  have hz : z ≠ 0 := ne_of_gt h0
  have hz1 : (1 : ℝ) - z ≠ 0 := by
    intro h; apply absurd h1; simp only [not_lt]; linarith [sub_eq_zero.mp h]
  have hid : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using hid.const_sub 1
  have hlog : HasDerivAt (fun x : ℝ => Real.log x) z⁻¹ z := Real.hasDerivAt_log hz
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - z)) z := hsub.log hz1
  have h1' : HasDerivAt (fun x : ℝ => -x * Real.log x) (-1 * Real.log z + -z * z⁻¹) z :=
    (hid.neg).mul hlog
  have h2' : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      (-1 * Real.log (1 - z) + (1 - z) * (-1 / (1 - z))) z := hsub.mul hlog1
  have := h1'.sub h2'
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `enat' z = log (1 - z) / z²` on `(0,1)`. -/
theorem hasDerivAt_enat {z : ℝ} (h0 : 0 < z) (h1 : z < 1) :
    HasDerivAt enat (Real.log (1 - z) / z ^ 2) z := by
  have hz : z ≠ 0 := ne_of_gt h0
  have hH := hasDerivAt_Hnat h0 h1
  have hid : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
  have hdiv : HasDerivAt (fun x : ℝ => Hnat x / x)
      (((Real.log (1 - z) - Real.log z) * z - Hnat z * 1) / z ^ 2) z := hH.div hid hz
  have heq : enat = fun x : ℝ => Hnat x / x := by funext x; rfl
  rw [heq]
  refine hdiv.congr_deriv ?_
  simp only [Hnat]
  field_simp
  ring

/-- **The derivative of `Dfun`.**  Obtained from the `sqrt`-free form `Dfun_sqrt_free`. -/
theorem hasDerivAt_Dfun {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : HasDerivAt Dfun (Dder s) s := by
  have hs : s ≠ 0 := ne_of_gt h0
  have hsq0 : 0 < s ^ 2 := by positivity
  have hsq1 : s ^ 2 < 1 := by nlinarith
  -- the three pieces
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s ^ 1) s := hasDerivAt_pow 2 s
  have hA : HasDerivAt (fun x : ℝ => enat (x ^ 2))
      (Real.log (1 - s ^ 2) / (s ^ 2) ^ 2 * (2 * s ^ 1)) s :=
    HasDerivAt.comp (h := fun x : ℝ => x ^ 2) s (hasDerivAt_enat hsq0 hsq1) hpow
  have hB : HasDerivAt enat (Real.log (1 - s) / s ^ 2) s := hasDerivAt_enat h0 h1
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have hP := ProfileSpeed.hasDerivAt_Ppoly s
  have hC0 : HasDerivAt (fun x : ℝ => (1 - x) * Ppoly x)
      (-1 * Ppoly s + (1 - s) *
        (19 / 100 - (45522 / 10000) * s + (107649 / 10000) * s ^ 2 - (78732 / 10000) * s ^ 3
          + (32805 / 10000) * s ^ 4)) s := hsub.mul hP
  have hC : HasDerivAt (fun x : ℝ => 4 * ((1 - x) * Ppoly x))
      (4 * (-1 * Ppoly s + (1 - s) *
        (19 / 100 - (45522 / 10000) * s + (107649 / 10000) * s ^ 2 - (78732 / 10000) * s ^ 3
          + (32805 / 10000) * s ^ 4))) s := by
    have h := hC0.const_mul (4 : ℝ)
    refine h.congr_deriv ?_
    ring
  have hsum : HasDerivAt (fun x : ℝ => 9 / 10 * enat (x ^ 2) - Cval * enat x
      + Real.log 2 / 10 * (4 * ((1 - x) * Ppoly x)))
      (9 / 10 * (Real.log (1 - s ^ 2) / (s ^ 2) ^ 2 * (2 * s ^ 1))
        - Cval * (Real.log (1 - s) / s ^ 2)
        + Real.log 2 / 10 * (4 * (-1 * Ppoly s + (1 - s) *
            (19 / 100 - (45522 / 10000) * s + (107649 / 10000) * s ^ 2
              - (78732 / 10000) * s ^ 3 + (32805 / 10000) * s ^ 4)))) s :=
    ((hA.const_mul _).sub (hB.const_mul _)).add (hC.const_mul _)
  -- transport along the `sqrt`-free identity, valid on the neighbourhood `Ioo 0 1`
  have hev : (fun x : ℝ => 9 / 10 * enat (x ^ 2) - Cval * enat x
      + Real.log 2 / 10 * (4 * ((1 - x) * Ppoly x))) =ᶠ[nhds s] Dfun := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    rw [Dfun_sqrt_free hx.1.le hx.2.le]
    ring
  refine (hsum.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [Dder, Npoly, Ppoly]
  field_simp
  ring

/-! ### 2. Elementary division monotonicity helpers -/

/-- For a **nonpositive** numerator, dividing by a larger positive denominator increases. -/
theorem div_le_div_of_nonpos_left {u p q : ℝ} (hu : u ≤ 0) (hp : 0 < p) (hpq : p ≤ q) :
    u / p ≤ u / q := by
  have hq : 0 < q := hp.trans_le hpq
  have key : u / p - u / q = u * (q - p) / (p * q) := by field_simp
  have hnum : u * (q - p) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu (by linarith)
  have : u * (q - p) / (p * q) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  linarith

/-- Dividing both sides of `c ≤ d` by a positive number. -/
theorem div_le_div_right' {c d p : ℝ} (h : c ≤ d) (hp : 0 < p) : c / p ≤ d / p := by
  gcongr

/-! ### 3. `enat` in logarithmic form -/

/-- `enat z = -log z - ((1-z)/z) log (1-z)` for `z ≠ 0`. -/
theorem enat_eq_log {z : ℝ} (hz : z ≠ 0) :
    enat z = -Real.log z - (1 - z) / z * Real.log (1 - z) := by
  simp only [enat, Hnat]
  field_simp

/-! ### 4. A certified rational lower bound for `Dfun` at a point -/

theorem Dfun_lower_at {m Lu Ll Ml Nu l2lo bnd : ℝ} (h0 : 0 < m) (h1 : m < 1)
    (hLu : Real.log m ≤ Lu) (hLl : Ll ≤ Real.log m)
    (hMl : Ml ≤ Real.log (1 - m)) (hNu : Real.log (1 - m ^ 2) ≤ Nu)
    (hl2 : l2lo ≤ Real.log 2)
    (hbnd : bnd ≤ 9 / 10 * (-2 * Lu - (1 - m ^ 2) / m ^ 2 * Nu)
      - Cval * (-Ll - (1 - m) / m * Ml) + l2lo / 10 * (4 * (1 - m) * Ppoly m)) :
    bnd ≤ Dfun m := by
  have hm : m ≠ 0 := ne_of_gt h0
  have hm2 : (m : ℝ) ^ 2 ≠ 0 := by positivity
  have hc1 : (0 : ℝ) ≤ (1 - m ^ 2) / m ^ 2 := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hc2 : (0 : ℝ) ≤ (1 - m) / m := div_nonneg (by linarith) h0.le
  have e1 : enat (m ^ 2) = -(2 * Real.log m) - (1 - m ^ 2) / m ^ 2 * Real.log (1 - m ^ 2) := by
    rw [enat_eq_log hm2, Real.log_pow]
    push_cast
    ring
  have e2 : enat m = -Real.log m - (1 - m) / m * Real.log (1 - m) := enat_eq_log hm
  have hP : 0 < Ppoly m := EntropyBound.Ppoly_pos_proof m ⟨h0.le, h1.le⟩
  have hgterm : (0 : ℝ) ≤ 4 * (1 - m) * Ppoly m := by
    have h4 : (0 : ℝ) ≤ 4 * (1 - m) := by linarith
    exact mul_nonneg h4 hP.le
  have hCval : (0 : ℝ) < Cval := by simp only [Cval]; norm_num
  have k1 : 9 / 10 * (-2 * Lu - (1 - m ^ 2) / m ^ 2 * Nu) ≤ 9 / 10 * enat (m ^ 2) := by
    rw [e1]
    have := mul_le_mul_of_nonneg_left hNu hc1
    linarith
  have k2 : Cval * enat m ≤ Cval * (-Ll - (1 - m) / m * Ml) := by
    rw [e2]
    have hstep := mul_le_mul_of_nonneg_left hMl hc2
    have : -Real.log m - (1 - m) / m * Real.log (1 - m) ≤ -Ll - (1 - m) / m * Ml := by linarith
    exact mul_le_mul_of_nonneg_left this hCval.le
  have k3 : l2lo / 10 * (4 * (1 - m) * Ppoly m)
      ≤ Real.log 2 / 10 * (4 * (1 - m) * Ppoly m) := by
    have hco : l2lo / 10 ≤ Real.log 2 / 10 := by linarith
    exact mul_le_mul_of_nonneg_right hco hgterm
  rw [Dfun_sqrt_free h0.le h1.le]
  linarith

/-! ### 5. A certified bound `|Dder| ≤ K` on a box -/

theorem abs_Dder_le {a b K L1 U1 L2 U2 NL NU l2lo l2hi : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hU1 : Real.log (1 - a) ≤ U1) (hL1 : L1 ≤ Real.log (1 - b))
    (hU2 : Real.log (1 - a ^ 2) ≤ U2) (hL2 : L2 ≤ Real.log (1 - b ^ 2))
    (hU1n : U1 ≤ 0) (hU2n : U2 ≤ 0)
    (hNL : ∀ x : ℝ, a ≤ x → x ≤ b → NL ≤ Npoly x)
    (hNU : ∀ x : ℝ, a ≤ x → x ≤ b → Npoly x ≤ NU)
    (hNL0 : 0 ≤ NL)
    (hl2lo : l2lo ≤ Real.log 2) (hl2hi : Real.log 2 ≤ l2hi) (hl2pos : 0 < l2lo)
    (hKhi : 9 / 5 * (U2 / b ^ 3) - Cval * L1 / a ^ 2 - 2 * l2lo / 5 * NL ≤ K)
    (hKlo : -K ≤ 9 / 5 * (L2 / a ^ 3) - Cval * U1 / b ^ 2 - 2 * l2hi / 5 * NU)
    {x : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) : |Dder x| ≤ K := by
  have hx0 : 0 < x := ha.trans_le hx1
  have hxb : x < 1 := hx2.trans_lt hb
  have hb0 : 0 < b := ha.trans_le hab
  have hCval : (0 : ℝ) < Cval := by simp only [Cval]; norm_num
  have hlog2 : (0 : ℝ) < Real.log 2 := lt_of_lt_of_le hl2pos hl2lo
  have hx3 : (0 : ℝ) < x ^ 3 := by positivity
  have hx2p : (0 : ℝ) < x ^ 2 := by positivity
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hax3 : a ^ 3 ≤ x ^ 3 := by gcongr
  have hxb3 : x ^ 3 ≤ b ^ 3 := by gcongr
  have hax2 : a ^ 2 ≤ x ^ 2 := by gcongr
  have hxb2 : x ^ 2 ≤ b ^ 2 := by gcongr
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have h1x2 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have h1b2 : (0 : ℝ) < 1 - b ^ 2 := by nlinarith
  have hA1 : Real.log (1 - x) ≤ U1 :=
    le_trans (Real.log_le_log h1x (by linarith)) hU1
  have hA2 : L1 ≤ Real.log (1 - x) :=
    le_trans hL1 (Real.log_le_log h1b (by linarith))
  have hB1 : Real.log (1 - x ^ 2) ≤ U2 :=
    le_trans (Real.log_le_log h1x2 (by nlinarith)) hU2
  have hB2 : L2 ≤ Real.log (1 - x ^ 2) :=
    le_trans hL2 (Real.log_le_log h1b2 (by nlinarith))
  have hNx1 : NL ≤ Npoly x := hNL x hx1 hx2
  have hNx2 : Npoly x ≤ NU := hNU x hx1 hx2
  have hNx0 : (0 : ℝ) ≤ Npoly x := hNL0.trans hNx1
  have hL1n : L1 ≤ 0 := hA2.trans (Real.log_nonpos (by linarith) (by linarith))
  have hL2n : L2 ≤ 0 := hB2.trans (Real.log_nonpos (by nlinarith) (by nlinarith))
  -- the three pieces
  have s1u : Real.log (1 - x ^ 2) / x ^ 3 ≤ U2 / b ^ 3 :=
    le_trans (div_le_div_right' hB1 hx3) (div_le_div_of_nonpos_left hU2n hx3 hxb3)
  have s1l : L2 / a ^ 3 ≤ Real.log (1 - x ^ 2) / x ^ 3 :=
    le_trans (div_le_div_of_nonpos_left hL2n ha3 hax3) (div_le_div_right' hB2 hx3)
  have s2u : Cval * Real.log (1 - x) / x ^ 2 ≤ Cval * U1 / b ^ 2 := by
    have h1 : Cval * Real.log (1 - x) ≤ Cval * U1 := mul_le_mul_of_nonneg_left hA1 hCval.le
    have h2 : Cval * U1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hCval.le hU1n
    exact le_trans (div_le_div_right' h1 hx2p) (div_le_div_of_nonpos_left h2 hx2p hxb2)
  have s2l : Cval * L1 / a ^ 2 ≤ Cval * Real.log (1 - x) / x ^ 2 := by
    have h1 : Cval * L1 ≤ Cval * Real.log (1 - x) := mul_le_mul_of_nonneg_left hA2 hCval.le
    have h2 : Cval * L1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hCval.le hL1n
    exact le_trans (div_le_div_of_nonpos_left h2 ha2 hax2) (div_le_div_right' h1 hx2p)
  have s3l : 2 * l2lo / 5 * NL ≤ 2 * Real.log 2 / 5 * Npoly x := by
    have hco : 2 * l2lo / 5 ≤ 2 * Real.log 2 / 5 := by linarith
    exact mul_le_mul hco hNx1 hNL0 (by linarith)
  have s3u : 2 * Real.log 2 / 5 * Npoly x ≤ 2 * l2hi / 5 * NU := by
    have hco : 2 * Real.log 2 / 5 ≤ 2 * l2hi / 5 := by linarith
    exact mul_le_mul hco hNx2 hNx0 (by linarith)
  have e : Dder x = 9 / 5 * (Real.log (1 - x ^ 2) / x ^ 3)
      - Cval * Real.log (1 - x) / x ^ 2 - 2 * Real.log 2 / 5 * Npoly x := by
    simp only [Dder]; ring
  rw [abs_le]
  constructor
  · rw [e]; linarith
  · rw [e]; linarith

/-! ### 6. The mean-value box bound -/

/-- **The derivative-corrected per-box lower bound.**  On `[a,b] ⊆ (0,1)`, if `bnd ≤ Dfun m` for
some `m ∈ [a,b]` and `|Dder| ≤ K` on the box, then `Dfun ≥ bnd - K * hh` on the box, where
`hh` dominates the distance from `m` to either endpoint. -/
theorem Dfun_box_mvt {a b m K hh bnd : ℝ} (ha : 0 < a) (hb : b < 1)
    (ham : a ≤ m) (hmb : m ≤ b) (hd1 : m - a ≤ hh) (hd2 : b - m ≤ hh) (hK0 : 0 ≤ K)
    (hK : ∀ x : ℝ, a ≤ x → x ≤ b → |Dder x| ≤ K)
    (hm : bnd ≤ Dfun m)
    {s : ℝ} (hs1 : a ≤ s) (hs2 : s ≤ b) :
    bnd - K * hh ≤ Dfun s := by
  have hderiv : ∀ x ∈ Set.Icc a b, HasDerivWithinAt Dfun (Dder x) (Set.Icc a b) x := by
    intro x hx
    exact (hasDerivAt_Dfun (ha.trans_le hx.1) (hx.2.trans_lt hb)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc a b, ‖Dder x‖ ≤ K := by
    intro x hx
    simpa [Real.norm_eq_abs] using hK x hx.1 hx.2
  have hmvt : ‖Dfun s - Dfun m‖ ≤ K * ‖s - m‖ :=
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      ⟨ham, hmb⟩ ⟨hs1, hs2⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have habs : |s - m| ≤ hh := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hstep : K * |s - m| ≤ K * hh := mul_le_mul_of_nonneg_left habs hK0
  have hfin : |Dfun s - Dfun m| ≤ K * hh := le_trans hmvt hstep
  have h2 := (abs_le.mp hfin).1
  linarith

/-! ### 7. Power-of-two scaled access to the certified rational log enclosures

For an argument `w` close to `0` (which is exactly what `Real.log (1 - s)` and
`Real.log (1 - s^2)` produce near `s = 1`), both the direct and the reciprocal route into
`EntropyBound.Constants.logLo_le` / `.le_logHi` have `artanh` parameter `|y| ≈ 1`, where the
series is useless.  Scaling `w` by a power of two into `[1,2]` keeps `|y| ≤ 1/3`. -/

theorem log_le_scaled {w c q : ℚ} {k J : ℕ} {l2lo r X : ℝ}
    (hw : (0 : ℚ) < w) (hX : X = (w : ℝ)) (hc : (2 : ℝ) ^ k * (w : ℝ) ≤ (c : ℝ))
    (hc0 : (0 : ℚ) < c) (hl2 : l2lo ≤ Real.log 2)
    (hq : Constants.logHi c J ≤ q) (hr : (q : ℝ) - k * l2lo ≤ r) :
    Real.log X ≤ r := by
  have hwr : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hpos : (0 : ℝ) < 2 ^ k * (w : ℝ) := by positivity
  have hmono : Real.log (2 ^ k * (w : ℝ)) ≤ Real.log (c : ℝ) := Real.log_le_log hpos hc
  have hsplit : Real.log ((2 : ℝ) ^ k * (w : ℝ)) = k * Real.log 2 + Real.log (w : ℝ) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hwr), Real.log_pow]
  have hhi : Real.log (c : ℝ) ≤ ((q : ℚ) : ℝ) := by
    refine le_trans (Constants.le_logHi c J hc0) ?_
    exact_mod_cast hq
  have hk : (k : ℝ) * l2lo ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k)
  rw [hX]
  linarith

theorem scaled_le_log {w c q : ℚ} {k J : ℕ} {l2hi r X : ℝ}
    (hw : (0 : ℚ) < w) (hX : X = (w : ℝ)) (hc : (c : ℝ) ≤ (2 : ℝ) ^ k * (w : ℝ))
    (hc0 : (0 : ℚ) < c) (hl2 : Real.log 2 ≤ l2hi)
    (hq : q ≤ Constants.logLo c J) (hr : r ≤ (q : ℝ) - k * l2hi) :
    r ≤ Real.log X := by
  have hwr : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hcr : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
  have hmono : Real.log (c : ℝ) ≤ Real.log ((2 : ℝ) ^ k * (w : ℝ)) := Real.log_le_log hcr hc
  have hsplit : Real.log ((2 : ℝ) ^ k * (w : ℝ)) = k * Real.log 2 + Real.log (w : ℝ) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hwr), Real.log_pow]
  have hlo : ((q : ℚ) : ℝ) ≤ Real.log (c : ℝ) := by
    refine le_trans ?_ (Constants.logLo_le c J hc0)
    exact_mod_cast hq
  have hk : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * l2hi :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k)
  rw [hX]
  linarith

/-! ### 8. The frozen numeric enclosure of `Real.log 2` used by every box -/

/-- Certified rational lower bound for `Real.log 2`, `J = 16` in the shared enclosure API. -/
def log2Lo : ℝ := 693147180559945 / 1000000000000000

/-- Certified rational upper bound for `Real.log 2`, `J = 16`. -/
def log2Hi : ℝ := 693147180559946 / 1000000000000000

theorem log2Lo_le : log2Lo ≤ Real.log 2 := by
  have h := Constants.logLo_le 2 16 (by norm_num)
  have hq : (693147180559945 / 1000000000000000 : ℚ) ≤ Constants.logLo 2 16 := by
    rw [Constants.logLo, Constants.logMid, Constants.logTail_of_one_le _ _ (by norm_num)]
    norm_num [Constants.yOf, Finset.sum_range_succ]
  have hc : ((693147180559945 / 1000000000000000 : ℚ) : ℝ)
      ≤ ((Constants.logLo 2 16 : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at hc
  norm_num at h
  simp only [log2Lo]
  linarith

theorem le_log2Hi : Real.log 2 ≤ log2Hi := by
  have h := Constants.le_logHi 2 16 (by norm_num)
  have hq : Constants.logHi 2 16 ≤ (693147180559946 / 1000000000000000 : ℚ) := by
    rw [Constants.logHi, Constants.logMid, Constants.logTail_of_one_le _ _ (by norm_num)]
    norm_num [Constants.yOf, Finset.sum_range_succ]
  have hc : ((Constants.logHi 2 16 : ℚ) : ℝ)
      ≤ ((693147180559946 / 1000000000000000 : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at hc
  norm_num at h
  simp only [log2Hi]
  linarith

theorem log2Lo_pos : (0 : ℝ) < log2Lo := by simp only [log2Lo]; norm_num

/-- Numeric interface: certified rational **upper** bound for `Real.log X`. -/
theorem logU {w c q : ℚ} {k J : ℕ} {X R : ℝ}
    (hw : (0 : ℚ) < w) (hc0 : (0 : ℚ) < c) (hX : X = (w : ℝ))
    (hc : (2 : ℝ) ^ k * (w : ℝ) ≤ (c : ℝ))
    (hq : Constants.logHi c J ≤ q) (hR : (q : ℝ) - k * log2Lo ≤ R) : Real.log X ≤ R :=
  log_le_scaled hw hX hc hc0 log2Lo_le hq hR

/-- Numeric interface: certified rational **lower** bound for `Real.log X`. -/
theorem logL {w c q : ℚ} {k J : ℕ} {X R : ℝ}
    (hw : (0 : ℚ) < w) (hc0 : (0 : ℚ) < c) (hX : X = (w : ℝ))
    (hc : (c : ℝ) ≤ (2 : ℝ) ^ k * (w : ℝ))
    (hq : q ≤ Constants.logLo c J) (hR : R ≤ (q : ℝ) - k * log2Hi) : R ≤ Real.log X :=
  scaled_le_log hw hX hc hc0 le_log2Hi hq hR

/-! ### 9. Certified bounds for `Npoly` on a box

`Npoly` is expanded around the left endpoint `a`; the coefficients are the (exactly
`ring`-checked) Taylor coefficients, so the radius `r₁w + r₂w² + r₃w³ + r₄w⁴ + c₅w⁵`
is essentially `|N'(a)| w`, not the far cruder termwise bound of the power basis. -/

def NpolyD1 (a : ℝ) : ℝ :=
  24661 / 5000 - 87966 / 2500 * a + 83349 / 1250 * a ^ 2 - 26244 / 500 * a ^ 3
    + 98415 / 5000 * a ^ 4

def NpolyD2 (a : ℝ) : ℝ :=
  -(43983 / 2500) + 83349 / 1250 * a - 39366 / 500 * a ^ 2 + 196830 / 5000 * a ^ 3

def NpolyD3 (a : ℝ) : ℝ := 27783 / 1250 - 26244 / 500 * a + 196830 / 5000 * a ^ 2

def NpolyD4 (a : ℝ) : ℝ := -(6561 / 500) + 98415 / 5000 * a

theorem term_abs_bound {c u w r : ℝ} (hc : |c| ≤ r) (hu0 : 0 ≤ u) (huw : u ≤ w) :
    -(r * w) ≤ c * u ∧ c * u ≤ r * w := by
  have hr : 0 ≤ r := le_trans (abs_nonneg c) hc
  have h1 : |c * u| ≤ r * w := by
    rw [abs_mul, abs_of_nonneg hu0]
    exact mul_le_mul hc huw hu0 hr
  exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩

theorem Npoly_box_bounds {a w r1 r2 r3 r4 R NL NU x : ℝ} (_hw : 0 ≤ w)
    (hx1 : a ≤ x) (hx2 : x ≤ a + w)
    (h1 : |NpolyD1 a| ≤ r1) (h2 : |NpolyD2 a| ≤ r2) (h3 : |NpolyD3 a| ≤ r3)
    (h4 : |NpolyD4 a| ≤ r4)
    (hR : r1 * w + r2 * w ^ 2 + r3 * w ^ 3 + r4 * w ^ 4 + 19683 / 5000 * w ^ 5 ≤ R)
    (hNL : NL ≤ Npoly a - R) (hNU : Npoly a + R ≤ NU) :
    NL ≤ Npoly x ∧ Npoly x ≤ NU := by
  have hu0 : (0 : ℝ) ≤ x - a := by linarith
  have huw : x - a ≤ w := by linarith
  have p2 : (x - a) ^ 2 ≤ w ^ 2 := by gcongr
  have p3 : (x - a) ^ 3 ≤ w ^ 3 := by gcongr
  have p4 : (x - a) ^ 4 ≤ w ^ 4 := by gcongr
  have p5 : (x - a) ^ 5 ≤ w ^ 5 := by gcongr
  have q2 : (0 : ℝ) ≤ (x - a) ^ 2 := pow_nonneg hu0 2
  have q3 : (0 : ℝ) ≤ (x - a) ^ 3 := pow_nonneg hu0 3
  have q4 : (0 : ℝ) ≤ (x - a) ^ 4 := pow_nonneg hu0 4
  have q5 : (0 : ℝ) ≤ (x - a) ^ 5 := pow_nonneg hu0 5
  have b1 := term_abs_bound h1 hu0 huw
  have b2 := term_abs_bound h2 q2 p2
  have b3 := term_abs_bound h3 q3 p3
  have b4 := term_abs_bound h4 q4 p4
  have b5 : 19683 / 5000 * (x - a) ^ 5 ≤ 19683 / 5000 * w ^ 5 := by linarith
  have b5' : (0 : ℝ) ≤ 19683 / 5000 * (x - a) ^ 5 := by linarith
  have hd : Npoly x = Npoly a + NpolyD1 a * (x - a) + NpolyD2 a * (x - a) ^ 2
      + NpolyD3 a * (x - a) ^ 3 + NpolyD4 a * (x - a) ^ 4 + 19683 / 5000 * (x - a) ^ 5 := by
    simp only [Npoly, NpolyD1, NpolyD2, NpolyD3, NpolyD4]
    ring
  rw [hd]
  constructor
  · linarith [b1.1, b2.1, b3.1, b4.1]
  · linarith [b1.2, b2.2, b3.2, b4.2]

/-! ### 10. The complete per-box positivity certificate -/

/-- **One box.**  All hypotheses are rational numeric facts except the eight certified
`Real.log` enclosures, which come from `logU` / `logL`. -/
theorem Dfun_box_pos {a b m hh K bnd Lu Ll Ml Nu U1 L1 U2 L2 NL NU : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (ham : a ≤ m) (hmb : m ≤ b)
    (hd1 : m - a ≤ hh) (hd2 : b - m ≤ hh) (hK0 : 0 ≤ K)
    (hLu : Real.log m ≤ Lu) (hLl : Ll ≤ Real.log m) (hMl : Ml ≤ Real.log (1 - m))
    (hNu : Real.log (1 - m ^ 2) ≤ Nu)
    (hU1 : Real.log (1 - a) ≤ U1) (hL1 : L1 ≤ Real.log (1 - b))
    (hU2 : Real.log (1 - a ^ 2) ≤ U2) (hL2 : L2 ≤ Real.log (1 - b ^ 2))
    (hU1n : U1 ≤ 0) (hU2n : U2 ≤ 0)
    (hNL : ∀ x : ℝ, a ≤ x → x ≤ b → NL ≤ Npoly x)
    (hNU : ∀ x : ℝ, a ≤ x → x ≤ b → Npoly x ≤ NU)
    (hNL0 : 0 ≤ NL)
    (hbnd : bnd ≤ 9 / 10 * (-2 * Lu - (1 - m ^ 2) / m ^ 2 * Nu)
      - Cval * (-Ll - (1 - m) / m * Ml) + log2Lo / 10 * (4 * (1 - m) * Ppoly m))
    (hKhi : 9 / 5 * (U2 / b ^ 3) - Cval * L1 / a ^ 2 - 2 * log2Lo / 5 * NL ≤ K)
    (hKlo : -K ≤ 9 / 5 * (L2 / a ^ 3) - Cval * U1 / b ^ 2 - 2 * log2Hi / 5 * NU)
    (hpos : 0 < bnd - K * hh)
    {s : ℝ} (hs1 : a ≤ s) (hs2 : s ≤ b) : 0 < Dfun s := by
  have hm0 : 0 < m := ha.trans_le ham
  have hm1 : m < 1 := hmb.trans_lt hb
  have hlow : bnd ≤ Dfun m := Dfun_lower_at hm0 hm1 hLu hLl hMl hNu log2Lo_le hbnd
  have hKb : ∀ x : ℝ, a ≤ x → x ≤ b → |Dder x| ≤ K := fun x hx1 hx2 =>
    abs_Dder_le ha hab hb hU1 hL1 hU2 hL2 hU1n hU2n hNL hNU hNL0 log2Lo_le le_log2Hi
      log2Lo_pos hKhi hKlo hx1 hx2
  have := Dfun_box_mvt ha hb ham hmb hd1 hd2 hK0 hKb hlow hs1 hs2
  linarith

end EntropyBound.Diagonal

end
