/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Entropy
import EntropyBound.Proofs.Toolbox.Series
import EntropyBound.Proofs.Toolbox.Parabola
import EntropyBound.Proofs.Toolbox.Qseries

/-!
# Stage B items B7 and B8 — the derivative of `Q` and the profile `A` (`SKETCH.md` (2f)–(2h))

This file contains the four remaining Stage B leaves:

* #13 `Qser_hasDerivAt`  (`HasDerivAt Qser (Qder z) z` for `0 ≤ z < 1`),
* #14 `Qder_upper_bounds` (`0 ≤ Q'`, `Q' ≤ z/(1-z²)`, `Q' ≤ -log(1-z²)/z`),
* #15 `Aser_closed_form`  (`Aser u = u √(Qser (1 - u²))` on `[0,1]`),
* #16 `Aser_hasDerivAt`   (`SKETCH.md` (2h)).

**#13** is honest termwise differentiation: for the given `z` we instantiate
`r := (z+1)/2 ∈ [1/2, 1)` and apply `hasDerivAt_tsum_of_isPreconnected` on the open convex
set `Set.Ioo (-r) r`, where the termwise derivative series is dominated by the geometric
series `∑ 2 (r²)ʲ`.  The frozen hypothesis `0 ≤ z < 1` is discharged for *every* such `z` —
the statement is never restricted to a subinterval.

**#14** uses the coefficient bounds `2j/((j+1)(2j+1)) ≤ 1` and `≤ 1/j`, both a consequence of
`(j+1)(2j+1) = 2j² + 3j + 1 ≥ 2j²`, compared against `∑_{j≥1} z^(2j-1) = z/(1-z²)` and
`∑_{j≥1} z^(2j-1)/j = -log(1-z²)/z`.

**#15** rests on the support identity `∑_{k≥1} (1-zᵏ)²/(k(k+1)) = (1-z) Q(z)` on `[0,1]`, whose
left-hand side is `1 - 2 f(z) + f(z²)` (`Toolbox.hasSum_fser` + `Toolbox.hasSum_inv_mul_succ`
transported by `Toolbox.hasSum_congr_fun`); substituting `z = 1 - u²` and using
`Real.sqrt_mul` / `Real.sqrt_sq` finishes.

**#16** is the chain rule on `u ↦ u √(Qser (1-u²))` using #13 and `Qser ≥ 1 > 0`, glued to the
frozen `Aser` by `HasDerivAt.congr_of_eventuallyEq` against #15 on `Set.Ioo 0 1`.

No `tsum` is ever replaced by a partial sum (BLUEPRINT Cheat-watch, Stage B).
-/

open Filter Finset
open scoped Topology

namespace EntropyBound.Toolbox

noncomputable section

/-! ### B7 — termwise differentiation of `Qser` -/

/-- The summand of `Qser`, as a function of the index and the point. -/
def qterm (j : ℕ) (y : ℝ) : ℝ := y ^ (2 * j) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))

/-- The termwise derivative of `qterm j`. -/
def qterm' (j : ℕ) (y : ℝ) : ℝ :=
  ((2 * j : ℕ) : ℝ) * y ^ (2 * j - 1) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))

theorem Qser_eq_tsum_qterm (y : ℝ) : Qser y = ∑' j : ℕ, qterm j y := by
  simp only [Qser, qterm]

theorem hasDerivAt_qterm (j : ℕ) (y : ℝ) : HasDerivAt (qterm j) (qterm' j y) y := by
  have h : HasDerivAt (fun w : ℝ => w ^ (2 * j) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)))
      (((2 * j : ℕ) : ℝ) * y ^ (2 * j - 1) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) y :=
    (hasDerivAt_pow (2 * j) y).div_const _
  exact h

/-- The geometric majorant of the termwise derivative series on `[-r, r]`. -/
theorem norm_qterm'_le {r y : ℝ} (hr : 1 / 2 ≤ r) (hy : |y| ≤ r) (j : ℕ) :
    ‖qterm' j y‖ ≤ 2 * (r ^ 2) ^ j := by
  have hr0 : (0 : ℝ) < r := by linarith
  match j with
  | 0 => simp [qterm']
  | (k + 1) =>
      have hex : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hD : (0 : ℝ) < ((k : ℝ) + 2) * (2 * (k : ℝ) + 3) := by positivity
      have hrw : qterm' (k + 1) y
          = (2 * (k : ℝ) + 2) * y ^ (2 * k + 1) / (((k : ℝ) + 2) * (2 * (k : ℝ) + 3)) := by
        simp only [qterm', hex]
        push_cast
        ring
      have habs0 : (0 : ℝ) ≤ |y| ^ (2 * k + 1) := by positivity
      have hstep1 : (2 * (k : ℝ) + 2) * |y| ^ (2 * k + 1) / (((k : ℝ) + 2) * (2 * (k : ℝ) + 3))
          ≤ |y| ^ (2 * k + 1) := by
        rw [div_le_iff₀ hD]
        have hc : 2 * (k : ℝ) + 2 ≤ ((k : ℝ) + 2) * (2 * (k : ℝ) + 3) := by nlinarith
        calc (2 * (k : ℝ) + 2) * |y| ^ (2 * k + 1)
            ≤ (((k : ℝ) + 2) * (2 * (k : ℝ) + 3)) * |y| ^ (2 * k + 1) :=
              mul_le_mul_of_nonneg_right hc habs0
          _ = |y| ^ (2 * k + 1) * (((k : ℝ) + 2) * (2 * (k : ℝ) + 3)) := by ring
      have hstep2 : |y| ^ (2 * k + 1) ≤ r ^ (2 * k + 1) :=
        pow_le_pow_left₀ (abs_nonneg y) hy _
      have hpow0 : (0 : ℝ) ≤ r ^ (2 * k + 1) := by positivity
      have hstep3 : r ^ (2 * k + 1) ≤ 2 * (r ^ 2) ^ (k + 1) := by
        have e1 : (2 : ℝ) * (r ^ 2) ^ (k + 1) = (2 * r) * r ^ (2 * k + 1) := by ring
        rw [e1]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r - 1) hpow0]
      rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos hD, abs_mul,
        abs_of_pos (show (0 : ℝ) < 2 * (k : ℝ) + 2 by positivity), abs_pow]
      linarith

theorem summable_qterm' {r y : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hy : |y| ≤ r) :
    Summable (fun j : ℕ => qterm' j y) := by
  have hr0 : (0 : ℝ) < r := by linarith
  refine Summable.of_norm_bounded ?_ (fun j => norm_qterm'_le hr hy j)
  exact (summable_geometric_of_lt_one (r := r ^ 2) (by positivity) (by nlinarith)).mul_left 2

/-- `∑' j, qterm' j z` is exactly `Qder z`: the `j = 0` term vanishes, and the shift
`j = m + 1` turns the summand into the frozen one. -/
theorem tsum_qterm'_eq_Qder {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    ∑' j : ℕ, qterm' j z = Qder z := by
  have hr : (1 : ℝ) / 2 ≤ (z + 1) / 2 := by linarith
  have hr1 : (z + 1) / 2 < 1 := by linarith
  have hy : |z| ≤ (z + 1) / 2 := by
    rw [abs_of_nonneg hz0]; linarith
  have hsum := summable_qterm' hr hr1 hy
  rw [hsum.tsum_eq_zero_add]
  have h0 : qterm' 0 z = 0 := by simp [qterm']
  rw [h0, zero_add]
  simp only [Qder]
  refine tsum_congr fun m => ?_
  have hex : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  simp only [qterm', hex]
  push_cast
  ring

/-- **B7 / #13.**  `Qser` is differentiable at every `z ∈ [0,1)` with derivative `Qder z`. -/
theorem hasDerivAt_Qser {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : HasDerivAt Qser (Qder z) z := by
  set r : ℝ := (z + 1) / 2 with hrdef
  have hr : (1 : ℝ) / 2 ≤ r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hu : Summable (fun j : ℕ => 2 * (r ^ 2) ^ j) :=
    (summable_geometric_of_lt_one (r := r ^ 2) (by positivity) (by nlinarith)).mul_left 2
  have hzmem : z ∈ Set.Ioo (-r) r := ⟨by linarith, by rw [hrdef]; linarith⟩
  have hg0 : Summable (fun j : ℕ => qterm j z) := by
    simpa only [qterm] using summable_Qser_term hz0 hz1.le
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected
    (fun j y _ => hasDerivAt_qterm j y)
    (fun j y hy => norm_qterm'_le hr (le_of_lt (abs_lt.mpr ⟨hy.1, hy.2⟩)) j)
    hzmem hg0 hzmem
  rw [tsum_qterm'_eq_Qder hz0 hz1] at key
  have heq : (fun w : ℝ => ∑' j : ℕ, qterm j w) = Qser := by
    funext w
    exact (Qser_eq_tsum_qterm w).symm
  rwa [heq] at key

/-! ### B7 — the three upper bounds on `Qder` -/

/-- The coefficient bound `2(m+1)/((m+2)(2m+3)) ≤ 1`, i.e. `(j+1)(2j+1) ≥ 2j` at `j = m+1`. -/
theorem Qder_coeff_le_one (m : ℕ) :
    2 * ((m : ℝ) + 1) ≤ ((m : ℝ) + 2) * (2 * (m : ℝ) + 3) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- The coefficient bound `2(m+1)/((m+2)(2m+3)) ≤ 1/(m+1)`, i.e. `(j+1)(2j+1) ≥ 2j²` at
`j = m+1`. -/
theorem Qder_coeff_le_inv (m : ℕ) :
    2 * ((m : ℝ) + 1) * ((m : ℝ) + 1) ≤ ((m : ℝ) + 2) * (2 * (m : ℝ) + 3) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- The termwise bound `2(m+1) z^(2m+1)/((m+2)(2m+3)) ≤ z^(2m+1)` for `0 ≤ z`. -/
theorem Qder_term_le_geom {z : ℝ} (hz0 : 0 ≤ z) (m : ℕ) :
    2 * ((m : ℝ) + 1) * z ^ (2 * m + 1) / (((m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      ≤ z ^ (2 * m + 1) := by
  have hD : (0 : ℝ) < ((m : ℝ) + 2) * (2 * (m : ℝ) + 3) := by positivity
  have hp : (0 : ℝ) ≤ z ^ (2 * m + 1) := pow_nonneg hz0 _
  rw [div_le_iff₀ hD]
  calc 2 * ((m : ℝ) + 1) * z ^ (2 * m + 1)
      = (2 * ((m : ℝ) + 1)) * z ^ (2 * m + 1) := by ring
    _ ≤ (((m : ℝ) + 2) * (2 * (m : ℝ) + 3)) * z ^ (2 * m + 1) :=
        mul_le_mul_of_nonneg_right (Qder_coeff_le_one m) hp
    _ = z ^ (2 * m + 1) * (((m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := by ring

/-- The geometric series `∑ z^(2m+1)` is summable on `[0,1)`. -/
theorem summable_odd_geometric {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun m : ℕ => z ^ (2 * m + 1)) := by
  refine (Summable.mul_left z (summable_geometric_of_lt_one (r := z ^ 2) (by positivity)
    (by nlinarith))).congr fun m => ?_
  rw [← pow_mul]
  ring

/-- The `Qder` summand is dominated by the geometric series `∑ z^(2m+1)` on `[0,1)`. -/
theorem summable_Qder_term {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun m : ℕ =>
      2 * ((m : ℝ) + 1) * z ^ (2 * m + 1) / (((m : ℝ) + 2) * (2 * (m : ℝ) + 3))) :=
  Summable.of_nonneg_of_le (fun m => by positivity) (fun m => Qder_term_le_geom hz0 m)
    (summable_odd_geometric hz0 hz1)

/-- `∑'_{m} z^(2m+1) = z / (1 - z²)` for `0 ≤ z < 1`. -/
theorem hasSum_odd_geometric {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun m : ℕ => z ^ (2 * m + 1)) (z / (1 - z ^ 2)) := by
  have hz2 : z ^ 2 < 1 := by nlinarith
  have h := (hasSum_geometric_of_lt_one (r := z ^ 2) (by positivity) hz2).mul_left z
  rw [← div_eq_mul_inv] at h
  refine hasSum_congr_fun h fun m => ?_
  rw [← pow_mul]
  ring

/-- `∑'_{m} z^(2m+1)/(m+1) = -log (1 - z²) / z` for `0 < z < 1`. -/
theorem hasSum_odd_over_index {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasSum (fun m : ℕ => z ^ (2 * m + 1) / ((m : ℝ) + 1)) (-Real.log (1 - z ^ 2) / z) := by
  have hz2 : |z ^ 2| < 1 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
    nlinarith
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hz2).div_const z
  refine hasSum_congr_fun h fun m => ?_
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hzne : z ≠ 0 := ne_of_gt hz0
  rw [← pow_mul]
  field_simp
  ring

end

end EntropyBound.Toolbox

namespace EntropyBound

/-- Frozen theorem #13 (`SKETCH.md` (2f), BLUEPRINT B7). -/
theorem Qser_hasDerivAt_proof : ∀ z : ℝ, 0 ≤ z → z < 1 → HasDerivAt Qser (Qder z) z :=
  fun _ hz0 hz1 => Toolbox.hasDerivAt_Qser hz0 hz1

/-- Frozen theorem #14 (`SKETCH.md` (2f), BLUEPRINT B7). -/
theorem Qder_upper_bounds_proof :
    ∀ z : ℝ, 0 ≤ z → z < 1 →
      0 ≤ Qder z ∧ Qder z ≤ z / (1 - z ^ 2) ∧
        (0 < z → Qder z ≤ -Real.log (1 - z ^ 2) / z) := by
  intro z hz0 hz1
  have hsum := Toolbox.summable_Qder_term hz0 hz1
  refine ⟨?_, ?_, ?_⟩
  · exact tsum_nonneg fun m => by positivity
  · -- compare against `∑ z^(2m+1) = z/(1-z²)`, using `2(m+1)/((m+2)(2m+3)) ≤ 1`
    have hgeo := Toolbox.hasSum_odd_geometric hz0 hz1
    refine le_trans (Summable.tsum_le_tsum (fun m => Toolbox.Qder_term_le_geom hz0 m) hsum
      hgeo.summable) hgeo.tsum_eq.le
  · -- compare against `∑ z^(2m+1)/(m+1) = -log(1-z²)/z`, using `2(m+1)/((m+2)(2m+3)) ≤ 1/(m+1)`
    intro hzpos
    have hlog := Toolbox.hasSum_odd_over_index hzpos hz1
    refine le_trans (Summable.tsum_le_tsum (fun m => ?_) hsum hlog.summable) hlog.tsum_eq.le
    have hD : (0 : ℝ) < ((m : ℝ) + 2) * (2 * (m : ℝ) + 3) := by positivity
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) ≤ z ^ (2 * m + 1) := pow_nonneg hz0 _
    rw [div_le_div_iff₀ hD hm1]
    calc 2 * ((m : ℝ) + 1) * z ^ (2 * m + 1) * ((m : ℝ) + 1)
        = (2 * ((m : ℝ) + 1) * ((m : ℝ) + 1)) * z ^ (2 * m + 1) := by ring
      _ ≤ (((m : ℝ) + 2) * (2 * (m : ℝ) + 3)) * z ^ (2 * m + 1) :=
          mul_le_mul_of_nonneg_right (Toolbox.Qder_coeff_le_inv m) hp
      _ = z ^ (2 * m + 1) * (((m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := by ring

end EntropyBound

namespace EntropyBound.Toolbox

noncomputable section

/-! ### B8 — the support identity `∑ (1-zᵏ)²/(k(k+1)) = (1-z) Q(z)` -/

theorem fser_zero : fser 0 = 0 := by
  have hz : ∀ m : ℕ, (0 : ℝ) ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) = 0 := by
    intro m
    simp
  simp only [fser, hz, tsum_zero]

theorem Qser_zero : Qser 0 = 1 := by
  simp only [Qser]
  rw [tsum_eq_single 0]
  · norm_num
  · intro j hj
    have h2j : 2 * j ≠ 0 := by omega
    rw [zero_pow h2j]
    simp

/-- `1 - 2 f(z) + f(z²) = (1-z) Q(z)` on `[0,1]`. -/
theorem one_sub_two_fser_add_fser_sq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - 2 * fser z + fser (z ^ 2) = (1 - z) * Qser z := by
  rcases eq_or_lt_of_le hz0 with h0 | h0
  · -- `z = 0`
    rw [← h0]
    norm_num [fser_zero, Qser_zero]
  rcases eq_or_lt_of_le hz1 with h1 | h1
  · -- `z = 1`
    rw [h1]
    norm_num [fser_one]
  -- `0 < z < 1`
  have hz2pos : (0 : ℝ) < z ^ 2 := by positivity
  have hz2lt : z ^ 2 < 1 := by nlinarith
  have hone : (0 : ℝ) < 1 - z := by linarith
  have hz2' : (0 : ℝ) < 1 - z ^ 2 := by linarith
  have hlog : Real.log (1 - z ^ 2) = Real.log (1 - z) + Real.log (1 + z) := by
    rw [show (1 : ℝ) - z ^ 2 = (1 - z) * (1 + z) by ring,
      Real.log_mul (ne_of_gt hone) (by positivity)]
  rw [fser_eq h0 h1, fser_eq hz2pos hz2lt, Qser_closed_form_proof z h0 h1, hlog]
  have hzne : z ≠ 0 := ne_of_gt h0
  field_simp
  ring

/-- **B8 support identity.**  `∑_{k ≥ 1} (1 - zᵏ)²/(k(k+1)) = (1 - z) Q(z)` on `[0,1]`. -/
theorem tsum_one_sub_pow_sq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∑' m : ℕ, (1 - z ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) = (1 - z) * Qser z := by
  have hz2 : (0 : ℝ) ≤ z ^ 2 := by positivity
  have hz2' : z ^ 2 ≤ 1 := by nlinarith
  have hA : HasSum (fun m : ℕ => 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) 1 := hasSum_inv_mul_succ
  have hB : HasSum (fun m : ℕ => z ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2))) (fser z) := by
    simpa only [fser] using (summable_fser_term hz0 hz1).hasSum
  have hC : HasSum (fun m : ℕ => (z ^ 2) ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      (fser (z ^ 2)) := by
    simpa only [fser] using (summable_fser_term hz2 hz2').hasSum
  have hkey : HasSum (fun m : ℕ => (1 - z ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      (1 - 2 * fser z + fser (z ^ 2)) := by
    refine hasSum_congr_fun ((hA.sub (hB.mul_left 2)).add hC) fun m => ?_
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
    have hpow : (z ^ 2) ^ (m + 1) = z ^ (m + 1) * z ^ (m + 1) := by
      rw [← pow_mul]
      ring
    rw [hpow]
    field_simp
    ring
  rw [hkey.tsum_eq, one_sub_two_fser_add_fser_sq hz0 hz1]

/-- **B8 / #15.**  `Aser u = u √(Qser (1 - u²))` on `[0,1]`. -/
theorem Aser_eq {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Aser u = u * Real.sqrt (Qser (1 - u ^ 2)) := by
  have hz0 : (0 : ℝ) ≤ 1 - u ^ 2 := by nlinarith
  have hz1 : (1 : ℝ) - u ^ 2 ≤ 1 := by nlinarith
  have hval := tsum_one_sub_pow_sq hz0 hz1
  simp only [Aser]
  rw [hval, show (1 : ℝ) - (1 - u ^ 2) = u ^ 2 by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hu0]

theorem Aser_zero : Aser 0 = 0 := by
  have h : ∀ m : ℕ,
      (1 - (1 - (0 : ℝ) ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) = 0 := by
    intro m
    norm_num
  simp only [Aser, h, tsum_zero, Real.sqrt_zero]

theorem Aser_one : Aser 1 = 1 := by
  have h : ∀ m : ℕ,
      (1 - (1 - (1 : ℝ) ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))
        = 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    intro m
    norm_num
  simp only [Aser, h]
  rw [tsum_inv_mul_succ, Real.sqrt_one]

/-! ### B8 — the derivative of `A` -/

/-- The closed form of `Aser` is differentiable on `(0,1)`, with the frozen derivative. -/
theorem hasDerivAt_Aser_closed {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun w : ℝ => w * Real.sqrt (Qser (1 - w ^ 2)))
      ((Qser (1 - u ^ 2) - u ^ 2 * Qder (1 - u ^ 2)) / Real.sqrt (Qser (1 - u ^ 2))) u := by
  have hzmem : (1 : ℝ) - u ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith
  have hz0 : (0 : ℝ) ≤ 1 - u ^ 2 := hzmem.1
  have hz1 : (1 : ℝ) - u ^ 2 < 1 := by nlinarith
  have hQ1 : (1 : ℝ) ≤ Qser (1 - u ^ 2) := (Qser_lower_bounds_proof _ hzmem).1
  have hQpos : (0 : ℝ) < Qser (1 - u ^ 2) := by linarith
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Qser (1 - u ^ 2)) := Real.sqrt_pos.mpr hQpos
  -- the inner map `w ↦ 1 - w²`
  have hinner : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-(2 * u)) u := by
    have h := (hasDerivAt_pow 2 u).const_sub 1
    simpa using h
  -- compose with `Qser`
  have hcomp : HasDerivAt (fun w : ℝ => Qser (1 - w ^ 2)) (Qder (1 - u ^ 2) * -(2 * u)) u := by
    have h := (hasDerivAt_Qser hz0 hz1).comp u hinner
    simpa [Function.comp_def] using h
  -- take the square root
  have hsqrt : HasDerivAt (fun w : ℝ => Real.sqrt (Qser (1 - w ^ 2)))
      (Qder (1 - u ^ 2) * -(2 * u) / (2 * Real.sqrt (Qser (1 - u ^ 2)))) u :=
    hcomp.sqrt (ne_of_gt hQpos)
  -- multiply by `w`
  refine (hasDerivAt_id' (x := u)).mul hsqrt |>.congr_deriv ?_
  have hsq : Real.sqrt (Qser (1 - u ^ 2)) ^ 2 = Qser (1 - u ^ 2) := Real.sq_sqrt hQpos.le
  have hsne : Real.sqrt (Qser (1 - u ^ 2)) ≠ 0 := ne_of_gt hsqrtpos
  have hstep : 1 * Real.sqrt (Qser (1 - u ^ 2))
      + u * (Qder (1 - u ^ 2) * -(2 * u) / (2 * Real.sqrt (Qser (1 - u ^ 2))))
      = (Real.sqrt (Qser (1 - u ^ 2)) ^ 2 - u ^ 2 * Qder (1 - u ^ 2))
          / Real.sqrt (Qser (1 - u ^ 2)) := by
    field_simp
    ring
  rw [hstep, hsq]

end

end EntropyBound.Toolbox

namespace EntropyBound

/-- Frozen theorem #15 (`SKETCH.md` (2g), BLUEPRINT B8). -/
theorem Aser_closed_form_proof :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, Aser u = u * Real.sqrt (Qser (1 - u ^ 2)) :=
  fun _ hu => Toolbox.Aser_eq hu.1 hu.2

/-- Frozen theorem #16 (`SKETCH.md` (2h), BLUEPRINT B8). -/
theorem Aser_hasDerivAt_proof :
    ∀ u : ℝ, 0 < u → u < 1 →
      HasDerivAt Aser
        ((Qser (1 - u ^ 2) - u ^ 2 * Qder (1 - u ^ 2)) / Real.sqrt (Qser (1 - u ^ 2))) u := by
  intro u hu0 hu1
  refine (Toolbox.hasDerivAt_Aser_closed hu0 hu1).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hu0 hu1] with w hw
  exact Toolbox.Aser_eq hw.1.le hw.2.le

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #13, restated verbatim. -/
theorem Qser_hasDerivAt : ∀ z : ℝ, 0 ≤ z → z < 1 → HasDerivAt Qser (Qder z) z :=
  EntropyBound.Qser_hasDerivAt_proof

/-- Frozen theorem #14, restated verbatim. -/
theorem Qder_upper_bounds :
    ∀ z : ℝ, 0 ≤ z → z < 1 →
      0 ≤ Qder z ∧ Qder z ≤ z / (1 - z ^ 2) ∧
        (0 < z → Qder z ≤ -Real.log (1 - z ^ 2) / z) :=
  EntropyBound.Qder_upper_bounds_proof

/-- Frozen theorem #15, restated verbatim. -/
theorem Aser_closed_form :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, Aser u = u * Real.sqrt (Qser (1 - u ^ 2)) :=
  EntropyBound.Aser_closed_form_proof

/-- Frozen theorem #16, restated verbatim. -/
theorem Aser_hasDerivAt :
    ∀ u : ℝ, 0 < u → u < 1 →
      HasDerivAt Aser
        ((Qser (1 - u ^ 2) - u ^ 2 * Qder (1 - u ^ 2)) / Real.sqrt (Qser (1 - u ^ 2))) u :=
  EntropyBound.Aser_hasDerivAt_proof

end EntropyBound.Solution

/-! ### No-drift gates for frozen theorems #13, #14, #15, #16 -/

example : @EntropyBound.Qser_hasDerivAt = @EntropyBound.Solution.Qser_hasDerivAt := rfl

example : @EntropyBound.Qder_upper_bounds = @EntropyBound.Solution.Qder_upper_bounds := rfl

example : @EntropyBound.Aser_closed_form = @EntropyBound.Solution.Aser_closed_form := rfl

example : @EntropyBound.Aser_hasDerivAt = @EntropyBound.Solution.Aser_hasDerivAt := rfl

/-! ### Guardrails required by `TASKS.md` / the BLUEPRINT Stage B cheat-watch box -/

example : EntropyBound.Aser 0 = 0 := EntropyBound.Toolbox.Aser_zero

example : EntropyBound.Aser 1 = 1 := EntropyBound.Toolbox.Aser_one
