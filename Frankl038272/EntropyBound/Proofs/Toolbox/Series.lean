/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Entropy

/-!
# Stage B — the auxiliary series `f` and the series form of `enat`

This file contains the dominating telescoping series of the BLUEPRINT Stage B preamble
(`summable_inv_mul_succ`, with `tsum = 1`) and the frozen theorems

* #8 `fser_closed_form` (`SKETCH.md` (2c), BLUEPRINT B3),
* #9 `enat_series_form` (`SKETCH.md` (2d), BLUEPRINT B4),
* #10 `enat_sum_of_squares` (`SKETCH.md` (2e), BLUEPRINT B5).

Every `tsum` here is the honest infinite series of `Defs.lean`; no partial sum ever replaces
one (BLUEPRINT Cheat-watch, Stage B).
-/

open Filter Finset
open scoped Topology

namespace EntropyBound.Toolbox

/-- Transport a `HasSum` along a pointwise equality of the summands. -/
theorem hasSum_congr_fun {f g : ℕ → ℝ} {a : ℝ} (h : HasSum f a) (heq : ∀ m, f m = g m) :
    HasSum g a := by
  have hfg : f = g := funext heq
  rwa [hfg] at h

/-! ### The dominating telescoping series `∑ 1/((m+1)(m+2)) = 1` -/

/-- The partial sums of the telescoping series `∑ 1/((m+1)(m+2))`. -/
theorem sum_range_inv_mul_succ (n : ℕ) :
    ∑ m ∈ Finset.range n, 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- The telescoping series `∑_{m ≥ 0} 1/((m+1)(m+2))` sums to `1`. -/
theorem hasSum_inv_mul_succ : HasSum (fun m : ℕ => 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) 1 := by
  have hsum : Summable (fun m : ℕ => 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
    refine summable_of_sum_range_le (c := 1) (fun n => by positivity) fun n => ?_
    rw [sum_range_inv_mul_succ n]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  rw [hsum.hasSum_iff_tendsto_nat]
  simp only [sum_range_inv_mul_succ]
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.sub h

/-- **Support lemma (BLUEPRINT Stage B preamble).**  The dominating series is summable. -/
theorem summable_inv_mul_succ : Summable (fun m : ℕ => 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) :=
  hasSum_inv_mul_succ.summable

/-- The value of the dominating series. -/
theorem tsum_inv_mul_succ : ∑' m : ℕ, 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) = 1 :=
  hasSum_inv_mul_succ.tsum_eq

/-- Every `fser`-type series on `[0,1]` is dominated by `summable_inv_mul_succ`. -/
theorem summable_fser_term {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun m : ℕ => x ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) summable_inv_mul_succ
  have hp : x ^ (m + 1) ≤ 1 := pow_le_one₀ hx0 hx1
  gcongr

/-! ### `fser` in closed form -/

/-- The series defining `fser` at `z ∈ (0,1)`, with its closed-form value. -/
theorem hasSum_fser {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasSum (fun m : ℕ => z ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      (1 + (1 - z) / z * Real.log (1 - z)) := by
  have habs : |z| < 1 := by rw [abs_of_pos hz0]; exact hz1
  have h1 : HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - z)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h2 : HasSum (fun n : ℕ => z ^ (n + 2) / ((n : ℝ) + 2)) (-Real.log (1 - z) - z) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ (n + 1) / ((n : ℝ) + 1)) 1).2 h1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at h
    refine hasSum_congr_fun h fun m => ?_
    push_cast
    ring
  have h3 : HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℝ) + 2))
      ((-Real.log (1 - z) - z) / z) := by
    refine hasSum_congr_fun (h2.div_const z) fun m => ?_
    field_simp
    ring
  have hval : -Real.log (1 - z) - (-Real.log (1 - z) - z) / z
      = 1 + (1 - z) / z * Real.log (1 - z) := by
    field_simp
    ring
  rw [← hval]
  refine hasSum_congr_fun (h1.sub h3) fun m => ?_
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- `fser` in closed form on `(0,1)`. -/
theorem fser_eq {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    fser z = 1 + (1 - z) / z * Real.log (1 - z) := by
  simp only [fser]
  exact (hasSum_fser hz0 hz1).tsum_eq

/-- `fser 1 = 1`, by the telescoping series. -/
theorem fser_one : fser 1 = 1 := by
  simp only [fser, one_pow]
  exact tsum_inv_mul_succ

end EntropyBound.Toolbox

namespace EntropyBound

/-- Frozen theorem #8 (`SKETCH.md` (2c), BLUEPRINT B3). -/
theorem fser_closed_form_proof :
    (∀ z : ℝ, 0 < z → z < 1 → fser z = 1 + (1 - z) / z * Real.log (1 - z)) ∧ fser 1 = 1 :=
  ⟨fun _ hz0 hz1 => Toolbox.fser_eq hz0 hz1, Toolbox.fser_one⟩

/-- Frozen theorem #9 (`SKETCH.md` (2d), BLUEPRINT B4). -/
theorem enat_series_form_proof :
    ∀ z : ℝ, 0 < z → z ≤ 1 → enat z = -Real.log z + 1 - fser z := by
  intro z hz0 hz1
  rcases eq_or_lt_of_le hz1 with hz | hz
  · subst hz
    simp [enat, Hnat, Toolbox.fser_one]
  · rw [Toolbox.fser_eq hz0 hz]
    have hz' : z ≠ 0 := ne_of_gt hz0
    simp only [enat, Hnat]
    field_simp
    ring

/-- Frozen theorem #10 (`SKETCH.md` (2e), BLUEPRINT B5). -/
theorem enat_sum_of_squares_proof :
    ∀ s t : ℝ, 0 < s → s ≤ 1 → 0 < t → t ≤ 1 →
      2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2)
        = ∑' m : ℕ, (s ^ (m + 1) - t ^ (m + 1)) ^ 2 / ((m + 1) * (m + 2)) := by
  intro s t hs0 hs1 ht0 ht1
  have hst0 : 0 < s * t := mul_pos hs0 ht0
  have hst1 : s * t ≤ 1 := by nlinarith
  have hs20 : (0 : ℝ) < s ^ 2 := by positivity
  have hs21 : s ^ 2 ≤ 1 := by nlinarith
  have ht20 : (0 : ℝ) < t ^ 2 := by positivity
  have ht21 : t ^ 2 ≤ 1 := by nlinarith
  -- the series form of each `enat`
  rw [enat_series_form_proof _ hst0 hst1, enat_series_form_proof _ hs20 hs21,
    enat_series_form_proof _ ht20 ht21]
  -- the logarithms cancel
  have hlog : Real.log (s * t) = Real.log s + Real.log t :=
    Real.log_mul (ne_of_gt hs0) (ne_of_gt ht0)
  have hlogs : Real.log (s ^ 2) = 2 * Real.log s := by
    rw [Real.log_pow]; push_cast; ring
  have hlogt : Real.log (t ^ 2) = 2 * Real.log t := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog, hlogs, hlogt]
  -- the remaining `fser` combination is the sum of squares, termwise
  have key : fser (s ^ 2) + fser (t ^ 2) - 2 * fser (s * t)
      = ∑' m : ℕ, (s ^ (m + 1) - t ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    have H1 : HasSum (fun m : ℕ => (s ^ 2) ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        (fser (s ^ 2)) := by
      simpa only [fser] using (Toolbox.summable_fser_term hs20.le hs21).hasSum
    have H2 : HasSum (fun m : ℕ => (t ^ 2) ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        (fser (t ^ 2)) := by
      simpa only [fser] using (Toolbox.summable_fser_term ht20.le ht21).hasSum
    have H3 : HasSum (fun m : ℕ => (s * t) ^ (m + 1) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        (fser (s * t)) := by
      simpa only [fser] using (Toolbox.summable_fser_term hst0.le hst1).hasSum
    have H : HasSum (fun m : ℕ => (s ^ (m + 1) - t ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        (fser (s ^ 2) + fser (t ^ 2) - 2 * fser (s * t)) := by
      refine Toolbox.hasSum_congr_fun ((H1.add H2).sub (H3.mul_left 2)) fun m => ?_
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
    exact H.tsum_eq.symm
  linarith [key]

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #8, restated verbatim. -/
theorem fser_closed_form :
    (∀ z : ℝ, 0 < z → z < 1 → fser z = 1 + (1 - z) / z * Real.log (1 - z)) ∧ fser 1 = 1 :=
  EntropyBound.fser_closed_form_proof

/-- Frozen theorem #9, restated verbatim. -/
theorem enat_series_form :
    ∀ z : ℝ, 0 < z → z ≤ 1 → enat z = -Real.log z + 1 - fser z :=
  EntropyBound.enat_series_form_proof

/-- Frozen theorem #10, restated verbatim. -/
theorem enat_sum_of_squares :
    ∀ s t : ℝ, 0 < s → s ≤ 1 → 0 < t → t ≤ 1 →
      2 * enat (s * t) - enat (s ^ 2) - enat (t ^ 2)
        = ∑' m : ℕ, (s ^ (m + 1) - t ^ (m + 1)) ^ 2 / ((m + 1) * (m + 2)) :=
  EntropyBound.enat_sum_of_squares_proof

end EntropyBound.Solution

/-- No-drift gates for frozen theorems #8, #9, #10. -/
example : @EntropyBound.fser_closed_form = @EntropyBound.Solution.fser_closed_form := rfl

example : @EntropyBound.enat_series_form = @EntropyBound.Solution.enat_series_form := rfl

example : @EntropyBound.enat_sum_of_squares = @EntropyBound.Solution.enat_sum_of_squares := rfl

/-! ### Guardrails required by `TASKS.md` -/

example : EntropyBound.fser 1 = 1 := EntropyBound.Toolbox.fser_one
