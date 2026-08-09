/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs

/-!
# Certified rational enclosures for `Real.log`

This file provides the **reusable** enclosure API announced by `BLUEPRINT.md` Stage A (A4)
and consumed by Stages E (E3) and G (G4):

* `EntropyBound.Constants.logLo a J` and `EntropyBound.Constants.logHi a J` are *rational*
  numbers, computed from the `artanh` series
  `log a = 2 ∑_{j ≥ 0} y^(2j+1)/(2j+1)`, `y = (a-1)/(a+1)`,
  truncated after `J` terms, with an explicit geometric tail bound;
* `logLo_le` and `le_logHi` certify `logLo a J ≤ Real.log a ≤ logHi a J` for every positive
  rational `a` and every truncation depth `J`.

The bounds are on `Real.log` itself — there is no rational surrogate for the logarithm
anywhere in this development (see the Stage A cheat-watch box of `BLUEPRINT.md`).

The analytic core is `abs_log_sub_sum_le`, an entirely real statement: for `|y| < 1` the
`artanh` series for `log (1+y) - log (1-y)` differs from its `J`-th partial sum by at most
`2/(2J+1) · |y|^(2J+1) · (1 - y²)⁻¹`.  Everything else is casting.
-/

namespace EntropyBound.Constants

open Finset

/-! ### The analytic core -/

/-- **Explicit remainder for the `artanh` series.**  For `|y| < 1` the partial sum of
`log (1+y) - log (1-y) = 2 ∑_{j ≥ 0} y^(2j+1)/(2j+1)` up to `j < J` differs from the true
value by at most `2/(2J+1) · |y|^(2J+1) · (1 - y²)⁻¹`, the geometric bound obtained by
replacing every denominator `2j+1` (`j ≥ J`) by `2J+1`. -/
theorem abs_log_sub_sum_le {y : ℝ} (hy : |y| < 1) (J : ℕ) :
    |Real.log (1 + y) - Real.log (1 - y) -
        ∑ j ∈ Finset.range J, 2 * (1 / (2 * (j : ℝ) + 1)) * y ^ (2 * j + 1)| ≤
      2 / (2 * (J : ℝ) + 1) * |y| ^ (2 * J + 1) * (1 - y ^ 2)⁻¹ := by
  have habs : (0 : ℝ) ≤ |y| := abs_nonneg y
  have hsq : y ^ 2 < 1 := by
    obtain ⟨h1, h2⟩ := abs_lt.1 hy
    nlinarith
  have hsq0 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) with hf
  have hsum : HasSum f (Real.log (1 + y) - Real.log (1 - y)) :=
    Real.hasSum_log_sub_log_of_abs_lt_one hy
  have htr : HasSum (fun n => f (n + J))
      (Real.log (1 + y) - Real.log (1 - y) - ∑ i ∈ Finset.range J, f i) :=
    (hasSum_nat_add_iff' J).2 hsum
  have hgeo : HasSum (fun n : ℕ => 2 / (2 * (J : ℝ) + 1) * |y| ^ (2 * J + 1) * (y ^ 2) ^ n)
      (2 / (2 * (J : ℝ) + 1) * |y| ^ (2 * J + 1) * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hsq0 hsq).mul_left _
  have hbd : ∀ n : ℕ,
      ‖f (n + J)‖ ≤ 2 / (2 * (J : ℝ) + 1) * |y| ^ (2 * J + 1) * (y ^ 2) ^ n := by
    intro n
    have hden : (0 : ℝ) < 2 * ((n : ℝ) + (J : ℝ)) + 1 := by positivity
    have hnorm : ‖f (n + J)‖ = 2 / (2 * ((n : ℝ) + (J : ℝ)) + 1) * |y| ^ (2 * (n + J) + 1) := by
      simp only [hf, Real.norm_eq_abs, abs_mul, abs_pow, Nat.cast_add]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / (2 * ((n : ℝ) + (J : ℝ)) + 1) by positivity)]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      ring
    have hpow : |y| ^ (2 * (n + J) + 1) = |y| ^ (2 * J + 1) * (y ^ 2) ^ n := by
      have : (y ^ 2) ^ n = |y| ^ (2 * n) := by
        rw [← sq_abs y, ← pow_mul, mul_comm]
      rw [this, ← pow_add]
      congr 1
      ring
    rw [hnorm, hpow]
    have hle : 2 / (2 * ((n : ℝ) + (J : ℝ)) + 1) ≤ 2 / (2 * (J : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hrest : (0 : ℝ) ≤ |y| ^ (2 * J + 1) * (y ^ 2) ^ n := by positivity
    calc 2 / (2 * ((n : ℝ) + (J : ℝ)) + 1) * (|y| ^ (2 * J + 1) * (y ^ 2) ^ n)
        ≤ 2 / (2 * (J : ℝ) + 1) * (|y| ^ (2 * J + 1) * (y ^ 2) ^ n) := by
          exact mul_le_mul_of_nonneg_right hle hrest
      _ = 2 / (2 * (J : ℝ) + 1) * |y| ^ (2 * J + 1) * (y ^ 2) ^ n := by ring
  simpa [Real.norm_eq_abs] using htr.norm_le_of_bounded hgeo hbd

/-! ### The rational enclosure -/

/-- The `artanh` argument `y = (a-1)/(a+1)` used to compute `log a`. -/
def yOf (a : ℚ) : ℚ := (a - 1) / (a + 1)

/-- The `J`-term partial sum of the `artanh` series for `log a`, as an exact rational. -/
def logMid (a : ℚ) (J : ℕ) : ℚ :=
  ∑ j ∈ Finset.range J, 2 * (1 / (2 * (j : ℚ) + 1)) * yOf a ^ (2 * j + 1)

/-- The explicit geometric bound on the tail of the `artanh` series for `log a`,
as an exact rational. -/
def logTail (a : ℚ) (J : ℕ) : ℚ :=
  2 / (2 * (J : ℚ) + 1) * |yOf a| ^ (2 * J + 1) * (1 - yOf a ^ 2)⁻¹

/-- Certified rational **lower** bound for `Real.log a` (`a > 0`), see `logLo_le`. -/
def logLo (a : ℚ) (J : ℕ) : ℚ := logMid a J - logTail a J

/-- Certified rational **upper** bound for `Real.log a` (`a > 0`), see `le_logHi`. -/
def logHi (a : ℚ) (J : ℕ) : ℚ := logMid a J + logTail a J

section Cast

variable (a : ℚ) (J : ℕ)

theorem yOf_cast : ((yOf a : ℚ) : ℝ) = ((a : ℝ) - 1) / ((a : ℝ) + 1) := by
  simp only [yOf]
  push_cast
  ring

theorem abs_yOf_cast_lt_one (ha : 0 < a) : |((yOf a : ℚ) : ℝ)| < 1 := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [yOf_cast a, abs_div, abs_of_pos (show (0 : ℝ) < (a : ℝ) + 1 by linarith),
    div_lt_one (by linarith)]
  exact abs_lt.2 ⟨by linarith, by linarith⟩

theorem log_eq_artanh (ha : 0 < a) :
    Real.log (1 + ((yOf a : ℚ) : ℝ)) - Real.log (1 - ((yOf a : ℚ) : ℝ)) = Real.log (a : ℝ) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hne : ((a : ℝ) + 1) ≠ 0 := by positivity
  have h1 : 1 + ((yOf a : ℚ) : ℝ) = 2 * (a : ℝ) / ((a : ℝ) + 1) := by
    rw [yOf_cast a]; field_simp; ring
  have h2 : 1 - ((yOf a : ℚ) : ℝ) = 2 / ((a : ℝ) + 1) := by
    rw [yOf_cast a]; field_simp; ring
  have h1p : (0 : ℝ) < 1 + ((yOf a : ℚ) : ℝ) := by rw [h1]; positivity
  have h2p : (0 : ℝ) < 1 - ((yOf a : ℚ) : ℝ) := by rw [h2]; positivity
  rw [← Real.log_div h1p.ne' h2p.ne']
  congr 1
  rw [h1, h2]
  field_simp

end Cast

/-- The analytic content of the enclosure: `Real.log a` is within `logTail a J` of the
rational partial sum `logMid a J`. -/
theorem abs_log_sub_logMid_le (a : ℚ) (J : ℕ) (ha : 0 < a) :
    |Real.log (a : ℝ) - ((logMid a J : ℚ) : ℝ)| ≤ ((logTail a J : ℚ) : ℝ) := by
  have h := abs_log_sub_sum_le (abs_yOf_cast_lt_one a ha) J
  rw [log_eq_artanh a ha] at h
  have hmid : ((logMid a J : ℚ) : ℝ) =
      ∑ j ∈ Finset.range J, 2 * (1 / (2 * (j : ℝ) + 1)) * ((yOf a : ℚ) : ℝ) ^ (2 * j + 1) := by
    simp only [logMid, Rat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have htail : ((logTail a J : ℚ) : ℝ) =
      2 / (2 * (J : ℝ) + 1) * |((yOf a : ℚ) : ℝ)| ^ (2 * J + 1) *
        (1 - ((yOf a : ℚ) : ℝ) ^ 2)⁻¹ := by
    simp only [logTail]
    push_cast
    ring
  rw [hmid, htail]
  exact h

/-- **Certified rational lower bound**: `logLo a J ≤ Real.log a` for every positive rational
`a` and every truncation depth `J`. -/
theorem logLo_le (a : ℚ) (J : ℕ) (ha : 0 < a) : ((logLo a J : ℚ) : ℝ) ≤ Real.log (a : ℝ) := by
  have h := abs_le.1 (abs_log_sub_logMid_le a J ha)
  have : ((logLo a J : ℚ) : ℝ) = ((logMid a J : ℚ) : ℝ) - ((logTail a J : ℚ) : ℝ) := by
    simp only [logLo]; push_cast; ring
  rw [this]
  linarith [h.1]

/-- **Certified rational upper bound**: `Real.log a ≤ logHi a J` for every positive rational
`a` and every truncation depth `J`. -/
theorem le_logHi (a : ℚ) (J : ℕ) (ha : 0 < a) : Real.log (a : ℝ) ≤ ((logHi a J : ℚ) : ℝ) := by
  have h := abs_le.1 (abs_log_sub_logMid_le a J ha)
  have : ((logHi a J : ℚ) : ℝ) = ((logMid a J : ℚ) : ℝ) + ((logTail a J : ℚ) : ℝ) := by
    simp only [logHi]; push_cast; ring
  rw [this]
  linarith [h.2]

/-- Convenience form of `logTail` when the `artanh` argument is nonnegative (i.e. `a ≥ 1`),
which removes the absolute value before numeric evaluation. -/
theorem logTail_of_one_le (a : ℚ) (J : ℕ) (ha : 1 ≤ a) :
    logTail a J = 2 / (2 * (J : ℚ) + 1) * yOf a ^ (2 * J + 1) * (1 - yOf a ^ 2)⁻¹ := by
  have hy : 0 ≤ yOf a := by
    simp only [yOf]
    exact div_nonneg (by linarith) (by linarith)
  rw [logTail, abs_of_nonneg hy]

/-- Convenience form of `logTail` when the `artanh` argument is nonpositive (i.e. `0 < a ≤ 1`),
which removes the absolute value before numeric evaluation.  Companion of
`logTail_of_one_le`; together they cover every positive rational argument. -/
theorem logTail_of_le_one (a : ℚ) (J : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) :
    logTail a J = 2 / (2 * (J : ℚ) + 1) * (-yOf a) ^ (2 * J + 1) * (1 - yOf a ^ 2)⁻¹ := by
  have hy : yOf a ≤ 0 := by
    simp only [yOf]
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  rw [logTail, abs_of_nonpos hy]

end EntropyBound.Constants
