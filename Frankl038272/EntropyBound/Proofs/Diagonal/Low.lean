/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Diagonal.Deriv

/-!
# Stage G item G4 — the low range `0 < s ≤ 1/8`

The `SKETCH.md` (7b) argument for `diagonal_small` discards the profile term `g(s)^2 ≥ 0`
and therefore only reaches `s ≤ 10⁻⁶`.  Keeping the profile term — which is a *polynomial*
by `gprofile_sq_eq` (#19) — the same elementary two-sided entropy bound (#7) already gives
positivity on the whole of `(0, 1/8]`, with margin `≈ 7.7 · 10⁻²`:

`Dfun s ≥ (9/5 - C)(-log s) + (9/10)(1 - s²) - C + (log 2/10)·4(1-s)P(s)`
      `≥ (8999/50000)·3 log 2 + (9/10)(63/64) - 81001/50000 + (log 2/10)·4·(7/8)·(9/5) > 0`.

This removes the entire `s → 0` end from the box partition of `diagonal_middle` (#43).
-/

noncomputable section

namespace EntropyBound.Diagonal

open EntropyBound

/-- `Ppoly ≥ 9/5` on `[0, 1/8]`. -/
theorem Ppoly_ge_low {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 8) : (18 : ℝ) / 10 ≤ Ppoly s := by
  simp only [Ppoly]
  nlinarith [sq_nonneg s, sq_nonneg (1 - s), mul_nonneg h0 (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg h0 h0) h0, sq_nonneg (s * s)]

/-- **The low range.**  `0 < Dfun s` for `0 < s ≤ 1/8`. -/
theorem Dfun_pos_low {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1 / 8) : 0 < Dfun s := by
  have hs1 : s < 1 := by linarith
  have hsq0 : (0 : ℝ) < s ^ 2 := by positivity
  have hsq1 : s ^ 2 < 1 := by nlinarith
  -- `X = -log s ≥ 3 log 2`
  have h8 : Real.log ((1 : ℝ) / 8) = -(3 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hX : 3 * Real.log 2 ≤ -Real.log s := by
    have := Real.log_le_log h0 h1
    rw [h8] at this
    linarith
  have hlog2 : log2Lo ≤ Real.log 2 := log2Lo_le
  -- the two entropy bounds (#7)
  have e1 := (EntropyBound.binEntropy_two_sided_proof (s ^ 2) hsq0 hsq1).1
  have e2 := (EntropyBound.binEntropy_two_sided_proof s h0 hs1).2
  have hinv1 : Real.log (1 / s ^ 2) = -(2 * Real.log s) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hinv2 : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
  rw [hinv1] at e1
  rw [hinv2] at e2
  -- turn them into `enat` bounds
  have k1 : -(2 * Real.log s) + 1 - s ^ 2 ≤ enat (s ^ 2) := by
    rw [enat, le_div_iff₀ hsq0]
    linarith
  have k2 : enat s ≤ -Real.log s + 1 := by
    rw [enat, div_le_iff₀ h0]
    linarith
  -- the profile term
  have hP : (18 : ℝ) / 10 ≤ Ppoly s := Ppoly_ge_low h0.le h1
  have hprod : (7 : ℝ) / 8 * (18 / 10) ≤ (1 - s) * Ppoly s := by nlinarith
  have hgt : log2Lo / 10 * (4 * ((7 : ℝ) / 8 * (18 / 10)))
      ≤ Real.log 2 / 10 * (4 * (1 - s) * Ppoly s) := by
    have hpos : (0 : ℝ) < log2Lo := log2Lo_pos
    nlinarith
  have hnum : (0 : ℝ) < (9 / 5 - 81001 / 50000) * (3 * log2Lo) + 9 / 10 * (63 / 64)
      - 81001 / 50000 + log2Lo / 10 * (4 * ((7 : ℝ) / 8 * (18 / 10))) := by
    simp only [log2Lo]
    norm_num
  have hXlo : 3 * log2Lo ≤ -Real.log s := le_trans (by linarith) hX
  have hsq : s ^ 2 ≤ 1 / 64 := by nlinarith
  rw [Dfun_sqrt_free h0.le hs1.le]
  simp only [Cval]
  linarith

end EntropyBound.Diagonal

end
