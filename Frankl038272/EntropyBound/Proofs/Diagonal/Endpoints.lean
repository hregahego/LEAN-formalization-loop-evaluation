/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Entropy
import EntropyBound.Proofs.Constants.Basic

/-!
# Stage G, items G1–G3 — the three elementary ranges of the diagonal estimate

`BLUEPRINT.md` Part 2 Stage G items G1, G2, G3, i.e. `SKETCH.md` (7a), (7b), (7c):

* `diagonal_at_one` (#40): `Dfun 1 = 0`;
* `diagonal_small` (#41): `0 < Dfun s` for `0 < s ≤ 10⁻⁶`;
* `diagonal_large` (#42): `0 < Dfun s` for `1 - 10⁻⁶ ≤ s < 1`.

The interval-arithmetic middle range `diagonal_middle` (#43) is **not** in this file.

Everything used here is already proved elsewhere: `binEntropy_two_sided` (#7) from
`Proofs/Toolbox/Entropy.lean`, and `log_ten_lower` (#2), `log_two_upper` (#4) from
`Proofs/Constants/Basic.lean`.  Support lemmas live in `namespace EntropyBound.Diagonal`.
-/

noncomputable section

namespace EntropyBound.Diagonal

open Real

/-! ### Support lemmas -/

/-- The binary entropy is symmetric about `1/2`.  Pure unfolding. -/
theorem Hnat_symm (z : ℝ) : Hnat z = Hnat (1 - z) := by
  have h : (1 : ℝ) - (1 - z) = z := by ring
  simp only [Hnat, h]
  ring

/-- `log 2 / 10 * g² ≥ 0`: the profile term of `Dfun` never hurts. -/
theorem gterm_nonneg (s : ℝ) : 0 ≤ Real.log 2 / 10 * (gprof s) ^ 2 :=
  mul_nonneg (by positivity) (sq_nonneg _)

/-- `log (1 / 10⁻⁶) = 6 log 10`, in the shape produced by `binEntropy_two_sided`. -/
theorem log_millionth : Real.log ((1 : ℝ) / 1000000) = -(6 * Real.log 10) := by
  rw [show ((1 : ℝ) / 1000000) = ((10 : ℝ) ^ (6 : ℕ))⁻¹ by norm_num, Real.log_inv,
    Real.log_pow]
  push_cast
  ring

end EntropyBound.Diagonal

namespace EntropyBound

open EntropyBound.Diagonal

/-! ### G1 — `SKETCH.md` (7a) -/

theorem diagonal_at_one_proof : Dfun 1 = 0 := by
  have hg : gprof 1 = 0 := by
    simp only [gprof]
    norm_num
  simp only [Dfun, enat, Hnat, hg]
  norm_num

/-! ### G2 — `SKETCH.md` (7b) -/

theorem diagonal_small_proof : ∀ s : ℝ, 0 < s → s ≤ 1 / 1000000 → 0 < Dfun s := by
  intro s hs0 hs1
  have hs1' : s < 1 := by linarith
  have hsq0 : (0 : ℝ) < s ^ 2 := by positivity
  have hsq1 : s ^ 2 < 1 := by nlinarith
  have hsqle : s ^ 2 ≤ 1 := le_of_lt hsq1
  -- `-log s ≥ 6 log 10 > 12`
  have hlog : Real.log s ≤ -(6 * Real.log 10) := by
    calc Real.log s ≤ Real.log ((1 : ℝ) / 1000000) := Real.log_le_log hs0 hs1
      _ = -(6 * Real.log 10) := log_millionth
  have hL : 12 < -Real.log s := by
    have := EntropyBound.log_ten_lower_proof
    linarith
  -- the two-sided entropy bounds of #7
  have h7s := EntropyBound.binEntropy_two_sided_proof s hs0 hs1'
  have h7sq := EntropyBound.binEntropy_two_sided_proof (s ^ 2) hsq0 hsq1
  have hlog1s : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
  have hlog1sq : Real.log (1 / s ^ 2) = -(2 * Real.log s) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [hlog1s] at h7s
  rw [hlog1sq] at h7sq
  -- `enat (s^2) ≥ -2 log s + 1 - s^2`
  have e1 : -(2 * Real.log s) + 1 - s ^ 2 ≤ Hnat (s ^ 2) / s ^ 2 := by
    rw [le_div_iff₀ hsq0]
    linarith [h7sq.1]
  -- `enat s ≤ -log s + 1`
  have e2 : Hnat s / s ≤ -Real.log s + 1 := by
    rw [div_le_iff₀ hs0]
    linarith [h7s.2]
  have e3 := gterm_nonneg s
  simp only [Dfun, enat, Cval]
  linarith

/-! ### G3 — `SKETCH.md` (7c) -/

theorem diagonal_large_proof : ∀ s : ℝ, 1 - 1 / 1000000 ≤ s → s < 1 → 0 < Dfun s := by
  intro s hs0 hs1
  have hsp : (0 : ℝ) < s := by linarith
  have hsq0 : (0 : ℝ) < s ^ 2 := by positivity
  have heps : (0 : ℝ) < 1 - s := by linarith
  have hepsle : (1 : ℝ) - s ≤ 1 / 1000000 := by linarith
  have hd0 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have hd1 : (1 : ℝ) - s ^ 2 < 1 := by nlinarith
  have he1 : (1 : ℝ) - s < 1 := by linarith
  -- `L = log (1/(1-s)) > 12`
  have hlogeps : Real.log (1 - s) ≤ -(6 * Real.log 10) := by
    calc Real.log (1 - s) ≤ Real.log ((1 : ℝ) / 1000000) := Real.log_le_log heps hepsle
      _ = -(6 * Real.log 10) := log_millionth
  have hL : 12 < Real.log (1 / (1 - s)) := by
    have h10 := EntropyBound.log_ten_lower_proof
    rw [one_div, Real.log_inv]
    linarith
  -- `log (1/(1-s²)) = L - log (1+s)`
  have hsplit : Real.log (1 / (1 - s ^ 2))
      = Real.log (1 / (1 - s)) - Real.log (1 + s) := by
    have hfac : (1 : ℝ) - s ^ 2 = (1 - s) * (1 + s) := by ring
    rw [hfac, one_div, Real.log_inv, Real.log_mul (ne_of_gt heps) (by linarith), one_div,
      Real.log_inv]
    ring
  have hlog1s : Real.log (1 + s) ≤ 25 / 36 := by
    have h2 := EntropyBound.log_two_upper_proof
    have : Real.log (1 + s) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith
  -- the two-sided entropy bounds of #7, transported by the symmetry `Hnat z = Hnat (1-z)`
  have h7d := (EntropyBound.binEntropy_two_sided_proof (1 - s ^ 2) hd0 hd1).1
  have h7e := (EntropyBound.binEntropy_two_sided_proof (1 - s) heps he1).2
  rw [← Hnat_symm] at h7d h7e
  rw [hsplit] at h7d
  set L : ℝ := Real.log (1 / (1 - s)) with hLdef
  set M : ℝ := Real.log (1 + s) with hMdef
  -- `s² ≥ 1 - 2·10⁻⁶`
  have hs2 : (1 : ℝ) - 1 / 500000 ≤ s ^ 2 := by nlinarith
  have hgap : (3 : ℝ) / 10 ≤ (L - M) + s ^ 2 - L := by linarith
  have hXpos : (0 : ℝ) < (L - M) + s ^ 2 := by linarith
  -- the bracket `(9/10)(1+s)(Lδ + s²) - C s (L+1)` is positive
  have hbr : 0 < 9 / 10 * (1 + s) * ((L - M) + s ^ 2) - Cval * s * (L + 1) := by
    have hA : 9 / 10 * (2 * s) * ((L - M) + s ^ 2)
        ≤ 9 / 10 * (1 + s) * ((L - M) + s ^ 2) := by
      nlinarith [mul_pos heps hXpos]
    have hB : 9 / 5 * s * (L + 3 / 10) ≤ 9 / 10 * (2 * s) * ((L - M) + s ^ 2) := by
      nlinarith [mul_nonneg (le_of_lt hsp) (by linarith : (0 : ℝ) ≤ (L - M) + s ^ 2 - (L + 3 / 10))]
    have hC : 0 < 9 / 5 * s * (L + 3 / 10) - Cval * s * (L + 1) := by
      have hrw : 9 / 5 * s * (L + 3 / 10) - Cval * s * (L + 1)
          = s * ((8999 * L - 54001) / 50000) := by
        simp only [Cval]; ring
      rw [hrw]
      exact mul_pos hsp (by linarith)
    linarith
  -- transfer to `Hnat`
  have hAlow : (1 - s ^ 2) * ((L - M) + s ^ 2) ≤ Hnat (s ^ 2) := by linarith
  have hBup : Cval * s * Hnat s ≤ Cval * s * ((1 - s) * (L + 1)) := by
    have hc : (0 : ℝ) ≤ Cval * s := by
      simp only [Cval]; positivity
    exact mul_le_mul_of_nonneg_left h7e hc
  have hprod : 0 < (1 - s) * (9 / 10 * (1 + s) * ((L - M) + s ^ 2) - Cval * s * (L + 1)) :=
    mul_pos heps hbr
  have hnum : 0 < 9 / 10 * Hnat (s ^ 2) - Cval * s * Hnat s := by nlinarith
  have hkey : 0 < 9 / 10 * (Hnat (s ^ 2) / s ^ 2) - Cval * (Hnat s / s) := by
    have heq : 9 / 10 * (Hnat (s ^ 2) / s ^ 2) - Cval * (Hnat s / s)
        = (9 / 10 * Hnat (s ^ 2) - Cval * s * Hnat s) / s ^ 2 := by
      field_simp
    rw [heq]
    exact div_pos hnum hsq0
  have e3 := gterm_nonneg s
  simp only [Dfun, enat]
  linarith

end EntropyBound

namespace EntropyBound.Solution

theorem diagonal_at_one : Dfun 1 = 0 :=
  EntropyBound.diagonal_at_one_proof

theorem diagonal_small : ∀ s : ℝ, 0 < s → s ≤ 1 / 1000000 → 0 < Dfun s :=
  EntropyBound.diagonal_small_proof

theorem diagonal_large : ∀ s : ℝ, 1 - 1 / 1000000 ≤ s → s < 1 → 0 < Dfun s :=
  EntropyBound.diagonal_large_proof

end EntropyBound.Solution

/-! ### No-drift gates -/

example : @EntropyBound.diagonal_at_one = @EntropyBound.Solution.diagonal_at_one := rfl
example : @EntropyBound.diagonal_small = @EntropyBound.Solution.diagonal_small := rfl
example : @EntropyBound.diagonal_large = @EntropyBound.Solution.diagonal_large := rfl

/-! ### Guardrail mandated by the Stage G cheat-watch box -/

example : EntropyBound.Dfun 1 = 0 := EntropyBound.diagonal_at_one_proof

end
