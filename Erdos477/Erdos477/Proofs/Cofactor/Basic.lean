import Erdos477.Defs

/-!
# Stage B — the explicit cofactor bound (L1.1–L1.2, κ = 1/2, SKETCH §4)

The degree-12 cofactor `Qcof u v = ∑_{i=0}^{12} uⁱ v^{12−i}` of the factorization
`u¹³ − v¹³ = (u − v) · Qcof u v` satisfies the explicit lower bound
`Qcof u v ≥ (1/2) · max |u| |v| ^ 12` for **all** real `u, v` (SKETCH §4, L1.1),
which upgrades to the gap bound `|u¹³ − v¹³| ≥ (1/2) · max |u| |v| ^ 12` for
distinct integers `u ≠ v` (L1.2).

Support declarations go in `namespace Erdos477` and must never shadow a frozen
name from `Erdos477/Defs.lean` or `Erdos477/Theorems.lean`.
-/

namespace Erdos477

/-! ## B1 — symmetry of the cofactor -/

/-- `Qcof` is symmetric: reindexing the sum by `i ↦ 12 − i` swaps the roles of
`u` and `v`. This is what licenses the WLOG `|v| ≤ |u|` in L1.1. -/
theorem Qcof_symm (u v : ℝ) : Qcof u v = Qcof v u := by
  simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-! ## B2 — the geometric-sum estimate -/

/-- For `|s| ≤ 1` the truncated geometric sum `∑_{j<13} sʲ` is at least `1/2`
(SKETCH §4, step 4). -/
theorem geom_q_ge_half {s : ℝ} (hs : |s| ≤ 1) :
    (1 / 2 : ℝ) ≤ ∑ j ∈ Finset.range 13, s ^ j := by
  have hs1 : -1 ≤ s := neg_le_of_abs_le hs
  rcases le_or_gt 0 s with hnn | hneg
  · -- `0 ≤ s`: every summand is nonnegative and the `j = 0` summand is `1`.
    have hone : (1 : ℝ) ≤ ∑ j ∈ Finset.range 13, s ^ j := by
      have h0 : (0 : ℕ) ∈ Finset.range 13 := by decide
      have := Finset.single_le_sum
        (f := fun j : ℕ => s ^ j)
        (fun j _ => pow_nonneg hnn j) h0
      simpa using this
    linarith
  · -- `-1 ≤ s < 0`: divide the identity `(∑_{j<13} sʲ)·(s − 1) = s¹³ − 1`.
    have hpos : (0 : ℝ) < 1 - s := by linarith
    have hkey : (∑ j ∈ Finset.range 13, s ^ j) * (s - 1) = s ^ 13 - 1 :=
      geom_sum_mul s 13
    have h13 : s ^ 13 < 0 := Odd.pow_neg (by decide) hneg
    have hkey' : (∑ j ∈ Finset.range 13, s ^ j) * (1 - s) = 1 - s ^ 13 := by
      linear_combination -hkey
    nlinarith [hkey', h13, hs1, hpos]

/-! ## B3 — the frozen bound `Qcof_ge_half_max_pow12` -/

/-- The one-sided (`|v| ≤ |u|`) form of L1.1; the frozen statement follows from it
by symmetry. -/
theorem Qcof_ge_half_of_abs_le {u v : ℝ} (h : |v| ≤ |u|) :
    (1 / 2) * max |u| |v| ^ 12 ≤ Qcof u v := by
  rcases eq_or_ne u 0 with rfl | hu
  · have hv : v = 0 := by
      have : |v| ≤ 0 := by simpa using h
      simpa using abs_nonpos_iff.mp this
    subst hv
    simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  · have hmax : max |u| |v| = |u| := max_eq_left h
    have habs : |u| ^ 12 = u ^ 12 := by
      rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hu12 : (0 : ℝ) < u ^ 12 := by positivity
    have hs : |v / u| ≤ 1 := by
      rw [abs_div]
      exact div_le_one_of_le₀ h (abs_nonneg u)
    have hq := geom_q_ge_half hs
    have hfac : Qcof u v = u ^ 12 * ∑ j ∈ Finset.range 13, (v / u) ^ j := by
      simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
      field_simp
      ring
    rw [hfac, hmax, habs]
    nlinarith [hq, hu12]

/-- **L1.1** (frozen `Qcof_ge_half_max_pow12`) — the explicit cofactor bound with
`κ = 1/2`, valid for all real `u, v`. -/
theorem Qcof_ge_half_max_pow12_proof (u v : ℝ) : (1 / 2) * max |u| |v| ^ 12 ≤ Qcof u v := by
  rcases le_total |v| |u| with h | h
  · exact Qcof_ge_half_of_abs_le h
  · rw [Qcof_symm, max_comm]
    exact Qcof_ge_half_of_abs_le h

/-! ## B4 — the frozen gap bound `abs_pow13_sub_pow13_ge` -/

/-- The factorization `u¹³ − v¹³ = (u − v) · Qcof u v` over `ℝ`. -/
theorem pow13_sub_factor (u v : ℝ) : u ^ 13 - v ^ 13 = (u - v) * Qcof u v := by
  simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- The cofactor is nonnegative on all of `ℝ²` (immediate from L1.1). -/
theorem Qcof_nonneg (u v : ℝ) : 0 ≤ Qcof u v :=
  le_trans (by positivity) (Qcof_ge_half_max_pow12_proof u v)

/-- **L1.2** (frozen `abs_pow13_sub_pow13_ge`) — the gap bound for distinct
integer thirteenth powers. -/
theorem abs_pow13_sub_pow13_ge_proof (u v : ℤ) (h : u ≠ v) :
    (1 / 2) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := by
  have hQ : 0 ≤ Qcof (u : ℝ) (v : ℝ) := Qcof_nonneg _ _
  have hone : (1 : ℝ) ≤ |(u : ℝ) - (v : ℝ)| := by
    have hz : (1 : ℤ) ≤ |u - v| := Int.one_le_abs (sub_ne_zero.mpr h)
    have : ((1 : ℤ) : ℝ) ≤ ((|u - v| : ℤ) : ℝ) := Int.cast_le.mpr hz
    rwa [Int.cast_one, Int.cast_abs, Int.cast_sub] at this
  rw [pow13_sub_factor, abs_mul, abs_of_nonneg hQ]
  calc (1 / 2) * max |(u : ℝ)| |(v : ℝ)| ^ 12
      ≤ Qcof (u : ℝ) (v : ℝ) := Qcof_ge_half_max_pow12_proof _ _
    _ = 1 * Qcof (u : ℝ) (v : ℝ) := (one_mul _).symm
    _ ≤ |(u : ℝ) - (v : ℝ)| * Qcof (u : ℝ) (v : ℝ) :=
        mul_le_mul_of_nonneg_right hone hQ

/-! ## Guardrails (BLUEPRINT, Stage B "Cheat watch") -/

example : Qcof 1 1 = 13 := by
  simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

example : Qcof 1 (-1) = 1 := by
  simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

example : Qcof 0 0 = 0 := by
  simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

example : Qcof 2 (-1) ≥ (1 / 2) * 2 ^ 12 := by
  simp only [Qcof, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end Erdos477
