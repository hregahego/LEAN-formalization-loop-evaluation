/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Poly

/-!
# Stage D, items D1–D2 — the degree-10 Bernstein certificate for `Gpoly` (`SKETCH.md` (4b))

`Gpoly = 64 P - 25 N^2` is a degree-10 polynomial.  Its positivity on `[0,1]` is certified,
**not** sampled: on each half of the interval `Gpoly` is rewritten in the degree-10 Bernstein
basis, whose 11 + 11 coefficients (`bGl`, `bGr` of `Defs.lean` D20) are all positive.  Since
the Bernstein basis is nonnegative on `[0,1]` and sums to `1`, the value is bounded below by
the smallest coefficient, `bGl 4 = 2530002779/840000000 > 0`.

Contents:

* `Gpoly_bernstein_left_proof`  (#28) — `G (x/2)       = ∑_{k<11} bGl k · B_{10,k}(x)`;
* `Gpoly_bernstein_right_proof` (#29) — `G (1/2 + x/2) = ∑_{k<11} bGr k · B_{10,k}(x)`;
* `Gpoly_pos_proof`            (#30) — `0 < G z` on `[0,1]`, by an explicit split at `1/2`.

Support lemmas are in `namespace EntropyBound.ProfileSpeed` (Stage C proves its own
degree-4 analogues in `namespace EntropyBound.RankOne`).
-/

namespace EntropyBound

namespace ProfileSpeed

/-! ### The eleven degree-10 binomial coefficients

`norm_num` does not evaluate `Nat.choose` on numerals, so the row of Pascal's triangle used by
`bern 10 k` is tabulated here (each entry is `rfl`) and fed to `simp` in the expansions below. -/

theorem choose_ten_0 : (10 : ℕ).choose 0 = 1 := rfl
theorem choose_ten_1 : (10 : ℕ).choose 1 = 10 := rfl
theorem choose_ten_2 : (10 : ℕ).choose 2 = 45 := rfl
theorem choose_ten_3 : (10 : ℕ).choose 3 = 120 := rfl
theorem choose_ten_4 : (10 : ℕ).choose 4 = 210 := rfl
theorem choose_ten_5 : (10 : ℕ).choose 5 = 252 := rfl
theorem choose_ten_6 : (10 : ℕ).choose 6 = 210 := rfl
theorem choose_ten_7 : (10 : ℕ).choose 7 = 120 := rfl
theorem choose_ten_8 : (10 : ℕ).choose 8 = 45 := rfl
theorem choose_ten_9 : (10 : ℕ).choose 9 = 10 := rfl
theorem choose_ten_10 : (10 : ℕ).choose 10 = 1 := rfl

/-! ### Generic Bernstein facts -/

/-- Every Bernstein basis polynomial is nonnegative on `[0,1]`. -/
theorem bern_nonneg {m k : ℕ} {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ bern m k x := by
  have : (0 : ℝ) ≤ 1 - x := by linarith
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 k)) (pow_nonneg this _)

/-- The degree-10 Bernstein basis is a partition of unity: `∑_{k<11} B_{10,k}(x) = 1`. -/
theorem sum_bern_ten_eq_one (x : ℝ) : ∑ k ∈ Finset.range 11, bern 10 k x = 1 := by
  calc ∑ k ∈ Finset.range 11, bern 10 k x
      = ∑ k ∈ Finset.range (10 + 1), x ^ k * (1 - x) ^ (10 - k) * ((10 : ℕ).choose k : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        simp only [bern]
        ring
    _ = (x + (1 - x)) ^ 10 := (add_pow x (1 - x) 10).symm
    _ = 1 := by rw [show x + (1 - x) = 1 by ring, one_pow]

/-- The common positive lower bound for both Bernstein coefficient vectors:
`min bGl = bGl 4 = 2530002779/840000000` and `min bGr = bGr 10 = 28`. -/
noncomputable def bMin : ℝ := 2530002779 / 840000000

theorem bMin_pos : 0 < bMin := by norm_num [bMin]

theorem bGl_ge_bMin {k : ℕ} (hk : k ∈ Finset.range 11) : bMin ≤ bGl k := by
  fin_cases hk <;> norm_num [bMin, bGl]

theorem bGr_ge_bMin {k : ℕ} (hk : k ∈ Finset.range 11) : bMin ≤ bGr k := by
  fin_cases hk <;> norm_num [bMin, bGr]

end ProfileSpeed

/-! ### The two Bernstein expansions -/

theorem Gpoly_bernstein_left_proof :
    ∀ x : ℝ, Gpoly (x / 2) = ∑ k ∈ Finset.range 11, bGl k * bern 10 k x := by
  intro x
  simp only [Gpoly, Ppoly, Npoly, bern, bGl, Finset.sum_range_succ, Finset.sum_range_zero,
    ProfileSpeed.choose_ten_0, ProfileSpeed.choose_ten_1, ProfileSpeed.choose_ten_2,
    ProfileSpeed.choose_ten_3, ProfileSpeed.choose_ten_4, ProfileSpeed.choose_ten_5,
    ProfileSpeed.choose_ten_6, ProfileSpeed.choose_ten_7, ProfileSpeed.choose_ten_8,
    ProfileSpeed.choose_ten_9, ProfileSpeed.choose_ten_10]
  push_cast
  ring

theorem Gpoly_bernstein_right_proof :
    ∀ x : ℝ, Gpoly (1 / 2 + x / 2) = ∑ k ∈ Finset.range 11, bGr k * bern 10 k x := by
  intro x
  simp only [Gpoly, Ppoly, Npoly, bern, bGr, Finset.sum_range_succ, Finset.sum_range_zero,
    ProfileSpeed.choose_ten_0, ProfileSpeed.choose_ten_1, ProfileSpeed.choose_ten_2,
    ProfileSpeed.choose_ten_3, ProfileSpeed.choose_ten_4, ProfileSpeed.choose_ten_5,
    ProfileSpeed.choose_ten_6, ProfileSpeed.choose_ten_7, ProfileSpeed.choose_ten_8,
    ProfileSpeed.choose_ten_9, ProfileSpeed.choose_ten_10]
  push_cast
  ring

/-! ### Positivity of `Gpoly` on `[0,1]` -/

theorem Gpoly_pos_proof : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < Gpoly z := by
  intro z hz
  obtain ⟨h0, h1⟩ := hz
  rcases le_or_gt z (1 / 2) with h | h
  · -- Left half: `z = x/2` with `x = 2z ∈ [0,1]`.
    have hx0 : (0 : ℝ) ≤ 2 * z := by linarith
    have hx1 : (2 : ℝ) * z ≤ 1 := by linarith
    have hzx : z = (2 * z) / 2 := by ring
    have key : ProfileSpeed.bMin * (∑ k ∈ Finset.range 11, bern 10 k (2 * z))
        ≤ ∑ k ∈ Finset.range 11, bGl k * bern 10 k (2 * z) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro k hk
      exact mul_le_mul_of_nonneg_right (ProfileSpeed.bGl_ge_bMin hk)
        (ProfileSpeed.bern_nonneg hx0 hx1)
    rw [ProfileSpeed.sum_bern_ten_eq_one, mul_one] at key
    rw [hzx, Gpoly_bernstein_left_proof (2 * z)]
    exact lt_of_lt_of_le ProfileSpeed.bMin_pos key
  · -- Right half: `z = 1/2 + x/2` with `x = 2z - 1 ∈ [0,1]`.
    have hx0 : (0 : ℝ) ≤ 2 * z - 1 := by linarith
    have hx1 : (2 : ℝ) * z - 1 ≤ 1 := by linarith
    have hzx : z = 1 / 2 + (2 * z - 1) / 2 := by ring
    have key : ProfileSpeed.bMin * (∑ k ∈ Finset.range 11, bern 10 k (2 * z - 1))
        ≤ ∑ k ∈ Finset.range 11, bGr k * bern 10 k (2 * z - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro k hk
      exact mul_le_mul_of_nonneg_right (ProfileSpeed.bGr_ge_bMin hk)
        (ProfileSpeed.bern_nonneg hx0 hx1)
    rw [ProfileSpeed.sum_bern_ten_eq_one, mul_one] at key
    rw [hzx, Gpoly_bernstein_right_proof (2 * z - 1)]
    exact lt_of_lt_of_le ProfileSpeed.bMin_pos key

/-! ### Guardrails required by `BLUEPRINT.md` Stage D -/

example : Gpoly 0 = 5023 / 100 := by norm_num [Gpoly, Ppoly, Npoly]

example : Gpoly 1 = 28 := by norm_num [Gpoly, Ppoly, Npoly]

end EntropyBound

namespace EntropyBound.Solution

theorem Gpoly_bernstein_left :
    ∀ x : ℝ, Gpoly (x / 2) = ∑ k ∈ Finset.range 11, bGl k * bern 10 k x :=
  EntropyBound.Gpoly_bernstein_left_proof

theorem Gpoly_bernstein_right :
    ∀ x : ℝ, Gpoly (1 / 2 + x / 2) = ∑ k ∈ Finset.range 11, bGr k * bern 10 k x :=
  EntropyBound.Gpoly_bernstein_right_proof

theorem Gpoly_pos : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < Gpoly z := EntropyBound.Gpoly_pos_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.Gpoly_bernstein_left = @EntropyBound.Solution.Gpoly_bernstein_left := rfl
example : @EntropyBound.Gpoly_bernstein_right = @EntropyBound.Solution.Gpoly_bernstein_right := rfl
example : @EntropyBound.Gpoly_pos = @EntropyBound.Solution.Gpoly_pos := rfl

end EntropyBound
