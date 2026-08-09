/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems

/-!
# Stage C · C4, C6 — the Bernstein certificate for `Rpoly`

`SKETCH.md` Step 3 (3c)/(3d) / `BLUEPRINT.md` Stage C, items C4 and C6.

`Rpoly` is *defined* by its degree-`(4,4)` Bernstein expansion against the frozen
`5 × 5` table `cR`.  Two things are proved here:

* `Rpoly_power_basis` (#24): the Bernstein expansion agrees with the power-basis table of
  `SKETCH.md` (3c) — a redundant cross-check that catches transcription errors;
* `Rpoly_lower_bound` (#26): since every `cR k l ≥ 31387/40000` (the minimum, attained at
  `cR 2 3`), every `bern 4 k x ≥ 0` on `[0,1]` and `∑ₖ bern 4 k x = 1` (binomial theorem),
  the double sum is bounded below by the smallest table entry.  This is a genuine
  certificate argument — no sampling of `(s,t)` is involved.
-/

namespace EntropyBound.RankOne

/-- The five degree-`4` binomial coefficients, as `rfl`-lemmas usable by `simp only`. -/
theorem choose_four_zero : Nat.choose 4 0 = 1 := rfl
theorem choose_four_one : Nat.choose 4 1 = 4 := rfl
theorem choose_four_two : Nat.choose 4 2 = 6 := rfl
theorem choose_four_three : Nat.choose 4 3 = 4 := rfl
theorem choose_four_four : Nat.choose 4 4 = 1 := rfl

/-- Bernstein basis polynomials are nonnegative on `[0,1]`. -/
theorem bern_nonneg (m k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ bern m k x := by
  unfold bern
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 k))
    (pow_nonneg (by linarith) _)

/-- The degree-`4` Bernstein basis is a partition of unity: `∑ₖ B_k(x) = 1`. -/
theorem sum_bern_four_eq_one (x : ℝ) : ∑ k ∈ Finset.range 5, bern 4 k x = 1 := by
  simp only [bern, Finset.sum_range_succ, Finset.sum_range_zero,
    choose_four_zero, choose_four_one, choose_four_two, choose_four_three, choose_four_four]
  push_cast
  ring

end EntropyBound.RankOne

namespace EntropyBound

/-- Frozen theorem #24 (`Rpoly_power_basis`). -/
theorem Rpoly_power_basis_proof :
    ∀ s t : ℝ, Rpoly s t
      = 5119741 / 1000000
        - (2653641 / 250000) * (s + t)
        + (5028723 / 500000) * (s ^ 2 + t ^ 2)
        - (1187541 / 250000) * (s ^ 3 + t ^ 3)
        + (1187541 / 1000000) * (s ^ 4 + t ^ 4)
        + (11244987 / 500000) * (s * t)
        - (8719569 / 500000) * (s * t ^ 2 + s ^ 2 * t)
        + (662661 / 100000) * (s * t ^ 3 + s ^ 3 * t)
        - (531441 / 500000) * (s * t ^ 4 + s ^ 4 * t)
        + (8070597 / 1000000) * (s ^ 2 * t ^ 2)
        + (124659 / 250000) * (s ^ 2 * t ^ 3 + s ^ 3 * t ^ 2)
        - (1187541 / 1000000) * (s ^ 2 * t ^ 4 + s ^ 4 * t ^ 2)
        - (2250423 / 500000) * (s ^ 3 * t ^ 3)
        + (531441 / 250000) * (s ^ 3 * t ^ 4 + s ^ 4 * t ^ 3)
        - (531441 / 500000) * (s ^ 4 * t ^ 4) := by
  intro s t
  simp only [Rpoly, cR, bern, Finset.sum_range_succ, Finset.sum_range_zero,
    RankOne.choose_four_zero, RankOne.choose_four_one, RankOne.choose_four_two,
    RankOne.choose_four_three, RankOne.choose_four_four]
  push_cast
  ring

/-- Frozen theorem #26 (`Rpoly_lower_bound`). -/
theorem Rpoly_lower_bound_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, 31387 / 40000 ≤ Rpoly s t := by
  rintro s ⟨hs0, hs1⟩ t ⟨ht0, ht1⟩
  -- The 25 explicit table entries are all at least the minimum `cR 2 3 = 31387/40000`.
  have hc : ∀ k < 5, ∀ l < 5, (31387 / 40000 : ℝ) ≤ cR k l := by
    intro k hk l hl
    interval_cases k <;> interval_cases l <;> norm_num [cR]
  have hs := RankOne.sum_bern_four_eq_one s
  have ht := RankOne.sum_bern_four_eq_one t
  -- Bound the inner sum for each `k`.
  have step : ∀ k ∈ Finset.range 5,
      (31387 / 40000 : ℝ) * bern 4 k s
        ≤ ∑ l ∈ Finset.range 5, cR k l * bern 4 k s * bern 4 l t := by
    intro k hk
    have hexp : (31387 / 40000 : ℝ) * bern 4 k s
        = ∑ l ∈ Finset.range 5, (31387 / 40000 : ℝ) * bern 4 k s * bern 4 l t := by
      rw [← Finset.mul_sum, ht, mul_one]
    rw [hexp]
    refine Finset.sum_le_sum ?_
    intro l hl
    have hBk := RankOne.bern_nonneg 4 k hs0 hs1
    have hBl := RankOne.bern_nonneg 4 l ht0 ht1
    have hckl := hc k (Finset.mem_range.mp hk) l (Finset.mem_range.mp hl)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hckl hBk) hBl
  have houter : (31387 / 40000 : ℝ)
      = ∑ k ∈ Finset.range 5, (31387 / 40000 : ℝ) * bern 4 k s := by
    rw [← Finset.mul_sum, hs, mul_one]
  calc (31387 / 40000 : ℝ)
      = ∑ k ∈ Finset.range 5, (31387 / 40000 : ℝ) * bern 4 k s := houter
    _ ≤ ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, cR k l * bern 4 k s * bern 4 l t :=
        Finset.sum_le_sum step
    _ = Rpoly s t := rfl

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #24, restated verbatim. -/
theorem Rpoly_power_basis :
    ∀ s t : ℝ, Rpoly s t
      = 5119741 / 1000000
        - (2653641 / 250000) * (s + t)
        + (5028723 / 500000) * (s ^ 2 + t ^ 2)
        - (1187541 / 250000) * (s ^ 3 + t ^ 3)
        + (1187541 / 1000000) * (s ^ 4 + t ^ 4)
        + (11244987 / 500000) * (s * t)
        - (8719569 / 500000) * (s * t ^ 2 + s ^ 2 * t)
        + (662661 / 100000) * (s * t ^ 3 + s ^ 3 * t)
        - (531441 / 500000) * (s * t ^ 4 + s ^ 4 * t)
        + (8070597 / 1000000) * (s ^ 2 * t ^ 2)
        + (124659 / 250000) * (s ^ 2 * t ^ 3 + s ^ 3 * t ^ 2)
        - (1187541 / 1000000) * (s ^ 2 * t ^ 4 + s ^ 4 * t ^ 2)
        - (2250423 / 500000) * (s ^ 3 * t ^ 3)
        + (531441 / 250000) * (s ^ 3 * t ^ 4 + s ^ 4 * t ^ 3)
        - (531441 / 500000) * (s ^ 4 * t ^ 4) :=
  EntropyBound.Rpoly_power_basis_proof

/-- Frozen theorem #26, restated verbatim. -/
theorem Rpoly_lower_bound :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, 31387 / 40000 ≤ Rpoly s t :=
  EntropyBound.Rpoly_lower_bound_proof

end EntropyBound.Solution

example : @EntropyBound.Rpoly_power_basis = @EntropyBound.Solution.Rpoly_power_basis := rfl
example : @EntropyBound.Rpoly_lower_bound = @EntropyBound.Solution.Rpoly_lower_bound := rfl

/-- Guardrail: the corner value `R(0,0) = c₀₀`. -/
example : EntropyBound.Rpoly 0 0 = 5119741 / 1000000 := by
  rw [EntropyBound.Rpoly_power_basis_proof]; norm_num

/-- Guardrail: the corner value `R(1,1) = c₄₄ = 1`. -/
example : EntropyBound.Rpoly 1 1 = 1 := by
  rw [EntropyBound.Rpoly_power_basis_proof]; norm_num
