/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Series
import EntropyBound.Proofs.Toolbox.Qseries
import EntropyBound.Proofs.Toolbox.Aseries

/-!
# Stage E items E5, E6 — the mean-value lower bound and the `ℓ²` speed bound

This file produces the frozen conclusions of

* `Aser_lipschitz_lower` (#37) — BLUEPRINT E5 / `SKETCH.md` (5d), first half;
* `entropy_speed_bound` (#38) — BLUEPRINT E6 / `SKETCH.md` (5d), second half;

each stated with

`hA : ∀ z : ℝ, 0 < z → z < 1 → 8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)`

as its ONLY extra hypothesis.  That hypothesis is exactly the frozen conclusion of
`Ader_lower_bound` (#36), which in turn is `Ader_lower_of_middle` applied to the still-open
`Ader_lower_middle` (#35); citing #35 directly would inject `sorryAx`, so it is threaded as
a hypothesis instead.  Once #35 lands, #36/#37/#38 are each a one-liner.

Everything else lives in `namespace EntropyBound.EntropySpeed`.
-/

namespace EntropyBound.EntropySpeed

noncomputable section

open Filter Topology

/-! ### Elementary bounds on the `Aser` summands -/

/-- The common denominator of every series in this file. -/
theorem denom_pos (m : ℕ) : (0 : ℝ) < ((m : ℝ) + 1) * ((m : ℝ) + 2) := by positivity

theorem pow_mem_Icc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    0 ≤ x ^ k ∧ x ^ k ≤ 1 :=
  ⟨pow_nonneg hx0 k, pow_le_one₀ hx0 hx1⟩

/-- Each summand of `Aser`'s inner series is bounded by the majorant `1/((m+1)(m+2))`. -/
theorem aterm_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))
      ≤ 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  obtain ⟨hp0, hp1⟩ := pow_mem_Icc hx0 hx1 (m + 1)
  have hD := denom_pos m
  gcongr
  nlinarith

theorem aterm_nonneg {x : ℝ} (m : ℕ) :
    0 ≤ (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have := denom_pos m
  positivity

theorem summable_aterm {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun m : ℕ => (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) :=
  Summable.of_nonneg_of_le (fun m => aterm_nonneg m) (fun m => aterm_le hx0 hx1 m)
    Toolbox.summable_inv_mul_succ

theorem prodterm_nonneg {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (m : ℕ) :
    0 ≤ (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  obtain ⟨hp0, hp1⟩ := pow_mem_Icc hx0 hx1 (m + 1)
  obtain ⟨hq0, hq1⟩ := pow_mem_Icc hy0 hy1 (m + 1)
  have hD := denom_pos m
  apply div_nonneg _ hD.le
  nlinarith

theorem summable_prodterm {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Summable (fun m : ℕ =>
      (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
  refine Summable.of_nonneg_of_le (fun m => prodterm_nonneg hx0 hx1 hy0 hy1 m) (fun m => ?_)
    Toolbox.summable_inv_mul_succ
  obtain ⟨hp0, hp1⟩ := pow_mem_Icc hx0 hx1 (m + 1)
  obtain ⟨hq0, hq1⟩ := pow_mem_Icc hy0 hy1 (m + 1)
  have hD := denom_pos m
  gcongr
  nlinarith

/-! ### E5 (first ingredient) — `ContinuousOn Aser (Set.Icc 0 1)` by the Weierstrass M-test -/

theorem continuousOn_Aser : ContinuousOn Aser (Set.Icc (0 : ℝ) 1) := by
  have hAeq : Aser = fun u : ℝ => Real.sqrt (∑' m : ℕ,
      (1 - (1 - u ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := rfl
  rw [hAeq]
  have hbound : ∀ (m : ℕ) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      ‖(1 - (1 - u ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))‖
        ≤ 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    intro m u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hx0 : (0 : ℝ) ≤ 1 - u ^ 2 := by nlinarith
    have hx1 : (1 : ℝ) - u ^ 2 ≤ 1 := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (aterm_nonneg m)]
    exact aterm_le hx0 hx1 m
  have huni := tendstoUniformlyOn_tsum
    (u := fun m : ℕ => 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
    Toolbox.summable_inv_mul_succ hbound
  have hcont : ContinuousOn
      (fun u : ℝ => ∑' m : ℕ,
        (1 - (1 - u ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      (Set.Icc (0 : ℝ) 1) := by
    refine huni.continuousOn (Filter.Eventually.frequently ?_)
    filter_upwards with t
    exact continuousOn_finsetSum _ fun m _ => Continuous.continuousOn (by fun_prop)
  simpa [Function.comp_def] using Real.continuous_sqrt.comp_continuousOn hcont

/-! ### E5 — the mean-value lower bound on the slope -/

/-- One-sided form of `Aser_lipschitz_lower`, for `u ≤ v`.  Both orderings of the frozen
statement are derived from it below; nothing is left to "by symmetry". -/
theorem Aser_slope_lower
    (hA : ∀ z : ℝ, 0 < z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z))
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) (huv : u ≤ v) :
    8 / 9 * (v - u) ≤ Aser v - Aser u := by
  rcases eq_or_lt_of_le huv with heq | hlt
  · rw [← heq]; simp
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope Aser
      (fun x : ℝ => (Qser (1 - x ^ 2) - x ^ 2 * Qder (1 - x ^ 2)) / Real.sqrt (Qser (1 - x ^ 2)))
      hlt (continuousOn_Aser.mono (Set.Icc_subset_Icc hu.1 hv.2))
      (fun x hx => EntropyBound.Aser_hasDerivAt_proof x (lt_of_le_of_lt hu.1 hx.1)
        (lt_of_lt_of_le hx.2 hv.2))
    have hc0 : 0 < c := lt_of_le_of_lt hu.1 hc.1
    have hc1 : c < 1 := lt_of_lt_of_le hc.2 hv.2
    have hz0 : (0 : ℝ) < 1 - c ^ 2 := by nlinarith
    have hz1 : (1 : ℝ) - c ^ 2 < 1 := by nlinarith
    have hAc := hA (1 - c ^ 2) hz0 hz1
    rw [show (1 : ℝ) - (1 - c ^ 2) = c ^ 2 by ring] at hAc
    rw [hslope, le_div_iff₀ (by linarith : (0 : ℝ) < v - u)] at hAc
    linarith

/-- BLUEPRINT E5 — the frozen conclusion of `Aser_lipschitz_lower` (#37), with the
`A' ≥ 8/9` statement (#36) as the only extra hypothesis. -/
theorem Aser_lipschitz_lower_of
    (hA : ∀ z : ℝ, 0 < z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      8 / 9 * |u - v| ≤ |Aser u - Aser v| := by
  intro u hu v hv
  rcases le_total u v with h | h
  · have hs := Aser_slope_lower hA hu hv h
    have h1 : (0 : ℝ) ≤ v - u := by linarith
    have h2 : (0 : ℝ) ≤ Aser v - Aser u := by linarith
    rw [abs_sub_comm u v, abs_sub_comm (Aser u) (Aser v), abs_of_nonneg h1, abs_of_nonneg h2]
    exact hs
  · have hs := Aser_slope_lower hA hv hu h
    have h1 : (0 : ℝ) ≤ u - v := by linarith
    have h2 : (0 : ℝ) ≤ Aser u - Aser v := by linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    exact hs

/-! ### E6 — Cauchy–Schwarz on partial sums, passed to the limit -/

theorem div_sqrt_mul_div_sqrt (X Y : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    X / Real.sqrt D * (Y / Real.sqrt D) = X * Y / D := by
  rw [div_mul_div_comm, Real.mul_self_sqrt hD]

theorem div_sqrt_sq (X : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    (X / Real.sqrt D) ^ 2 = X ^ 2 / D := by
  rw [div_pow, Real.sq_sqrt hD]

/-- Cauchy–Schwarz for the partial sums of the two `Aser` sequences. -/
theorem cauchy_schwarz_range (x y : ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range N,
        (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2))) ^ 2
      ≤ (∑ m ∈ Finset.range N, (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        * ∑ m ∈ Finset.range N, (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun m : ℕ => (1 - x ^ (m + 1)) / Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2)))
    (fun m : ℕ => (1 - y ^ (m + 1)) / Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2)))
  have e1 : ∀ m : ℕ,
      (1 - x ^ (m + 1)) / Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2))
        * ((1 - y ^ (m + 1)) / Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      = (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    fun m => div_sqrt_mul_div_sqrt _ _ (denom_pos m).le
  have e2 : ∀ m : ℕ,
      ((1 - x ^ (m + 1)) / Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2))) ^ 2
      = (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    fun m => div_sqrt_sq _ (denom_pos m).le
  have e3 : ∀ m : ℕ,
      ((1 - y ^ (m + 1)) / Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2))) ^ 2
      = (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    fun m => div_sqrt_sq _ (denom_pos m).le
  rw [Finset.sum_congr rfl (fun m _ => e1 m), Finset.sum_congr rfl (fun m _ => e2 m),
    Finset.sum_congr rfl (fun m _ => e3 m)] at h
  exact h

/-- The `tsum` form of Cauchy–Schwarz for the two `Aser` sequences. -/
theorem tsum_prodterm_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∑' m : ℕ, (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      ≤ Real.sqrt (∑' m : ℕ, (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        * Real.sqrt (∑' m : ℕ, (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
  refine Real.tsum_le_of_sum_range_le (fun m => prodterm_nonneg hx0 hx1 hy0 hy1 m) (fun N => ?_)
  set P : ℝ := ∑ m ∈ Finset.range N,
    (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) with hP
  set A : ℝ := ∑ m ∈ Finset.range N,
    (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) with hAdef
  set B : ℝ := ∑ m ∈ Finset.range N,
    (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) with hBdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun m _ => prodterm_nonneg hx0 hx1 hy0 hy1 m
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun m _ => aterm_nonneg m
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun m _ => aterm_nonneg m
  have hCS : P ^ 2 ≤ A * B := cauchy_schwarz_range x y N
  have hstep : P ≤ Real.sqrt A * Real.sqrt B := by
    have h1 := Real.sqrt_le_sqrt hCS
    rwa [Real.sqrt_sq hP0, Real.sqrt_mul hA0] at h1
  have hAtot : A ≤ ∑' m : ℕ, (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    Summable.sum_le_tsum _ (fun m _ => aterm_nonneg m) (summable_aterm hx0 hx1)
  have hBtot : B ≤ ∑' m : ℕ, (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    Summable.sum_le_tsum _ (fun m _ => aterm_nonneg m) (summable_aterm hy0 hy1)
  refine hstep.trans (mul_le_mul (Real.sqrt_le_sqrt hAtot) (Real.sqrt_le_sqrt hBtot)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Expansion of the frozen `#38` summand into the three `Aser`-type series. -/
theorem tsum_diff_sq_eq {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∑' m : ℕ, (x ^ (m + 1) - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      = (∑' m : ℕ, (1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        - 2 * (∑' m : ℕ,
            (1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
        + ∑' m : ℕ, (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
  have Hx := (summable_aterm hx0 hx1).hasSum
  have Hy := (summable_aterm hy0 hy1).hasSum
  have Hp := (summable_prodterm hx0 hx1 hy0 hy1).hasSum
  have Hcomb := (Hx.sub (Hp.mul_left 2)).add Hy
  have heq : (fun m : ℕ => (x ^ (m + 1) - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      = fun m : ℕ =>
        ((1 - x ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))
          - 2 * ((1 - x ^ (m + 1)) * (1 - y ^ (m + 1)) / (((m : ℝ) + 1) * ((m : ℝ) + 2))))
        + (1 - y ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    funext m
    have hD : ((m : ℝ) + 1) * ((m : ℝ) + 2) ≠ 0 := ne_of_gt (denom_pos m)
    field_simp
    ring
  rw [heq]
  exact Hcomb.tsum_eq

/-- BLUEPRINT E6 — the frozen conclusion of `entropy_speed_bound` (#38), with the
`A' ≥ 8/9` statement (#36) as the only extra hypothesis. -/
theorem entropy_speed_bound_of
    (hA : ∀ z : ℝ, 0 < z → z < 1 →
      8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      8 / 9 * |u - v|
        ≤ Real.sqrt (∑' m : ℕ,
            ((1 - u ^ 2) ^ (m + 1) - (1 - v ^ 2) ^ (m + 1)) ^ 2 / ((m + 1) * (m + 2))) := by
  intro u hu v hv
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have hx0 : (0 : ℝ) ≤ 1 - u ^ 2 := by nlinarith
  have hx1 : (1 : ℝ) - u ^ 2 ≤ 1 := by nlinarith
  have hy0 : (0 : ℝ) ≤ 1 - v ^ 2 := by nlinarith
  have hy1 : (1 : ℝ) - v ^ 2 ≤ 1 := by nlinarith
  -- the two `Aser` values as square roots of the two series
  have hAu : Aser u
      = Real.sqrt (∑' m : ℕ, (1 - (1 - u ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) :=
    rfl
  have hAv : Aser v
      = Real.sqrt (∑' m : ℕ, (1 - (1 - v ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) :=
    rfl
  have hAsum0 : 0 ≤ ∑' m : ℕ,
      (1 - (1 - u ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    tsum_nonneg fun m => aterm_nonneg m
  have hBsum0 : 0 ≤ ∑' m : ℕ,
      (1 - (1 - v ^ 2) ^ (m + 1)) ^ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
    tsum_nonneg fun m => aterm_nonneg m
  -- the key inequality: the frozen series dominates `(Aser u - Aser v)²`
  have hkey : (Aser u - Aser v) ^ 2
      ≤ ∑' m : ℕ, ((1 - u ^ 2) ^ (m + 1) - (1 - v ^ 2) ^ (m + 1)) ^ 2
          / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    rw [tsum_diff_sq_eq hx0 hx1 hy0 hy1, hAu, hAv]
    -- `A - 2 P + B ≥ A - 2 √A √B + B = (√A - √B)²`
    have hCS := tsum_prodterm_le hx0 hx1 hy0 hy1
    have hsqA := Real.sq_sqrt hAsum0
    have hsqB := Real.sq_sqrt hBsum0
    nlinarith [hCS, hsqA, hsqB]
  -- conclude by monotonicity of `Real.sqrt` and E5
  have hlip := Aser_lipschitz_lower_of hA u ⟨hu0, hu1⟩ v ⟨hv0, hv1⟩
  have hmono := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_sq_eq_abs] at hmono
  exact le_trans hlip hmono

end

end EntropyBound.EntropySpeed

/-! ### Cheat-watch guardrails (BLUEPRINT Stage B/E boundary values of `Aser`) -/

example : EntropyBound.Aser 0 = 0 := EntropyBound.Toolbox.Aser_zero
example : EntropyBound.Aser 1 = 1 := EntropyBound.Toolbox.Aser_one
