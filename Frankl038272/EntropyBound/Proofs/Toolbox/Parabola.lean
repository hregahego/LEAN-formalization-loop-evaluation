/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Entropy
import EntropyBound.Proofs.Toolbox.Series

/-!
# Stage B — the parabola lower bound for the binary entropy (`SKETCH.md` (2a), BLUEPRINT B1)

Frozen theorem #6, `binEntropy_parabola_lower`, on **all** of `[0,1]`.

The route is the one of the sketch, written in the variable `u = 1 - 2z`:
with `ψ u = (1+u) log (1+u) + (1-u) log (1-u)` one has `Hnat z = log 2 - ψ u / 2`, and the
honest power series of `ψ`,
`ψ u = ∑_{j ≥ 0} u^(2j+2) / ((j+1)(2j+1))`   (`hasSum_psi`),
has nonnegative coefficients, so `ψ u ≤ u² ∑_j 1/((j+1)(2j+1)) ≤ 2 u² log 2`, the last step
because every partial sum of the coefficient series is `≤ ψ 1 = 2 log 2`.  Then
`4 z (1-z) = 1 - u²` finishes.  No series is ever truncated: the truncation appears only
inside the *inequality* `∑_{j<N} c j ≤ 2 log 2`, which is then passed to the limit.
-/

open Filter Finset
open scoped Topology

namespace EntropyBound.Toolbox

noncomputable section

/-- `ψ u = (1+u) log (1+u) + (1-u) log (1-u)`; it satisfies `Hnat z = log 2 - ψ (1-2z) / 2`. -/
def psi (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u)

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

theorem psi_one : psi 1 = 2 * Real.log 2 := by
  norm_num [psi]

/-- `Hnat` in the symmetric variable `u = 1 - 2z`. -/
theorem Hnat_eq_psi {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Hnat z = Real.log 2 - psi (1 - 2 * z) / 2 := by
  have e1 : (1 : ℝ) + (1 - 2 * z) = 2 * (1 - z) := by ring
  have e2 : (1 : ℝ) - (1 - 2 * z) = 2 * z := by ring
  have hz1' : (0 : ℝ) < 1 - z := by linarith
  simp only [Hnat, psi, e1, e2]
  rw [Real.log_mul two_ne_zero (ne_of_gt hz1'), Real.log_mul two_ne_zero (ne_of_gt hz0)]
  ring

/-- `∑_{k ≥ 0} x^(k+2)/((k+1)(k+2)) = (1-x) log (1-x) + x` for `|x| < 1`. -/
theorem hasSum_pow_add_two {x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ (k + 2) / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
      ((1 - x) * Real.log (1 - x) + x) := by
  have h1 : HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hA : HasSum (fun n : ℕ => x ^ (n + 2) / ((n : ℝ) + 1)) (x * -Real.log (1 - x)) := by
    refine hasSum_congr_fun (h1.mul_left x) fun m => ?_
    ring
  have hB : HasSum (fun n : ℕ => x ^ (n + 2) / ((n : ℝ) + 2)) (-Real.log (1 - x) - x) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) 1).2 h1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at h
    refine hasSum_congr_fun h fun m => ?_
    push_cast
    ring
  have hval : x * -Real.log (1 - x) - (-Real.log (1 - x) - x)
      = (1 - x) * Real.log (1 - x) + x := by ring
  rw [← hval]
  refine hasSum_congr_fun (hA.sub hB) fun m => ?_
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The symmetrized summand, supported on the even indices. -/
def psiTerm (u : ℝ) (k : ℕ) : ℝ :=
  u ^ (k + 2) / (((k : ℝ) + 1) * ((k : ℝ) + 2))
    + (-u) ^ (k + 2) / (((k : ℝ) + 1) * ((k : ℝ) + 2))

/-- The honest power series of `ψ`: `ψ u = ∑_{j ≥ 0} u^(2j+2)/((j+1)(2j+1))` for `|u| < 1`. -/
theorem hasSum_psi {u : ℝ} (hu : |u| < 1) :
    HasSum (fun j : ℕ => u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) (psi u) := by
  have hu' : |(-u)| < 1 := by rwa [abs_neg]
  have h1 := hasSum_pow_add_two hu
  have h2 := hasSum_pow_add_two hu'
  rw [show (1 - -u : ℝ) = 1 + u by ring] at h2
  have hv : ((1 - u) * Real.log (1 - u) + u) + ((1 + u) * Real.log (1 + u) + -u) = psi u := by
    simp only [psi]; ring
  have hsum : HasSum (fun k : ℕ => psiTerm u k) (psi u) := by
    rw [← hv]
    exact h1.add h2
  have hvanish : ∀ k : ℕ, k ∉ Set.range (fun j : ℕ => 2 * j) → psiTerm u k = 0 := by
    intro k hk
    have hko : k % 2 = 1 := by
      by_contra h
      exact hk ⟨k / 2, by change 2 * (k / 2) = k; omega⟩
    have hodd : Odd (k + 2) := by rw [Nat.odd_iff]; omega
    simp only [psiTerm]
    rw [hodd.neg_pow]
    ring
  have hres := ((mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff hvanish).2 hsum
  refine hasSum_congr_fun hres fun j => ?_
  have heven : Even (2 * j + 2) := ⟨j + 1, by ring⟩
  simp only [Function.comp_apply, psiTerm]
  rw [heven.neg_pow]
  have hd1 : (0 : ℝ) < ((2 * j : ℕ) : ℝ) + 1 := by positivity
  have hd2 : (0 : ℝ) < ((2 * j : ℕ) : ℝ) + 2 := by positivity
  have hd3 : (0 : ℝ) < ((j : ℝ) + 1) := by positivity
  have hd4 : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  push_cast
  field_simp
  ring

/-- The coefficient series `∑ 1/((j+1)(2j+1))` is summable. -/
theorem summable_coeff : Summable (fun j : ℕ => 1 / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_inv_mul_succ.mul_left 2)
  have hA : (0 : ℝ) < ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) := by positivity
  have hB : (0 : ℝ) < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [mul_one_div, div_le_div_iff₀ hA hB]
  nlinarith

/-- Every partial sum of the coefficient series is at most `ψ 1 = 2 log 2`. -/
theorem sum_range_coeff_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (1 : ℝ) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)) ≤ 2 * Real.log 2 := by
  have hFcont : Continuous (fun u : ℝ =>
      ∑ j ∈ Finset.range N, u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) := by
    refine continuous_finsetSum _ fun j _ => ?_
    fun_prop
  have hle : ∀ u : ℝ, 0 ≤ u → u < 1 →
      (∑ j ∈ Finset.range N, u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) ≤ psi u := by
    intro u hu0 hu1
    have habs : |u| < 1 := by rw [abs_of_nonneg hu0]; exact hu1
    have hs := hasSum_psi habs
    calc ∑ j ∈ Finset.range N, u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))
        ≤ ∑' j : ℕ, u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)) :=
          hs.summable.sum_le_tsum _ (fun i _ => by positivity)
      _ = psi u := hs.tsum_eq
  have hseq : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hc.sub h0
  have h1 := (hFcont.tendsto 1).comp hseq
  have h2 := (continuous_psi.tendsto 1).comp hseq
  have hfinal := le_of_tendsto_of_tendsto' h1 h2 fun n => by
    refine hle _ ?_ ?_
    · have h : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  simpa [psi_one] using hfinal

/-- The coefficient series sums to at most `2 log 2` (in fact exactly). -/
theorem tsum_coeff_le : ∑' j : ℕ, (1 : ℝ) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)) ≤ 2 * Real.log 2 :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) sum_range_coeff_le

/-- The key bound `ψ u ≤ 2 u² log 2` on `(-1,1)`. -/
theorem psi_le {u : ℝ} (hu : |u| < 1) : psi u ≤ 2 * Real.log 2 * u ^ 2 := by
  have hu2 : u ^ 2 ≤ 1 := by
    rcases abs_lt.mp hu with ⟨hl, hr⟩
    nlinarith
  have hs := hasSum_psi hu
  have hterm : ∀ j : ℕ, u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))
      ≤ u ^ 2 * (1 / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) := by
    intro j
    have hD : (0 : ℝ) < ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) := by positivity
    have hpow : u ^ (2 * j + 2) ≤ u ^ 2 := by
      have h1 : (u ^ 2) ^ j ≤ 1 := pow_le_one₀ (by positivity) hu2
      have h2 : u ^ (2 * j + 2) = u ^ 2 * (u ^ 2) ^ j := by
        rw [← pow_mul, ← pow_add]
        ring_nf
      rw [h2]
      nlinarith [sq_nonneg u]
    rw [mul_one_div]
    gcongr
  calc psi u = ∑' j : ℕ, u ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)) := hs.tsum_eq.symm
    _ ≤ ∑' j : ℕ, u ^ 2 * (1 / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1))) :=
        Summable.tsum_le_tsum hterm hs.summable (summable_coeff.mul_left _)
    _ = u ^ 2 * ∑' j : ℕ, (1 : ℝ) / (((j : ℝ) + 1) * (2 * (j : ℝ) + 1)) := tsum_mul_left
    _ ≤ u ^ 2 * (2 * Real.log 2) := by
        have : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
        exact mul_le_mul_of_nonneg_left tsum_coeff_le this
    _ = 2 * Real.log 2 * u ^ 2 := by ring

end

end EntropyBound.Toolbox

namespace EntropyBound

/-- Frozen theorem #6 (`SKETCH.md` (2a), BLUEPRINT B1), on all of `[0,1]`. -/
theorem binEntropy_parabola_lower_proof :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 4 * Real.log 2 * (z * (1 - z)) ≤ Hnat z := by
  intro z hz
  obtain ⟨hz0, hz1⟩ := hz
  rcases eq_or_lt_of_le hz0 with h0 | h0
  · rw [← h0]
    simp [Hnat]
  rcases eq_or_lt_of_le hz1 with h1 | h1
  · rw [h1]
    simp [Hnat]
  have habs : |1 - 2 * z| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hpsi := Toolbox.psi_le habs
  rw [Toolbox.Hnat_eq_psi h0 h1]
  nlinarith [hpsi]

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #6, restated verbatim. -/
theorem binEntropy_parabola_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, 4 * Real.log 2 * (z * (1 - z)) ≤ Hnat z :=
  EntropyBound.binEntropy_parabola_lower_proof

end EntropyBound.Solution

/-- No-drift gate for frozen theorem #6. -/
example :
    @EntropyBound.binEntropy_parabola_lower
      = @EntropyBound.Solution.binEntropy_parabola_lower := rfl

/-! ### Guardrail required by `TASKS.md` -/

example : EntropyBound.Qser 0 = 1 := by
  simp only [EntropyBound.Qser]
  rw [tsum_eq_single 0]
  · norm_num
  · intro j hj
    have h2j : 2 * j ≠ 0 := by omega
    rw [zero_pow h2j]
    simp
