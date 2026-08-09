/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.RankOne.Kernel
import EntropyBound.Proofs.RankOne.Bernstein
import EntropyBound.Proofs.RankOne.Determinant
-- `Toolbox.Parabola` (not the `Toolbox.Basic` hub) is imported on purpose: it is the file that
-- actually holds `binEntropy_parabola_lower_proof` (#6), and depending on the hub would couple
-- this stage to every other in-progress `Toolbox` file.
import EntropyBound.Proofs.Toolbox.Parabola
import EntropyBound.Proofs.Toolbox.Poly

/-!
# Stage C, items C3 and C7 — the rank-one product bound (`SKETCH.md` Step 3 (3b), (3e))

This file closes the `RankOne` stage:

* `diag_normalization_proof`     (#23, C3) — `s · g(s) = 2 √(q(s,s)(1 - q(s,s)))` on `[0,1]`;
* `rank_one_product_bound_proof` (#27, C7) — `log 2 · (s t g(s) g(t)) ≤ H(q(s,t))` on `[0,1]²`.

For (#23) both sides are nonnegative, so it suffices to match squares: by
`gprofile_sq_eq` (#19) the left square is `s² · 4 (1-s) P(s)`, and the right one is
`4 q(s,s)(1 - q(s,s))`, which is the *same* polynomial because of the radicand
factorization `(1 + λ²(1-s)²)(1 - s²(1 + λ²(1-s)²)) = (1-s) P(s)`.

For (#27) the determinant identity `Rpoly_determinant_identity` (#25) together with
`Rpoly_lower_bound` (#26) gives

  `q(s,s)(1-q(s,s)) · q(t,t)(1-q(t,t)) ≤ (q(s,t)(1-q(s,t)))²`,

whose square root — legitimate since `q(1-q) ≥ 0` by `q_mem_Icc` (#22) — combines with (#23)
into `s t g(s) g(t) ≤ 4 q(s,t)(1 - q(s,t))`.  Multiplying by `log 2 > 0` and applying
`binEntropy_parabola_lower` (#6) at `q(s,t) ∈ [0,1]` finishes the proof.  The boundary case
`s = 1` (where `g(1) = 0`) needs no separate treatment: every step above holds on the closed
square.

Support lemmas live in `namespace EntropyBound.RankOne`.
-/

namespace EntropyBound

namespace RankOne

/-- `gprof` is a nonnegative multiple of a square root, hence nonnegative everywhere. -/
theorem gprof_nonneg (s : ℝ) : 0 ≤ gprof s := by
  simp only [gprof]
  positivity

/-- The diagonal square identity behind `diag_normalization`: it is a polynomial identity,
valid for every real `s` once `gprof s ^ 2` has been replaced by `4 (1-s) P s`. -/
theorem diag_sq_eq (s : ℝ) :
    s ^ 2 * (4 * (1 - s) * Ppoly s) = 2 ^ 2 * (qker s s * (1 - qker s s)) := by
  simp only [qker, Ppoly]
  ring

end RankOne

/-! ### C3 — the diagonal normalization `s g(s) = 2 √(q(s,s)(1 - q(s,s)))` -/

theorem diag_normalization_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, s * gprof s = 2 * Real.sqrt (qker s s * (1 - qker s s)) := by
  intro s hs
  have hnn : 0 ≤ s * gprof s := mul_nonneg hs.1 (RankOne.gprof_nonneg s)
  have hsq : (s * gprof s) ^ 2 = 2 ^ 2 * (qker s s * (1 - qker s s)) := by
    rw [mul_pow, gprofile_sq_eq_proof s hs]
    exact RankOne.diag_sq_eq s
  calc s * gprof s = Real.sqrt ((s * gprof s) ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt (2 ^ 2 * (qker s s * (1 - qker s s))) := by rw [hsq]
    _ = 2 * Real.sqrt (qker s s * (1 - qker s s)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-! ### C7 — the rank-one product bound -/

theorem rank_one_product_bound_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.log 2 * (s * t * gprof s * gprof t) ≤ Hnat (qker s t) := by
  intro s hs t ht
  have hqst : qker s t ∈ Set.Icc (0 : ℝ) 1 := q_mem_Icc_proof s hs t ht
  have hss : qker s s ∈ Set.Icc (0 : ℝ) 1 := q_mem_Icc_proof s hs s hs
  have htt : qker t t ∈ Set.Icc (0 : ℝ) 1 := q_mem_Icc_proof t ht t ht
  have ha : 0 ≤ qker s s * (1 - qker s s) := mul_nonneg hss.1 (by linarith [hss.2])
  have hb : 0 ≤ qker t t * (1 - qker t t) := mul_nonneg htt.1 (by linarith [htt.2])
  have hqq : 0 ≤ qker s t * (1 - qker s t) := mul_nonneg hqst.1 (by linarith [hqst.2])
  -- the slack term of the determinant identity is nonnegative
  have hslack : 0 ≤ s ^ 2 * t ^ 2 * (s - t) ^ 2 * Rpoly s t :=
    mul_nonneg (by positivity) (by linarith [Rpoly_lower_bound_proof s hs t ht])
  have hab : qker s s * (1 - qker s s) * (qker t t * (1 - qker t t))
      ≤ (qker s t * (1 - qker s t)) ^ 2 := by
    have hdet := Rpoly_determinant_identity_proof s t
    linarith
  -- take square roots
  have hsqrt :
      Real.sqrt (qker s s * (1 - qker s s)) * Real.sqrt (qker t t * (1 - qker t t))
        ≤ qker s t * (1 - qker s t) := by
    rw [← Real.sqrt_mul ha]
    calc Real.sqrt (qker s s * (1 - qker s s) * (qker t t * (1 - qker t t)))
        ≤ Real.sqrt ((qker s t * (1 - qker s t)) ^ 2) := Real.sqrt_le_sqrt hab
      _ = qker s t * (1 - qker s t) := Real.sqrt_sq hqq
  -- rewrite the two diagonal factors
  have hd1 : s * gprof s = 2 * Real.sqrt (qker s s * (1 - qker s s)) :=
    diag_normalization_proof s hs
  have hd2 : t * gprof t = 2 * Real.sqrt (qker t t * (1 - qker t t)) :=
    diag_normalization_proof t ht
  have hprod : s * t * gprof s * gprof t ≤ 4 * (qker s t * (1 - qker s t)) := by
    have hre : s * t * gprof s * gprof t = (s * gprof s) * (t * gprof t) := by ring
    rw [hre, hd1, hd2]
    linarith [hsqrt]
  -- and conclude with the parabola lower bound for `Hnat`
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 4 * Real.log 2 * (qker s t * (1 - qker s t)) ≤ Hnat (qker s t) :=
    binEntropy_parabola_lower_proof (qker s t) hqst
  have hmul := mul_le_mul_of_nonneg_left hprod hlog2.le
  nlinarith [hmul, hH]

end EntropyBound

namespace EntropyBound.Solution

theorem diag_normalization :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, s * gprof s = 2 * Real.sqrt (qker s s * (1 - qker s s)) :=
  EntropyBound.diag_normalization_proof

theorem rank_one_product_bound :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.log 2 * (s * t * gprof s * gprof t) ≤ Hnat (qker s t) :=
  EntropyBound.rank_one_product_bound_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.diag_normalization = @EntropyBound.Solution.diag_normalization := rfl
example :
    @EntropyBound.rank_one_product_bound = @EntropyBound.Solution.rank_one_product_bound := rfl

/-! ### Guardrails (`BLUEPRINT.md` Stage C cheat-watch) -/

example : Rpoly 0 0 = 5119741 / 1000000 := by
  have := Rpoly_power_basis_proof 0 0
  norm_num at this
  linarith

example : Rpoly 1 1 = 1 := by
  have := Rpoly_power_basis_proof 1 1
  norm_num at this
  linarith

end EntropyBound
