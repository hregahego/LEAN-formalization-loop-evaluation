/-
# Stage F — `Prob20/Proofs/Surjectivity/`

The mixed second finite difference and the frozen theorems #15, #16:

* `bigP_not_mem_range_proof`  (#15) `P ∉ range θ_{n+2}`;
* `theta_not_surjective_proof` (#16) `∃ F ∈ Int(D^{n+2}), F ∉ range θ_{n+2}`.

The argument: on a pure tensor `f₁ ⊗ ⋯ ⊗ f_{n+2}` the mixed second difference
`Δ N F = F(u,u,0…) - F(u,0,0…) - F(0,u,0…) + F(0,0,0…)` telescopes into
`(∏_{i≥2} fᵢ(0)) · (f₀(u) - f₀(0)) · (f₁(u) - f₁(0))`, which lies in `𝔪²` for all
large `N` by the Stage D key lemma; the property "`Δ N · ∈ 𝔪²` for large `N`" cuts
out a `↥Dom`-submodule `EvMv`, so `PiTensorProduct.induction_on` gives
`range θ ≤ EvMv` for the WHOLE tensor power.  But `Δ N (bigP n) = g((u1 N)²)`
has exactly one factor of `t` in its numerator, so it is never in `𝔪²`.

Support lemmas are prefixed `surj_`.
-/
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac
import Prob20.Proofs.Domain.Local
import Prob20.Proofs.Theta.Basic
import Prob20.Proofs.Theta.MemIntMv
import Prob20.Proofs.KeyPolys.Basic
import Prob20.Proofs.Vanishing.Basic

namespace Prob20

/-! ## F1 — the four evaluation points and the mixed second difference -/

/-- The evaluation point `(x, y, 0, …, 0) : Fin (n+2) → K`. -/
noncomputable def surj_pt {n : ℕ} (x y : K) : Fin (n + 2) → K :=
  Fin.cons x (Fin.cons y (fun _ => 0))

theorem surj_pt_zero {n : ℕ} (x y : K) : (surj_pt x y : Fin (n + 2) → K) 0 = x := by
  simp [surj_pt]

theorem surj_pt_one {n : ℕ} (x y : K) : (surj_pt x y : Fin (n + 2) → K) 1 = y := by
  rw [← Fin.succ_zero_eq_one, surj_pt, Fin.cons_succ, Fin.cons_zero]

theorem surj_pt_succ_succ {n : ℕ} (x y : K) (i : Fin n) :
    (surj_pt x y : Fin (n + 2) → K) i.succ.succ = 0 := by
  simp [surj_pt]

/-- Splitting off the two distinguished coordinates of a product over `Fin (n+2)`. -/
theorem surj_prod_eval {n : ℕ} (f : Fin (n + 2) → Polynomial K) (x y : K) :
    ∏ i, (f i).eval (surj_pt x y i)
      = (f 0).eval x * ((f 1).eval y * ∏ i : Fin n, (f i.succ.succ).eval 0) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.succ_zero_eq_one, surj_pt_zero, surj_pt_one, surj_pt_succ_succ]

/-- The mixed second difference `Δ N F` along the test family `u1`. -/
noncomputable def surj_delta (n N : ℕ) (F : MvPolynomial (Fin (n + 2)) K) : K :=
  MvPolynomial.eval (surj_pt (u1 N) (u1 N)) F - MvPolynomial.eval (surj_pt (u1 N) 0) F
    - MvPolynomial.eval (surj_pt 0 (u1 N)) F + MvPolynomial.eval (surj_pt 0 0) F

theorem surj_smul_eval {n : ℕ} (c : ↥Dom) (F : MvPolynomial (Fin n) K) (w : Fin n → K) :
    MvPolynomial.eval w (c • F) = (c : K) * MvPolynomial.eval w F := by
  rw [Algebra.smul_def, map_mul]
  simp [int_algebraMap_dom_apply]

theorem surj_delta_add (n N : ℕ) (F G : MvPolynomial (Fin (n + 2)) K) :
    surj_delta n N (F + G) = surj_delta n N F + surj_delta n N G := by
  simp only [surj_delta, map_add]; ring

theorem surj_delta_smul (n N : ℕ) (c : ↥Dom) (F : MvPolynomial (Fin (n + 2)) K) :
    surj_delta n N (c • F) = (c : K) * surj_delta n N F := by
  simp only [surj_delta, surj_smul_eval]; ring

/-! ## F2 — `range θ_{n+2} ≤ EvMv` -/

/-- `EvMv n = {F | Δ N F ∈ 𝔪² for all large N}`, a `↥Dom`-submodule of `K[X₀..X_{n+1}]`.
(Exactly the multivariate analogue of Stage D's `Ev1`; note `𝔪²`, not `𝔪`.) -/
noncomputable def EvMv (n : ℕ) : Submodule ↥Dom (MvPolynomial (Fin (n + 2)) K) where
  carrier := {F : MvPolynomial (Fin (n + 2)) K | ∃ N₀ : ℕ, ∀ N ≥ N₀, surj_delta n N F ∈ maxPow 2}
  zero_mem' := ⟨0, fun N _ => by simp [surj_delta]⟩
  add_mem' := by
    rintro F G ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    rw [surj_delta_add]
    exact (maxPow 2).add_mem (h₁ N (le_trans (le_max_left _ _) hN))
      (h₂ N (le_trans (le_max_right _ _) hN))
  smul_mem' := by
    rintro c F ⟨N₀, h₀⟩
    refine ⟨N₀, fun N hN => ?_⟩
    rw [surj_delta_smul]
    exact loc_mul_mem_maxPow (Dom_le_T c.2) (h₀ N hN)

/-- Evaluating `∏ᵢ fᵢ(Xᵢ)` at a point is the product of the one-variable values. -/
theorem surj_eval_prod (n : ℕ) (f : Fin n → Polynomial K) (w : Fin n → K) :
    MvPolynomial.eval w (∏ i, Polynomial.aeval (MvPolynomial.X i) (f i))
      = ∏ i, (f i).eval (w i) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => mv_eval_aeval_X n i w (f i)

/-- **The telescoping identity.**  On a product `∏ᵢ fᵢ(Xᵢ)` the mixed second
difference factors as `(∏_{i≥2} fᵢ(0)) · (f₀(u) - f₀(0)) · (f₁(u) - f₁(0))`.
All four terms of `Δ` are needed for this. -/
theorem surj_mixed_difference_prod {n : ℕ} (f : Fin (n + 2) → Polynomial K) (N : ℕ) :
    surj_delta n N (∏ i, Polynomial.aeval (MvPolynomial.X i) (f i))
      = (∏ i : Fin n, (f i.succ.succ).eval 0)
        * (((f 0).eval (u1 N) - (f 0).eval 0) * ((f 1).eval (u1 N) - (f 1).eval 0)) := by
  simp only [surj_delta, surj_eval_prod, surj_prod_eval]
  ring

/-- Pure tensors land in `EvMv`. -/
theorem surj_tprod_mem_EvMv (n : ℕ) (f : Fin (n + 2) → ↥IntD) :
    theta ↥Dom K (n + 2) (PiTensorProduct.tprod ↥Dom f) ∈ EvMv n := by
  rw [theta_apply_tprod_proof]
  obtain ⟨N₁, h₁⟩ := eval_sub_eval_zero_mem_max_u1 ((f 0 : Polynomial K)) (f 0).2
  obtain ⟨N₂, h₂⟩ := eval_sub_eval_zero_mem_max_u1 ((f 1 : Polynomial K)) (f 1).2
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  rw [surj_mixed_difference_prod (fun i => (f i : Polynomial K)) N]
  have hR : (∏ i : Fin n, ((f i.succ.succ : Polynomial K)).eval 0) ∈ Dom :=
    Subring.prod_mem _ fun i _ => eval_zero_mem_Dom _ (f i.succ.succ).2
  exact loc_mul_mem_maxPow (Dom_le_T hR)
    (maxPow_mul_maxPow (h₁ N (le_trans (le_max_left _ _) hN))
      (h₂ N (le_trans (le_max_right _ _) hN)))

/-- **F2.**  The image of the WHOLE tensor power lies in `EvMv` — proved by
`PiTensorProduct.induction_on`, not just on pure tensors. -/
theorem surj_range_le_EvMv (n : ℕ) :
    LinearMap.range (theta ↥Dom K (n + 2)) ≤ EvMv n := by
  rintro F ⟨x, rfl⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [map_smul]
      exact (EvMv n).smul_mem r (surj_tprod_mem_EvMv n f)
  | add x y hx hy =>
      rw [map_add]
      exact (EvMv n).add_mem hx hy

/-! ## F3 — `bigP n ∉ EvMv n` -/

theorem surj_g_eval_zero : g.eval (0 : K) = 0 := by
  simp [g, q, p]

/-- The mixed second difference of `P` collapses to the single value `g((u1 N)²)`. -/
theorem surj_delta_bigP (n N : ℕ) :
    surj_delta n N (bigP n) = g.eval (u1 N * u1 N) := by
  simp only [surj_delta, bigP_eval, surj_pt_zero, surj_pt_one, mul_zero, zero_mul,
    surj_g_eval_zero]
  ring

/-- `y = (u1 (M+1))² = t²(t+1)^{2M+2}`, as an element of `A`. -/
noncomputable def surj_yA (M : ℕ) : A := Polynomial.X ^ 2 * (Polynomial.X + 1) ^ (2 * M + 2)

/-- `q(y) = y(y+1)/π = t(t+1)^{2M+1}(y+1)`, as an element of `A`. -/
noncomputable def surj_qA (M : ℕ) : A :=
  Polynomial.X * (Polynomial.X + 1) ^ (2 * M + 1) * (surj_yA M + 1)

/-- The cofactor of the single factor `t` in the numerator of `g(y)`. -/
noncomputable def surj_wA (M : ℕ) : A :=
  (Polynomial.X + 1) ^ (2 * M + 1) * (surj_yA M + 1) * (surj_qA M + 1)

theorem surj_u1_sq_eq (M : ℕ) :
    u1 (M + 1) * u1 (M + 1) = algebraMap A K (surj_yA M) := by
  rw [van_u1_eq, ← map_mul]
  congr 1
  simp only [van_uA1, surj_yA]
  ring

theorem surj_piA_mul_qA (M : ℕ) :
    piA * surj_qA M = surj_yA M * surj_yA M + surj_yA M := by
  simp only [piA, surj_qA, surj_yA]
  ring

theorem surj_q_eval_u1_sq (M : ℕ) :
    q.eval (u1 (M + 1) * u1 (M + 1)) = algebraMap A K (surj_qA M) := by
  have h : piK * algebraMap A K (surj_qA M)
      = algebraMap A K (surj_yA M) * algebraMap A K (surj_yA M)
        + algebraMap A K (surj_yA M) := by
    rw [piK, ← map_mul, surj_piA_mul_qA, map_add, map_mul]
  rw [q, Polynomial.eval_mul, Polynomial.eval_C, key_p_eval, surj_u1_sq_eq, ← h,
    ← mul_assoc, inv_mul_cancel₀ frac_piK_ne_zero, one_mul]

theorem surj_g_eval_u1_sq (M : ℕ) :
    g.eval (u1 (M + 1) * u1 (M + 1)) = algebraMap A K (Polynomial.X * surj_wA M) := by
  rw [key_g_eval, surj_q_eval_u1_sq, ← map_mul, ← map_add]
  congr 1
  simp only [surj_wA, surj_qA]
  ring

theorem surj_wA_eval_zero (M : ℕ) : (surj_wA M).eval 0 = 1 := by
  simp [surj_wA, surj_qA, surj_yA]

/-- The witness really lies in `𝔪` … -/
theorem surj_g_eval_u1_sq_mem_max (M : ℕ) : g.eval (u1 (M + 1) * u1 (M + 1)) ∈ maxSet := by
  rw [surj_g_eval_u1_sq, van_mem_maxPow_algebraMap, pow_one]
  refine ⟨(Polynomial.X + 1) ^ (2 * M) * (surj_yA M + 1) * (surj_qA M + 1), ?_⟩
  simp only [surj_wA, piA]
  ring

/-- **F3 (core).** … and fails to lie in `𝔪²`, for EVERY `N = M + 1 ≥ 1`:
the numerator of `g((u1 N)²)` has exactly one factor of `t`. -/
theorem surj_g_eval_u1_sq_not_mem (M : ℕ) : g.eval (u1 (M + 1) * u1 (M + 1)) ∉ maxPow 2 := by
  rw [surj_g_eval_u1_sq, van_mem_maxPow_algebraMap]
  refine van_not_dvd_piA_sq_X (surj_wA M) ?_
  rw [surj_wA_eval_zero]
  decide

/-! ## F4 — the frozen statements #15 and #16 -/

/-- **#15** The witness `P` is not in the image of `θ_{n+2}`. -/
theorem bigP_not_mem_range_proof :
    ∀ n : ℕ, bigP n ∉ LinearMap.range (theta ↥Dom K (n + 2)) := by
  intro n hmem
  obtain ⟨N₀, hN₀⟩ := surj_range_le_EvMv n hmem
  have h := hN₀ (N₀ + 1) (Nat.le_succ N₀)
  rw [surj_delta_bigP] at h
  exact surj_g_eval_u1_sq_not_mem N₀ h

/-- **#16** Failure of surjectivity onto `Int(Dⁿ)`: `P ∈ Int(D^{n+2})` (frozen #10)
but `P ∉ range θ_{n+2}` (#15). -/
theorem theta_not_surjective_proof :
    ∀ n : ℕ, ∃ F ∈ IntDn (n + 2), F ∉ LinearMap.range (theta ↥Dom K (n + 2)) :=
  fun n => ⟨bigP n, bigP_mem_intMv_proof n, bigP_not_mem_range_proof n⟩

/-! ## Guardrails — the witness lives exactly between `𝔪` and `𝔪²` -/

example : g.eval ((u1 1) ^ 2) ∈ maxSet := by
  rw [pow_two]
  exact surj_g_eval_u1_sq_mem_max 0

example : g.eval ((u1 1) ^ 2) ∉ maxPow 2 := by
  rw [pow_two]
  exact surj_g_eval_u1_sq_not_mem 0

end Prob20
