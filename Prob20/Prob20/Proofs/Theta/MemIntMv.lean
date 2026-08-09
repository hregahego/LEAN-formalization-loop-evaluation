/-
# Stage B4 — `θₙ` lands in `Int(Dⁿ)`

The `aeval`/`eval` commutation lemma `mv_eval_aeval_X` and the frozen statement
**#6** `theta_mem_intMv`, proved here as `theta_mem_intMv_proof`.

Helper names are prefixed `mv_` so they cannot clash with the sibling module
`Prob20/Proofs/Theta/Basic.lean`.
-/
import Prob20.Defs

open scoped TensorProduct

namespace Prob20

/-! ## The `aeval`/`eval` commutation lemma -/

/-- Substituting the variable `Xᵢ` into a one-variable polynomial `f` and then
evaluating at `w : Fin n → K` is the same as evaluating `f` at `w i`. -/
theorem mv_eval_aeval_X (n : ℕ) (i : Fin n) (w : Fin n → K) (f : Polynomial K) :
    MvPolynomial.eval w (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) K) f)
      = f.eval (w i) := by
  induction f using Polynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg]
  | monomial m c _ => simp [pow_succ]

/-! ## `θₙ` on pure tensors, and their membership in `Int(Dⁿ)` -/

/-- `θₙ (f₁ ⊗ ⋯ ⊗ fₙ) = ∏ᵢ fᵢ(Xᵢ)`, re-derived here so that this module does not
depend on the sibling module's `theta_apply_tprod_proof`. -/
theorem mv_theta_tprod (n : ℕ) (f : Fin n → ↥IntD) :
    theta ↥Dom K n (PiTensorProduct.tprod ↥Dom f)
      = ∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial K)) := by
  simp [theta, thetaMul, PiTensorProduct.lift.tprod]

/-- The image of a pure tensor lies in `Int(Dⁿ)`: at any `v : Fin n → ↥Dom` the
product evaluates to `∏ᵢ fᵢ(vᵢ) ∈ D`, since each `fᵢ ∈ Int(D)`. -/
theorem mv_prod_aeval_mem_IntDn (n : ℕ) (f : Fin n → ↥IntD) :
    (∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial K))) ∈ IntDn n := by
  intro v
  rw [map_prod]
  refine prod_mem fun i _ => ?_
  rw [mv_eval_aeval_X]
  exact (f i).2 (v i)

/-! ## Frozen statement #6 -/

/-- **#6** `θₙ` really lands in `Int(Dⁿ)`.  Proved for **all** `x` in the tensor
power by `PiTensorProduct.induction_on`, reducing to scaled pure tensors. -/
theorem theta_mem_intMv_proof :
    ∀ (n : ℕ) (x : ⨂[↥Dom] (_ : Fin n), ↥IntD), theta ↥Dom K n x ∈ IntDn n := by
  intro n x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [map_smul, mv_theta_tprod]
      exact Subalgebra.smul_mem _ (mv_prod_aeval_mem_IntDn n f) r
  | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy

end Prob20
