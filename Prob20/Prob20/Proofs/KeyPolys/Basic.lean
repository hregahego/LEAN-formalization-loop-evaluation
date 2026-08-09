/-
# Stage C — `Prob20/Proofs/KeyPolys/`

The explicit polynomials `p = X² + X`, `q = p/π`, `g = q² + q`, `P = g(X₀X₁)`
and the frozen theorems #7–#10:

* `p_eval_mem_max_proof`   (#7)  `p(D) ⊆ 𝔪`;
* `smul_p_mem_int_proof`   (#8)  `c·p ∈ Int(D)` for **every** `c ∈ T`;
* `g_mem_int_proof`        (#9)  `g ∈ Int(D)`;
* `bigP_mem_intMv_proof`   (#10) `P ∈ Int(D^{n+2})`.

Support lemmas are prefixed `key_`.
-/
import Prob20.Defs
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac
import Prob20.Proofs.Theta.Basic
import Prob20.Proofs.Theta.MemIntMv

namespace Prob20

/-! ## C1 — the Key Observation `p(D) ⊆ 𝔪` (frozen statement #7) -/

/-- `p(x) = x·x + x`. -/
theorem key_p_eval (x : K) : p.eval x = x * x + x := by
  simp [p, pow_two]

/-- **#7** Key Observation: `p(D) ⊆ 𝔪`, where `p = X² + X`.

For `x ∈ D ⊆ T` this is `mul_self_add_self_mem_max` (both residue fields of `T`
are `𝔽₂`, so `x² + x` is divisible by `t` and by `t + 1`). -/
theorem p_eval_mem_max_proof : ∀ x : K, x ∈ Dom → p.eval x ∈ maxSet := by
  intro x hx
  rw [key_p_eval]
  exact mul_self_add_self_mem_max x (Dom_le_T hx)

/-! ## C2 — `c·p ∈ Int(D)` for every `c ∈ T` (frozen statement #8) -/

/-- `𝔪` is a `T`-submodule of `K`, so it absorbs multiplication by elements of `T`. -/
theorem key_mul_mem_max {c x : K} (hc : c ∈ T) (hx : x ∈ maxSet) : c * x ∈ maxSet :=
  maxSet.smul_mem (⟨c, hc⟩ : ↥T) hx

/-- **#8** Key Observation: `c·p ∈ Int(D)` for every `c ∈ T`.

For `x ∈ D` we have `(C c * p).eval x = c · p(x) ∈ T · 𝔪 ⊆ 𝔪 ⊆ D`. -/
theorem smul_p_mem_int_proof : ∀ c : K, c ∈ T → Polynomial.C c * p ∈ IntD := by
  intro c hc
  refine (mem_IntD_iff _).2 fun x hx => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  exact max_le_Dom _ (key_mul_mem_max hc (p_eval_mem_max_proof x hx))

/-- `t ∈ T`. -/
theorem key_tK_mem_T : tK ∈ T := algebraMap_mem_T Polynomial.X

/-- `t + 1 ∈ T`. -/
theorem key_tK_add_one_mem_T : tK + 1 ∈ T := T.add_mem key_tK_mem_T T.one_mem

/-- `p ∈ Int(D)` (Stage E needs it as an element of `↥Int(D)`). -/
theorem p_mem_int : p ∈ IntD := by
  simpa using smul_p_mem_int_proof 1 T.one_mem

/-- `t·p ∈ Int(D)` (Stage E needs it as an element of `↥Int(D)`). -/
theorem t_mul_p_mem_int : Polynomial.C tK * p ∈ IntD :=
  smul_p_mem_int_proof tK key_tK_mem_T

/-- `(t+1)·p ∈ Int(D)` (Stage E needs it as an element of `↥Int(D)`). -/
theorem t_add_one_mul_p_mem_int : Polynomial.C (tK + 1) * p ∈ IntD :=
  smul_p_mem_int_proof (tK + 1) key_tK_add_one_mem_T

/-! ## C3 — `q(D) ⊆ T` -/

/-- For every `x ∈ D`, `q(x) = p(x)/π ∈ T`: by #7 `p(x) = π·y` with `y ∈ T`, and
`π ≠ 0`, so `q(x) = π⁻¹·(π·y) = y`. -/
theorem q_eval_mem_T : ∀ x : K, x ∈ Dom → q.eval x ∈ T := by
  intro x hx
  obtain ⟨y, hy, hpx⟩ := p_eval_mem_max_proof x hx
  have hq : q.eval x = y := by
    rw [q, Polynomial.eval_mul, Polynomial.eval_C, hpx, pow_one, ← mul_assoc,
      inv_mul_cancel₀ frac_piK_ne_zero, one_mul]
  rw [hq]
  exact hy

/-! ## C4 — `g ∈ Int(D)` (frozen statement #9) -/

/-- `g(x) = q(x)·q(x) + q(x)`. -/
theorem key_g_eval (x : K) : g.eval x = q.eval x * q.eval x + q.eval x := by
  simp [g, pow_two]

/-- **#9** `g = q² + q ∈ Int(D)`, where `q = (X² + X)/π`.

For **every** `x ∈ D` we have `q(x) ∈ T` (C3), hence `g(x) = q(x)² + q(x) ∈ 𝔪 ⊆ D`
by `mul_self_add_self_mem_max`. -/
theorem g_mem_int_proof : g ∈ IntD := by
  refine (mem_IntD_iff _).2 fun x hx => ?_
  rw [key_g_eval]
  exact max_le_Dom _ (mul_self_add_self_mem_max _ (q_eval_mem_T x hx))

/-! ## C5 — `P(X₀, X₁) = g(X₀X₁) ∈ Int(D^{n+2})` (frozen statement #10) -/

/-- Substituting an arbitrary multivariate polynomial `u` into a one-variable
polynomial `f` and then evaluating commutes with evaluating `f` at `u(w)`.
(The `mv_eval_aeval_X`-style commutation lemma, for an arbitrary substituted
term instead of a single variable `Xᵢ`.) -/
theorem key_mv_eval_aeval (n : ℕ) (u : MvPolynomial (Fin n) K) (w : Fin n → K)
    (f : Polynomial K) :
    MvPolynomial.eval w (Polynomial.aeval u f) = f.eval (MvPolynomial.eval w u) := by
  induction f using Polynomial.induction_on with
  | C c => simp
  | add f₁ f₂ h₁ h₂ => simp [h₁, h₂]
  | monomial m c _ => simp [pow_succ]

/-- `P(X₀, …, X_{n+1}) = g(X₀X₁)` evaluates to `g(w₀·w₁)`.  (Stage F uses this.) -/
theorem bigP_eval : ∀ (n : ℕ) (w : Fin (n + 2) → K),
    MvPolynomial.eval w (bigP n) = g.eval (w 0 * w 1) := by
  intro n w
  rw [bigP, key_mv_eval_aeval]
  simp

/-- **#10** `P(X₀, X₁) = g(X₀X₁) ∈ Int(D^{n+2})`.

Quantified over **all** `w : Fin (n+2) → D`: `w₀·w₁ ∈ D` since `D` is a subring,
so `P(w) = g(w₀·w₁) ∈ D` by #9. -/
theorem bigP_mem_intMv_proof : ∀ n : ℕ, bigP n ∈ IntDn (n + 2) := by
  intro n
  refine (mem_IntDn_iff _ _).2 fun w hw => ?_
  rw [bigP_eval]
  exact (mem_IntD_iff g).1 g_mem_int_proof _ (Dom.mul_mem (hw 0) (hw 1))

/-! ## Guardrails -/

example : g.eval 0 = 0 := by
  simp [g, q, p]

example : p.eval piK ∈ maxSet :=
  p_eval_mem_max_proof piK ⟨0, 1, T.one_mem, by simp⟩

end Prob20
