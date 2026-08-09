/-
# Prob20 — the clean answer

Once a frozen theorem of `Prob20/Theorems.lean` is proved in `Prob20/Proofs/**`,
restate it **verbatim** here in `namespace Prob20.Solution` and set it
`:= <name>_proof` (the sorry-free declaration from `Proofs/`).

`scripts/verify.py` checks `#print axioms Prob20.Solution.<name>` for every
frozen name, and generates the gate `@Prob20.<name> = @Prob20.Solution.<name>`
so the restatement cannot drift from the frozen statement.

Iteration 2: frozen #1, #2, #4, #5, #6 are proved and re-exported below.
Iteration 3: frozen #3, #7, #8, #9, #10, #11, #12, #13 are re-exported as well.
Iteration 4: frozen #14, #15, #16, #17 complete the list — all 17 are discharged.
-/
import Prob20.Theorems
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac
import Prob20.Proofs.Domain.Local
import Prob20.Proofs.Theta.Basic
import Prob20.Proofs.Theta.MemIntMv
import Prob20.Proofs.KeyPolys.Basic
import Prob20.Proofs.Vanishing.Basic
import Prob20.Proofs.Injectivity.Basic
import Prob20.Proofs.Surjectivity.Basic
import Prob20.Proofs.Headline.Basic

open scoped TensorProduct

namespace Prob20.Solution

/-- **#1** `D` is an integral domain. -/
theorem D_isDomain : IsDomain ↥Dom := Prob20.D_isDomain_proof

/-- **#2** `D = 𝔽₂ + 𝔪`, i.e. `D/𝔪 ≅ 𝔽₂`: an element of `K` lies in `D` exactly when
it is congruent to `0` or to `1` modulo `𝔪`. -/
theorem mem_Dom_iff_mem_max_or_sub_one_mem_max :
    ∀ x : K, x ∈ Dom ↔ (x ∈ maxSet ∨ x - 1 ∈ maxSet) :=
  Prob20.mem_Dom_iff_mem_max_or_sub_one_mem_max_proof

/-- **#3** `D` is a local ring, with maximal ideal exactly `maxD` (= `𝔪`). -/
theorem D_isLocalRing :
    ∃ h : IsLocalRing ↥Dom, @IsLocalRing.maximalIdeal ↥Dom _ h = maxD :=
  Prob20.D_isLocalRing_proof

/-- **#4** `K = Frac(D)`, so `IntD` really is the textbook `Int(D)`. -/
theorem D_isFractionRing : IsFractionRing ↥Dom K := Prob20.D_isFractionRing_proof

/-- **#5** `θₙ` really is `f₁ ⊗ ⋯ ⊗ fₙ ↦ ∏ᵢ fᵢ(Xᵢ)`.
This is the anti-cheat statement that pins `theta` to the canonical map. -/
theorem theta_apply_tprod :
    ∀ (n : ℕ) (f : Fin n → ↥IntD),
      theta ↥Dom K n (PiTensorProduct.tprod ↥Dom f)
        = ∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial K)) :=
  Prob20.theta_apply_tprod_proof

/-- **#6** `θₙ` really lands in `Int(Dⁿ)`, so `θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is well defined. -/
theorem theta_mem_intMv :
    ∀ (n : ℕ) (x : ⨂[↥Dom] (_ : Fin n), ↥IntD), theta ↥Dom K n x ∈ IntDn n :=
  Prob20.theta_mem_intMv_proof

/-- **#7** Key Observation: `p(D) ⊆ 𝔪`, where `p = X² + X`. -/
theorem p_eval_mem_max : ∀ x : K, x ∈ Dom → p.eval x ∈ maxSet := Prob20.p_eval_mem_max_proof

/-- **#8** Key Observation: `c·p ∈ Int(D)` for every `c ∈ T`. -/
theorem smul_p_mem_int : ∀ c : K, c ∈ T → Polynomial.C c * p ∈ IntD :=
  Prob20.smul_p_mem_int_proof

/-- **#9** `g = q² + q ∈ Int(D)`, where `q = (X² + X)/π`. -/
theorem g_mem_int : g ∈ IntD := Prob20.g_mem_int_proof

/-- **#10** `P(X₀, X₁) = g(X₀X₁) ∈ Int(D^{n+2})`. -/
theorem bigP_mem_intMv : ∀ n : ℕ, bigP n ∈ IntDn (n + 2) := Prob20.bigP_mem_intMv_proof

/-- **#11** `p ∉ 𝔪·Int(D)`. -/
theorem p_not_mem_max_int : p ∉ maxSmulInt := Prob20.p_not_mem_max_int_proof

/-- **#12** `t·p ∉ 𝔪·Int(D)`. -/
theorem t_mul_p_not_mem_max_int : Polynomial.C tK * p ∉ maxSmulInt :=
  Prob20.t_mul_p_not_mem_max_int_proof

/-- **#13** `(t+1)·p ∉ 𝔪·Int(D)`. -/
theorem t_add_one_mul_p_not_mem_max_int :
    Polynomial.C (tK + 1) * p ∉ maxSmulInt :=
  Prob20.t_add_one_mul_p_not_mem_max_int_proof

/-- **#14** Failure of injectivity: `θₙ` is not injective for any `n ≥ 2`. -/
theorem theta_not_injective :
    ∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n + 2)) :=
  Prob20.theta_not_injective_proof

/-- **#15** The witness `P` is not in the image of `θₙ`. -/
theorem bigP_not_mem_range :
    ∀ n : ℕ, bigP n ∉ LinearMap.range (theta ↥Dom K (n + 2)) :=
  Prob20.bigP_not_mem_range_proof

/-- **#16** Failure of surjectivity onto `Int(Dⁿ)`: there is an element of `Int(D^{n+2})`
outside the image of `θ_{n+2}`. -/
theorem theta_not_surjective :
    ∀ n : ℕ, ∃ F ∈ IntDn (n + 2), F ∉ LinearMap.range (theta ↥Dom K (n + 2)) :=
  Prob20.theta_not_surjective_proof

/-- **#17 — HEADLINE.** For the explicit domain `D = 𝔽₂ + t(t+1)T` and every `n ≥ 2`,
the canonical map `θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is neither injective nor surjective. -/
theorem theta_not_injective_not_surjective :
    ∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n + 2)) ∧
      ∃ F ∈ IntDn (n + 2), F ∉ LinearMap.range (theta ↥Dom K (n + 2)) :=
  Prob20.theta_not_injective_not_surjective_proof

end Prob20.Solution
