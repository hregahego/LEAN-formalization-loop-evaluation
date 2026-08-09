/-
# Prob20 — FROZEN theorem statements

The complete list of frozen statements for Problem 20, all `:= sorry`.
This file is **frozen** after SETUP: its SHA-256 is pinned in
`scripts/frozen.sha256`.  No proof may ever change a character of it; proofs are
written in `Prob20/Proofs/**` and re-exposed in `Prob20/Solution.lean`, with
`Prob20/Discharge.lean` machine-checking that each proof has *exactly* the frozen
type.

Numbering follows `BLUEPRINT.md` Part −1 §3.
-/
import Prob20.Defs

open scoped TensorProduct

namespace Prob20

/-- **#1** `D` is an integral domain. -/
theorem D_isDomain : IsDomain ↥Dom := sorry

/-- **#2** `D = 𝔽₂ + 𝔪`, i.e. `D/𝔪 ≅ 𝔽₂`: an element of `K` lies in `D` exactly when
it is congruent to `0` or to `1` modulo `𝔪`. -/
theorem mem_Dom_iff_mem_max_or_sub_one_mem_max :
    ∀ x : K, x ∈ Dom ↔ (x ∈ maxSet ∨ x - 1 ∈ maxSet) := sorry

/-- **#3** `D` is a local ring, with maximal ideal exactly `maxD` (= `𝔪`). -/
theorem D_isLocalRing :
    ∃ h : IsLocalRing ↥Dom, @IsLocalRing.maximalIdeal ↥Dom _ h = maxD := sorry

/-- **#4** `K = Frac(D)`, so `IntD` really is the textbook `Int(D)`. -/
theorem D_isFractionRing : IsFractionRing ↥Dom K := sorry

/-- **#5** `θₙ` really is `f₁ ⊗ ⋯ ⊗ fₙ ↦ ∏ᵢ fᵢ(Xᵢ)`.
This is the anti-cheat statement that pins `theta` to the canonical map. -/
theorem theta_apply_tprod :
    ∀ (n : ℕ) (f : Fin n → ↥IntD),
      theta ↥Dom K n (PiTensorProduct.tprod ↥Dom f)
        = ∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial K)) := sorry

/-- **#6** `θₙ` really lands in `Int(Dⁿ)`, so `θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is well defined. -/
theorem theta_mem_intMv :
    ∀ (n : ℕ) (x : ⨂[↥Dom] (_ : Fin n), ↥IntD), theta ↥Dom K n x ∈ IntDn n := sorry

/-- **#7** Key Observation: `p(D) ⊆ 𝔪`, where `p = X² + X`. -/
theorem p_eval_mem_max : ∀ x : K, x ∈ Dom → p.eval x ∈ maxSet := sorry

/-- **#8** Key Observation: `c·p ∈ Int(D)` for every `c ∈ T`. -/
theorem smul_p_mem_int : ∀ c : K, c ∈ T → Polynomial.C c * p ∈ IntD := sorry

/-- **#9** `g = q² + q ∈ Int(D)`, where `q = (X² + X)/π`. -/
theorem g_mem_int : g ∈ IntD := sorry

/-- **#10** `P(X₀, X₁) = g(X₀X₁) ∈ Int(D^{n+2})`. -/
theorem bigP_mem_intMv : ∀ n : ℕ, bigP n ∈ IntDn (n + 2) := sorry

/-- **#11** `p ∉ 𝔪·Int(D)`. -/
theorem p_not_mem_max_int : p ∉ maxSmulInt := sorry

/-- **#12** `t·p ∉ 𝔪·Int(D)`. -/
theorem t_mul_p_not_mem_max_int : Polynomial.C tK * p ∉ maxSmulInt := sorry

/-- **#13** `(t+1)·p ∉ 𝔪·Int(D)`. -/
theorem t_add_one_mul_p_not_mem_max_int :
    Polynomial.C (tK + 1) * p ∉ maxSmulInt := sorry

/-- **#14** Failure of injectivity: `θₙ` is not injective for any `n ≥ 2`. -/
theorem theta_not_injective :
    ∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n + 2)) := sorry

/-- **#15** The witness `P` is not in the image of `θₙ`. -/
theorem bigP_not_mem_range :
    ∀ n : ℕ, bigP n ∉ LinearMap.range (theta ↥Dom K (n + 2)) := sorry

/-- **#16** Failure of surjectivity onto `Int(Dⁿ)`: there is an element of `Int(D^{n+2})`
outside the image of `θ_{n+2}`. -/
theorem theta_not_surjective :
    ∀ n : ℕ, ∃ F ∈ IntDn (n + 2), F ∉ LinearMap.range (theta ↥Dom K (n + 2)) := sorry

/-- **#17 — HEADLINE.** For the explicit domain `D = 𝔽₂ + t(t+1)T` and every `n ≥ 2`,
the canonical map `θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is neither injective nor surjective. -/
theorem theta_not_injective_not_surjective :
    ∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n + 2)) ∧
      ∃ F ∈ IntDn (n + 2), F ∉ LinearMap.range (theta ↥Dom K (n + 2)) := sorry

end Prob20
