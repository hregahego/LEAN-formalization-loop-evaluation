/-
# Prob27b — Stage F support file

Stage F of `BLUEPRINT.md` Part 2: P·e leaves Int(A); the headline (F1–F5)

This iteration realises **F1–F4**, i.e. the frozen theorem
`Pe_not_integerValued : ¬ IsIntegerValued (P * Polynomial.C (iota (RAlg.e : A)))`
(SKETCH Step 5).  F5 (`prob27b_counterexample`) is deliberately **not** attempted
here.

The whole point of Step 5 is that the constant `e` must be pushed onto the
**coefficients** of `F̃` before evaluating: `(p * Polynomial.C c).eval x` is
*not* `p.eval x * c` over the noncommutative coefficient ring `A`, and
`Polynomial.eval_mul` / `aeval` are unavailable.  So F1 rewrites
`P * C (ι e)` as `invPi • ((F̃ * C e).map ι)` coefficientwise (F1), F2 computes
`(F̃ * C e)(u+v) = s` in `A`, and F3 shows `s/π` is not in `ι(A)` by deriving
that `π = X` would have to be a unit of `𝔽₂[X]`.
-/
import Prob27b.Defs
import Prob27b.Proofs.StageA.Basic
import Prob27b.Proofs.StageD.Basic
import Prob27b.Proofs.StageE.Basic

namespace Prob27b

namespace StageF

open Polynomial

/-! ## Bridges

Own copies (per the iteration-2 namespace discipline: Stages D/E are being
edited concurrently, so nothing outside `Prob27b.Defs` / `Prob27b.Proofs.StageA`
may be imported). -/

/-- A `RingHom` commutes with `eval` across `Polynomial.map`.  Valid for
arbitrary semirings — no commutativity is used, which matters because `A` and
`B` are noncommutative. -/
theorem eval_map_hom {S T : Type} [Semiring S] [Semiring T] (φ : S →+* T)
    (p : Polynomial S) (x : S) : (p.map φ).eval (φ x) = φ (p.eval x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- Scalars pull out of `eval`.  Proved by `Polynomial.induction_on'` and
`smul_mul_assoc`; `Polynomial.smul_eq_C_mul` is unavailable here because
`Polynomial.C c` is not central in `Polynomial B`. -/
theorem eval_smul (c : K) (p : Polynomial B) (x : B) : (c • p).eval x = c • p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [smul_add, Polynomial.eval_add, Polynomial.eval_add, hp, hq, smul_add]
  | monomial n a =>
      rw [Polynomial.smul_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial,
        smul_mul_assoc]

/-- `1/π · π = 1` in `K`.  This is `inv_mul_cancel₀` applied to
`algebraMap D K π ≠ 0`, which holds because `algebraMap D K` is injective
(`IsFractionRing`) and `π = X ≠ 0`. -/
theorem invPi_mul_pi : invPi * algebraMap D K pi = 1 := by
  have h : (algebraMap D K pi) ≠ 0 := by
    intro hz
    have h0 : pi = 0 := IsFractionRing.injective D K (by rw [hz, map_zero])
    exact Polynomial.X_ne_zero (R := ZMod 2) h0
  exact inv_mul_cancel₀ h

/-! ## F1 — `P · e` as a scalar multiple of `(F̃ · e)` mapped into `B[X]` -/

/-- **F1.**  The constant `ι e` is multiplied into the *coefficients*; the
`invPi` scalar comes out by `smul_mul_assoc`. -/
theorem Pe_eq : P * Polynomial.C (iota (RAlg.e : A))
    = invPi • ((Ftilde * Polynomial.C (RAlg.e : A)).map iota) := by
  ext n
  simp only [P, Polynomial.coeff_mul_C, Polynomial.coeff_smul, Polynomial.coeff_map,
    map_mul, smul_mul_assoc]

/-! ## F2 — `(F̃ · e)(u+v) = s` in `A` -/

/-- **F2, part 1.**  The `A`-side copy of Stage C's `Fe_eq`: the `X²` coefficient
dies because `u·e = 0` and the `X⁴` coefficient survives because `(e+u)·e = e`
(Stage A's `RAlg.u_mul_e` / `RAlg.eu_mul_e`, both generic in the coefficient
ring, hence available over `D`). -/
theorem Ftilde_e_eq : Ftilde * Polynomial.C (RAlg.e : A)
    = Polynomial.monomial 3 (RAlg.e : A) + Polynomial.monomial 4 (RAlg.e : A)
      + Polynomial.monomial 5 (RAlg.e : A) + Polynomial.monomial 6 (RAlg.e : A) := by
  ext n
  simp only [Ftilde, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_monomial,
    add_mul, ite_mul, zero_mul, RAlg.u_mul_e, RAlg.e_mul_e, ite_self, zero_add, add_zero]

/-! ### Guardrails for F2 (the two coefficients Step 3/Step 5 turn on) -/

example : (Ftilde * Polynomial.C (RAlg.e : A)).coeff 2 = 0 := by
  simp only [Ftilde, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_monomial,
    add_mul, ite_mul, zero_mul, RAlg.u_mul_e, RAlg.e_mul_e, ite_self, zero_add, add_zero]
  norm_num

example : (Ftilde * Polynomial.C (RAlg.e : A)).coeff 4 = (RAlg.e : A) := by
  simp only [Ftilde, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_monomial,
    add_mul, ite_mul, zero_mul, RAlg.u_mul_e, RAlg.e_mul_e, ite_self, zero_add, add_zero]
  norm_num

/-- **F2.**  `(F̃ · e)(u+v) = e(u+v)³ + e(u+v)⁴ + e(u+v)⁵ + e(u+v)⁶ = s`, since
`(u+v)⁴ = (u+v)⁵ = (u+v)⁶ = 0` and `e·(u+v)³ = e(s+w) = s`. -/
theorem Ftilde_e_eval_a0 :
    (Ftilde * Polynomial.C (RAlg.e : A)).eval ((RAlg.u : A) + RAlg.v) = (RAlg.s : A) := by
  rw [Ftilde_e_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_monomial]
  rw [RAlg.e_mul_a0_cubed, RAlg.a0_pow_four, RAlg.a0_pow_five, RAlg.a0_pow_six,
    mul_zero, add_zero, add_zero, add_zero]

/-! ## F3 — `s/π ∉ ι(A)` -/

/-- **F3.**  This is the sketch's "`s` is not divisible by `π` because `A` is
`D`-free on `e,f,u,v,p,q,s,w`", *computed*: if `invPi • ι s = ι y`, then reading
off coefficient `6` gives `algebraMap D K (y.coeff 6) = invPi`, hence
`y.coeff 6 * π = 1` by injectivity of `algebraMap D K`, i.e. `X` would be a unit
of `𝔽₂[X]` — refuted by evaluating that equation at `0`. -/
theorem s_div_pi_not_integral : invPi • iota (RAlg.s : A) ∉ Set.range iota := by
  rintro ⟨y, hy⟩
  have h6 := congrArg (fun z : B => RAlg.coeff z 6) hy
  simp only [iota, RAlg.coeff_map, RAlg.coeff_smul, RAlg.s, RAlg.coeff_single, if_true,
    map_one, mul_one] at h6
  have key : algebraMap D K (y.coeff 6 * pi) = algebraMap D K 1 := by
    rw [map_mul, h6, invPi_mul_pi, map_one]
  have key2 : y.coeff 6 * pi = 1 := IsFractionRing.injective D K key
  have hev := congrArg (Polynomial.eval (0 : ZMod 2)) key2
  simp [pi] at hev

end StageF

/-! ## F4 — frozen 16 -/

/-- **Frozen 16.**  `P · e ∉ Int(A)`.  Instantiating the hypothetical
integer-valuedness at `x = u + v` and rewriting with F1, `eval_smul`,
`eval_map_hom` and F2 gives the value `invPi • ι s`, which F3 rules out.  The
product is kept in the frozen order `P * Polynomial.C (iota RAlg.e)`: the
failure is one-sided. -/
theorem Pe_not_integerValued_proof :
    ¬ IsIntegerValued (P * Polynomial.C (iota (RAlg.e : A))) := by
  intro h
  have hx := h ((RAlg.u : A) + RAlg.v)
  rw [StageF.Pe_eq, StageF.eval_smul, StageF.eval_map_hom, StageF.Ftilde_e_eval_a0] at hx
  exact StageF.s_div_pi_not_integral hx

end Prob27b

/-! ## The clean restatement of the frozen Stage-F theorem -/

namespace Prob27b.Solution

/-- **Frozen 16.** `P·e ∉ Int(A)` (Step 5).  The order of the product is frozen:
the failure is one-sided. -/
theorem Pe_not_integerValued :
    ¬ IsIntegerValued (P * Polynomial.C (iota (RAlg.e : A))) := Prob27b.Pe_not_integerValued_proof

end Prob27b.Solution

/-! ## F5 — frozen 17, the HEADLINE

The SKETCH's "Conclusion": `P ∈ Int(A)`, `e ∈ Int(A)`, `P·e ∉ Int(A)`, so `Int(A)`
is not closed under multiplication — while `D = 𝔽₂[X]` still has finite residue
rings and `A` is still finite free of rank `8` over `D` and torsion-free.  Those
three conjuncts are the conjecture's hypotheses, so they are part of the
statement: without them the existential would not contradict anything.

Purely an assembly of already-proved `_proof` names — nothing new is derived
here.  The existential's `p, q` are `P` and `Polynomial.C (iota RAlg.e)` **in
that order**, so `p * q` is the frozen product `P * Polynomial.C (iota RAlg.e)`;
the failure is one-sided and `Polynomial.C (iota RAlg.e) * P` would not do. -/

namespace Prob27b

/-- **Frozen 17 (HEADLINE).**  Problem 27(b) is false. -/
theorem prob27b_counterexample_proof :
    (∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)) ∧
    Nonempty (Module.Basis (Fin 8) D A) ∧
    NoZeroSMulDivisors D A ∧
    (∃ p q : Polynomial B,
        IsIntegerValued p ∧ IsIntegerValued q ∧ ¬ IsIntegerValued (p * q)) :=
  ⟨Prob27b.D_hasFiniteResidueRings_proof, Prob27b.A_isFreeOfRankEight_proof,
    Prob27b.A_torsionFree_proof, P, Polynomial.C (iota (RAlg.e : A)),
    Prob27b.P_integerValued_proof, Prob27b.constE_integerValued_proof,
    Prob27b.Pe_not_integerValued_proof⟩

end Prob27b

/-! ## The clean restatement of the headline -/

namespace Prob27b.Solution

/-- **Frozen 17 (HEADLINE).** `D` has finite residue rings, `A` is finite free of
rank `8` over `D` and torsion-free, and yet `Int(A)` is not closed under
multiplication. -/
theorem prob27b_counterexample :
    (∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)) ∧
    Nonempty (Module.Basis (Fin 8) D A) ∧
    NoZeroSMulDivisors D A ∧
    (∃ p q : Polynomial B,
        IsIntegerValued p ∧ IsIntegerValued q ∧ ¬ IsIntegerValued (p * q)) :=
  Prob27b.prob27b_counterexample_proof

end Prob27b.Solution
