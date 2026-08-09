/-
# Prob20 — FROZEN definitions

Problem 20 (Cahen–Fontana–Frisch–Glaz): the canonical map
`θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is neither injective nor surjective.

This file is **frozen** after SETUP: its SHA-256 is pinned in
`scripts/frozen.sha256` and it may never be edited during the proving phase.
Every modeling decision recorded in `BLUEPRINT.md` Part −1 §2 is realised here.

The counterexample lives inside the single concrete field `K = 𝔽₂(t)`:
`T` is `𝔽₂[t]` localized away from `(t)` and `(t+1)`, `π = t(t+1)`,
`𝔪 = πT`, and `D = 𝔽₂ + 𝔪`.
-/
import Mathlib

open scoped TensorProduct

namespace Prob20

/-! ## Global abbreviations: the universe of discourse -/

/-- The coefficient field `k = 𝔽₂`. -/
abbrev F : Type := ZMod 2

/-- The base ring `A = 𝔽₂[t]`. -/
abbrev A : Type := Polynomial (ZMod 2)

/-- The ambient field `K = Frac(A) = 𝔽₂(t)`. -/
abbrev K : Type := RatFunc (ZMod 2)

/-- The element `t ∈ K`. -/
noncomputable def tK : K := algebraMap A K Polynomial.X

/-! ## D1 — the multiplicative set `S = A ∖ ((t) ∪ (t+1))` -/

/-- `S = A ∖ ((t) ∪ (t+1))`, rendered as `a(0) ≠ 0 ∧ a(1) ≠ 0`
(over `𝔽₂`, `t + 1 = t - 1`, so this is exactly "not divisible by `t` or by `t+1`"). -/
def S : Submonoid A where
  carrier := {a : A | a.eval 0 ≠ 0 ∧ a.eval 1 ≠ 0}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩ <;> simp only [Polynomial.eval_mul, ne_eq, mul_eq_zero, not_or]
    · exact ⟨ha.1, hb.1⟩
    · exact ⟨ha.2, hb.2⟩

/-! ## D2 — the semilocal PID `T = S⁻¹A ⊆ K` -/

/-- `T = S⁻¹A`, realised as a subring of `K`.  The `∃ a, ∃ s ∈ S, s·x = a` form
makes every closure proof pure algebra (common denominators). -/
def T : Subring K where
  carrier := {x : K | ∃ a : A, ∃ s ∈ S, algebraMap A K s * x = algebraMap A K a}
  zero_mem' := ⟨0, 1, S.one_mem, by simp⟩
  one_mem' := ⟨1, 1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, r, hr, hy⟩
    refine ⟨r * a + s * b, s * r, S.mul_mem hs hr, ?_⟩
    simp only [map_mul, map_add]
    linear_combination (algebraMap A K r) * hx + (algebraMap A K s) * hy
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    exact ⟨-a, s, hs, by simp only [map_neg]; linear_combination -hx⟩
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, r, hr, hy⟩
    refine ⟨a * b, s * r, S.mul_mem hs hr, ?_⟩
    simp only [map_mul]
    linear_combination (algebraMap A K r * y) * hx + (algebraMap A K a) * hy

/-! ## D3 — `π = t(t+1)` and the powers `𝔪ʲ = πʲT` -/

/-- `π = t(t+1) ∈ A`. -/
noncomputable def piA : A := Polynomial.X * (Polynomial.X + 1)

/-- `π = t(t+1) ∈ K`. -/
noncomputable def piK : K := algebraMap A K piA

/-- `𝔪ʲ = πʲ·T`, as a `T`-submodule of `K` (fractional-ideal style, so that its
elements are elements of `K`).  Only `j = 1, 2` are ever used. -/
noncomputable def maxPow (j : ℕ) : Submodule ↥T K where
  carrier := {x : K | ∃ y ∈ T, x = piK ^ j * y}
  zero_mem' := ⟨0, T.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u + v, T.add_mem hu hv, by ring⟩
  smul_mem' := by
    rintro c x ⟨u, hu, rfl⟩
    refine ⟨(c : K) * u, T.mul_mem c.2 hu, ?_⟩
    change (c : K) * (piK ^ j * u) = piK ^ j * ((c : K) * u)
    ring

/-- `𝔪 = πT`. -/
noncomputable abbrev maxSet : Submodule ↥T K := maxPow 1

/-! ## D4 — the counterexample domain `D = 𝔽₂ + 𝔪` -/

/-- `D = 𝔽₂ + 𝔪 ⊆ K`, rendered literally as "constant plus an element of `𝔪`". -/
noncomputable def Dom : Subring K where
  carrier := {x : K | ∃ c : ZMod 2, ∃ y ∈ T, x = algebraMap (ZMod 2) K c + piK * y}
  zero_mem' := ⟨0, 0, T.zero_mem, by simp⟩
  one_mem' := ⟨1, 0, T.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨c, u, hu, rfl⟩ ⟨d, v, hv, rfl⟩
    exact ⟨c + d, u + v, T.add_mem hu hv, by simp only [map_add]; ring⟩
  neg_mem' := by
    rintro x ⟨c, u, hu, rfl⟩
    exact ⟨-c, -u, T.neg_mem hu, by simp only [map_neg]; ring⟩
  mul_mem' := by
    rintro x y ⟨c, u, hu, rfl⟩ ⟨d, v, hv, rfl⟩
    refine ⟨c * d, algebraMap (ZMod 2) K c * v + algebraMap (ZMod 2) K d * u + piK * (u * v),
      ?_, ?_⟩
    · have hc : algebraMap (ZMod 2) K c ∈ T :=
        ⟨Polynomial.C c, 1, S.one_mem, by simp⟩
      have hd : algebraMap (ZMod 2) K d ∈ T :=
        ⟨Polynomial.C d, 1, S.one_mem, by simp⟩
      have hpi : piK ∈ T := ⟨piA, 1, S.one_mem, by simp [piK]⟩
      exact T.add_mem (T.add_mem (T.mul_mem hc hv) (T.mul_mem hd hu))
        (T.mul_mem hpi (T.mul_mem hu hv))
    · simp only [map_mul]; ring

/-- Every element of `D` lies in `T`.  (Needed already here, to build `maxD`.) -/
theorem Dom_le_T : Dom ≤ T := by
  rintro x ⟨c, u, hu, rfl⟩
  have hc : algebraMap (ZMod 2) K c ∈ T := ⟨Polynomial.C c, 1, S.one_mem, by simp⟩
  have hpi : piK ∈ T := ⟨piA, 1, S.one_mem, by simp [piK]⟩
  exact T.add_mem hc (T.mul_mem hpi hu)

/-- The maximal ideal `𝔪` of `D`, as an honest `Ideal ↥Dom`. -/
noncomputable def maxD : Ideal ↥Dom where
  carrier := {d : ↥Dom | (d : K) ∈ maxSet}
  zero_mem' := by
    change ((0 : ↥Dom) : K) ∈ maxSet
    simpa only [Subring.coe_zero] using Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    change ((a + b : ↥Dom) : K) ∈ maxSet
    simpa only [Subring.coe_add] using Submodule.add_mem _ ha hb
  smul_mem' := by
    rintro c d ⟨y, hy, hd⟩
    refine ⟨(c : K) * y, T.mul_mem (Dom_le_T c.2) hy, ?_⟩
    change ((c : K) * (d : K)) = piK ^ 1 * ((c : K) * y)
    rw [hd]; ring

/-! ## D5 — `Int(R)` for a general domain -/

/-- `Int(R) = {f ∈ Kr[X] : f(R) ⊆ R}`, the textbook ring of integer-valued
polynomials, defined for an **arbitrary** pair `(R, Kr)` with `Algebra R Kr`. -/
def IntPoly (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr] :
    Subalgebra R (Polynomial Kr) where
  carrier := {f : Polynomial Kr |
    ∀ d : R, f.eval (algebraMap R Kr d) ∈ (algebraMap R Kr).range}
  mul_mem' hf hg d := by
    simpa only [Polynomial.eval_mul] using mul_mem (hf d) (hg d)
  one_mem' d := by simpa only [Polynomial.eval_one] using one_mem _
  add_mem' hf hg d := by
    simpa only [Polynomial.eval_add] using add_mem (hf d) (hg d)
  zero_mem' d := by simpa only [Polynomial.eval_zero] using zero_mem _
  algebraMap_mem' r d := by
    simpa only [Polynomial.algebraMap_apply, Polynomial.eval_C] using
      RingHom.mem_range_self (algebraMap R Kr) r

/-- `Int(D)` for the counterexample domain. -/
noncomputable abbrev IntD : Subalgebra ↥Dom (Polynomial K) := IntPoly ↥Dom K

/-! ## D6 — `Int(Rⁿ)` for a general domain -/

/-- `Int(Rⁿ) = {G ∈ Kr[X₁..Xₙ] : G(Rⁿ) ⊆ R}`, quantified over **all** `v : Fin n → R`. -/
def IntMv (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr] (n : ℕ) :
    Subalgebra R (MvPolynomial (Fin n) Kr) where
  carrier := {G : MvPolynomial (Fin n) Kr |
    ∀ v : Fin n → R,
      MvPolynomial.eval (fun i => algebraMap R Kr (v i)) G ∈ (algebraMap R Kr).range}
  mul_mem' hF hG v := by
    simpa only [map_mul] using mul_mem (hF v) (hG v)
  one_mem' v := by simpa only [map_one] using one_mem _
  add_mem' hF hG v := by
    simpa only [map_add] using add_mem (hF v) (hG v)
  zero_mem' v := by simpa only [map_zero] using zero_mem _
  algebraMap_mem' r v := by simp

/-- `Int(Dⁿ)` for the counterexample domain. -/
noncomputable abbrev IntDn (n : ℕ) : Subalgebra ↥Dom (MvPolynomial (Fin n) K) :=
  IntMv ↥Dom K n

/-! ## D7 — the canonical map `θₙ` -/

/-- The multilinear map `(f₁, …, fₙ) ↦ ∏ᵢ fᵢ(Xᵢ)` underlying `θₙ`. -/
noncomputable def thetaMul (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr] (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => ↥(IntPoly R Kr)) (MvPolynomial (Fin n) Kr) :=
  (MultilinearMap.mkPiAlgebra R (Fin n) (MvPolynomial (Fin n) Kr)).compLinearMap
    (fun i =>
      ((Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) Kr)).restrictScalars
        R).toLinearMap ∘ₗ (IntPoly R Kr).val.toLinearMap)

/-- `θₙ : Int(R)^{⊗ₙ} → Kr[X₁..Xₙ]`, the `R`-linear map determined by
`f₁ ⊗ ⋯ ⊗ fₙ ↦ ∏ᵢ fᵢ(Xᵢ)`.  (Frozen as a linear map into the *ambient*
multivariate polynomial ring; `theta_mem_intMv` certifies that its range lies in
`Int(Rⁿ)`, and `theta_apply_tprod` pins it to the sketch's formula.) -/
noncomputable def theta (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr] (n : ℕ) :
    (⨂[R] (_ : Fin n), ↥(IntPoly R Kr)) →ₗ[R] MvPolynomial (Fin n) Kr :=
  PiTensorProduct.lift (thetaMul R Kr n)

/-! ## D8 — the key polynomials -/

/-- `p(X) = X² + X`. -/
noncomputable def p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X

/-- `q(X) = (X² + X)/π`. -/
noncomputable def q : Polynomial K := Polynomial.C piK⁻¹ * p

/-- `g(X) = q(X)² + q(X)`. -/
noncomputable def g : Polynomial K := q ^ 2 + q

/-- `P(X₀, X₁) = g(X₀X₁)`, in `n + 2` variables (so "`n ≥ 2`" is rendered `n + 2`). -/
noncomputable def bigP (n : ℕ) : MvPolynomial (Fin (n + 2)) K :=
  Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin (n + 2)) K) g

/-! ## D9 — the module `𝔪·Int(D)` -/

/-- `𝔪·Int(D)`: the `D`-submodule of `K[X]` spanned by **all** products `c·f` with
`c ∈ 𝔪` and `f ∈ Int(D)`. -/
noncomputable def maxSmulInt : Submodule ↥Dom (Polynomial K) :=
  Submodule.span ↥Dom
    {G : Polynomial K | ∃ c : K, c ∈ maxSet ∧ ∃ f ∈ IntD, G = Polynomial.C c * f}

end Prob20
