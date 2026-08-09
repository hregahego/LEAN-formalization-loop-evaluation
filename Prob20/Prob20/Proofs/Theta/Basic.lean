/-
# Stage B — `Int(D)`, `Int(Dⁿ)` and the canonical map `θₙ`

Stage B items **B1**, **B2**, **B3** of `BLUEPRINT.md`:

* B1 — the *element* form of membership in `IntD` / `IntDn` (`mem_IntD_iff`,
  `mem_IntDn_iff`) plus the closure lemmas every later stage consumes.
* B2 — multilinearity of `thetaMul`; this is free with the `Defs.lean` rendering
  (`MultilinearMap.compLinearMap` of `MultilinearMap.mkPiAlgebra`), so there is
  nothing to prove here.
* B3 — frozen statement **#5** `theta_apply_tprod`, proved as
  `theta_apply_tprod_proof`, pinning `θₙ` to `f₁ ⊗ ⋯ ⊗ fₙ ↦ ∏ᵢ fᵢ(Xᵢ)`.
-/
import Prob20.Defs

open scoped TensorProduct

namespace Prob20

/-! ## B1 — element form of `Int(R)` and `Int(Rⁿ)` -/

/-- For a subring `Dom` of `K`, the structure map `↥Dom → K` is the coercion. -/
theorem int_algebraMap_dom_apply (d : ↥Dom) : algebraMap ↥Dom K d = (d : K) := rfl

/-- The range of `algebraMap ↥Dom K` is exactly the carrier of `Dom`. -/
theorem int_mem_range_iff (x : K) : x ∈ (algebraMap ↥Dom K).range ↔ x ∈ Dom := by
  constructor
  · rintro ⟨d, rfl⟩
    exact d.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **B1** `f ∈ Int(D)` iff `f` maps `D` into `D`, phrased with elements of `K`
carrying a membership hypothesis. -/
theorem mem_IntD_iff :
    ∀ f : Polynomial K, f ∈ IntD ↔ ∀ x : K, x ∈ Dom → f.eval x ∈ Dom := by
  intro f
  constructor
  · intro hf x hx
    exact (int_mem_range_iff _).1 (hf ⟨x, hx⟩)
  · intro h d
    exact (int_mem_range_iff _).2 (h (d : K) d.2)

/-- **B1** `G ∈ Int(Dⁿ)` iff `G` maps `Dⁿ` into `D`, phrased with tuples of
elements of `K` carrying membership hypotheses. -/
theorem mem_IntDn_iff :
    ∀ (n : ℕ) (G : MvPolynomial (Fin n) K),
      G ∈ IntDn n ↔
        ∀ w : Fin n → K, (∀ i, w i ∈ Dom) → MvPolynomial.eval w G ∈ Dom := by
  intro n G
  constructor
  · intro hG w hw
    have h := hG (fun i => ⟨w i, hw i⟩)
    exact (int_mem_range_iff _).1 h
  · intro h v
    exact (int_mem_range_iff _).2 (h (fun i => (v i : K)) fun i => (v i).2)

/-- **B1** Constants from `D` are integer-valued. -/
theorem C_mem_IntD : ∀ c : K, c ∈ Dom → Polynomial.C c ∈ IntD := by
  intro c hc
  refine (mem_IntD_iff _).2 fun x _ => ?_
  simpa only [Polynomial.eval_C] using hc

/-- **B1** The identity polynomial is integer-valued. -/
theorem X_mem_IntD : (Polynomial.X : Polynomial K) ∈ IntD := by
  refine (mem_IntD_iff _).2 fun x hx => ?_
  simpa only [Polynomial.eval_X] using hx

/-- **B1** An integer-valued polynomial has constant term in `D`.  (Stage D.3 and
Stage F2 both need this.) -/
theorem eval_zero_mem_Dom : ∀ f : Polynomial K, f ∈ IntD → f.eval 0 ∈ Dom := by
  intro f hf
  exact (mem_IntD_iff f).1 hf 0 Dom.zero_mem

/-! ## B3 — `θₙ` on pure tensors (frozen statement #5)

B2 needs no work: `thetaMul` is defined in `Defs.lean` as a
`MultilinearMap.compLinearMap` of `MultilinearMap.mkPiAlgebra`, so its
multilinearity is definitional. -/

/-- **B3, generic form.** For an arbitrary pair `(R, Kr)` the map `θₙ` sends the
pure tensor `f₁ ⊗ ⋯ ⊗ fₙ` to `∏ᵢ fᵢ(Xᵢ)`. -/
theorem theta_apply_tprod_generic (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr]
    (n : ℕ) (f : Fin n → ↥(IntPoly R Kr)) :
    theta R Kr n (PiTensorProduct.tprod R f)
      = ∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial Kr)) := by
  simp [theta, thetaMul, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]

/-- **Frozen statement #5** (`theta_apply_tprod`): `θₙ` really is
`f₁ ⊗ ⋯ ⊗ fₙ ↦ ∏ᵢ fᵢ(Xᵢ)`. -/
theorem theta_apply_tprod_proof :
    ∀ (n : ℕ) (f : Fin n → ↥IntD),
      theta ↥Dom K n (PiTensorProduct.tprod ↥Dom f)
        = ∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial K)) :=
  fun n f => theta_apply_tprod_generic ↥Dom K n f

/-! ### Stage-B guardrails

These confirm that the product-of-`fᵢ(Xᵢ)` shape really came out of the
`Defs.lean` rendering of `thetaMul`. -/

example : theta ↥Dom K 1 (PiTensorProduct.tprod ↥Dom fun _ => (1 : ↥IntD)) = 1 := by
  rw [theta_apply_tprod_proof]
  simp

example (f : Fin 1 → ↥IntD) :
    theta ↥Dom K 1 (PiTensorProduct.tprod ↥Dom f)
      = Polynomial.aeval (MvPolynomial.X 0) ((f 0 : Polynomial K)) := by
  rw [theta_apply_tprod_proof]
  simp

example (c d : K) (hc : c ∈ Dom) (hd : d ∈ Dom) :
    theta ↥Dom K 2 (PiTensorProduct.tprod ↥Dom
        ![⟨Polynomial.C c, C_mem_IntD c hc⟩, ⟨Polynomial.C d, C_mem_IntD d hd⟩])
      = MvPolynomial.C c * MvPolynomial.C d := by
  rw [theta_apply_tprod_proof]
  simp [Fin.prod_univ_two]

end Prob20
