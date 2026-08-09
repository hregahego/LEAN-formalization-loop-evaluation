/-
Stage C -- the characteristic-2 `s`-component obstruction (C1-C3).

Iteration 1 delivered C1 (`f2_cancel`) and C2 (`dvd_s_of_u_vanish`), together
with the packaged `∀`-form `hcanc_Dbase` that Stage E consumes as its `hcanc`
hypothesis.  Iteration 2 adds C3 (`s_component_cancellation_proof`) on top of the
Stage-B coordinate layer, with the two reusable span characterisations
`mem_span_sElt_iff` and `mem_span_t_sElt_iff`.

WARNING.  Everything in this file is special to the base ring `Dbase = 𝔽₂[t]`.
The statement of `dvd_s_of_u_vanish` is FALSE over `Polynomial Dbase` -- that
asymmetry between `D` and `D[X]` *is* the counterexample of Problem 30(c).  So
none of these lemmas may be marked `@[simp]`, turned into an instance, or
restated at a generic base: Stage E must take the cancellation as an explicit
hypothesis and only ever instantiate it at `B = Dbase`, `τ = tD`.

Nothing here edits `Defs.lean` or `Theorems.lean`.
-/
import Prob30c.Defs
import Prob30c.Proofs.Model.Basic

namespace Prob30c

/-- **C1.**  The characteristic-2 cancellation, at the level of constant terms.

Over `𝔽₂`: if the `u₁`-coordinate `α₂β₃ + α₃β₂ + α₃β₃` and the `u₂`-coordinate
`α₁β₃ + α₃β₁ + α₂β₂` of a product both vanish, then the "`α₂β₂`-free" part
`α₁β₃ + α₃β₁` already vanishes on its own.

Proved by kernel `decide` over all `64 = 2⁶` tuples.  (Mathematically: if
`α₂β₂ ≠ 0` then `α₂ = β₂ = 1`, and the first equation reads
`β₃ + α₃ + α₃β₃ = 0`, which over `𝔽₂` forces `α₃ = β₃ = 0`, so
`α₁β₃ + α₃β₁ = 0`; otherwise `α₂β₂ = 0` and the second equation gives it
directly.)

This is FALSE over a bigger base such as `𝔽₂[t]` in place of `𝔽₂` -- see
`hcanc_Dbase` for the only extension of it that survives. -/
theorem f2_cancel : ∀ α₁ α₂ α₃ β₁ β₂ β₃ : ZMod 2,
    α₂ * β₃ + α₃ * β₂ + α₃ * β₃ = 0 → α₁ * β₃ + α₃ * β₁ + α₂ * β₂ = 0 →
    α₁ * β₃ + α₃ * β₁ = 0 := by
  decide

/-- **C2.**  The coefficient-level cancellation over `Dbase = 𝔽₂[t]`.

If the two `u`-coordinates `a₂b₃ + a₃b₂ + a₃b₃` and `a₁b₃ + a₃b₁ + a₂b₂` of a
product vanish in `Dbase`, then the `s`-coordinate `a₁b₃ + a₃b₁` is divisible by
`tD = X`: an extra factor of `t` is forced.

`Polynomial.X_dvd_iff` reduces the goal to the vanishing of the constant term,
and `Polynomial.mul_coeff_zero` turns the two hypotheses into instances of
`f2_cancel` at the constant terms.

This is exactly the shape Stage E takes as its hypothesis
`hcanc : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : B, … → … → τ ∣ (a₁*b₃ + a₃*b₁)`, so it must not
be specialised further, reordered, or given extra hypotheses. -/
theorem dvd_s_of_u_vanish (a₁ a₂ a₃ b₁ b₂ b₃ : Dbase)
    (h₁ : a₂ * b₃ + a₃ * b₂ + a₃ * b₃ = 0) (h₂ : a₁ * b₃ + a₃ * b₁ + a₂ * b₂ = 0) :
    tD ∣ (a₁ * b₃ + a₃ * b₁) := by
  rw [Polynomial.X_dvd_iff]
  have h₁' : a₂.coeff 0 * b₃.coeff 0 + a₃.coeff 0 * b₂.coeff 0
      + a₃.coeff 0 * b₃.coeff 0 = 0 := by
    simpa only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_zero]
      using congrArg (fun p => Polynomial.coeff p 0) h₁
  have h₂' : a₁.coeff 0 * b₃.coeff 0 + a₃.coeff 0 * b₁.coeff 0
      + a₂.coeff 0 * b₂.coeff 0 = 0 := by
    simpa only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_zero]
      using congrArg (fun p => Polynomial.coeff p 0) h₂
  simpa only [Polynomial.coeff_add, Polynomial.mul_coeff_zero] using
    f2_cancel _ _ _ _ _ _ h₁' h₂'

/-- **C2, packaged.**  `dvd_s_of_u_vanish` as the single `∀`-statement that
Stage E applies, i.e. the hypothesis
`hcanc : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : B, a₂*b₃+a₃*b₂+a₃*b₃ = 0 →
  a₁*b₃+a₃*b₁+a₂*b₂ = 0 → τ ∣ (a₁*b₃+a₃*b₁)` instantiated at
`B = Dbase`, `τ = tD`.

The *same* statement with `B = Polynomial Dbase` and `τ = Polynomial.C tD` is
FALSE; the witness is the pair of polynomials behind `fPoly_mul_gPoly`.  That is
precisely why Stage E must carry `hcanc` as a hypothesis instead of proving it
generically. -/
theorem hcanc_Dbase : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : Dbase,
    a₂ * b₃ + a₃ * b₂ + a₃ * b₃ = 0 → a₁ * b₃ + a₃ * b₁ + a₂ * b₂ = 0 →
    tD ∣ (a₁ * b₃ + a₃ * b₁) :=
  dvd_s_of_u_vanish

/-- The `hcanc` statement is **FALSE** at the polynomial base
`B = Polynomial Dbase`, `τ = Polynomial.C tD`.

The witness is exactly the coefficient tuple of `fPoly`/`gPoly` (D11):
`(a₁, a₂, a₃) = (0, 1, X)` and `(b₁, b₂, b₃) = (1 + X, X + X², X²)`.  Both
`u`-coordinates vanish (in characteristic 2), yet the `s`-coordinate is
`a₁b₃ + a₃b₁ = X + X²`, whose degree-1 coefficient is `1`, not a multiple of
`tD`.

This is recorded here as a proved guardrail, not as a mere comment: it is the
reason Stage E must take the cancellation as an explicit hypothesis, and the
reason Stage F may never transport `dvd_s_of_u_vanish` along the polynomial
equivalence. -/
theorem hcanc_polyDbase_false : ¬ (∀ a₁ a₂ a₃ b₁ b₂ b₃ : Polynomial Dbase,
    a₂ * b₃ + a₃ * b₂ + a₃ * b₃ = 0 → a₁ * b₃ + a₃ * b₁ + a₂ * b₂ = 0 →
    (Polynomial.C tD : Polynomial Dbase) ∣ (a₁ * b₃ + a₃ * b₁)) := by
  have h2 : (2 : Polynomial Dbase) = 0 := CharTwo.two_eq_zero
  intro h
  have hd := h 0 1 Polynomial.X (1 + Polynomial.X)
    (Polynomial.X + Polynomial.X ^ 2) (Polynomial.X ^ 2)
    (by ring_nf; rw [h2]; ring) (by ring_nf; rw [h2]; ring)
  rw [show (0 : Polynomial Dbase) * Polynomial.X ^ 2 + Polynomial.X * (1 + Polynomial.X)
        = Polynomial.X + Polynomial.X ^ 2 by ring,
    Polynomial.C_dvd_iff_dvd_coeff] at hd
  have h1 : (tD : Dbase) ∣ 1 := by
    simpa only [Polynomial.coeff_add, Polynomial.coeff_X_one, Polynomial.coeff_X_pow,
      if_neg (by decide : ¬((1 : ℕ) = 2)), add_zero] using hd 1
  exact (Polynomial.not_isUnit_X (R := F2)) (isUnit_of_dvd_one h1)

/-! ## C3 — the frozen `s_component_cancellation`

The two support lemmas below say that the `s`-line ideals are as small as they
look: because `J` annihilates `s` (`Alg.Wid_mul_Jid`), multiplying `s` by an
arbitrary element of `Alg B τ q` only ever sees that element's `Unitization.fst`
part, so `Ideal.span {w * s}` collapses to the `B`-submodule `B ∙ (w * s)`.

These are structural facts about `Alg B τ q` for an arbitrary base — they carry
no characteristic-2 content and are stated generically so that only C3 itself
stays tied to `Dbase`. -/

section Support

variable {B : Type} [CommRing B] {τ : B} {q : ℕ}

/-- Multiplying `algebraMap w * s` by an arbitrary `c` only sees `c.fst`:
the `J`-part of `c` is annihilated because `algebraMap w * s ∈ W`. -/
theorem algebraMap_mul_sElt_mul (w : B) (c : Alg B τ q) :
    algebraMap B (Alg B τ q) w * Alg.sElt B τ q * c
      = algebraMap B (Alg B τ q) (w * c.fst) * Alg.sElt B τ q := by
  refine Alg.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [Jmod.quo_smul_mk, mul_comm]

/-- The ideal generated by `algebraMap w * s` is the `B`-line through it. -/
theorem mem_span_algebraMap_mul_sElt_iff (w : B) {z : Alg B τ q} :
    z ∈ Ideal.span {algebraMap B (Alg B τ q) w * Alg.sElt B τ q}
      ↔ ∃ b : B, z = algebraMap B (Alg B τ q) (w * b) * Alg.sElt B τ q := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.fst, algebraMap_mul_sElt_mul w c⟩
  · rintro ⟨b, rfl⟩
    exact ⟨algebraMap B (Alg B τ q) b, by rw [map_mul]; ring⟩

/-- **C3 support.**  `Ideal.span {s} = B ∙ s`, in coordinates. -/
theorem mem_span_sElt_iff {z : Alg B τ q} :
    z ∈ Ideal.span {Alg.sElt B τ q}
      ↔ ∃ b : B, z = algebraMap B (Alg B τ q) b * Alg.sElt B τ q := by
  simpa using mem_span_algebraMap_mul_sElt_iff (B := B) (τ := τ) (q := q) 1 (z := z)

/-- **C3 support.**  `Ideal.span {t · s} = B ∙ (t · s) = τ · (B ∙ s)`. -/
theorem mem_span_t_sElt_iff {z : Alg B τ q} :
    z ∈ Ideal.span {Alg.tElt B τ q * Alg.sElt B τ q}
      ↔ ∃ b : B, z = algebraMap B (Alg B τ q) (τ * b) * Alg.sElt B τ q := by
  rw [Alg.tElt_def]
  exact mem_span_algebraMap_mul_sElt_iff τ

end Support

/-- **C3 (FROZEN `s_component_cancellation`).**  If `x, y ∈ J` and the product
`x * y` lies in the `s`-line `(D/t^q)s`, then it already lies in `t · (D/t^q)s`.

This is the critical obstruction of Step 2, and it is special to the base
`Dbase = 𝔽₂[t]`: the `x, y` are ARBITRARY elements of `J`, and the conclusion is
strictly stronger than the hypothesis (`sElt q ∉ Ideal.span {tElt q * sElt q}`).

Proof.  `Alg.mem_Jid_iff` gives `x.fst = y.fst = 0`, so by `Alg.γ₁_mul` /
`Alg.γ₂_mul` the vanishing of the two `u`-coordinates of `x * y` — which is what
`mem_span_sElt_iff` extracts from the hypothesis — is literally the pair of
hypotheses of `dvd_s_of_u_vanish` at `aᵢ = Alg.αᵢ x`, `bᵢ = Alg.αᵢ y`.  That
lemma yields `tD ∣ (α₁ x * α₃ y + α₃ x * α₁ y)`, and by `Alg.σ_mul` the latter
expression is exactly a lift of the `s`-coordinate of `x * y`; writing it as
`tD * c` and comparing on the `s`-line (`Alg.algebraMap_mul_sElt_eq_zero_iff`)
exhibits the required membership through `mem_span_t_sElt_iff`. -/
theorem s_component_cancellation_proof (q : ℕ) (x y : A q)
    (hx : x ∈ Jid Dbase tD q) (hy : y ∈ Jid Dbase tD q)
    (h : x * y ∈ Ideal.span {sElt q}) :
    x * y ∈ Ideal.span {tElt q * sElt q} := by
  have hx0 : x.fst = 0 := Alg.mem_Jid_iff.1 hx
  have hy0 : y.fst = 0 := Alg.mem_Jid_iff.1 hy
  obtain ⟨b, hb⟩ := mem_span_sElt_iff.1 h
  -- the `u₁`-coordinate of `x * y` vanishes
  have h₁ : Alg.α₂ x * Alg.α₃ y + Alg.α₃ x * Alg.α₂ y + Alg.α₃ x * Alg.α₃ y = 0 := by
    have h' : Alg.γ₁ (x * y) = 0 := by rw [hb]; simp
    rw [Alg.γ₁_mul, hx0, hy0] at h'
    linear_combination h'
  -- the `u₂`-coordinate of `x * y` vanishes
  have h₂ : Alg.α₁ x * Alg.α₃ y + Alg.α₃ x * Alg.α₁ y + Alg.α₂ x * Alg.α₂ y = 0 := by
    have h' : Alg.γ₂ (x * y) = 0 := by rw [hb]; simp
    rw [Alg.γ₂_mul, hx0, hy0] at h'
    linear_combination h'
  -- characteristic 2 over `𝔽₂[t]` forces an extra factor of `t` in the `s`-coordinate
  obtain ⟨c, hc⟩ := dvd_s_of_u_vanish (Alg.α₁ x) (Alg.α₂ x) (Alg.α₃ x)
    (Alg.α₁ y) (Alg.α₂ y) (Alg.α₃ y) h₁ h₂
  have hσ : (Ideal.Quotient.mk (Ideal.span {tD ^ q}) b : Quo Dbase tD q)
      = Ideal.Quotient.mk _ (tD * c) := by
    have hb' := congrArg Alg.σ hb
    rw [Alg.σ_mul, hx0, hy0, Alg.σ_algebraMap_mul_sElt] at hb'
    simp only [zero_smul, zero_add] at hb'
    rw [← hb', hc]
  refine mem_span_t_sElt_iff.2 ⟨c, ?_⟩
  rw [hb, ← sub_eq_zero, ← sub_mul, ← map_sub]
  exact (Alg.algebraMap_mul_sElt_eq_zero_iff _).2 (by rw [map_sub, hσ, sub_self])

end Prob30c
