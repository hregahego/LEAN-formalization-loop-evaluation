import Erdos477.Proofs.FunctionField.Corollary32
import Erdos477.Proofs.Elementary.Basic

/-!
# Stage C step C4 — L2.1 (`no_linear_param`)

This file closes the frozen `Erdos477.no_linear_param`
(`Erdos477/Theorems.lean:74-77`), the exclusion hypothesis that Heath-Brown's
count needs, following BLUEPRINT §"Stage C" paragraph **C4** and SKETCH §5.2.3
("derivation of L2.1").

The route is **Route A** throughout: the three integer polynomials are pushed
into `RatFunc ℚ` and Corollary 3.2
(`Erdos477.no_rational_param_of_not_mem_Bset_proof`, Stage C step C3) is applied
to them.  Concretely, with

```
    q i  := Polynomial.map (Int.castRingHom ℚ) (p i)  ,
    p̄ i  := algebraMap (Polynomial ℚ) (RatFunc ℚ) (q i)  ,
    f := p̄₁ ,  g := -p̄₂ ,  h := -p̄₃ ,
```

oddness of `13` (`Erdos477.odd_thirteen`) turns `f¹³ − g¹³ − h¹³` into
`p̄₁¹³ + p̄₂¹³ + p̄₃¹³`, which is the image of the hypothesis `hsum` under two ring
maps and hence equals `RatFunc.C (-(c : ℚ))`.  Corollary 3.2 makes all three
constant; injectivity of `algebraMap (Polynomial ℚ) (RatFunc ℚ)` pulls that back
to `q i = Polynomial.C a`, so `(q i).natDegree = 0`, and `natDegree` is preserved
by the injective `Int.castRingHom ℚ`.

The binders `h₁ h₂ h₃` of the frozen statement are **not needed** by this route —
Route A proves the stronger statement without any degree restriction — but they
must stay in the signature or the `rfl` gate against the frozen type fails, so
the main declaration carries a scoped `set_option linter.unusedVariables false`.

Route B (SKETCH §5.1, the elementary Vandermonde proof of L2.1) is FORBIDDEN
here: it would let `no_linear_param` compile without ever touching
`Erdos477.brownawell_masser_P1_four_term`, and `scripts/verify.py` check 4b would
fail the run.  `Polynomial.abc` (Mathlib's Mason–Stothers) is likewise forbidden.
Neither appears below.
-/

namespace Erdos477

/-- A rational function that is constant after negation is constant. -/
theorem isConstRF_of_neg {K : Type*} [Field K] {f : RatFunc K} (hf : IsConstRF (-f)) :
    IsConstRF f := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨-a, ?_⟩
  rw [map_neg, ← ha, neg_neg]

/-- If the image of an integer polynomial in `RatFunc ℚ` is constant, the
polynomial has degree `0`. -/
theorem natDegree_eq_zero_of_isConstRF {p : Polynomial ℤ}
    (hp : IsConstRF (algebraMap (Polynomial ℚ) (RatFunc ℚ)
      (p.map (Int.castRingHom ℚ)))) : p.natDegree = 0 := by
  obtain ⟨a, ha⟩ := hp
  rw [← RatFunc.algebraMap_C] at ha
  have hq : p.map (Int.castRingHom ℚ) = Polynomial.C a := RatFunc.algebraMap_injective ℚ ha
  have hinj : Function.Injective (Int.castRingHom ℚ) := fun x y hxy => by
    simpa [Int.coe_castRingHom] using hxy
  have := Polynomial.natDegree_map_eq_of_injective hinj p
  rw [hq, Polynomial.natDegree_C] at this
  exact this.symm

set_option linter.unusedVariables false in
/-- **L2.1** (BLUEPRINT Stage C, step C4; SKETCH §5.2.3): for `c ∉ Bset` there is
no genuinely linear solution of `p₁¹³ + p₂¹³ + p₃¹³ = C (−c)` in `ℤ[X]`.

Type-identical to the frozen `Erdos477.no_linear_param`.  The degree hypotheses
`h₁ h₂ h₃` are part of the frozen signature and are deliberately unused: Route A
excludes *every* nonconstant polynomial solution, not just the linear ones. -/
theorem no_linear_param_proof (c : ℤ) (hc : c ∉ Bset) (p₁ p₂ p₃ : Polynomial ℤ)
    (hsum : p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c))
    (h₁ : p₁.natDegree ≤ 1) (h₂ : p₂.natDegree ≤ 1) (h₃ : p₃.natDegree ≤ 1) :
    p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := by
  -- Push the identity into `ℚ[X]` ...
  have hq : (p₁.map (Int.castRingHom ℚ)) ^ 13 + (p₂.map (Int.castRingHom ℚ)) ^ 13
      + (p₃.map (Int.castRingHom ℚ)) ^ 13 = Polynomial.C (-(c : ℚ)) := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) hsum
    simpa [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C] using h
  -- ... and then into `RatFunc ℚ`.
  have hrf : (algebraMap (Polynomial ℚ) (RatFunc ℚ) (p₁.map (Int.castRingHom ℚ))) ^ 13
      + (algebraMap (Polynomial ℚ) (RatFunc ℚ) (p₂.map (Int.castRingHom ℚ))) ^ 13
      + (algebraMap (Polynomial ℚ) (RatFunc ℚ) (p₃.map (Int.castRingHom ℚ))) ^ 13
      = RatFunc.C (-(c : ℚ)) := by
    have h := congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) hq
    simpa [map_add, map_pow, RatFunc.algebraMap_C] using h
  -- The substitution `X := f`, `Y := -g`, `Z := -h` of SKETCH §5.2.3.
  have hfgh : (algebraMap (Polynomial ℚ) (RatFunc ℚ) (p₁.map (Int.castRingHom ℚ))) ^ 13
      - (-(algebraMap (Polynomial ℚ) (RatFunc ℚ) (p₂.map (Int.castRingHom ℚ)))) ^ 13
      - (-(algebraMap (Polynomial ℚ) (RatFunc ℚ) (p₃.map (Int.castRingHom ℚ)))) ^ 13
      = RatFunc.C (-(c : ℚ)) := by
    rw [Odd.neg_pow odd_thirteen, Odd.neg_pow odd_thirteen, sub_neg_eq_add, sub_neg_eq_add]
    exact hrf
  obtain ⟨hf, hg, hh⟩ := no_rational_param_of_not_mem_Bset_proof c hc _ _ _ hfgh
  exact ⟨natDegree_eq_zero_of_isConstRF hf,
    natDegree_eq_zero_of_isConstRF (isConstRF_of_neg hg),
    natDegree_eq_zero_of_isConstRF (isConstRF_of_neg hh)⟩

end Erdos477
