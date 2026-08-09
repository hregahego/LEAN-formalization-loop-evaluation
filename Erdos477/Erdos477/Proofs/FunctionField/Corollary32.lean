import Erdos477.Proofs.FunctionField.Lemma31

/-!
# Stage C step C3 — Corollary 3.2 (`no_rational_param_of_not_mem_Bset`)

This file closes the frozen `Erdos477.no_rational_param_of_not_mem_Bset`
(`Erdos477/Theorems.lean:68-70`) by feeding the ✅ Lemma 3.1 of
`Erdos477/Proofs/FunctionField/Lemma31.lean` into the ✅ *conditional* Corollary
3.2 of `Erdos477/Proofs/FunctionField/BMForms.lean`:

* `Erdos477.no_rational_param_of_C2` is the frozen statement with its Lemma-3.1
  input replaced by an explicit hypothesis `hC2` of exactly that shape
  (BLUEPRINT §"Stage C" step C3 / SKETCH §5.2.3, homogenization included);
* `Erdos477.no_nonconstant_param_of_not_pow13_proof` is the frozen Lemma 3.1
  (BLUEPRINT step C2 / SKETCH §5.2.2), derived from
  `Erdos477.brownawell_masser_P1_four_term` through
  `Erdos477.bm_forms_height_bound_proof`;
* the two side conditions Lemma 3.1 needs at `N := -(c : ℚ)` are
  `Erdos477.neg_cast_ne_zero_of_not_mem_Bset` (`-(c:ℚ) ≠ 0`, from
  `zero_mem_Bset_proof`) and `Erdos477.not_exists_pow13_neg`
  (`¬ ∃ d : ℚ, d ^ 13 = -(c:ℚ)`, from `mem_Bset_of_rat_pow13_proof` and the
  oddness of `13`), both ✅ in `BMForms.lean`.

Nothing new is proved here; Route B (SKETCH §5.1, the Vandermonde argument) and
`Polynomial.abc` are forbidden on this path and do not appear.
-/

namespace Erdos477

/-- **Paper Corollary 3.2** (BLUEPRINT Stage C, step C3; SKETCH §5.2.3).
For `c ∉ Bset` the affine surface `u¹³ − v¹³ − t¹³ = −c` carries no nonconstant
rational parametrization over `ℚ`.

Type-identical to the frozen `Erdos477.no_rational_param_of_not_mem_Bset`. -/
theorem no_rational_param_of_not_mem_Bset_proof (c : ℤ) (hc : c ∉ Bset)
    (f g h : RatFunc ℚ) (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h :=
  no_rational_param_of_C2 c hc
    (fun e A hA => no_nonconstant_param_of_not_pow13_proof _
      (neg_cast_ne_zero_of_not_mem_Bset c hc) (not_exists_pow13_neg c hc) e A hA)
    f g h hfgh

end Erdos477
