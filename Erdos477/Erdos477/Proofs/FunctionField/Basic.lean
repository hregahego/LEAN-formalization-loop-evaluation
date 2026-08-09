import Erdos477.Defs

/-!
# Stage C — function-field exclusion, Route A (BM4-for-forms, Lemma 3.1, Cor 3.2, L2.1; SKETCH §5.2)

This file currently contains **step C0** of `BLUEPRINT.md` §"Stage C": the `ord_P`
calculus on `ℙ¹_k`, i.e. the support API on which every later part of Stage C
rests.  The chart convention is the one frozen in `Erdos477/Defs.lean`:
`some a ↔ [a : 1]`, `none ↔ [1 : 0]`, and `ord_∞ f = − f.intDegree`.  The
guardrail `example`s at the end of the file pin it down.

Nothing here uses `Erdos477.brownawell_masser_P1_four_term`; the axiom enters at
step C1 (`bm_forms_height_bound`), which is deliberately *not* in this file yet.
Route B (the Vandermonde argument of SKETCH §5.1) is forbidden in this file and
does not appear.

Support declarations go in `namespace Erdos477` and must never shadow a frozen
name from `Erdos477/Defs.lean` or `Erdos477/Theorems.lean`.
-/

namespace Erdos477

open scoped Classical

variable {k : Type*} [Field k]

/-! ## Unfolding lemmas for `ordP` -/

theorem ordP_none_eq (f : RatFunc k) : ordP (none : P1Point k) f = - f.intDegree := rfl

theorem ordP_some_eq (a : k) (f : RatFunc k) :
    ordP (some a) f = (Polynomial.rootMultiplicity a f.num : ℤ)
      - (Polynomial.rootMultiplicity a f.denom : ℤ) := rfl

/-- `ord_P` computed from *any* representation `f = p / q` (not necessarily the
normalized one), at a finite point. -/
theorem ordP_some_eq_of_eq_div {a : k} {f : RatFunc k} {p q : Polynomial k}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : f = algebraMap (Polynomial k) (RatFunc k) p / algebraMap (Polynomial k) (RatFunc k) q) :
    ordP (some a) f
      = (Polynomial.rootMultiplicity a p : ℤ) - (Polynomial.rootMultiplicity a q : ℤ) := by
  have hf : f ≠ 0 := by
    rw [h]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have key : f.num * q = p * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr h
  have h1 : Polynomial.rootMultiplicity a (f.num * q)
      = Polynomial.rootMultiplicity a f.num + Polynomial.rootMultiplicity a q :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero (RatFunc.num_ne_zero hf) hq)
  have h2 : Polynomial.rootMultiplicity a (p * f.denom)
      = Polynomial.rootMultiplicity a p + Polynomial.rootMultiplicity a f.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hp (RatFunc.denom_ne_zero f))
  rw [key, h2] at h1
  rw [ordP_some_eq]
  omega

/-- `ord_∞` computed from *any* representation `f = p / q`. -/
theorem ordP_none_eq_of_eq_div {f : RatFunc k} {p q : Polynomial k}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : f = algebraMap (Polynomial k) (RatFunc k) p / algebraMap (Polynomial k) (RatFunc k) q) :
    ordP (none : P1Point k) f = (q.natDegree : ℤ) - (p.natDegree : ℤ) := by
  rw [ordP_none_eq, h,
    RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  ring

/-! ## The multiplicative calculus -/

@[simp]
theorem ordP_one (P : P1Point k) : ordP P (1 : RatFunc k) = 0 := by
  cases P with
  | none => simp [ordP_none_eq]
  | some a =>
    rw [ordP_some_eq, RatFunc.num_one, RatFunc.denom_one, ← Polynomial.C_1,
      Polynomial.rootMultiplicity_C]
    simp

/-- `ord_P` of a constant is `0`.  (BLUEPRINT C0 lists this with a hypothesis
`a ≠ 0`; it is in fact unconditional, since `RatFunc.C 0 = 0` and `ordP P 0 = 0`.) -/
@[simp]
theorem ordP_C (P : P1Point k) (a : k) : ordP P (RatFunc.C a) = 0 := by
  cases P with
  | none => simp [ordP_none_eq]
  | some b =>
    rw [ordP_some_eq, RatFunc.num_C, RatFunc.denom_C, Polynomial.rootMultiplicity_C,
      ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    simp

theorem ordP_mul (P : P1Point k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordP P (f * g) = ordP P f + ordP P g := by
  have hrep : f * g = algebraMap (Polynomial k) (RatFunc k) (f.num * g.num)
      / algebraMap (Polynomial k) (RatFunc k) (f.denom * g.denom) := by
    rw [map_mul, map_mul, ← div_mul_div_comm, RatFunc.num_div_denom, RatFunc.num_div_denom]
  cases P with
  | none =>
    rw [ordP_none_eq, ordP_none_eq, ordP_none_eq, RatFunc.intDegree_mul hf hg]
    ring
  | some a =>
    rw [ordP_some_eq_of_eq_div
        (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
        (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)) hrep,
      Polynomial.rootMultiplicity_mul (mul_ne_zero (RatFunc.num_ne_zero hf)
        (RatFunc.num_ne_zero hg)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero (RatFunc.denom_ne_zero f)
        (RatFunc.denom_ne_zero g)),
      ordP_some_eq, ordP_some_eq]
    push_cast
    ring

theorem ordP_pow (P : P1Point k) {f : RatFunc k} (hf : f ≠ 0) (n : ℕ) :
    ordP P (f ^ n) = n * ordP P f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ordP_mul P (pow_ne_zero n hf) hf, ih]
    push_cast
    ring

/-- `ord_P` vanishes on constants.  (BLUEPRINT C0 lists this with the extra
hypothesis `f ≠ 0`; it is unconditional, cf. `ordP_C`.) -/
theorem ordP_eq_zero_of_const (P : P1Point k) {f : RatFunc k} (hf : IsConstRF f) :
    ordP P f = 0 := by
  obtain ⟨a, rfl⟩ := hf
  exact ordP_C P a

/-! ## The support of `ord_• f` -/

/-- A concrete finite superset of the zeros and poles of `f`, together with the
point at infinity. -/
noncomputable def suppFinset (f : RatFunc k) : Finset (P1Point k) :=
  insert none ((f.num.roots.toFinset ∪ f.denom.roots.toFinset).image some)

theorem ordP_ne_zero_mem_suppFinset (P : P1Point k) {f : RatFunc k} (hf : f ≠ 0)
    (h : ordP P f ≠ 0) : P ∈ suppFinset f := by
  cases P with
  | none => exact Finset.mem_insert_self _ _
  | some a =>
    rw [suppFinset, Finset.mem_insert]
    refine Or.inr (Finset.mem_image.mpr ⟨a, ?_, rfl⟩)
    rw [ordP_some_eq] at h
    have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
    have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
    rcases Nat.lt_or_ge 0 (Polynomial.rootMultiplicity a f.num) with hpos | hzero
    · exact Finset.mem_union_left _
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hnum).mpr
          ((Polynomial.rootMultiplicity_pos hnum).mp hpos)))
    · have hnum0 : Polynomial.rootMultiplicity a f.num = 0 := Nat.le_zero.mp hzero
      have hpos' : 0 < Polynomial.rootMultiplicity a f.denom := by omega
      exact Finset.mem_union_right _
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hden).mpr
          ((Polynomial.rootMultiplicity_pos hden).mp hpos')))

theorem card_suppFinset_le (f : RatFunc k) :
    (suppFinset f).card ≤ f.num.natDegree + f.denom.natDegree + 1 := by
  have h1 : (suppFinset f).card
      ≤ ((f.num.roots.toFinset ∪ f.denom.roots.toFinset).image some).card + 1 :=
    Finset.card_insert_le _ _
  have h2 : ((f.num.roots.toFinset ∪ f.denom.roots.toFinset).image some).card
      ≤ (f.num.roots.toFinset ∪ f.denom.roots.toFinset).card := Finset.card_image_le
  have h3 : (f.num.roots.toFinset ∪ f.denom.roots.toFinset).card
      ≤ f.num.roots.toFinset.card + f.denom.roots.toFinset.card := Finset.card_union_le _ _
  have h4 : f.num.roots.toFinset.card ≤ f.num.natDegree :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
  have h5 : f.denom.roots.toFinset.card ≤ f.denom.natDegree :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
  omega

theorem ordP_ne_zero_finite {f : RatFunc k} (hf : f ≠ 0) :
    {P : P1Point k | ordP P f ≠ 0}.Finite := by
  refine Set.Finite.subset (suppFinset f).finite_toSet ?_
  intro P hP
  exact ordP_ne_zero_mem_suppFinset P hf hP

/-! ## Heights -/

theorem minOrd_eq_zero_of_notMem {r : ℕ} {S : Finset (P1Point k)} {u : Fin r → RatFunc k}
    (hu : ∀ i, IsSUnitOn S (u i)) {P : P1Point k} (hP : P ∉ S) : minOrd u P = 0 := by
  rw [minOrd]
  split_ifs with h
  · obtain ⟨i, -⟩ := h
    refine le_antisymm ?_ ?_
    · exact (Finset.inf'_le _ (Finset.mem_univ i)).trans_eq ((hu i).2 P hP)
    · exact Finset.le_inf' _ _ fun j _ => ((hu j).2 P hP).ge
  · rfl

theorem projHeight_eq_sum_over_S {r : ℕ} {S : Finset (P1Point k)} {u : Fin r → RatFunc k}
    (hu : ∀ i, IsSUnitOn S (u i)) : projHeight u = - ∑ P ∈ S, minOrd u P := by
  have hsub : Function.support (minOrd u) ⊆ (S : Set (P1Point k)) := by
    intro P hP
    by_contra hPS
    exact hP (minOrd_eq_zero_of_notMem hu hPS)
  rw [projHeight, finsum_eq_finsetSum_of_support_subset _ hsub]

/-! ## The degree formula on `ℙ¹` -/

/-- Over an algebraically closed field the root multiplicities of a nonzero
polynomial, summed over any finite set containing its roots, give its degree. -/
theorem sum_rootMultiplicity_eq_natDegree [IsAlgClosed k] {p : Polynomial k} (hp : p ≠ 0)
    {R : Finset k} (hR : p.roots.toFinset ⊆ R) :
    ∑ a ∈ R, Polynomial.rootMultiplicity a p = p.natDegree := by
  have h1 : ∑ a ∈ R, Polynomial.rootMultiplicity a p
      = ∑ a ∈ p.roots.toFinset, Polynomial.rootMultiplicity a p := by
    refine (Finset.sum_subset hR ?_).symm
    intro a _ ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp] at ha
    exact Polynomial.rootMultiplicity_eq_zero ha
  rw [h1]
  simp_rw [← Polynomial.count_roots]
  rw [Multiset.toFinset_sum_count_eq]
  exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

/-- **The degree formula on `ℙ¹`.**  For a nonzero rational function the orders at
all points of `ℙ¹_k` sum to zero. -/
theorem sum_ordP_eq_zero [IsAlgClosed k] {f : RatFunc k} (hf : f ≠ 0) :
    ∑ᶠ P : P1Point k, ordP P f = 0 := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hsub : Function.support (fun P : P1Point k => ordP P f)
      ⊆ (suppFinset f : Set (P1Point k)) := fun P hP =>
    ordP_ne_zero_mem_suppFinset P hf hP
  rw [finsum_eq_finsetSum_of_support_subset _ hsub]
  set R : Finset k := f.num.roots.toFinset ∪ f.denom.roots.toFinset with hRdef
  have hnone : (none : P1Point k) ∉ R.image some := by
    simp
  rw [suppFinset, ← hRdef, Finset.sum_insert hnone,
    Finset.sum_image (fun x _ y _ h => Option.some_injective k h)]
  have hR1 : f.num.roots.toFinset ⊆ R := Finset.subset_union_left
  have hR2 : f.denom.roots.toFinset ⊆ R := Finset.subset_union_right
  have e1 : ∑ a ∈ R, (Polynomial.rootMultiplicity a f.num : ℤ) = (f.num.natDegree : ℤ) := by
    rw [← Nat.cast_sum, sum_rootMultiplicity_eq_natDegree hnum hR1]
  have e2 : ∑ a ∈ R, (Polynomial.rootMultiplicity a f.denom : ℤ) = (f.denom.natDegree : ℤ) := by
    rw [← Nat.cast_sum, sum_rootMultiplicity_eq_natDegree hden hR2]
  have e3 : ∑ a ∈ R, ordP (some a) f = (f.num.natDegree : ℤ) - (f.denom.natDegree : ℤ) := by
    simp only [ordP_some_eq]
    rw [Finset.sum_sub_distrib, e1, e2]
  rw [e3, ordP_none_eq, RatFunc.intDegree]
  ring

/-! ## Binary forms on `ℙ¹`

The two support lemmas of BLUEPRINT C1/C2 about projective zeros of binary forms:
a projective zero of a product is a projective zero of a factor, and a nonzero
form of degree `e` has at most `e` projective zeros.  Both use the *same* chart
convention as `ordP`. -/

theorem isProjZero_none_iff (Φ : MvPolynomial (Fin 2) k) :
    IsProjZero Φ (none : P1Point k) ↔ MvPolynomial.eval ![1, 0] Φ = 0 := Iff.rfl

theorem isProjZero_some_iff (Φ : MvPolynomial (Fin 2) k) (a : k) :
    IsProjZero Φ (some a) ↔ MvPolynomial.eval ![a, 1] Φ = 0 := Iff.rfl

theorem IsProjZero_prod {n : ℕ} {A : Fin n → MvPolynomial (Fin 2) k} {P : P1Point k}
    (h : IsProjZero (∏ i, A i) P) : ∃ i, IsProjZero (A i) P := by
  cases P with
  | none =>
    rw [isProjZero_none_iff, map_prod, Finset.prod_eq_zero_iff] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, (isProjZero_none_iff _).mpr hi⟩
  | some a =>
    rw [isProjZero_some_iff, map_prod, Finset.prod_eq_zero_iff] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, (isProjZero_some_iff _ _).mpr hi⟩

/-- Dehomogenization of a binary form: `Φ ↦ Φ(X, 1)`.  This is the affine chart
`some a ↔ [a : 1]` of the frozen convention. -/
noncomputable def dehom (Φ : MvPolynomial (Fin 2) k) : Polynomial k :=
  MvPolynomial.aeval ![Polynomial.X, 1] Φ

theorem eval_dehom (Φ : MvPolynomial (Fin 2) k) (a : k) :
    Polynomial.eval a (dehom Φ) = MvPolynomial.eval ![a, 1] Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp [dehom]
  | add p q hp hq =>
    simp only [dehom, map_add, Polynomial.eval_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [dehom, map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul,
      MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    congr 1
    fin_cases i <;> simp

theorem dehom_eq_sum (Φ : MvPolynomial (Fin 2) k) :
    dehom Φ = ∑ d ∈ Φ.support, Polynomial.C (MvPolynomial.coeff d Φ) * Polynomial.X ^ (d 0) := by
  rw [dehom, MvPolynomial.aeval_def, Polynomial.algebraMap_eq, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.prod_univ_two]
  simp

/-- On the support of a form of degree `e` the two exponents add up to `e`. -/
theorem add_eq_of_mem_support {Φ : MvPolynomial (Fin 2) k} {e : ℕ}
    (hΦ : Φ.IsHomogeneous e) {d : Fin 2 →₀ ℕ} (hd : d ∈ Φ.support) : d 0 + d 1 = e := by
  have h := hΦ.degree_eq_sum_deg_support hd
  rw [← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
  omega

/-- Hence the exponent of the first variable already determines the exponent vector. -/
theorem eq_of_mem_support_of_apply_zero_eq {Φ : MvPolynomial (Fin 2) k} {e : ℕ}
    (hΦ : Φ.IsHomogeneous e) {d d' : Fin 2 →₀ ℕ} (hd : d ∈ Φ.support) (hd' : d' ∈ Φ.support)
    (h : d 0 = d' 0) : d = d' := by
  have h1 := add_eq_of_mem_support hΦ hd
  have h2 := add_eq_of_mem_support hΦ hd'
  refine Finsupp.ext fun i => ?_
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact h
  · omega

theorem natDegree_dehom_le {Φ : MvPolynomial (Fin 2) k} {e : ℕ} (hΦ : Φ.IsHomogeneous e) :
    (dehom Φ).natDegree ≤ e := by
  rw [dehom_eq_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_pow_le.trans ?_)
  have := add_eq_of_mem_support hΦ hd
  simp only [Polynomial.natDegree_X, mul_one]
  omega

theorem coeff_dehom_of_mem_support {Φ : MvPolynomial (Fin 2) k} {e : ℕ}
    (hΦ : Φ.IsHomogeneous e) {d : Fin 2 →₀ ℕ} (hd : d ∈ Φ.support) :
    (dehom Φ).coeff (d 0) = MvPolynomial.coeff d Φ := by
  rw [dehom_eq_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single d]
  · simp
  · intro b hb hbd
    have hne : d 0 ≠ b 0 := fun h => hbd (eq_of_mem_support_of_apply_zero_eq hΦ hb hd h.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro h; exact absurd hd h

theorem dehom_ne_zero {Φ : MvPolynomial (Fin 2) k} {e : ℕ} (hΦ : Φ.IsHomogeneous e)
    (h0 : Φ ≠ 0) : dehom Φ ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero h0
  intro hcon
  apply hd
  rw [← coeff_dehom_of_mem_support hΦ (MvPolynomial.mem_support_iff.mpr hd), hcon,
    Polynomial.coeff_zero]

/-- If `[1 : 0]` is a projective zero of a degree-`e` form, the dehomogenization
loses a degree. -/
theorem coeff_dehom_top_eq_zero {Φ : MvPolynomial (Fin 2) k} {e : ℕ}
    (hΦ : Φ.IsHomogeneous e) (h : IsProjZero Φ (none : P1Point k)) : (dehom Φ).coeff e = 0 := by
  rw [isProjZero_none_iff] at h
  rw [dehom_eq_sum, Polynomial.finsetSum_coeff, ← h, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hsum := add_eq_of_mem_support hΦ hd
  rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
  · rw [h1, pow_zero, if_pos (by omega), mul_one]
  · rw [zero_pow (by omega), if_neg (by omega)]

theorem projZeroCount_le_of_isHomogeneous {Φ : MvPolynomial (Fin 2) k} {e : ℕ}
    (h0 : Φ ≠ 0) (hΦ : Φ.IsHomogeneous e) : projZeroCount Φ ≤ e := by
  have hφ0 : dehom Φ ≠ 0 := dehom_ne_zero hΦ h0
  have hdeg : (dehom Φ).natDegree ≤ e := natDegree_dehom_le hΦ
  have hroots : (dehom Φ).roots.toFinset.card ≤ (dehom Φ).natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  have hsome : ∀ a : k, IsProjZero Φ (some a) → a ∈ (dehom Φ).roots.toFinset := by
    intro a ha
    refine Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hφ0).mpr ?_)
    rw [Polynomial.IsRoot, eval_dehom]
    exact (isProjZero_some_iff Φ a).mp ha
  by_cases hnone : IsProjZero Φ (none : P1Point k)
  · have hlt : (dehom Φ).natDegree < e := by
      rcases hdeg.lt_or_eq with h | h
      · exact h
      · exact absurd (Polynomial.leadingCoeff_eq_zero.not.mpr hφ0)
          (not_not.mpr (by rw [Polynomial.leadingCoeff, h]; exact coeff_dehom_top_eq_zero hΦ hnone))
    have hsub : {P : P1Point k | IsProjZero Φ P}
        ⊆ ↑(insert (none : P1Point k) ((dehom Φ).roots.toFinset.image some)) := by
      rintro (_ | a) hP
      · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
      · exact Finset.mem_coe.mpr
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hsome a hP)))
    have h1 : projZeroCount Φ
        ≤ (insert (none : P1Point k) ((dehom Φ).roots.toFinset.image some)).card := by
      rw [projZeroCount, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    have h2 : (insert (none : P1Point k) ((dehom Φ).roots.toFinset.image some)).card
        ≤ ((dehom Φ).roots.toFinset.image some).card + 1 := Finset.card_insert_le _ _
    have h3 : ((dehom Φ).roots.toFinset.image some).card ≤ (dehom Φ).roots.toFinset.card :=
      Finset.card_image_le
    omega
  · have hsub : {P : P1Point k | IsProjZero Φ P}
        ⊆ ↑((dehom Φ).roots.toFinset.image some) := by
      rintro (_ | a) hP
      · exact absurd hP hnone
      · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (hsome a hP))
    have h1 : projZeroCount Φ ≤ ((dehom Φ).roots.toFinset.image some).card := by
      rw [projZeroCount, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    have h3 : ((dehom Φ).roots.toFinset.image some).card ≤ (dehom Φ).roots.toFinset.card :=
      Finset.card_image_le
    omega

/-! ## Guardrails pinning down the chart convention

`some a ↔ [a : 1]`, `none ↔ [1 : 0]`, `ord_∞ = −intDegree` (BLUEPRINT Stage C
cheat-watch box; PROGRESS decision (7)). -/

example : ordP (none : P1Point ℂ) (RatFunc.X : RatFunc ℂ) = -1 := by
  rw [ordP_none_eq, RatFunc.intDegree_X]

example : ordP (some (0 : ℂ)) (RatFunc.X : RatFunc ℂ) = 1 := by
  have h : Polynomial.rootMultiplicity (0 : ℂ) Polynomial.X = 1 := by
    simpa using Polynomial.rootMultiplicity_X_sub_C (x := (0 : ℂ)) (y := 0)
  rw [ordP_some_eq, RatFunc.num_X, RatFunc.denom_X, h, ← Polynomial.C_1,
    Polynomial.rootMultiplicity_C]
  simp

example : ordP (none : P1Point ℂ) (RatFunc.C 5) = 0 := ordP_C _ _

example : ordP (some (0 : ℂ)) (RatFunc.C 5) = 0 := ordP_C _ _

example :
    projZeroCount (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) = 2 := by
  have hset : {P : P1Point ℂ |
      IsProjZero (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) P}
      = {none, some 0} := by
    ext P
    cases P with
    | none => simp [isProjZero_none_iff]
    | some a => simp [isProjZero_some_iff]
  rw [projZeroCount, hset, Set.ncard_pair (by simp)]

end Erdos477
