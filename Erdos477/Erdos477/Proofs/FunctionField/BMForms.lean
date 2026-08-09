import Erdos477.Proofs.FunctionField.Basic
import Erdos477.Proofs.Elementary.Basic

/-!
# Stage C step C1 — Brownawell–Masser for binary forms (`bm_forms_height_bound`)

This file **derives** `Erdos477.bm_forms_height_bound_proof` from the assumed
certificate `Erdos477.brownawell_masser_P1_four_term` (`Erdos477/Defs.lean`),
following BLUEPRINT §"Stage C" step C1 and SKETCH §5.2.1.

The route: dehomogenize each form `A i` in the affine chart `some a ↔ [a : 1]`
of the frozen convention (`Erdos477.dehom`), pass to the family of *ratios*
`u i := â i / â j` in `RatFunc k`, take `S` to be the (finite) set of projective
zeros of `∏ i, A i`, and compute `projHeight u = d`.

The choice of the family `u` deserves a comment, since it deviates slightly from
the route sketched in `TASKS.md` (which suggested `u i := â i / X ^ d`).  BM
requires each `u i` to be an `S`-unit for `S = ` the projective zeros of the
product, and neither `â i` nor `â i / X ^ d` has that property: the first has a
pole of order `d` at `none` even when `none ∉ S`, the second a pole of order `d`
at `some 0` even when `some 0 ∉ S`.  The *ratios* `â i / â j` do have it, because
at a point off `S` no `A i` vanishes, so numerator and denominator have the same
order there (`0` at a finite point, `-d` at `none`).  Since the projective height
is unchanged by multiplying the whole family by a fixed nonzero rational function
(the degree formula `sum_ordP_eq_zero` makes the correction telescope to `0`),
the computation `projHeight u = d` of SKETCH §5.2.1 is unaffected.

Route B (the Vandermonde argument of SKETCH §5.1) is forbidden here and does not
appear, and `Polynomial.abc` is not used.  No new `axiom` is declared: the only
certificate consumed is `Erdos477.brownawell_masser_P1_four_term`.
-/

namespace Erdos477

open scoped Classical

section Support

variable {k : Type*} [Field k]

/-! ## Dehomogenization is a ring map, and is injective on forms of a fixed degree -/

theorem dehom_zero : dehom (0 : MvPolynomial (Fin 2) k) = 0 := by
  simp [dehom]

theorem dehom_mul (Φ Ψ : MvPolynomial (Fin 2) k) : dehom (Φ * Ψ) = dehom Φ * dehom Ψ := by
  simp [dehom]

theorem dehom_C (a : k) : dehom (MvPolynomial.C a : MvPolynomial (Fin 2) k) = Polynomial.C a := by
  simp [dehom]

theorem dehom_sum {ι : Type*} (s : Finset ι) (Φ : ι → MvPolynomial (Fin 2) k) :
    dehom (∑ i ∈ s, Φ i) = ∑ i ∈ s, dehom (Φ i) := by
  simp [dehom]

/-- Two exponent vectors in two variables agree as soon as both coordinates do. -/
theorem finsupp_fin_two_ext {b m : Fin 2 →₀ ℕ} (h0 : b 0 = m 0) (h1 : b 1 = m 1) : b = m := by
  refine Finsupp.ext fun i => ?_
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact h0
  · exact h1

theorem degree_fin_two (m : Fin 2 →₀ ℕ) : m.degree = m 0 + m 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- The top coefficient of the dehomogenization of a degree-`e` form is its value at `[1 : 0]`.
(Generalizes `coeff_dehom_top_eq_zero`.) -/
theorem coeff_dehom_top {Φ : MvPolynomial (Fin 2) k} {e : ℕ} (hΦ : Φ.IsHomogeneous e) :
    (dehom Φ).coeff e = MvPolynomial.eval ![1, 0] Φ := by
  rw [dehom_eq_sum, Polynomial.finsetSum_coeff, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hsum := add_eq_of_mem_support hΦ hd
  rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
  · rw [h1, pow_zero, if_pos (by omega), mul_one]
  · rw [zero_pow (by omega), if_neg (by omega)]

/-- Unconditional version of `coeff_dehom_of_mem_support`. -/
theorem coeff_dehom_eq {Φ : MvPolynomial (Fin 2) k} {e : ℕ} (hΦ : Φ.IsHomogeneous e)
    {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 = e) :
    (dehom Φ).coeff (m 0) = MvPolynomial.coeff m Φ := by
  by_cases h : m ∈ Φ.support
  · exact coeff_dehom_of_mem_support hΦ h
  · rw [MvPolynomial.notMem_support_iff.mp h, dehom_eq_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb2 := add_eq_of_mem_support hΦ hb
    have hne : b 0 ≠ m 0 := by
      intro hh
      exact h (finsupp_fin_two_ext hh (by omega) ▸ hb)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hne]

/-- Dehomogenization is injective on binary forms of a *fixed* degree. -/
theorem dehom_injective_of_isHomogeneous {Φ Ψ : MvPolynomial (Fin 2) k} {e : ℕ}
    (hΦ : Φ.IsHomogeneous e) (hΨ : Ψ.IsHomogeneous e) (h : dehom Φ = dehom Ψ) : Φ = Ψ := by
  refine MvPolynomial.ext _ _ fun m => ?_
  by_cases hm : m 0 + m 1 = e
  · rw [← coeff_dehom_eq hΦ hm, ← coeff_dehom_eq hΨ hm, h]
  · have hdeg : m.degree ≠ e := by rw [degree_fin_two]; exact hm
    rw [hΦ.coeff_eq_zero hdeg, hΨ.coeff_eq_zero hdeg]

/-! ## `ordP` of a polynomial and of a quotient -/

theorem ordP_div (P : P1Point k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordP P (f / g) = ordP P f - ordP P g := by
  have h := ordP_mul P (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ _ hg] at h
  omega

theorem ordP_some_algebraMap {p : Polynomial k} (hp : p ≠ 0) (α : k) :
    ordP (some α) (algebraMap (Polynomial k) (RatFunc k) p)
      = (Polynomial.rootMultiplicity α p : ℤ) := by
  rw [ordP_some_eq_of_eq_div hp (one_ne_zero) (by simp), ← Polynomial.C_1,
    Polynomial.rootMultiplicity_C]
  simp

theorem ordP_none_algebraMap (p : Polynomial k) :
    ordP (none : P1Point k) (algebraMap (Polynomial k) (RatFunc k) p)
      = -(p.natDegree : ℤ) := by
  rw [ordP_none_eq, RatFunc.intDegree_polynomial]

/-! ## Projective zeros -/

/-- Converse of `IsProjZero_prod`. -/
theorem isProjZero_prod_of {n : ℕ} {A : Fin n → MvPolynomial (Fin 2) k} {P : P1Point k}
    (i : Fin n) (h : IsProjZero (A i) P) : IsProjZero (∏ j, A j) P := by
  cases P with
  | none =>
    rw [isProjZero_none_iff, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  | some a =>
    rw [isProjZero_some_iff, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h

/-- A nonzero binary form has finitely many projective zeros. -/
theorem isProjZero_finite {Φ : MvPolynomial (Fin 2) k} {e : ℕ} (h0 : Φ ≠ 0)
    (hΦ : Φ.IsHomogeneous e) : {P : P1Point k | IsProjZero Φ P}.Finite := by
  have hφ0 : dehom Φ ≠ 0 := dehom_ne_zero hΦ h0
  refine Set.Finite.subset
    (insert (none : P1Point k) ((dehom Φ).roots.toFinset.image some)).finite_toSet ?_
  rintro (_ | a) hP
  · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
  · refine Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_))
    refine Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hφ0).mpr ?_)
    rw [Polynomial.IsRoot, eval_dehom]
    exact (isProjZero_some_iff Φ a).mp hP

/-! ## `minOrd` -/

theorem minOrd_eq_inf' {r : ℕ} {u : Fin r → RatFunc k} (P : P1Point k)
    (h : (Finset.univ : Finset (Fin r)).Nonempty) :
    minOrd u P = Finset.univ.inf' h (fun i => ordP P (u i)) := by
  rw [minOrd]
  split_ifs
  rfl

end Support

/-! ## C1 — the derivation -/

/-- **BLUEPRINT Stage C, step C1.**  Brownawell–Masser for homogeneous binary forms,
derived from `Erdos477.brownawell_masser_P1_four_term`.  Type character-identical to
the frozen `Erdos477.bm_forms_height_bound` (`Erdos477/Theorems.lean:52-58`). -/
theorem bm_forms_height_bound_proof {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (r d : ℕ) (hr : 3 ≤ r) (A : Fin r → MvPolynomial (Fin 2) k)
    (hA0 : ∀ i, A i ≠ 0) (hhom : ∀ i, (A i).IsHomogeneous d)
    (hcop : NoCommonProjZero A) (hsum : ∑ i, A i = 0)
    (hsub : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, A i ≠ 0)
    (hnc : ¬ IsConstantFamily A) :
    (d : ℤ) ≤ (Nat.choose (r - 1) 2 : ℤ) * ((projZeroCount (∏ i, A i) : ℤ) - 2) := by
  classical
  have hr0 : 0 < r := by omega
  have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hr0⟩⟩
  obtain ⟨j⟩ : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  -- the dehomogenized family and the family of ratios
  obtain ⟨a, ha⟩ : ∃ a : Fin r → Polynomial k, ∀ i, a i = dehom (A i) := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w : Fin r → RatFunc k,
      ∀ i, w i = algebraMap (Polynomial k) (RatFunc k) (a i) := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hud⟩ : ∃ u : Fin r → RatFunc k, ∀ i, u i = w i / w j := ⟨_, fun _ => rfl⟩
  have ha0 : ∀ i, a i ≠ 0 := fun i => (ha i) ▸ dehom_ne_zero (hhom i) (hA0 i)
  have hw0 : ∀ i, w i ≠ 0 := fun i => (hwd i) ▸ RatFunc.algebraMap_ne_zero (ha0 i)
  have hu0 : ∀ i, u i ≠ 0 := fun i => (hud i) ▸ div_ne_zero (hw0 i) (hw0 j)
  -- partial sums of the forms are homogeneous of degree `d`
  have hhomsum : ∀ J : Finset (Fin r), (∑ i ∈ J, A i).IsHomogeneous d := by
    intro J
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      (MvPolynomial.mem_homogeneousSubmodule d (A i)).mpr (hhom i)
  -- (i) the additive hypotheses transfer
  have hsum_a : ∑ i, a i = 0 := by
    simp only [ha, ← dehom_sum, hsum, dehom_zero]
  have hsub_a : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, a i ≠ 0 := by
    intro J h1 h2
    simp only [ha, ← dehom_sum]
    exact dehom_ne_zero (hhomsum J) (hsub J h1 h2)
  have hsum_u : ∑ i, u i = 0 := by
    have h1 : ∑ i, u i = (∑ i, w i) / w j := by
      simp only [hud, Finset.sum_div]
    have h2 : ∑ i, w i = 0 := by
      simp only [hwd, ← map_sum, hsum_a, map_zero]
    rw [h1, h2, zero_div]
  have hsub_u : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, u i ≠ 0 := by
    intro J h1 h2
    have he : ∑ i ∈ J, u i
        = (algebraMap (Polynomial k) (RatFunc k) (∑ i ∈ J, a i)) / w j := by
      simp only [hud, hwd, Finset.sum_div, map_sum]
    rw [he]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero (hsub_a J h1 h2)) (hw0 j)
  -- (ii) `NoCommonProjZero` in the two charts
  have hinf : ∃ i, MvPolynomial.eval ![1, 0] (A i) ≠ 0 := by
    by_contra hcon
    have hall : ∀ i, MvPolynomial.eval ![1, 0] (A i) = 0 := fun i =>
      not_not.mp fun hi => hcon ⟨i, hi⟩
    have h := congrFun (hcop ![1, 0] hall) 0
    simp at h
  have hfin_nz : ∀ α : k, ∃ i, MvPolynomial.eval ![α, 1] (A i) ≠ 0 := by
    intro α
    by_contra hcon
    have hall : ∀ i, MvPolynomial.eval ![α, 1] (A i) = 0 := fun i =>
      not_not.mp fun hi => hcon ⟨i, hi⟩
    have h := congrFun (hcop ![α, 1] hall) 1
    simp at h
  -- (iii) orders of the `w i`
  have hordw_some : ∀ (i : Fin r) (α : k),
      ordP (some α) (w i) = (Polynomial.rootMultiplicity α (a i) : ℤ) := by
    intro i α
    rw [hwd i, ordP_some_algebraMap (ha0 i)]
  have hordw_none : ∀ i, ordP (none : P1Point k) (w i) = -((a i).natDegree : ℤ) := by
    intro i
    rw [hwd i, ordP_none_algebraMap]
  have hdeg_le : ∀ i, (a i).natDegree ≤ d := fun i => (ha i) ▸ natDegree_dehom_le (hhom i)
  have hdeg_top : ∀ i, MvPolynomial.eval ![1, 0] (A i) ≠ 0 → (a i).natDegree = d := by
    intro i hi
    refine le_antisymm (hdeg_le i) (Polynomial.le_natDegree_of_ne_zero ?_)
    rw [ha i, coeff_dehom_top (hhom i)]
    exact hi
  have hrm_zero : ∀ (α : k) (i : Fin r), MvPolynomial.eval ![α, 1] (A i) ≠ 0 →
      Polynomial.rootMultiplicity α (a i) = 0 := by
    intro α i hi
    refine Polynomial.rootMultiplicity_eq_zero ?_
    rw [Polynomial.IsRoot, ha i, eval_dehom]
    exact hi
  -- (iv) the finite set `S` of projective zeros of the product
  have hZfin : {P : P1Point k | IsProjZero (∏ i, A i) P}.Finite := by
    refine Set.Finite.subset
      (Set.finite_iUnion (fun i : Fin r => isProjZero_finite (hA0 i) (hhom i))) ?_
    intro P hP
    obtain ⟨i, hi⟩ := IsProjZero_prod hP
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨S, hSmem⟩ : ∃ S : Finset (P1Point k),
      ∀ P, P ∈ S ↔ IsProjZero (∏ i, A i) P :=
    ⟨hZfin.toFinset, fun P => hZfin.mem_toFinset⟩
  have hScard : (S.card : ℤ) = (projZeroCount (∏ i, A i) : ℤ) := by
    have hcoe : (S : Set (P1Point k)) = {P : P1Point k | IsProjZero (∏ i, A i) P} := by
      ext P
      simpa using hSmem P
    rw [projZeroCount, ← hcoe, Set.ncard_coe_finset]
  -- (v) each `u i` is an `S`-unit
  have hunit : ∀ i, IsSUnitOn S (u i) := by
    intro i
    refine ⟨hu0 i, ?_⟩
    intro P hP
    have hPz : ¬ IsProjZero (∏ i, A i) P := fun h => hP ((hSmem P).mpr h)
    rw [hud i, ordP_div P (hw0 i) (hw0 j)]
    cases P with
    | none =>
      have h1 : ∀ t : Fin r, (a t).natDegree = d := by
        intro t
        refine hdeg_top t fun hzero => hPz ?_
        exact isProjZero_prod_of t ((isProjZero_none_iff (A t)).mpr hzero)
      rw [hordw_none i, hordw_none j, h1 i, h1 j, sub_self]
    | some α =>
      have h1 : ∀ t : Fin r, Polynomial.rootMultiplicity α (a t) = 0 := by
        intro t
        refine hrm_zero α t fun hzero => hPz ?_
        exact isProjZero_prod_of t ((isProjZero_some_iff (A t) α).mpr hzero)
      rw [hordw_some i α, hordw_some j α, h1 i, h1 j, sub_self]
  -- (vi) the family is not all constant
  have hnonconst : ¬ ∀ i, IsConstRF (u i) := by
    intro hall
    refine hnc ?_
    choose c hc using hall
    refine ⟨c, A j, fun i => ?_⟩
    have h1 : w i = RatFunc.C (c i) * w j := by
      rw [← hc i, hud i, div_mul_cancel₀ _ (hw0 j)]
    have h2 : algebraMap (Polynomial k) (RatFunc k) (a i)
        = algebraMap (Polynomial k) (RatFunc k) (Polynomial.C (c i) * a j) := by
      rw [← hwd i, h1, hwd j, map_mul, RatFunc.algebraMap_C]
    have h3 : a i = Polynomial.C (c i) * a j := RatFunc.algebraMap_injective k h2
    refine dehom_injective_of_isHomogeneous (hhom i) ?_ ?_
    · simpa using (MvPolynomial.isHomogeneous_C (Fin 2) (c i)).mul (hhom j)
    · rw [← ha i, h3, dehom_mul, dehom_C, ha j]
  -- (vii) the height computation, SKETCH §5.2.1
  have hminOrd : ∀ P : P1Point k, minOrd u P = minOrd w P - ordP P (w j) := by
    intro P
    rw [minOrd_eq_inf' P hne, minOrd_eq_inf' P hne]
    have hval : ∀ i, ordP P (u i) = ordP P (w i) - ordP P (w j) := by
      intro i
      rw [hud i, ordP_div P (hw0 i) (hw0 j)]
    refine le_antisymm ?_ ?_
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' hne (fun i => ordP P (w i))
      rw [hi0, ← hval i0]
      exact Finset.inf'_le _ (Finset.mem_univ i0)
    · refine Finset.le_inf' _ _ fun i _ => ?_
      rw [hval i]
      exact sub_le_sub_right (Finset.inf'_le _ (Finset.mem_univ i)) _
  have hminw_some : ∀ α : k, minOrd w (some α) = 0 := by
    intro α
    rw [minOrd_eq_inf' _ hne]
    obtain ⟨i0, hi0⟩ := hfin_nz α
    refine le_antisymm ?_ ?_
    · refine le_trans (Finset.inf'_le _ (Finset.mem_univ i0)) ?_
      rw [hordw_some i0 α, hrm_zero α i0 hi0]
      simp
    · refine Finset.le_inf' _ _ fun i _ => ?_
      rw [hordw_some i α]
      exact Int.natCast_nonneg _
  have hminw_none : minOrd w (none : P1Point k) = -(d : ℤ) := by
    rw [minOrd_eq_inf' _ hne]
    obtain ⟨i0, hi0⟩ := hinf
    refine le_antisymm ?_ ?_
    · refine le_trans (Finset.inf'_le _ (Finset.mem_univ i0)) ?_
      rw [hordw_none i0, hdeg_top i0 hi0]
    · refine Finset.le_inf' _ _ fun i _ => ?_
      rw [hordw_none i]
      exact neg_le_neg (by exact_mod_cast hdeg_le i)
  have hsupp_w : ∀ P : P1Point k, P ≠ none → minOrd w P = 0 := by
    rintro (_ | α) h
    · exact absurd rfl h
    · exact hminw_some α
  have hheight : projHeight u = (d : ℤ) := by
    have hsupp1 : (Function.support (fun P : P1Point k => minOrd w P)).Finite := by
      refine Set.Finite.subset (Set.finite_singleton (none : P1Point k)) ?_
      intro P hP
      by_contra hcon
      exact hP (hsupp_w P (by simpa using hcon))
    have hsupp2 : (Function.support (fun P : P1Point k => ordP P (w j))).Finite :=
      ordP_ne_zero_finite (hw0 j)
    have hfinsum_w : ∑ᶠ P : P1Point k, minOrd w P = -(d : ℤ) := by
      rw [finsum_eq_single (fun P : P1Point k => minOrd w P) none fun P hP => hsupp_w P hP]
      exact hminw_none
    have hfinsum_wj : ∑ᶠ P : P1Point k, ordP P (w j) = 0 := sum_ordP_eq_zero (hw0 j)
    have hsplit : ∑ᶠ P : P1Point k, minOrd u P
        = (∑ᶠ P : P1Point k, minOrd w P) - ∑ᶠ P : P1Point k, ordP P (w j) := by
      simp only [hminOrd]
      exact finsum_sub_distrib hsupp1 hsupp2
    rw [projHeight, hsplit, hfinsum_w, hfinsum_wj]
    ring
  -- (viii) apply the assumed certificate
  have hbm := brownawell_masser_P1_four_term S r hr u hunit hnonconst hsum_u hsub_u
  rw [hheight, hScard] at hbm
  exact hbm


/-! ## Stage C step C3 — the homogenization bridge (Corollary 3.2, conditional form)

The rest of this file implements BLUEPRINT §"Stage C" step C3 / SKETCH §5.2.3 in
*conditional* form: everything except the C2 input
(`no_nonconstant_param_of_not_pow13`), which is not available yet and which is
therefore taken as the hypothesis `hC2` of `no_rational_param_of_C2` below.

The route is SKETCH §5.2.3 verbatim.  Given `f, g, h : RatFunc ℚ` with
`f¹³ − g¹³ − h¹³ = C(−c)`, the substitution `X := f`, `Y := −g`, `Z := −h`
(13 is odd) turns the equation into `X¹³ + Y¹³ + Z¹³ = C(−c)`.  Putting the three
over a common denominator and dividing out a common factor gives four polynomials
`F₁, G₁, H₁, R₁` with `R₁ ≠ 0`, a Bézout identity `F₁a + G₁b + H₁u + R₁w = 1`, and
`F₁¹³ + G₁¹³ + H₁¹³ = C(−c) · R₁¹³`.  Homogenizing all four to the common degree
`e := max` of their degrees produces `IsParamOfXN (−c) e A`: the Bézout identity
rules out a common zero in the chart `some α ↔ [α : 1]`, and the maximality of `e`
rules one out at `none ↔ [1 : 0]`, where the value of a form is the degree-`e`
coefficient of its dehomogenization (`coeff_dehom_top`).

Route B (SKETCH §5.1) and `Polynomial.abc` do not appear here either.
-/

theorem neg_cast_ne_zero_of_not_mem_Bset (c : ℤ) (hc : c ∉ Bset) : -(c : ℚ) ≠ 0 := by
  intro h
  have hc0 : c = 0 := by exact_mod_cast neg_eq_zero.mp h
  exact hc (hc0 ▸ zero_mem_Bset_proof)

theorem not_exists_pow13_neg (c : ℤ) (hc : c ∉ Bset) : ¬ ∃ d : ℚ, d ^ 13 = -(c : ℚ) := by
  rintro ⟨d, hd⟩
  refine hc (mem_Bset_of_rat_pow13_proof c (-d) ?_)
  rw [Odd.neg_pow odd_thirteen, hd, neg_neg]

/-! ### Homogenization of a polynomial to a binary form of a prescribed degree -/

section Homog

variable {K : Type*} [Field K]

/-- `homog e p` is the degree-`e` homogenization `X₁^e · p (X₀ / X₁)` of `p`, written
without division.  It is a section of `Erdos477.dehom` on polynomials of degree `≤ e`
(`dehom_homog`), so it uses the frozen chart convention `some a ↔ [a : 1]`. -/
noncomputable def homog (e : ℕ) (p : Polynomial K) : MvPolynomial (Fin 2) K :=
  ∑ i ∈ Finset.range (e + 1),
    MvPolynomial.C (p.coeff i) * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (e - i)

theorem homog_isHomogeneous (e : ℕ) (p : Polynomial K) : (homog e p).IsHomogeneous e := by
  rw [homog, ← MvPolynomial.mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have hie : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : ((MvPolynomial.C (p.coeff i) : MvPolynomial (Fin 2) K) *
      MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (e - i)).IsHomogeneous (0 + 1 * i + 1 * (e - i)) :=
    ((MvPolynomial.isHomogeneous_C _ _).mul
      ((MvPolynomial.isHomogeneous_X _ _).pow _)).mul ((MvPolynomial.isHomogeneous_X _ _).pow _)
  have h2 : 0 + 1 * i + 1 * (e - i) = e := by omega
  rwa [h2] at h1

theorem dehom_homog {e : ℕ} {p : Polynomial K} (hp : p.natDegree ≤ e) :
    dehom (homog e p) = p := by
  rw [homog, dehom]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one,
    Polynomial.algebraMap_eq]
  refine Eq.trans ?_ (Polynomial.as_sum_range' p (e + 1) (by omega)).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial]

theorem eval_map_homog {L : Type*} [Field L] (φ : K →+* L) (e : ℕ) (p : Polynomial K)
    (v : Fin 2 → L) :
    MvPolynomial.eval v (MvPolynomial.map φ (homog e p))
      = ∑ i ∈ Finset.range (e + 1), φ (p.coeff i) * v 0 ^ i * v 1 ^ (e - i) := by
  rw [homog]
  simp

theorem eval_map_homog_of_snd_ne_zero {L : Type*} [Field L] (φ : K →+* L) {e : ℕ}
    {p : Polynomial K} (hp : p.natDegree ≤ e) {v : Fin 2 → L} (hv : v 1 ≠ 0) :
    MvPolynomial.eval v (MvPolynomial.map φ (homog e p))
      = v 1 ^ e * Polynomial.eval (v 0 / v 1) (p.map φ) := by
  rw [eval_map_homog, Polynomial.eval_eq_sum_range' (n := e + 1)
      (lt_of_le_of_lt (Polynomial.natDegree_map_le) (by omega)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hie : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : v 1 ^ (e - i) * v 1 ^ i = v 1 ^ e := by
    rw [← pow_add]; congr 1; omega
  rw [Polynomial.coeff_map, div_pow, ← hpow]
  field_simp

theorem eval_map_homog_of_snd_eq_zero {L : Type*} [Field L] (φ : K →+* L) (e : ℕ)
    (p : Polynomial K) {v : Fin 2 → L} (hv : v 1 = 0) :
    MvPolynomial.eval v (MvPolynomial.map φ (homog e p)) = φ (p.coeff e) * v 0 ^ e := by
  rw [eval_map_homog, Finset.sum_eq_single e]
  · rw [hv, Nat.sub_self, pow_zero, mul_one]
  · intro i hi hne
    have hie : i < e := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    rw [hv, zero_pow (by omega), mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ e) h


end Homog

/-! ### A Bézout identity for four polynomials after removing their common factor -/

section Bezout

variable {K : Type*} [Field K]

theorem exists_gcd_bezout (p q : Polynomial K) :
    ∃ d a b : Polynomial K, d = p * a + q * b ∧ d ∣ p ∧ d ∣ q :=
  ⟨EuclideanDomain.gcd p q, EuclideanDomain.gcdA p q, EuclideanDomain.gcdB p q,
    EuclideanDomain.gcd_eq_gcd_ab p q, EuclideanDomain.gcd_dvd_left p q,
    EuclideanDomain.gcd_dvd_right p q⟩

theorem exists_bezout_of_four (p q r s : Polynomial K) (hs : s ≠ 0) :
    ∃ Δ P Q R S a b u w : Polynomial K, Δ ≠ 0 ∧
      p = Δ * P ∧ q = Δ * Q ∧ r = Δ * R ∧ s = Δ * S ∧
      P * a + Q * b + R * u + S * w = 1 := by
  obtain ⟨g₁, a₁, b₁, hg₁, hd₁p, hd₁q⟩ := exists_gcd_bezout p q
  obtain ⟨g₂, a₂, b₂, hg₂, hd₂r, hd₂s⟩ := exists_gcd_bezout r s
  obtain ⟨Δ, a₃, b₃, hg₃, hd₃₁, hd₃₂⟩ := exists_gcd_bezout g₁ g₂
  obtain ⟨P, hP⟩ := hd₃₁.trans hd₁p
  obtain ⟨Q, hQ⟩ := hd₃₁.trans hd₁q
  obtain ⟨R, hR⟩ := hd₃₂.trans hd₂r
  obtain ⟨S, hS⟩ := hd₃₂.trans hd₂s
  have hΔ0 : Δ ≠ 0 := by
    intro hz
    exact hs (by rw [hS, hz, zero_mul])
  refine ⟨Δ, P, Q, R, S, a₁ * a₃, b₁ * a₃, a₂ * b₃, b₂ * b₃, hΔ0, hP, hQ, hR, hS, ?_⟩
  refine mul_left_cancel₀ hΔ0 ?_
  rw [mul_one]
  calc Δ * (P * (a₁ * a₃) + Q * (b₁ * a₃) + R * (a₂ * b₃) + S * (b₂ * b₃))
      = (Δ * P * a₁ + Δ * Q * b₁) * a₃ + (Δ * R * a₂ + Δ * S * b₂) * b₃ := by ring
    _ = (p * a₁ + q * b₁) * a₃ + (r * a₂ + s * b₂) * b₃ := by rw [← hP, ← hQ, ← hR, ← hS]
    _ = g₁ * a₃ + g₂ * b₃ := by rw [← hg₁, ← hg₂]
    _ = Δ := hg₃.symm


end Bezout

/-! ### `dehom` on sums and powers -/

theorem dehom_add {K : Type*} [Field K] (Φ Ψ : MvPolynomial (Fin 2) K) :
    dehom (Φ + Ψ) = dehom Φ + dehom Ψ := by
  simp [dehom]

theorem dehom_pow {K : Type*} [Field K] (Φ : MvPolynomial (Fin 2) K) (n : ℕ) :
    dehom (Φ ^ n) = dehom Φ ^ n := by
  simp [dehom]

/-! ### The homogenization bridge -/

/-- **BLUEPRINT Stage C, step C3 / SKETCH §5.2.3, the clearing-denominators step.**
A nonconstant rational solution of `f¹³ − g¹³ − h¹³ = −c` yields a genuine
parametrization `IsParamOfXN (−c) e A` of `X_{−c}` by binary forms which is not a
constant family. -/
theorem exists_form_param_of_ratfunc (c : ℤ) (f g h : RatFunc ℚ)
    (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ)))
    (hnc : ¬ (IsConstRF f ∧ IsConstRF g ∧ IsConstRF h)) :
    ∃ (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ),
      IsParamOfXN (-(c : ℚ)) e A ∧ ¬ IsConstantFamily A := by
  classical
  have hCne : ∀ a : ℚ, a ≠ 0 → RatFunc.C a ≠ (0 : RatFunc ℚ) := by
    intro a ha
    rw [← RatFunc.algebraMap_C]
    exact RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr ha)
  -- numerators and denominators
  have hdf : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hdg : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hdh : h.denom ≠ 0 := RatFunc.denom_ne_zero h
  have hfn : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) f.num
      = f * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) f.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero hdf)).mp (RatFunc.num_div_denom f)
  have hgn : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) g.num
      = g * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) g.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero hdg)).mp (RatFunc.num_div_denom g)
  have hhn : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) h.num
      = h * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) h.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero hdh)).mp (RatFunc.num_div_denom h)
  -- a common denominator
  obtain ⟨F₀, hF₀⟩ : ∃ x : Polynomial ℚ, x = f.num * g.denom * h.denom := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀⟩ : ∃ x : Polynomial ℚ, x = -(g.num * f.denom * h.denom) := ⟨_, rfl⟩
  obtain ⟨H₀, hH₀⟩ : ∃ x : Polynomial ℚ, x = -(h.num * f.denom * g.denom) := ⟨_, rfl⟩
  obtain ⟨R₀, hR₀⟩ : ∃ x : Polynomial ℚ, x = f.denom * g.denom * h.denom := ⟨_, rfl⟩
  have hR₀0 : R₀ ≠ 0 := by
    rw [hR₀]; exact mul_ne_zero (mul_ne_zero hdf hdg) hdh
  have hFR : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) F₀
      = f * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₀ := by
    rw [hF₀, hR₀, map_mul, map_mul, map_mul, map_mul, hfn]; ring
  have hGR : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) G₀
      = -g * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₀ := by
    rw [hG₀, hR₀, map_neg, map_mul, map_mul, map_mul, map_mul, hgn]; ring
  have hHR : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) H₀
      = -h * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₀ := by
    rw [hH₀, hR₀, map_neg, map_mul, map_mul, map_mul, map_mul, hhn]; ring
  -- divide out the common factor
  obtain ⟨Δ, F₁, G₁, H₁, R₁, aa, bb, uu, ww, hΔ0, hFe, hGe, hHe, hRe, hbez⟩ :=
    exists_bezout_of_four F₀ G₀ H₀ R₀ hR₀0
  have hΔa0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) Δ ≠ 0 := RatFunc.algebraMap_ne_zero hΔ0
  have hR₁0 : R₁ ≠ 0 := by
    intro hz; exact hR₀0 (by rw [hRe, hz, mul_zero])
  have hcancel : ∀ (y : RatFunc ℚ) (X : Polynomial ℚ),
      (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Δ * X)
        = y * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Δ * R₁) →
      (algebraMap (Polynomial ℚ) (RatFunc ℚ)) X
        = y * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₁ := by
    intro y X hxy
    rw [map_mul, map_mul] at hxy
    refine mul_left_cancel₀ hΔa0 ?_
    rw [hxy]; ring
  have hF1 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) F₁
      = f * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₁ :=
    hcancel f F₁ (by rw [← hFe, ← hRe]; exact hFR)
  have hG1 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) G₁
      = -g * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₁ :=
    hcancel (-g) G₁ (by rw [← hGe, ← hRe]; exact hGR)
  have hH1 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) H₁
      = -h * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₁ :=
    hcancel (-h) H₁ (by rw [← hHe, ← hRe]; exact hHR)
  -- the polynomial identity
  have hpoly : F₁ ^ 13 + G₁ ^ 13 + H₁ ^ 13 = Polynomial.C (-(c : ℚ)) * R₁ ^ 13 := by
    refine RatFunc.algebraMap_injective ℚ ?_
    simp only [map_add, map_pow, map_mul, RatFunc.algebraMap_C]
    rw [hF1, hG1, hH1, ← hfgh]
    ring
  -- the four polynomials, packaged
  obtain ⟨P, hP⟩ : ∃ P : Fin 4 → Polynomial ℚ, P = ![F₁, G₁, H₁, R₁] := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ,
      e = max (max F₁.natDegree G₁.natDegree) (max H₁.natDegree R₁.natDegree) := ⟨_, rfl⟩
  have hi4 : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  have hP0 : P 0 = F₁ := by rw [hP]; simp
  have hP1 : P 1 = G₁ := by rw [hP]; simp
  have hP2 : P 2 = H₁ := by rw [hP]; simp
  have hP3 : P 3 = R₁ := by rw [hP]; simp
  have hPdeg : ∀ i, (P i).natDegree ≤ e := by
    intro i
    rcases hi4 i with rfl | rfl | rfl | rfl
    · rw [hP0, he]; omega
    · rw [hP1, he]; omega
    · rw [hP2, he]; omega
    · rw [hP3, he]; omega
  -- if all four are constant multiples of one polynomial, `f`, `g`, `h` are all constant
  have hallconst : ∀ (b : Fin 4 → ℚ) (D : Polynomial ℚ),
      (∀ i, P i = Polynomial.C (b i) * D) → False := by
    intro b D hb
    have hR₁b : R₁ = Polynomial.C (b 3) * D := by rw [← hP3]; exact hb 3
    have hD0 : D ≠ 0 := by
      intro hz; exact hR₁0 (by rw [hR₁b, hz, mul_zero])
    have hb30 : b 3 ≠ 0 := by
      intro hz; exact hR₁0 (by rw [hR₁b, hz, map_zero, zero_mul])
    have hDa0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) D ≠ 0 := RatFunc.algebraMap_ne_zero hD0
    have hkey : ∀ (i : Fin 4) (y : RatFunc ℚ),
        (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (P i)
          = y * (algebraMap (Polynomial ℚ) (RatFunc ℚ)) R₁ → y = RatFunc.C (b i / b 3) := by
      intro i y hy
      rw [hb i, map_mul, RatFunc.algebraMap_C] at hy
      rw [hR₁b, map_mul, RatFunc.algebraMap_C] at hy
      have hy2 : RatFunc.C (b i) = y * RatFunc.C (b 3) := by
        refine mul_right_cancel₀ hDa0 ?_
        rw [hy]; ring
      rw [map_div₀, hy2, mul_div_assoc, div_self (hCne _ hb30), mul_one]
    refine hnc ⟨⟨b 0 / b 3, hkey 0 f (by rw [hP0]; exact hF1)⟩, ⟨-(b 1 / b 3), ?_⟩,
      ⟨-(b 2 / b 3), ?_⟩⟩
    · have := hkey 1 (-g) (by rw [hP1]; exact hG1)
      rw [← neg_eq_iff_eq_neg.mpr this.symm, map_neg]
    · have := hkey 2 (-h) (by rw [hP2]; exact hH1)
      rw [← neg_eq_iff_eq_neg.mpr this.symm, map_neg]
  -- `1 ≤ e`
  have he1 : 1 ≤ e := by
    by_contra hcon
    have he0 : e = 0 := by omega
    refine hallconst (fun i => (P i).coeff 0) 1 fun i => ?_
    rw [mul_one]
    exact Polynomial.eq_C_of_natDegree_eq_zero (le_antisymm (he0 ▸ hPdeg i) (Nat.zero_le _))
  -- the homogenized family
  obtain ⟨A, hA⟩ : ∃ A : Fin 4 → MvPolynomial (Fin 2) ℚ, A = fun i => homog e (P i) := ⟨_, rfl⟩
  have hAhom : ∀ i, (A i).IsHomogeneous e := by
    intro i; rw [hA]; exact homog_isHomogeneous e (P i)
  have hdehomA : ∀ i, dehom (A i) = P i := by
    intro i; rw [hA]; exact dehom_homog (hPdeg i)
  -- no common projective zero over `ℂ`
  have hncz : NoCommonProjZero (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (A i)) := by
    intro v hv
    have hv' : ∀ i, MvPolynomial.eval v
        (MvPolynomial.map (algebraMap ℚ ℂ) (homog e (P i))) = 0 := by
      intro i; have := hv i; rwa [hA] at this
    have hv0 : v 0 = 0 ∧ v 1 = 0 := by
      by_cases hv1 : v 1 = 0
      · refine ⟨?_, hv1⟩
        obtain ⟨i0, hi0⟩ : ∃ i : Fin 4, (P i).natDegree = e := by
          have hd : e = F₁.natDegree ∨ e = G₁.natDegree ∨ e = H₁.natDegree
              ∨ e = R₁.natDegree := by rw [he]; omega
          rcases hd with hd | hd | hd | hd
          · exact ⟨0, by rw [hP0]; exact hd.symm⟩
          · exact ⟨1, by rw [hP1]; exact hd.symm⟩
          · exact ⟨2, by rw [hP2]; exact hd.symm⟩
          · exact ⟨3, by rw [hP3]; exact hd.symm⟩
        have hPi0 : P i0 ≠ 0 := by
          intro hz
          rw [hz, Polynomial.natDegree_zero] at hi0
          omega
        have hcf : (P i0).coeff e ≠ 0 := by
          rw [← hi0]; exact Polynomial.leadingCoeff_ne_zero.mpr hPi0
        have hval := hv' i0
        rw [eval_map_homog_of_snd_eq_zero _ e _ hv1] at hval
        rcases mul_eq_zero.mp hval with hz | hz
        · exact absurd ((map_eq_zero_iff _ (algebraMap ℚ ℂ).injective).mp hz) hcf
        · exact (pow_eq_zero_iff (n := e) (by omega)).mp hz
      · exfalso
        have hroot : ∀ i, Polynomial.eval (v 0 / v 1)
            ((P i).map (algebraMap ℚ ℂ)) = 0 := by
          intro i
          have hval := hv' i
          rw [eval_map_homog_of_snd_ne_zero _ (hPdeg i) hv1] at hval
          rcases mul_eq_zero.mp hval with hz | hz
          · exact absurd hz (pow_ne_zero _ hv1)
          · exact hz
        have hr0 := hroot 0
        have hr1 := hroot 1
        have hr2 := hroot 2
        have hr3 := hroot 3
        rw [hP0] at hr0
        rw [hP1] at hr1
        rw [hP2] at hr2
        rw [hP3] at hr3
        have hmap := congrArg (fun q : Polynomial ℚ =>
          Polynomial.eval (v 0 / v 1) (q.map (algebraMap ℚ ℂ))) hbez
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at hmap
        rw [hr0, hr1, hr2, hr3] at hmap
        simp at hmap
    have hi2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    funext i
    rcases hi2 i with rfl | rfl
    · simpa using hv0.1
    · simpa using hv0.2
  -- the defining identity of the parametrization
  have hpow13 : ∀ i, (A i ^ 13).IsHomogeneous (13 * e) := by
    intro i
    have hh := (hAhom i).pow 13
    rwa [Nat.mul_comm e 13] at hh
  have heq : A 0 ^ 13 + A 1 ^ 13 + A 2 ^ 13 = MvPolynomial.C (-(c : ℚ)) * A 3 ^ 13 := by
    refine dehom_injective_of_isHomogeneous (e := 13 * e) ?_ ?_ ?_
    · rw [← MvPolynomial.mem_homogeneousSubmodule]
      exact add_mem (add_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hpow13 0))
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hpow13 1)))
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hpow13 2))
    · simpa using (MvPolynomial.isHomogeneous_C (Fin 2) (-(c : ℚ))).mul (hpow13 3)
    · rw [dehom_add, dehom_add, dehom_pow, dehom_pow, dehom_pow, dehom_mul, dehom_pow, dehom_C,
        hdehomA 0, hdehomA 1, hdehomA 2, hdehomA 3, hP0, hP1, hP2, hP3]
      exact hpoly
  -- the family is not constant
  have hncf : ¬ IsConstantFamily A := by
    rintro ⟨b, Φ, hb⟩
    refine hallconst b (dehom Φ) fun i => ?_
    rw [← hdehomA i, hb i, dehom_mul, dehom_C]
  exact ⟨e, A, ⟨he1, hAhom, hncz, heq⟩, hncf⟩


set_option linter.unusedVariables false in
/-- **BLUEPRINT Stage C, step C3 / SKETCH §5.2.3 (Corollary 3.2), conditional form.**
This is the frozen `no_rational_param_of_not_mem_Bset` with its Lemma-3.1 input
(`Erdos477.no_nonconstant_param_of_not_pow13`, still open) replaced by the explicit
hypothesis `hC2` of exactly that shape.  It is deliberately NOT named
`no_rational_param_of_not_mem_Bset_proof`. -/
-- `hc` is part of the signature mandated by `TASKS.md` (Iteration 3, Agent 3) so that
-- the frozen theorem becomes a one-line application once C2 lands; the proof itself
-- does not need it, and the linter would otherwise flag the binder.
theorem no_rational_param_of_C2 (c : ℤ) (hc : c ∉ Bset)
    (hC2 : ∀ (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ),
      IsParamOfXN (-(c : ℚ)) e A → IsConstantFamily A)
    (f g h : RatFunc ℚ)
    (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h := by
  by_contra hcon
  obtain ⟨e, A, hA, hncf⟩ := exists_form_param_of_ratfunc c f g h hfgh hcon
  exact hncf (hC2 e A hA)

example (c : ℤ) (hc : c ∉ Bset)
    (C2 : ∀ (N : ℚ), N ≠ 0 → (¬ ∃ d : ℚ, d ^ 13 = N) → ∀ (e : ℕ)
      (A : Fin 4 → MvPolynomial (Fin 2) ℚ), IsParamOfXN N e A → IsConstantFamily A)
    (f g h : RatFunc ℚ) (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h :=
  no_rational_param_of_C2 c hc (fun e A hA => C2 _ (neg_cast_ne_zero_of_not_mem_Bset c hc)
    (not_exists_pow13_neg c hc) e A hA) f g h hfgh
/-! ### Guardrails

These pin down the chart convention shared by `homog`, `dehom` and `IsProjZero`
(`some a ↔ [a : 1]`, `none ↔ [1 : 0]`), and check that the frozen
`no_rational_param_of_not_mem_Bset` really is one application away.  The `C2`
hypothesis below is the frozen statement of `no_nonconstant_param_of_not_pow13`
written out; it is a *hypothesis*, so nothing here cites the open frozen theorem. -/

/-- The second variable is the homogenizing one: `homog 1 X = X₀`. -/
example : homog 1 (Polynomial.X : Polynomial ℚ) = MvPolynomial.X 0 := by
  simp [homog, Finset.sum_range_succ]

/-- ... and `homog 1 1 = X₁`. -/
example : homog 1 (1 : Polynomial ℚ) = MvPolynomial.X 1 := by
  simp [homog, Polynomial.coeff_one]

/-- At `none ↔ [1 : 0]` a homogenization evaluates to the top coefficient. -/
theorem eval_top_homog {K : Type*} [Field K] {e : ℕ} {p : Polynomial K}
    (hp : p.natDegree ≤ e) : MvPolynomial.eval ![1, 0] (homog e p) = p.coeff e := by
  rw [← coeff_dehom_top (homog_isHomogeneous e p), dehom_homog hp]

/-- At `some α ↔ [α : 1]` it evaluates to `p α`. -/
theorem eval_chart_homog {K : Type*} [Field K] {e : ℕ} {p : Polynomial K}
    (hp : p.natDegree ≤ e) (α : K) :
    MvPolynomial.eval ![α, 1] (homog e p) = p.eval α := by
  rw [← eval_dehom, dehom_homog hp]

/-- Once Stage C2 lands, the frozen `no_rational_param_of_not_mem_Bset`
(`Erdos477/Theorems.lean:68-70`) is exactly this one-liner. -/
example (c : ℤ) (hc : c ∉ Bset)
    (C2 : ∀ (N : ℚ), N ≠ 0 → (¬ ∃ d : ℚ, d ^ 13 = N) → ∀ (e : ℕ)
      (A : Fin 4 → MvPolynomial (Fin 2) ℚ), IsParamOfXN N e A → IsConstantFamily A)
    (f g h : RatFunc ℚ) (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h :=
  no_rational_param_of_C2 c hc (fun e A hA => C2 _ (neg_cast_ne_zero_of_not_mem_Bset c hc)
    (not_exists_pow13_neg c hc) e A hA) f g h hfgh

end Erdos477
