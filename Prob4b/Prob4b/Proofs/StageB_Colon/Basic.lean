/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b worker agent-iter2-2
-/
import Prob4b.Proofs.StageA_Algebra.Basic
import Prob4b.Proofs.StageA_Algebra.NormalForm

/-!
# Stage B — the colon lemma `(I : m) = I + m²`

This module covers `BLUEPRINT.md` Part 2 Stage A step A6 and Stage B step B1.

Delivered here:

* `mem_mB_iff` — `x ∈ mB` iff the constant coefficient of `x` vanishes;
* `isUnit_of_not_mem_mB` — `B` is local with maximal ideal `mB`;
* `B_colon_two_gen_proof` — frozen theorem 5,
  `colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2`.

Everything is computed through the Stage A normal form `nf`, which turns the
noncomputable quotient `Balg` into the computable coordinate space
`Idx → ZMod 2`.

All support lemmas introduced here carry the `colon_` prefix, as required by the
iteration's naming rules.
-/

open MvPolynomial

namespace Prob4b

noncomputable section

/-! ## Bridges between `mB`, `mPol` and the normal form -/

/-- The relation ideal sits inside the irrelevant maximal ideal upstairs. -/
theorem colon_relIdeal_le_mPol : relIdeal ≤ mPol := by
  have hX : ∀ i : Fin 4, (X i : Pol) ∈ mPol := by
    intro i
    rw [mPol]
    refine Ideal.subset_span ?_
    fin_cases i <;> simp
  refine sup_le (Ideal.pow_le_self (by norm_num)) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hX 0)) (Ideal.mul_mem_right _ _ (hX 1))

/-- Membership in `mB` is membership of some preimage in `mPol`. -/
theorem colon_mem_mB_iff_exists (x : Balg) :
    x ∈ mB ↔ ∃ p ∈ mPol, Ideal.Quotient.mk relIdeal p = x := by
  rw [mB_eq_map]
  exact Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective

/-- `mB ^ 2` is the extension of `mPol ^ 2`. -/
theorem colon_mB_sq_eq_map : mB ^ 2 = Ideal.map (Ideal.Quotient.mk relIdeal) (mPol ^ 2) := by
  rw [mB_eq_map, Ideal.map_pow]

/-- Membership in `mB ^ 2` is membership of some preimage in `mPol ^ 2`. -/
theorem colon_mem_mB_sq_iff_exists (x : Balg) :
    x ∈ mB ^ 2 ↔ ∃ p ∈ mPol ^ 2, Ideal.Quotient.mk relIdeal p = x := by
  rw [colon_mB_sq_eq_map]
  exact Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective

/-- `mPol ^ 2` has no monomial of degree below two. -/
theorem colon_mPol_sq_le_degGe_two : mPol ^ 2 ≤ degGe 2 := by
  have h : mPol * mPol ≤ degGe 2 :=
    le_trans (Ideal.mul_mono mPol_le_degGe_one mPol_le_degGe_one) (degGe_mul 1 1)
  simpa [pow_two] using h

/-- An `F₂`-multiple of an element of an ideal of `B` stays in the ideal. -/
theorem colon_smul_mem {I : Ideal Balg} (c : ZMod 2) {y : Balg} (h : y ∈ I) : c • y ∈ I := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · simpa using h

/-- Every nonconstant basis monomial lies in `mB`. -/
theorem colon_monB_mem_mB {i : Idx} (hi : i ≠ Sum.inl ()) : monB i ∈ mB := by
  have h1 : 1 ≤ edeg (monoExp i) := by
    rcases i with u | k | j
    · cases u; exact absurd rfl hi
    · simp
    · simp
  refine (colon_mem_mB_iff_exists _).2 ⟨monomial (monoExp i) 1, ?_, rfl⟩
  simpa using monomial_mem_mPol_pow 1 (monoExp i) h1

/-- Every degree-two basis monomial lies in `mB ^ 2`. -/
theorem colon_monB_mem_mB_sq (j : Fin 9) : monB (Sum.inr (Sum.inr j)) ∈ mB ^ 2 := by
  refine (colon_mem_mB_sq_iff_exists _).2 ⟨monomial (monoExp (Sum.inr (Sum.inr j))) 1, ?_, rfl⟩
  exact monomial_mem_mPol_pow 2 _ (by simp)

/-! ## A6 — the maximal ideal read off from the normal form -/

/-- Stage A, step A6: `x` lies in the maximal ideal exactly when its constant
coefficient vanishes. -/
theorem mem_mB_iff (x : Balg) : x ∈ mB ↔ nf x (Sum.inl ()) = 0 := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := (colon_mem_mB_iff_exists x).1 hx
    rw [nf_mk, nfPol_apply, if_neg (by decide : (Sum.inl () : Idx) ≠ adIdx), add_zero,
      monoExp_inl]
    exact mem_degGe.1 (mPol_le_degGe_one hp) 0 (by simp)
  · intro hx
    have hsum : x = ∑ i : Idx, nf x i • monB i := by
      rw [← sec_apply, sec_nf_apply]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hi : i = Sum.inl ()
    · subst hi
      rw [hx, zero_smul]
      exact Ideal.zero_mem _
    · exact colon_smul_mem _ (colon_monB_mem_mB hi)

/-- `x` lies in `mB ^ 2` exactly when its constant and degree-one coefficients
all vanish. -/
theorem colon_mem_mB_sq_iff (x : Balg) :
    x ∈ mB ^ 2 ↔ nf x (Sum.inl ()) = 0 ∧ ∀ k : Fin 4, nf x (Sum.inr (Sum.inl k)) = 0 := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := (colon_mem_mB_sq_iff_exists x).1 hx
    have hd := colon_mPol_sq_le_degGe_two hp
    constructor
    · rw [nf_mk, nfPol_apply, if_neg (by decide : (Sum.inl () : Idx) ≠ adIdx), add_zero,
        monoExp_inl]
      exact mem_degGe.1 hd 0 (by simp)
    · intro k
      rw [nf_mk, nfPol_apply,
        if_neg (by simp [adIdx] : (Sum.inr (Sum.inl k) : Idx) ≠ adIdx), add_zero, monoExp_lin]
      exact mem_degGe.1 hd _ (by simp)
  · rintro ⟨h0, h1⟩
    have hsum : x = ∑ i : Idx, nf x i • monB i := by
      rw [← sec_apply, sec_nf_apply]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rcases i with u | k | j
    · cases u
      rw [h0, zero_smul]
      exact Ideal.zero_mem _
    · rw [h1 k, zero_smul]
      exact Ideal.zero_mem _
    · exact colon_smul_mem _ (colon_monB_mem_mB_sq j)

/-! ## A6 — locality of `B` -/

/-- Stage A, step A6: an element outside the maximal ideal is a unit. -/
theorem isUnit_of_not_mem_mB (x : Balg) (hx : x ∉ mB) : IsUnit x := by
  have hc : nf x (Sum.inl ()) ≠ 0 := fun h => hx ((mem_mB_iff x).2 h)
  set y : Balg := x + 1 with hy
  have hymem : y ∈ mB := by
    refine (mem_mB_iff y).2 ?_
    have h1 : nf y (Sum.inl ()) = nf x (Sum.inl ()) + 1 := by
      rw [hy, map_add, Pi.add_apply, nf_one, Pi.single_eq_same]
    have h2 : nf x (Sum.inl ()) = 1 := by
      have := hc
      revert this
      generalize nf x (Sum.inl ()) = c
      revert c
      decide
    rw [h1, h2]
    decide
  have hxy : x = 1 + y := by
    rw [hy]
    have h2 : (2 : Balg) = 0 := B_two_eq_zero
    linear_combination (norm := ring_nf) -h2
  have hcube : y * y * y = 0 := mul_mem_mB_three hymem hymem hymem
  refine ⟨⟨x, 1 + y + y * y, ?_, ?_⟩, rfl⟩
  · rw [hxy]
    have hexp : (1 + y) * (1 + y + y * y) = 1 + 2 * y + 2 * (y * y) + y * y * y := by ring
    rw [hexp, hcube, B_two_eq_zero]
    ring
  · rw [hxy]
    have hexp : (1 + y + y * y) * (1 + y) = 1 + 2 * y + 2 * (y * y) + y * y * y := by ring
    rw [hexp, hcube, B_two_eq_zero]
    ring

/-! ## Degree-one elements in coordinates -/

/-- The degree-one element of `B` with coordinate vector `s`. -/
def colon_lin (s : Fin 4 → ZMod 2) : Balg := ∑ k : Fin 4, s k • vvec k

/-- Normal form of a generator. -/
theorem colon_nf_vvec (k : Fin 4) : nf (vvec k) = Pi.single (Sum.inr (Sum.inl k)) 1 := by
  fin_cases k <;> simp [vvec]

/-- Coordinates of a degree-one element. -/
theorem colon_nf_lin_apply (s : Fin 4 → ZMod 2) (i : Idx) :
    nf (colon_lin s) i = ∑ k : Fin 4, s k * (if i = Sum.inr (Sum.inl k) then 1 else 0) := by
  rw [colon_lin, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, colon_nf_vvec]
  simp [Pi.single_apply, smul_eq_mul]

/-- The constant coordinate of a degree-one element vanishes. -/
@[simp] theorem colon_nf_lin_const (s : Fin 4 → ZMod 2) :
    nf (colon_lin s) (Sum.inl ()) = 0 := by
  rw [colon_nf_lin_apply]
  simp

/-- The degree-one coordinates of `colon_lin s` are the entries of `s`. -/
@[simp] theorem colon_nf_lin_lin (s : Fin 4 → ZMod 2) (k : Fin 4) :
    nf (colon_lin s) (Sum.inr (Sum.inl k)) = s k := by
  rw [colon_nf_lin_apply, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The degree-two coordinates of a degree-one element vanish. -/
@[simp] theorem colon_nf_lin_quad (s : Fin 4 → ZMod 2) (j : Fin 9) :
    nf (colon_lin s) (Sum.inr (Sum.inr j)) = 0 := by
  rw [colon_nf_lin_apply]
  simp

/-- Degree-one elements lie in the maximal ideal. -/
theorem colon_lin_mem_mB (s : Fin 4 → ZMod 2) : colon_lin s ∈ mB :=
  (mem_mB_iff _).2 (colon_nf_lin_const s)

/-- A generator is the degree-one element of the corresponding unit vector. -/
theorem colon_lin_single (k : Fin 4) : colon_lin (Pi.single k 1) = vvec k := by
  rw [colon_lin, Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne hl]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Every element of `mB` splits as a degree-one part plus an element of `mB ^ 2`. -/
theorem colon_deg_split (x : Balg) (hx : x ∈ mB) :
    ∃ w : Balg, w ∈ mB ^ 2 ∧ x = colon_lin (fun k => nf x (Sum.inr (Sum.inl k))) + w := by
  refine ⟨x - colon_lin (fun k => nf x (Sum.inr (Sum.inl k))), ?_, by ring⟩
  refine (colon_mem_mB_sq_iff _).2 ⟨?_, ?_⟩
  · rw [map_sub, Pi.sub_apply, colon_nf_lin_const, (mem_mB_iff x).1 hx, sub_zero]
  · intro k
    rw [map_sub, Pi.sub_apply, colon_nf_lin_lin, sub_self]

/-! ## The multiplication `V × V → W` in coordinates -/

/-- The index of the degree-two basis monomial `X k * X l` (with `bc` folded onto
`ad`). -/
def colon_pairIdx : Fin 4 → Fin 4 → Fin 9 :=
  ![![0, 1, 2, 3], ![1, 4, 3, 5], ![2, 3, 6, 7], ![3, 5, 7, 8]]

/-- Normal form of a product of two generators. -/
theorem colon_nf_vvec_mul (k l : Fin 4) :
    nf (vvec k * vvec l) = Pi.single (Sum.inr (Sum.inr (colon_pairIdx k l))) 1 := by
  fin_cases k <;> fin_cases l <;> simp [vvec, colon_pairIdx, adIdx, mul_comm]

/-- Expansion of the product of two degree-one elements. -/
theorem colon_lin_mul_expand (s z : Fin 4 → ZMod 2) :
    colon_lin s * colon_lin z
      = ∑ k : Fin 4, ∑ l : Fin 4, (s k * z l) • (vvec k * vvec l) := by
  rw [colon_lin, colon_lin, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Coordinates of a product of two degree-one elements. -/
theorem colon_nf_lin_mul_apply (s z : Fin 4 → ZMod 2) (i : Idx) :
    nf (colon_lin s * colon_lin z) i
      = ∑ k : Fin 4, ∑ l : Fin 4,
          (s k * z l) * (if i = Sum.inr (Sum.inr (colon_pairIdx k l)) then 1 else 0) := by
  rw [colon_lin_mul_expand, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, colon_nf_vvec_mul]
  simp [Pi.single_apply, smul_eq_mul]

/-- The nine degree-two coordinates of a product of two degree-one elements. -/
def colon_mulc (s z : Fin 4 → ZMod 2) : Fin 9 → ZMod 2 :=
  ![s 0 * z 0,
    s 0 * z 1 + s 1 * z 0,
    s 0 * z 2 + s 2 * z 0,
    s 0 * z 3 + s 3 * z 0 + (s 1 * z 2 + s 2 * z 1),
    s 1 * z 1,
    s 1 * z 3 + s 3 * z 1,
    s 2 * z 2,
    s 2 * z 3 + s 3 * z 2,
    s 3 * z 3]

set_option linter.unnecessarySeqFocus false in
/-- The degree-two coordinates of a product of degree-one elements are given by
`colon_mulc`. -/
theorem colon_nf_lin_mul_quad (s z : Fin 4 → ZMod 2) (j : Fin 9) :
    nf (colon_lin s * colon_lin z) (Sum.inr (Sum.inr j)) = colon_mulc s z j := by
  rw [colon_nf_lin_mul_apply]
  fin_cases j <;> simp [colon_pairIdx, colon_mulc, Fin.sum_univ_four] <;> ring

/-! ## Nondegeneracy of the multiplication -/

set_option synthInstance.maxSize 4000 in
/-- Auxiliary finite check backing `colon_mul_inj_of_ne_zero`. -/
theorem colon_scalar_nondeg : ∀ a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 2,
    a0 * b0 = 0 → a0 * b1 + a1 * b0 = 0 → a0 * b2 + a2 * b0 = 0 →
    a0 * b3 + a3 * b0 + (a1 * b2 + a2 * b1) = 0 → a1 * b1 = 0 →
    a1 * b3 + a3 * b1 = 0 → a2 * b2 = 0 → a2 * b3 + a3 * b2 = 0 → a3 * b3 = 0 →
    (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0) ∨ (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0) := by
  decide

/-- An element with vanishing normal form is zero. -/
theorem colon_eq_zero_of_nf {x : Balg} (h : nf x = 0) : x = 0 := by
  have := sec_nf_apply x
  rw [h, map_zero] at this
  exact this.symm

/-- A degree-one element is zero exactly when its coordinate vector is. -/
theorem colon_lin_eq_zero_iff (s : Fin 4 → ZMod 2) : colon_lin s = 0 ↔ ∀ k, s k = 0 := by
  constructor
  · intro h k
    have := colon_nf_lin_lin s k
    rw [h, map_zero] at this
    simpa using this.symm
  · intro h
    refine colon_eq_zero_of_nf ?_
    funext i
    rcases i with u | k | j
    · cases u; simp
    · simpa using h k
    · simp

/-- The core Stage B linear-algebra fact: a product of two nonzero degree-one
elements of `B` is nonzero. -/
theorem colon_mul_inj_of_ne_zero (s z : Fin 4 → ZMod 2)
    (h : colon_lin s * colon_lin z = 0) : colon_lin s = 0 ∨ colon_lin z = 0 := by
  have hj : ∀ j : Fin 9, colon_mulc s z j = 0 := by
    intro j
    rw [← colon_nf_lin_mul_quad, h, map_zero]
    rfl
  have h0 : s 0 * z 0 = 0 := hj 0
  have h1 : s 0 * z 1 + s 1 * z 0 = 0 := hj 1
  have h2 : s 0 * z 2 + s 2 * z 0 = 0 := hj 2
  have h3 : s 0 * z 3 + s 3 * z 0 + (s 1 * z 2 + s 2 * z 1) = 0 := hj 3
  have h4 : s 1 * z 1 = 0 := hj 4
  have h5 : s 1 * z 3 + s 3 * z 1 = 0 := hj 5
  have h6 : s 2 * z 2 = 0 := hj 6
  have h7 : s 2 * z 3 + s 3 * z 2 = 0 := hj 7
  have h8 : s 3 * z 3 = 0 := hj 8
  rcases colon_scalar_nondeg (s 0) (s 1) (s 2) (s 3) (z 0) (z 1) (z 2) (z 3)
      h0 h1 h2 h3 h4 h5 h6 h7 h8 with ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
  · left
    refine (colon_lin_eq_zero_iff s).2 fun k => ?_
    fin_cases k <;> assumption
  · right
    refine (colon_lin_eq_zero_iff z).2 fun k => ?_
    fin_cases k <;> assumption

/-! ## Structure of an ideal generated by two elements of `mB` -/

/-- A product `mB ^ 2 · mB` vanishes. -/
theorem colon_sq_mul (w z : Balg) (hw : w ∈ mB ^ 2) (hz : z ∈ mB) : w * z = 0 := by
  have h : w * z ∈ mB ^ 2 * mB := Ideal.mul_mem_mul hw hz
  rw [← pow_succ, B_maximalIdeal_pow_three_proof] at h
  simpa using h

/-- Splitting off the constant term of an element of `B`. -/
theorem colon_const_split (u : Balg) :
    ∃ u' : Balg, u' ∈ mB ∧ u = nf u (Sum.inl ()) • (1 : Balg) + u' := by
  refine ⟨u - nf u (Sum.inl ()) • (1 : Balg), ?_, by ring⟩
  refine (mem_mB_iff _).2 ?_
  rw [map_sub, Pi.sub_apply, map_smul, Pi.smul_apply, nf_one, Pi.single_eq_same]
  simp

/-- The elements of an ideal generated by two elements of `mB`: an `F₂`-combination
of the generators plus degree-one multiples of them. -/
theorem colon_span_pair_desc (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB) :
    t ∈ Ideal.span {x, y} ↔ ∃ (α β : ZMod 2) (u v : Fin 4 → ZMod 2),
      t = α • x + β • y + colon_lin u * x + colon_lin v * y := by
  constructor
  · intro ht
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.1 ht
    simp only [smul_eq_mul] at hpq
    obtain ⟨p', hp', hp⟩ := colon_const_split p
    obtain ⟨q', hq', hq⟩ := colon_const_split q
    obtain ⟨p'', hp'', hp'eq⟩ := colon_deg_split p' hp'
    obtain ⟨q'', hq'', hq'eq⟩ := colon_deg_split q' hq'
    refine ⟨nf p (Sum.inl ()), nf q (Sum.inl ()),
      (fun k => nf p' (Sum.inr (Sum.inl k))), (fun k => nf q' (Sum.inr (Sum.inl k))), ?_⟩
    have hP : p = nf p (Sum.inl ()) • (1 : Balg)
        + (colon_lin (fun k => nf p' (Sum.inr (Sum.inl k))) + p'') := by
      rw [← hp'eq, ← hp]
    have hQ : q = nf q (Sum.inl ()) • (1 : Balg)
        + (colon_lin (fun k => nf q' (Sum.inr (Sum.inl k))) + q'') := by
      rw [← hq'eq, ← hq]
    have e1 : p'' * x = 0 := colon_sq_mul _ _ hp'' hx
    have e2 : q'' * y = 0 := colon_sq_mul _ _ hq'' hy
    have hpx : p * x = nf p (Sum.inl ()) • x
        + colon_lin (fun k => nf p' (Sum.inr (Sum.inl k))) * x := by
      conv_lhs => rw [hP]
      rw [add_mul, add_mul, e1, smul_mul_assoc, one_mul, add_zero]
    have hqy : q * y = nf q (Sum.inl ()) • y
        + colon_lin (fun k => nf q' (Sum.inr (Sum.inl k))) * y := by
      conv_lhs => rw [hQ]
      rw [add_mul, add_mul, e2, smul_mul_assoc, one_mul, add_zero]
    rw [← hpq, hpx, hqy]
    ring
  · rintro ⟨α, β, u, v, rfl⟩
    have hxs : x ∈ Ideal.span {x, y} := Ideal.subset_span (by simp)
    have hys : y ∈ Ideal.span {x, y} := Ideal.subset_span (by simp)
    exact Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.add_mem _ (colon_smul_mem _ hxs) (colon_smul_mem _ hys))
      (Ideal.mul_mem_left _ _ hxs)) (Ideal.mul_mem_left _ _ hys)

/-- The degree-one coordinate vector of an element of `B`. -/
def colon_co (x : Balg) : Fin 4 → ZMod 2 := fun k => nf x (Sum.inr (Sum.inl k))

/-- Degree-one coordinates of an `F₂`-scalar multiple. -/
@[simp] theorem colon_co_smul (c : ZMod 2) (x : Balg) : colon_co (c • x) = c • colon_co x := by
  funext k
  simp [colon_co]

/-- Degree-one coordinates of a sum. -/
@[simp] theorem colon_co_add (x y : Balg) : colon_co (x + y) = colon_co x + colon_co y := by
  funext k
  simp [colon_co]

/-- Degree-one coordinates of an element of `mB ^ 2` vanish. -/
theorem colon_co_of_mem_sq {w : Balg} (hw : w ∈ mB ^ 2) : colon_co w = 0 := by
  funext k
  exact (colon_mem_mB_sq_iff w).1 hw |>.2 k

/-- A product of two elements of `mB` lies in `mB ^ 2`. -/
theorem colon_mul_mem_sq {u w : Balg} (hu : u ∈ mB) (hw : w ∈ mB) : u * w ∈ mB ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul hu hw

/-- Degree-one coordinates of a product of two elements of `mB` vanish. -/
theorem colon_co_mul {u w : Balg} (hu : u ∈ mB) (hw : w ∈ mB) : colon_co (u * w) = 0 :=
  colon_co_of_mem_sq (colon_mul_mem_sq hu hw)

/-- The degree-one coordinates of `colon_lin s` are `s`. -/
@[simp] theorem colon_co_lin (s : Fin 4 → ZMod 2) : colon_co (colon_lin s) = s := by
  funext k
  simp [colon_co]

/-! ## `mB` is not generated by two elements -/

/-- The pigeonhole bound: `Fin 4` does not inject into the three nonzero pairs. -/
theorem colon_pigeon (f : Fin 4 → ZMod 2 × ZMod 2) (hinj : Function.Injective f)
    (hne : ∀ k, f k ≠ 0) : False := by
  have hcard : Fintype.card {p : ZMod 2 × ZMod 2 // p ≠ 0} = 3 := by decide
  have hle : Fintype.card (Fin 4) ≤ Fintype.card {p : ZMod 2 × ZMod 2 // p ≠ 0} :=
    Fintype.card_le_of_injective (fun k => ⟨f k, hne k⟩)
      (fun a b hab => hinj (congrArg Subtype.val hab))
  rw [hcard, Fintype.card_fin] at hle
  omega

/-- `mB` needs more than two generators: it is not contained in an ideal generated
by two elements of `mB`. This is the four-dimensionality of `mB / mB ^ 2`. -/
theorem colon_mB_not_two_gen (x y : Balg) (hx : x ∈ mB) (hy : y ∈ mB) :
    ¬ mB ≤ Ideal.span {x, y} := by
  intro hle
  have hgen : ∀ k : Fin 4, vvec k ∈ Ideal.span {x, y} := by
    intro k
    refine hle ?_
    rw [mB]
    refine Ideal.subset_span ?_
    fin_cases k <;> simp [vvec]
  have hco : ∀ k : Fin 4, ∃ p : ZMod 2 × ZMod 2,
      Pi.single k (1 : ZMod 2) = p.1 • colon_co x + p.2 • colon_co y := by
    intro k
    obtain ⟨α, β, u, v, heq⟩ := (colon_span_pair_desc x y (vvec k) hx hy).1 (hgen k)
    refine ⟨(α, β), ?_⟩
    have h1 : colon_co (vvec k) = Pi.single k (1 : ZMod 2) := by
      funext j
      rw [colon_co, colon_nf_vvec, Pi.single_apply, Pi.single_apply]
      simp [eq_comm]
    rw [← h1, heq]
    rw [colon_co_add, colon_co_add, colon_co_add, colon_co_smul, colon_co_smul,
      colon_co_mul (colon_lin_mem_mB u) hx, colon_co_mul (colon_lin_mem_mB v) hy]
    simp
  choose f hf using hco
  refine colon_pigeon f (fun k l hkl => ?_) (fun k hk => ?_)
  · have h := (hf k).trans (hkl ▸ (hf l).symm)
    by_contra hne
    have := congrFun h k
    simp [hne] at this
  · have := hf k
    rw [hk] at this
    have h2 := congrFun this k
    simp at h2

/-! ## The colon ideal -/

/-- Unfolding the colon ideal by `mB`. -/
theorem colon_mem_colonI_iff (I : Ideal Balg) (t : Balg) :
    t ∈ colonI I mB ↔ ∀ z ∈ mB, t * z ∈ I := by
  rw [colonI]
  simp [Submodule.mem_colon, smul_eq_mul]

/-- The easy inclusion `I ⊔ mB ^ 2 ≤ (I : mB)`: the first summand because `I` is an
ideal, the second because `mB ^ 3 = ⊥`. -/
theorem colon_le_colonI (I : Ideal Balg) : I ⊔ mB ^ 2 ≤ colonI I mB := by
  refine sup_le (fun t ht => ?_) (fun t ht => ?_)
  · exact (colon_mem_colonI_iff I t).2 fun z _ => Ideal.mul_mem_right _ _ ht
  · refine (colon_mem_colonI_iff I t).2 fun z hz => ?_
    rw [colon_sq_mul t z ht hz]
    exact I.zero_mem

/-- A unit vector is a nonzero degree-one element. -/
theorem colon_lin_single_ne_zero (k : Fin 4) : colon_lin (Pi.single k (1 : ZMod 2)) ≠ 0 := by
  intro h
  have := (colon_lin_eq_zero_iff _).1 h k
  simp at this

/-! ## The `I = ⊥` instance of the colon lemma -/

/-- The annihilator of the maximal ideal is `mB ^ 2`: the `I = ⊥` instance of the
Stage B colon lemma. -/
theorem colon_bot_eq : colonI (⊥ : Ideal Balg) mB = mB ^ 2 := by
  refine le_antisymm (fun t ht => ?_) ?_
  · have hmul : ∀ z ∈ mB, t * z = 0 := by
      intro z hz
      simpa using (colon_mem_colonI_iff ⊥ t).1 ht z hz
    have htm : t ∈ mB := by
      by_contra hcon
      obtain ⟨w, hw⟩ := (isUnit_of_not_mem_mB t hcon).exists_left_inv
      have h1 : vvec 0 = 0 := by
        have h2 : t * vvec 0 = 0 := hmul _ (by rw [mB]; exact Ideal.subset_span (by simp [vvec]))
        calc vvec 0 = w * (t * vvec 0) := by rw [← mul_assoc, hw, one_mul]
          _ = 0 := by rw [h2, mul_zero]
      rw [← colon_lin_single] at h1
      exact colon_lin_single_ne_zero 0 h1
    obtain ⟨w, hw, hteq⟩ := colon_deg_split t htm
    have hzero : colon_lin (fun k => nf t (Sum.inr (Sum.inl k))) = 0 := by
      have h0 : colon_lin (fun k => nf t (Sum.inr (Sum.inl k)))
          * colon_lin (Pi.single 0 (1 : ZMod 2)) = 0 := by
        have h1 : t * vvec 0 = 0 :=
          hmul _ (by rw [mB]; exact Ideal.subset_span (by simp [vvec]))
        rw [colon_lin_single]
        conv at h1 => rw [hteq]
        rw [add_mul, colon_sq_mul w (vvec 0) hw
          (by rw [mB]; exact Ideal.subset_span (by simp [vvec])), add_zero] at h1
        exact h1
      rcases colon_mul_inj_of_ne_zero _ _ h0 with h | h
      · exact h
      · exact absurd h (colon_lin_single_ne_zero 0)
    rw [hteq, hzero, zero_add]
    exact hw
  · intro t ht
    exact colon_le_colonI ⊥ (Submodule.mem_sup_right ht)

/-! ## Reduction of the colon lemma to the degree-one space -/

/-- The degree-one element of the zero vector is zero. -/
@[simp] theorem colon_lin_zero : colon_lin (0 : Fin 4 → ZMod 2) = 0 :=
  (colon_lin_eq_zero_iff _).2 fun _ => rfl

/-- `colon_lin` is additive. -/
theorem colon_lin_add (s z : Fin 4 → ZMod 2) :
    colon_lin (s + z) = colon_lin s + colon_lin z := by
  rw [colon_lin, colon_lin, colon_lin, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.add_apply, add_smul]

/-- Two degree-one elements with the same value have the same coordinates. -/
theorem colon_lin_injective : Function.Injective colon_lin := by
  intro s z hsz
  have h : colon_lin (s + z) = 0 := by
    rw [colon_lin_add, hsz]
    have h2 : ∀ w : Balg, w + w = 0 := by
      intro w
      have : w + w = 2 * w := by ring
      rw [this, B_two_eq_zero, zero_mul]
    exact h2 _
  funext k
  have := (colon_lin_eq_zero_iff _).1 h k
  simp only [Pi.add_apply] at this
  have hz : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide
  exact hz _ _ this

/-- Reduction step: an element of the colon ideal of a two-generated ideal
contained in `mB` lies in `mB`. -/
theorem colon_mem_mB_of_mem_colonI (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB)
    (ht : t ∈ colonI (Ideal.span {x, y}) mB) : t ∈ mB := by
  by_contra hcon
  obtain ⟨w, hw⟩ := (isUnit_of_not_mem_mB t hcon).exists_left_inv
  refine colon_mB_not_two_gen x y hx hy fun z hz => ?_
  have h1 : t * z ∈ Ideal.span {x, y} := (colon_mem_colonI_iff _ t).1 ht z hz
  have h2 : z = w * (t * z) := by rw [← mul_assoc, hw, one_mul]
  rw [h2]
  exact Ideal.mul_mem_left _ _ h1

/-- Reduction step: the degree-one part of an element of the colon ideal multiplies
the whole degree-one space into the ideal. -/
theorem colon_lin_mul_mem (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB)
    (ht : t ∈ colonI (Ideal.span {x, y}) mB) (z : Fin 4 → ZMod 2) :
    colon_lin (colon_co t) * colon_lin z ∈ Ideal.span {x, y} := by
  have htm : t ∈ mB := colon_mem_mB_of_mem_colonI x y t hx hy ht
  obtain ⟨w, hw, hteq⟩ := colon_deg_split t htm
  have hco : (fun k => nf t (Sum.inr (Sum.inl k))) = colon_co t := rfl
  rw [hco] at hteq
  have h1 : t * colon_lin z ∈ Ideal.span {x, y} :=
    (colon_mem_colonI_iff _ t).1 ht _ (colon_lin_mem_mB z)
  have h2 : w * colon_lin z = 0 := colon_sq_mul w _ hw (colon_lin_mem_mB z)
  rw [hteq, add_mul, h2, add_zero] at h1
  exact h1

/-! ## The colon lemma when both generators lie in `mB ^ 2` -/

/-- If both generators lie in `mB ^ 2`, the colon ideal is exactly `mB ^ 2`.
This is the degenerate case of the Stage B colon lemma in which the two
generators have vanishing degree-one part. -/
theorem colon_sq_case (x y t : Balg) (hx : x ∈ mB ^ 2) (hy : y ∈ mB ^ 2)
    (ht : t ∈ colonI (Ideal.span {x, y}) mB) : t ∈ mB ^ 2 := by
  have hxm : x ∈ mB := by
    have : mB ^ 2 ≤ mB := Ideal.pow_le_self (by norm_num)
    exact this hx
  have hym : y ∈ mB := by
    have : mB ^ 2 ≤ mB := Ideal.pow_le_self (by norm_num)
    exact this hy
  have htm : t ∈ mB := colon_mem_mB_of_mem_colonI x y t hxm hym ht
  obtain ⟨w, hw, hteq⟩ := colon_deg_split t htm
  have hco : (fun k => nf t (Sum.inr (Sum.inl k))) = colon_co t := rfl
  rw [hco] at hteq
  have hkey : ∀ z : Fin 4 → ZMod 2, ∃ p : ZMod 2 × ZMod 2,
      colon_lin (colon_co t) * colon_lin z = p.1 • x + p.2 • y := by
    intro z
    obtain ⟨α, β, u, v, heq⟩ := (colon_span_pair_desc x y _ hxm hym).1
      (colon_lin_mul_mem x y t hxm hym ht z)
    refine ⟨(α, β), ?_⟩
    have e1 : colon_lin u * x = 0 := by
      rw [mul_comm]
      exact colon_sq_mul x _ hx (colon_lin_mem_mB u)
    have e2 : colon_lin v * y = 0 := by
      rw [mul_comm]
      exact colon_sq_mul y _ hy (colon_lin_mem_mB v)
    rw [heq, e1, e2, add_zero, add_zero]
  choose g hg using hkey
  have hzero : colon_lin (colon_co t) = 0 := by
    by_contra hne
    have hinj : Function.Injective g := by
      intro z z' hzz
      have h1 : colon_lin (colon_co t) * colon_lin z
          = colon_lin (colon_co t) * colon_lin z' := by
        rw [hg z, hg z', hzz]
      have h2 : colon_lin (colon_co t) * colon_lin (z + z') = 0 := by
        rw [colon_lin_add, mul_add, h1]
        have h3 : ∀ u : Balg, u + u = 0 := by
          intro u
          have : u + u = 2 * u := by ring
          rw [this, B_two_eq_zero, zero_mul]
        exact h3 _
      rcases colon_mul_inj_of_ne_zero _ _ h2 with h | h
      · exact absurd h hne
      · have h4 : z + z' = 0 := colon_lin_injective (by rw [h, colon_lin_zero])
        have h5 : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide
        funext k
        exact h5 _ _ (congrFun h4 k)
    have hcard := Fintype.card_le_of_injective g hinj
    simp at hcard
  rw [hteq, hzero, zero_add]
  exact hw

/-! ## Guardrails -/

/-- Guardrail: the `I = 0` instance of the colon lemma. -/
example : colonI (⊥ : Ideal Balg) mB = mB ^ 2 := colon_bot_eq

/-- Guardrail: the pairwise intersection of two principal ideals is not zero. -/
example : xa * xb ∈ Ideal.span {xa} ⊓ Ideal.span {xb} :=
  ⟨Ideal.mul_mem_right _ _ (Ideal.subset_span rfl),
    Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)⟩

end

end Prob4b
