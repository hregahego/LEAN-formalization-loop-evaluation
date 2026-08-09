/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b worker agent-iter2-4
-/
import Prob4b.Proofs.StageA_Algebra.Basic
import Prob4b.Proofs.StageA_Algebra.NormalForm
import Prob4b.Proofs.StageB_Colon.TripleInter
import Prob4b.Proofs.StageB_Colon.ColonAssembly

/-!
# Stage C — the module `M = B⁴ / Bv`

This file delivers the parts of Stage C that depend on Stage A alone:

* **C0** the presentation lemmas `mem_Nsub` and `smulTop_span_singleton_mem`;
* **C3** `M_u_mem_triple_proof` (frozen theorem 10), via the three explicit
  witnesses frozen in the D3 modeling decision;
* **C4** `M_u_ne_zero_proof` (frozen theorem 9), a genuine non-membership
  `![0, ab + b², 0, bc + bd] ∉ Bv` computed through the normal form `nf`.

Iteration 3 adds **C5** `M_triple_defect_proof` (frozen theorem 11), on top of
Stage B's `B_triple_inter_eq_bot_proof`.

Iteration 4 adds the rest of **C0** (`mu_ann_vvec`, i.e. `(0 : v) = m²`) and
**C1**/**C2**: `mu_ann_eq_of_colon` and `mu_pair_inter_of_colon`, stated with
frozen theorem 5 as an explicit hypothesis, and then the unconditional
`M_ann_eq_proof` / `M_pair_inter_proof` (frozen theorems 7 and 8) obtained by
feeding them Stage B's `B_colon_two_gen_proof`.
-/

open MvPolynomial

namespace Prob4b

noncomputable section

/-! ## C0 — presentation lemmas -/

/-- Membership in the cyclic submodule `Bv ⊆ B⁴`. -/
theorem mem_Nsub (w : Fin 4 → Balg) : w ∈ Nsub ↔ ∃ t : Balg, w = t • vvec := by
  rw [Nsub, Submodule.mem_span_singleton]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

/-- The `D0` shape for `xM`: an element of `M` lies in `x·M` exactly when it is
`x • n` for some `n : M`. -/
theorem smulTop_span_singleton_mem (x : Balg) (m : Mmod) :
    m ∈ (smulTop (Ideal.span {x}) : Submodule Balg Mmod) ↔ ∃ n : Mmod, x • n = m := by
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr n _
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
      exact ⟨s • n, by rw [mul_smul]⟩
    · rintro m₁ m₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩
      exact ⟨n₁ + n₂, by rw [smul_add]⟩
  · rintro ⟨n, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) Submodule.mem_top

/-! ## C3 — the three witnesses for `u` -/

/-- The frozen representative of `u` in `B⁴`. -/
theorem mu_uElt_def :
    uElt = Submodule.Quotient.mk ![0, xa * xb + xb * xb, 0, xb * xc + xb * xd] := rfl

/-- Witness 1: `u = b · [(0, a + b, 0, c + d)]`, exact already in `B⁴`. -/
theorem mu_witness_xb :
    xb • (Submodule.Quotient.mk ![0, xa + xb, 0, xc + xd] : Mmod) = uElt := by
  have hv : (xb • ![0, xa + xb, 0, xc + xd] : Fin 4 → Balg)
      = ![0, xa * xb + xb * xb, 0, xb * xc + xb * xd] := by
    simp only [Matrix.smul_cons, Matrix.smul_empty, Matrix.vecCons_inj, smul_eq_mul, and_true]
    exact ⟨by ring, by ring, by ring, by ring⟩
  rw [mu_uElt_def, ← hv]
  rfl

/-- Witness 2: `u = (a + b) · [(0, b, 0, d)]`, exact in `B⁴` thanks to `ad = bc`. -/
theorem mu_witness_ab :
    (xa + xb) • (Submodule.Quotient.mk ![0, xb, 0, xd] : Mmod) = uElt := by
  have hv : ((xa + xb) • ![0, xb, 0, xd] : Fin 4 → Balg)
      = ![0, xa * xb + xb * xb, 0, xb * xc + xb * xd] := by
    simp only [Matrix.smul_cons, Matrix.smul_empty, Matrix.vecCons_inj, smul_eq_mul, and_true]
    refine ⟨by ring, by ring, by ring, ?_⟩
    linear_combination B_relation'
  rw [mu_uElt_def, ← hv]
  rfl

/-- Witness 3: `u = a · [(b, b, d, d)]`. This one holds only in the quotient: at
the level of `B⁴` the two vectors differ by `b • v ∈ Bv`. -/
theorem mu_witness_xa :
    xa • (Submodule.Quotient.mk ![xb, xb, xd, xd] : Mmod) = uElt := by
  have hv : (xa • ![xb, xb, xd, xd] : Fin 4 → Balg)
      - ![0, xa * xb + xb * xb, 0, xb * xc + xb * xd] = xb • vvec := by
    simp only [vvec, Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_sub_cons,
      Matrix.empty_sub_empty, Matrix.vecCons_inj, smul_eq_mul, and_true]
    refine ⟨by ring, ?_, ?_, ?_⟩
    · linear_combination (-(xb * xb)) * B_two_eq_zero
    · linear_combination B_relation'
    · linear_combination B_relation' - (xb * xd) * B_two_eq_zero
  have hmem : (xa • ![xb, xb, xd, xd] : Fin 4 → Balg)
      - ![0, xa * xb + xb * xb, 0, xb * xc + xb * xd] ∈ Nsub := by
    rw [hv, mem_Nsub]
    exact ⟨xb, rfl⟩
  rw [mu_uElt_def]
  exact (Submodule.Quotient.eq Nsub).2 hmem

/-- Frozen theorem 10: `u` lies in `aM ∩ bM ∩ (a+b)M`. -/
theorem M_u_mem_triple_proof :
    uElt ∈ (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) ⊓
      smulTop (Ideal.span {xb}) ⊓ smulTop (Ideal.span {xa + xb}) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (smulTop_span_singleton_mem xa uElt).2 ⟨_, mu_witness_xa⟩
  · exact (smulTop_span_singleton_mem xb uElt).2 ⟨_, mu_witness_xb⟩
  · exact (smulTop_span_singleton_mem (xa + xb) uElt).2 ⟨_, mu_witness_ab⟩

/-! ## C4 — `u ≠ 0`, computed through the normal form -/

/-- The class in `B` of the variable `X k`. -/
def gen (k : Fin 4) : Balg := Ideal.Quotient.mk relIdeal (X k)

@[simp] theorem gen_zero : gen 0 = xa := rfl

@[simp] theorem gen_one : gen 1 = xb := rfl

@[simp] theorem gen_two : gen 2 = xc := rfl

@[simp] theorem gen_three : gen 3 = xd := rfl

/-- `monB` of the constant index is `1`. -/
theorem mu_monB_inl : monB (Sum.inl ()) = 1 := by
  rw [monB, monoExp_inl]
  simp

/-- `monB` of a degree-1 index is the corresponding generator. -/
theorem mu_monB_lin (k : Fin 4) : monB (Sum.inr (Sum.inl k)) = gen k := by
  rw [monB, monoExp_lin, gen, X]

/-- Every generator lies in the maximal ideal `m`. -/
theorem mu_gen_mem_mB (k : Fin 4) : gen k ∈ mB := by
  have h : ({xa, xb, xc, xd} : Set Balg) ⊆ (mB : Set Balg) := Ideal.subset_span
  fin_cases k
  · exact h (by simp)
  · exact h (by simp)
  · exact h (by simp)
  · exact h (by simp)

/-- A degree-2 basis monomial times a generator vanishes: it is a product of
three elements of `m`, and `m³ = 0`. -/
theorem mu_monB_quad_mul (j : Fin 9) (k : Fin 4) :
    monB (Sum.inr (Sum.inr j)) * gen k = 0 := by
  have hmon : monB (Sum.inr (Sum.inr j)) = gen (deg2 j).1 * gen (deg2 j).2 := by
    rw [monB, monoExp_quad, gen, gen, mk_X_mul_mk_X]
  rw [hmon]
  exact mul_mem_mB_three (mu_gen_mem_mB _) (mu_gen_mem_mB _) (mu_gen_mem_mB k)

/-- Multiplication by a generator only sees the degree `≤ 1` part of `t`: the
degree-2 basis monomials are annihilated. -/
theorem mu_mul_gen (t : Balg) (k : Fin 4) :
    t * gen k = nf t (Sum.inl ()) • gen k
      + ∑ j : Fin 4, nf t (Sum.inr (Sum.inl j)) • (gen j * gen k) := by
  conv_lhs => rw [← sec_nf_apply t]
  rw [sec_apply, Finset.sum_mul, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h3 : ∑ j : Fin 9, nf t (Sum.inr (Sum.inr j)) • monB (Sum.inr (Sum.inr j)) * gen k
      = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_mul_assoc, mu_monB_quad_mul, smul_zero]
  rw [h3, add_zero]
  simp only [Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, mu_monB_inl,
    mu_monB_lin, smul_mul_assoc, one_mul]

/-- The `a²`-coordinate of `t · a` is the `a`-coordinate of `t`. -/
theorem mu_coeff_mul_xa (t : Balg) :
    nf (t * xa) (Sum.inr (Sum.inr 0)) = nf t (Sum.inr (Sum.inl 0)) := by
  rw [show xa = gen 0 from rfl, mu_mul_gen t 0]
  rw [map_add, map_smul, Fin.sum_univ_four, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul]
  simp only [gen_zero, gen_one, gen_two, gen_three, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, nf_xa, nf_xa_mul_xa]
  rw [show xb * xa = xa * xb from mul_comm _ _, show xc * xa = xa * xc from mul_comm _ _,
    show xd * xa = xa * xd from mul_comm _ _]
  simp only [nf_xa_mul_xb, nf_xa_mul_xc, nf_xa_mul_xd, adIdx]
  rw [Pi.single_eq_of_ne (by decide), Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide), Pi.single_eq_of_ne (by decide),
    Pi.single_eq_of_ne (by decide)]
  ring

/-- The `ab`-coordinate of `t · b` is the `a`-coordinate of `t`. -/
theorem mu_coeff_mul_xb (t : Balg) :
    nf (t * xb) (Sum.inr (Sum.inr 1)) = nf t (Sum.inr (Sum.inl 0)) := by
  rw [show xb = gen 1 from rfl, mu_mul_gen t 1]
  rw [map_add, map_smul, Fin.sum_univ_four, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul]
  simp only [gen_zero, gen_one, gen_two, gen_three, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, nf_xb, nf_xa_mul_xb, nf_xb_mul_xb]
  rw [show xc * xb = xb * xc from mul_comm _ _, show xd * xb = xb * xd from mul_comm _ _]
  simp only [nf_xb_mul_xc, nf_xb_mul_xd, adIdx]
  rw [Pi.single_eq_of_ne (by decide), Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide), Pi.single_eq_of_ne (by decide),
    Pi.single_eq_of_ne (by decide)]
  ring

/-- Frozen theorem 9: the defect element `u` is nonzero in `M`. -/
theorem M_u_ne_zero_proof : uElt ≠ 0 := by
  intro hzero
  rw [mu_uElt_def, Submodule.Quotient.mk_eq_zero] at hzero
  obtain ⟨t, ht⟩ := (mem_Nsub _).mp hzero
  have h0 : t * xa = 0 := by
    have := congrFun ht 0
    simpa [vvec, smul_eq_mul] using this.symm
  have h1 : t * xb = xa * xb + xb * xb := by
    have := congrFun ht 1
    simpa [vvec, smul_eq_mul] using this.symm
  have ha0 : nf t (Sum.inr (Sum.inl 0)) = 0 := by
    rw [← mu_coeff_mul_xa t, h0, map_zero, Pi.zero_apply]
  have ha1 : nf t (Sum.inr (Sum.inl 0)) = 1 := by
    rw [← mu_coeff_mul_xb t, h1, map_add, Pi.add_apply, nf_xa_mul_xb, nf_xb_mul_xb,
      Pi.single_eq_same, Pi.single_eq_of_ne (by decide)]
    ring
  rw [ha0] at ha1
  exact zero_ne_one ha1

/-! ## C5 — the triple defect in `M` -/

/-- `I · M = 0` when `I = ⊥`: the module side of `Submodule.bot_smul`. -/
theorem mu_smulTop_bot : (smulTop (⊥ : Ideal Balg) : Submodule Balg Mmod) = ⊥ :=
  Submodule.bot_smul _

/-- **C5** (frozen theorem 11). `M` does *not* preserve the triple intersection
`aB ∩ bB ∩ (a+b)B`: the left-hand side contains the nonzero element `u`, while
the right-hand side is `smulTop ⊥ = ⊥`. -/
theorem M_triple_defect_proof :
    (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) ⊓ smulTop (Ideal.span {xb}) ⊓
        smulTop (Ideal.span {xa + xb}) ≠
      smulTop (Ideal.span {xa} ⊓ Ideal.span {xb} ⊓ Ideal.span {xa + xb}) := by
  intro h
  have hu : uElt ∈ (smulTop (Ideal.span {xa} ⊓ Ideal.span {xb} ⊓
      Ideal.span {xa + xb}) : Submodule Balg Mmod) := h ▸ M_u_mem_triple_proof
  rw [B_triple_inter_eq_bot_proof, mu_smulTop_bot, Submodule.mem_bot] at hu
  exact M_u_ne_zero_proof hu

/-! ## C0 (continued) — the annihilator of `v`

Everything from here on is Iteration 4 work (BLUEPRINT Stage C steps C0/C1/C2).
Frozen theorem 5 (`B_colon_two_gen`) is still open, so the two targets carry it
as the explicit hypothesis

`hB1 : ∀ x y : Balg, colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2`

and are named `mu_ann_eq_of_colon` / `mu_pair_inter_of_colon`; the moment
frozen 5 lands they become frozen theorems 7 and 8 by instantiation.
-/

/-- Every coordinate of `v = (a, b, c, d)` lies in the maximal ideal `m`. -/
theorem mu_vvec_mem_mB (i : Fin 4) : vvec i ∈ mB := by
  have h : ({xa, xb, xc, xd} : Set Balg) ⊆ (mB : Set Balg) := Ideal.subset_span
  fin_cases i
  · exact h (by simp [vvec])
  · exact h (by simp [vvec])
  · exact h (by simp [vvec])
  · exact h (by simp [vvec])

/-- `m` is generated by the four coordinates of `v`, so an element multiplying
all of them into an ideal `I` multiplies the whole of `m` into `I`. -/
theorem mu_mul_mem_of_vvec (I : Ideal Balg) (t : Balg) (h : ∀ i, t * vvec i ∈ I) :
    ∀ z ∈ mB, t * z ∈ I := by
  have hA : t * xa ∈ I := h 0
  have hB : t * xb ∈ I := h 1
  have hC : t * xc ∈ I := h 2
  have hD : t * xd ∈ I := h 3
  intro z hz
  rw [mB] at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
      rcases hw with rfl | rfl | rfl | rfl
      exacts [hA, hB, hC, hD]
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact I.add_mem hu hv
  | smul r u _ hu =>
      rw [smul_eq_mul, show t * (r * u) = r * (t * u) by ring]
      exact I.mul_mem_left _ hu

/-- The colon form of `mu_mul_mem_of_vvec`. -/
theorem mu_mem_colonI_of_vvec (I : Ideal Balg) (t : Balg) (h : ∀ i, t * vvec i ∈ I) :
    t ∈ colonI I mB := by
  rw [colonI, Submodule.mem_colon]
  intro z hz
  rw [smul_eq_mul]
  exact mu_mul_mem_of_vvec I t h z hz

/-- **C0.** `(0 : v) = m²`: an element of `B` kills all four coordinates of `v`
exactly when it lies in `m²`. The forward direction is the `x = y = 0` instance
of frozen theorem 5, the backward one is `m³ = 0`. -/
theorem mu_ann_vvec
    (hB1 : ∀ x y : Balg, colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2)
    (t : Balg) : (∀ i, t * vvec i = 0) ↔ t ∈ mB ^ 2 := by
  constructor
  · intro h
    have h0 : t ∈ colonI (Ideal.span {(0 : Balg), 0}) mB :=
      mu_mem_colonI_of_vvec _ t fun i => by rw [h i]; exact Submodule.zero_mem _
    rw [hB1 0 0] at h0
    have hspan : (Ideal.span {(0 : Balg), 0} : Ideal Balg) = ⊥ := by simp
    rwa [hspan, bot_sup_eq] at h0
  · intro ht i
    have h3 : t * vvec i ∈ mB ^ 3 := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul ht (mu_vvec_mem_mB i)
    rw [B_maximalIdeal_pow_three_proof, Ideal.mem_bot] at h3
    exact h3

/-! ## C1 / C2 — `M` preserves annihilators and pairwise intersections -/

/-- Unfolding of `annM Mmod x`. -/
theorem mu_mem_annM (x : Balg) (m : Mmod) : m ∈ annM Mmod x ↔ x • m = 0 := by
  rw [annM, LinearMap.mem_ker, LinearMap.lsmul_apply]

/-- If every coordinate of `w : B⁴` lies in the ideal `J`, then the class of `w`
in `M` lies in `J·M`. -/
theorem mu_mk_mem_smulTop (J : Ideal Balg) (w : Fin 4 → Balg) (hw : ∀ i, w i ∈ J) :
    (Submodule.Quotient.mk w : Mmod) ∈ (smulTop J : Submodule Balg Mmod) := by
  have hsum : w = ∑ i : Fin 4, w i • (Pi.single i (1 : Balg)) := by
    funext j
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  have hmk : (Submodule.Quotient.mk w : Mmod) = Nsub.mkQ w := rfl
  rw [hmk, hsum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem_smul (hw i) Submodule.mem_top

/-- The class of `t • v` is zero in `M`. -/
theorem mu_mk_smul_vvec (t : Balg) : (Submodule.Quotient.mk (t • vvec) : Mmod) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact (mem_Nsub _).mpr ⟨t, rfl⟩

/-- **C1** = frozen theorem 7, modulo frozen theorem 5. `M` preserves
annihilators: `(0 :_M x) = (0 :_B x)·M` for every `x : B`. -/
theorem mu_ann_eq_of_colon
    (hB1 : ∀ x y : Balg, colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2) :
    ∀ x : Balg, annM Mmod x = smulTop (ann x) := by
  intro x
  refine le_antisymm ?_ ?_
  · intro m hm
    rw [mu_mem_annM] at hm
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective Nsub m
    have hxp : (x • p : Fin 4 → Balg) ∈ Nsub := by
      rw [← Submodule.Quotient.mk_eq_zero]
      rw [show (Submodule.Quotient.mk (x • p) : Mmod)
        = x • (Submodule.Quotient.mk p : Mmod) from rfl]
      exact hm
    obtain ⟨t, ht⟩ := (mem_Nsub _).mp hxp
    have hcoord : ∀ i, t * vvec i = x * p i := by
      intro i
      have := congrFun ht i
      simpa [Pi.smul_apply, smul_eq_mul] using this.symm
    have hcol : t ∈ colonI (Ideal.span {x, x}) mB := by
      refine mu_mem_colonI_of_vvec _ t fun i => ?_
      rw [hcoord i]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    rw [hB1 x x] at hcol
    obtain ⟨t₁, ht₁, z, hz, hteq⟩ := Submodule.mem_sup.mp hcol
    rw [Set.pair_eq_singleton, Ideal.mem_span_singleton'] at ht₁
    obtain ⟨s, hs⟩ := ht₁
    have hzv : ∀ i, z * vvec i = 0 := (mu_ann_vvec hB1 z).mpr hz
    have hkill : ∀ i, x * (p - s • vvec) i = 0 := by
      intro i
      have h1 : x * p i = t * vvec i := (hcoord i).symm
      have h2 : t * vvec i = s * x * vvec i := by
        rw [← hteq, ← hs, add_mul, hzv i, add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_sub, h1, h2]
      ring
    have hmem : (Submodule.Quotient.mk (p - s • vvec) : Mmod)
        ∈ (smulTop (ann x) : Submodule Balg Mmod) := by
      refine mu_mk_mem_smulTop _ _ fun i => ?_
      rw [mem_ann]
      rw [mul_comm]
      exact hkill i
    have hsplit : (Submodule.Quotient.mk (p - s • vvec) : Mmod)
        = Submodule.Quotient.mk p - Submodule.Quotient.mk (s • vvec) :=
      map_sub Nsub.mkQ p (s • vvec)
    have heq : (Submodule.Quotient.mk (p - s • vvec) : Mmod)
        = Submodule.Quotient.mk p := by
      rw [hsplit, mu_mk_smul_vvec, sub_zero]
    rwa [heq] at hmem
  · refine Submodule.smul_le.mpr fun r hr n _ => ?_
    rw [mu_mem_annM, smul_smul, mul_comm, (mem_ann x r).mp hr, zero_smul]

/-- **C2** = frozen theorem 8, modulo frozen theorem 5. `M` preserves pairwise
principal intersections: `xM ∩ yM = (xB ∩ yB)M`. -/
theorem mu_pair_inter_of_colon
    (hB1 : ∀ x y : Balg, colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2) :
    ∀ x y : Balg, (smulTop (Ideal.span {x}) : Submodule Balg Mmod) ⊓
        smulTop (Ideal.span {y}) =
      smulTop (Ideal.span {x} ⊓ Ideal.span {y}) := by
  intro x y
  refine le_antisymm ?_ ?_
  · rintro m ⟨hmx, hmy⟩
    obtain ⟨n₁, hn₁⟩ := (smulTop_span_singleton_mem x m).mp hmx
    obtain ⟨n₂, hn₂⟩ := (smulTop_span_singleton_mem y m).mp hmy
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective Nsub n₁
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective Nsub n₂
    have hdiff : (x • p - y • q : Fin 4 → Balg) ∈ Nsub := by
      rw [← Submodule.Quotient.mk_eq_zero]
      rw [show (Submodule.Quotient.mk (x • p - y • q) : Mmod)
        = Submodule.Quotient.mk (x • p) - Submodule.Quotient.mk (y • q) from
        map_sub Nsub.mkQ _ _]
      rw [show (Submodule.Quotient.mk (x • p) : Mmod)
        = x • (Submodule.Quotient.mk p : Mmod) from rfl]
      rw [show (Submodule.Quotient.mk (y • q) : Mmod)
        = y • (Submodule.Quotient.mk q : Mmod) from rfl]
      rw [hn₁, hn₂, sub_self]
    obtain ⟨t, ht⟩ := (mem_Nsub _).mp hdiff
    have hcoord : ∀ i, t * vvec i = x * p i - y * q i := by
      intro i
      have := congrFun ht i
      simpa [Pi.smul_apply, smul_eq_mul] using this.symm
    have hcol : t ∈ colonI (Ideal.span {x, y}) mB := by
      refine mu_mem_colonI_of_vvec _ t fun i => ?_
      rw [hcoord i]
      refine Submodule.sub_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    rw [hB1 x y] at hcol
    obtain ⟨t₁, ht₁, z, hz, hteq⟩ := Submodule.mem_sup.mp hcol
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp ht₁
    have hzv : ∀ i, z * vvec i = 0 := (mu_ann_vvec hB1 z).mpr hz
    have hxy : ∀ i, x * (p - α • vvec) i = y * (q + β • vvec) i := by
      intro i
      have h1 : t * vvec i = (α * x + β * y) * vvec i := by
        rw [← hteq, hαβ, add_mul, hzv i, add_zero]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h2 : x * p i - y * q i = (α * x + β * y) * vvec i := by
        rw [← hcoord i, h1]
      rw [mul_sub, mul_add]
      linear_combination h2
    have hm : m = Submodule.Quotient.mk (x • (p - α • vvec)) := by
      rw [show (Submodule.Quotient.mk (x • (p - α • vvec)) : Mmod)
        = x • (Submodule.Quotient.mk (p - α • vvec) : Mmod) from rfl]
      rw [show (Submodule.Quotient.mk (p - α • vvec) : Mmod)
        = Submodule.Quotient.mk p - Submodule.Quotient.mk (α • vvec) from
        map_sub Nsub.mkQ _ _]
      rw [mu_mk_smul_vvec, sub_zero, hn₁]
    rw [hm]
    refine mu_mk_mem_smulTop _ _ fun i => ?_
    have hval : (x • (p - α • vvec) : Fin 4 → Balg) i = x * (p - α • vvec) i := rfl
    rw [hval]
    refine ⟨?_, ?_⟩
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)
    · rw [hxy i]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self y)
  · exact le_inf (Submodule.smul_mono_left inf_le_left)
      (Submodule.smul_mono_left inf_le_right)

/-! ## C1 / C2 unconditionally

Frozen theorem 5 landed (as `B_colon_two_gen_proof`, in
`Prob4b/Proofs/StageB_Colon/ColonAssembly.lean`) while this file was being
written, so the hypothesis `hB1` can be discharged and the two targets become
frozen theorems 7 and 8 outright.
-/

/-- Frozen theorem 7: `M` preserves annihilators, `(0 :_M x) = (0 :_B x)·M`. -/
theorem M_ann_eq_proof : ∀ x : Balg, annM Mmod x = smulTop (ann x) :=
  mu_ann_eq_of_colon B_colon_two_gen_proof

/-- Frozen theorem 8: `M` preserves pairwise principal intersections,
`xM ∩ yM = (xB ∩ yB)M`. -/
theorem M_pair_inter_proof :
    ∀ x y : Balg, (smulTop (Ideal.span {x}) : Submodule Balg Mmod) ⊓
        smulTop (Ideal.span {y}) =
      smulTop (Ideal.span {x} ⊓ Ideal.span {y}) :=
  mu_pair_inter_of_colon B_colon_two_gen_proof

/-! ## Guardrail -/

/-- Guardrail (Stage C cheat-watch (f)): `aM` is not the zero submodule — if it
were, `M` would have collapsed. -/
example : (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) ≠ ⊥ := by
  intro h
  apply M_u_ne_zero_proof
  have hmem : uElt ∈ (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) :=
    M_u_mem_triple_proof.1.1
  rw [h] at hmem
  exact hmem

end

end Prob4b
