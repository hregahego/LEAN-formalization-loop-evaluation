/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b worker agent-iter3-3
-/
import Prob4b.Proofs.StageB_Colon.Basic

/-!
# Stage B — the rank-one leaf of the colon lemma

This module covers `BLUEPRINT.md` Part 2 Stage B step B1.4, the half named
`dim_inter_eq_two` there and `colon_dim_inter_le` in the `PROGRESS.md` entry of
2026-08-09T18:02:38Z.

The statement is a purely finite fact about the explicit `F₂`-multiplication table
`colon_mulc : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → (Fin 9 → ZMod 2)` of
`Prob4b/Proofs/StageB_Colon/Basic.lean`: writing `V = ⟨a,b,c,d⟩` and `W` for the
nine-dimensional degree-two part of `B`, for `s ≠ s'` nonzero in `V` the subspace
`{z | s·z ∈ s'·V}` has at most four elements, i.e. `dim (s·V ⊓ s'·V) ≤ 2`.

Delivered here:

* `lin1_inter_card_le` — the target above;
* `lin1_rank_one_case` — the rank-one sub-case of frozen theorem 5 that it settles.

**Implementation note (measured).** A `decide` on the statement in its `ZMod 2`
form is out of reach for the kernel: every `ZMod 2` operation is a `Nat.mod` behind
several instance projections, and the enumeration ranges over `16³` triples with an
inner span-membership search. Everything is therefore mirrored into `Nat` bit
masks (`lin1_mulN`), where the kernel's GMP-accelerated `Nat` operations make the
same enumeration cheap, and the two encodings are bridged by the 256-case
`lin1_spec`.  Every `decide` here is an ordinary kernel evaluation on `Nat` /
`ZMod 2` / `Fin n`; no compiler-backed evaluation is used anywhere.

All declarations carry the `lin1_` prefix, as required by the iteration's naming
rules.
-/

namespace Prob4b

/-! ## A `Nat` bit-mask mirror of the multiplication table -/

/-- Bit `i` of the natural number `n`, as a natural number. -/
def lin1_bit (n i : Nat) : Nat := (n >>> i) &&& 1

/-- The `Nat` bit-mask mirror of `colon_mulc`: a degree-one vector is encoded as the
four-bit number `s₀ + 2s₁ + 4s₂ + 8s₃`, a degree-two vector as the corresponding
nine-bit number, and `lin1_mulN` computes the product in that encoding.  The nine
coefficients are exactly those of `colon_mulc`, with `bc` folded onto `ad` in the
fourth one. -/
def lin1_mulN (s z : Nat) : Nat :=
  (lin1_bit s 0 * lin1_bit z 0) % 2
  + 2 * ((lin1_bit s 0 * lin1_bit z 1 + lin1_bit s 1 * lin1_bit z 0) % 2)
  + 4 * ((lin1_bit s 0 * lin1_bit z 2 + lin1_bit s 2 * lin1_bit z 0) % 2)
  + 8 * ((lin1_bit s 0 * lin1_bit z 3 + lin1_bit s 3 * lin1_bit z 0
        + lin1_bit s 1 * lin1_bit z 2 + lin1_bit s 2 * lin1_bit z 1) % 2)
  + 16 * ((lin1_bit s 1 * lin1_bit z 1) % 2)
  + 32 * ((lin1_bit s 1 * lin1_bit z 3 + lin1_bit s 3 * lin1_bit z 1) % 2)
  + 64 * ((lin1_bit s 2 * lin1_bit z 2) % 2)
  + 128 * ((lin1_bit s 2 * lin1_bit z 3 + lin1_bit s 3 * lin1_bit z 2) % 2)
  + 256 * ((lin1_bit s 3 * lin1_bit z 3) % 2)

/-- The encoding of a degree-one coordinate vector as a four-bit natural number. -/
def lin1_e4 (s : Fin 4 → ZMod 2) : Nat :=
  (s 0).val + 2 * (s 1).val + 4 * (s 2).val + 8 * (s 3).val

/-- The encoding of a degree-two coordinate vector as a nine-bit natural number. -/
def lin1_e9 (v : Fin 9 → ZMod 2) : Nat :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val
    + 32 * (v 5).val + 64 * (v 6).val + 128 * (v 7).val + 256 * (v 8).val

set_option maxRecDepth 10000 in
/-- The encoding of a degree-one vector is a four-bit number. -/
theorem lin1_e4_lt (s : Fin 4 → ZMod 2) : lin1_e4 s < 16 := by
  revert s; decide

set_option maxRecDepth 10000 in
/-- The encoding of degree-one vectors is injective. -/
theorem lin1_e4_inj : Function.Injective lin1_e4 := by
  intro s z; revert s z; decide

/-- The zero vector has encoding `0`. -/
@[simp] theorem lin1_e4_zero : lin1_e4 (0 : Fin 4 → ZMod 2) = 0 := by
  decide

/-- A vector with encoding `0` is zero. -/
theorem lin1_e4_ne_zero {s : Fin 4 → ZMod 2} (hs : s ≠ 0) : lin1_e4 s ≠ 0 := by
  intro h
  exact hs (lin1_e4_inj (by rw [h, lin1_e4_zero]))

set_option maxRecDepth 10000 in
/-- The bridge between the two encodings: `lin1_mulN` computes `colon_mulc`. -/
theorem lin1_spec (s z : Fin 4 → ZMod 2) :
    lin1_e9 (colon_mulc s z) = lin1_mulN (lin1_e4 s) (lin1_e4 z) := by
  revert s z; decide

/-! ## The finite count in the cheap encoding -/

set_option maxRecDepth 10000 in
/-- The whole content of the rank-one leaf, checked in the `Nat` bit-mask
encoding: for two distinct nonzero degree-one vectors `a`, `b`, at most four of the
sixteen degree-one vectors `z` satisfy `a·z ∈ b·V`. -/
theorem lin1_countN : ∀ a < 16, ∀ b < 16, a ≠ 0 → b ≠ 0 → a ≠ b →
    ((Finset.range 16).filter
      (fun z => ∃ w ∈ Finset.range 16, lin1_mulN a z = lin1_mulN b w)).card ≤ 4 := by
  decide

/-! ## The rank-one leaf -/

/-- BLUEPRINT Stage B step B1.4 (`dim_inter_eq_two`): for `s ≠ s'` nonzero in the
degree-one space `V`, the subspace `{z ∈ V | s·z ∈ s'·V}` of `V` has at most four
elements.  Equivalently `dim (s·V ⊓ s'·V) ≤ 2`, since `z ↦ s·z` is injective
(`colon_mul_inj_of_ne_zero`). -/
theorem lin1_inter_card_le (s s' : Fin 4 → ZMod 2) (hs : s ≠ 0) (hs' : s' ≠ 0)
    (hne : s ≠ s') :
    (Finset.univ.filter (fun z => ∃ w, colon_mulc s z = colon_mulc s' w)).card ≤ 4 := by
  have hcount := lin1_countN (lin1_e4 s) (lin1_e4_lt s) (lin1_e4 s') (lin1_e4_lt s')
    (lin1_e4_ne_zero hs) (lin1_e4_ne_zero hs') (fun h => hne (lin1_e4_inj h))
  refine le_trans (Finset.card_le_card_of_injOn lin1_e4 ?_ ?_) hcount
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz
    obtain ⟨w, hw⟩ := hz.2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_range.2 (lin1_e4_lt z), lin1_e4 w, Finset.mem_range.2 (lin1_e4_lt w), ?_⟩
    rw [← lin1_spec, ← lin1_spec, hw]
  · exact fun a _ b _ h => lin1_e4_inj h

/-! ## Guardrails -/

set_option maxRecDepth 10000 in
/-- Guardrail: the bound of `lin1_inter_card_le` is sharp and the set it bounds is
not accidentally empty.  For `s = a` and `s' = b` the set is `{0, b, d, b + d}`:
`a·b` and `a·d = b·c` are the two independent elements of `a·V ⊓ b·V`, so the
intersection really has dimension two. -/
example : (Finset.univ.filter
    (fun z => ∃ w, colon_mulc ![1, 0, 0, 0] z = colon_mulc ![0, 1, 0, 0] w)).card = 4 := by
  decide

set_option maxRecDepth 10000 in
/-- Guardrail: the hypothesis `s ≠ s'` of `lin1_inter_card_le` is doing work — for
`s = s'` the set is all of `V`. -/
example : (Finset.univ.filter
    (fun z => ∃ w, colon_mulc ![1, 0, 0, 0] z = colon_mulc ![1, 0, 0, 0] w)).card = 16 := by
  decide

/-! ## Degree-two coordinates and bilinearity -/

/-- The degree-two coordinate vector of an element of `B`. -/
noncomputable def lin1_q (e : Balg) : Fin 9 → ZMod 2 := fun j => nf e (Sum.inr (Sum.inr j))

/-- Degree-two coordinates are additive. -/
@[simp] theorem lin1_q_add (e f : Balg) : lin1_q (e + f) = lin1_q e + lin1_q f := by
  funext j
  simp [lin1_q]

/-- Degree-two coordinates commute with `F₂`-scalars. -/
@[simp] theorem lin1_q_smul (c : ZMod 2) (e : Balg) : lin1_q (c • e) = c • lin1_q e := by
  funext j
  simp [lin1_q]

/-- The degree-two coordinates of a product of two degree-one elements are given by
the multiplication table `colon_mulc`. -/
theorem lin1_q_lin_mul (a b : Fin 4 → ZMod 2) :
    lin1_q (colon_lin a * colon_lin b) = colon_mulc a b := by
  funext j
  exact colon_nf_lin_mul_quad a b j

/-- `colon_mulc` is additive in its second argument. -/
theorem lin1_mulc_add_right (s z z' : Fin 4 → ZMod 2) :
    colon_mulc s (z + z') = colon_mulc s z + colon_mulc s z' := by
  rw [← lin1_q_lin_mul, ← lin1_q_lin_mul, ← lin1_q_lin_mul, colon_lin_add, mul_add, lin1_q_add]

/-- `colon_mulc` is symmetric. -/
theorem lin1_mulc_comm (s z : Fin 4 → ZMod 2) : colon_mulc s z = colon_mulc z s := by
  rw [← lin1_q_lin_mul, ← lin1_q_lin_mul, mul_comm]

/-- The two elements of `ZMod 2`. -/
theorem lin1_zmod_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- `colon_mulc` is additive in its first argument. -/
theorem lin1_mulc_add_left (s s' z : Fin 4 → ZMod 2) :
    colon_mulc (s + s') z = colon_mulc s z + colon_mulc s' z := by
  rw [← lin1_q_lin_mul, ← lin1_q_lin_mul, ← lin1_q_lin_mul, colon_lin_add, add_mul, lin1_q_add]

/-! ## The rank-one sub-case of the colon lemma -/

/-- The rank-one sub-case of frozen theorem 5 (`B_colon_two_gen`): if the second
generator has vanishing degree-one part, then the colon ideal of `Ideal.span {x, y}`
by `mB` is contained in `Ideal.span {x, y} ⊔ mB ^ 2`.

This is an explicitly-scoped sub-case lemma, not the frozen statement: the
hypothesis `colon_co y = 0` is exactly the rank condition, and the rank-two case is
handled elsewhere. -/
theorem lin1_rank_one_case (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB)
    (hcy : colon_co y = 0) (ht : t ∈ colonI (Ideal.span {x, y}) mB) :
    t ∈ Ideal.span {x, y} ⊔ mB ^ 2 := by
  have hy2 : y ∈ mB ^ 2 :=
    (colon_mem_mB_sq_iff y).2 ⟨(mem_mB_iff y).1 hy, fun k => congrFun hcy k⟩
  by_cases hcx : colon_co x = 0
  · have hx2 : x ∈ mB ^ 2 :=
      (colon_mem_mB_sq_iff x).2 ⟨(mem_mB_iff x).1 hx, fun k => congrFun hcx k⟩
    exact Submodule.mem_sup_right (colon_sq_case x y t hx2 hy2 ht)
  have htm : t ∈ mB := colon_mem_mB_of_mem_colonI x y t hx hy ht
  obtain ⟨w, hw, hteq⟩ := colon_deg_split t htm
  obtain ⟨wx, hwx, hxeq⟩ := colon_deg_split x hx
  have hcot : (fun k => nf t (Sum.inr (Sum.inl k))) = colon_co t := rfl
  have hcox : (fun k => nf x (Sum.inr (Sum.inl k))) = colon_co x := rfl
  rw [hcot] at hteq
  rw [hcox] at hxeq
  by_cases hst0 : colon_co t = 0
  · rw [hteq, hst0, colon_lin_zero, zero_add]
    exact Submodule.mem_sup_right hw
  by_cases hstx : colon_co t = colon_co x
  · have hlin : colon_lin (colon_co x) = x - wx := eq_sub_of_add_eq hxeq.symm
    have hrw : x - wx + w = x + (w - wx) := by ring
    rw [hteq, hstx, hlin, hrw]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.subset_span (by simp)))
      (Submodule.mem_sup_right (Submodule.sub_mem _ hw hwx))
  exfalso
  -- every degree-one `z` contributes a `β`-multiple of `y` plus an element of `cx · V`
  have key : ∀ z : Fin 4 → ZMod 2, ∃ (β : ZMod 2) (u : Fin 4 → ZMod 2),
      colon_mulc (colon_co t) z = β • lin1_q y + colon_mulc (colon_co x) u := by
    intro z
    obtain ⟨α, β, u, v, heq⟩ := (colon_span_pair_desc x y _ hx hy).1
      (colon_lin_mul_mem x y t hx hy ht z)
    have hα : α = 0 := by
      have h0 : colon_co (colon_lin (colon_co t) * colon_lin z) = 0 :=
        colon_co_mul (colon_lin_mem_mB _) (colon_lin_mem_mB z)
      rw [heq, colon_co_add, colon_co_add, colon_co_add, colon_co_smul, colon_co_smul,
        colon_co_mul (colon_lin_mem_mB u) hx, colon_co_mul (colon_lin_mem_mB v) hy, hcy] at h0
      simp only [smul_zero, add_zero] at h0
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hcx
      have h1 : α * colon_co x k = 0 := by
        have := congrFun h0 k
        simpa [Pi.smul_apply, smul_eq_mul] using this
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hk
    have e1 : colon_lin v * y = 0 := by
      rw [mul_comm]; exact colon_sq_mul y _ hy2 (colon_lin_mem_mB v)
    have e0 : colon_lin u * wx = 0 := by
      rw [mul_comm]; exact colon_sq_mul wx _ hwx (colon_lin_mem_mB u)
    have e2 : colon_lin u * x = colon_lin u * colon_lin (colon_co x) := by
      conv_lhs => rw [hxeq]
      rw [mul_add, e0, add_zero]
    rw [hα, e1, e2, zero_smul, zero_add, add_zero] at heq
    refine ⟨β, u, ?_⟩
    rw [← lin1_q_lin_mul, heq, lin1_q_add, lin1_q_smul, lin1_q_lin_mul, lin1_mulc_comm]
  -- the set of `z` with `β = 0` is a subspace of index at most two, so has at least
  -- eight elements; but it has at most four by `lin1_inter_card_le`
  have hcard : (Finset.univ.filter
      (fun z => ∃ w, colon_mulc (colon_co t) z = colon_mulc (colon_co x) w)).card ≤ 4 :=
    lin1_inter_card_le _ _ hst0 hcx hstx
  set K : Finset (Fin 4 → ZMod 2) := Finset.univ.filter
    (fun z => ∃ w, colon_mulc (colon_co t) z = colon_mulc (colon_co x) w) with hK
  have hmemK : ∀ z : Fin 4 → ZMod 2, z ∈ K ↔
      ∃ w, colon_mulc (colon_co t) z = colon_mulc (colon_co x) w := by
    intro z
    rw [hK, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ z, h⟩⟩
  have hbeta : ∀ z : Fin 4 → ZMod 2, z ∉ K → ∀ β : ZMod 2, ∀ u : Fin 4 → ZMod 2,
      colon_mulc (colon_co t) z = β • lin1_q y + colon_mulc (colon_co x) u → β = 1 := by
    intro z hz β u hzu
    rcases lin1_zmod_cases β with rfl | rfl
    · exact absurd ((hmemK z).2 ⟨u, by rw [hzu, zero_smul, zero_add]⟩) hz
    · rfl
  have hpsi : ∀ z₁ z₂ : Fin 4 → ZMod 2, z₁ ∉ K → z₂ ∉ K → z₁ + z₂ ∈ K := by
    intro z₁ z₂ h₁ h₂
    obtain ⟨β₁, u₁, e₁⟩ := key z₁
    obtain ⟨β₂, u₂, e₂⟩ := key z₂
    have hb₁ : β₁ = 1 := hbeta z₁ h₁ β₁ u₁ e₁
    have hb₂ : β₂ = 1 := hbeta z₂ h₂ β₂ u₂ e₂
    refine (hmemK _).2 ⟨u₁ + u₂, ?_⟩
    have hsum : colon_mulc (colon_co t) (z₁ + z₂)
        = (β₁ + β₂) • lin1_q y + colon_mulc (colon_co x) (u₁ + u₂) := by
      rw [lin1_mulc_add_right, e₁, e₂, lin1_mulc_add_right, add_smul]
      abel
    rw [hsum, hb₁, hb₂, (by decide : (1 : ZMod 2) + 1 = 0), zero_smul, zero_add]
  -- counting
  have h16 : (Finset.univ : Finset (Fin 4 → ZMod 2)).card = 16 := by decide
  have hsum : K.card + Kᶜ.card = 16 := by
    rw [Finset.card_add_card_compl K, ← Finset.card_univ, h16]
  rcases Finset.eq_empty_or_nonempty Kᶜ with hempty | ⟨z₁, hz₁⟩
  · rw [hempty, Finset.card_empty, Nat.add_zero] at hsum
    omega
  · have hz₁' : z₁ ∉ K := Finset.mem_compl.1 hz₁
    have hinj : (Kᶜ : Finset (Fin 4 → ZMod 2)).card ≤ K.card := by
      refine Finset.card_le_card_of_injOn (fun z => z + z₁) ?_ ?_
      · intro z hz
        exact Finset.mem_coe.2
          (hpsi z z₁ (Finset.mem_compl.1 (Finset.mem_coe.1 hz)) hz₁')
      · exact fun a _ b _ h => add_right_cancel h
    omega

/-! ## The full rank-at-most-one case -/

/-- Swapping the two generators of a two-generated ideal. -/
theorem lin1_span_pair_comm (x y : Balg) : Ideal.span {x, y} = Ideal.span {y, x} := by
  rw [Set.pair_comm]

/-- Replacing the second generator by `x + y`. -/
theorem lin1_span_pair_add (x y : Balg) : Ideal.span {x, x + y} = Ideal.span {x, y} := by
  have hx : x ∈ Ideal.span {x, y} := Ideal.subset_span (by simp)
  have hy : y ∈ Ideal.span {x, y} := Ideal.subset_span (by simp)
  have hx' : x ∈ Ideal.span {x, x + y} := Ideal.subset_span (by simp)
  have hxy' : x + y ∈ Ideal.span {x, x + y} := Ideal.subset_span (by simp)
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · refine Set.insert_subset hx (Set.singleton_subset_iff.2 (Ideal.add_mem _ hx hy))
  · refine Set.insert_subset hx' (Set.singleton_subset_iff.2 ?_)
    have h := Ideal.sub_mem (Ideal.span {x, x + y}) hxy' hx'
    have h2 : x + y - x = y := by ring
    rwa [h2] at h

/-- Adding an element of `Fin 4 → ZMod 2` to itself gives zero. -/
theorem lin1_add_self (v : Fin 4 → ZMod 2) : v + v = 0 := by
  funext k
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h (v k)

/-- The full rank-at-most-one case of frozen theorem 5 (`B_colon_two_gen`): whenever
the degree-one parts of the two generators are `F₂`-dependent, the colon ideal of
`Ideal.span {x, y}` by `mB` is contained in `Ideal.span {x, y} ⊔ mB ^ 2`.

Over `F₂` dependence of `colon_co x` and `colon_co y` means exactly
`colon_co x = 0 ∨ colon_co y = 0 ∨ colon_co x = colon_co y`, so what remains of the
hard inclusion of frozen theorem 5, after the unit case, is the rank-two case.
This is an explicitly-scoped sub-case lemma, not the frozen statement. -/
theorem lin1_rank_le_one_case (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB)
    (hdep : colon_co x = 0 ∨ colon_co y = 0 ∨ colon_co x = colon_co y)
    (ht : t ∈ colonI (Ideal.span {x, y}) mB) : t ∈ Ideal.span {x, y} ⊔ mB ^ 2 := by
  rcases hdep with hcx | hcy | hxy
  · rw [lin1_span_pair_comm] at ht ⊢
    exact lin1_rank_one_case y x t hy hx hcx ht
  · exact lin1_rank_one_case x y t hx hy hcy ht
  · have hy' : x + y ∈ mB := Ideal.add_mem _ hx hy
    have hcy' : colon_co (x + y) = 0 := by
      rw [colon_co_add, ← hxy, lin1_add_self]
    rw [← lin1_span_pair_add x y] at ht ⊢
    exact lin1_rank_one_case x (x + y) t hx hy' hcy' ht

end Prob4b
