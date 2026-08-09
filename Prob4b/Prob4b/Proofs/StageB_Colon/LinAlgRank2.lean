/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b worker agent-iter3-4
-/
import Prob4b.Proofs.StageB_Colon.Basic

/-!
# Stage B — the rank-2 leaf of the colon lemma

This module discharges the *rank-2* finite-linear-algebra leaf of `BLUEPRINT.md`
Part 2 Stage B step B1.4, left open by the `⚠️` PROGRESS entry of
2026-08-09T18:02:38Z.

Everything here is a statement about the explicit `ZMod 2` multiplication table
`colon_mulc : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → (Fin 9 → ZMod 2)` of
`Prob4b/Proofs/StageB_Colon/Basic.lean`; no `Balg`, no ideals.

Main result:

* `lin2_not_mem_sum` — for `cx, cy` independent and `t ∉ span {cx, cy}` (spelled
  over `F₂` as `cx ≠ 0`, `cy ≠ 0`, `cx ≠ cy`, `t ≠ 0`, `t ≠ cx`, `t ≠ cy`,
  `t ≠ cx + cy`) there is a `z` with `colon_mulc t z ∉ Img cx + Img cy`.

The proof is by an explicit **dual certificate**. Write `V = (Fin 4 → ZMod 2)`
for the degree-one space and `W = (Fin 9 → ZMod 2)` for the degree-two space.
A vector `c : W` pairs with `colon_mulc s z` as the symmetric bilinear form
`M c` whose matrix has entries `M₀₀ = c₀`, `M₀₁ = c₁`, `M₀₂ = c₂`,
`M₀₃ = M₁₂ = c₃`, `M₁₁ = c₄`, `M₁₃ = c₅`, `M₂₂ = c₆`, `M₂₃ = c₇`, `M₃₃ = c₈`;
the identification `M₀₃ = M₁₂` is exactly the relation `ad = bc`, and it costs the
single linear constraint recorded by `lin2_Q`/`lin2_B` in `lin2_pair_mulc`.

A certificate killing `cx` and `cy` but not `t` is built from two vectors
`v, w` orthogonal to `cx, cy` with `v ⬝ t = 1` and `w ⬝ t = 0` (which exist
because `cx, cy, t` are independent — the two `decide`d finite facts
`lin2_exists_perp_aux` and `lin2_exists_perp_zero_aux`), as
`M = a·vvᵀ + b·(vwᵀ + wvᵀ)` with `(a, b) ∈ {(1,0), (0,1), (1,1)}` chosen so that
the constraint `a·Q(v) + b·B(v,w) = 0` holds.

All declarations carry the `lin2_` prefix, as required by the iteration's naming
rules.
-/

namespace Prob4b

/-! ## Coordinate bookkeeping in `Fin 4 → ZMod 2` -/

/-- The standard bilinear pairing on the degree-one space `V = Fin 4 → ZMod 2`. -/
def lin2_dot (v s : Fin 4 → ZMod 2) : ZMod 2 :=
  v 0 * s 0 + v 1 * s 1 + v 2 * s 2 + v 3 * s 3

/-- The standard pairing on the degree-two space `W = Fin 9 → ZMod 2`. -/
def lin2_pair (c q : Fin 9 → ZMod 2) : ZMod 2 :=
  c 0 * q 0 + c 1 * q 1 + c 2 * q 2 + c 3 * q 3 + c 4 * q 4 + c 5 * q 5 + c 6 * q 6 +
    c 7 * q 7 + c 8 * q 8

/-- The pairing on `W` is additive in its second argument. -/
theorem lin2_pair_add (c q q' : Fin 9 → ZMod 2) :
    lin2_pair c (q + q') = lin2_pair c q + lin2_pair c q' := by
  simp only [lin2_pair, Pi.add_apply]
  ring

/-- Two vectors of `V` agree iff their four coordinates do. -/
theorem lin2_funext (s z : Fin 4 → ZMod 2) :
    s = z ↔ s 0 = z 0 ∧ s 1 = z 1 ∧ s 2 = z 2 ∧ s 3 = z 3 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- In `ZMod 2` a nonzero scalar is `1`. -/
theorem lin2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert h
  revert c
  decide

/-- A nonzero vector of `V` has a coordinate equal to `1`. -/
theorem lin2_exists_one {s : Fin 4 → ZMod 2} (hs : s ≠ 0) : ∃ k : Fin 4, s k = 1 := by
  by_contra hcon
  simp only [not_exists] at hcon
  refine hs (funext fun k => ?_)
  have h : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  simpa using h _ (hcon k)

/-- In characteristic two a vanishing sum of two vectors means they are equal. -/
theorem lin2_eq_of_add_eq_zero {s z : Fin 4 → ZMod 2} (h : s + z = 0) : s = z := by
  funext i
  have hi : s i + z i = 0 := by simpa using congrFun h i
  have hc : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
  exact hc _ _ hi

/-- Over `F₂` the three conditions `cx ≠ 0`, `cy ≠ 0`, `cx ≠ cy` are exactly
linear independence of `cx` and `cy`: the only vanishing combination is the
trivial one. -/
theorem lin2_smul_eq_zero {cx cy : Fin 4 → ZMod 2} (h1 : cx ≠ 0) (h2 : cy ≠ 0)
    (h3 : cx ≠ cy) {a b : ZMod 2} (h : a • cx + b • cy = 0) : a = 0 ∧ b = 0 := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · exact ⟨ha, hb⟩
  · rw [ha, lin2_eq_one_of_ne_zero hb, zero_smul, one_smul, zero_add] at h
    exact absurd h h2
  · rw [hb, lin2_eq_one_of_ne_zero ha, zero_smul, one_smul, add_zero] at h
    exact absurd h h1
  · rw [lin2_eq_one_of_ne_zero ha, lin2_eq_one_of_ne_zero hb, one_smul, one_smul] at h
    exact absurd (lin2_eq_of_add_eq_zero h) h3

/-- Evaluating `lin2_dot` against a standard basis vector reads off a coordinate. -/
theorem lin2_dot_single (p : Fin 4 → ZMod 2) (k : Fin 4) :
    lin2_dot p (Pi.single k 1) = p k := by
  fin_cases k <;> simp [lin2_dot]

/-! ## The dual certificate -/

/-- The `(i, j)` entry of the symmetric matrix `a·vvᵀ + b·(vwᵀ + wvᵀ)`. -/
def lin2_M (a b : ZMod 2) (v w : Fin 4 → ZMod 2) (i j : Fin 4) : ZMod 2 :=
  a * (v i * v j) + b * (v i * w j + w i * v j)

/-- The degree-two covector attached to the symmetric matrix `lin2_M a b v w`;
the entry at index `3` serves both the `ad` and the `bc` position. -/
def lin2_cert (a b : ZMod 2) (v w : Fin 4 → ZMod 2) : Fin 9 → ZMod 2 :=
  ![lin2_M a b v w 0 0, lin2_M a b v w 0 1, lin2_M a b v w 0 2, lin2_M a b v w 0 3,
    lin2_M a b v w 1 1, lin2_M a b v w 1 3, lin2_M a b v w 2 2, lin2_M a b v w 2 3,
    lin2_M a b v w 3 3]

/-- The defect of `vvᵀ` against the relation `ad = bc`. -/
def lin2_Q (v : Fin 4 → ZMod 2) : ZMod 2 := v 0 * v 3 - v 1 * v 2

/-- The defect of `vwᵀ + wvᵀ` against the relation `ad = bc`. -/
def lin2_B (v w : Fin 4 → ZMod 2) : ZMod 2 :=
  v 0 * w 3 + w 0 * v 3 - v 1 * w 2 - w 1 * v 2

set_option linter.unusedSimpArgs false in
/-- The key evaluation: pairing the certificate `lin2_cert a b v w` with the
degree-two coordinate vector `colon_mulc s z` computes the symmetric form
`a·(v ⬝ s)(v ⬝ z) + b·((v ⬝ s)(w ⬝ z) + (w ⬝ s)(v ⬝ z))`, up to the single
correction term coming from the identification `ad = bc`. -/
theorem lin2_pair_mulc (a b : ZMod 2) (v w s z : Fin 4 → ZMod 2) :
    lin2_pair (lin2_cert a b v w) (colon_mulc s z)
      = a * (lin2_dot v s * lin2_dot v z)
        + b * (lin2_dot v s * lin2_dot w z + lin2_dot w s * lin2_dot v z)
        + (a * lin2_Q v + b * lin2_B v w) * (s 1 * z 2 + s 2 * z 1) := by
  simp only [lin2_pair, lin2_cert, lin2_M, lin2_dot, lin2_Q, lin2_B, colon_mulc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-! ## The two finite existence facts -/

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 4000 in
/-- Scalar form of `lin2_exists_perp`: if `cx, cy, t` are linearly independent
over `F₂` there is a covector orthogonal to `cx` and `cy` but not to `t`. -/
theorem lin2_exists_perp_aux :
    ∀ x0 x1 x2 x3 y0 y1 y2 y3 t0 t1 t2 t3 : ZMod 2,
      ¬ (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0) →
      ¬ (y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0) →
      ¬ (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3) →
      ¬ (t0 = 0 ∧ t1 = 0 ∧ t2 = 0 ∧ t3 = 0) →
      ¬ (t0 = x0 ∧ t1 = x1 ∧ t2 = x2 ∧ t3 = x3) →
      ¬ (t0 = y0 ∧ t1 = y1 ∧ t2 = y2 ∧ t3 = y3) →
      ¬ (t0 = x0 + y0 ∧ t1 = x1 + y1 ∧ t2 = x2 + y2 ∧ t3 = x3 + y3) →
      ∃ v0 v1 v2 v3 : ZMod 2,
        v0 * x0 + v1 * x1 + v2 * x2 + v3 * x3 = 0 ∧
        v0 * y0 + v1 * y1 + v2 * y2 + v3 * y3 = 0 ∧
        v0 * t0 + v1 * t1 + v2 * t2 + v3 * t3 = 1 := by decide

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 4000 in
/-- Scalar form of `lin2_exists_perp_zero`: if `cx, cy, t` are linearly
independent over `F₂` there is a *nonzero* covector orthogonal to all three. -/
theorem lin2_exists_perp_zero_aux :
    ∀ x0 x1 x2 x3 y0 y1 y2 y3 t0 t1 t2 t3 : ZMod 2,
      ¬ (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0) →
      ¬ (y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0) →
      ¬ (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3) →
      ¬ (t0 = 0 ∧ t1 = 0 ∧ t2 = 0 ∧ t3 = 0) →
      ¬ (t0 = x0 ∧ t1 = x1 ∧ t2 = x2 ∧ t3 = x3) →
      ¬ (t0 = y0 ∧ t1 = y1 ∧ t2 = y2 ∧ t3 = y3) →
      ¬ (t0 = x0 + y0 ∧ t1 = x1 + y1 ∧ t2 = x2 + y2 ∧ t3 = x3 + y3) →
      ∃ w0 w1 w2 w3 : ZMod 2,
        ¬ (w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0) ∧
        w0 * x0 + w1 * x1 + w2 * x2 + w3 * x3 = 0 ∧
        w0 * y0 + w1 * y1 + w2 * y2 + w3 * y3 = 0 ∧
        w0 * t0 + w1 * t1 + w2 * t2 + w3 * t3 = 0 := by decide

/-- The seven `F₂` independence hypotheses, in scalar coordinates. -/
structure lin2_Indep (cx cy t : Fin 4 → ZMod 2) : Prop where
  /-- `cx ≠ 0` in coordinates. -/
  hx : ¬ (cx 0 = 0 ∧ cx 1 = 0 ∧ cx 2 = 0 ∧ cx 3 = 0)
  /-- `cy ≠ 0` in coordinates. -/
  hy : ¬ (cy 0 = 0 ∧ cy 1 = 0 ∧ cy 2 = 0 ∧ cy 3 = 0)
  /-- `cx ≠ cy` in coordinates. -/
  hxy : ¬ (cx 0 = cy 0 ∧ cx 1 = cy 1 ∧ cx 2 = cy 2 ∧ cx 3 = cy 3)
  /-- `t ≠ 0` in coordinates. -/
  ht : ¬ (t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0)
  /-- `t ≠ cx` in coordinates. -/
  htx : ¬ (t 0 = cx 0 ∧ t 1 = cx 1 ∧ t 2 = cx 2 ∧ t 3 = cx 3)
  /-- `t ≠ cy` in coordinates. -/
  hty : ¬ (t 0 = cy 0 ∧ t 1 = cy 1 ∧ t 2 = cy 2 ∧ t 3 = cy 3)
  /-- `t ≠ cx + cy` in coordinates. -/
  htxy : ¬ (t 0 = cx 0 + cy 0 ∧ t 1 = cx 1 + cy 1 ∧ t 2 = cx 2 + cy 2 ∧
    t 3 = cx 3 + cy 3)

/-- Vector form of `lin2_exists_perp_aux`. -/
theorem lin2_exists_perp {cx cy t : Fin 4 → ZMod 2} (h : lin2_Indep cx cy t) :
    ∃ v : Fin 4 → ZMod 2,
      lin2_dot v cx = 0 ∧ lin2_dot v cy = 0 ∧ lin2_dot v t = 1 := by
  obtain ⟨v0, v1, v2, v3, hA, hB, hC⟩ :=
    lin2_exists_perp_aux (cx 0) (cx 1) (cx 2) (cx 3) (cy 0) (cy 1) (cy 2) (cy 3)
      (t 0) (t 1) (t 2) (t 3) h.hx h.hy h.hxy h.ht h.htx h.hty h.htxy
  exact ⟨![v0, v1, v2, v3], by simpa [lin2_dot] using hA, by simpa [lin2_dot] using hB,
    by simpa [lin2_dot] using hC⟩

/-- Vector form of `lin2_exists_perp_zero_aux`. -/
theorem lin2_exists_perp_zero {cx cy t : Fin 4 → ZMod 2} (h : lin2_Indep cx cy t) :
    ∃ w : Fin 4 → ZMod 2,
      w ≠ 0 ∧ lin2_dot w cx = 0 ∧ lin2_dot w cy = 0 ∧ lin2_dot w t = 0 := by
  obtain ⟨w0, w1, w2, w3, hne, hA, hB, hC⟩ :=
    lin2_exists_perp_zero_aux (cx 0) (cx 1) (cx 2) (cx 3) (cy 0) (cy 1) (cy 2) (cy 3)
      (t 0) (t 1) (t 2) (t 3) h.hx h.hy h.hxy h.ht h.htx h.hty h.htxy
  refine ⟨![w0, w1, w2, w3], ?_, by simpa [lin2_dot] using hA,
    by simpa [lin2_dot] using hB, by simpa [lin2_dot] using hC⟩
  intro hzero
  exact hne (by simpa using (lin2_funext _ _).1 hzero)

/-! ## The certificate argument -/

/-- Given a dual certificate `(a, b, v, w)` satisfying the relation constraint
`a·Q(v) + b·B(v,w) = 0`, orthogonal to `cx` and `cy`, and with `a·v + b·w`
paired nontrivially against `t`, the product `colon_mulc t z` escapes
`Img cx + Img cy` for a suitable `z`. -/
theorem lin2_key (cx cy t v w : Fin 4 → ZMod 2) (a b : ZMod 2)
    (hvx : lin2_dot v cx = 0) (hvy : lin2_dot v cy = 0) (hvt : lin2_dot v t = 1)
    (hwx : lin2_dot w cx = 0) (hwy : lin2_dot w cy = 0) (hwt : lin2_dot w t = 0)
    (hK : a * lin2_Q v + b * lin2_B v w = 0)
    (hk : ∃ k : Fin 4, a * v k + b * w k = 1) :
    ∃ z : Fin 4 → ZMod 2, ∀ u u' : Fin 4 → ZMod 2,
      colon_mulc t z ≠ colon_mulc cx u + colon_mulc cy u' := by
  obtain ⟨k, hk⟩ := hk
  refine ⟨Pi.single k 1, fun u u' hcon => ?_⟩
  set c := lin2_cert a b v w with hc
  have e1 : lin2_pair c (colon_mulc t (Pi.single k 1)) = 1 := by
    rw [hc, lin2_pair_mulc, hvt, hwt, hK, lin2_dot_single, lin2_dot_single]
    linear_combination hk
  have e2 : lin2_pair c (colon_mulc cx u) = 0 := by
    rw [hc, lin2_pair_mulc, hvx, hwx, hK]
    ring
  have e3 : lin2_pair c (colon_mulc cy u') = 0 := by
    rw [hc, lin2_pair_mulc, hvy, hwy, hK]
    ring
  have hpair := congrArg (lin2_pair c) hcon
  rw [e1, lin2_pair_add, e2, e3, add_zero] at hpair
  exact one_ne_zero hpair

/-- **The rank-2 leaf of `B_colon_two_gen`.** If `cx, cy` are independent over
`F₂` and `t ∉ span {cx, cy}`, then the degree-two image of `t` is not contained
in the sum of the degree-two images of `cx` and `cy`: there is a `z` with
`colon_mulc t z ≠ colon_mulc cx u + colon_mulc cy v` for all `u, v`. -/
theorem lin2_not_mem_sum (cx cy t : Fin 4 → ZMod 2) (h1 : cx ≠ 0) (h2 : cy ≠ 0)
    (h3 : cx ≠ cy) (h4 : t ≠ 0) (h5 : t ≠ cx) (h6 : t ≠ cy) (h7 : t ≠ cx + cy) :
    ∃ z : Fin 4 → ZMod 2, ∀ u v : Fin 4 → ZMod 2,
      colon_mulc t z ≠ colon_mulc cx u + colon_mulc cy v := by
  have hI : lin2_Indep cx cy t :=
    { hx := fun hh => h1 ((lin2_funext _ _).2 (by simpa using hh))
      hy := fun hh => h2 ((lin2_funext _ _).2 (by simpa using hh))
      hxy := fun hh => h3 ((lin2_funext _ _).2 (by simpa using hh))
      ht := fun hh => h4 ((lin2_funext _ _).2 (by simpa using hh))
      htx := fun hh => h5 ((lin2_funext _ _).2 (by simpa using hh))
      hty := fun hh => h6 ((lin2_funext _ _).2 (by simpa using hh))
      htxy := fun hh => h7 ((lin2_funext _ _).2 (by simpa using hh)) }
  obtain ⟨v, hvx, hvy, hvt⟩ := lin2_exists_perp hI
  obtain ⟨w, hw0, hwx, hwy, hwt⟩ := lin2_exists_perp_zero hI
  have hv0 : v ≠ 0 := by
    intro hz
    rw [hz] at hvt
    simp [lin2_dot] at hvt
  by_cases hQ : lin2_Q v = 0
  · obtain ⟨k, hk⟩ := lin2_exists_one hv0
    refine lin2_key cx cy t v w 1 0 hvx hvy hvt hwx hwy hwt ?_ ⟨k, ?_⟩
    · rw [hQ]; ring
    · rw [hk]; ring
  · by_cases hB : lin2_B v w = 0
    · obtain ⟨k, hk⟩ := lin2_exists_one hw0
      refine lin2_key cx cy t v w 0 1 hvx hvy hvt hwx hwy hwt ?_ ⟨k, ?_⟩
      · rw [hB]; ring
      · rw [hk]; ring
    · have hQ1 : lin2_Q v = 1 := lin2_eq_one_of_ne_zero hQ
      have hB1 : lin2_B v w = 1 := lin2_eq_one_of_ne_zero hB
      have hvw : v + w ≠ 0 := by
        intro hz
        rw [lin2_eq_of_add_eq_zero hz, hwt] at hvt
        exact one_ne_zero hvt.symm
      obtain ⟨k, hk⟩ := lin2_exists_one hvw
      refine lin2_key cx cy t v w 1 1 hvx hvy hvt hwx hwy hwt ?_ ⟨k, ?_⟩
      · rw [hQ1, hB1]; decide
      · have hvwk : v k + w k = 1 := by simpa using hk
        linear_combination hvwk

/-- The degree-two multiplication table is symmetric. -/
theorem lin2_mulc_comm (s z : Fin 4 → ZMod 2) : colon_mulc s z = colon_mulc z s := by
  funext j
  fin_cases j <;> simp only [colon_mulc] <;> ring_nf

/-- The orientation of `lin2_not_mem_sum` in which the two ambient images are
written `colon_mulc u cx` and `colon_mulc v cy`, as they arise from
`colon_span_pair_desc`. -/
theorem lin2_not_mem_sum' (cx cy t : Fin 4 → ZMod 2) (h1 : cx ≠ 0) (h2 : cy ≠ 0)
    (h3 : cx ≠ cy) (h4 : t ≠ 0) (h5 : t ≠ cx) (h6 : t ≠ cy) (h7 : t ≠ cx + cy) :
    ∃ z : Fin 4 → ZMod 2, ∀ u v : Fin 4 → ZMod 2,
      colon_mulc t z ≠ colon_mulc u cx + colon_mulc v cy := by
  obtain ⟨z, hz⟩ := lin2_not_mem_sum cx cy t h1 h2 h3 h4 h5 h6 h7
  refine ⟨z, fun u v => ?_⟩
  rw [lin2_mulc_comm u cx, lin2_mulc_comm v cy]
  exact hz u v

/-! ## Guardrail

The hypotheses of `lin2_not_mem_sum` are satisfiable — `a`, `b`, `c` are an
independent triple — so the statement is not vacuous. -/

example : ∃ z : Fin 4 → ZMod 2, ∀ u v : Fin 4 → ZMod 2,
    colon_mulc ![0, 0, 1, 0] z
      ≠ colon_mulc ![1, 0, 0, 0] u + colon_mulc ![0, 1, 0, 0] v :=
  lin2_not_mem_sum _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end Prob4b
