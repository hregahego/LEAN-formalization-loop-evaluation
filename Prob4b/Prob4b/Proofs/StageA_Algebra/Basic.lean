/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b SETUP agent
-/
import Prob4b.Defs

/-!
# Stage A — the algebra `B`: the relation, `m³ = 0`, Noetherianity

This module covers `BLUEPRINT.md` Part 2 Stage A steps A1, A2 and A5, together
with the D0 bridge lemma `mem_ann`.

Delivered here:

* `mem_ann` — the D0 bridge `y ∈ ann x ↔ y * x = 0`;
* `B_relation_proof` / `B_relation'` — the defining relation `ad + bc = 0`,
  in additive and in equational form;
* `mB_eq_map` — `mB` is the extension of `mPol` along the quotient map;
* `B_maximalIdeal_pow_three_proof` and its corollary `mul_mem_mB_three`;
* `B_isNoetherianRing_proof`.

The normal form `nf` / `basisB` and `B_nontrivial` live in a separate Stage A
module and are not used here.
-/

namespace Prob4b

/-! ## D0 — the annihilator bridge lemma -/

/-- The D0 bridge lemma: membership in the annihilator ideal `(0 : x)` is the
equation `y * x = 0`. Every later stage reads `ann` through this lemma. -/
theorem mem_ann {S : Type*} [CommRing S] (x y : S) : y ∈ ann x ↔ y * x = 0 := by
  rw [ann, colonI, Submodule.bot_colon, Submodule.mem_annihilator_span_singleton,
    smul_eq_mul]

/-! ## A1 — the defining relation -/

/-- `2 = 0` in the polynomial ring `F₂[a,b,c,d]`. -/
theorem Pol_two_eq_zero : (2 : Pol) = 0 := by
  have h : (2 : Pol) = MvPolynomial.C (2 : ZMod 2) := by
    rw [map_ofNat]
  rw [h, show (2 : ZMod 2) = 0 by decide, map_zero]

/-- `2 = 0` in `B`: the algebra has characteristic two, so `-x = x`. -/
theorem B_two_eq_zero : (2 : Balg) = 0 := by
  have h : (2 : Balg) = Ideal.Quotient.mk relIdeal (2 : Pol) := by
    rw [map_ofNat]
  rw [h, Pol_two_eq_zero, map_zero]

/-- In `B` every element is its own additive inverse. -/
theorem B_neg_eq (x : Balg) : -x = x := by
  have h : x + x = 0 := by rw [← two_mul, B_two_eq_zero, zero_mul]
  exact neg_eq_of_add_eq_zero_left h

/-- Frozen theorem 2: the defining relation `ad + bc = 0` holds in `B`. -/
theorem B_relation_proof : xa * xd + xb * xc = 0 := by
  have h : xa * xd + xb * xc =
      Ideal.Quotient.mk relIdeal
        (MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2) := by
    simp [xa, xb, xc, xd]
  rw [h, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))

/-- The equational form of the defining relation, `ad = bc`; this is the shape
every later stage rewrites with. -/
theorem B_relation' : xa * xd = xb * xc := by
  have h := eq_neg_of_add_eq_zero_left B_relation_proof
  rwa [B_neg_eq] at h

/-! ## A2 — `m³ = 0` -/

/-- `mB` is the extension of the irrelevant maximal ideal `mPol` along the
quotient map. -/
theorem mB_eq_map : mB = Ideal.map (Ideal.Quotient.mk relIdeal) mPol := by
  rw [mB, mPol, Ideal.map_span]
  congr 1
  simp [Set.image_insert_eq, xa, xb, xc, xd]

/-- Frozen theorem 4: the maximal ideal of `B` satisfies `m³ = 0`. Proved for
the ideal power `mB ^ 3`, which includes coefficients. -/
theorem B_maximalIdeal_pow_three_proof : mB ^ 3 = ⊥ := by
  rw [mB_eq_map, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact le_sup_left

/-- Corollary of `mB ^ 3 = ⊥`: any product of three elements of the maximal
ideal vanishes. -/
theorem mul_mem_mB_three {x y z : Balg} (hx : x ∈ mB) (hy : y ∈ mB) (hz : z ∈ mB) :
    x * y * z = 0 := by
  have h1 : x * y ∈ mB ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  have h2 : x * y * z ∈ mB ^ 3 := by
    have := Ideal.mul_mem_mul h1 hz
    rwa [← pow_succ] at this
  rw [B_maximalIdeal_pow_three_proof, Ideal.mem_bot] at h2
  exact h2

/-! ## A5 — Noetherianity -/

/-- Frozen theorem 3: `B` is a Noetherian ring, by the Hilbert basis theorem for
`Pol` transported along the surjection `Pol → B`. -/
theorem B_isNoetherianRing_proof : IsNoetherianRing Balg :=
  isNoetherianRing_of_surjective Pol Balg (Ideal.Quotient.mk relIdeal)
    Ideal.Quotient.mk_surjective

end Prob4b
