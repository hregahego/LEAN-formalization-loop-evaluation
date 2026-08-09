import TreeIrred.Defs

/-!
# Stage B -- Lemma 1 for an abstract integral lattice (`norm_one_irreducible`)

This file renders SKETCH.md Lemma 1 ("Norm-one elements are irreducible"):
in a positive definite *integral* lattice `(M, F)`, an element `x` with
`F x x = 1` is irreducible.

Everything stays at the abstract `AddCommGroup M` level: `M` is never
specialised, no `Module ℤ M`/freeness/finite-rank/`BilinForm` structure is
added, and the integrality step `0 < F a a → 1 ≤ F a a` is *derived* from the
codomain being `ℤ` rather than assumed.  See `BLUEPRINT.md` Part 2, Stage B.
-/

namespace TreeIrred

namespace NormOne

variable {M : Type} [AddCommGroup M] (F : M → M → ℤ)

/-- Additivity in the **second** argument, derived from additivity in the first
argument plus symmetry. -/
theorem add_right (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
    (hsymm : ∀ x y : M, F x y = F y x) (z u v : M) :
    F z (u + v) = F z u + F z v := by
  rw [hsymm z (u + v), hadd u v z, hsymm u z, hsymm v z]

/-- The binomial expansion `F (a+b) (a+b) = F a a + 2 * F a b + F b b`. -/
theorem expand_add (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
    (hsymm : ∀ x y : M, F x y = F y x) (a b : M) :
    F (a + b) (a + b) = F a a + 2 * F a b + F b b := by
  rw [hadd a b (a + b), add_right F hadd hsymm a a b, add_right F hadd hsymm b a b,
    hsymm b a]
  ring

end NormOne

/-- **Frozen theorem #2** (`TreeIrred.norm_one_irreducible`, SKETCH.md Lemma 1).
If `x = a + b` with `a, b ≠ 0` and `F a b ≥ 0`, then positive definiteness over
`ℤ` forces `F a a ≥ 1` and `F b b ≥ 1`, so `F x x ≥ 2`, contradicting
`F x x = 1`. -/
theorem norm_one_irreducible_proof {M : Type} [AddCommGroup M] (F : M → M → ℤ)
    (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
    (hsymm : ∀ x y : M, F x y = F y x)
    (hpd : ∀ x : M, x ≠ 0 → 0 < F x x)
    (x : M) (hx : F x x = 1) : LatIrred F x := by
  rintro ⟨a, b, ha, hb, rfl, hab⟩
  -- `0 < F a a` in `ℤ` *means* `1 ≤ F a a`; this integrality is the whole lemma.
  have ha' : 0 < F a a := hpd a ha
  have hb' : 0 < F b b := hpd b hb
  rw [NormOne.expand_add F hadd hsymm a b] at hx
  omega

end TreeIrred
