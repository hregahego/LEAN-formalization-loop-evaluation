import TreeIrred.Defs

/-!
# Frozen theorem statements

The complete list of the 13 frozen statements of `BLUEPRINT.md` Part −1 §3, all
`:= sorry`.  This file is **frozen**: its SHA-256 is pinned in
`scripts/frozen.sha256`.  Proofs live in `TreeIrred/Proofs/**`; the frozen
statements are re-exposed, proven, in `TreeIrred/Solution.lean`.
-/

namespace TreeIrred

-- 1 · model sanity: `form` really is the Gram matrix SKETCH.md describes
theorem form_gram_entries (T : RTree) (hnd : (verts T).Nodup) (u v : ℕ)
    (hu : u ∈ verts T) (hv : v ∈ verts T) :
    (u = v → B T (basis u) (basis v) = wt T u) ∧
    (u ≠ v → Adj T u v → B T (basis u) (basis v) = -1) ∧
    (u ≠ v → ¬ Adj T u v → B T (basis u) (basis v) = 0) := sorry

-- 2 · Lemma 1
theorem norm_one_irreducible {M : Type} [AddCommGroup M] (F : M → M → ℤ)
    (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
    (hsymm : ∀ x y : M, F x y = F y x)
    (hpd : ∀ x : M, x ≠ 0 → 0 < F x x)
    (x : M) (hx : F x x = 1) : LatIrred F x := sorry

-- 3 · Lemma 2, the capacity recursion
theorem capacity_node_formula (a : ℕ) (w : ℤ) (c : List RTree) :
    gamma (RTree.node a w c) = 1 / ((w : ℚ) - (c.map gamma).sum) := sorry

-- 4 · Lemma 2, the Schur denominator is positive
theorem capacity_denom_pos (C : RTree) (hC : Admissible C) :
    0 < (C.wtRoot : ℚ) - (C.kids.map gamma).sum := sorry

-- 5,6 · Lemma 2, 0 < γ(C) < 1
theorem capacity_pos (C : RTree) (hC : Admissible C) : 0 < gamma C := sorry

theorem capacity_lt_one (C : RTree) (hC : Admissible C) : gamma C < 1 := sorry

-- 7 · γ really is (Q_C⁻¹)_{ρρ}: the dual vector ρ# exists and has square γ
theorem capacity_spec (C : RTree) (hnd : (verts C).Nodup) (hC : Admissible C) :
    ∃ u : ℕ → ℚ, (∀ y : ℕ → ℚ, BQ C u y = y C.root) ∧ BQ C u u = gamma C := sorry

-- 8 · admissible ⇒ positive definite (the clause dropped from `Admissible`)
theorem admissible_posDef (C : RTree) (hC : Admissible C) : PosDef C := sorry

-- 9 · Lemma 3, the rooted estimate  ★ MILESTONE
theorem rooted_estimate (C : RTree) (hC : Admissible C) (x : ℕ → ℤ) (k : ℤ) :
    0 ≤ (B C x x : ℚ) - (2 * k + 1) * (x C.root : ℚ) + gamma C * k * (k + 1) := sorry

-- 10 · Corollary 1
theorem admissible_root_bound (C : RTree) (hC : Admissible C)
    (x : ℕ → ℤ) (hx : NonzeroOn C x) : 0 < B C x x - x C.root := sorry

-- 11 · re-rooting loses nothing
theorem exists_reroot_at (T : RTree) (u : ℕ) (hu : u ∈ verts T) :
    ∃ T' : RTree, T'.root = u ∧ (verts T').Perm (verts T) ∧
      (∀ v : ℕ, wt T' v = wt T v) ∧ (∀ v : ℕ, deg T' v = deg T v) ∧
      (∀ x y : ℕ → ℤ, B T' x y = B T x y) := sorry

-- 12 · Theorem 1 with the bad vertex at the root
theorem pointed_root_irreducible (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :
    ∃ u ∈ verts T, Irred T (basis u) := sorry

-- 13 · Theorem 1  ★ HEADLINE
theorem tree_has_irreducible_vertex (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (v : ℕ) (hv : v ∈ verts T)
    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :
    ∃ u ∈ verts T, Irred T (basis u) := sorry

end TreeIrred
