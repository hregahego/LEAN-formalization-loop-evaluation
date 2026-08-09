import TreeIrred.Theorems
import TreeIrred.Proofs.Model.Basic
import TreeIrred.Proofs.NormOne.Basic
import TreeIrred.Proofs.Capacity.Basic
import TreeIrred.Proofs.Reroot.Basic
import TreeIrred.Proofs.PosDef.Basic
import TreeIrred.Proofs.RootedEstimate.Basic
import TreeIrred.Proofs.RootBound.Basic
import TreeIrred.Proofs.Pointed.Basic
import TreeIrred.Proofs.Main.Basic

/-!
# Solution

Each of the 13 frozen theorems of `TreeIrred/Theorems.lean` is to be restated
here **verbatim** in `namespace TreeIrred.Solution` and closed by the
corresponding sorry-free `<name>_proof` declaration from `TreeIrred/Proofs/**`.

`scripts/verify.py` checks that `#print axioms TreeIrred.Solution.<name>` is
clean for every frozen name, and generates the statement gates
`@TreeIrred.<name> = @TreeIrred.Solution.<name> := rfl`.

All thirteen are wired up below (Stages A, B, C, D, E, F, G, H, I): every frozen
name now has a sorry-free `<name>_proof` in `TreeIrred/Proofs/**`, and
`TreeIrred/Discharge.lean` carries the 24 matching `rfl` no-drift gates.
-/

namespace TreeIrred.Solution

-- 1 · model sanity: `form` really is the Gram matrix SKETCH.md describes
theorem form_gram_entries (T : RTree) (hnd : (verts T).Nodup) (u v : ℕ)
    (hu : u ∈ verts T) (hv : v ∈ verts T) :
    (u = v → B T (basis u) (basis v) = wt T u) ∧
    (u ≠ v → Adj T u v → B T (basis u) (basis v) = -1) ∧
    (u ≠ v → ¬ Adj T u v → B T (basis u) (basis v) = 0) :=
  TreeIrred.form_gram_entries_proof T hnd u v hu hv

-- 2 · Lemma 1
theorem norm_one_irreducible {M : Type} [AddCommGroup M] (F : M → M → ℤ)
    (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
    (hsymm : ∀ x y : M, F x y = F y x)
    (hpd : ∀ x : M, x ≠ 0 → 0 < F x x)
    (x : M) (hx : F x x = 1) : LatIrred F x :=
  TreeIrred.norm_one_irreducible_proof F hadd hsymm hpd x hx

-- 3 · Lemma 2, the capacity recursion
theorem capacity_node_formula (a : ℕ) (w : ℤ) (c : List RTree) :
    gamma (RTree.node a w c) = 1 / ((w : ℚ) - (c.map gamma).sum) :=
  TreeIrred.capacity_node_formula_proof a w c

-- 4 · Lemma 2, the Schur denominator is positive
theorem capacity_denom_pos (C : RTree) (hC : Admissible C) :
    0 < (C.wtRoot : ℚ) - (C.kids.map gamma).sum :=
  TreeIrred.capacity_denom_pos_proof C hC

-- 5,6 · Lemma 2, 0 < γ(C) < 1
theorem capacity_pos (C : RTree) (hC : Admissible C) : 0 < gamma C :=
  TreeIrred.capacity_pos_proof C hC

theorem capacity_lt_one (C : RTree) (hC : Admissible C) : gamma C < 1 :=
  TreeIrred.capacity_lt_one_proof C hC

-- 7 · γ really is (Q_C⁻¹)_{ρρ}: the dual vector ρ# exists and has square γ
theorem capacity_spec (C : RTree) (hnd : (verts C).Nodup) (hC : Admissible C) :
    ∃ u : ℕ → ℚ, (∀ y : ℕ → ℚ, BQ C u y = y C.root) ∧ BQ C u u = gamma C :=
  TreeIrred.capacity_spec_proof C hnd hC

-- 8 · admissible ⇒ positive definite (the clause dropped from `Admissible`)
theorem admissible_posDef (C : RTree) (hC : Admissible C) : PosDef C :=
  TreeIrred.admissible_posDef_proof C hC

-- 9 · Lemma 3, the rooted estimate  ★ MILESTONE
theorem rooted_estimate (C : RTree) (hC : Admissible C) (x : ℕ → ℤ) (k : ℤ) :
    0 ≤ (B C x x : ℚ) - (2 * k + 1) * (x C.root : ℚ) + gamma C * k * (k + 1) :=
  TreeIrred.rooted_estimate_proof C hC x k

-- 10 · Corollary 1
theorem admissible_root_bound (C : RTree) (hC : Admissible C)
    (x : ℕ → ℤ) (hx : NonzeroOn C x) : 0 < B C x x - x C.root :=
  TreeIrred.admissible_root_bound_proof C hC x hx

-- 11 · re-rooting loses nothing
theorem exists_reroot_at (T : RTree) (u : ℕ) (hu : u ∈ verts T) :
    ∃ T' : RTree, T'.root = u ∧ (verts T').Perm (verts T) ∧
      (∀ v : ℕ, wt T' v = wt T v) ∧ (∀ v : ℕ, deg T' v = deg T v) ∧
      (∀ x y : ℕ → ℤ, B T' x y = B T x y) :=
  TreeIrred.exists_reroot_at_proof T u hu

-- 12 · Theorem 1 with the bad vertex at the root
theorem pointed_root_irreducible (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :
    ∃ u ∈ verts T, Irred T (basis u) :=
  TreeIrred.pointed_root_irreducible_proof T hnd hpd hgood

-- 13 · Theorem 1  ★ HEADLINE
theorem tree_has_irreducible_vertex (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (v : ℕ) (hv : v ∈ verts T)
    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :
    ∃ u ∈ verts T, Irred T (basis u) :=
  TreeIrred.tree_has_irreducible_vertex_proof T hnd hpd v hv huniq

end TreeIrred.Solution
