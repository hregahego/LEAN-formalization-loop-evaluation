import Mathlib

/-!
# Definitions (FROZEN)

Every object the formalization needs, in dependency order, following
`BLUEPRINT.md` Part −1 §2.  This file is **frozen**: its SHA-256 is pinned in
`scripts/frozen.sha256` and it must never be edited during the proving phase.

`USER_NOTES.md` permits **no** assumed-certificate axioms, so this file declares
no `axiom` whatsoever and `scripts/ALLOWED_AXIOMS.txt` is empty.
-/

namespace TreeIrred

/-! ## D1 — the labelled rooted weighted tree -/

/-- A finite weighted tree, presented as a labelled rooted inductive tree: each
node carries a vertex `label : ℕ` and a `weight : ℤ`, and a list of child
subtrees.  Genuine tree-hood (pairwise distinct labels) is *not* baked in; it is
the hypothesis `(verts T).Nodup` wherever it is needed. -/
inductive RTree : Type
  | node (label : ℕ) (weight : ℤ) (children : List RTree)

/-- The label of the root. -/
def RTree.root : RTree → ℕ
  | .node a _ _ => a

/-- The weight of the root. -/
def RTree.wtRoot : RTree → ℤ
  | .node _ w _ => w

/-- The list of child subtrees of the root. -/
def RTree.kids : RTree → List RTree
  | .node _ _ c => c

/-! ## D2 — the induction principle -/

/-- The "root + all children" induction principle: the auto-generated
`RTree.rec` for a nested inductive carries two motives, and this packages it in
the shape every proof in this project uses (`induction T using RTree.recAll`).

Built from `RTree.rec` with `motive_2 := fun c => ∀ t ∈ c, motive t`.  Since
`motive` may land in an arbitrary `Sort*`, the cons case decides `t = hd`
classically, which is why this is `noncomputable`; it is only ever used to build
proofs. -/
@[elab_as_elim]
noncomputable def RTree.recAll {motive : RTree → Sort*}
    (h : ∀ a w c, (∀ t ∈ c, motive t) → motive (.node a w c)) : ∀ t, motive t :=
  RTree.rec (motive_1 := motive) (motive_2 := fun c => ∀ t ∈ c, motive t)
    (fun a w c ih => h a w c ih)
    (fun t ht => absurd ht (by simp))
    (fun hd tl ihd itl t ht => by
      by_cases hth : t = hd
      · subst hth; exact ihd
      · exact itl t (by simpa [hth] using ht))

/-! ## D3 — the vertex data -/

/-- The list of `(label, weight)` pairs of all vertices, root first. -/
def vwts : RTree → List (ℕ × ℤ)
  | .node a w c => (a, w) :: c.attach.flatMap (fun t => vwts t.1)
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem t.2
  omega

/-- The list of vertex labels. -/
def verts (T : RTree) : List ℕ := (vwts T).map Prod.fst

/-- The weight of the vertex labelled `u`, read off `vwts` with default `0`
outside `verts T` (where it is never read). -/
def wt (T : RTree) (u : ℕ) : ℤ := ((vwts T).lookup u).getD 0

/-! ## D4 — the unrooted combinatorics -/

/-- The edge list, each edge listed **once**, oriented parent → child. -/
def edges : RTree → List (ℕ × ℕ)
  | .node a _ c => c.map (fun t => (a, t.root)) ++ c.attach.flatMap (fun t => edges t.1)
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem t.2
  omega

/-- Adjacency: `edges` symmetrised. -/
def Adj (T : RTree) (u v : ℕ) : Prop := (u, v) ∈ edges T ∨ (v, u) ∈ edges T

/-- The degree `d_T u` of the **unrooted** tree: the number of incident edges.
Deliberately *not* "number of children (+1)"; that identity is a lemma. -/
def deg (T : RTree) (u : ℕ) : ℕ := (edges T).countP (fun e => e.1 = u || e.2 = u)

/-! ## D5 — admissible rooted trees -/

/-- `SKETCH.md`'s *admissible* rooted tree, with the positive-definiteness
clause **dropped** (it is proved, as `admissible_posDef`, not assumed): every
weight is at least `2` and `w x ≥ ch x + 1` at every vertex. -/
def Admissible : RTree → Prop
  | .node _ w c => 2 ≤ w ∧ (c.length : ℤ) + 1 ≤ w ∧ ∀ t ∈ c, Admissible t

/-! ## D6 — the lattice and its bilinear form -/

/-- The Gram bilinear form of `T` in the vertex basis, over any commutative
ring: diagonal weights minus the symmetrised edge contributions.  The edge
summand is symmetric under swapping the endpoints, which is what makes
re-rooting preserve the form on the nose. -/
def form {R : Type} [CommRing R] (T : RTree) (x y : ℕ → R) : R :=
  ((vwts T).map (fun p => (p.2 : R) * x p.1 * y p.1)).sum
    - ((edges T).map (fun e => x e.1 * y e.2 + x e.2 * y e.1)).sum

/-- The form on the integral lattice `L T`. -/
abbrev B (T : RTree) (x y : ℕ → ℤ) : ℤ := form T x y

/-- The form on `L T ⊗ ℚ`. -/
abbrev BQ (T : RTree) (x y : ℕ → ℚ) : ℚ := form T x y

/-- The basis vector of the vertex labelled `u`. -/
def basis {R : Type} [CommRing R] (u : ℕ) : ℕ → R := fun v => if v = u then 1 else 0

/-! ## D7 — lattice-relative predicates -/

/-- `x ≠ 0` **in `L T`**: nonzero at some vertex *of `T`*.  Junk supported off
the tree is zero in `L T` even though it is nonzero as a function. -/
def NonzeroOn (T : RTree) (x : ℕ → ℤ) : Prop := ∃ u ∈ verts T, x u ≠ 0

/-- Positive definiteness of the form, stated over `ℤ`. -/
def PosDef (T : RTree) : Prop := ∀ x : ℕ → ℤ, NonzeroOn T x → 0 < B T x x

/-- `x` is reducible in `L T`: it splits **on `verts T`** as `a + b` with both
parts nonzero in `L T` and `B T a b ≥ 0`. -/
def Reducible (T : RTree) (x : ℕ → ℤ) : Prop :=
  ∃ a b : ℕ → ℤ, NonzeroOn T a ∧ NonzeroOn T b ∧
    (∀ u ∈ verts T, x u = a u + b u) ∧ 0 ≤ B T a b

/-- `x` is irreducible in `L T`. -/
def Irred (T : RTree) (x : ℕ → ℤ) : Prop := ¬ Reducible T x

/-! ## D8 — the capacity -/

/-- The capacity `γ C`, defined by the Schur recursion
`γ (node w c) = 1 / (w - Σ γ cᵢ)`.  Its identification with `(Q_C⁻¹) ρ ρ` is
owed as the frozen theorem `capacity_spec`. -/
def gamma : RTree → ℚ
  | .node _ w c => 1 / ((w : ℚ) - (c.attach.map (fun t => gamma t.1)).sum)
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem t.2
  omega

/-! ## D9 — reducibility in an abstract integral lattice -/

/-- Reducibility in an abstract integral lattice `(M, F)`.  Here `a ≠ 0` really
is the group's zero: there is no ambient vertex set. -/
def LatRed {M : Type} [AddCommGroup M] (F : M → M → ℤ) (x : M) : Prop :=
  ∃ a b : M, a ≠ 0 ∧ b ≠ 0 ∧ x = a + b ∧ 0 ≤ F a b

/-- Irreducibility in an abstract integral lattice `(M, F)`. -/
def LatIrred {M : Type} [AddCommGroup M] (F : M → M → ℤ) (x : M) : Prop := ¬ LatRed F x

end TreeIrred
