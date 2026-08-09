import TreeIrred.Proofs.Model.Basic
import TreeIrred.Proofs.Reroot.Basic
import TreeIrred.Proofs.Pointed.Basic

/-!
# Stage I -- the headline, bad vertex arbitrary

This file contains the whole mathematical content of frozen theorem #13
(`tree_has_irreducible_vertex`), *parameterised* on frozen theorem #12
(`pointed_root_irreducible`), which is being proved concurrently in
`TreeIrred/Proofs/Pointed/Basic.lean` and therefore may not be imported yet.

The route is BLUEPRINT Part 2, Stage I (I1--I2): re-root `T` at the bad vertex
`v` with the frozen `exists_reroot_at` (Stage G), transport `Nodup`, `PosDef`
and the "every non-root vertex is good" hypothesis to the re-rooted tree,
apply the pointed theorem there, and transport the resulting irreducible vertex
back.  All transport is along the `List.Perm` of vertex lists and the equality
of forms supplied by `exists_reroot_at`; per PROGRESS.md 2026-08-09T14:38:50Z we
never assume that a one-step pivot preserves `wt` -- the re-rooted tree comes
*only* from `exists_reroot_at_proof`.
-/

namespace TreeIrred

namespace Main

/-! ## Transport along a re-rooting -/

/-- `NonzeroOn` only sees the vertex *set*, so it transports along a permutation
of the vertex lists.  (Nonzero-ness is always relative to `verts`, never "`≠ 0`
as a function" -- BLUEPRINT trap 1.) -/
theorem nonzeroOn_transport {T T' : RTree} (hperm : (verts T').Perm (verts T))
    {x : ℕ → ℤ} (hx : NonzeroOn T x) : NonzeroOn T' x := by
  obtain ⟨u, hu, hne⟩ := hx
  exact ⟨u, hperm.mem_iff.mpr hu, hne⟩

/-- Positive definiteness transports along a re-rooting: the vertex lists are
permutations of one another and the forms are equal on all of `ℕ → ℤ`. -/
theorem posDef_transport {T T' : RTree} (hperm : (verts T').Perm (verts T))
    (hB : ∀ x y : ℕ → ℤ, B T' x y = B T x y) (hpd : PosDef T) : PosDef T' := by
  intro x hx
  rw [hB]
  exact hpd x (nonzeroOn_transport hperm.symm hx)

/-- Reducibility transports along a re-rooting, with the *same* witnesses `a`,
`b`.  The splitting condition stays the frozen "agreement on `verts`" form. -/
theorem reducible_transport {T T' : RTree} (hperm : (verts T').Perm (verts T))
    (hB : ∀ x y : ℕ → ℤ, B T' x y = B T x y) {x : ℕ → ℤ}
    (h : Reducible T x) : Reducible T' x := by
  obtain ⟨a, b, ha, hb, hsplit, hab⟩ := h
  refine ⟨a, b, nonzeroOn_transport hperm ha, nonzeroOn_transport hperm hb, ?_, ?_⟩
  · intro u hu
    exact hsplit u (hperm.mem_iff.mp hu)
  · rw [hB]
    exact hab

/-- Irreducibility transports *backwards* along a re-rooting. -/
theorem irred_transport {T T' : RTree} (hperm : (verts T').Perm (verts T))
    (hB : ∀ x y : ℕ → ℤ, B T' x y = B T x y) {x : ℕ → ℤ}
    (h : Irred T' x) : Irred T x := fun hred => h (reducible_transport hperm hB hred)

/-! ## The headline, parameterised on the pointed case -/

/-- Frozen theorem #13 `tree_has_irreducible_vertex`, with frozen theorem #12
`pointed_root_irreducible` taken as the hypothesis `hP` (written in arrow form).
Once `TreeIrred.pointed_root_irreducible_proof` lands, `hP` is discharged by it
and this closes the headline in one line.

`huniq` is used only through its `→` direction (a non-`v` vertex is not bad),
but the hypothesis itself is kept as the frozen iff at every vertex. -/
theorem tree_has_irreducible_vertex_of_pointed
    (hP : ∀ (T : RTree), (verts T).Nodup → PosDef T →
      (∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) →
      ∃ u ∈ verts T, Irred T (basis u))
    (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (v : ℕ) (hv : v ∈ verts T)
    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :
    ∃ u ∈ verts T, Irred T (basis u) := by
  -- I1: re-root at the bad vertex and transport every hypothesis.
  obtain ⟨T', hroot, hperm, hwt, hdeg, hB⟩ := exists_reroot_at_proof T v hv
  have hnd' : (verts T').Nodup := hperm.symm.nodup hnd
  have hpd' : PosDef T' := posDef_transport hperm hB hpd
  have hgood : ∀ u ∈ verts T', u ≠ T'.root → (deg T' u : ℤ) ≤ wt T' u := by
    intro u hu hne
    rw [hdeg, hwt]
    have hu' : u ∈ verts T := hperm.mem_iff.mp hu
    have hnb : ¬ wt T u < (deg T u : ℤ) := fun hlt => hne (hroot ▸ (huniq u hu').mp hlt)
    omega
  -- I2: apply the pointed theorem at `T'` and transport the witness back.
  obtain ⟨u, hu', hirr'⟩ := hP T' hnd' hpd' hgood
  exact ⟨u, hperm.mem_iff.mp hu', irred_transport hperm hB hirr'⟩

/-! ## Guardrails on a concrete 3-vertex path (`norm_num`, never `decide`) -/

/-- The 3-vertex path, rooted at the end labelled `0`; the bad vertex of the
guardrail is the other end, `2`. -/
private def P : RTree := .node 0 2 [.node 1 2 [.node 2 2 []]]

example : verts P = [0, 1, 2] := by norm_num [P]

example : (2 : ℕ) ∈ verts P := by norm_num [P]

/-- The transport of I1 really fires on a concrete tree: re-rooting `P` at the
vertex `2` yields a tree rooted there whose vertex list is still `Nodup` and
whose `deg`, `wt` and form agree with `P`'s, so `PosDef` transports. -/
example : ∃ T' : RTree, T'.root = 2 ∧ (verts T').Nodup ∧
    (∀ u : ℕ, deg T' u = deg P u) ∧ (∀ u : ℕ, wt T' u = wt P u) ∧
    (∀ x y : ℕ → ℤ, B T' x y = B P x y) ∧ (PosDef P → PosDef T') := by
  obtain ⟨T', hroot, hperm, hwt, hdeg, hB⟩ := exists_reroot_at_proof P 2 (by norm_num [P])
  exact ⟨T', hroot, hperm.symm.nodup (by norm_num [P]), hdeg, hwt, hB,
    fun h => posDef_transport hperm hB h⟩

/-- A 4-vertex star whose centre is the unique bad vertex: `wt = 2 < 3 = deg`
there, and every leaf has `wt = 5 > 1 = deg`. -/
private def S : RTree := .node 0 2 [.node 1 5 [], .node 2 5 [], .node 3 5 []]

private theorem S_verts : verts S = [0, 1, 2, 3] := by norm_num [S]

/-- The frozen `huniq` hypothesis really is satisfiable: `0` is the unique bad
vertex of the star `S`. -/
private theorem S_huniq : ∀ u ∈ verts S, (wt S u < (deg S u : ℤ) ↔ u = 0) := by
  have hw : vwts S = [(0, 2), (1, 5), (2, 5), (3, 5)] := by norm_num [S]
  have hv := S_verts
  have h0 : wt S 0 = 2 := by simp only [wt, hw]; rfl
  have h1 : wt S 1 = 5 := by simp only [wt, hw]; rfl
  have h2 : wt S 2 = 5 := by simp only [wt, hw]; rfl
  have h3 : wt S 3 = 5 := by simp only [wt, hw]; rfl
  have d0 : deg S 0 = 3 := by norm_num [S, deg, RTree.root]
  have d1 : deg S 1 = 1 := by norm_num [S, deg, RTree.root]
  have d2 : deg S 2 = 1 := by norm_num [S, deg, RTree.root]
  have d3 : deg S 3 = 1 := by norm_num [S, deg, RTree.root]
  intro u hu
  rw [hv] at hu
  fin_cases hu <;> norm_num [h0, h1, h2, h3, d0, d1, d2, d3]

/-- The re-rooting step of I1 is not vacuous: presented rooted at the leaf `1`,
the same star still has its unique bad vertex at `0`, which is *not* the root —
exactly the configuration `tree_has_irreducible_vertex_of_pointed` has to move
before the pointed theorem `hP` applies. -/
example : ∃ T' : RTree, T'.root = 1 ∧ (0 : ℕ) ≠ T'.root ∧
    ∀ u ∈ verts T', (wt T' u < (deg T' u : ℤ) ↔ u = 0) := by
  obtain ⟨T', hroot, hperm, hwt, hdeg, _⟩ :=
    exists_reroot_at_proof S 1 (by rw [S_verts]; norm_num)
  refine ⟨T', hroot, by simp [hroot], fun u hu => ?_⟩
  rw [hwt, hdeg]
  exact S_huniq u (hperm.mem_iff.mp hu)

end Main

/-! ## Frozen theorem #13 -/

/-- **Frozen theorem #13** (`TreeIrred/Theorems.lean`:68-71), Theorem 1 — the
headline.  `Main.tree_has_irreducible_vertex_of_pointed` carries the whole Stage-I
transport; its `hP` binder is the frozen `pointed_root_irreducible` (Stage H) in
arrow form, so Stage H's `pointed_root_irreducible_proof` closes it directly. -/
theorem tree_has_irreducible_vertex_proof (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (v : ℕ) (hv : v ∈ verts T)
    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :
    ∃ u ∈ verts T, Irred T (basis u) :=
  TreeIrred.Main.tree_has_irreducible_vertex_of_pointed
    TreeIrred.pointed_root_irreducible_proof T hnd hpd v hv huniq

end TreeIrred
