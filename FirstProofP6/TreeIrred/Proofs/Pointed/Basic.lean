import TreeIrred.Proofs.Model.Basic
import TreeIrred.Proofs.NormOne.Basic
import TreeIrred.Proofs.Capacity.Basic
import TreeIrred.Proofs.PosDef.Basic
import TreeIrred.Proofs.RootedEstimate.Basic
import TreeIrred.Proofs.RootBound.Basic

/-!
# Stage H -- `pointed_root_irreducible`, modulo Stage F

Following `BLUEPRINT.md` Part 2 Stage H (items H1-H5) = `SKETCH.md` Theorem 1
(`SKETCH.md`:181-261).

* `Pointed.wt_pos` (H1) -- positive definiteness forces every weight positive;
* `Pointed.weight_one_irred` (H2) -- a vertex of weight `1` is irreducible;
* `Pointed.admissible_of_deg` (H3) -- the local degree/weight conditions of
  `SKETCH.md`:187-199 imply `Admissible`;
* `Pointed.schur_pos` (H4) -- the Schur positivity `0 < W - Σ γᵢ` at the root;
* `Pointed.pointed_root_irreducible_of_rootBound` (H5) -- the whole of the frozen
  `pointed_root_irreducible`, with the frozen `admissible_root_bound` (Stage F,
  `TreeIrred/Proofs/RootBound/Basic.lean`, being written concurrently and hence
  not importable here) taken as the hypothesis `hRB` in arrow form.  Feeding it
  `TreeIrred.admissible_root_bound_proof` closes the frozen statement in one
  line.

Throughout, "nonzero" is `NonzeroOn T ·` (nonzero *at some vertex of `T`*) and a
splitting is required only on `verts T`, exactly as `Defs.lean` D7 states them;
and `deg` stays the frozen unrooted `edges`-based `countP`, so the identity
`d_T(x) = ch(x) + 1` is *derived* from `deg_root`/`deg_subroot`, never assumed.
-/

namespace TreeIrred

namespace Pointed

/-! ## H1 -- positive definiteness makes every weight positive -/

/-- **H1.** In a positive definite tree every vertex weight is positive: the
diagonal Gram entry at `u` is `wt T u` and `basis u` is nonzero in `L T`. -/
theorem wt_pos (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T) :
    ∀ u ∈ verts T, 0 < wt T u := by
  intro u hu
  have hnz : NonzeroOn T (basis u) := ⟨u, hu, by simp [basis]⟩
  have h := hpd (basis u) hnz
  rwa [(form_gram_entries_proof T hnd u u hu hu).1 rfl] at h

/-! ## H2 -- the weight-one escape -/

/-- Expansion of the diagonal along a splitting `x = a + b` **on `verts T`**.
The hypothesis is agreement on `verts T` only (`Defs.lean` D7), which is all a
`Reducible` witness provides. -/
theorem form_split_diag {T : RTree} {x a b : ℕ → ℤ}
    (hsplit : ∀ u ∈ verts T, x u = a u + b u) :
    B T x x = B T a a + 2 * B T a b + B T b b := by
  change form T x x = form T a a + 2 * form T a b + form T b b
  rw [form_congr T x (fun z => a z + b z) x hsplit,
    form_congr_right T (fun z => a z + b z) x (fun z => a z + b z) hsplit,
    form_add_left, form_add_right, form_add_right, form_comm T b a]
  ring

/-- **H2.** A vertex of weight `1` in a positive definite tree is irreducible.
This is the Stage-B argument (`norm_one_irreducible`) transported to the
concrete lattice: a splitting would give `1 = B T a a + 2 * B T a b + B T b b`
with both diagonal terms `≥ 1` over `ℤ` and the cross term `≥ 0`. -/
theorem weight_one_irred (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    {u : ℕ} (hu : u ∈ verts T) (hw : wt T u = 1) : Irred T (basis u) := by
  rintro ⟨a, b, ha, hb, hsplit, hab⟩
  have hdiag : B T (basis u) (basis u) = 1 := by
    rw [(form_gram_entries_proof T hnd u u hu hu).1 rfl, hw]
  have hexp := form_split_diag hsplit
  have ha' := hpd a ha
  have hb' := hpd b hb
  omega

/-! ## H3 -- the local degree/weight conditions imply `Admissible` -/

/-- **H3.** `SKETCH.md`:187-199: if every vertex of `t` has weight `≥ 2`, every
non-root vertex has `d_t(x) ≤ w(x)`, and the root has `d_t(ρ) + 1 ≤ w(ρ)`, then
`t` is admissible.  The rooted count `ch(x) + 1 = d_t(x)` is derived from the
frozen unrooted `deg` via `deg_root`/`deg_subroot`, never assumed. -/
theorem admissible_of_deg : ∀ t : RTree, (verts t).Nodup →
    (∀ x ∈ verts t, 2 ≤ wt t x) →
    (∀ x ∈ verts t, x ≠ t.root → (deg t x : ℤ) ≤ wt t x) →
    ((deg t t.root : ℤ) + 1 ≤ wt t t.root) → Admissible t := by
  intro t
  induction t using RTree.recAll with
  | _ a w c ih =>
    intro hnd h2 h3 h4
    have hroot : (RTree.node a w c).root = a := rfl
    have hamem : a ∈ verts (RTree.node a w c) := by
      rw [verts_node]; exact List.mem_cons_self
    have hwa : wt (RTree.node a w c) a = w := by
      have hp : ((a, w) : ℕ × ℤ) ∈ vwts (RTree.node a w c) := by
        rw [vwts_node]; exact List.mem_cons_self
      exact wt_eq_of_mem_vwts hnd hp
    have hfm := verts_node_flatMap_nodup hnd
    rw [Admissible]
    refine ⟨?_, ?_, ?_⟩
    · have h := h2 a hamem
      rwa [hwa] at h
    · have h := h4
      rwa [hroot, deg_root hnd, hwa] at h
    · intro t' ht'
      have hant : a ∉ verts t' := verts_node_root_not_mem hnd ht'
      refine ih t' ht' (verts_child_nodup hfm ht') ?_ ?_ ?_
      · intro x hx
        have h := h2 x (mem_verts_of_mem_child ht' hx)
        rwa [wt_sub hnd ht' hx] at h
      · intro x hx hxr
        have hxa : x ≠ (RTree.node a w c).root := by
          rw [hroot]; rintro rfl; exact hant hx
        have h := h3 x (mem_verts_of_mem_child ht' hx) hxa
        rwa [deg_sub hnd ht' hx hxr, wt_sub hnd ht' hx] at h
      · have hrmem : t'.root ∈ verts t' := root_mem_verts t'
        have hxa : t'.root ≠ (RTree.node a w c).root := by
          rw [hroot]; intro hr; exact hant (hr ▸ hrmem)
        have h := h3 t'.root (mem_verts_of_mem_child ht' hrmem) hxa
        rw [deg_subroot hnd ht', wt_sub hnd ht' hrmem] at h
        push_cast at h
        linarith

/-! ## H4 -- Schur positivity at the root -/

/-- **H4.**  For a positive definite tree whose child subtrees are all
admissible, the Schur complement at the root is positive: `0 < W - Σ γᵢ`.

The witness is the rational vector `X` that is `1` at the root and the dual
vector `ρᵢ^#` of the child `tᵢ` on `verts tᵢ`; the branches do not interfere
because `verts` of distinct children are disjoint and `dualScaled` vanishes off
its own subtree.  Positivity of `BQ T X X` comes from `hpd` through
`posDefQ_of_posDef` -- never from `Admissible T`, which is exactly what the root
is allowed to violate. -/
theorem schur_pos (v : ℕ) (W : ℤ) (c : List RTree)
    (hnd : (verts (RTree.node v W c)).Nodup) (hpd : PosDef (RTree.node v W c))
    (hadm : ∀ t ∈ c, Admissible t) : 0 < (W : ℚ) - (c.map gamma).sum := by
  have hfl : (c.flatMap verts).Nodup := verts_node_flatMap_nodup hnd
  set X : ℕ → ℚ := fun u => if u = v then 1 else (c.map fun t => dual t u).sum with hXdef
  have hXv : X v = 1 := by simp [hXdef]
  have hXt : ∀ t ∈ c, ∀ u ∈ verts t, X u = dual t u := by
    intro t ht u hu
    have hne : u ≠ v := fun h => verts_node_root_not_mem hnd ht (h ▸ hu)
    simp only [hXdef, if_neg hne]
    refine sum_map_eq_single (kids_nodup hfl) ht _ ?_
    intro t' ht' hne'
    exact dual_vanish t' 1 u (verts_node_nodup_disjoint hfl ht ht' (Ne.symm hne') hu)
  have hXroot : ∀ t ∈ c, X t.root = gamma t := by
    intro t ht
    rw [hXt t ht t.root (root_mem_verts t)]
    simp [dual, dualScaled_root]
  have hBt : ∀ t ∈ c, form t X X = gamma t := by
    intro t ht
    have hagree : ∀ u ∈ verts t, X u = dual t u := hXt t ht
    rw [form_congr t X (dual t) X hagree, form_congr_right t (dual t) X (dual t) hagree]
    have h := dual_apply t (verts_child_nodup hfl ht) (hadm t ht) 1 (dual t)
    have h2 : dual t t.root = gamma t := by simp [dual, dualScaled_root]
    rw [h2, one_mul] at h
    exact h
  have hform : form (RTree.node v W c) X X = (W : ℚ) - (c.map gamma).sum := by
    rw [form_node]
    have e1 : (c.map fun t => form t X X).sum = (c.map gamma).sum := by
      exact congrArg List.sum (List.map_congr_left hBt)
    have e2 : (c.map fun t => X v * X t.root + X t.root * X v).sum
        = 2 * (c.map gamma).sum := by
      have e : (c.map fun t => X v * X t.root + X t.root * X v)
          = (c.map fun t => 2 * gamma t) := by
        refine List.map_congr_left ?_
        intro t ht
        rw [hXv, hXroot t ht]; ring
      rw [e, List.sum_map_mul_left]
    rw [e1, e2, hXv]
    ring
  have hmem : v ∈ verts (RTree.node v W c) := by
    rw [verts_node]; exact List.mem_cons_self
  have hpos : (0 : ℚ) < form (RTree.node v W c) X X :=
    posDefQ_of_posDef hpd X ⟨v, hmem, by rw [hXv]; norm_num⟩
  rwa [hform] at hpos

/-! ## H5 -- the contradiction -/

/-- A list sum of nonnegative integers with one strictly positive term is
positive (the `ℤ` twin of `PosDef.sum_pos_of_mem`). -/
theorem sum_pos_of_mem_int {α : Type*} {c : List α} {f : α → ℤ}
    (hnn : ∀ t ∈ c, 0 ≤ f t) {t₀ : α} (ht₀ : t₀ ∈ c) (hpos : 0 < f t₀) :
    0 < (c.map f).sum := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ht₀
  have h1 : 0 ≤ (l₁.map f).sum := by
    refine List.sum_nonneg ?_
    intro n hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hn
    exact hnn s (List.mem_append_left _ hs)
  have h2 : 0 ≤ (l₂.map f).sum := by
    refine List.sum_nonneg ?_
    intro n hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hn
    exact hnn s (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  linarith

/-- The `p ≤ -1` normalisation is a genuine **substitution**: replacing `z` by
`z' u = -(basis v u) - z u` leaves `B T z z + B T (basis v) z` unchanged.  Pure
bilinearity, so it holds for any pair of vectors. -/
theorem swap_id (T : RTree) (e z : ℕ → ℤ) :
    form T (fun u => -(e u) - z u) (fun u => -(e u) - z u)
        + form T e (fun u => -(e u) - z u)
      = form T z z + form T e z := by
  have hl : ∀ y : ℕ → ℤ,
      form T (fun u => -(e u) - z u) y = -form T e y - form T z y := by
    intro y
    rw [form_sub_left T (fun u => -(e u)) z y, form_neg_left]
  have hr : ∀ x : ℕ → ℤ,
      form T x (fun u => -(e u) - z u) = -form T x e - form T x z := by
    intro x
    rw [form_comm T x (fun u => -(e u) - z u), hl x, form_comm T e x, form_comm T z x]
  rw [hr (fun u => -(e u) - z u), hr e, hl e, hl z, form_comm T z e]
  ring

/-- The cross-term identity behind `0 ≤ B T a b ↔ Φ z ≤ 0`, where `a = e + z`
and `b = -z` on `verts T`. -/
theorem cross_id (T : RTree) (e z : ℕ → ℤ) :
    form T (fun u => e u + z u) (fun u => -(z u)) = -(form T z z + form T e z) := by
  rw [form_add_left T e z (fun u => -(z u)),
    form_comm T e (fun u => -(z u)), form_comm T z (fun u => -(z u)),
    form_neg_left T z e, form_neg_left T z z, form_comm T z e]
  ring

/-- **Expansion.**  With `p := z v` and `sᵢ := z tᵢ.root`,
`B T z z + B T (basis v) z = W·p·(p+1) + Σᵢ (B tᵢ z z - (2p+1)·sᵢ)`.
The `basis v` row is `W·p - Σᵢ sᵢ` because `basis v` vanishes on every child
subtree (`Nodup`). -/
theorem expand_z (v : ℕ) (W : ℤ) (c : List RTree)
    (hnd : (verts (RTree.node v W c)).Nodup) (z : ℕ → ℤ) :
    form (RTree.node v W c) z z + form (RTree.node v W c) (basis v) z
      = W * z v * (z v + 1)
        + (c.map fun t => form t z z - (2 * z v + 1) * z t.root).sum := by
  have hvnot : ∀ t ∈ c, v ∉ verts t := fun t ht => verts_node_root_not_mem hnd ht
  have hbv : (basis v : ℕ → ℤ) v = 1 := by simp [basis]
  have hbr : ∀ t ∈ c, (basis v : ℕ → ℤ) t.root = 0 := by
    intro t ht
    have h : t.root ≠ v := fun h => hvnot t ht (h ▸ root_mem_verts t)
    simp [basis, h]
  have e0 : (c.map fun t => form t (basis v) z).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro n hn
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
    refine form_vanish t _ z ?_
    intro u hu
    have h : u ≠ v := fun h => hvnot t ht (h ▸ hu)
    simp [basis, h]
  have e1 : (c.map fun t => (basis v : ℕ → ℤ) v * z t.root
      + (basis v : ℕ → ℤ) t.root * z v) = c.map fun t => z t.root := by
    refine List.map_congr_left ?_
    intro t ht
    rw [hbv, hbr t ht]
    ring
  have e2 : (c.map fun t => z v * z t.root + z t.root * z v)
      = c.map fun t => 2 * z v * z t.root := by
    refine List.map_congr_left ?_
    intro t _
    ring
  have e3 : (c.map fun t => form t z z - (2 * z v + 1) * z t.root).sum
      = (c.map fun t => form t z z).sum
        - (2 * z v + 1) * (c.map fun t => z t.root).sum := by
    rw [sum_map_sub_eq c (fun t => form t z z) (fun t => (2 * z v + 1) * z t.root),
      List.sum_map_mul_left]
  rw [form_node, form_node, e0, e1, e2, e3, List.sum_map_mul_left, hbv]
  simp only [Int.cast_id]
  ring

/-- **H5, core.**  With the root weight `W`, all children admissible, the Schur
positivity of H4 and `0 ≤ z v`, the quantity `B T z z + B T (basis v) z` is
strictly positive.  `1 ≤ z v` uses `rooted_estimate`, `z v = 0` uses
`admissible_root_bound` (here the hypothesis `hRB`). -/
theorem core_pos
    (hRB : ∀ (C : RTree), Admissible C → ∀ (x : ℕ → ℤ), NonzeroOn C x →
      0 < B C x x - x C.root)
    (v : ℕ) (W : ℤ) (c : List RTree) (hnd : (verts (RTree.node v W c)).Nodup)
    (hadm : ∀ t ∈ c, Admissible t) (hschur : 0 < (W : ℚ) - (c.map gamma).sum)
    (z : ℕ → ℤ) (hz : NonzeroOn (RTree.node v W c) z) (hp : 0 ≤ z v) :
    0 < form (RTree.node v W c) z z + form (RTree.node v W c) (basis v) z := by
  rw [expand_z v W c hnd z]
  rcases eq_or_lt_of_le hp with hp0 | hp1
  · -- `p = 0`: every summand is `≥ 0`, and one of them is `> 0`.
    have hzv : z v = 0 := hp0.symm
    obtain ⟨u, hu, hzu⟩ := hz
    rw [verts_node, List.mem_cons] at hu
    have huv : u ≠ v := by
      rintro rfl
      exact hzu hzv
    obtain ⟨t₀, ht₀, hut₀⟩ := List.mem_flatMap.1 (hu.resolve_left huv)
    have hnn : ∀ t ∈ c, 0 ≤ form t z z - (2 * z v + 1) * z t.root := by
      intro t ht
      by_cases hnz : ∃ u ∈ verts t, z u ≠ 0
      · have h : 0 < form t z z - z t.root := hRB t (hadm t ht) z hnz
        rw [hzv]
        linarith
      · have hnz' : ∀ u ∈ verts t, z u = 0 :=
          fun u hu => not_not.1 fun h => hnz ⟨u, hu, h⟩
        have h1 : form t z z = 0 := form_vanish t z z hnz'
        have h2 : z t.root = 0 := hnz' t.root (root_mem_verts t)
        simp [h1, h2]
    have hposi : 0 < form t₀ z z - (2 * z v + 1) * z t₀.root := by
      have h : 0 < form t₀ z z - z t₀.root := hRB t₀ (hadm t₀ ht₀) z ⟨u, hut₀, hzu⟩
      rw [hzv]
      linarith
    have hsum := sum_pos_of_mem_int hnn ht₀ hposi
    rw [hzv] at hsum ⊢
    linarith
  · -- `1 ≤ p`: the rooted estimate on each child, summed.
    have hP : (1 : ℚ) ≤ ((z v : ℤ) : ℚ) := by
      have : (1 : ℤ) ≤ z v := by omega
      exact_mod_cast this
    have hcast : (((c.map fun t => form t z z - (2 * z v + 1) * z t.root).sum : ℤ) : ℚ)
        = (c.map fun t => ((form t z z : ℤ) : ℚ)
            - (2 * ((z v : ℤ) : ℚ) + 1) * ((z t.root : ℤ) : ℚ)).sum := by
      rw [cast_sum_map]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro t _
      push_cast
      ring
    have hle : (c.map fun t => -(gamma t * ((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1))).sum
        ≤ (c.map fun t => ((form t z z : ℤ) : ℚ)
            - (2 * ((z v : ℤ) : ℚ) + 1) * ((z t.root : ℤ) : ℚ)).sum := by
      refine RootedEstimate.sum_map_le ?_
      intro t ht
      have h : (0 : ℚ) ≤ ((form t z z : ℤ) : ℚ)
          - (2 * ((z v : ℤ) : ℚ) + 1) * ((z t.root : ℤ) : ℚ)
          + gamma t * ((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1) :=
        rooted_estimate_proof t (hadm t ht) z (z v)
      linarith
    have hlhs : (c.map fun t => -(gamma t * ((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1))).sum
        = -(((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1)) * (c.map gamma).sum := by
      have e : (c.map fun t => -(gamma t * ((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1)))
          = c.map fun t => -(((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1)) * gamma t := by
        refine List.map_congr_left ?_
        intro t _
        ring
      rw [e, List.sum_map_mul_left]
    rw [hlhs] at hle
    have hPP : (0 : ℚ) < ((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1) := by nlinarith
    have hW : ((W * z v * (z v + 1) : ℤ) : ℚ)
        = (W : ℚ) * ((z v : ℤ) : ℚ) * (((z v : ℤ) : ℚ) + 1) := by push_cast; ring
    have hgoal : (0 : ℚ) < ((W * z v * (z v + 1)
        + (c.map fun t => form t z z - (2 * z v + 1) * z t.root).sum : ℤ) : ℚ) := by
      rw [Int.cast_add, hW, hcast]
      nlinarith [hle, mul_pos hPP hschur]
    exact_mod_cast hgoal

/-- **H5 = frozen theorem #12, parameterised on frozen theorem #10.**  `hRB` is
`admissible_root_bound` (`TreeIrred/Theorems.lean`:53-54) in arrow form; Stage F
lives in a file that is being written concurrently and therefore cannot be
imported here.  Everything else is proved outright. -/
theorem pointed_root_irreducible_of_rootBound
    (hRB : ∀ (C : RTree), Admissible C → ∀ (x : ℕ → ℤ), NonzeroOn C x →
      0 < B C x x - x C.root)
    (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :
    ∃ u ∈ verts T, Irred T (basis u) := by
  -- (a) the weight-one escape
  by_cases hone : ∃ u ∈ verts T, wt T u = 1
  · obtain ⟨u, hu, hw⟩ := hone
    exact ⟨u, hu, weight_one_irred T hnd hpd hu hw⟩
  have hone' : ∀ u ∈ verts T, wt T u ≠ 1 := fun u hu h => hone ⟨u, hu, h⟩
  have h2 : ∀ u ∈ verts T, 2 ≤ wt T u := by
    intro u hu
    have h0 := wt_pos T hnd hpd u hu
    have h1 := hone' u hu
    omega
  obtain ⟨v, W, c⟩ := T
  simp only [RTree.root] at hgood
  have hfl : (c.flatMap verts).Nodup := verts_node_flatMap_nodup hnd
  -- (b) every child subtree is admissible
  have hadm : ∀ t ∈ c, Admissible t := by
    intro t ht
    have hant : v ∉ verts t := verts_node_root_not_mem hnd ht
    refine admissible_of_deg t (verts_child_nodup hfl ht) ?_ ?_ ?_
    · intro x hx
      have h := h2 x (mem_verts_of_mem_child ht hx)
      rwa [wt_sub hnd ht hx] at h
    · intro x hx hxr
      have hxv : x ≠ v := fun h => hant (h ▸ hx)
      have h := hgood x (mem_verts_of_mem_child ht hx) hxv
      rwa [deg_sub hnd ht hx hxr, wt_sub hnd ht hx] at h
    · have hrm := root_mem_verts t
      have hxv : t.root ≠ v := fun h => hant (h ▸ hrm)
      have h := hgood t.root (mem_verts_of_mem_child ht hrm) hxv
      rw [deg_subroot hnd ht, wt_sub hnd ht hrm] at h
      push_cast at h
      linarith
  -- (c) Schur positivity at the root
  have hschur := schur_pos v W c hnd hpd hadm
  refine ⟨v, by rw [verts_node]; exact List.mem_cons_self, ?_⟩
  -- (d) the contradiction
  rintro ⟨a, b, ha, hb, hsplit, hab⟩
  have hbv : (basis v : ℕ → ℤ) v = 1 := by simp [basis]
  obtain ⟨z, hzdef⟩ : ∃ z : ℕ → ℤ, z = fun u => -(b u) := ⟨_, rfl⟩
  have hzb : ∀ u, b u = -(z u) := by intro u; rw [hzdef]; ring
  have hsplit' : ∀ u ∈ verts (RTree.node v W c),
      a u = (basis v : ℕ → ℤ) u + z u := by
    intro u hu
    have h := hsplit u hu
    have h' := hzb u
    omega
  -- `0 ≤ B T a b` becomes `Φ z ≤ 0`, where `Φ z = B T z z + B T (basis v) z`
  have hΦle : form (RTree.node v W c) z z
      + form (RTree.node v W c) (basis v) z ≤ 0 := by
    have h1 : form (RTree.node v W c) a b
        = form (RTree.node v W c) (fun u => (basis v : ℕ → ℤ) u + z u)
            (fun u => -(z u)) := by
      rw [form_congr _ a (fun u => (basis v : ℕ → ℤ) u + z u) b hsplit']
      exact form_congr_right _ _ b (fun u => -(z u)) (fun u _ => hzb u)
    have h3 := hab
    change 0 ≤ form (RTree.node v W c) a b at h3
    rw [h1, cross_id (RTree.node v W c) (basis v) z] at h3
    linarith
  have hzn : NonzeroOn (RTree.node v W c) z := by
    obtain ⟨u, hu, hbu⟩ := hb
    have h' := hzb u
    exact ⟨u, hu, by omega⟩
  rcases le_or_gt 0 (z v) with hp | hp
  · have := core_pos hRB v W c hnd hadm hschur z hzn hp
    linarith
  · -- normalise by the genuine substitution `z' u = -(basis v u) - z u`
    have hz'n : NonzeroOn (RTree.node v W c) (fun u => -((basis v : ℕ → ℤ) u) - z u) := by
      obtain ⟨u, hu, hau⟩ := ha
      refine ⟨u, hu, ?_⟩
      change -((basis v : ℕ → ℤ) u) - z u ≠ 0
      have h := hsplit' u hu
      omega
    have hz'p : 0 ≤ -((basis v : ℕ → ℤ) v) - z v := by rw [hbv]; omega
    have hpos := core_pos hRB v W c hnd hadm hschur _ hz'n hz'p
    rw [swap_id (RTree.node v W c) (basis v) z] at hpos
    linarith

/-! ## Guardrails

Concrete check that `admissible_of_deg` really applies, on the star
`0 - 1`, `0 - 2` with root weight `3` and leaf weights `2`.  `vwts` and `edges`
are well-founded recursions (PROGRESS decisions (2)/(5)), so these are closed by
`simp`/`norm_num`, never `decide`.
-/

example : Admissible (RTree.node 0 3 [.node 1 2 [], .node 2 2 []]) := by
  refine admissible_of_deg _ ?_ ?_ ?_ ?_
  · norm_num
  · intro x hx
    norm_num at hx
    rcases hx with rfl | rfl | rfl <;> simp [wt, List.lookup]
  · intro x hx _
    norm_num at hx
    rcases hx with rfl | rfl | rfl <;> simp [wt, deg, List.lookup, RTree.root]
  · simp [wt, deg, RTree.root]

/-- The child of the 3-vertex path `P := 0 - 1 - 2` (all weights `2`) has
capacity `2/3`. -/
example : gamma (RTree.node 1 2 [.node 2 2 []]) = 2 / 3 := by norm_num [gamma]

/-- `schur_pos` on the same `P`: `0 < 2 - 2/3`.  `P` really is positive definite
(it is admissible), and its single child subtree really is admissible, so H4
applies and the Schur complement at the root is `4/3 > 0`. -/
example : (0 : ℚ) < ((2 : ℤ) : ℚ)
    - ([RTree.node 1 2 [RTree.node 2 2 []]].map gamma).sum := by
  refine schur_pos 0 2 [RTree.node 1 2 [RTree.node 2 2 []]] ?_ ?_ ?_
  · norm_num
  · exact admissible_posDef_proof _ (by norm_num [Admissible])
  · intro t ht
    norm_num at ht
    subst ht
    norm_num [Admissible]

end Pointed

/-! ## Frozen theorem #12 -/

/-- **Frozen theorem #12** (`TreeIrred/Theorems.lean`:63-65), Theorem 1 with the
bad vertex at the root (`SKETCH.md`:241-259).  The whole mathematical content is
`Pointed.pointed_root_irreducible_of_rootBound`; its `hRB` binder is the frozen
`admissible_root_bound` (Stage F) in arrow form, so Stage F's
`admissible_root_bound_proof` closes it directly. -/
theorem pointed_root_irreducible_proof (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :
    ∃ u ∈ verts T, Irred T (basis u) :=
  TreeIrred.Pointed.pointed_root_irreducible_of_rootBound
    TreeIrred.admissible_root_bound_proof T hnd hpd hgood

end TreeIrred
