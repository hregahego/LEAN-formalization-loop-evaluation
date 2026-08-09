import TreeIrred.Defs

/-!
# Stage A -- the form API and the Gram-matrix sanity check (`form_gram_entries`)

Support declarations for Stage A of `BLUEPRINT.md` Part 2: the `attach`-removing
list helpers, the `@[simp]` unfolding lemmas for `vwts`/`verts`/`edges`, the
expansion `form_node`, the algebraic API of `form`, the `verts`-relative
congruence lemmas, the `ℤ → ℚ` bridge, the local structure lemmas under
`(verts T).Nodup`, and finally the frozen statement `form_gram_entries`.
-/

namespace TreeIrred

/-! ## A1 -- removing `List.attach` -/

/-- `List.attach` is invisible to `List.flatMap` composed with the coercion. -/
theorem attach_flatMap_eq {α β : Type*} (c : List α) (f : α → List β) :
    c.attach.flatMap (fun t => f t.1) = c.flatMap f := by
  induction c with
  | nil => simp
  | cons a l ih =>
      simp only [List.attach_cons, List.flatMap_cons, List.flatMap_map]
      rw [ih]

/-- `List.attach` is invisible to `List.map` composed with the coercion. -/
theorem attach_map_eq {α β : Type*} (c : List α) (f : α → β) :
    c.attach.map (fun t => f t.1) = c.map f := by
  induction c with
  | nil => simp
  | cons a l ih =>
      simp only [List.attach_cons, List.map_cons, List.map_map, Function.comp_def]
      rw [ih]

@[simp]
theorem vwts_node (a : ℕ) (w : ℤ) (c : List RTree) :
    vwts (.node a w c) = (a, w) :: c.flatMap vwts := by
  rw [vwts, attach_flatMap_eq]

@[simp]
theorem verts_node (a : ℕ) (w : ℤ) (c : List RTree) :
    verts (.node a w c) = a :: c.flatMap verts := by
  simp only [verts, vwts_node, List.map_cons, List.map_flatMap]
  rfl

@[simp]
theorem edges_node (a : ℕ) (w : ℤ) (c : List RTree) :
    edges (.node a w c) = c.map (fun t => (a, t.root)) ++ c.flatMap edges := by
  rw [edges, attach_flatMap_eq]

/-! ## A2 -- the expansion `form_node` -/

/-- Sums distribute over `List.flatMap`. -/
theorem sum_flatMap_eq {α R : Type*} [AddCommMonoid R] (c : List α) (f : α → List R) :
    (c.flatMap f).sum = (c.map fun t => (f t).sum).sum := by
  induction c with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Sums of pointwise differences split. -/
theorem sum_map_sub_eq {α R : Type*} [AddCommGroup R] (c : List α) (f g : α → R) :
    (c.map fun t => f t - g t).sum = (c.map f).sum - (c.map g).sum := by
  induction c with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- The expansion of `form` at a node: the root's own weight, plus the forms of
the child subtrees, minus one symmetrised contribution per root-to-child edge. -/
theorem form_node {R : Type} [CommRing R] (a : ℕ) (w : ℤ) (c : List RTree) (x y : ℕ → R) :
    form (.node a w c) x y = (w : R) * x a * y a + (c.map (fun t => form t x y)).sum
      - (c.map (fun t => x a * y t.root + x t.root * y a)).sum := by
  simp only [form, vwts_node, edges_node, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, List.map_flatMap, sum_flatMap_eq, List.map_map, Function.comp_def,
    sum_map_sub_eq]
  ring

/-! ## A3 -- the algebraic API of `form` -/

/-- Sums of pointwise negations. -/
theorem sum_map_neg_eq {α R : Type*} [AddCommGroup R] (c : List α) (f : α → R) :
    (c.map fun t => -f t).sum = -(c.map f).sum := by
  induction c with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; abel

theorem form_comm {R : Type} [CommRing R] (T : RTree) (x y : ℕ → R) :
    form T x y = form T y x := by
  unfold form
  refine congr_arg₂ (· - ·) (congrArg List.sum (List.map_congr_left fun p _ => ?_))
    (congrArg List.sum (List.map_congr_left fun e _ => ?_))
  · ring
  · ring

theorem form_add_left {R : Type} [CommRing R] (T : RTree) (x x' y : ℕ → R) :
    form T (fun u => x u + x' u) y = form T x y + form T x' y := by
  unfold form
  have h1 : ((vwts T).map fun p => (p.2 : R) * (x p.1 + x' p.1) * y p.1)
      = ((vwts T).map fun p => (p.2 : R) * x p.1 * y p.1 + (p.2 : R) * x' p.1 * y p.1) :=
    List.map_congr_left fun p _ => by ring
  have h2 : ((edges T).map fun e => (x e.1 + x' e.1) * y e.2 + (x e.2 + x' e.2) * y e.1)
      = ((edges T).map fun e => (x e.1 * y e.2 + x e.2 * y e.1)
          + (x' e.1 * y e.2 + x' e.2 * y e.1)) :=
    List.map_congr_left fun e _ => by ring
  rw [h1, h2, List.sum_map_add, List.sum_map_add]
  ring

theorem form_add_right {R : Type} [CommRing R] (T : RTree) (x y y' : ℕ → R) :
    form T x (fun u => y u + y' u) = form T x y + form T x y' := by
  rw [form_comm, form_add_left, form_comm T y x, form_comm T y' x]

theorem form_neg_left {R : Type} [CommRing R] (T : RTree) (x y : ℕ → R) :
    form T (fun u => -x u) y = -form T x y := by
  unfold form
  have h1 : ((vwts T).map fun p => (p.2 : R) * (-x p.1) * y p.1)
      = ((vwts T).map fun p => -((p.2 : R) * x p.1 * y p.1)) :=
    List.map_congr_left fun p _ => by ring
  have h2 : ((edges T).map fun e => (-x e.1) * y e.2 + (-x e.2) * y e.1)
      = ((edges T).map fun e => -(x e.1 * y e.2 + x e.2 * y e.1)) :=
    List.map_congr_left fun e _ => by ring
  rw [h1, h2, sum_map_neg_eq, sum_map_neg_eq]
  ring

theorem form_sub_left {R : Type} [CommRing R] (T : RTree) (x x' y : ℕ → R) :
    form T (fun u => x u - x' u) y = form T x y - form T x' y := by
  have h : (fun u => x u - x' u) = (fun u => x u + (-x' u)) := by
    funext u; ring
  rw [h, form_add_left, form_neg_left]
  ring

theorem form_zero_left {R : Type} [CommRing R] (T : RTree) (y : ℕ → R) :
    form T (fun _ => (0 : R)) y = 0 := by
  unfold form
  have h1 : ((vwts T).map fun p => (p.2 : R) * 0 * y p.1) = ((vwts T).map fun _ => (0 : R)) :=
    List.map_congr_left fun p _ => by ring
  have h2 : ((edges T).map fun e => (0 : R) * y e.2 + (0 : R) * y e.1)
      = ((edges T).map fun _ => (0 : R)) :=
    List.map_congr_left fun e _ => by ring
  rw [h1, h2]
  simp

/-! ## A4 -- `edges_subset_verts`, `form_congr`, `form_vanish` -/

theorem root_mem_verts (T : RTree) : T.root ∈ verts T := by
  cases T with
  | node a w c => simp [RTree.root]

theorem mem_verts_of_mem_child {a : ℕ} {w : ℤ} {c : List RTree} {t : RTree} {u : ℕ}
    (ht : t ∈ c) (hu : u ∈ verts t) : u ∈ verts (RTree.node a w c) := by
  rw [verts_node]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, ht, hu⟩)

theorem fst_mem_verts {T : RTree} {p : ℕ × ℤ} (hp : p ∈ vwts T) : p.1 ∈ verts T :=
  List.mem_map_of_mem hp

/-- Both endpoints of every edge of `T` are vertices of `T`. -/
theorem edges_subset_verts (T : RTree) :
    ∀ e ∈ edges T, e.1 ∈ verts T ∧ e.2 ∈ verts T := by
  induction T using RTree.recAll with
  | _ a w c ih =>
    intro e he
    rw [edges_node] at he
    rcases List.mem_append.1 he with h | h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
      exact ⟨by rw [verts_node]; exact List.mem_cons_self,
        mem_verts_of_mem_child ht (root_mem_verts t)⟩
    · obtain ⟨t, ht, het⟩ := List.mem_flatMap.1 h
      obtain ⟨h1, h2⟩ := ih t ht e het
      exact ⟨mem_verts_of_mem_child ht h1, mem_verts_of_mem_child ht h2⟩

/-- `form T` only sees the values of its first argument **on `verts T`**. -/
theorem form_congr {R : Type} [CommRing R] (T : RTree) (x x' y : ℕ → R)
    (h : ∀ u ∈ verts T, x u = x' u) : form T x y = form T x' y := by
  unfold form
  refine congr_arg₂ (· - ·) (congrArg List.sum (List.map_congr_left fun p hp => ?_))
    (congrArg List.sum (List.map_congr_left fun e he => ?_))
  · rw [h p.1 (fst_mem_verts hp)]
  · obtain ⟨h1, h2⟩ := edges_subset_verts T e he
    rw [h e.1 h1, h e.2 h2]

/-- `form T` only sees the values of its second argument **on `verts T`**. -/
theorem form_congr_right {R : Type} [CommRing R] (T : RTree) (x y y' : ℕ → R)
    (h : ∀ u ∈ verts T, y u = y' u) : form T x y = form T x y' := by
  rw [form_comm, form_congr T y y' x h, form_comm]

/-- A vector vanishing on `verts T` is zero in `L T`. -/
theorem form_vanish {R : Type} [CommRing R] (T : RTree) (x y : ℕ → R)
    (h : ∀ u ∈ verts T, x u = 0) : form T x y = 0 := by
  rw [form_congr T x (fun _ => (0 : R)) y h, form_zero_left]

/-! ## A5 -- the `ℤ → ℚ` bridge -/

theorem cast_sum_map {α : Type*} (l : List α) (f : α → ℤ) :
    (((l.map f).sum : ℤ) : ℚ) = (l.map fun a => ((f a : ℤ) : ℚ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]

/-- The one and only `ℤ`/`ℚ` bridge: the integral form is the rational form on
the coefficient-wise cast vectors. -/
theorem form_cast (T : RTree) (x y : ℕ → ℤ) :
    ((B T x y : ℤ) : ℚ) = BQ T (fun u => (x u : ℚ)) (fun u => (y u : ℚ)) := by
  change ((form T x y : ℤ) : ℚ) = form T (fun u => (x u : ℚ)) (fun u => (y u : ℚ))
  unfold form
  rw [Int.cast_sub, cast_sum_map, cast_sum_map]
  refine congr_arg₂ (· - ·) (congrArg List.sum (List.map_congr_left fun p _ => ?_))
    (congrArg List.sum (List.map_congr_left fun e _ => ?_))
  · push_cast
    ring
  · push_cast
    ring

/-! ## A6 -- local structure under `(verts T).Nodup` -/

section ListAux

variable {α : Type*}

/-- A list sum in which only one summand can be nonzero. -/
theorem sum_map_eq_single {R : Type*} [AddCommMonoid R] {c : List α} (hc : c.Nodup)
    {t : α} (ht : t ∈ c) (g : α → R) (h0 : ∀ t' ∈ c, t' ≠ t → g t' = 0) :
    (c.map g).sum = g t := by
  induction c with
  | nil => cases ht
  | cons hd tl ih =>
    rw [List.nodup_cons] at hc
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ht with rfl | ht'
    · have hz : (tl.map g).sum = 0 := by
        refine List.sum_eq_zero ?_
        intro n hn
        obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hn
        exact h0 t' (List.mem_cons_of_mem _ ht') (fun h => hc.1 (h ▸ ht'))
      rw [hz, add_zero]
    · have hz : g hd = 0 := by
        refine h0 hd List.mem_cons_self (fun h => hc.1 ?_)
        exact h ▸ ht'
      rw [hz, zero_add]
      exact ih hc.2 ht' fun t' ht'' => h0 t' (List.mem_cons_of_mem _ ht'')

/-- A `countP` in which exactly one element qualifies. -/
theorem countP_eq_one_of_unique {c : List α} (hc : c.Nodup) {t : α} (ht : t ∈ c)
    {p : α → Bool} (hpt : p t = true) (h0 : ∀ t' ∈ c, p t' = true → t' = t) :
    c.countP p = 1 := by
  induction c with
  | nil => cases ht
  | cons hd tl ih =>
    rw [List.nodup_cons] at hc
    rw [List.countP_cons]
    rcases List.mem_cons.1 ht with rfl | ht'
    · have hz : tl.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro x hx hpx
        exact hc.1 (h0 x (List.mem_cons_of_mem _ hx) hpx ▸ hx)
      rw [hz, if_pos hpt]
    · have hhd : ¬ p hd = true := fun hcon => hc.1 (h0 hd List.mem_cons_self hcon ▸ ht')
      rw [if_neg hhd, add_zero]
      exact ih hc.2 ht' fun t' ht'' => h0 t' (List.mem_cons_of_mem _ ht'')

/-- `List.lookup` reads off the (unique, by `Nodup`) entry of a key. -/
theorem lookup_eq_of_mem {l : List (ℕ × ℤ)} (hnd : (l.map Prod.fst).Nodup) {p : ℕ × ℤ}
    (hp : p ∈ l) : l.lookup p.1 = some p.2 := by
  induction l with
  | nil => cases hp
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hp with rfl | hp'
    · obtain ⟨k, v⟩ := p
      change ((k, v) :: tl).lookup k = some v
      exact List.lookup_cons_self
    · have hne : ¬ (p.1 = hd.1) := by
        intro h
        exact hnd.1 (h ▸ List.mem_map_of_mem hp')
      have hb : (p.1 == hd.1) = false := by simpa using hne
      rw [show hd = (hd.1, hd.2) from rfl]
      simp only [List.lookup_cons, hb]
      exact ih hnd.2 hp'

end ListAux

/-- Under `Nodup`, distinct child subtrees have disjoint vertex sets. -/
theorem verts_node_nodup_disjoint {c : List RTree} (h : (c.flatMap verts).Nodup)
    {t t' : RTree} (ht : t ∈ c) (ht' : t' ∈ c) (hne : t ≠ t') {u : ℕ}
    (hu : u ∈ verts t) : u ∉ verts t' := by
  induction c with
  | nil => cases ht
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.1 ht with rfl | ht2
    · rcases List.mem_cons.1 ht' with rfl | ht'2
      · exact absurd rfl hne
      · exact fun hc => h3 u hu u (List.mem_flatMap.2 ⟨t', ht'2, hc⟩) rfl
    · rcases List.mem_cons.1 ht' with rfl | ht'2
      · exact fun hc => h3 u hc u (List.mem_flatMap.2 ⟨t, ht2, hu⟩) rfl
      · exact ih h2 ht2 ht'2

/-- Under `Nodup`, the child subtrees are pairwise distinct. -/
theorem kids_nodup {c : List RTree} (h : (c.flatMap verts).Nodup) : c.Nodup := by
  induction c with
  | nil => simp
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih h2⟩
    exact h3 hd.root (root_mem_verts hd) hd.root
      (List.mem_flatMap.2 ⟨hd, hmem, root_mem_verts hd⟩) rfl

theorem verts_child_nodup {c : List RTree} (h : (c.flatMap verts).Nodup) {t : RTree}
    (ht : t ∈ c) : (verts t).Nodup := (List.nodup_flatMap.1 h).1 t ht

/-- Under `Nodup`, a child subtree is determined by its root. -/
theorem kid_eq_of_root_eq {c : List RTree} (h : (c.flatMap verts).Nodup) {t t' : RTree}
    (ht : t ∈ c) (ht' : t' ∈ c) (hr : t.root = t'.root) : t = t' := by
  by_contra hne
  refine verts_node_nodup_disjoint h ht ht' hne (root_mem_verts t) ?_
  rw [hr]
  exact root_mem_verts t'

theorem verts_node_flatMap_nodup {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) : (c.flatMap verts).Nodup := by
  rw [verts_node, List.nodup_cons] at hnd
  exact hnd.2

theorem verts_node_root_not_mem {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) {t : RTree} (ht : t ∈ c) : a ∉ verts t := by
  rw [verts_node, List.nodup_cons] at hnd
  exact fun h => hnd.1 (List.mem_flatMap.2 ⟨t, ht, h⟩)

/-! ### degrees -/

theorem deg_node (a : ℕ) (w : ℤ) (c : List RTree) (u : ℕ) :
    deg (RTree.node a w c) u
      = (c.countP fun t => decide (a = u) || decide (t.root = u))
        + (c.map fun t => deg t u).sum := by
  simp only [deg, edges_node, List.countP_append, List.countP_map, List.countP_flatMap,
    Function.comp_def]

/-- A vertex outside the tree has degree `0`. -/
theorem deg_eq_zero_of_not_mem {T : RTree} {u : ℕ} (hu : u ∉ verts T) : deg T u = 0 := by
  rw [deg, List.countP_eq_zero]
  intro e he hp
  obtain ⟨h1, h2⟩ := edges_subset_verts T e he
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
  rcases hp with hp | hp
  · exact hu (hp ▸ h1)
  · exact hu (hp ▸ h2)

/-- The root's degree is its number of children -- the identity that makes the
rooted presentation match the unrooted degree.  `deg` itself stays the frozen
`edges`-based count. -/
theorem deg_root {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) : deg (RTree.node a w c) a = c.length := by
  rw [deg_node]
  have h1 : (c.countP fun t => decide (a = a) || decide (t.root = a)) = c.length := by
    simp
  have h2 : (c.map fun t => deg t a).sum = 0 := by
    refine List.sum_eq_zero ?_
    intro n hn
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
    exact deg_eq_zero_of_not_mem (verts_node_root_not_mem hnd ht)
  rw [h1, h2, Nat.add_zero]

/-- A child root gains exactly one edge -- the one to its parent. -/
theorem deg_subroot {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) {t : RTree} (ht : t ∈ c) :
    deg (RTree.node a w c) t.root = deg t t.root + 1 := by
  have hfm := verts_node_flatMap_nodup hnd
  have hane : a ≠ t.root := fun h => verts_node_root_not_mem hnd ht (h ▸ root_mem_verts t)
  rw [deg_node]
  have h1 : (c.countP fun t' => decide (a = t.root) || decide (t'.root = t.root)) = 1 := by
    refine countP_eq_one_of_unique (kids_nodup hfm) ht ?_ ?_
    · simp
    · intro t' ht' hp
      simp only [Bool.or_eq_true, decide_eq_true_eq, hane, false_or] at hp
      exact kid_eq_of_root_eq hfm ht' ht hp
  have h2 : (c.map fun t' => deg t' t.root).sum = deg t t.root := by
    refine sum_map_eq_single (kids_nodup hfm) ht _ ?_
    intro t' ht' hne
    exact deg_eq_zero_of_not_mem
      (verts_node_nodup_disjoint hfm ht ht' (Ne.symm hne) (root_mem_verts t))
  rw [h1, h2, Nat.add_comm]

/-- Away from the child root, degrees are computed inside the subtree. -/
theorem deg_sub {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) {t : RTree} (ht : t ∈ c) {u : ℕ}
    (hu : u ∈ verts t) (hur : u ≠ t.root) : deg (RTree.node a w c) u = deg t u := by
  have hfm := verts_node_flatMap_nodup hnd
  have hane : a ≠ u := fun h => verts_node_root_not_mem hnd ht (h ▸ hu)
  rw [deg_node]
  have h1 : (c.countP fun t' => decide (a = u) || decide (t'.root = u)) = 0 := by
    rw [List.countP_eq_zero]
    intro t' ht' hp
    simp only [Bool.or_eq_true, decide_eq_true_eq, hane, false_or] at hp
    by_cases htt : t' = t
    · subst htt
      exact hur hp.symm
    · refine verts_node_nodup_disjoint hfm ht ht' (Ne.symm htt) hu ?_
      rw [← hp]
      exact root_mem_verts t'
  have h2 : (c.map fun t' => deg t' u).sum = deg t u := by
    refine sum_map_eq_single (kids_nodup hfm) ht _ ?_
    intro t' ht' hne
    exact deg_eq_zero_of_not_mem (verts_node_nodup_disjoint hfm ht ht' (Ne.symm hne) hu)
  rw [h1, h2, Nat.zero_add]

/-! ### weights -/

/-- Under `Nodup`, `wt` reads off any `vwts` entry. -/
theorem wt_eq_of_mem_vwts {T : RTree} (hnd : (verts T).Nodup) {p : ℕ × ℤ}
    (hp : p ∈ vwts T) : wt T p.1 = p.2 := by
  rw [verts] at hnd
  rw [wt, lookup_eq_of_mem hnd hp]
  rfl

/-- Weights are computed inside the subtree. -/
theorem wt_sub {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) {t : RTree} (ht : t ∈ c) {u : ℕ}
    (hu : u ∈ verts t) : wt (RTree.node a w c) u = wt t u := by
  rw [verts] at hu
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
  have hmem : p ∈ vwts (RTree.node a w c) := by
    rw [vwts_node]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, ht, hp⟩)
  rw [wt_eq_of_mem_vwts hnd hmem,
    wt_eq_of_mem_vwts (verts_child_nodup (verts_node_flatMap_nodup hnd) ht) hp]

/-! ## A7 -- the Gram-matrix entries -/

/-- The number of edges of `T` joining `u` and `v`, counted in both
orientations. -/
def ecount (T : RTree) (u v : ℕ) : ℕ :=
  (edges T).countP (fun e => decide (e.1 = u ∧ e.2 = v))
    + (edges T).countP (fun e => decide (e.1 = v ∧ e.2 = u))

theorem ecount_comm (T : RTree) (u v : ℕ) : ecount T u v = ecount T v u :=
  Nat.add_comm _ _

theorem ecount_node (a : ℕ) (w : ℤ) (c : List RTree) (u v : ℕ) :
    ecount (RTree.node a w c) u v
      = ((c.countP fun t => decide (a = u ∧ t.root = v))
          + (c.countP fun t => decide (a = v ∧ t.root = u)))
        + (c.map fun t => ecount t u v).sum := by
  simp only [ecount, edges_node, List.countP_append, List.countP_map, List.countP_flatMap,
    Function.comp_def, List.sum_map_add]
  omega

theorem ecount_eq_zero_left {T : RTree} {u : ℕ} (hu : u ∉ verts T) (v : ℕ) :
    ecount T u v = 0 := by
  have h1 : (edges T).countP (fun e => decide (e.1 = u ∧ e.2 = v)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he hp
    simp only [decide_eq_true_eq] at hp
    exact hu (by rw [← hp.1]; exact (edges_subset_verts T e he).1)
  have h2 : (edges T).countP (fun e => decide (e.1 = v ∧ e.2 = u)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he hp
    simp only [decide_eq_true_eq] at hp
    exact hu (by rw [← hp.2]; exact (edges_subset_verts T e he).2)
  rw [ecount, h1, h2]

/-- Distinct children have distinct roots, so at most one child root equals `v`. -/
theorem countP_root_le_one {c : List RTree} (h : (c.flatMap verts).Nodup) (v : ℕ) :
    (c.countP fun t => decide (t.root = v)) ≤ 1 := by
  by_cases hex : ∃ t ∈ c, t.root = v
  · obtain ⟨t, ht, hr⟩ := hex
    refine le_of_eq (countP_eq_one_of_unique (kids_nodup h) ht (by simp [hr]) ?_)
    intro t' ht' hp
    simp only [decide_eq_true_eq] at hp
    exact kid_eq_of_root_eq h ht' ht (by rw [hp, hr])
  · simp only [not_exists, not_and] at hex
    refine le_of_eq_of_le (List.countP_eq_zero.2 ?_) (Nat.zero_le 1)
    intro t ht hp
    simp only [decide_eq_true_eq] at hp
    exact hex t ht hp

/-- Under `Nodup` the tree has no loops. -/
theorem edges_no_loop : ∀ (T : RTree), (verts T).Nodup → ∀ e ∈ edges T, e.1 ≠ e.2 := by
  intro T
  induction T using RTree.recAll with
  | _ a w c ih =>
    intro hnd e he
    rw [edges_node] at he
    rcases List.mem_append.1 he with h | h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
      intro hcon
      have hcon' : a = t.root := hcon
      exact verts_node_root_not_mem hnd ht (by rw [hcon']; exact root_mem_verts t)
    · obtain ⟨t, ht, het⟩ := List.mem_flatMap.1 h
      exact ih t ht (verts_child_nodup (verts_node_flatMap_nodup hnd) ht) e het

/-- Under `Nodup`, two distinct vertices are joined by at most one edge. -/
theorem ecount_le_one : ∀ (T : RTree), (verts T).Nodup → ∀ u v : ℕ, u ≠ v →
    ecount T u v ≤ 1 := by
  intro T
  induction T using RTree.recAll with
  | _ a w c ih =>
    intro hnd u v huv
    have hfm := verts_node_flatMap_nodup hnd
    rw [ecount_node]
    by_cases hau : a = u
    · have e1 : (c.countP fun t => decide (a = u ∧ t.root = v))
          = (c.countP fun t => decide (t.root = v)) :=
        List.countP_congr fun t _ => by simp [hau]
      have e2 : (c.countP fun t => decide (a = v ∧ t.root = u)) = 0 := by
        refine List.countP_eq_zero.2 fun t ht hp => ?_
        simp only [decide_eq_true_eq] at hp
        exact huv (by rw [← hau]; exact hp.1)
      have e3 : (c.map fun t => ecount t u v).sum = 0 := by
        refine List.sum_eq_zero ?_
        intro n hn
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
        exact ecount_eq_zero_left (by rw [← hau]; exact verts_node_root_not_mem hnd ht) v
      rw [e1, e2, e3]
      simpa using countP_root_le_one hfm v
    · by_cases hav : a = v
      · have e1 : (c.countP fun t => decide (a = u ∧ t.root = v)) = 0 := by
          refine List.countP_eq_zero.2 fun t ht hp => ?_
          simp only [decide_eq_true_eq] at hp
          exact hau hp.1
        have e2 : (c.countP fun t => decide (a = v ∧ t.root = u))
            = (c.countP fun t => decide (t.root = u)) :=
          List.countP_congr fun t _ => by simp [hav]
        have e3 : (c.map fun t => ecount t u v).sum = 0 := by
          refine List.sum_eq_zero ?_
          intro n hn
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
          rw [ecount_comm]
          exact ecount_eq_zero_left (by rw [← hav]; exact verts_node_root_not_mem hnd ht) u
        rw [e1, e2, e3]
        simpa using countP_root_le_one hfm u
      · have e1 : (c.countP fun t => decide (a = u ∧ t.root = v)) = 0 := by
          refine List.countP_eq_zero.2 fun t ht hp => ?_
          simp only [decide_eq_true_eq] at hp
          exact hau hp.1
        have e2 : (c.countP fun t => decide (a = v ∧ t.root = u)) = 0 := by
          refine List.countP_eq_zero.2 fun t ht hp => ?_
          simp only [decide_eq_true_eq] at hp
          exact hav hp.1
        rw [e1, e2]
        by_cases hex : ∃ t ∈ c, u ∈ verts t
        · obtain ⟨t₀, ht₀, hu₀⟩ := hex
          have e3 : (c.map fun t => ecount t u v).sum = ecount t₀ u v := by
            refine sum_map_eq_single (kids_nodup hfm) ht₀ _ ?_
            intro t' ht' hne
            exact ecount_eq_zero_left
              (verts_node_nodup_disjoint hfm ht₀ ht' (Ne.symm hne) hu₀) v
          rw [e3]
          simpa using ih t₀ ht₀ (verts_child_nodup hfm ht₀) u v huv
        · simp only [not_exists, not_and] at hex
          have e3 : (c.map fun t => ecount t u v).sum = 0 := by
            refine List.sum_eq_zero ?_
            intro n hn
            obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
            exact ecount_eq_zero_left (hex t ht) v
          rw [e3]
          simp

theorem one_le_ecount_of_adj {T : RTree} {u v : ℕ} (h : Adj T u v) : 1 ≤ ecount T u v := by
  have h' : (u, v) ∈ edges T ∨ (v, u) ∈ edges T := h
  rw [ecount]
  rcases h' with h | h
  · have h1 : 0 < (edges T).countP (fun e => decide (e.1 = u ∧ e.2 = v)) :=
      List.countP_pos_iff.2 ⟨(u, v), h, by simp⟩
    omega
  · have h2 : 0 < (edges T).countP (fun e => decide (e.1 = v ∧ e.2 = u)) :=
      List.countP_pos_iff.2 ⟨(v, u), h, by simp⟩
    omega

theorem ecount_eq_zero_of_not_adj {T : RTree} {u v : ℕ} (h : ¬ Adj T u v) :
    ecount T u v = 0 := by
  rw [ecount]
  have h1 : (edges T).countP (fun e => decide (e.1 = u ∧ e.2 = v)) = 0 := by
    refine List.countP_eq_zero.2 fun e he hp => ?_
    simp only [decide_eq_true_eq] at hp
    exact h (Or.inl (by rw [← hp.1, ← hp.2]; exact he))
  have h2 : (edges T).countP (fun e => decide (e.1 = v ∧ e.2 = u)) = 0 := by
    refine List.countP_eq_zero.2 fun e he hp => ?_
    simp only [decide_eq_true_eq] at hp
    exact h (Or.inr (by rw [← hp.1, ← hp.2]; exact he))
  rw [h1, h2]

/-- Indicator sums count. -/
theorem sum_map_ite_eq_countP {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun a => if p a then (1 : ℤ) else 0).sum
      = ((l.countP fun a => decide (p a) : ℕ) : ℤ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : p a
    · rw [if_pos h, if_pos (decide_eq_true h), Nat.cast_add, Nat.cast_one]
      ring
    · rw [if_neg h, if_neg (by simp [h]), Nat.cast_add, Nat.cast_zero]
      ring

/-- Off the diagonal the vertex-weight part of `form` contributes nothing. -/
theorem vwts_sum_off_diag (T : RTree) (u v : ℕ) (huv : u ≠ v) :
    ((vwts T).map fun p =>
      (p.2 : ℤ) * (if p.1 = u then (1 : ℤ) else 0) * (if p.1 = v then (1 : ℤ) else 0)).sum
      = 0 := by
  have hrw : ((vwts T).map fun p =>
      (p.2 : ℤ) * (if p.1 = u then (1 : ℤ) else 0) * (if p.1 = v then (1 : ℤ) else 0))
      = ((vwts T).map fun _ => (0 : ℤ)) := by
    refine List.map_congr_left fun p _ => ?_
    by_cases h2 : p.1 = v
    · have h1 : ¬ p.1 = u := fun h => huv (by rw [← h]; exact h2)
      rw [if_neg h1, mul_zero, zero_mul]
    · rw [if_neg h2, mul_zero]
  rw [hrw]
  simp

theorem ite_mul_ite_and (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℤ) else 0) * (if Q then (1 : ℤ) else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P
  · by_cases hQ : Q
    · simp [hP, hQ]
    · simp [hP, hQ]
  · simp [hP]

theorem ite_mul_ite_and' (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℤ) else 0) * (if Q then (1 : ℤ) else 0) = if Q ∧ P then 1 else 0 := by
  by_cases hP : P
  · by_cases hQ : Q
    · simp [hP, hQ]
    · simp [hP, hQ]
  · simp [hP]

/-- The edge part of `form` on two basis vectors counts the joining edges. -/
theorem edge_sum_eq (T : RTree) (u v : ℕ) :
    ((edges T).map fun e =>
      (if e.1 = u then (1 : ℤ) else 0) * (if e.2 = v then (1 : ℤ) else 0)
      + (if e.2 = u then (1 : ℤ) else 0) * (if e.1 = v then (1 : ℤ) else 0)).sum
      = (ecount T u v : ℤ) := by
  have hrw : ((edges T).map fun e =>
      (if e.1 = u then (1 : ℤ) else 0) * (if e.2 = v then (1 : ℤ) else 0)
      + (if e.2 = u then (1 : ℤ) else 0) * (if e.1 = v then (1 : ℤ) else 0))
      = ((edges T).map fun e => (if (e.1 = u ∧ e.2 = v) then (1 : ℤ) else 0)
          + (if (e.1 = v ∧ e.2 = u) then (1 : ℤ) else 0)) :=
    List.map_congr_left fun e _ => by
      rw [ite_mul_ite_and, ite_mul_ite_and']
  rw [hrw, List.sum_map_add, sum_map_ite_eq_countP, sum_map_ite_eq_countP, ecount]
  push_cast
  ring

/-- **Frozen statement 1** (`TreeIrred.form_gram_entries`): `form` really is the
Gram matrix of the weighted tree in the vertex basis. -/
theorem form_gram_entries_proof (T : RTree) (hnd : (verts T).Nodup) (u v : ℕ)
    (hu : u ∈ verts T) (hv : v ∈ verts T) :
    (u = v → B T (basis u) (basis v) = wt T u) ∧
    (u ≠ v → Adj T u v → B T (basis u) (basis v) = -1) ∧
    (u ≠ v → ¬ Adj T u v → B T (basis u) (basis v) = 0) := by
  have hvnd : (vwts T).Nodup := List.Nodup.of_map Prod.fst (by rw [verts] at hnd; exact hnd)
  have hinj := List.inj_on_of_nodup_map (f := Prod.fst) (by rw [verts] at hnd; exact hnd)
  have hB : B T (basis u) (basis v)
      = ((vwts T).map fun p =>
          (p.2 : ℤ) * (if p.1 = u then (1 : ℤ) else 0) * (if p.1 = v then (1 : ℤ) else 0)).sum
        - ((edges T).map fun e =>
            (if e.1 = u then (1 : ℤ) else 0) * (if e.2 = v then (1 : ℤ) else 0)
            + (if e.2 = u then (1 : ℤ) else 0) * (if e.1 = v then (1 : ℤ) else 0)).sum := rfl
  refine ⟨fun huv => ?_, fun huv hadj => ?_, fun huv hadj => ?_⟩
  · subst huv
    obtain ⟨p₀, hp₀, hp₀u⟩ : ∃ p ∈ vwts T, p.1 = u := by
      rw [verts] at hu
      exact List.mem_map.1 hu
    have hvsum : ((vwts T).map fun p =>
        (p.2 : ℤ) * (if p.1 = u then (1 : ℤ) else 0) * (if p.1 = u then (1 : ℤ) else 0)).sum
        = p₀.2 := by
      have hrw : ((vwts T).map fun p =>
          (p.2 : ℤ) * (if p.1 = u then (1 : ℤ) else 0) * (if p.1 = u then (1 : ℤ) else 0))
          = ((vwts T).map fun p => if p.1 = u then (p.2 : ℤ) else 0) :=
        List.map_congr_left fun p _ => by by_cases h : p.1 = u <;> simp [h]
      have h0 : ∀ p ∈ vwts T, p ≠ p₀ → (if p.1 = u then (p.2 : ℤ) else 0) = 0 := by
        intro p hp hne
        have hpu : ¬ p.1 = u := fun hcon => hne (hinj hp hp₀ (by rw [hcon, hp₀u]))
        rw [if_neg hpu]
      rw [hrw, sum_map_eq_single hvnd hp₀ _ h0, if_pos hp₀u]
    have hesum : ((edges T).map fun e =>
        (if e.1 = u then (1 : ℤ) else 0) * (if e.2 = u then (1 : ℤ) else 0)
        + (if e.2 = u then (1 : ℤ) else 0) * (if e.1 = u then (1 : ℤ) else 0)).sum = 0 := by
      have hrw : ((edges T).map fun e =>
          (if e.1 = u then (1 : ℤ) else 0) * (if e.2 = u then (1 : ℤ) else 0)
          + (if e.2 = u then (1 : ℤ) else 0) * (if e.1 = u then (1 : ℤ) else 0))
          = ((edges T).map fun _ => (0 : ℤ)) := by
        refine List.map_congr_left fun e he => ?_
        have hne := edges_no_loop T hnd e he
        by_cases h1 : e.1 = u
        · have h2 : ¬ e.2 = u := fun h => hne (h1.trans h.symm)
          simp [h1, h2]
        · simp [h1]
      rw [hrw]
      simp
    rw [hB, hvsum, hesum, sub_zero, ← hp₀u, wt_eq_of_mem_vwts hnd hp₀]
  · have h := edge_sum_eq T u v
    rw [hB, vwts_sum_off_diag T u v huv, h, zero_sub,
      Nat.le_antisymm (ecount_le_one T hnd u v huv) (one_le_ecount_of_adj hadj)]
    norm_num
  · have h := edge_sum_eq T u v
    rw [hB, vwts_sum_off_diag T u v huv, h, ecount_eq_zero_of_not_adj hadj]
    norm_num

/-! ## Guardrails

Concrete sanity checks on the path `P = 0 - 1 - 2` with all weights `2`, and on
the star `0 - 1`, `0 - 2`.  `vwts`/`edges` are defined by well-founded recursion
(PROGRESS decisions (2)/(5)), so these are closed by `norm_num`, never `decide`.
-/

example : verts (RTree.node 0 2 [.node 1 2 [.node 2 2 []]]) = [0, 1, 2] := by
  norm_num

example : deg (RTree.node 0 2 [.node 1 2 [.node 2 2 []]]) 1 = 2 := by
  norm_num [deg, RTree.root]

example : deg (RTree.node 0 2 [.node 1 2 [.node 2 2 []]]) 0 = 1 := by
  norm_num [deg, RTree.root]

example : B (RTree.node 0 2 [.node 1 2 [.node 2 2 []]]) (basis 0) (basis 1) = -1 := by
  norm_num [B, form, basis, RTree.root]

example : B (RTree.node 0 2 [.node 1 2 [.node 2 2 []]]) (basis 0) (basis 2) = 0 := by
  norm_num [B, form, basis, RTree.root]

example : B (RTree.node 0 2 [.node 1 2 [.node 2 2 []]]) (basis 1) (basis 1) = 2 := by
  norm_num [B, form, basis, RTree.root]

example : deg (RTree.node 0 3 [.node 1 2 [], .node 2 2 []]) 0 = 2 := by
  norm_num [deg, RTree.root]

end TreeIrred
