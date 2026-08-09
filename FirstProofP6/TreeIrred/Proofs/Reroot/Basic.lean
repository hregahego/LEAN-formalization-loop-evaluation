import TreeIrred.Defs

/-!
# Stage G -- re-rooting (`exists_reroot_at`)

Support declarations for Stage G.  Everything auxiliary lives in the nested
namespace `TreeIrred.Reroot` so that it can never clash with the top-level
helpers Stage A is developing in parallel.
See `BLUEPRINT.md` Part 2, Stage G.
-/

namespace TreeIrred

namespace Reroot

/-! ## Unfolding `vwts` / `edges` through `List.attach` -/

theorem attach_flatMap_eq {α β : Type} (c : List α) (f : α → List β) :
    c.attach.flatMap (fun t => f t.1) = c.flatMap f := by
  conv_rhs => rw [← List.attach_map_subtype_val c]
  rw [List.flatMap_map]

theorem attach_map_eq {α β : Type} (c : List α) (f : α → β) :
    c.attach.map (fun t => f t.1) = c.map f := by
  conv_rhs => rw [← List.attach_map_subtype_val c]
  rw [List.map_map]
  rfl

@[simp] theorem vwts_node (a : ℕ) (w : ℤ) (c : List RTree) :
    vwts (.node a w c) = (a, w) :: c.flatMap vwts := by
  rw [vwts, attach_flatMap_eq]

@[simp] theorem edges_node (a : ℕ) (w : ℤ) (c : List RTree) :
    edges (.node a w c) = c.map (fun t => (a, t.root)) ++ c.flatMap edges := by
  rw [edges, attach_flatMap_eq]

@[simp] theorem verts_node (a : ℕ) (w : ℤ) (c : List RTree) :
    verts (.node a w c) = a :: c.flatMap verts := by
  simp only [verts, vwts_node, List.map_cons, List.map_flatMap]
  rfl

/-! ## The unordered edge key -/

/-- The unordered version of an edge: the pair sorted by `min`/`max`.  Both the
degree count and the edge summand of `form` factor through it. -/
def ekey (e : ℕ × ℕ) : ℕ × ℕ := (min e.1 e.2, max e.1 e.2)

theorem ekey_comm (x y : ℕ) : ekey (x, y) = ekey (y, x) := by
  simp [ekey, min_comm, max_comm]

/-! ## Hanging extra subtrees off the root -/

/-- `att t rest` hangs the extra subtrees `rest` off the root of `t`. -/
def att (t : RTree) (rest : List RTree) : RTree :=
  .node t.root t.wtRoot (t.kids ++ rest)

@[simp] theorem att_root (t : RTree) (rest : List RTree) : (att t rest).root = t.root := rfl

theorem att_nil (t : RTree) : att t [] = t := by
  cases t with
  | node a w c => simp [att, RTree.root, RTree.wtRoot, RTree.kids]

theorem vwts_att (t : RTree) (rest : List RTree) :
    vwts (att t rest) = vwts t ++ rest.flatMap vwts := by
  cases t with
  | node a w c => simp [att, RTree.root, RTree.wtRoot, RTree.kids, List.flatMap_append]

theorem edges_att (t : RTree) (rest : List RTree) :
    (edges (att t rest)).Perm
      (edges t ++ rest.map (fun s => (t.root, s.root)) ++ rest.flatMap edges) := by
  cases t with
  | node a w c =>
    simp only [att, RTree.root, RTree.wtRoot, RTree.kids, edges_node, List.map_append,
      List.flatMap_append]
    rw [List.perm_iff_count]
    intro z
    simp [List.count_append]
    omega

/-! ## The honest re-rooting: existence of a tree rooted at any vertex -/

/-- Core re-rooting recursion.  For every tree `t`, every vertex `u` of `t` and
every list `rest` of extra subtrees hung off `t`'s root, there is a tree `s`
rooted at `u` with the same vertex-weight multiset and the same multiset of
*unordered* edges as `att t rest`.  The recursion is structural in `t`: the
"rest of the world" is pushed down into the accumulator `rest`. -/
theorem reroot_core (t : RTree) : ∀ u ∈ verts t, ∀ rest : List RTree,
    ∃ s : RTree, s.root = u ∧ (vwts s).Perm (vwts (att t rest)) ∧
      ((edges s).map ekey).Perm ((edges (att t rest)).map ekey) := by
  induction t using RTree.recAll with
  | h b w' d ih =>
    intro u hu rest
    rw [verts_node, List.mem_cons, List.mem_flatMap] at hu
    rcases hu with rfl | ⟨t₀, ht₀, hut₀⟩
    · exact ⟨att (.node u w' d) rest, rfl, .refl _, .refl _⟩
    · obtain ⟨d₁, d₂, rfl⟩ := List.append_of_mem ht₀
      obtain ⟨s, hs, hsv, hse⟩ :=
        ih t₀ ht₀ u hut₀ [RTree.node b w' (d₁ ++ d₂ ++ rest)]
      refine ⟨s, hs, hsv.trans ?_, hse.trans ?_⟩
      · simp only [vwts_att, vwts_node, List.flatMap_cons, List.flatMap_nil,
          List.flatMap_append, List.append_nil, List.append_assoc, List.cons_append]
        rw [List.perm_iff_count]
        intro z
        simp [List.count_append, List.count_cons]
        omega
      · refine ((edges_att t₀ _).map ekey).trans ?_
        refine List.Perm.trans ?_ (((edges_att _ rest).map ekey).symm)
        simp only [edges_node, RTree.root, List.map_append, List.map_cons, List.map_nil,
          List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.append_nil,
          List.append_assoc, List.cons_append, List.map_map]
        rw [List.perm_iff_count]
        intro z
        simp [List.count_append, List.count_cons, ekey, min_comm, max_comm]
        omega

/-! ## Transporting `deg` and `form` along the two invariants -/

theorem ekey_incidence (v : ℕ) (e : ℕ × ℕ) :
    ((ekey e).1 = v || (ekey e).2 = v) = (e.1 = v || e.2 = v) := by
  obtain ⟨p, q⟩ := e
  rcases le_total p q with h | h
  · simp only [ekey, min_eq_left h, max_eq_right h]
  · simp only [ekey, min_eq_right h, max_eq_left h, Bool.or_comm]

theorem deg_eq_of_ekey_perm {T T' : RTree}
    (he : ((edges T').map ekey).Perm ((edges T).map ekey)) (v : ℕ) :
    deg T' v = deg T v := by
  have key : ∀ E : List (ℕ × ℕ),
      E.countP (fun e => e.1 = v || e.2 = v)
        = (E.map ekey).countP (fun e => e.1 = v || e.2 = v) := by
    intro E
    rw [List.countP_map]
    exact List.countP_congr (fun e _ => by rw [Function.comp_apply, ekey_incidence])
  change (edges T').countP _ = (edges T).countP _
  rw [key (edges T'), key (edges T)]
  exact he.countP_eq _

theorem form_eq_of_perms {R : Type} [CommRing R] {T T' : RTree} (x y : ℕ → R)
    (hv : (vwts T').Perm (vwts T))
    (he : ((edges T').map ekey).Perm ((edges T).map ekey)) :
    form T' x y = form T x y := by
  have hpt : ∀ e : ℕ × ℕ,
      x (ekey e).1 * y (ekey e).2 + x (ekey e).2 * y (ekey e).1
        = x e.1 * y e.2 + x e.2 * y e.1 := by
    rintro ⟨p, q⟩
    rcases le_total p q with h | h
    · simp only [ekey, min_eq_left h, max_eq_right h]
    · simp only [ekey, min_eq_right h, max_eq_left h]
      ring
  have key : ∀ E : List (ℕ × ℕ),
      (E.map (fun e => x e.1 * y e.2 + x e.2 * y e.1)).sum
        = ((E.map ekey).map (fun e => x e.1 * y e.2 + x e.2 * y e.1)).sum := by
    intro E
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left (fun e _ => (hpt e).symm))
  change ((vwts T').map _).sum - ((edges T').map _).sum
      = ((vwts T).map _).sum - ((edges T).map _).sum
  rw [key (edges T'), key (edges T), (hv.map _).sum_eq, (he.map _).sum_eq]

theorem wt_eq_of_lookup_eq {T T' : RTree}
    (h : ∀ v, (vwts T').lookup v = (vwts T).lookup v) (v : ℕ) : wt T' v = wt T v := by
  simp only [wt, h v]

/-! ## Re-assigning the weights: the surgery that restores `wt` -/

/-- Delete the first entry whose label is `a`. -/
def eraseKey (a : ℕ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => []
  | p :: l => if p.1 = a then l else p :: eraseKey a l

/-- The list of labels of a vertex-weight list. -/
def labs (l : List (ℕ × ℤ)) : List ℕ := l.map Prod.fst

/-- The DFS vertex-weight list of a forest. -/
def vwtsL (ts : List RTree) : List (ℕ × ℤ) := ts.flatMap vwts

/-- The DFS edge list of a forest. -/
def edgesL (ts : List RTree) : List (ℕ × ℕ) := ts.flatMap edges

@[simp] theorem labs_nil : labs [] = [] := rfl

@[simp] theorem labs_cons (k : ℕ) (w : ℤ) (l : List (ℕ × ℤ)) :
    labs ((k, w) :: l) = k :: labs l := rfl

@[simp] theorem labs_append (l₁ l₂ : List (ℕ × ℤ)) :
    labs (l₁ ++ l₂) = labs l₁ ++ labs l₂ := List.map_append

@[simp] theorem vwtsL_nil : vwtsL [] = [] := rfl

@[simp] theorem vwtsL_cons (t : RTree) (ts : List RTree) :
    vwtsL (t :: ts) = vwts t ++ vwtsL ts := rfl

@[simp] theorem edgesL_nil : edgesL [] = [] := rfl

@[simp] theorem edgesL_cons (t : RTree) (ts : List RTree) :
    edgesL (t :: ts) = edges t ++ edgesL ts := rfl

theorem vwts_node' (a : ℕ) (w : ℤ) (c : List RTree) :
    vwts (.node a w c) = (a, w) :: vwtsL c := vwts_node a w c

theorem edges_node' (a : ℕ) (w : ℤ) (c : List RTree) :
    edges (.node a w c) = c.map (fun t => (a, t.root)) ++ edgesL c := edges_node a w c

theorem lookup_append (v : ℕ) (l₁ l₂ : List (ℕ × ℤ)) :
    (l₁ ++ l₂).lookup v = (l₁.lookup v).orElse (fun _ => l₂.lookup v) := by
  induction l₁ with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : v = k
    · subst hk; simp
    · have hb : (v == k) = false := by simpa using hk
      simp [List.lookup_cons, hb, ih]

theorem lookup_eraseKey_ne {a v : ℕ} (h : v ≠ a) (l : List (ℕ × ℤ)) :
    (eraseKey a l).lookup v = l.lookup v := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = a
    · subst hk
      have hb : (v == k) = false := by simpa using h
      simp [eraseKey, List.lookup_cons, hb]
    · simp [eraseKey, hk, List.lookup_cons, ih]

theorem labs_eraseKey (a : ℕ) (l : List (ℕ × ℤ)) :
    labs (eraseKey a l) = (labs l).erase a := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = a
    · subst hk; simp [eraseKey]
    · have hb : ¬ (k == a) = true := by simpa using hk
      simp [eraseKey, hk, List.erase_cons_tail hb, ih]

theorem exists_lookup_of_mem_labs {a : ℕ} {l : List (ℕ × ℤ)} (h : a ∈ labs l) :
    ∃ w, l.lookup a = some w := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : a = k
    · subst hk; exact ⟨w, by simp⟩
    · have hb : (a == k) = false := by simpa using hk
      rw [labs_cons, List.mem_cons] at h
      obtain ⟨w', hw'⟩ := ih (h.resolve_left hk)
      exact ⟨w', by simp [List.lookup_cons, hb, hw']⟩

theorem perm_eraseKey {a : ℕ} {l : List (ℕ × ℤ)} (h : a ∈ labs l) :
    ((a, (l.lookup a).getD 0) :: eraseKey a l).Perm l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : k = a
    · subst hk; simp [eraseKey]
    · have hb : (a == k) = false := by simpa using fun hh : a = k => hk hh.symm
      rw [labs_cons, List.mem_cons] at h
      have hrec := ih (h.resolve_left (fun hh => hk hh.symm))
      simp only [eraseKey, if_neg hk, List.lookup_cons, hb]
      exact (List.Perm.swap _ _ _).trans (hrec.cons _)

/-- Re-assign the weights of a forest by walking it in DFS order and matching
labels against `l`, consuming one entry of `l` per vertex.  The second component
is the unconsumed remainder of `l`. -/
def relabelL : List RTree → List (ℕ × ℤ) → List RTree × List (ℕ × ℤ)
  | [], l => ([], l)
  | (.node a _ c) :: ts, l =>
      (RTree.node a ((l.lookup a).getD 0) (relabelL c (eraseKey a l)).1
          :: (relabelL ts (relabelL c (eraseKey a l)).2).1,
        (relabelL ts (relabelL c (eraseKey a l)).2).2)

theorem relabelL_shape (ts : List RTree) (l : List (ℕ × ℤ)) :
    (relabelL ts l).1.map RTree.root = ts.map RTree.root
      ∧ edgesL (relabelL ts l).1 = edgesL ts
      ∧ labs (vwtsL (relabelL ts l).1) = labs (vwtsL ts) := by
  induction ts, l using relabelL.induct with
  | case1 l => simp [relabelL]
  | case2 a w c ts l ih1 ih2 =>
    obtain ⟨rc, ec, vc⟩ := ih1
    obtain ⟨rt, et, vt⟩ := ih2
    have hmap : ∀ cc : List RTree,
        cc.map (fun t => (a, t.root)) = (cc.map RTree.root).map (fun r => (a, r)) := by
      intro cc; rw [List.map_map]; rfl
    refine ⟨by simp [relabelL, RTree.root, rt], ?_, ?_⟩
    · simp only [relabelL, edgesL_cons, edges_node']
      rw [hmap (relabelL c (eraseKey a l)).1, rc, ← hmap c, ec, et]
    · simp only [relabelL, vwtsL_cons, vwts_node', labs_append, labs_cons, vc, vt]

theorem relabelL_main : ∀ (ts : List RTree) (l : List (ℕ × ℤ)),
    (∀ x, (labs (vwtsL ts)).count x ≤ (labs l).count x) →
    (vwtsL (relabelL ts l).1 ++ (relabelL ts l).2).Perm l
      ∧ ∀ v, ((vwtsL (relabelL ts l).1 ++ (relabelL ts l).2).lookup v = l.lookup v) := by
  intro ts l
  induction ts, l using relabelL.induct with
  | case1 l => intro _; simp [relabelL]
  | case2 a w c ts l ih1 ih2 =>
    intro H
    have hlabs : labs (vwtsL (RTree.node a w c :: ts))
        = a :: (labs (vwtsL c) ++ labs (vwtsL ts)) := by
      simp [vwtsL]
    have hHa : (labs (vwtsL c)).count a + (labs (vwtsL ts)).count a + 1
        ≤ (labs l).count a := by
      have h1 := H a
      rw [hlabs, List.count_cons, List.count_append] at h1
      simpa using h1
    have hHx : ∀ x, x ≠ a → (labs (vwtsL c)).count x + (labs (vwtsL ts)).count x
        ≤ (labs l).count x := by
      intro x hx
      have h1 := H x
      rw [hlabs, List.count_cons, List.count_append] at h1
      have hb : ¬ (a == x) = true := by simpa using fun hh : a = x => hx hh.symm
      simpa [hb] using h1
    have hamem : a ∈ labs l := by
      rw [← List.count_pos_iff]
      omega
    have hera_a : (labs (eraseKey a l)).count a = (labs l).count a - 1 := by
      rw [labs_eraseKey, List.count_erase_self]
    have hera_x : ∀ x, x ≠ a → (labs (eraseKey a l)).count x = (labs l).count x := by
      intro x hx
      rw [labs_eraseKey, List.count_erase_of_ne hx]
    have hH1 : ∀ x, (labs (vwtsL c)).count x ≤ (labs (eraseKey a l)).count x := by
      intro x
      by_cases hx : x = a
      · subst hx; omega
      · rw [hera_x x hx]
        have := hHx x hx
        omega
    obtain ⟨p1, q1⟩ := ih1 hH1
    have hshape1 := (relabelL_shape c (eraseKey a l)).2.2
    have hH2 : ∀ x, (labs (vwtsL ts)).count x
        ≤ (labs (relabelL c (eraseKey a l)).2).count x := by
      intro x
      have hc : (labs (vwtsL (relabelL c (eraseKey a l)).1)).count x
          + (labs (relabelL c (eraseKey a l)).2).count x
          = (labs (eraseKey a l)).count x := by
        have hp := (p1.map Prod.fst).count_eq x
        rw [List.map_append, List.count_append] at hp
        exact hp
      rw [hshape1] at hc
      by_cases hx : x = a
      · subst hx; omega
      · rw [hera_x x hx] at hc
        have := hHx x hx
        omega
    obtain ⟨p2, q2⟩ := ih2 hH2
    have hunf : vwtsL (relabelL (RTree.node a w c :: ts) l).1
        = ((a, (l.lookup a).getD 0) :: vwtsL (relabelL c (eraseKey a l)).1)
          ++ vwtsL (relabelL ts (relabelL c (eraseKey a l)).2).1 := by
      simp [relabelL, vwtsL]
    have hrem : (relabelL (RTree.node a w c :: ts) l).2
        = (relabelL ts (relabelL c (eraseKey a l)).2).2 := by
      simp [relabelL]
    constructor
    · rw [hunf, hrem]
      simp only [List.cons_append, List.append_assoc]
      refine List.Perm.trans (List.Perm.cons _ ?_) (perm_eraseKey hamem)
      exact (List.Perm.append_left _ p2).trans (by simpa using p1)
    · intro v
      rw [hunf, hrem]
      by_cases hv : v = a
      · subst hv
        obtain ⟨w0, hw0⟩ := exists_lookup_of_mem_labs hamem
        simp [hw0]
      · have hb : (v == a) = false := by simpa using hv
        simp only [List.cons_append, List.append_assoc, List.lookup_cons, hb]
        rw [lookup_append, q2 v, ← lookup_append, q1 v, lookup_eraseKey_ne hv]

theorem relabelL_singleton (t : RTree) (l : List (ℕ × ℤ)) :
    ∃ s : RTree, (relabelL [t] l).1 = [s] := by
  cases t with
  | node a w c =>
    exact ⟨RTree.node a ((l.lookup a).getD 0) (relabelL c (eraseKey a l)).1,
      by simp [relabelL]⟩

/-- The surgery packaged for a single tree: any tree `s` whose vertex-weight
list is a permutation of `l` can have its weights re-assigned so that the
resulting tree has the *same* `List.lookup` behaviour as `l`, without touching
its labels (hence without touching `edges`, `verts` or the root). -/
theorem exists_relabel (s : RTree) (l : List (ℕ × ℤ)) (hs : (vwts s).Perm l) :
    ∃ s' : RTree, s'.root = s.root ∧ edges s' = edges s ∧ (vwts s').Perm l ∧
      ∀ v, (vwts s').lookup v = l.lookup v := by
  obtain ⟨s', hs'⟩ := relabelL_singleton s l
  have hshape := relabelL_shape [s] l
  rw [hs'] at hshape
  obtain ⟨hroots, hedges, hlabsEq⟩ := hshape
  have hcount : ∀ x, (labs (vwtsL [s])).count x ≤ (labs l).count x := by
    intro x
    have h := (hs.map Prod.fst).count_eq x
    simp only [vwtsL_cons, vwtsL_nil, List.append_nil]
    exact le_of_eq h
  obtain ⟨hperm, hlookup⟩ := relabelL_main [s] l hcount
  rw [hs'] at hperm hlookup
  simp only [vwtsL_cons, vwtsL_nil, List.append_nil] at hperm hlookup
  have hlen : (vwts s').length = (vwts s).length := by
    have := congrArg List.length hlabsEq
    simpa [labs] using this
  have hrem : (relabelL [s] l).2 = [] := by
    have h1 := hperm.length_eq
    have h2 := hs.length_eq
    rw [List.length_append] at h1
    rw [List.length_eq_zero_iff.symm]
    omega
  rw [hrem, List.append_nil] at hperm hlookup
  refine ⟨s', ?_, ?_, hperm, hlookup⟩
  · simpa using hroots
  · simpa using hedges

end Reroot

open Reroot in
/-- Frozen theorem #11 (`Theorems.lean:57-60`): re-rooting loses nothing. -/
theorem exists_reroot_at_proof (T : RTree) (u : ℕ) (hu : u ∈ verts T) :
    ∃ T' : RTree, T'.root = u ∧ (verts T').Perm (verts T) ∧
      (∀ v : ℕ, wt T' v = wt T v) ∧ (∀ v : ℕ, deg T' v = deg T v) ∧
      (∀ x y : ℕ → ℤ, B T' x y = B T x y) := by
  obtain ⟨s, hsroot, hsv, hse⟩ := reroot_core T u hu []
  rw [att_nil] at hsv hse
  obtain ⟨s', hroot', hedges', hperm', hlookup'⟩ := exists_relabel s (vwts T) hsv
  have hse' : ((edges s').map ekey).Perm ((edges T).map ekey) := by
    rw [hedges']; exact hse
  refine ⟨s', by rw [hroot', hsroot], hperm'.map Prod.fst, ?_, ?_, ?_⟩
  · exact wt_eq_of_lookup_eq hlookup'
  · exact deg_eq_of_ekey_perm hse'
  · intro x y
    exact form_eq_of_perms x y hperm' hse'

namespace Reroot

/-! ## Guardrails on a concrete 3-vertex path (`norm_num`, never `decide`) -/

/-- The 3-vertex path, rooted at the end labelled `0`. -/
private def P : RTree := .node 0 2 [.node 1 2 [.node 2 2 []]]

/-- The same path, rooted at the other end. -/
private def Q : RTree := .node 2 2 [.node 1 2 [.node 0 2 []]]

example : P.root = 0 := rfl

example : Q.root = 2 := rfl

example : verts P = [0, 1, 2] := by norm_num [P]

example : verts Q = [2, 1, 0] := by norm_num [Q]

example : edges P = [(0, 1), (1, 2)] := by norm_num [P, RTree.root]

example : edges Q = [(2, 1), (1, 0)] := by norm_num [Q, RTree.root]

example : deg Q 0 = deg P 0 ∧ deg Q 1 = deg P 1 ∧ deg Q 2 = deg P 2 := by
  norm_num [P, Q, deg, RTree.root]

example : wt Q 0 = wt P 0 ∧ wt Q 1 = wt P 1 ∧ wt Q 2 = wt P 2 := by
  have hP : vwts P = [(0, 2), (1, 2), (2, 2)] := by norm_num [P]
  have hQ : vwts Q = [(2, 2), (1, 2), (0, 2)] := by norm_num [Q]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [wt, hP, hQ] <;> rfl

example : B Q (basis 0) (basis 1) = B P (basis 0) (basis 1) := by
  norm_num [P, Q, form, basis, RTree.root]

example : ∃ T' : RTree, T'.root = 2 ∧ (verts T').Perm (verts P) ∧
    (∀ v : ℕ, wt T' v = wt P v) ∧ (∀ v : ℕ, deg T' v = deg P v) ∧
    (∀ x y : ℕ → ℤ, B T' x y = B P x y) :=
  exists_reroot_at_proof P 2 (by norm_num [P])

end Reroot

end TreeIrred
