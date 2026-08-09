import TreeIrred.Defs

/-!
# Stage C -- the capacity recursion and `0 < gamma < 1` (Lemma 2)

Frozen theorems #3--#6 (`capacity_node_formula`, `capacity_denom_pos`,
`capacity_pos`, `capacity_lt_one`), proved here as `<name>_proof`.
See `BLUEPRINT.md` Part 2, Stage C and `SKETCH.md` Lemma 2.

The support lemmas live in the nested `namespace TreeIrred.Capacity` so that
they cannot clash with Stage A's top-level `attach`-unfolding helpers, which are
being written concurrently.
-/

namespace TreeIrred

namespace Capacity

/-- Local copy of the Stage A `attach`-map helper, specialised to `gamma`:
`gamma` recurses through `c.attach`, and nothing unfolds without this. -/
theorem attach_map_gamma (c : List RTree) :
    c.attach.map (fun t => gamma t.1) = c.map gamma := by
  simp

/-- The Schur recursion with `c.attach` replaced by `c` (frozen statement #3). -/
theorem gamma_node (a : ℕ) (w : ℤ) (c : List RTree) :
    gamma (RTree.node a w c) = 1 / ((w : ℚ) - (c.map gamma).sum) := by
  rw [gamma, attach_map_gamma]

/-- If every capacity in a list is at most `1`, the sum is at most the length. -/
theorem sum_le_length {c : List RTree} (h : ∀ t ∈ c, gamma t ≤ 1) :
    (c.map gamma).sum ≤ (c.length : ℚ) := by
  induction c with
  | nil => simp
  | cons hd tl ih =>
      have h1 : gamma hd ≤ 1 := h hd (by simp)
      have h2 : (tl.map gamma).sum ≤ (tl.length : ℚ) :=
        ih fun t ht => h t (List.mem_cons_of_mem _ ht)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- Every capacity in the list is `< 1`, so the sum stays strictly below any
`n` that dominates both `1` and the length.  The `c = []` case is the *same*
computation: the empty sum is `0 < 1 ≤ n`. -/
theorem sum_lt_of_le {c : List RTree} (h : ∀ t ∈ c, gamma t < 1) {n : ℚ}
    (h1 : 1 ≤ n) (hn : (c.length : ℚ) ≤ n) : (c.map gamma).sum < n := by
  cases c with
  | nil => simpa using lt_of_lt_of_le zero_lt_one h1
  | cons hd tl =>
      have hhd : gamma hd < 1 := h hd (by simp)
      have htl : (tl.map gamma).sum ≤ (tl.length : ℚ) :=
        sum_le_length fun t ht => le_of_lt (h t (List.mem_cons_of_mem _ ht))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hn
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- The heart of Lemma 2: one induction giving the *strict* denominator bound
`1 < w - Σ γᵢ` together with `0 < γ < 1`. -/
theorem key : ∀ C : RTree, Admissible C →
    1 < (C.wtRoot : ℚ) - (C.kids.map gamma).sum ∧ 0 < gamma C ∧ gamma C < 1 := by
  intro C
  induction C using RTree.recAll with
  | _ a w c ih =>
    intro hC
    rw [Admissible] at hC
    obtain ⟨hw2, hwl, hkids⟩ := hC
    have hlt1 : ∀ t ∈ c, gamma t < 1 := fun t ht => (ih t ht (hkids t ht)).2.2
    have hw2' : (2 : ℚ) ≤ (w : ℚ) := by exact_mod_cast hw2
    have hwl' : (c.length : ℚ) + 1 ≤ (w : ℚ) := by exact_mod_cast hwl
    have hsum : (c.map gamma).sum < (w : ℚ) - 1 :=
      sum_lt_of_le hlt1 (by linarith) (by linarith)
    have hden : 1 < (w : ℚ) - (c.map gamma).sum := by linarith
    refine ⟨hden, ?_, ?_⟩
    · rw [gamma_node]
      exact div_pos zero_lt_one (by linarith)
    · rw [gamma_node, div_lt_one (by linarith)]
      exact hden

end Capacity

/-! ## The four frozen statements -/

theorem capacity_node_formula_proof (a : ℕ) (w : ℤ) (c : List RTree) :
    gamma (RTree.node a w c) = 1 / ((w : ℚ) - (c.map gamma).sum) :=
  Capacity.gamma_node a w c

theorem capacity_denom_pos_proof (C : RTree) (hC : Admissible C) :
    0 < (C.wtRoot : ℚ) - (C.kids.map gamma).sum := by
  have h := (Capacity.key C hC).1
  linarith

theorem capacity_pos_proof (C : RTree) (hC : Admissible C) : 0 < gamma C :=
  (Capacity.key C hC).2.1

theorem capacity_lt_one_proof (C : RTree) (hC : Admissible C) : gamma C < 1 :=
  (Capacity.key C hC).2.2

/-! ## Guardrails (modelling sanity checks; `norm_num`, never `decide`) -/

example : gamma (.node 0 2 [.node 1 2 [.node 2 2 []]]) = 3 / 4 := by
  norm_num [gamma]

example : gamma (.node 0 3 [.node 1 2 [], .node 2 2 []]) = 1 / 2 := by
  norm_num [gamma]

end TreeIrred
