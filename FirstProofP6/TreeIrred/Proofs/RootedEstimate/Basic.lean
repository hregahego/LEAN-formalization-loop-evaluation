import TreeIrred.Proofs.Model.Basic
import TreeIrred.Proofs.Capacity.Basic

/-!
# Stage E -- Lemma 3, the rooted estimate -- the mathematical heart

Frozen theorem #9 `rooted_estimate` (`TreeIrred/Theorems.lean:49-50`), proved
here as `TreeIrred.rooted_estimate_proof`, following `BLUEPRINT.md` Part 2
Stage E (E1--E6) and `SKETCH.md` Lemma 3.

The support lemmas live in the nested `namespace TreeIrred.RootedEstimate`.
-/

namespace TreeIrred

namespace RootedEstimate

/-! ## List helpers over `ℚ` -/

/-- Termwise comparison of two list sums. -/
theorem sum_map_le {α : Type*} {l : List α} {f g : α → ℚ} (h : ∀ t ∈ l, f t ≤ g t) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons b tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := h b (by simp)
    have htl := ih fun s hs => h s (by simp [hs])
    linarith

/-- A list sum of nonnegative terms is nonnegative. -/
theorem sum_map_nonneg {α : Type*} {l : List α} {f : α → ℚ} (h : ∀ t ∈ l, 0 ≤ f t) :
    0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := h b (by simp)
    have htl := ih fun s hs => h s (by simp [hs])
    linarith

/-- The triangle inequality for a list sum. -/
theorem abs_sum_le_sum_abs {α : Type*} (l : List α) (f : α → ℚ) :
    |(l.map f).sum| ≤ (l.map fun t => |f t|).sum := by
  induction l with
  | nil => simp
  | cons b tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (by linarith)

/-- `Σᵢ (sᵢ - γᵢ·A) = Σᵢ sᵢ - (Σᵢ γᵢ)·A`. -/
theorem sum_diff (c : List RTree) (s : RTree → ℚ) (A : ℚ) :
    (c.map fun t => s t - gamma t * A).sum = (c.map s).sum - (c.map gamma).sum * A := by
  induction c with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-! ## E3 -- summing the child bounds through `form_node` -/

/-- Summing the child lower bounds of E2 across `form_node`: if every child of
`.node a w c` satisfies the E2 estimate then the form at the node is bounded
below by `(w - Σγᵢ)·A² + D`.  The `c = []` case is the same computation. -/
theorem node_lower (a : ℕ) (w : ℤ) (c : List RTree) (X : ℕ → ℚ)
    (h : ∀ t ∈ c, -(gamma t) * (X a) ^ 2 + |X t.root - gamma t * X a|
      ≤ form t X X - 2 * X a * X t.root) :
    ((w : ℚ) - (c.map gamma).sum) * (X a) ^ 2
        + (c.map fun t => |X t.root - gamma t * X a|).sum
      ≤ form (RTree.node a w c) X X := by
  rw [form_node]
  induction c with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    linarith
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := h b (by simp)
    have hl := ih fun t ht => h t (by simp [ht])
    linarith

/-! ## E4/E5 -- the arithmetic core -/

/-- The purely arithmetic heart of Lemma 3.  With `τ = A·Wd` the target is
`0 ≤ γ(τ-k)(τ-k-1) + D`; it is closed by the sign of `(τ-k)(τ-k-1)` outside
`(k, k+1)`, and inside `(k, k+1)` by the integer `M` at distance
`|τ - M| ≤ D` from `τ`. -/
theorem core {Wd A D g : ℚ} {k M : ℤ}
    (hgw : g * Wd = 1) (hg0 : 0 < g) (hg1 : g < 1)
    (hD0 : 0 ≤ D) (hDM : |A * Wd - (M : ℚ)| ≤ D) :
    0 ≤ Wd * A ^ 2 + D - (2 * (k : ℚ) + 1) * A + g * (k : ℚ) * ((k : ℚ) + 1) := by
  have hid : Wd * A ^ 2 + D - (2 * (k : ℚ) + 1) * A + g * (k : ℚ) * ((k : ℚ) + 1)
      = g * (A * Wd - (k : ℚ)) * (A * Wd - (k : ℚ) - 1) + D := by
    linear_combination ((2 * (k : ℚ) + 1) * A - Wd * A ^ 2) * hgw
  rw [hid]
  rcases le_or_gt (A * Wd) (k : ℚ) with h | h
  · have h1 : (0 : ℚ) ≤ (-(A * Wd - (k : ℚ))) * (-(A * Wd - (k : ℚ) - 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg hg0.le h1]
  · rcases le_or_gt ((k : ℚ) + 1) (A * Wd) with h2 | h2
    · have h1 : (0 : ℚ) ≤ (A * Wd - (k : ℚ)) * (A * Wd - (k : ℚ) - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hg0.le h1]
    · -- `k < τ < k+1`: the integer `M` cannot lie strictly between `k` and `k+1`
      have hal : 0 < A * Wd - (k : ℚ) := by linarith
      have hbe : 0 < (k : ℚ) + 1 - A * Wd := by linarith
      have hMcase : ((M : ℚ) ≤ (k : ℚ)) ∨ ((k : ℚ) + 1 ≤ (M : ℚ)) := by
        rcases le_or_gt M k with hm | hm
        · exact Or.inl (by exact_mod_cast hm)
        · refine Or.inr ?_
          have hm' : k + 1 ≤ M := hm
          exact_mod_cast hm'
      have hprodle : (A * Wd - (k : ℚ)) * ((k : ℚ) + 1 - A * Wd) ≤ D := by
        rcases hMcase with hm | hm
        · have h3 : A * Wd - (M : ℚ) ≤ |A * Wd - (M : ℚ)| := le_abs_self _
          nlinarith [sq_nonneg (A * Wd - (k : ℚ))]
        · have h3 : (M : ℚ) - A * Wd ≤ |A * Wd - (M : ℚ)| := by
            rw [abs_sub_comm]
            exact le_abs_self _
          nlinarith [sq_nonneg ((k : ℚ) + 1 - A * Wd)]
      nlinarith [mul_pos (sub_pos.mpr hg1) (mul_pos hal hbe)]

/-! ## The induction -/

/-- Lemma 3, in the form the induction needs (`k` generalised). -/
theorem main : ∀ C : RTree, Admissible C → ∀ (x : ℕ → ℤ) (k : ℤ),
    0 ≤ (B C x x : ℚ) - (2 * k + 1) * (x C.root : ℚ) + gamma C * k * (k + 1) := by
  intro C
  induction C using RTree.recAll with
  | _ a w c ih =>
    intro hC x k
    simp only [RTree.root]
    have hden : 1 < (w : ℚ) - (c.map gamma).sum := (Capacity.key (RTree.node a w c) hC).1
    have hWdpos : (0 : ℚ) < (w : ℚ) - (c.map gamma).sum := by linarith
    have hg0 : 0 < gamma (RTree.node a w c) := capacity_pos_proof _ hC
    have hg1 : gamma (RTree.node a w c) < 1 := capacity_lt_one_proof _ hC
    have hgw : gamma (RTree.node a w c) * ((w : ℚ) - (c.map gamma).sum) = 1 := by
      rw [capacity_node_formula_proof, one_div, inv_mul_cancel₀ (ne_of_gt hWdpos)]
    have hC' := hC
    rw [Admissible] at hC'
    obtain ⟨-, -, hkids⟩ := hC'
    have hcast : ∀ t : RTree, ((B t x x : ℤ) : ℚ)
        = form t (fun u => ((x u : ℤ) : ℚ)) (fun u => ((x u : ℤ) : ℚ)) :=
      fun t => form_cast t x x
    -- E1 + E2 + E3: the lower bound on the form at the node
    have hlow : ((w : ℚ) - (c.map gamma).sum) * ((x a : ℤ) : ℚ) ^ 2
        + (c.map fun t => |((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ)|).sum
        ≤ form (RTree.node a w c) (fun u => ((x u : ℤ) : ℚ))
            (fun u => ((x u : ℤ) : ℚ)) := by
      refine node_lower a w c (fun u => ((x u : ℤ) : ℚ)) ?_
      intro t ht
      have h1 := ih t ht (hkids t ht) x (x a)
      have h2 := ih t ht (hkids t ht) x (x a - 1)
      rw [hcast t] at h1 h2
      push_cast at h2
      rcases abs_cases (((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ)) with
        ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] <;> linarith
    -- the integer witness `M = w·A - Σᵢ sᵢ` and the triangle inequality
    have hMcast : ((w * x a - (c.map fun t => x t.root).sum : ℤ) : ℚ)
        = (w : ℚ) * ((x a : ℤ) : ℚ) - (c.map fun t => ((x t.root : ℤ) : ℚ)).sum := by
      rw [Int.cast_sub, Int.cast_mul, cast_sum_map]
    have hsd := sum_diff c (fun t => ((x t.root : ℤ) : ℚ)) ((x a : ℤ) : ℚ)
    have hsum : ((x a : ℤ) : ℚ) * ((w : ℚ) - (c.map gamma).sum)
          - ((w * x a - (c.map fun t => x t.root).sum : ℤ) : ℚ)
        = (c.map fun t => ((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ)).sum := by
      rw [hsd, hMcast]
      ring
    have hDM : |((x a : ℤ) : ℚ) * ((w : ℚ) - (c.map gamma).sum)
          - ((w * x a - (c.map fun t => x t.root).sum : ℤ) : ℚ)|
        ≤ (c.map fun t => |((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ)|).sum := by
      rw [hsum]
      exact abs_sum_le_sum_abs c
        (fun t => ((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ))
    have hD0 : (0 : ℚ)
        ≤ (c.map fun t => |((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ)|).sum :=
      sum_map_nonneg fun t _ => abs_nonneg _
    have hcore := core (Wd := (w : ℚ) - (c.map gamma).sum) (A := ((x a : ℤ) : ℚ))
      (D := (c.map fun t => |((x t.root : ℤ) : ℚ) - gamma t * ((x a : ℤ) : ℚ)|).sum)
      (g := gamma (RTree.node a w c)) (k := k)
      (M := w * x a - (c.map fun t => x t.root).sum) hgw hg0 hg1 hD0 hDM
    rw [hcast (RTree.node a w c)]
    linarith

end RootedEstimate

/-! ## The frozen statement -/

theorem rooted_estimate_proof (C : RTree) (hC : Admissible C) (x : ℕ → ℤ) (k : ℤ) :
    0 ≤ (B C x x : ℚ) - (2 * k + 1) * (x C.root : ℚ) + gamma C * k * (k + 1) :=
  RootedEstimate.main C hC x k

/-! ## Guardrails (modelling sanity checks; `norm_num`, never `decide`) -/

example : Admissible (RTree.node 0 2 [RTree.node 1 2 [RTree.node 2 2 []]]) := by
  norm_num [Admissible]

/-- The estimate really does apply, at every `k`, to the concrete path `P`. -/
example (x : ℕ → ℤ) (k : ℤ) :
    0 ≤ (B (RTree.node 0 2 [RTree.node 1 2 [RTree.node 2 2 []]]) x x : ℚ)
      - (2 * k + 1) * (x 0 : ℚ)
      + gamma (RTree.node 0 2 [RTree.node 1 2 [RTree.node 2 2 []]]) * k * (k + 1) :=
  rooted_estimate_proof _ (by norm_num [Admissible]) x k

end TreeIrred
