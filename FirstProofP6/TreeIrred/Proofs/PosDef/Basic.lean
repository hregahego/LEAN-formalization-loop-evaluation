import TreeIrred.Proofs.Model.Basic
import TreeIrred.Proofs.Capacity.Basic

/-!
# Stage D -- rational form, the dual vector `ρ^#`, positive definiteness

Frozen theorems #7 (`capacity_spec`) and #8 (`admissible_posDef`), proved here as
`capacity_spec_proof` and `admissible_posDef_proof`, together with the support
lemmas Stages F and H consume: `dualScaled`, `dual`, `dual_vanish`, `dual_apply`,
`psd_gamma`, `posDefQ_of_posDef`.  See `BLUEPRINT.md` Part 2, Stage D (D1--D6).

Purely internal helpers live in the nested `namespace TreeIrred.PosDef`.
-/

namespace TreeIrred

/-! ## D1 -- the dual vector `ρ^#` -/

/-- The scaled dual vector: `dualScaled C s` is `s` times the vector `ρ^#` of
`SKETCH.md`, the solution of `Q_C · ρ^# = e_ρ`.  The scaling parameter is what
lets the definition recurse: the restriction of `ρ^#` to a child subtree `Cᵢ` is
`γ · (ρᵢ)^#` computed inside `Cᵢ`. -/
def dualScaled : RTree → ℚ → (ℕ → ℚ)
  | .node a w c, s => fun u =>
      if u = a then s * gamma (.node a w c)
      else (c.attach.map (fun t => dualScaled t.1 (s * gamma (.node a w c)) u)).sum
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem t.2
  omega

/-- The dual vector `ρ^#` itself. -/
def dual (C : RTree) : ℕ → ℚ := dualScaled C 1

/-- `dualScaled` at a node, with `c.attach` replaced by `c`. -/
theorem dualScaled_node (a : ℕ) (w : ℤ) (c : List RTree) (s : ℚ) (u : ℕ) :
    dualScaled (RTree.node a w c) s u =
      if u = a then s * gamma (RTree.node a w c)
      else (c.map (fun t => dualScaled t (s * gamma (RTree.node a w c)) u)).sum := by
  simp only [dualScaled]
  rw [attach_map_eq c (fun t => dualScaled t (s * gamma (RTree.node a w c)) u)]

/-- The value of the dual vector at the root. -/
theorem dualScaled_root (C : RTree) (s : ℚ) : dualScaled C s C.root = s * gamma C := by
  cases C with
  | node a w c => rw [dualScaled_node]; simp [RTree.root]

/-! ## D2 -- the defining property of `ρ^#` -/

/-- The dual vector vanishes off the tree (no `Nodup` needed). -/
theorem dual_vanish : ∀ (C : RTree) (s : ℚ) (u : ℕ), u ∉ verts C → dualScaled C s u = 0 := by
  intro C
  induction C using RTree.recAll with
  | _ a w c ih =>
    intro s u hu
    rw [verts_node, List.mem_cons, not_or] at hu
    obtain ⟨hua, huc⟩ := hu
    rw [dualScaled_node, if_neg hua]
    refine List.sum_eq_zero ?_
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    exact ih t ht _ u fun h => huc (List.mem_flatMap.2 ⟨t, ht, h⟩)

/-- On the vertices of a child subtree, the dual vector of the whole tree is the
(rescaled) dual vector of that subtree. -/
theorem PosDef.dual_restrict {a : ℕ} {w : ℤ} {c : List RTree}
    (hnd : (verts (RTree.node a w c)).Nodup) (s : ℚ) {t : RTree} (ht : t ∈ c)
    {v : ℕ} (hv : v ∈ verts t) :
    dualScaled (RTree.node a w c) s v = dualScaled t (s * gamma (RTree.node a w c)) v := by
  have hfl : (c.flatMap verts).Nodup := verts_node_flatMap_nodup hnd
  have hva : v ≠ a := fun h => verts_node_root_not_mem hnd ht (h ▸ hv)
  rw [dualScaled_node, if_neg hva]
  refine sum_map_eq_single (kids_nodup hfl) ht _ ?_
  intro t' ht' hne
  exact dual_vanish t' _ v (verts_node_nodup_disjoint hfl ht ht' (Ne.symm hne) hv)

/-- **D2.**  `ρ^#` really is the dual of the root: `BQ C (dualScaled C s) y = s * y ρ`
for **every** rational vector `y`. -/
theorem dual_apply : ∀ (C : RTree), (verts C).Nodup → Admissible C →
    ∀ (s : ℚ) (y : ℕ → ℚ), BQ C (dualScaled C s) y = s * y C.root := by
  intro C
  induction C using RTree.recAll with
  | _ a w c ih =>
    intro hnd hC s y
    have hfl : (c.flatMap verts).Nodup := verts_node_flatMap_nodup hnd
    have hC' := hC
    rw [Admissible] at hC'
    obtain ⟨-, -, hkids⟩ := hC'
    have hden : (0 : ℚ) < (w : ℚ) - (c.map gamma).sum := capacity_denom_pos_proof _ hC
    have hg : gamma (RTree.node a w c) * ((w : ℚ) - (c.map gamma).sum) = 1 := by
      rw [capacity_node_formula_proof a w c]
      field_simp
    set g : ℚ := gamma (RTree.node a w c) with hgdef
    have hroot : dualScaled (RTree.node a w c) s a = s * g := by
      rw [dualScaled_node, if_pos rfl]
    -- the child forms, by the induction hypothesis
    have hchild : ∀ t ∈ c, form t (dualScaled (RTree.node a w c) s) y = s * g * y t.root := by
      intro t ht
      have hcg : form t (dualScaled (RTree.node a w c) s) y
          = form t (dualScaled t (s * g)) y :=
        form_congr t _ _ y fun v hv => PosDef.dual_restrict hnd s ht hv
      rw [hcg]
      exact ih t ht (verts_child_nodup hfl ht) (hkids t ht) (s * g) y
    -- the values of the dual vector at the child roots
    have hkidroot : ∀ t ∈ c, dualScaled (RTree.node a w c) s t.root = s * g * gamma t := by
      intro t ht
      rw [PosDef.dual_restrict hnd s ht (root_mem_verts t), dualScaled_root]
    change form (RTree.node a w c) (dualScaled (RTree.node a w c) s) y = s * y a
    rw [form_node]
    have h1 : (c.map fun t => form t (dualScaled (RTree.node a w c) s) y).sum
        = (c.map fun t => s * g * y t.root).sum :=
      congrArg List.sum (List.map_congr_left hchild)
    have h2 : (c.map fun t => dualScaled (RTree.node a w c) s a * y t.root
          + dualScaled (RTree.node a w c) s t.root * y a).sum
        = (c.map fun t => s * g * y t.root).sum + (c.map fun t => s * g * y a * gamma t).sum := by
      rw [← List.sum_map_add]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro t ht
      rw [hroot, hkidroot t ht]
      ring
    rw [h1, h2, hroot]
    have h3 : (c.map fun t => s * g * y a * gamma t).sum = s * g * y a * (c.map gamma).sum :=
      List.sum_map_mul_left c gamma (s * g * y a)
    rw [h3]
    have : (w : ℚ) * (s * g) * y a - s * g * y a * (c.map gamma).sum
        = s * y a * (g * ((w : ℚ) - (c.map gamma).sum)) := by ring
    rw [show (w : ℚ) * (s * g) * y a + (c.map fun t => s * g * y t.root).sum
        - ((c.map fun t => s * g * y t.root).sum + s * g * y a * (c.map gamma).sum)
        = (w : ℚ) * (s * g) * y a - s * g * y a * (c.map gamma).sum from by ring, this, hg]
    ring

/-! ## D3 -- frozen theorem #7 -/

theorem capacity_spec_proof (C : RTree) (hnd : (verts C).Nodup) (hC : Admissible C) :
    ∃ u : ℕ → ℚ, (∀ y : ℕ → ℚ, BQ C u y = y C.root) ∧ BQ C u u = gamma C := by
  have hr : dual C C.root = gamma C := by rw [dual, dualScaled_root, one_mul]
  refine ⟨dual C, fun y => ?_, ?_⟩
  · have h := dual_apply C hnd hC 1 y
    rw [one_mul] at h
    exact h
  · have h := dual_apply C hnd hC 1 (dual C)
    rw [one_mul, hr] at h
    exact h

/-! ## D4 -- the positive-semidefinite estimate `psd_gamma` -/

namespace PosDef

/-- The node expansion of `form T x x`, regrouped as the Schur term
`(w − Σγᵢ)·x(ρ)²` plus one completed-square bracket per child. -/
theorem form_node_split (a : ℕ) (w : ℤ) (c : List RTree) (x : ℕ → ℚ) :
    form (RTree.node a w c) x x
      = ((w : ℚ) - (c.map gamma).sum) * x a ^ 2
        + (c.map fun t => form t x x - 2 * x a * x t.root + gamma t * x a ^ 2).sum := by
  rw [form_node]
  induction c with
  | nil => simp; ring
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    linear_combination ih

/-- A list sum of nonnegative terms with one strictly positive term is positive. -/
theorem sum_pos_of_mem {α : Type*} {c : List α} {f : α → ℚ}
    (hnn : ∀ t ∈ c, 0 ≤ f t) {t₀ : α} (ht₀ : t₀ ∈ c) (hpos : 0 < f t₀) :
    0 < (c.map f).sum := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ht₀
  have h1 : 0 ≤ (l₁.map f).sum := by
    refine List.sum_nonneg ?_
    intro z hz
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
    exact hnn s (List.mem_append_left _ hs)
  have h2 : 0 ≤ (l₂.map f).sum := by
    refine List.sum_nonneg ?_
    intro z hz
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
    exact hnn s (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  linarith

/-- Sums of nonnegative terms are nonnegative. -/
theorem sum_nonneg_of_mem {α : Type*} {c : List α} {f : α → ℚ}
    (hnn : ∀ t ∈ c, 0 ≤ f t) : 0 ≤ (c.map f).sum := by
  refine List.sum_nonneg ?_
  intro z hz
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  exact hnn s hs

end PosDef

/-- **D4.**  The completed-square estimate: for every admissible `C`, every
rational vector `x` and every `t : ℚ`,
`BQ C x x - 2·t·x(ρ) + γ(C)·t² ≥ 0`.  No `Nodup` is needed. -/
theorem psd_gamma : ∀ (C : RTree), Admissible C → ∀ (x : ℕ → ℚ) (t : ℚ),
    0 ≤ BQ C x x - 2 * t * x C.root + gamma C * t ^ 2 := by
  intro C
  induction C using RTree.recAll with
  | _ a w c ih =>
    intro hC x t
    have hC' := hC
    rw [Admissible] at hC'
    obtain ⟨-, -, hkids⟩ := hC'
    have hden : (0 : ℚ) < (w : ℚ) - (c.map gamma).sum := capacity_denom_pos_proof _ hC
    have hgpos : 0 < gamma (RTree.node a w c) := capacity_pos_proof _ hC
    have hg : gamma (RTree.node a w c) * ((w : ℚ) - (c.map gamma).sum) = 1 := by
      rw [capacity_node_formula_proof a w c]
      field_simp
    have hbr : ∀ s ∈ c, 0 ≤ form s x x - 2 * x a * x s.root + gamma s * x a ^ 2 :=
      fun s hs => ih s hs (hkids s hs) x (x a)
    have hsum : 0 ≤ (c.map fun s => form s x x - 2 * x a * x s.root + gamma s * x a ^ 2).sum :=
      PosDef.sum_nonneg_of_mem hbr
    change 0 ≤ form (RTree.node a w c) x x - 2 * t * x a + gamma (RTree.node a w c) * t ^ 2
    rw [PosDef.form_node_split]
    have hsq : 0 ≤ (x a - gamma (RTree.node a w c) * t) ^ 2 / gamma (RTree.node a w c) :=
      div_nonneg (sq_nonneg _) hgpos.le
    have hid : ((w : ℚ) - (c.map gamma).sum) * x a ^ 2 - 2 * t * x a
        + gamma (RTree.node a w c) * t ^ 2
        = (x a - gamma (RTree.node a w c) * t) ^ 2 / gamma (RTree.node a w c) := by
      rw [eq_div_iff (ne_of_gt hgpos)]
      linear_combination (x a ^ 2) * hg
    linarith

/-! ## D5 -- frozen theorem #8 -/

/-- The rational form is positive definite on admissible trees.  This is the
real content of `admissible_posDef`; the integral statement is a cast away. -/
theorem PosDef.posDefQ : ∀ (C : RTree), Admissible C → ∀ x : ℕ → ℚ,
    (∃ u ∈ verts C, x u ≠ 0) → 0 < BQ C x x := by
  intro C
  induction C using RTree.recAll with
  | _ a w c ih =>
    intro hC x hx
    have hC' := hC
    rw [Admissible] at hC'
    obtain ⟨-, -, hkids⟩ := hC'
    have hden : (0 : ℚ) < (w : ℚ) - (c.map gamma).sum := capacity_denom_pos_proof _ hC
    have hbr : ∀ s ∈ c, 0 ≤ form s x x - 2 * x a * x s.root + gamma s * x a ^ 2 :=
      fun s hs => psd_gamma s (hkids s hs) x (x a)
    have hsum : 0 ≤ (c.map fun s => form s x x - 2 * x a * x s.root + gamma s * x a ^ 2).sum :=
      PosDef.sum_nonneg_of_mem hbr
    change 0 < form (RTree.node a w c) x x
    rw [PosDef.form_node_split]
    by_cases ha : x a = 0
    · obtain ⟨u, hu, hxu⟩ := hx
      rw [verts_node, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact absurd ha hxu
      · obtain ⟨t, ht, hut⟩ := List.mem_flatMap.1 hu
        have hIH : 0 < form t x x := ih t ht (hkids t ht) x ⟨u, hut, hxu⟩
        have hpos : 0 < form t x x - 2 * x a * x t.root + gamma t * x a ^ 2 := by
          rw [ha]; linarith
        have hs := PosDef.sum_pos_of_mem hbr ht hpos
        have hz : ((w : ℚ) - (c.map gamma).sum) * x a ^ 2 = 0 := by rw [ha]; ring
        linarith
    · have hxa2 : 0 < x a ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha))
      have h1 : 0 < ((w : ℚ) - (c.map gamma).sum) * x a ^ 2 := mul_pos hden hxa2
      linarith

theorem admissible_posDef_proof (C : RTree) (hC : Admissible C) : PosDef C := by
  intro x hx
  obtain ⟨u, hu, hxu⟩ := hx
  have h : (0 : ℚ) < BQ C (fun v => (x v : ℚ)) (fun v => (x v : ℚ)) :=
    PosDef.posDefQ C hC _ ⟨u, hu, by exact_mod_cast hxu⟩
  rw [← form_cast] at h
  exact_mod_cast h

/-! ## D6 -- clearing denominators -/

namespace PosDef

/-- The explicit common denominator of `x` over `verts T`: an iterated `lcm`, no
choice involved. -/
def lcmDen (T : RTree) (x : ℕ → ℚ) : ℕ :=
  (verts T).foldr (fun u n => Nat.lcm (x u).den n) 1

theorem foldr_lcm_pos (x : ℕ → ℚ) :
    ∀ l : List ℕ, 0 < l.foldr (fun u n => Nat.lcm (x u).den n) 1
  | [] => Nat.one_pos
  | hd :: tl => Nat.lcm_pos (x hd).den_pos (foldr_lcm_pos x tl)

theorem lcmDen_pos (T : RTree) (x : ℕ → ℚ) : 0 < lcmDen T x := foldr_lcm_pos x (verts T)

theorem den_dvd_foldr_lcm (x : ℕ → ℚ) :
    ∀ (l : List ℕ) (u : ℕ), u ∈ l → (x u).den ∣ l.foldr (fun v n => Nat.lcm (x v).den n) 1 := by
  intro l
  induction l with
  | nil => intro u hu; cases hu
  | cons hd tl ih =>
    intro u hu
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hu with rfl | hu'
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih u hu') (Nat.dvd_lcm_right _ _)

theorem den_dvd_lcmDen (T : RTree) (x : ℕ → ℚ) (u : ℕ) (hu : u ∈ verts T) :
    (x u).den ∣ lcmDen T x := den_dvd_foldr_lcm x (verts T) u hu

/-- If `q.den ∣ n` then `n * q` is an integer, on the nose. -/
theorem num_cast_of_den_dvd {q : ℚ} {n : ℕ} (h : q.den ∣ n) :
    (((((n : ℚ) * q).num) : ℤ) : ℚ) = (n : ℚ) * q := by
  obtain ⟨k, hk⟩ := h
  have hq : (n : ℚ) * q = ((k * q.num : ℤ) : ℚ) := by
    rw [hk]
    push_cast
    rw [show ((q.den : ℚ) * (k : ℚ)) * q = (k : ℚ) * (q * (q.den : ℚ)) from by ring,
      Rat.mul_den_eq_num]
  rw [hq, Rat.num_intCast]

/-- Scalars pull out of the first argument of `form`. -/
theorem form_smul_left {R : Type} [CommRing R] (T : RTree) (s : R) (x y : ℕ → R) :
    form T (fun u => s * x u) y = s * form T x y := by
  unfold form
  have h1 : ((vwts T).map fun p => (p.2 : R) * (s * x p.1) * y p.1)
      = ((vwts T).map fun p => s * ((p.2 : R) * x p.1 * y p.1)) :=
    List.map_congr_left fun p _ => by ring
  have h2 : ((edges T).map fun e => (s * x e.1) * y e.2 + (s * x e.2) * y e.1)
      = ((edges T).map fun e => s * (x e.1 * y e.2 + x e.2 * y e.1)) :=
    List.map_congr_left fun e _ => by ring
  rw [h1, h2, List.sum_map_mul_left (vwts T) (fun p => (p.2 : R) * x p.1 * y p.1) s,
    List.sum_map_mul_left (edges T) (fun e => x e.1 * y e.2 + x e.2 * y e.1) s]
  ring

end PosDef

/-- **D6.**  Positive definiteness over `ℤ` upgrades to positive definiteness over
`ℚ`, by clearing denominators with the explicit `lcm`. -/
theorem posDefQ_of_posDef {T : RTree} (hpd : PosDef T) (x : ℕ → ℚ)
    (hx : ∃ u ∈ verts T, x u ≠ 0) : 0 < BQ T x x := by
  obtain ⟨u₀, hu₀, hxu₀⟩ := hx
  obtain ⟨N, hNpos, hdvd⟩ : ∃ N : ℕ, 0 < N ∧ ∀ v ∈ verts T, (x v).den ∣ N :=
    ⟨PosDef.lcmDen T x, PosDef.lcmDen_pos T x, fun v hv => PosDef.den_dvd_lcmDen T x v hv⟩
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  set y : ℕ → ℤ := fun v => ((N : ℚ) * x v).num with hydef
  have hcast : ∀ v ∈ verts T, ((y v : ℤ) : ℚ) = (N : ℚ) * x v :=
    fun v hv => PosDef.num_cast_of_den_dvd (hdvd v hv)
  have h1 : ((B T y y : ℤ) : ℚ) = BQ T (fun v => (y v : ℚ)) (fun v => (y v : ℚ)) :=
    form_cast T y y
  have h2 : BQ T (fun v => (y v : ℚ)) (fun v => (y v : ℚ))
      = BQ T (fun v => (N : ℚ) * x v) (fun v => (N : ℚ) * x v) :=
    (form_congr T _ _ _ hcast).trans (form_congr_right T _ _ _ hcast)
  have h3 : BQ T (fun v => (N : ℚ) * x v) (fun v => (N : ℚ) * x v) = (N : ℚ) ^ 2 * BQ T x x := by
    change form T (fun v => (N : ℚ) * x v) (fun v => (N : ℚ) * x v) = _
    rw [PosDef.form_smul_left, form_comm, PosDef.form_smul_left, form_comm]
    ring
  have hyn : NonzeroOn T y := by
    refine ⟨u₀, hu₀, fun h => hxu₀ ?_⟩
    have hc := hcast u₀ hu₀
    rw [h] at hc
    have hz : (N : ℚ) * x u₀ = 0 := by
      rw [← hc]; norm_num
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd h' (ne_of_gt hNQ)
    · exact h'
  have h4 : 0 < B T y y := hpd y hyn
  have h5 : (0 : ℚ) < (N : ℚ) ^ 2 * BQ T x x := by
    rw [← h3, ← h2, ← h1]
    exact_mod_cast h4
  nlinarith [h5, hNQ]

/-! ## Guardrails (modelling sanity checks; `norm_num`, never `decide`) -/

example : Admissible (RTree.node 0 2 [RTree.node 1 2 [RTree.node 2 2 []]]) := by
  norm_num [Admissible]

example : PosDef (RTree.node 0 2 [RTree.node 1 2 [RTree.node 2 2 []]]) :=
  admissible_posDef_proof _ (by norm_num [Admissible])

example : dual (RTree.node 0 2 []) 0 = 1 / 2 := by
  norm_num [dual, dualScaled_node, capacity_node_formula_proof]

end TreeIrred
