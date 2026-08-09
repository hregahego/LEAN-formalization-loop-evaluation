/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Assembly.Basic

/-!
# Stage L item L2 — the cube → `Finset α` transfer (`BLUEPRINT.md` L2, `SKETCH.md` Step 12)

`frankl_cube` (#60) lives on the Boolean cube `Fin n → Bool`; the headline `frankl_038272`
(#61) is about an arbitrary family `F : Finset (Finset α)` over an arbitrary
`[DecidableEq α]` type.  This file supplies the transfer, in hypothesis form:

`Assembly.frankl_038272_of_cube` takes the frozen statement of #60 **verbatim** as a
hypothesis and produces the frozen statement of #61 **verbatim**.

The construction is BLUEPRINT L2: enumerate the ground set `U := F.sup id` by
`U.equivFin.symm : Fin U.card ≃ ↥U` and push `F` forward along the indicator map
`A ↦ fun i => decide (ε i ∈ A)`.  The support lemmas are `Assembly.tr_*`:

* `tr_subset_ground`   — every member of `F` is contained in the ground set;
* `tr_injOn`           — the indicator map is **injective on `F`** (this is what makes
                          `G.card = F.card`, so the transferred bound is about `F` itself);
* `tr_card`            — `(trCube F).card = F.card`;
* `tr_unionClosedCube` — `UnionClosed F → UnionClosedCube (trCube F)`;
* `tr_filter_card`     — the coordinate-`i` fibre cards agree;
* `tr_nonempty`, `tr_exists_ne_false` — the two nondegeneracy hypotheses transfer.

Note on `decide`: the *tactic* `decide` is banned in this project; `Decidable.decide` used
as the ordinary `Prop → Bool` indicator **function** is not a tactic and is what is used
here (BLUEPRINT Stage L cheat-watch explicitly allows it).
-/

namespace EntropyBound.Assembly

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The ground set of a family: the union of all its members. -/
def trGround (F : Finset (Finset α)) : Finset α := F.sup id

/-- The enumeration of the ground set used by the transfer. -/
def trEnum (F : Finset (Finset α)) : Fin (trGround F).card ≃ ↥(trGround F) :=
  (trGround F).equivFin.symm

/-- The indicator vector of `A ⊆ α` relative to the enumerated ground set of `F`. -/
def trVec (F : Finset (Finset α)) (A : Finset α) : Fin (trGround F).card → Bool :=
  fun i => decide (((trEnum F i : ↥(trGround F)) : α) ∈ A)

/-- The family `F`, pushed forward onto the Boolean cube of its ground set. -/
def trCube (F : Finset (Finset α)) : Finset (Fin (trGround F).card → Bool) :=
  F.image (trVec F)

section Support

variable {F : Finset (Finset α)}

/-- Every member of `F` is a subset of the ground set `F.sup id`. -/
theorem tr_subset_ground {A : Finset α} (hA : A ∈ F) : A ⊆ trGround F :=
  Finset.le_sup (f := id) hA

@[simp] theorem tr_apply (A : Finset α) (i : Fin (trGround F).card) :
    trVec F A i = true ↔ ((trEnum F i : ↥(trGround F)) : α) ∈ A := by
  simp [trVec]

/-- The indicator map is injective on `F`: two members of `F` are subsets of the ground
set, so agreeing on every ground-set point forces equality. -/
theorem tr_injOn : Set.InjOn (trVec F) (F : Set (Finset α)) := by
  intro A hA B hB hAB
  have key : ∀ a : α, a ∈ trGround F → (a ∈ A ↔ a ∈ B) := by
    intro a ha
    have h := congrFun hAB (trEnum F |>.symm ⟨a, ha⟩)
    have hval : ((trEnum F ((trEnum F).symm ⟨a, ha⟩) : ↥(trGround F)) : α) = a := by
      rw [Equiv.apply_symm_apply]
    simp only [trVec, hval, decide_eq_decide] at h
    exact h
  ext a
  constructor
  · intro haA
    exact (key a (tr_subset_ground hA haA)).mp haA
  · intro haB
    exact (key a (tr_subset_ground hB haB)).mpr haB

/-- The transfer preserves cardinality. -/
theorem tr_card : (trCube F).card = F.card :=
  Finset.card_image_of_injOn tr_injOn

/-- `orVec` of two indicator vectors is the indicator vector of the union. -/
theorem tr_orVec (A B : Finset α) : orVec (trVec F A) (trVec F B) = trVec F (A ∪ B) := by
  funext i
  by_cases h1 : ((trEnum F i : ↥(trGround F)) : α) ∈ A <;>
    by_cases h2 : ((trEnum F i : ↥(trGround F)) : α) ∈ B <;>
      simp [orVec, trVec, Finset.mem_union, h1, h2]

/-- Union-closedness transfers to the cube. -/
theorem tr_unionClosedCube (hUC : UnionClosed F) : UnionClosedCube (trCube F) := by
  intro x hx y hy
  simp only [trCube, Finset.mem_image] at hx hy ⊢
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨B, hB, rfl⟩ := hy
  exact ⟨A ∪ B, hUC A hA B hB, (tr_orVec A B).symm⟩

/-- The coordinate-`i` fibre of the transferred family has the same cardinality as the
family of members of `F` containing the `i`-th ground-set point. -/
theorem tr_filter_card (i : Fin (trGround F).card) :
    ((trCube F).filter (fun x => x i = true)).card
      = (F.filter (fun A => ((trEnum F i : ↥(trGround F)) : α) ∈ A)).card := by
  have himg : (trCube F).filter (fun x => x i = true)
      = (F.filter (fun A => ((trEnum F i : ↥(trGround F)) : α) ∈ A)).image (trVec F) := by
    ext x
    simp only [trCube, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨A, hA, rfl⟩, hx⟩
      exact ⟨A, ⟨hA, (tr_apply A i).mp hx⟩, rfl⟩
    · rintro ⟨A, ⟨hAF, hAi⟩, rfl⟩
      exact ⟨⟨A, hAF, rfl⟩, (tr_apply A i).mpr hAi⟩
  rw [himg, Finset.card_image_of_injOn]
  exact tr_injOn.mono (by intro A hA; exact (Finset.mem_filter.1 hA).1)

/-- Nonemptiness transfers. -/
theorem tr_nonempty (hne : F.Nonempty) : (trCube F).Nonempty :=
  hne.image _

omit [DecidableEq α] in
/-- Some member of a nonempty family other than `{∅}` is nonempty. -/
theorem tr_exists_ne_empty (hne : F.Nonempty) (hnt : F ≠ {∅}) : ∃ A ∈ F, A ≠ ∅ := by
  by_contra h
  apply hnt
  have hall : ∀ A ∈ F, A = ∅ := by
    intro A hA
    by_contra hA0
    exact h ⟨A, hA, hA0⟩
  obtain ⟨A₀, hA₀⟩ := hne
  have hempty : (∅ : Finset α) ∈ F := hall A₀ hA₀ ▸ hA₀
  ext A
  simp only [Finset.mem_singleton]
  exact ⟨fun hA => hall A hA, fun hA => hA ▸ hempty⟩

/-- The nontriviality hypothesis transfers. -/
theorem tr_exists_ne_false (hne : F.Nonempty) (hnt : F ≠ {∅}) :
    ∃ x ∈ trCube F, x ≠ fun _ => false := by
  obtain ⟨A, hAF, hA⟩ := tr_exists_ne_empty hne hnt
  obtain ⟨a, haA⟩ := Finset.nonempty_iff_ne_empty.2 hA
  have ha : a ∈ trGround F := tr_subset_ground hAF haA
  refine ⟨trVec F A, Finset.mem_image_of_mem _ hAF, ?_⟩
  intro hcon
  have h := congrFun hcon ((trEnum F).symm ⟨a, ha⟩)
  have hval : ((trEnum F ((trEnum F).symm ⟨a, ha⟩) : ↥(trGround F)) : α) = a := by
    rw [Equiv.apply_symm_apply]
  simp only [trVec, hval, decide_eq_false_iff_not] at h
  exact h haA

end Support

/-- **Stage L item L2.**  The frozen cube statement `frankl_cube` (#60) implies the frozen
headline `frankl_038272` (#61), for an arbitrary `[DecidableEq α]` type `α` and an
arbitrary family `F`, with exactly the frozen hypotheses. -/
theorem frankl_038272_of_cube (F : Finset (Finset α))
    (hcube : ∀ {n : ℕ} (G : Finset (Fin n → Bool)), UnionClosedCube G → G.Nonempty →
      (∃ x ∈ G, x ≠ fun _ => false) →
      ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card)
    (hUC : UnionClosed F) (hne : F.Nonempty) (hnt : F ≠ {∅}) :
    ∃ x : α, 1196 * F.card ≤ 3125 * (F.filter (fun A => x ∈ A)).card := by
  obtain ⟨i, hi⟩ := hcube (trCube F) (tr_unionClosedCube hUC) (tr_nonempty hne)
    (tr_exists_ne_false hne hnt)
  refine ⟨((trEnum F i : ↥(trGround F)) : α), ?_⟩
  rwa [tr_card, tr_filter_card i] at hi

/-! ### Guardrail — the transfer applies end-to-end to a concrete union-closed family -/

/-- End-to-end shape check (BLUEPRINT Stage L cheat-watch): feeding the frozen cube
statement to `frankl_038272_of_cube` at the concrete union-closed family
`{{0}, {0,1}} : Finset (Finset ℕ)` produces the headline conclusion for that family. -/
example
    (h : ∀ {n : ℕ} (G : Finset (Fin n → Bool)), UnionClosedCube G → G.Nonempty →
      (∃ x ∈ G, x ≠ fun _ => false) →
      ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card) :
    ∃ x : ℕ, 1196 * ({{0}, {0, 1}} : Finset (Finset ℕ)).card
      ≤ 3125 * (({{0}, {0, 1}} : Finset (Finset ℕ)).filter (fun A => x ∈ A)).card := by
  refine frankl_038272_of_cube ({{0}, {0, 1}} : Finset (Finset ℕ)) h ?_ ?_ ?_
  · intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB ⊢
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact Or.inl (Finset.union_self _)
    · exact Or.inr (by ext a; simp)
    · exact Or.inr (by ext a; simp; tauto)
    · exact Or.inr (Finset.union_self _)
  · exact ⟨{0}, by simp⟩
  · intro hcon
    have hmem : ({0} : Finset ℕ) ∈ ({∅} : Finset (Finset ℕ)) := by
      rw [← hcon]; simp
    simp at hmem

end

end EntropyBound.Assembly

/-! ### Frozen theorem #61 — the headline

`EntropyBound.frankl_cube_proof` (#60) is ✅ in `EntropyBound/Proofs/Assembly/Cube.lean`, so
the hypothesis of `Assembly.frankl_038272_of_cube` is discharged outright. -/

namespace EntropyBound

theorem frankl_038272_proof {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hUC : UnionClosed F) (hne : F.Nonempty) (hnt : F ≠ {∅}) :
    ∃ x : α, 1196 * F.card ≤ 3125 * (F.filter (fun A => x ∈ A)).card :=
  Assembly.frankl_038272_of_cube F EntropyBound.frankl_cube_proof hUC hne hnt

namespace Solution

theorem frankl_038272 {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hUC : UnionClosed F) (hne : F.Nonempty) (hnt : F ≠ {∅}) :
    ∃ x : α, 1196 * F.card ≤ 3125 * (F.filter (fun A => x ∈ A)).card :=
  EntropyBound.frankl_038272_proof F hUC hne hnt

end Solution

example : @EntropyBound.frankl_038272 = @EntropyBound.Solution.frankl_038272 := rfl

end EntropyBound
