import Erdos477.Defs

/-!
# Stage F — the greedy tiling criterion (Lemma 5.1, SKETCH §7)

Pure combinatorics: no number theory, no other stage's results.  For an
**arbitrary** `B : Set ℤ` satisfying the greedy hypothesis `(H)` we build a
tiling complement `A` as the union of a chain of finite `D`-separated sets,
following BLUEPRINT Stage F steps F1–F4 / SKETCH §7.

* F1 `Dsub`, `Dsep`, `translate_inter_nonempty_iff` — the difference set, the
  `D`-separatedness predicate and its translate-disjointness characterisation.
* F2 `step`, `Aseq` — the greedy recursion over the enumeration `enum : ℕ ≃ ℤ`
  coming from `Denumerable ℤ`, with the classical case split on
  `enum j ∈ Aseq j + B`.
* F3 `Aseq_mono`, `Aseq_spec` — monotonicity, then the **combined** induction
  carrying `(I1)` `D`-separatedness and `(I2)` coverage of `enum i` for `i < j`.
* F4 `greedy_tiling_proof` — `A := ⋃ j, ↑(Aseq j)`.

Support declarations live in `namespace Erdos477.Greedy` so that they cannot
shadow a frozen name from `Erdos477/Defs.lean` or `Erdos477/Theorems.lean`.
-/

namespace Erdos477

namespace Greedy

open scoped Classical

variable {B : Set ℤ}

/-! ## F1 — the difference set and `D`-separatedness -/

/-- `D = B − B`, in exactly the existential shape used by the frozen statement of
`greedy_tiling`. -/
def Dsub (B : Set ℤ) : Set ℤ := {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}

/-- `D` is symmetric (SKETCH §9.5(2)); used for the `a − a_j ∉ D` half of `(I1)`. -/
lemma neg_mem_Dsub {d : ℤ} (hd : d ∈ Dsub B) : -d ∈ Dsub B := by
  obtain ⟨x, hx, y, hy, rfl⟩ := hd
  exact ⟨y, hy, x, hx, by ring⟩

/-- `0 ∈ D` as soon as `B` is nonempty (SKETCH §7, remark before the proof). -/
lemma zero_mem_Dsub {b : ℤ} (hb : b ∈ B) : (0 : ℤ) ∈ Dsub B :=
  ⟨b, hb, b, hb, by ring⟩

/-- `A` is `D`-separated: distinct elements differ by something outside `B − B`. -/
def Dsep (B : Set ℤ) (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → a - a' ∉ Dsub B

/-- The translate-disjointness characterisation of `D`-separatedness
(SKETCH §7): `(a + B) ∩ (a' + B) ≠ ∅ ↔ a − a' ∈ B − B`. -/
lemma translate_inter_nonempty_iff (a a' : ℤ) :
    (((fun x => a + x) '' B) ∩ ((fun x => a' + x) '' B)).Nonempty ↔ a - a' ∈ Dsub B := by
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, ⟨b', hb', h⟩⟩
    replace h : a' + b' = a + b := h
    exact ⟨b', hb', b, hb, by omega⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨a + y, ⟨y, hy, rfl⟩, ⟨x, hx, show a' + x = a + y by omega⟩⟩

/-- `n` is covered by `A`, i.e. `n ∈ A + B`. -/
def Covered (B : Set ℤ) (A : Finset ℤ) (n : ℤ) : Prop := ∃ a ∈ A, n - a ∈ B

/-- The greedy hypothesis `(H)` of SKETCH §7 for an arbitrary `B ⊆ ℤ`. -/
def GreedyH (B : Set ℤ) : Prop :=
  ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) → ∃ b ∈ B, ∀ c ∈ C, c - b ∉ Dsub B

/-- `(H)` at `C = ∅` shows `B ≠ ∅` (SKETCH §7, first remark). -/
lemma nonempty_of_greedyH (H : GreedyH B) : ∃ b, b ∈ B := by
  obtain ⟨b, hb, -⟩ := H ∅ (fun c hc => absurd hc (by simp))
  exact ⟨b, hb⟩

/-! ## F2 — the greedy step and the chain `Aseq` -/

/-- In Case 2 of the recursion every element of `C_j = {n − a : a ∈ A}` avoids `B`. -/
lemma image_notMem {n : ℤ} {A : Finset ℤ} (h : ¬ ∃ a ∈ A, n - a ∈ B) :
    ∀ c ∈ A.image (fun a => n - a), c ∉ B := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
  exact fun hb => h ⟨a, ha, hb⟩

/-- One greedy step at the integer `n`: keep `A` if `n` is already covered,
otherwise adjoin `n − b_j` for a `b_j` supplied by `(H)`. -/
noncomputable def step (H : GreedyH B) (n : ℤ) (A : Finset ℤ) : Finset ℤ :=
  if h : ∃ a ∈ A, n - a ∈ B then A
  else insert (n - (H (A.image fun a => n - a) (image_notMem h)).choose) A

lemma step_of_pos (H : GreedyH B) {n : ℤ} {A : Finset ℤ} (h : ∃ a ∈ A, n - a ∈ B) :
    step H n A = A := dif_pos h

lemma step_of_neg (H : GreedyH B) {n : ℤ} {A : Finset ℤ} (h : ¬ ∃ a ∈ A, n - a ∈ B) :
    step H n A =
      insert (n - (H (A.image fun a => n - a) (image_notMem h)).choose) A := dif_neg h

lemma subset_step (H : GreedyH B) (n : ℤ) (A : Finset ℤ) : A ⊆ step H n A := by
  by_cases h : ∃ a ∈ A, n - a ∈ B
  · exact le_of_eq (step_of_pos H h).symm
  · rw [step_of_neg H h]
    exact Finset.subset_insert _ _

/-- SKETCH §9.5(9): in Case 2 the new element `a_j = n − b_j` is genuinely new,
because otherwise `a_j − a_j = 0 ∈ D` would violate the choice of `b_j`. -/
lemma step_newElt_notMem (H : GreedyH B) {n : ℤ} {A : Finset ℤ}
    (h : ¬ ∃ a ∈ A, n - a ∈ B) :
    n - (H (A.image fun a => n - a) (image_notMem h)).choose ∉ A := by
  have hspec := (H (A.image fun a => n - a) (image_notMem h)).choose_spec
  set b := (H (A.image fun a => n - a) (image_notMem h)).choose
  intro hmem
  obtain ⟨b₀, hb₀⟩ := nonempty_of_greedyH H
  have hmemC : n - (n - b) ∈ A.image (fun a => n - a) := Finset.mem_image_of_mem _ hmem
  refine hspec.2 _ hmemC ?_
  have hzero : n - (n - b) - b = 0 := by ring
  rw [hzero]
  exact zero_mem_Dsub hb₀

/-- After one step at `n`, the integer `n` is covered — Case 1 by assumption,
Case 2 by `n = a_j + b_j`. -/
lemma covered_step (H : GreedyH B) (n : ℤ) (A : Finset ℤ) : Covered B (step H n A) n := by
  by_cases h : ∃ a ∈ A, n - a ∈ B
  · rw [step_of_pos H h]; exact h
  · rw [step_of_neg H h]
    refine ⟨n - _, Finset.mem_insert_self _ _, ?_⟩
    have hb := (H (A.image fun a => n - a) (image_notMem h)).choose_spec.1
    simpa using hb

/-- `(I1)` is preserved by a greedy step. -/
lemma Dsep_step (H : GreedyH B) (n : ℤ) {A : Finset ℤ} (hA : Dsep B A) :
    Dsep B (step H n A) := by
  by_cases h : ∃ a ∈ A, n - a ∈ B
  · rwa [step_of_pos H h]
  · rw [step_of_neg H h]
    have hspec := (H (A.image fun a => n - a) (image_notMem h)).choose_spec
    set b := (H (A.image fun a => n - a) (image_notMem h)).choose
    have key : ∀ a ∈ A, n - b - a ∉ Dsub B := by
      intro a ha hc
      have hmemC : n - a ∈ A.image (fun a => n - a) := Finset.mem_image_of_mem _ ha
      exact hspec.2 _ hmemC (by rwa [sub_right_comm] at hc)
    intro x hx y hy hxy
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rcases Finset.mem_insert.1 hy with rfl | hy
      · exact absurd rfl hxy
      · exact key y hy
    · rcases Finset.mem_insert.1 hy with rfl | hy
      · exact fun hc => key x hx (by simpa using neg_mem_Dsub hc)
      · exact hA x hx y hy hxy

/-- The enumeration of `ℤ` used by the greedy construction. -/
def enum : ℕ ≃ ℤ := (Denumerable.eqv ℤ).symm

/-- The greedy chain `A₀ ⊆ A₁ ⊆ ⋯` of SKETCH §7. -/
noncomputable def Aseq (H : GreedyH B) : ℕ → Finset ℤ
  | 0 => ∅
  | (j + 1) => step H (enum j) (Aseq H j)

/-! ## F3 — monotonicity and the combined `(I1) ∧ (I2)` induction -/

lemma Aseq_subset_succ (H : GreedyH B) (j : ℕ) : Aseq H j ⊆ Aseq H (j + 1) :=
  subset_step H (enum j) (Aseq H j)

lemma Aseq_mono (H : GreedyH B) {i j : ℕ} (hij : i ≤ j) : Aseq H i ⊆ Aseq H j := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (Aseq_subset_succ H _)

/-- The combined induction: `(I1)` `Aseq H j` is `D`-separated, and `(I2)` it
covers `enum i` for every `i < j`. -/
lemma Aseq_spec (H : GreedyH B) (j : ℕ) :
    Dsep B (Aseq H j) ∧ ∀ i < j, Covered B (Aseq H j) (enum i) := by
  induction j with
  | zero =>
      exact ⟨fun a ha => absurd ha (Finset.notMem_empty a),
        fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ j ih =>
      refine ⟨Dsep_step H (enum j) ih.1, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · obtain ⟨a, ha, hb⟩ := ih.2 i hlt
        exact ⟨a, Aseq_subset_succ H j ha, hb⟩
      · exact covered_step H (enum i) (Aseq H i)

end Greedy

/-! ## F4 — the frozen statement -/

open Greedy in
/-- **Stage F / L4.1 = paper's Lemma 5.1** — proof of the frozen `greedy_tiling`. -/
theorem greedy_tiling_proof (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
      ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := by
  have H' : GreedyH B := H
  refine ⟨⋃ j : ℕ, ↑(Aseq H' j), ?_⟩
  intro n
  obtain ⟨j, hj⟩ : ∃ j : ℕ, enum j = n := ⟨enum.symm n, by simp⟩
  obtain ⟨a, ha, hb⟩ := (Aseq_spec H' (j + 1)).2 j (Nat.lt_succ_self j)
  rw [hj] at hb
  refine ⟨(a, n - a), ⟨?_, hb, by ring⟩, ?_⟩
  · exact Set.mem_iUnion.2 ⟨j + 1, Finset.mem_coe.mpr ha⟩
  · rintro p ⟨hp1, hp2, hp3⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hp1
    have hkm : p.1 ∈ Aseq H' (max k (j + 1)) :=
      Aseq_mono H' (le_max_left _ _) (Finset.mem_coe.mp hk)
    have ham : a ∈ Aseq H' (max k (j + 1)) := Aseq_mono H' (le_max_right _ _) ha
    have hfst : p.1 = a := by
      by_contra hne
      exact (Aseq_spec H' (max k (j + 1))).1 p.1 hkm a ham hne
        ⟨n - a, hb, p.2, hp2, by omega⟩
    have hsnd : p.2 = n - a := by omega
    exact Prod.ext hfst hsnd

/-! ## Guardrail (BLUEPRINT Stage F cheat-watch)

The frozen conclusion at `B := Set.univ` must be provable directly in a couple of
lines, with `A = {0}`; this pins down that the `∃!` is over the **pair** and is
not accidentally vacuous. -/

example :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ,
      ab.1 ∈ A ∧ ab.2 ∈ (Set.univ : Set ℤ) ∧ ab.1 + ab.2 = n := by
  refine ⟨{0}, fun n => ⟨(0, n), ⟨rfl, trivial, by ring⟩, ?_⟩⟩
  rintro p ⟨hp1, -, hp3⟩
  have h0 : p.1 = 0 := hp1
  exact Prod.ext h0 (by omega)

/-- The general theorem does apply at `B := Set.univ` (the hypothesis `(H)` is
then only satisfiable through `C = ∅`, which is why `(H)` must not be restricted
to nonempty `C`). -/
example : ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ,
    ab.1 ∈ A ∧ ab.2 ∈ (Set.univ : Set ℤ) ∧ ab.1 + ab.2 = n := by
  refine greedy_tiling_proof Set.univ ?_
  intro C hC
  refine ⟨0, trivial, fun c hc => absurd (hC c hc) (by simp)⟩

end Erdos477
