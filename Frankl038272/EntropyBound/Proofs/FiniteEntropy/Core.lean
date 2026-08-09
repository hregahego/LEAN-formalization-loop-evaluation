/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems

/-!
# Stage I core — the finitary entropy toolbox (`SKETCH.md` Step 9, BLUEPRINT items I1, I4, I5, I7)

This file develops the elementary theory of `entropyW` / `law` / `Hrv` as frozen in
`EntropyBound/Defs.lean` — strictly finitary, no `MeasureTheory`, no `PMF`, no
`ProbabilityTheory`.

Contents:

* support lemmas `law_nonneg`, `law_sum_eq_one`, `negMulLog_nonneg`, `entropyW_nonneg`;
* the Gibbs bound `entropyW_le_log_card` (BLUEPRINT I1);
* `uniform_entropy_eq_log_card_proof` (#51, I5);
* `entropy_le_log_card_proof` (#50, I4);
* `freq_eq_one_sub_ES_proof` (#53, I7).
-/

namespace EntropyBound

open Finset

noncomputable section

namespace FiniteEntropy

/-! ### Elementary facts about `law` and `entropyW` -/

/-- Each term of `entropyW` is nonnegative on `[0,1]`. -/
lemma negMulLog_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ -x * Real.log x := by
  have hlog : Real.log x ≤ 0 := Real.log_nonpos h0 h1
  nlinarith

/-- The pushforward law of a nonnegative weight vector is nonnegative. -/
lemma law_nonneg {ι β : Type*} [Fintype ι] [DecidableEq β] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (Z : ι → β) (b : β) : 0 ≤ law w Z b := by
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases h : Z i = b <;> simp [h, hw i]

/-- The pushforward law of a probability weight vector is a probability weight vector. -/
lemma law_sum_eq_one {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β] {w : ι → ℝ}
    (hw1 : ∑ i, w i = 1) (Z : ι → β) : ∑ b, law w Z b = 1 := by
  simp only [law]
  rw [Finset.sum_comm]
  simpa using hw1

/-- Entropy of a finite weight vector with values in `[0,1]` is nonnegative. -/
lemma entropyW_nonneg {β : Type*} [Fintype β] {p : β → ℝ} (hp : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) : 0 ≤ entropyW p :=
  Finset.sum_nonneg fun b _ => negMulLog_nonneg (hp b) (hp1 b)

/-- **Gibbs' inequality.** A probability weight vector supported on a finite set `S` has
entropy at most `log |S|`.  Proved from `log x ≤ x - 1` only. -/
lemma entropyW_le_log_card {β : Type*} [Fintype β] (p : β → ℝ) (hp : ∀ b, 0 ≤ p b)
    (hp1 : ∑ b, p b = 1) (S : Finset β) (hsupp : ∀ b, b ∉ S → p b = 0) :
    entropyW p ≤ Real.log (S.card : ℝ) := by
  have hsum : ∑ b ∈ S, p b = 1 :=
    (Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => hsupp b hb)).trans hp1
  have hScard : 0 < S.card := by
    rcases Finset.eq_empty_or_nonempty S with rfl | h
    · simp at hsum
    · exact Finset.card_pos.mpr h
  have hNpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hScard
  have hent : entropyW p = ∑ b ∈ S, -(p b) * Real.log (p b) := by
    simp only [entropyW]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro b _ hb
    simp [hsupp b hb]
  rw [hent]
  have key : ∀ b ∈ S,
      -(p b) * Real.log (p b) ≤ p b * Real.log (S.card : ℝ) + (1 / (S.card : ℝ) - p b) := by
    intro b _
    rcases eq_or_lt_of_le (hp b) with h | h
    · rw [← h]
      simp
    · have hlog := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((S.card : ℝ) * p b)⁻¹ by positivity)
      rw [Real.log_inv, Real.log_mul (ne_of_gt hNpos) (ne_of_gt h)] at hlog
      have h3 := mul_le_mul_of_nonneg_left hlog h.le
      have h4 : p b * (((S.card : ℝ) * p b)⁻¹ - 1) = 1 / (S.card : ℝ) - p b := by
        field_simp
      rw [h4] at h3
      linarith
  calc ∑ b ∈ S, -(p b) * Real.log (p b)
      ≤ ∑ b ∈ S, (p b * Real.log (S.card : ℝ) + (1 / (S.card : ℝ) - p b)) :=
        Finset.sum_le_sum key
    _ = Real.log (S.card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_sub_distrib,
          hsum, Finset.sum_const, nsmul_eq_mul]
        field_simp
        ring

/-! ### The uniform weight vector on a finite family -/

lemma unifW_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) : 0 ≤ unifW G x := by
  unfold unifW
  split
  · positivity
  · exact le_rfl

lemma unifW_sum_eq_one {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∑ x, unifW G x = 1 := by
  have hcard : (0 : ℝ) < (G.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hG
  simp only [unifW]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The identity map has the uniform vector itself as its law. -/
lemma law_unifW_id {n : ℕ} (G : Finset (Fin n → Bool)) :
    law (unifW G) id = unifW G := by
  funext b
  simp only [law, id_eq]
  exact Fintype.sum_ite_eq' b (unifW G)

/-! ### The prefix fibers of a family, and `pcond` as a function of the prefix -/

/-- The set of members of `G` whose length-`i` prefix is the pattern `v`. -/
def prefFiber {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    Finset (Fin n → Bool) := G.filter (fun x => pref i.val x = v)

/-- `pcond` as a function of the prefix pattern rather than of a member of the cube. -/
def pcondV {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) : ℝ :=
  if (prefFiber G i v).card = 0 then 0
  else (((prefFiber G i v).filter (fun x => x i = false)).card : ℝ)
        / ((prefFiber G i v).card : ℝ)

lemma pcond_eq_pcondV {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (x : Fin n → Bool) :
    pcond G i x = pcondV G i (pref i.val x) := rfl

/-- On a prefix fiber, `|A| * pcondV = |B|`. -/
lemma card_mul_pcondV {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    ((prefFiber G i v).card : ℝ) * pcondV G i v =
      (((prefFiber G i v).filter (fun x => x i = false)).card : ℝ) := by
  unfold pcondV
  split
  · rename_i h
    have hzero : (prefFiber G i v).filter (fun x => x i = false) = ∅ := by
      rw [Finset.card_eq_zero] at h
      rw [h]
      simp
    rw [hzero, h]
    simp
  · rename_i h
    have : ((prefFiber G i v).card : ℝ) ≠ 0 := by exact_mod_cast h
    field_simp

end FiniteEntropy

/-! ### Frozen theorem #51 — the entropy of the uniform member -/

theorem uniform_entropy_eq_log_card_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    Hrv (unifW G) id = Real.log (G.card : ℝ) := by
  have hcard : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hG
  rw [Hrv, FiniteEntropy.law_unifW_id]
  have hterm : ∀ x : Fin n → Bool, -(unifW G x) * Real.log (unifW G x)
      = if x ∈ G then (1 / (G.card : ℝ)) * Real.log (G.card : ℝ) else 0 := by
    intro x
    by_cases hx : x ∈ G
    · simp only [unifW, if_pos hx]
      rw [one_div, Real.log_inv]
      ring
    · simp [unifW, hx]
  simp only [entropyW, hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ### Frozen theorem #50 — the maximum-entropy (Gibbs) bound -/

theorem entropy_le_log_card_proof {Ω : Type*} [Fintype Ω] {n : ℕ} (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (Z : Ω → (Fin n → Bool)) (G : Finset (Fin n → Bool))
    (hZ : ∀ ω, w ω ≠ 0 → Z ω ∈ G) :
    Hrv w Z ≤ Real.log (G.card : ℝ) := by
  refine FiniteEntropy.entropyW_le_log_card _ (FiniteEntropy.law_nonneg hw Z)
    (FiniteEntropy.law_sum_eq_one hw1 Z) G ?_
  intro b hb
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases h : Z ω = b
  · rw [if_pos h]
    by_contra hne
    exact hb (h ▸ hZ ω hne)
  · rw [if_neg h]

/-! ### Frozen theorem #53 — the frequency identity -/

theorem freq_eq_one_sub_ES_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∀ i : Fin n,
      ((G.filter (fun x => x i = true)).card : ℝ) / (G.card : ℝ) = 1 - ESfun G i := by
  intro i
  have hcard : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hG
  -- Step 1: the expectation of `pcond` is the fraction of members with `i`-th bit `false`.
  have hE : ESfun G i
      = ((G.filter (fun x => x i = false)).card : ℝ) / (G.card : ℝ) := by
    have h1 : ESfun G i = (1 / (G.card : ℝ)) * ∑ x ∈ G, pcond G i x := by
      simp only [ESfun, unifW, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    -- fiberwise regrouping of `∑ x ∈ G, pcond G i x`
    have h2 : ∑ x ∈ G, pcond G i x
        = ∑ v : Fin n → Bool,
            (((FiniteEntropy.prefFiber G i v).filter (fun x => x i = false)).card : ℝ) := by
      rw [← Finset.sum_fiberwise G (fun x => pref i.val x) (fun x => pcond G i x)]
      refine Finset.sum_congr rfl fun v _ => ?_
      have : ∀ x ∈ G.filter (fun x => pref i.val x = v),
          pcond G i x = FiniteEntropy.pcondV G i v := by
        intro x hx
        rw [FiniteEntropy.pcond_eq_pcondV, (Finset.mem_filter.1 hx).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      exact FiniteEntropy.card_mul_pcondV G i v
    have h3 : ((G.filter (fun x => x i = false)).card : ℝ)
        = ∑ v : Fin n → Bool,
            (((FiniteEntropy.prefFiber G i v).filter (fun x => x i = false)).card : ℝ) :=
      calc ((G.filter (fun x => x i = false)).card : ℝ)
          = ∑ x ∈ G, (if x i = false then (1 : ℝ) else 0) := by simp
        _ = ∑ v : Fin n → Bool, ∑ x ∈ G.filter (fun x => pref i.val x = v),
              (if x i = false then (1 : ℝ) else 0) :=
            (Finset.sum_fiberwise G (fun x => pref i.val x) _).symm
        _ = ∑ v : Fin n → Bool,
              (((FiniteEntropy.prefFiber G i v).filter (fun x => x i = false)).card : ℝ) :=
            Finset.sum_congr rfl fun v _ => by simp [FiniteEntropy.prefFiber]
    rw [h1, h2, ← h3]
    ring
  rw [hE]
  have hsplit : (G.filter (fun x => x i = true)).card + (G.filter (fun x => x i = false)).card
      = G.card := by
    have := Finset.card_filter_add_card_filter_not
      (s := G) (p := fun x => x i = true)
    simpa using this
  have hsplit' : ((G.filter (fun x => x i = true)).card : ℝ)
      + ((G.filter (fun x => x i = false)).card : ℝ) = (G.card : ℝ) := by
    exact_mod_cast hsplit
  field_simp
  linarith

end

namespace Solution

theorem uniform_entropy_eq_log_card {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    Hrv (unifW G) id = Real.log (G.card : ℝ) :=
  EntropyBound.uniform_entropy_eq_log_card_proof G hG

theorem entropy_le_log_card {Ω : Type*} [Fintype Ω] {n : ℕ} (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (Z : Ω → (Fin n → Bool)) (G : Finset (Fin n → Bool))
    (hZ : ∀ ω, w ω ≠ 0 → Z ω ∈ G) :
    Hrv w Z ≤ Real.log (G.card : ℝ) :=
  EntropyBound.entropy_le_log_card_proof w hw hw1 Z G hZ

theorem freq_eq_one_sub_ES {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∀ i : Fin n,
      ((G.filter (fun x => x i = true)).card : ℝ) / (G.card : ℝ) = 1 - ESfun G i :=
  EntropyBound.freq_eq_one_sub_ES_proof G hG

end Solution

example : @EntropyBound.uniform_entropy_eq_log_card
    = @EntropyBound.Solution.uniform_entropy_eq_log_card := rfl

example : @EntropyBound.entropy_le_log_card = @EntropyBound.Solution.entropy_le_log_card := rfl

example : @EntropyBound.freq_eq_one_sub_ES = @EntropyBound.Solution.freq_eq_one_sub_ES := rfl

/-! ### Guardrails (BLUEPRINT Stage I cheat-watch) -/

example : Hrv (unifW ({fun _ => false} : Finset (Fin 1 → Bool))) id = 0 := by
  rw [uniform_entropy_eq_log_card_proof _ ⟨fun _ => false, by simp⟩]
  simp

example : Hrv (unifW (Finset.univ : Finset (Fin 1 → Bool))) id = Real.log 2 := by
  rw [uniform_entropy_eq_log_card_proof _ Finset.univ_nonempty]
  norm_num

end EntropyBound
