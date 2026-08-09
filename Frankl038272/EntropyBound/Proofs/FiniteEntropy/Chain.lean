/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.FiniteEntropy.Core

/-!
# Stage I — chain rule and "conditioning reduces entropy" (BLUEPRINT items I2, I3, I6)

Everything here is finitary: `Hrv`/`condHrv` are the frozen definitions of
`EntropyBound/Defs.lean`, and `condHrv w Z W = Hrv w (Z, W) - Hrv w W` *by definition*, so
the pair chain rule is definitional and the whole content of #48 is the bookkeeping identity
`Hrv w (X i, pref i X) = Hrv w (pref (i+1) X)`.

Contents:

* the log-sum inequality `log_sum_ineq` and the superadditivity `psi_superadd` of the
  homogeneous entropy functional — the analytic core of #49;
* `condHrv_le_of_comp_proof` (#49) for an **arbitrary** `f`;
* `Hrv_map_eq`, the `pref` bookkeeping lemmas, and `entropy_chain_rule_proof` (#48);
* `condHrv_eq_HiFun` and `prefix_entropy_decomposition_proof` (#52).
-/

namespace EntropyBound

open Finset

namespace FiniteEntropy

/-! ### The log-sum inequality -/

/-- **Log-sum inequality** (in the form needed below): if `0 ≤ a c ≤ b c` on a finite index
set, then `∑ a c * log (b c / a c) ≤ (∑ a c) * log ((∑ b c)/(∑ a c))`.  Proved from
`Real.log_le_sub_one_of_pos` alone. -/
lemma log_sum_ineq {κ : Type*} (K : Finset κ) (a b : κ → ℝ)
    (ha : ∀ c ∈ K, 0 ≤ a c) (hab : ∀ c ∈ K, a c ≤ b c) :
    ∑ c ∈ K, a c * (Real.log (b c) - Real.log (a c))
      ≤ (∑ c ∈ K, a c) * (Real.log (∑ c ∈ K, b c) - Real.log (∑ c ∈ K, a c)) := by
  set A := ∑ c ∈ K, a c with hAdef
  set B := ∑ c ∈ K, b c with hBdef
  have hA : 0 ≤ A := Finset.sum_nonneg ha
  have hAB : A ≤ B := Finset.sum_le_sum hab
  rcases eq_or_lt_of_le hA with hzero | hApos
  · have hall : ∀ c ∈ K, a c = 0 := by
      intro c hc
      exact (Finset.sum_eq_zero_iff_of_nonneg ha).1 hzero.symm c hc
    have h1 : ∑ c ∈ K, a c * (Real.log (b c) - Real.log (a c)) = 0 :=
      Finset.sum_eq_zero fun c hc => by rw [hall c hc]; ring
    have h2 : A = 0 := hzero.symm
    simp [h1, h2]
  · have hBpos : 0 < B := lt_of_lt_of_le hApos hAB
    have key : ∀ c ∈ K, a c * (Real.log (b c) - Real.log (a c))
        ≤ (A / B) * b c - a c + a c * (Real.log B - Real.log A) := by
      intro c hc
      rcases eq_or_lt_of_le (ha c hc) with h | h
      · have hb : 0 ≤ b c := le_trans (ha c hc) (hab c hc)
        rw [← h]
        have hq : 0 ≤ A / B := by positivity
        have : 0 ≤ A / B * b c := mul_nonneg hq hb
        simpa using this
      · have hbc : 0 < b c := lt_of_lt_of_le h (hab c hc)
        have hlog := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < b c * A / (a c * B) by positivity)
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (ne_of_gt hbc) (ne_of_gt hApos),
          Real.log_mul (ne_of_gt h) (ne_of_gt hBpos)] at hlog
        have h3 := mul_le_mul_of_nonneg_left hlog h.le
        have h4 : a c * (b c * A / (a c * B) - 1) = A / B * b c - a c := by
          field_simp
        rw [h4] at h3
        linarith
    calc ∑ c ∈ K, a c * (Real.log (b c) - Real.log (a c))
        ≤ ∑ c ∈ K, ((A / B) * b c - a c + a c * (Real.log B - Real.log A)) :=
          Finset.sum_le_sum key
      _ = A * (Real.log B - Real.log A) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            ← Finset.sum_mul, ← hAdef, ← hBdef]
          field_simp
          ring

/-! ### Superadditivity of the homogeneous entropy functional -/

/-- `∑ φ(Q z) - φ(∑ Q z)` rewritten as `∑ Q z * log ((∑ Q)/Q z)`. -/
lemma entropy_diff_eq {β : Type*} [Fintype β] (Q : β → ℝ) :
    (∑ z, -(Q z) * Real.log (Q z)) - (-(∑ z, Q z) * Real.log (∑ z, Q z))
      = ∑ z, Q z * (Real.log (∑ z', Q z') - Real.log (Q z)) := by
  have e1 : ∑ z, Q z * (Real.log (∑ z', Q z') - Real.log (Q z))
      = (∑ z, Q z) * Real.log (∑ z', Q z') + ∑ z, -(Q z) * Real.log (Q z) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [e1]; ring

/-- **Superadditivity** of `Ψ(v) = ∑ φ(v z) - φ(∑ v z)`, the `1`-homogeneous concave
extension of Shannon entropy.  This is exactly "conditioning on more reduces entropy",
before it is dressed up with laws. -/
lemma psi_superadd {β κ : Type*} [Fintype β] (K : Finset κ) (P : β → κ → ℝ)
    (hP : ∀ z c, 0 ≤ P z c) :
    ∑ c ∈ K, ((∑ z, -(P z c) * Real.log (P z c)) - (-(∑ z, P z c) * Real.log (∑ z, P z c)))
      ≤ (∑ z, -(∑ c ∈ K, P z c) * Real.log (∑ c ∈ K, P z c))
        - (-(∑ c ∈ K, ∑ z, P z c) * Real.log (∑ c ∈ K, ∑ z, P z c)) := by
  have hswap : ∑ c ∈ K, ∑ z, P z c = ∑ z, ∑ c ∈ K, P z c := Finset.sum_comm
  rw [hswap]
  rw [entropy_diff_eq (fun z => ∑ c ∈ K, P z c)]
  rw [Finset.sum_congr rfl (fun c (_ : c ∈ K) => entropy_diff_eq (fun z => P z c))]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun z _ => ?_
  have hle := log_sum_ineq K (fun c => P z c) (fun c => ∑ z', P z' c)
    (fun c _ => hP z c) (fun c _ => Finset.single_le_sum (fun z' _ => hP z' c) (Finset.mem_univ z))
  have hsum : ∑ c ∈ K, ∑ z', P z' c = ∑ z', ∑ c ∈ K, P z' c := Finset.sum_comm
  rw [hsum] at hle
  exact hle

/-! ### Laws of pairs, and of a composed random variable -/

lemma law_pair_sum {Ω β γ : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (w : Ω → ℝ) (Z : Ω → β) (W : Ω → γ) (c : γ) :
    ∑ z, law w (fun ω => (Z ω, W ω)) (z, c) = law w W c := by
  simp only [law]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : W ω = c
  · simp only [Prod.mk.injEq, h, and_true]
    exact Fintype.sum_ite_eq (Z ω) (fun _ => w ω)
  · simp [Prod.mk.injEq, h]

lemma law_comp {Ω γ δ : Type*} [Fintype Ω] [DecidableEq γ] [Fintype γ] [DecidableEq δ]
    (w : Ω → ℝ) (W : Ω → γ) (f : γ → δ) (d : δ) :
    law w (fun ω => f (W ω)) d = ∑ c ∈ Finset.univ.filter (fun c => f c = d), law w W c := by
  simp only [law]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_ite_eq (Finset.univ.filter (fun c => f c = d)) (W ω) (fun _ => w ω)]
  simp

lemma law_pair_comp {Ω β γ δ : Type*} [Fintype Ω] [DecidableEq β] [DecidableEq γ] [Fintype γ]
    [DecidableEq δ] (w : Ω → ℝ) (Z : Ω → β) (W : Ω → γ) (f : γ → δ) (z : β) (d : δ) :
    law w (fun ω => (Z ω, f (W ω))) (z, d)
      = ∑ c ∈ Finset.univ.filter (fun c => f c = d), law w (fun ω => (Z ω, W ω)) (z, c) := by
  simp only [law]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : Z ω = z
  · simp only [Prod.mk.injEq, h, true_and]
    rw [Finset.sum_ite_eq (Finset.univ.filter (fun c => f c = d)) (W ω) (fun _ => w ω)]
    simp
  · simp [Prod.mk.injEq, h]

lemma Hrv_pair_eq {Ω β γ : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] (w : Ω → ℝ) (Z : Ω → β) (W : Ω → γ) :
    Hrv w (fun ω => (Z ω, W ω))
      = ∑ c : γ, ∑ z : β, -(law w (fun ω => (Z ω, W ω)) (z, c))
          * Real.log (law w (fun ω => (Z ω, W ω)) (z, c)) := by
  simp only [Hrv, entropyW]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

end FiniteEntropy

/-! ### Frozen theorem #49 — conditioning on more reduces entropy -/

theorem condHrv_le_of_comp_proof {Ω : Type*} [Fintype Ω] {β γ δ : Type*} [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (Z : Ω → β) (W : Ω → γ) (f : γ → δ) :
    condHrv w Z (fun ω => f (W ω)) ≥ condHrv w Z W := by
  classical
  have _hw1 := hw1
  set P : β → γ → ℝ := fun z c => law w (fun ω => (Z ω, W ω)) (z, c) with hPdef
  have hPnn : ∀ z c, 0 ≤ P z c := fun z c => FiniteEntropy.law_nonneg hw _ _
  have hL : condHrv w Z W
      = ∑ c : γ, ((∑ z, -(P z c) * Real.log (P z c))
          - (-(∑ z, P z c) * Real.log (∑ z, P z c))) := by
    rw [condHrv, FiniteEntropy.Hrv_pair_eq]
    simp only [Hrv, entropyW]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hPdef]
    simp only
    rw [FiniteEntropy.law_pair_sum]
  have hR : condHrv w Z (fun ω => f (W ω))
      = ∑ d : δ, ((∑ z, -(∑ c ∈ Finset.univ.filter (fun c => f c = d), P z c)
            * Real.log (∑ c ∈ Finset.univ.filter (fun c => f c = d), P z c))
          - (-(∑ c ∈ Finset.univ.filter (fun c => f c = d), ∑ z, P z c)
            * Real.log (∑ c ∈ Finset.univ.filter (fun c => f c = d), ∑ z, P z c))) := by
    rw [condHrv, FiniteEntropy.Hrv_pair_eq]
    simp only [Hrv, entropyW]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [FiniteEntropy.law_pair_comp]
    · rw [FiniteEntropy.law_comp]
      have : ∀ c : γ, law w W c = ∑ z, P z c := fun c =>
        (FiniteEntropy.law_pair_sum w Z W c).symm
      simp only [this]
  rw [ge_iff_le, hL, hR]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset γ) f
      (fun c => (∑ z, -(P z c) * Real.log (P z c))
        - (-(∑ z, P z c) * Real.log (∑ z, P z c)))]
  refine Finset.sum_le_sum fun d _ => ?_
  exact FiniteEntropy.psi_superadd _ P hPnn

namespace FiniteEntropy

/-! ### Relabelling a random variable by an injective-on-its-range map -/

/-- If `e` separates the values actually taken by `Y`, then `e ∘ Y` has the same entropy
as `Y`. -/
lemma Hrv_map_eq {Ω β γ : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] (w : Ω → ℝ) (Y : Ω → β) (e : β → γ)
    (he : ∀ ω ω', e (Y ω) = e (Y ω') → Y ω = Y ω') :
    Hrv w (fun ω => e (Y ω)) = Hrv w Y := by
  classical
  set R : Finset β := Finset.image Y Finset.univ with hR
  have hlawY : ∀ z, z ∉ R → law w Y z = 0 := by
    intro z hz
    refine Finset.sum_eq_zero fun ω _ => ?_
    have hne : Y ω ≠ z := fun h => hz (h ▸ Finset.mem_image_of_mem Y (Finset.mem_univ ω))
    rw [if_neg hne]
  have hlawE : ∀ c, c ∉ R.image e → law w (fun ω => e (Y ω)) c = 0 := by
    intro c hc
    refine Finset.sum_eq_zero fun ω _ => ?_
    have hne : e (Y ω) ≠ c := fun h =>
      hc (h ▸ Finset.mem_image_of_mem e (Finset.mem_image_of_mem Y (Finset.mem_univ ω)))
    rw [if_neg hne]
  have hinj : ∀ z ∈ R, ∀ z' ∈ R, e z = e z' → z = z' := by
    intro z hz z' hz' hzz
    obtain ⟨ω, _, hω⟩ := Finset.mem_image.1 hz
    obtain ⟨ω', _, hω'⟩ := Finset.mem_image.1 hz'
    rw [← hω, ← hω']
    exact he ω ω' (by rw [hω, hω']; exact hzz)
  have hval : ∀ z ∈ R, law w (fun ω => e (Y ω)) (e z) = law w Y z := by
    intro z hz
    simp only [law]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : Y ω = z
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg]
      intro hcontra
      exact h (hinj (Y ω) (Finset.mem_image_of_mem Y (Finset.mem_univ ω)) z hz hcontra)
  calc Hrv w (fun ω => e (Y ω))
      = ∑ c ∈ R.image e,
          -(law w (fun ω => e (Y ω)) c) * Real.log (law w (fun ω => e (Y ω)) c) := by
        simp only [Hrv, entropyW]
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro c _ hc
        simp [hlawE c hc]
    _ = ∑ z ∈ R,
          -(law w (fun ω => e (Y ω)) (e z)) * Real.log (law w (fun ω => e (Y ω)) (e z)) :=
        Finset.sum_image hinj
    _ = ∑ z ∈ R, -(law w Y z) * Real.log (law w Y z) :=
        Finset.sum_congr rfl fun z hz => by rw [hval z hz]
    _ = Hrv w Y := by
        simp only [Hrv, entropyW]
        refine Finset.sum_subset (Finset.subset_univ _) ?_
        intro z _ hz
        simp [hlawY z hz]

/-- The entropy of a constant random variable is `0`. -/
lemma Hrv_const {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] {w : Ω → ℝ}
    (hw1 : ∑ ω, w ω = 1) (b₀ : β) : Hrv w (fun _ => b₀) = 0 := by
  have hlaw : law w (fun _ : Ω => b₀) = fun b => if b₀ = b then (1 : ℝ) else 0 := by
    funext b
    simp only [law]
    by_cases h : b₀ = b
    · simp [h, hw1]
    · simp [h]
  simp only [Hrv, entropyW, hlaw]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : b₀ = b <;> simp [h]

/-! ### Bookkeeping lemmas for `pref` -/

lemma pref_pref {n : ℕ} {k m : ℕ} (h : k ≤ m) (x : Fin n → Bool) :
    pref k (pref m x) = pref k x := by
  funext j
  simp only [pref]
  by_cases hj : (j : ℕ) < k
  · simp only [if_pos hj, if_pos (lt_of_lt_of_le hj h)]
  · simp only [if_neg hj]

lemma pref_succ_apply_self {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    pref (i.val + 1) x i = x i := by
  simp only [pref, if_pos (Nat.lt_succ_self i.val)]

lemma pref_succ_ext {n : ℕ} (i : Fin n) (x x' : Fin n → Bool)
    (h1 : x i = x' i) (h2 : pref i.val x = pref i.val x') :
    pref (i.val + 1) x = pref (i.val + 1) x' := by
  funext j
  simp only [pref]
  by_cases hji : (j : ℕ) < i.val + 1
  · simp only [if_pos hji]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hji with h | h
    · have hh := congrFun h2 j
      simp only [pref, if_pos h] at hh
      exact hh
    · have hji' : j = i := Fin.ext h
      subst hji'
      exact h1
  · simp only [if_neg hji]

lemma pref_full {n : ℕ} (x : Fin n → Bool) : pref n x = x := by
  funext j
  simp only [pref, if_pos j.isLt]

lemma pref_zero {n : ℕ} (x : Fin n → Bool) : pref 0 x = fun _ => false := by
  funext j
  simp only [pref, Nat.not_lt_zero, if_neg, not_false_eq_true]

end FiniteEntropy

/-! ### Frozen theorem #48 — the chain rule -/

theorem entropy_chain_rule_proof {Ω : Type*} [Fintype Ω] {n : ℕ} (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (X : Ω → (Fin n → Bool)) :
    Hrv w X = ∑ i : Fin n, condHrv w (fun ω => X ω i) (fun ω => pref i.val (X ω)) := by
  classical
  have _hw := hw
  have hstep : ∀ i : Fin n, condHrv w (fun ω => X ω i) (fun ω => pref i.val (X ω))
      = Hrv w (fun ω => pref (i.val + 1) (X ω)) - Hrv w (fun ω => pref i.val (X ω)) := by
    intro i
    rw [condHrv]
    congr 1
    have hmap := FiniteEntropy.Hrv_map_eq w (fun ω => pref (i.val + 1) (X ω))
      (fun y => (y i, pref i.val y)) ?_
    · rw [← hmap]
      congr 1
      funext ω
      simp only [FiniteEntropy.pref_succ_apply_self,
        FiniteEntropy.pref_pref (Nat.le_succ i.val)]
    · intro ω ω' h
      simp only [Prod.mk.injEq, FiniteEntropy.pref_succ_apply_self,
        FiniteEntropy.pref_pref (Nat.le_succ i.val)] at h
      exact FiniteEntropy.pref_succ_ext i _ _ h.1 h.2
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => Hrv w (fun ω => pref (k + 1) (X ω)) - Hrv w (fun ω => pref k (X ω))) n]
  rw [Finset.sum_range_sub (fun k => Hrv w (fun ω => pref k (X ω))) n]
  have hzero : Hrv w (fun ω => pref 0 (X ω)) = 0 := by
    have hcst : (fun ω => pref 0 (X ω)) = (fun _ : Ω => (fun _ : Fin n => false)) := by
      funext ω
      exact FiniteEntropy.pref_zero (X ω)
    rw [hcst]
    exact FiniteEntropy.Hrv_const hw1 _
  have hfull : (fun ω => pref n (X ω)) = X := by
    funext ω
    exact FiniteEntropy.pref_full (X ω)
  rw [hzero, hfull, sub_zero]

namespace FiniteEntropy

/-! ### The prefix conditional entropy is `HiFun` -/

/-- The two-point entropy identity `φ(a) + φ(b) - φ(a+b) = (a+b) H(a/(a+b))`. -/
lemma split_entropy (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (-a * Real.log a) + (-b * Real.log b) - (-(a + b) * Real.log (a + b))
      = (a + b) * Hnat (a / (a + b)) := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0]
    simp [Hnat]
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · rw [← hb0, add_zero, div_self (ne_of_gt hapos)]
      simp [Hnat]
    · have hs : 0 < a + b := by linarith
      have e1 : 1 - a / (a + b) = b / (a + b) := by
        field_simp
        ring
      simp only [Hnat, e1]
      rw [Real.log_div (ne_of_gt hapos) (ne_of_gt hs),
        Real.log_div (ne_of_gt hbpos) (ne_of_gt hs)]
      field_simp
      ring

lemma law_pref_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    law (unifW G) (fun x => pref i.val x) v
      = ((prefFiber G i v).card : ℝ) / (G.card : ℝ) := by
  have hcongr : ∀ x : Fin n → Bool, (if pref i.val x = v then unifW G x else 0)
      = if x ∈ prefFiber G i v then (1 : ℝ) / (G.card : ℝ) else 0 := by
    intro x
    simp only [unifW, prefFiber, Finset.mem_filter]
    by_cases h1 : x ∈ G <;> by_cases h2 : pref i.val x = v <;> simp [h1, h2]
  simp only [law]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hcongr x), Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

lemma law_pair_false_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    law (unifW G) (fun x => (x i, pref i.val x)) (false, v)
      = (((prefFiber G i v).filter (fun x => x i = false)).card : ℝ) / (G.card : ℝ) := by
  have hcongr : ∀ x : Fin n → Bool,
      (if (x i, pref i.val x) = (false, v) then unifW G x else 0)
        = if x ∈ (prefFiber G i v).filter (fun x => x i = false) then (1 : ℝ) / (G.card : ℝ)
            else 0 := by
    intro x
    simp only [unifW, prefFiber, Finset.mem_filter, Prod.mk.injEq]
    by_cases h1 : x ∈ G <;> by_cases h2 : pref i.val x = v <;> by_cases h3 : x i = false <;>
      simp [h1, h2, h3]
  simp only [law]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hcongr x), Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The heart of BLUEPRINT I6: the conditional entropy of the `i`-th bit given the length-`i`
prefix, under the uniform distribution on `G`, is the prefix-weighted average `HiFun G i` of
`Hnat (pcond G i ·)`. -/
lemma condHrv_eq_HiFun {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) :
    condHrv (unifW G) (fun x => x i) (fun x => pref i.val x) = HiFun G i := by
  classical
  set w := unifW G with hw
  set P : Bool → (Fin n → Bool) → ℝ :=
    fun b v => law w (fun x => (x i, pref i.val x)) (b, v) with hP
  have hPnn : ∀ b v, 0 ≤ P b v := fun b v =>
    law_nonneg (unifW_nonneg G) _ _
  have hlawW : ∀ v, law w (fun x => pref i.val x) v = P false v + P true v := by
    intro v
    rw [← law_pair_sum w (fun x => x i) (fun x => pref i.val x) v]
    rw [Fintype.sum_bool]
    ring
  -- the conditional entropy as a sum over prefix patterns
  have hcond : condHrv w (fun x => x i) (fun x => pref i.val x)
      = ∑ v : Fin n → Bool, ((-(P false v) * Real.log (P false v))
          + (-(P true v) * Real.log (P true v))
          - (-(P false v + P true v) * Real.log (P false v + P true v))) := by
    rw [condHrv, Hrv_pair_eq]
    simp only [Hrv, entropyW]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hlawW v, Fintype.sum_bool]
    ring
  -- each summand is `Pr(prefix = v) * Hnat (pcondV G i v)`
  have hterm : ∀ v : Fin n → Bool,
      ((-(P false v) * Real.log (P false v)) + (-(P true v) * Real.log (P true v))
          - (-(P false v + P true v) * Real.log (P false v + P true v)))
        = law w (fun x => pref i.val x) v * Hnat (pcondV G i v) := by
    intro v
    rw [split_entropy (P false v) (P true v) (hPnn false v) (hPnn true v), ← hlawW v]
    rcases eq_or_lt_of_le (law_nonneg (unifW_nonneg G) (fun x => pref i.val x) v) with h0 | hpos
    · rw [← h0]
      simp
    · congr 1
      have hAcard : ((prefFiber G i v).card : ℝ) ≠ 0 := by
        intro hc
        rw [law_pref_eq G i v, hc] at hpos
        simp at hpos
      have hGcard : ((G.card : ℝ)) ≠ 0 := by
        intro hc
        rw [law_pref_eq G i v, hc] at hpos
        simp at hpos
      have hAne : (prefFiber G i v).card ≠ 0 := by exact_mod_cast hAcard
      rw [hP]
      simp only
      rw [hw, law_pair_false_eq G i v, law_pref_eq G i v]
      unfold pcondV
      rw [if_neg hAne]
      field_simp
  rw [hcond, Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hterm v)]
  -- and `HiFun` is the same sum, regrouped fibrewise
  have hHi : HiFun G i
      = ∑ v : Fin n → Bool, law w (fun x => pref i.val x) v * Hnat (pcondV G i v) := by
    simp only [HiFun, ← hw]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n → Bool)) (fun x => pref i.val x)
      (fun x => w x * Hnat (pcond G i x))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hval : ∀ x ∈ Finset.univ.filter (fun x => pref i.val x = v),
        w x * Hnat (pcond G i x) = w x * Hnat (pcondV G i v) := by
      intro x hx
      rw [pcond_eq_pcondV, (Finset.mem_filter.1 hx).2]
    rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
    congr 1
    simp only [law]
    rw [Finset.sum_filter]
  rw [hHi]

end FiniteEntropy

/-! ### Frozen theorem #52 — the prefix entropy decomposition -/

theorem prefix_entropy_decomposition_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∑ i : Fin n, HiFun G i = Real.log (G.card : ℝ) := by
  have hchain := entropy_chain_rule_proof (unifW G) (FiniteEntropy.unifW_nonneg G)
    (FiniteEntropy.unifW_sum_eq_one G hG) (id : (Fin n → Bool) → (Fin n → Bool))
  rw [uniform_entropy_eq_log_card_proof G hG] at hchain
  rw [hchain]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [id_eq]
  exact (FiniteEntropy.condHrv_eq_HiFun G i).symm

namespace Solution

theorem entropy_chain_rule {Ω : Type*} [Fintype Ω] {n : ℕ} (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (X : Ω → (Fin n → Bool)) :
    Hrv w X = ∑ i : Fin n, condHrv w (fun ω => X ω i) (fun ω => pref i.val (X ω)) :=
  EntropyBound.entropy_chain_rule_proof w hw hw1 X

theorem condHrv_le_of_comp {Ω : Type*} [Fintype Ω] {β γ δ : Type*} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (Z : Ω → β) (W : Ω → γ) (f : γ → δ) :
    condHrv w Z (fun ω => f (W ω)) ≥ condHrv w Z W :=
  EntropyBound.condHrv_le_of_comp_proof w hw hw1 Z W f

theorem prefix_entropy_decomposition {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∑ i : Fin n, HiFun G i = Real.log (G.card : ℝ) :=
  EntropyBound.prefix_entropy_decomposition_proof G hG

end Solution

example : @EntropyBound.entropy_chain_rule = @EntropyBound.Solution.entropy_chain_rule := rfl

example : @EntropyBound.condHrv_le_of_comp = @EntropyBound.Solution.condHrv_le_of_comp := rfl

example : @EntropyBound.prefix_entropy_decomposition
    = @EntropyBound.Solution.prefix_entropy_decomposition := rfl

end EntropyBound
