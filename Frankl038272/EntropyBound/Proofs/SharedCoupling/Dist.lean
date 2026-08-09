/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.FiniteEntropy.Core
import EntropyBound.Proofs.FiniteEntropy.Chain
import EntropyBound.Proofs.RankOne.Kernel

/-!
# Stage K item K1 — the shared-sign coupling is a distribution (`SKETCH.md` (11a))

Frozen theorem #56.  The transition kernel `kern` is an honest Markov kernel: each value lies
in `[0,1]` (by the factor bounds of Stage C item C2, applied to `pcond G i v ∈ [0,1]`), and the
two values at a fixed prefix sum to `1`.  The chain sum `∑ x, ∏ i, kern G i (u i) x (x i) = 1`
is then proved by an induction on the coordinate index: adding one coordinate halves the sum,
because flipping that coordinate is a fixed-point-free involution under which the partial
product's *other* factors are invariant.

Support lemmas live in `namespace EntropyBound.SharedCoupling`.
-/

namespace EntropyBound

namespace SharedCoupling

open FiniteEntropy

/-! ### `pcond` is a probability -/

lemma pcondV_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    0 ≤ pcondV G i v := by
  unfold pcondV
  split
  · exact le_rfl
  · positivity

lemma pcondV_le_one {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    pcondV G i v ≤ 1 := by
  unfold pcondV
  split
  · norm_num
  · rename_i h
    have hpos : (0 : ℝ) < ((prefFiber G i v).card : ℝ) := by
      have : 0 < (prefFiber G i v).card := Nat.pos_of_ne_zero h
      exact_mod_cast this
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_filter_le _ _

lemma pcond_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    0 ≤ pcond G i v := by
  rw [pcond_eq_pcondV]; exact pcondV_nonneg G i _

lemma pcond_le_one {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    pcond G i v ≤ 1 := by
  rw [pcond_eq_pcondV]; exact pcondV_le_one G i _

/-! ### The modified transition probability stays in `[0,1]` -/

lemma pmod_true {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    pmod G i true v = pcond G i v + lam * pcond G i v * (1 - pcond G i v) := by
  unfold pmod lam
  rw [if_pos (rfl : (true : Bool) = true)]
  ring

lemma pmod_false {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    pmod G i false v = pcond G i v - lam * pcond G i v * (1 - pcond G i v) := by
  unfold pmod lam
  rw [if_neg (by simp : ¬ ((false : Bool) = true))]
  ring

lemma pmod_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) : 0 ≤ pmod G i σ v := by
  have h0 := pcond_nonneg G i v
  have h1 := pcond_le_one G i v
  cases σ with
  | false => rw [pmod_false]; exact RankOne.sub_factor_nonneg h0
  | true => rw [pmod_true]; exact RankOne.add_factor_nonneg h0 h1

lemma pmod_le_one {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) : pmod G i σ v ≤ 1 := by
  have h0 := pcond_nonneg G i v
  have h1 := pcond_le_one G i v
  cases σ with
  | false => rw [pmod_false]; exact RankOne.sub_factor_le_one h0 h1
  | true => rw [pmod_true]; exact RankOne.add_factor_le_one h1

/-- Transitions at the endpoints are unchanged: this is what keeps the modified chain inside
the support of the original one. -/
lemma pmod_eq_of_endpoints {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) (h : pcond G i v = 0 ∨ pcond G i v = 1) :
    pmod G i σ v = pcond G i v := by
  rcases h with h | h <;> simp only [pmod, h] <;> ring

/-! ### `kern` is a Markov kernel -/

lemma kern_false {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) : kern G i σ v false = pmod G i σ v := by
  simp [kern]

lemma kern_true {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) : kern G i σ v true = 1 - pmod G i σ v := by
  simp [kern]

lemma kern_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) (b : Bool) : 0 ≤ kern G i σ v b := by
  cases b with
  | false => rw [kern_false]; exact pmod_nonneg G i σ v
  | true => rw [kern_true]; linarith [pmod_le_one G i σ v]

lemma kern_le_one {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) (b : Bool) : kern G i σ v b ≤ 1 := by
  cases b with
  | false => rw [kern_false]; exact pmod_le_one G i σ v
  | true => rw [kern_true]; linarith [pmod_nonneg G i σ v]

lemma kern_sum_eq_one {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) : ∑ b : Bool, kern G i σ v b = 1 := by
  rw [Fintype.sum_bool, kern_false, kern_true]
  ring

/-- The two values of `kern` at a fixed prefix, listed in either order, sum to `1`. -/
lemma kern_add_not {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    (v : Fin n → Bool) (b : Bool) : kern G i σ v b + kern G i σ v (!b) = 1 := by
  cases b <;>
    simp only [Bool.not_false, Bool.not_true, kern_false, kern_true] <;> ring

/-! ### The partial chain product -/

/-- The product of the transition weights over the first `k` coordinates. -/
noncomputable def chainProd {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (k : ℕ)
    (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), kern G i (u i) x (x i)

lemma chainProd_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (k : ℕ)
    (x : Fin n → Bool) : 0 ≤ chainProd G u k x :=
  Finset.prod_nonneg fun i _ => kern_nonneg G i (u i) x (x i)

lemma chainProd_zero {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool)
    (x : Fin n → Bool) : chainProd G u 0 x = 1 := by
  simp [chainProd]

lemma chainProd_full {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool)
    (x : Fin n → Bool) : chainProd G u n x = ∏ i, kern G i (u i) x (x i) := by
  simp only [chainProd]
  congr 1
  exact Finset.filter_true_of_mem fun i _ => i.isLt

lemma pcond_congr_pref {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) {x y : Fin n → Bool}
    (h : pref i.val x = pref i.val y) : pcond G i x = pcond G i y := by
  rw [pcond_eq_pcondV, pcond_eq_pcondV, h]

lemma kern_congr {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool)
    {x y : Fin n → Bool} (h : pcond G i x = pcond G i y) (b : Bool) :
    kern G i σ x b = kern G i σ y b := by
  simp only [kern, pmod, h]

/-- The partial chain product only depends on the prefix. -/
lemma chainProd_congr {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (k : ℕ)
    {x y : Fin n → Bool} (h : pref k x = pref k y) :
    chainProd G u k x = chainProd G u k y := by
  simp only [chainProd]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hik : i.val < k := (Finset.mem_filter.1 hi).2
  have hxy : x i = y i := by
    have h1 := congrFun h i
    simpa only [pref, if_pos hik] using h1
  have hpref : pref i.val x = pref i.val y := by
    rw [← pref_pref (le_of_lt hik) x, h, pref_pref (le_of_lt hik) y]
  rw [hxy]
  exact kern_congr G i (u i) (pcond_congr_pref G i hpref) (y i)

/-- Adding one coordinate to the partial product. -/
lemma chainProd_succ {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (i : Fin n)
    (x : Fin n → Bool) :
    chainProd G u (i.val + 1) x
      = kern G i (u i) x (x i) * chainProd G u i.val x := by
  classical
  have hset : (Finset.univ.filter (fun j : Fin n => j.val < i.val + 1))
      = insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · intro hj
      rcases hj with h | h
      · rw [h]; exact Nat.lt_succ_self i.val
      · exact Nat.lt_succ_of_lt h
  have hnot : i ∉ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by simp
  simp only [chainProd, hset]
  rw [Finset.prod_insert hnot]

/-! ### Halving: one more coordinate halves the chain sum -/

lemma pref_update_self {n : ℕ} (i : Fin n) (x : Fin n → Bool) (b : Bool) :
    pref i.val (Function.update x i b) = pref i.val x := by
  funext j
  simp only [pref, Function.update_apply]
  by_cases h : (j : ℕ) < i.val
  · have hne : j ≠ i := by
      intro hji
      rw [hji] at h
      exact absurd h (lt_irrefl i.val)
    simp [h, hne]
  · simp [h]

lemma two_mul_chain_sum_succ {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool)
    (i : Fin n) :
    2 * (∑ x, chainProd G u (i.val + 1) x) = ∑ x, chainProd G u i.val x := by
  classical
  have hflip : ∀ x : Fin n → Bool,
      (2 * chainProd G u (i.val + 1) x - chainProd G u i.val x)
        + (2 * chainProd G u (i.val + 1) (Function.update x i (!(x i)))
            - chainProd G u i.val (Function.update x i (!(x i)))) = 0 := by
    intro x
    have hyk : (Function.update x i (!(x i))) i = !(x i) := by simp
    have hpref : pref i.val (Function.update x i (!(x i))) = pref i.val x :=
      pref_update_self i x (!(x i))
    have hck : chainProd G u i.val (Function.update x i (!(x i))) = chainProd G u i.val x :=
      chainProd_congr G u i.val hpref
    have hkern : kern G i (u i) (Function.update x i (!(x i)))
        ((Function.update x i (!(x i))) i) = kern G i (u i) x (!(x i)) := by
      rw [hyk]
      exact kern_congr G i (u i) (pcond_congr_pref G i hpref) _
    rw [chainProd_succ G u i x, chainProd_succ G u i (Function.update x i (!(x i))),
      hkern, hck]
    have hadd := kern_add_not G i (u i) x (x i)
    linear_combination (2 * chainProd G u i.val x) * hadd
  have hne : ∀ x : Fin n → Bool,
      (2 * chainProd G u (i.val + 1) x - chainProd G u i.val x) ≠ 0 →
        Function.update x i (!(x i)) ≠ x := by
    intro x _ hcontra
    have hc := congrFun hcontra i
    simp at hc
  have hinv : ∀ x : Fin n → Bool,
      Function.update (Function.update x i (!(x i))) i
          (!((Function.update x i (!(x i))) i)) = x := by
    intro x
    have h1 : (Function.update x i (!(x i))) i = !(x i) := by simp
    rw [h1]
    funext j
    by_cases h : j = i <;> simp [h]
  have hsum : ∑ x, (2 * chainProd G u (i.val + 1) x - chainProd G u i.val x) = 0 :=
    Finset.sum_ninvolution (fun x => Function.update x i (!(x i))) hflip hne
      (fun _ => Finset.mem_univ _) hinv
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

lemma chain_sum_pow {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) :
    ∀ k : ℕ, k ≤ n → (2 : ℝ) ^ k * (∑ x, chainProd G u k x) = 2 ^ n := by
  intro k
  induction k with
  | zero =>
      intro _
      simp only [pow_zero, one_mul]
      have h0 : ∀ x : Fin n → Bool, chainProd G u 0 x = 1 := chainProd_zero G u
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => h0 x)]
      simp
  | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hprev := ih (le_of_lt hkn)
      have hstep : 2 * (∑ x, chainProd G u (k + 1) x) = ∑ x, chainProd G u k x :=
        two_mul_chain_sum_succ G u ⟨k, hkn⟩
      have hre : (2 : ℝ) ^ (k + 1) * (∑ x, chainProd G u (k + 1) x)
          = 2 ^ k * (2 * ∑ x, chainProd G u (k + 1) x) := by ring
      rw [hre, hstep]
      exact hprev

/-- **The chain sums to one.**  No hypothesis on `G` is needed: the junk value `pcond = 0`
still gives a Markov kernel. -/
lemma chain_sum_one {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) :
    ∑ x, (∏ i, kern G i (u i) x (x i)) = 1 := by
  have h := chain_sum_pow G u n le_rfl
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hfull : ∀ x : Fin n → Bool, chainProd G u n x = ∏ i, kern G i (u i) x (x i) :=
    chainProd_full G u
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hfull x)] at h
  field_simp at h
  exact h

/-! ### `wshW` is a distribution -/

lemma wshW_nonneg {n : ℕ} (G : Finset (Fin n → Bool))
    (p : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) : 0 ≤ wshW G p := by
  simp only [wshW]
  refine mul_nonneg (mul_nonneg (by positivity) ?_) ?_ <;>
    exact Finset.prod_nonneg fun i _ => kern_nonneg G i _ _ _

lemma wshW_sum_eq_one {n : ℕ} (G : Finset (Fin n → Bool)) : ∑ p, wshW G p = 1 := by
  classical
  have hstep : ∀ u : Fin n → Bool,
      ∑ q : (Fin n → Bool) × (Fin n → Bool), wshW G (u, q) = (1 / 2 : ℝ) ^ n := by
    intro u
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x : Fin n → Bool,
        ∑ y, wshW G (u, x, y)
          = ((1 / 2 : ℝ) ^ n * (∏ i, kern G i (u i) x (x i))) := by
      intro x
      simp only [wshW]
      rw [← Finset.mul_sum, chain_sum_one G u, mul_one]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hinner x)]
    rw [← Finset.mul_sum, chain_sum_one G u, mul_one]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hstep u)]
  rw [Finset.sum_const, Finset.card_univ]
  simp

end SharedCoupling

/-! ### Frozen theorem #56 — the shared-sign coupling is a distribution -/

theorem shared_isDist_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    (∀ p, 0 ≤ wshW G p) ∧ ∑ p, wshW G p = 1 := by
  have _hG := hG
  exact ⟨SharedCoupling.wshW_nonneg G, SharedCoupling.wshW_sum_eq_one G⟩

namespace Solution

theorem shared_isDist {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    (∀ p, 0 ≤ wshW G p) ∧ ∑ p, wshW G p = 1 :=
  EntropyBound.shared_isDist_proof G hG

end Solution

example : @EntropyBound.shared_isDist = @EntropyBound.Solution.shared_isDist := rfl

end EntropyBound
