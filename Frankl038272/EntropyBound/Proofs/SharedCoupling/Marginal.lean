/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.SharedCoupling.Dist

/-!
# Stage K items K2 and K3 — support and marginal uniformity (`SKETCH.md` (11a), (11b))

Frozen theorems #57 and #58.

* #57: transitions with `pcond ∈ {0,1}` are unchanged (`pmod_eq_of_endpoints`), so the modified
  chain never leaves the support of the original one; an induction on the coordinate index shows
  that each prefix of a `wshW`-supported vector is realized inside `G`.
* #58: averaging the explicit product formula over the sign vector factorizes coordinatewise
  (`Fintype.prod_sum`), and `(1/2)(π(v,b;+) + π(v,b;-))` is the *unmodified* transition
  probability; the resulting telescoping product is `unifW G x` by the chain rule for the
  uniform distribution on `G`.
-/

namespace EntropyBound

namespace SharedCoupling

open FiniteEntropy

/-! ### Prefix fibers, indexed by a plain natural number -/

/-- The members of `G` agreeing with `x` on the first `k` coordinates. -/
def fibK {n : ℕ} (G : Finset (Fin n → Bool)) (k : ℕ) (x : Fin n → Bool) :
    Finset (Fin n → Bool) := G.filter (fun z => pref k z = pref k x)

lemma fibK_val {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (x : Fin n → Bool) :
    fibK G i.val x = prefFiber G i (pref i.val x) := rfl

lemma fibK_zero {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) : fibK G 0 x = G := by
  refine Finset.filter_true_of_mem fun z _ => ?_
  rw [pref_zero, pref_zero]

lemma fibK_full {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) :
    fibK G n x = G.filter (fun z => z = x) := by
  refine Finset.filter_congr fun z _ => ?_
  rw [pref_full, pref_full]

/-- Peeling one coordinate off a prefix fiber. -/
lemma fibK_succ {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (x : Fin n → Bool) :
    fibK G (i.val + 1) x = (fibK G i.val x).filter (fun z => z i = x i) := by
  ext z
  simp only [fibK, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hpz⟩
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · rw [← pref_pref (Nat.le_succ i.val) z, hpz, pref_pref (Nat.le_succ i.val) x]
    · have h1 := congrFun hpz i
      simpa only [pref_succ_apply_self] using h1
  · rintro ⟨⟨hz, hpz⟩, hzi⟩
    exact ⟨hz, pref_succ_ext i z x hzi hpz⟩

/-! ### K2 — the modified chain stays in the support -/

lemma support_prefix {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) (u x : Fin n → Bool)
    (hall : ∀ i : Fin n, kern G i (u i) x (x i) ≠ 0) :
    ∀ k : ℕ, k ≤ n → (fibK G k x).Nonempty := by
  intro k
  induction k with
  | zero => intro _; rw [fibK_zero]; exact hG
  | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      set i : Fin n := ⟨k, hkn⟩ with hidef
      have hA : (fibK G i.val x).Nonempty := ih (le_of_lt hkn)
      have hcard : (fibK G i.val x).card ≠ 0 := by
        rw [← Finset.card_pos] at hA
        omega
      have hcardR : ((fibK G i.val x).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
      have hp : pcond G i x = pcondV G i (pref i.val x) := pcond_eq_pcondV G i x
      have hpv : pcondV G i (pref i.val x)
          = (((fibK G i.val x).filter (fun z => z i = false)).card : ℝ)
              / ((fibK G i.val x).card : ℝ) := by
        rw [fibK_val]
        unfold pcondV
        rw [if_neg (by rw [fibK_val] at hcard; exact hcard)]
      have hgoal : (fibK G (i.val + 1) x).Nonempty := by
        rw [fibK_succ]
        cases hxi : x i with
        | false =>
            have hpne : pcond G i x ≠ 0 := by
              intro h0
              have := pmod_eq_of_endpoints G i (u i) x (Or.inl h0)
              have hk0 : kern G i (u i) x (x i) = 0 := by
                rw [hxi, kern_false, this, h0]
              exact hall i hk0
            rw [hp, hpv] at hpne
            have hBpos : (((fibK G i.val x).filter (fun z => z i = false)).card : ℝ) ≠ 0 := by
              intro h0
              rw [h0] at hpne
              simp at hpne
            have : ((fibK G i.val x).filter (fun z => z i = false)).Nonempty := by
              rw [← Finset.card_pos]
              have : ((fibK G i.val x).filter (fun z => z i = false)).card ≠ 0 :=
                Nat.cast_ne_zero.mp hBpos
              omega
            obtain ⟨z, hz⟩ := this
            exact ⟨z, by simpa [hxi] using hz⟩
        | true =>
            have hpne : pcond G i x ≠ 1 := by
              intro h1
              have := pmod_eq_of_endpoints G i (u i) x (Or.inr h1)
              have hk0 : kern G i (u i) x (x i) = 0 := by
                rw [hxi, kern_true, this, h1]; ring
              exact hall i hk0
            by_contra hcon
            rw [Finset.not_nonempty_iff_eq_empty] at hcon
            have hall' : ∀ z ∈ fibK G i.val x, z i = false := by
              intro z hz
              by_contra hzc
              have hzt : z i = true := by
                cases hb : z i
                · exact absurd hb hzc
                · rfl
              have hmem : z ∈ (fibK G i.val x).filter (fun z => z i = true) :=
                Finset.mem_filter.2 ⟨hz, hzt⟩
              rw [hcon] at hmem
              simp at hmem
            have heq : (fibK G i.val x).filter (fun z => z i = false) = fibK G i.val x :=
              Finset.filter_true_of_mem hall'
            rw [hp, hpv, heq, div_self hcardR] at hpne
            exact hpne rfl
      exact hgoal

lemma chain_mem {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) (u x : Fin n → Bool)
    (h : (∏ i, kern G i (u i) x (x i)) ≠ 0) : x ∈ G := by
  have hall : ∀ i : Fin n, kern G i (u i) x (x i) ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := support_prefix G hG u x hall n le_rfl
  rw [fibK_full, Finset.mem_filter] at hz
  exact hz.2 ▸ hz.1

/-! ### K3 — marginal uniformity -/

/-- The *unmodified* transition probability of the original chain. -/
noncomputable def qbit {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) (i : Fin n) : ℝ :=
  if x i = false then pcond G i x else 1 - pcond G i x

lemma qbit_false {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) {i : Fin n}
    (h : x i = false) : qbit G x i = pcond G i x := by
  unfold qbit; rw [if_pos h]

lemma qbit_true {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) {i : Fin n}
    (h : x i = true) : qbit G x i = 1 - pcond G i x := by
  unfold qbit
  rw [if_neg (by rw [h]; simp)]

/-- Averaging the modified transition over the two signs restores the original one. -/
lemma sum_sign_kern {n : ℕ} (G : Finset (Fin n → Bool)) (x : Fin n → Bool) (i : Fin n) :
    ∑ b : Bool, kern G i b x (x i) = 2 * qbit G x i := by
  rw [Fintype.sum_bool]
  cases hxi : x i with
  | false =>
      rw [qbit_false G x hxi, kern_false, kern_false, pmod_true, pmod_false]
      ring
  | true =>
      rw [qbit_true G x hxi, kern_true, kern_true, pmod_true, pmod_false]
      ring

/-- The chain rule for the uniform distribution on `G`. -/
lemma card_fibK_div {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) (x : Fin n → Bool) :
    ∀ k : ℕ, k ≤ n →
      ((fibK G k x).card : ℝ) / (G.card : ℝ)
        = ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), qbit G x i := by
  have hGcard : ((G.card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hG).ne'
  intro k
  induction k with
  | zero =>
      intro _
      rw [fibK_zero]
      have hemp : (Finset.univ.filter (fun i : Fin n => i.val < 0)) = ∅ := by simp
      rw [hemp, Finset.prod_empty]
      exact div_self hGcard
  | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      set i : Fin n := ⟨k, hkn⟩ with hidef
      have hprev := ih (le_of_lt hkn)
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
      rw [show k + 1 = i.val + 1 from rfl, hset, Finset.prod_insert hnot, ← hprev]
      -- the cardinality recursion
      have hBcard : ((fibK G i.val x).card : ℝ) * pcond G i x
          = (((fibK G i.val x).filter (fun z => z i = false)).card : ℝ) := by
        rw [pcond_eq_pcondV, fibK_val]
        exact card_mul_pcondV G i (pref i.val x)
      have hsplit : (((fibK G i.val x).filter (fun z => z i = false)).card
          + ((fibK G i.val x).filter (fun z => ¬ (z i = false))).card)
            = (fibK G i.val x).card := by
        have h := Finset.card_filter_add_card_filter_not
          (s := fibK G i.val x) (p := fun z => z i = false)
        simpa using h
      have hkey : ((fibK G (i.val + 1) x).card : ℝ)
          = ((fibK G i.val x).card : ℝ) * qbit G x i := by
        rw [fibK_succ]
        cases hxi : x i with
        | false =>
            rw [qbit_false G x hxi]
            exact hBcard.symm
        | true =>
            rw [qbit_true G x hxi]
            have hfil : (fibK G i.val x).filter (fun z => z i = true)
                = (fibK G i.val x).filter (fun z => ¬ (z i = false)) := by
              refine Finset.filter_congr fun z _ => ?_
              cases z i <;> simp
            rw [hfil]
            have hsplitR : ((((fibK G i.val x).filter (fun z => z i = false)).card : ℝ)
                + (((fibK G i.val x).filter (fun z => ¬ (z i = false))).card : ℝ))
                  = ((fibK G i.val x).card : ℝ) := by exact_mod_cast hsplit
            linear_combination hsplitR + hBcard
      rw [hkey]
      field_simp
      ring

lemma prod_qbit_eq_unifW {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty)
    (x : Fin n → Bool) : (∏ i, qbit G x i) = unifW G x := by
  have h := card_fibK_div G hG x n le_rfl
  have hfil : (Finset.univ.filter (fun i : Fin n => i.val < n)) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => i.isLt
  rw [hfil] at h
  rw [← h, fibK_full, Finset.filter_eq' G x]
  by_cases hx : x ∈ G
  · rw [if_pos hx]
    simp only [Finset.card_singleton, Nat.cast_one, unifW, if_pos hx]
  · rw [if_neg hx]
    simp only [Finset.card_empty, Nat.cast_zero, unifW, if_neg hx, zero_div]

lemma sum_y_wshW {n : ℕ} (G : Finset (Fin n → Bool)) (u x : Fin n → Bool) :
    ∑ y, wshW G (u, x, y) = (1 / 2 : ℝ) ^ n * (∏ i, kern G i (u i) x (x i)) := by
  simp only [wshW]
  rw [← Finset.mul_sum, chain_sum_one G u, mul_one]

end SharedCoupling

/-! ### Frozen theorem #57 — the shared coupling stays inside `G` -/

theorem shared_support_mem_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty)
    (hUC : UnionClosedCube G) :
    ∀ p, wshW G p ≠ 0 → orVec p.2.1 p.2.2 ∈ G := by
  intro p hp
  simp only [wshW] at hp
  have h1 : (∏ i, kern G i (p.1 i) p.2.1 (p.2.1 i)) ≠ 0 := by
    intro h
    apply hp
    rw [h, mul_zero, zero_mul]
  have h2 : (∏ i, kern G i (p.1 i) p.2.2 (p.2.2 i)) ≠ 0 := by
    intro h
    apply hp
    rw [h, mul_zero]
  exact hUC _ (SharedCoupling.chain_mem G hG p.1 p.2.1 h1) _
    (SharedCoupling.chain_mem G hG p.1 p.2.2 h2)

/-! ### Frozen theorem #58 — the shared coupling has uniform marginals -/

theorem shared_marginal_uniform_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∀ x, (∑ u, ∑ y, wshW G (u, x, y)) = unifW G x := by
  intro x
  have hstep : ∀ u : Fin n → Bool,
      ∑ y, wshW G (u, x, y) = (1 / 2 : ℝ) ^ n * (∏ i, kern G i (u i) x (x i)) :=
    fun u => SharedCoupling.sum_y_wshW G u x
  rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hstep u), ← Finset.mul_sum]
  have hfac : ∑ u : Fin n → Bool, (∏ i, kern G i (u i) x (x i))
      = ∏ i : Fin n, ∑ b : Bool, kern G i b x (x i) :=
    (Fintype.prod_sum (fun (i : Fin n) (b : Bool) => kern G i b x (x i))).symm
  rw [hfac]
  have hsign : ∀ i : Fin n, ∑ b : Bool, kern G i b x (x i) = 2 * SharedCoupling.qbit G x i :=
    fun i => SharedCoupling.sum_sign_kern G x i
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hsign i)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [SharedCoupling.prod_qbit_eq_unifW G hG x]
  have h2 : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, h2, one_mul]

namespace Solution

theorem shared_support_mem {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty)
    (hUC : UnionClosedCube G) :
    ∀ p, wshW G p ≠ 0 → orVec p.2.1 p.2.2 ∈ G :=
  EntropyBound.shared_support_mem_proof G hG hUC

theorem shared_marginal_uniform {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∀ x, (∑ u, ∑ y, wshW G (u, x, y)) = unifW G x :=
  EntropyBound.shared_marginal_uniform_proof G hG

end Solution

example : @EntropyBound.shared_support_mem = @EntropyBound.Solution.shared_support_mem := rfl

example : @EntropyBound.shared_marginal_uniform
    = @EntropyBound.Solution.shared_marginal_uniform := rfl

end EntropyBound
