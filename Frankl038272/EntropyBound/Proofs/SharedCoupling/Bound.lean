/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.SharedCoupling.Marginal
import EntropyBound.Proofs.RankOne.Product
import EntropyBound.Proofs.IndepCoupling.Bound

/-!
# Stage K item K4 — the shared-sign coupling bound (`SKETCH.md` (11c), (11d))

Frozen theorem #59.

The chain rule (#48) plus "conditioning on more reduces entropy" (#49) bound the entropy of
`Z = X̃ ∨ Ỹ` below by `∑ᵢ condHrv` given the pair of prefixes.  Conditioned on the two
prefixes the fresh sign `Uᵢ` is still uniform and independent, so the conditional
zero-probability of the union bit is the sign-average of the product of the two modified
zero-probabilities, i.e. exactly `qker Sᵢ Tᵢ` (`q_sign_average`, #21).  `rank_one_product_bound`
(#27) applied pointwise, and then Cauchy–Schwarz over the sign vector — where `wshW`'s explicit
product formula makes `X̃` and `Ỹ` conditionally i.i.d. — give `(Egfun G i)^2`.
-/

namespace EntropyBound

namespace SharedCoupling

open FiniteEntropy

/-! ### Generic finite-sum plumbing -/

/-- A law-weighted sum is a weight-weighted sum along the random variable. -/
lemma sum_law_mul {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] (w : Ω → ℝ)
    (W : Ω → β) (F : β → ℝ) : ∑ c, law w W c * F c = ∑ p, w p * F (W p) := by
  classical
  simp only [law, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (W p)]
  · rw [if_pos rfl]
  · intro c _ hc
    rw [if_neg (fun h => hc h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Splitting a sum over the cube according to the value of one coordinate. -/
lemma sum_split_coord {n : ℕ} (i : Fin n) (g : (Fin n → Bool) → ℝ) :
    ∑ x, g x = ∑ b : Bool, ∑ x, (if x i = b then g x else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_bool]
  cases hx : x i <;> simp

/-! ### The partial product does not see the later signs -/

lemma chainProd_u_update {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (i : Fin n)
    (b : Bool) (v : Fin n → Bool) :
    chainProd G (Function.update u i b) i.val v = chainProd G u i.val v := by
  simp only [chainProd]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := by
    intro h
    have := (Finset.mem_filter.1 hj).2
    rw [h] at this
    exact absurd this (lt_irrefl i.val)
  rw [Function.update_apply, if_neg hji]

/-! ### Summing the full chain product over the completions of a prefix -/

lemma tailSum {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) :
    ∀ m k : ℕ, k + m = n → ∀ v : Fin n → Bool,
      ∑ x, (if pref k x = pref k v then chainProd G u n x else 0) = chainProd G u k v := by
  intro m
  induction m with
  | zero =>
      intro k hk v
      have hnk : n = k := by omega
      subst hnk
      have hcongr : ∀ x : Fin n → Bool,
          (if pref n x = pref n v then chainProd G u n x else 0)
            = (if x = v then chainProd G u n x else 0) := by
        intro x
        rw [pref_full, pref_full]
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hcongr x)]
      exact Fintype.sum_ite_eq' v (fun x => chainProd G u n x)
  | succ m ih =>
      intro k hk v
      have hkn : k < n := by omega
      have hk' : (k + 1) + m = n := by omega
      set i : Fin n := ⟨k, hkn⟩ with hidef
      have hval : ∀ w : Fin n → Bool, pref (k + 1) w i = w i := by
        intro w
        simp only [pref]
        rw [if_pos (Nat.lt_succ_self k : (i : ℕ) < k + 1)]
      have hkey : ∀ x : Fin n → Bool,
          (if pref k x = pref k v then chainProd G u n x else 0)
            = ∑ b : Bool, (if pref (k + 1) x = pref (k + 1) (Function.update v i b)
                then chainProd G u n x else 0) := by
        intro x
        by_cases hpx : pref k x = pref k v
        · rw [if_pos hpx, Fintype.sum_bool]
          have hone : ∀ b : Bool, (pref (k + 1) x = pref (k + 1) (Function.update v i b))
              ↔ x i = b := by
            intro b
            constructor
            · intro h
              have h1 := congrFun h i
              rw [hval x, hval (Function.update v i b)] at h1
              rw [h1]
              simp
            · intro h
              refine pref_succ_ext i x (Function.update v i b) ?_ ?_
              · rw [h]; simp
              · rw [pref_update_self i v b]; exact hpx
          cases hxi : x i with
          | false =>
              rw [if_neg (by rw [hone]; rw [hxi]; simp),
                if_pos (by rw [hone]; exact hxi)]
              ring
          | true =>
              rw [if_pos (by rw [hone]; exact hxi),
                if_neg (by rw [hone]; rw [hxi]; simp)]
              ring
        · rw [if_neg hpx]
          refine (Finset.sum_eq_zero fun b _ => ?_).symm
          refine if_neg ?_
          intro h
          apply hpx
          have h1 : pref k x = pref k (Function.update v i b) := by
            rw [← pref_pref (Nat.le_succ k) x, h, pref_pref (Nat.le_succ k)]
          rw [h1, pref_update_self i v b]
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hkey x), Finset.sum_comm]
      have hstep : ∀ b : Bool,
          ∑ x, (if pref (k + 1) x = pref (k + 1) (Function.update v i b)
              then chainProd G u n x else 0)
            = kern G i (u i) v b * chainProd G u k v := by
        intro b
        rw [ih (k + 1) hk' (Function.update v i b)]
        have hw : chainProd G u (i.val + 1) (Function.update v i b)
            = kern G i (u i) (Function.update v i b) ((Function.update v i b) i)
              * chainProd G u i.val (Function.update v i b) :=
          chainProd_succ G u i (Function.update v i b)
        have hpv : pref i.val (Function.update v i b) = pref i.val v := pref_update_self i v b
        have hcp : chainProd G u i.val (Function.update v i b) = chainProd G u i.val v :=
          chainProd_congr G u i.val hpv
        have hb : (Function.update v i b) i = b := by simp
        rw [show k + 1 = i.val + 1 from rfl, hw, hb, hcp]
        congr 1
        exact kern_congr G i (u i) (pcond_congr_pref G i hpv) b
      rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hstep b), ← Finset.sum_mul,
        kern_sum_eq_one, one_mul]

/-- The `k`-prefix map only hits `k`-prefix patterns. -/
lemma pref_eq_pattern {n : ℕ} {k : ℕ} {x v : Fin n → Bool} (h : pref k x = v) :
    pref k v = v := by
  rw [← h, pref_pref le_rfl]

/-! ### Halving in the sign vector -/

lemma two_mul_sum_sign {n : ℕ} (i : Fin n) (h : (Fin n → Bool) → ℝ)
    (hinv : ∀ u : Fin n → Bool, h (Function.update u i (!(u i))) = h u) (σ : Bool) :
    2 * ∑ u, (if u i = σ then h u else 0) = ∑ u, h u := by
  classical
  have hflip : ∀ u : Fin n → Bool,
      (2 * (if u i = σ then h u else 0) - h u)
        + (2 * (if (Function.update u i (!(u i))) i = σ
              then h (Function.update u i (!(u i))) else 0)
            - h (Function.update u i (!(u i)))) = 0 := by
    intro u
    have hui : (Function.update u i (!(u i))) i = !(u i) := by simp
    rw [hui, hinv u]
    have hsplit : (if u i = σ then h u else 0) + (if (!(u i)) = σ then h u else 0) = h u := by
      cases hu : u i <;> cases σ <;> simp
    linarith [hsplit]
  have hne : ∀ u : Fin n → Bool,
      (2 * (if u i = σ then h u else 0) - h u) ≠ 0 →
        Function.update u i (!(u i)) ≠ u := by
    intro u _ hc
    have := congrFun hc i
    simp at this
  have hinv2 : ∀ u : Fin n → Bool,
      Function.update (Function.update u i (!(u i))) i
          (!((Function.update u i (!(u i))) i)) = u := by
    intro u
    have h1 : (Function.update u i (!(u i))) i = !(u i) := by simp
    rw [h1]
    funext j
    by_cases hj : j = i <;> simp [hj]
  have hsum : ∑ u, (2 * (if u i = σ then h u else 0) - h u) = 0 :=
    Finset.sum_ninvolution (fun u => Function.update u i (!(u i))) hflip hne
      (fun _ => Finset.mem_univ _) hinv2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith


/-! ### Factorizing a `wshW` double sum -/

lemma sum_wsh_pair {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool)
    (A B : (Fin n → Bool) → Prop) [DecidablePred A] [DecidablePred B] :
    (∑ x, ∑ y, (if A x ∧ B y then wshW G (u, x, y) else 0))
      = (1 / 2 : ℝ) ^ n * ((∑ x, if A x then chainProd G u n x else 0)
          * (∑ y, if B y then chainProd G u n y else 0)) := by
  classical
  have hpoint : ∀ x y : Fin n → Bool,
      (if A x ∧ B y then wshW G (u, x, y) else 0)
        = (1 / 2 : ℝ) ^ n * ((if A x then chainProd G u n x else 0)
            * (if B y then chainProd G u n y else 0)) := by
    intro x y
    simp only [wshW, chainProd_full]
    by_cases h1 : A x <;> by_cases h2 : B y <;> simp [h1, h2]
    ring
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hpoint x y))]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-! ### Summing the chain product over a prefix fibre, with and without the current bit -/

lemma tail_pattern {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (i : Fin n)
    {v : Fin n → Bool} (hv : pref i.val v = v) :
    (∑ x, if pref i.val x = v then chainProd G u n x else 0) = chainProd G u i.val v := by
  have hi := i.isLt
  have h := tailSum G u (n - i.val) i.val (by omega) v
  rw [hv] at h
  exact h

lemma tail_pattern_bit {n : ℕ} (G : Finset (Fin n → Bool)) (u : Fin n → Bool) (i : Fin n)
    {v : Fin n → Bool} (hv : pref i.val v = v) (b : Bool) :
    (∑ x, if x i = b ∧ pref i.val x = v then chainProd G u n x else 0)
      = kern G i (u i) v b * chainProd G u i.val v := by
  classical
  have hi := i.isLt
  have hval : ∀ w : Fin n → Bool, pref (i.val + 1) w i = w i := by
    intro w
    simp only [pref]
    rw [if_pos (Nat.lt_succ_self i.val : (i : ℕ) < i.val + 1)]
  have hpv : pref i.val (Function.update v i b) = pref i.val v := pref_update_self i v b
  have hiff : ∀ x : Fin n → Bool,
      (x i = b ∧ pref i.val x = v)
        ↔ pref (i.val + 1) x = pref (i.val + 1) (Function.update v i b) := by
    intro x
    constructor
    · rintro ⟨hb, hp⟩
      refine pref_succ_ext i x (Function.update v i b) ?_ ?_
      · rw [hb]; simp
      · rw [hpv, hv]; exact hp
    · intro h
      constructor
      · have h1 := congrFun h i
        rw [hval x, hval (Function.update v i b)] at h1
        rw [h1]; simp
      · have h1 : pref i.val x = pref i.val (Function.update v i b) := by
          rw [← pref_pref (Nat.le_succ i.val) x, h, pref_pref (Nat.le_succ i.val)]
        rw [h1, hpv, hv]
  have hcongr : ∀ x : Fin n → Bool,
      (if x i = b ∧ pref i.val x = v then chainProd G u n x else 0)
        = (if pref (i.val + 1) x = pref (i.val + 1) (Function.update v i b)
            then chainProd G u n x else 0) := by
    intro x
    by_cases h : x i = b ∧ pref i.val x = v
    · rw [if_pos h, if_pos ((hiff x).1 h)]
    · rw [if_neg h, if_neg (fun hc => h ((hiff x).2 hc))]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hcongr x)]
  rw [tailSum G u (n - (i.val + 1)) (i.val + 1) (by omega) (Function.update v i b)]
  rw [chainProd_succ G u i (Function.update v i b)]
  have hb : (Function.update v i b) i = b := by simp
  rw [hb, chainProd_congr G u i.val hpv]
  congr 1
  exact kern_congr G i (u i) (pcond_congr_pref G i hpv) b

/-! ### The two laws of the shared coupling at a pair of prefixes -/

lemma law_wsh_zero {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v t : Fin n → Bool)
    (hv : pref i.val v ≠ v) :
    law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) (v, t) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  refine if_neg ?_
  intro h
  exact hv (pref_eq_pattern (congrArg Prod.fst h))

lemma law_wsh_zero' {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v t : Fin n → Bool)
    (ht : pref i.val t ≠ t) :
    law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) (v, t) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  refine if_neg ?_
  intro h
  exact ht (pref_eq_pattern (congrArg Prod.snd h))

lemma law_wsh_pref {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) {v t : Fin n → Bool}
    (hv : pref i.val v = v) (ht : pref i.val t = t) :
    law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) (v, t)
      = ∑ u, (1 / 2 : ℝ) ^ n * (chainProd G u i.val v * chainProd G u i.val t) := by
  classical
  simp only [law]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type]
  have hcongr : ∀ x y : Fin n → Bool,
      (if (pref i.val (u, x, y).2.1, pref i.val (u, x, y).2.2) = (v, t)
          then wshW G (u, x, y) else 0)
        = (if (pref i.val x = v) ∧ (pref i.val y = t) then wshW G (u, x, y) else 0) := by
    intro x y
    simp only [Prod.mk.injEq]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hcongr x y))]
  rw [sum_wsh_pair G u (fun x => pref i.val x = v) (fun y => pref i.val y = t)]
  rw [tail_pattern G u i hv, tail_pattern G u i ht]

lemma law_wsh_false {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) {v t : Fin n → Bool}
    (hv : pref i.val v = v) (ht : pref i.val t = t) :
    law (wshW G)
        (fun p => ((orVec p.2.1 p.2.2) i, (pref i.val p.2.1, pref i.val p.2.2))) (false, (v, t))
      = ∑ u, (1 / 2 : ℝ) ^ n * ((kern G i (u i) v false * chainProd G u i.val v)
          * (kern G i (u i) t false * chainProd G u i.val t)) := by
  classical
  simp only [law]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type]
  have hcongr : ∀ x y : Fin n → Bool,
      (if ((orVec (u, x, y).2.1 (u, x, y).2.2) i,
            (pref i.val (u, x, y).2.1, pref i.val (u, x, y).2.2)) = (false, (v, t))
          then wshW G (u, x, y) else 0)
        = (if ((x i = false) ∧ (pref i.val x = v)) ∧ ((y i = false) ∧ (pref i.val y = t))
            then wshW G (u, x, y) else 0) := by
    intro x y
    simp only [orVec, Prod.mk.injEq]
    by_cases h1 : x i = false <;> by_cases h2 : y i = false <;>
      by_cases h3 : pref i.val x = v <;> by_cases h4 : pref i.val y = t <;>
      simp [h1, h2, h3, h4]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hcongr x y))]
  rw [sum_wsh_pair G u (fun x => (x i = false) ∧ (pref i.val x = v))
    (fun y => (y i = false) ∧ (pref i.val y = t))]
  rw [tail_pattern_bit G u i hv false, tail_pattern_bit G u i ht false]

/-! ### The sign average: the conditional zero-probability is `qker` -/

lemma law_wsh_false_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v t : Fin n → Bool) :
    law (wshW G)
        (fun p => ((orVec p.2.1 p.2.2) i, (pref i.val p.2.1, pref i.val p.2.2))) (false, (v, t))
      = law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) (v, t)
        * qker (pcondV G i v) (pcondV G i t) := by
  classical
  by_cases hv : pref i.val v = v
  · by_cases ht : pref i.val t = t
    · -- both are genuine prefix patterns
      set s : ℝ := pcondV G i v with hs
      set r : ℝ := pcondV G i t with hr
      have hsv : pcond G i v = s := by rw [hs, pcond_eq_pcondV, hv]
      have hrt : pcond G i t = r := by rw [hr, pcond_eq_pcondV, ht]
      set h : (Fin n → Bool) → ℝ :=
        fun u => (1 / 2 : ℝ) ^ n * (chainProd G u i.val v * chainProd G u i.val t) with hh
      have hinv : ∀ u : Fin n → Bool, h (Function.update u i (!(u i))) = h u := by
        intro u
        rw [hh]
        simp only
        rw [chainProd_u_update G u i (!(u i)) v, chainProd_u_update G u i (!(u i)) t]
      set f : Bool → ℝ := fun σ => kern G i σ v false * kern G i σ t false with hf
      have hLHS : law (wshW G)
          (fun p => ((orVec p.2.1 p.2.2) i, (pref i.val p.2.1, pref i.val p.2.2)))
            (false, (v, t)) = ∑ u, f (u i) * h u := by
        rw [law_wsh_false G i hv ht]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hf, hh]
        ring
      have hsplit : ∑ u, f (u i) * h u = ∑ σ : Bool, f σ * ∑ u, (if u i = σ then h u else 0) := by
        rw [sum_split_coord i (fun u => f (u i) * h u)]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hu : u i = σ
        · rw [if_pos hu, if_pos hu, hu]
        · rw [if_neg hu, if_neg hu, mul_zero]
      have hhalf : ∀ σ : Bool, ∑ u, (if u i = σ then h u else 0) = (1 / 2 : ℝ) * ∑ u, h u := by
        intro σ
        have := two_mul_sum_sign i h hinv σ
        linarith
      rw [hLHS, hsplit]
      rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => by rw [hhalf σ])]
      rw [← Finset.sum_mul, law_wsh_pref G i hv ht]
      have hHsum : ∑ u, h u
          = ∑ u, (1 / 2 : ℝ) ^ n * (chainProd G u i.val v * chainProd G u i.val t) := by
        rw [hh]
      rw [← hHsum]
      have hqs := q_sign_average_proof s r
      rw [Fintype.sum_bool] at *
      rw [hf]
      simp only
      rw [kern_false, kern_false, kern_false, kern_false,
        pmod_true G i v, pmod_false G i v, pmod_true G i t, pmod_false G i t,
        hsv, hrt, hqs]
      ring
    · rw [law_wsh_zero' G i v t ht, zero_mul]
      refine Finset.sum_eq_zero fun p _ => ?_
      refine if_neg ?_
      intro hc
      exact ht (pref_eq_pattern (congrArg Prod.snd (congrArg Prod.snd hc)))
  · rw [law_wsh_zero G i v t hv, zero_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    refine if_neg ?_
    intro hc
    exact hv (pref_eq_pattern (congrArg Prod.fst (congrArg Prod.snd hc)))


/-! ### The conditional entropy given both prefixes -/

/-- `S g(S)` as a function of a full vector, resp. of a prefix pattern. -/
noncomputable def gterm {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (x : Fin n → Bool) : ℝ :=
  pcond G i x * gprof (pcond G i x)

noncomputable def gtermV {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) : ℝ :=
  pcondV G i v * gprof (pcondV G i v)

lemma gterm_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (x : Fin n → Bool) :
    gterm G i x = gtermV G i (pref i.val x) := by
  simp only [gterm, gtermV, pcond_eq_pcondV]

lemma condHrv_shared_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) :
    condHrv (wshW G) (fun p => (orVec p.2.1 p.2.2) i)
        (fun p => (pref i.val p.2.1, pref i.val p.2.2))
      = ∑ c : (Fin n → Bool) × (Fin n → Bool),
          law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) c
            * Hnat (qker (pcondV G i c.1) (pcondV G i c.2)) := by
  classical
  set w := wshW G with hw
  set W : ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) →
      ((Fin n → Bool) × (Fin n → Bool)) :=
    fun p => (pref i.val p.2.1, pref i.val p.2.2) with hW
  set Q : Bool → ((Fin n → Bool) × (Fin n → Bool)) → ℝ :=
    fun b c => law w (fun p => ((orVec p.2.1 p.2.2) i, W p)) (b, c) with hQ
  have hQnn : ∀ b c, 0 ≤ Q b c := fun b c => law_nonneg (wshW_nonneg G) _ _
  have hlawW : ∀ c, law w W c = Q false c + Q true c := by
    intro c
    rw [← law_pair_sum w (fun p => (orVec p.2.1 p.2.2) i) W c, Fintype.sum_bool, hQ]
    ring
  have hcond : condHrv w (fun p => (orVec p.2.1 p.2.2) i) W
      = ∑ c : (Fin n → Bool) × (Fin n → Bool),
          ((-(Q false c) * Real.log (Q false c)) + (-(Q true c) * Real.log (Q true c))
            - (-(Q false c + Q true c) * Real.log (Q false c + Q true c))) := by
    rw [condHrv, Hrv_pair_eq]
    simp only [Hrv, entropyW]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hlawW c, Fintype.sum_bool, hQ]
    ring
  have hterm : ∀ c : (Fin n → Bool) × (Fin n → Bool),
      ((-(Q false c) * Real.log (Q false c)) + (-(Q true c) * Real.log (Q true c))
          - (-(Q false c + Q true c) * Real.log (Q false c + Q true c)))
        = law w W c * Hnat (qker (pcondV G i c.1) (pcondV G i c.2)) := by
    intro c
    obtain ⟨v, t⟩ := c
    rw [split_entropy (Q false (v, t)) (Q true (v, t)) (hQnn false (v, t)) (hQnn true (v, t)),
      ← hlawW (v, t)]
    rcases eq_or_lt_of_le (law_nonneg (wshW_nonneg G) W (v, t)) with h0 | hpos
    · rw [← h0]
      simp
    · have hne : law w W (v, t) ≠ 0 := ne_of_gt hpos
      have hfalse : Q false (v, t)
          = law w W (v, t) * qker (pcondV G i v) (pcondV G i t) := by
        rw [hQ, hW, hw]
        exact law_wsh_false_eq G i v t
      congr 1
      rw [hfalse]
      field_simp
  rw [hcond, Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => hterm c)]

lemma condHrv_shared_ge {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) :
    Real.log 2 * (∑ p, wshW G p * (gterm G i p.2.1 * gterm G i p.2.2))
      ≤ condHrv (wshW G) (fun p => (orVec p.2.1 p.2.2) i)
          (fun p => (pref i.val p.2.1, pref i.val p.2.2)) := by
  classical
  rw [condHrv_shared_eq]
  have hL : (∑ p, wshW G p * (gterm G i p.2.1 * gterm G i p.2.2))
      = ∑ c : (Fin n → Bool) × (Fin n → Bool),
          law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) c
            * (gtermV G i c.1 * gtermV G i c.2) := by
    rw [sum_law_mul (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2))
      (fun c => gtermV G i c.1 * gtermV G i c.2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [gterm_eq, gterm_eq]
  rw [hL, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hnn : 0 ≤ law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) c :=
    law_nonneg (wshW_nonneg G) _ _
  have hs : pcondV G i c.1 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pcondV_nonneg G i c.1, pcondV_le_one G i c.1⟩
  have ht : pcondV G i c.2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pcondV_nonneg G i c.2, pcondV_le_one G i c.2⟩
  have h27 := rank_one_product_bound_proof (pcondV G i c.1) hs (pcondV G i c.2) ht
  have hrw : Real.log 2 * (law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) c
      * (gtermV G i c.1 * gtermV G i c.2))
      = law (wshW G) (fun p => (pref i.val p.2.1, pref i.val p.2.2)) c
        * (Real.log 2 * (pcondV G i c.1 * pcondV G i c.2
            * gprof (pcondV G i c.1) * gprof (pcondV G i c.2))) := by
    simp only [gtermV]
    ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left h27 hnn

/-! ### Conditional i.i.d. structure and Cauchy–Schwarz -/

lemma sum_wsh_gterm_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) :
    (∑ p, wshW G p * (gterm G i p.2.1 * gterm G i p.2.2))
      = ∑ u, (1 / 2 : ℝ) ^ n * (∑ x, chainProd G u n x * gterm G i x) ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type]
  have hpoint : ∀ x y : Fin n → Bool,
      wshW G (u, x, y) * (gterm G i x * gterm G i y)
        = (1 / 2 : ℝ) ^ n * ((chainProd G u n x * gterm G i x)
            * (chainProd G u n y * gterm G i y)) := by
    intro x y
    simp only [wshW, chainProd_full]
    ring
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hpoint x y))]
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

lemma sum_wsh_M_eq {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) (i : Fin n) :
    (∑ u, (1 / 2 : ℝ) ^ n * (∑ x, chainProd G u n x * gterm G i x)) = Egfun G i := by
  classical
  have hmarg : ∀ x : Fin n → Bool, (∑ u, (1 / 2 : ℝ) ^ n * chainProd G u n x) = unifW G x := by
    intro x
    rw [← shared_marginal_uniform_proof G hG x]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sum_y_wshW G u x, chainProd_full]
  have hstep : (∑ u, (1 / 2 : ℝ) ^ n * (∑ x, chainProd G u n x * gterm G i x))
      = ∑ x, (∑ u, (1 / 2 : ℝ) ^ n * chainProd G u n x) * gterm G i x := by
    have h1 : ∀ u : Fin n → Bool,
        (1 / 2 : ℝ) ^ n * (∑ x, chainProd G u n x * gterm G i x)
          = ∑ x, (1 / 2 : ℝ) ^ n * chainProd G u n x * gterm G i x := by
      intro u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => h1 u), Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
  rw [hstep, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => by rw [hmarg x])]
  simp only [Egfun, gterm]

/-- **`E[W²] ≥ (E W)²`** along the sign vector: since `wshW` factorizes given the signs, the
two chains are conditionally i.i.d., so the expectation of the product is the mean square. -/
lemma cauchy_step {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) (i : Fin n) :
    (Egfun G i) ^ 2 ≤ ∑ p, wshW G p * (gterm G i p.2.1 * gterm G i p.2.2) := by
  classical
  rw [sum_wsh_gterm_eq]
  set M : (Fin n → Bool) → ℝ := fun u => ∑ x, chainProd G u n x * gterm G i x with hM
  set c : ℝ := Egfun G i with hc
  have hpi : (∑ _u : (Fin n → Bool), (1 / 2 : ℝ) ^ n) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp
  have hmean : (∑ u, (1 / 2 : ℝ) ^ n * M u) = c := sum_wsh_M_eq G hG i
  have hnonneg : 0 ≤ ∑ u, (1 / 2 : ℝ) ^ n * (M u - c) ^ 2 :=
    Finset.sum_nonneg fun u _ => mul_nonneg (by positivity) (sq_nonneg _)
  have hexp : (∑ u, (1 / 2 : ℝ) ^ n * (M u - c) ^ 2)
      = (∑ u, (1 / 2 : ℝ) ^ n * (M u) ^ 2)
        - 2 * c * (∑ u, (1 / 2 : ℝ) ^ n * M u)
        + c ^ 2 * (∑ _u : (Fin n → Bool), (1 / 2 : ℝ) ^ n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hexp, hmean, hpi] at hnonneg
  nlinarith [hnonneg]

end SharedCoupling

/-! ### Frozen theorem #59 — the shared-sign coupling bound -/

theorem shared_coupling_bound_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    Real.log 2 * (∑ i : Fin n, (Egfun G i) ^ 2)
      ≤ Hrv (wshW G) (fun p => orVec p.2.1 p.2.2) := by
  classical
  have hnn := SharedCoupling.wshW_nonneg G
  have hsum := SharedCoupling.wshW_sum_eq_one G
  rw [entropy_chain_rule_proof (wshW G) hnn hsum (fun p => orVec p.2.1 p.2.2), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hcomp := condHrv_le_of_comp_proof (wshW G) hnn hsum
    (fun p => (orVec p.2.1 p.2.2) i) (fun p => (pref i.val p.2.1, pref i.val p.2.2))
    (fun q : (Fin n → Bool) × (Fin n → Bool) => orVec q.1 q.2)
  have hfun : (fun p : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
      orVec (pref i.val p.2.1) (pref i.val p.2.2))
      = fun p : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
          pref i.val (orVec p.2.1 p.2.2) := by
    funext p
    rw [IndepCoupling.pref_orVec]
  simp only at hcomp
  rw [hfun] at hcomp
  refine le_trans ?_ hcomp
  refine le_trans ?_ (SharedCoupling.condHrv_shared_ge G i)
  exact mul_le_mul_of_nonneg_left (SharedCoupling.cauchy_step G hG i)
    (le_of_lt (Real.log_pos (by norm_num)))

namespace Solution

theorem shared_coupling_bound {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    Real.log 2 * (∑ i : Fin n, (Egfun G i) ^ 2)
      ≤ Hrv (wshW G) (fun p => orVec p.2.1 p.2.2) :=
  EntropyBound.shared_coupling_bound_proof G hG

end Solution

example : @EntropyBound.shared_coupling_bound = @EntropyBound.Solution.shared_coupling_bound := rfl

end EntropyBound
