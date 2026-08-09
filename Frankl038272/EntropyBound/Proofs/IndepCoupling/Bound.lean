/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.FiniteEntropy.Core
import EntropyBound.Proofs.FiniteEntropy.Chain

/-!
# Stage J item J2 — the independent coupling bound (`SKETCH.md` Step 10)

Frozen theorem #55.  The chain rule (#48) applied to the union vector `Z = X' ∨ Y'` under the
product weight `windW G`, followed by "conditioning on more reduces entropy" (#49) with the
pair of prefixes as the finer conditioning, and finally the exact evaluation of the resulting
conditional entropy.

The load-bearing step is the last one: given both prefixes, the two bits are independent
(the weight is a product), and the union bit is `false` **iff both** bits are `false`, so its
conditional zero-probability is the *product* `pcond G i x * pcond G i y`.

Support lemmas live in `namespace EntropyBound.IndepCoupling`.
-/

namespace EntropyBound

namespace IndepCoupling

open FiniteEntropy

/-! ### The product weight is a distribution -/

/-- A sum over the product cube of a product of one-variable functions factorizes. -/
lemma sum_prod_mul {n : ℕ} (F H : (Fin n → Bool) → ℝ) :
    ∑ p : (Fin n → Bool) × (Fin n → Bool), F p.1 * H p.2 = (∑ x, F x) * (∑ y, H y) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

lemma windW_nonneg {n : ℕ} (G : Finset (Fin n → Bool))
    (p : (Fin n → Bool) × (Fin n → Bool)) : 0 ≤ windW G p :=
  mul_nonneg (unifW_nonneg G _) (unifW_nonneg G _)

lemma windW_sum_eq_one {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∑ p, windW G p = 1 := by
  have h : ∑ p : (Fin n → Bool) × (Fin n → Bool), windW G p
      = (∑ x, unifW G x) * (∑ y, unifW G y) := sum_prod_mul (unifW G) (unifW G)
  rw [h, unifW_sum_eq_one G hG, one_mul]

/-! ### The `pref` / `orVec` commutation lemma -/

/-- Masking commutes with the coordinatewise union: this is what makes #49 applicable. -/
lemma pref_orVec {n : ℕ} (k : ℕ) (x y : Fin n → Bool) :
    pref k (orVec x y) = orVec (pref k x) (pref k y) := by
  funext j
  simp only [pref, orVec]
  by_cases h : (j : ℕ) < k <;> simp [h]

/-! ### Laws under the product weight factorize -/

lemma law_windW_prod {n : ℕ} {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (G : Finset (Fin n → Bool)) (F : (Fin n → Bool) → β) (H : (Fin n → Bool) → γ)
    (a : β) (b : γ) :
    law (windW G) (fun p => (F p.1, H p.2)) (a, b)
      = law (unifW G) F a * law (unifW G) H b := by
  simp only [law]
  rw [← sum_prod_mul (fun x => if F x = a then unifW G x else 0)
      (fun y => if H y = b then unifW G y else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [windW, Prod.mk.injEq]
  by_cases h1 : F p.1 = a <;> by_cases h2 : H p.2 = b <;> simp [h1, h2]

/-- The joint law of the union bit and the pair of prefixes, at the value `false`, is the
product of the two one-chain "bit `false`, prefix `v`" laws — the union bit is `false` iff
*both* bits are. -/
lemma law_windW_false {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v u : Fin n → Bool) :
    law (windW G) (fun p => ((orVec p.1 p.2) i, (pref i.val p.1, pref i.val p.2)))
        (false, (v, u))
      = law (unifW G) (fun x => (x i, pref i.val x)) (false, v)
        * law (unifW G) (fun x => (x i, pref i.val x)) (false, u) := by
  simp only [law]
  rw [← sum_prod_mul (fun x => if (x i, pref i.val x) = (false, v) then unifW G x else 0)
      (fun y => if (y i, pref i.val y) = (false, u) then unifW G y else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [windW, orVec, Prod.mk.injEq]
  by_cases h1 : p.1 i = false <;> by_cases h2 : p.2 i = false <;>
    by_cases h3 : pref i.val p.1 = v <;> by_cases h4 : pref i.val p.2 = u <;>
    simp [h1, h2, h3, h4]

/-- The "bit `false`, prefix `v`" law is the prefix law times the conditional probability. -/
lemma law_false_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) :
    law (unifW G) (fun x => (x i, pref i.val x)) (false, v)
      = law (unifW G) (fun x => pref i.val x) v * pcondV G i v := by
  rw [law_pair_false_eq, law_pref_eq, div_mul_eq_mul_div, card_mul_pcondV]

/-! ### Fiberwise regrouping along the prefix map -/

lemma sum_unifW_fiberwise {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n)
    (F : (Fin n → Bool) → ℝ) :
    ∑ x, unifW G x * F (pref i.val x)
      = ∑ v, law (unifW G) (fun x => pref i.val x) v * F v := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n → Bool)) (fun x => pref i.val x)
    (fun x => unifW G x * F (pref i.val x))]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hval : ∀ x ∈ Finset.univ.filter (fun x => pref i.val x = v),
      unifW G x * F (pref i.val x) = unifW G x * F v := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
  congr 1
  simp only [law]
  rw [Finset.sum_filter]

end IndepCoupling

/-! ### The conditional entropy of the union bit given both prefixes -/

namespace IndepCoupling

open FiniteEntropy

/-- The exact evaluation of the conditional entropy appearing in #55. -/
lemma condHrv_indep_eq {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) :
    condHrv (windW G) (fun p => (orVec p.1 p.2) i)
        (fun p => (pref i.val p.1, pref i.val p.2))
      = ∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y) := by
  classical
  set w := windW G with hw
  set L : (Fin n → Bool) → ℝ := fun v => law (unifW G) (fun x => pref i.val x) v with hL
  set Q : Bool → ((Fin n → Bool) × (Fin n → Bool)) → ℝ :=
    fun b c => law w (fun p => ((orVec p.1 p.2) i, (pref i.val p.1, pref i.val p.2))) (b, c)
    with hQ
  have hQnn : ∀ b c, 0 ≤ Q b c := fun b c =>
    law_nonneg (windW_nonneg G) _ _
  have hlawW : ∀ c : (Fin n → Bool) × (Fin n → Bool),
      law w (fun p => (pref i.val p.1, pref i.val p.2)) c = Q false c + Q true c := by
    intro c
    rw [← law_pair_sum w (fun p => (orVec p.1 p.2) i)
      (fun p => (pref i.val p.1, pref i.val p.2)) c]
    rw [Fintype.sum_bool]
    rw [hQ]
    ring
  -- the conditional entropy, expanded as a sum over pairs of prefix patterns
  have hcond : condHrv w (fun p => (orVec p.1 p.2) i)
        (fun p => (pref i.val p.1, pref i.val p.2))
      = ∑ c : (Fin n → Bool) × (Fin n → Bool),
          ((-(Q false c) * Real.log (Q false c)) + (-(Q true c) * Real.log (Q true c))
            - (-(Q false c + Q true c) * Real.log (Q false c + Q true c))) := by
    rw [condHrv, Hrv_pair_eq]
    simp only [Hrv, entropyW]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hlawW c, Fintype.sum_bool]
    rw [hQ]
    ring
  -- each summand is the prefix-pair probability times `Hnat` of the *product*
  have hterm : ∀ c : (Fin n → Bool) × (Fin n → Bool),
      ((-(Q false c) * Real.log (Q false c)) + (-(Q true c) * Real.log (Q true c))
          - (-(Q false c + Q true c) * Real.log (Q false c + Q true c)))
        = L c.1 * L c.2 * Hnat (pcondV G i c.1 * pcondV G i c.2) := by
    intro c
    obtain ⟨v, u⟩ := c
    have hprod : law w (fun p => (pref i.val p.1, pref i.val p.2)) (v, u) = L v * L u := by
      rw [hw, hL]
      exact law_windW_prod G (fun x => pref i.val x) (fun x => pref i.val x) v u
    have hfalse : Q false (v, u) = (L v * pcondV G i v) * (L u * pcondV G i u) := by
      rw [hQ]
      simp only
      rw [hw, law_windW_false G i v u, law_false_eq, law_false_eq, hL]
    rw [split_entropy (Q false (v, u)) (Q true (v, u)) (hQnn false (v, u)) (hQnn true (v, u)),
      ← hlawW (v, u), hprod]
    rcases eq_or_lt_of_le (mul_nonneg (law_nonneg (unifW_nonneg G) _ v)
      (law_nonneg (unifW_nonneg G) _ u) : (0:ℝ) ≤ L v * L u) with h0 | hpos
    · rw [← h0]
      simp
    · have hLv : L v ≠ 0 := fun h => by rw [h, zero_mul] at hpos; exact lt_irrefl 0 hpos
      have hLu : L u ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl 0 hpos
      have harg : Q false (v, u) / (L v * L u) = pcondV G i v * pcondV G i u := by
        rw [hfalse]
        field_simp
      rw [harg]
  rw [hcond, Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => hterm c)]
  -- regroup the right-hand side fiberwise, twice
  rw [Fintype.sum_prod_type]
  have hRHS : ∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y)
      = ∑ v, L v * (∑ u, L u * Hnat (pcondV G i v * pcondV G i u)) := by
    have hinner : ∀ x : Fin n → Bool,
        ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y)
          = unifW G x * (∑ u, L u * Hnat (pcondV G i (pref i.val x) * pcondV G i u)) := by
      intro x
      rw [← sum_unifW_fiberwise G i
        (fun u => Hnat (pcondV G i (pref i.val x) * pcondV G i u)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [pcond_eq_pcondV, pcond_eq_pcondV]
      ring
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hinner x)]
    exact sum_unifW_fiberwise G i
      (fun v => ∑ u, L u * Hnat (pcondV G i v * pcondV G i u))
  rw [hRHS]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

end IndepCoupling

/-! ### Frozen theorem #55 — the independent coupling bound -/

theorem indep_coupling_bound_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∑ i : Fin n, (∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
      ≤ Hrv (windW G) (fun p => orVec p.1 p.2) := by
  classical
  have hnn := IndepCoupling.windW_nonneg G
  have hsum := IndepCoupling.windW_sum_eq_one G hG
  rw [entropy_chain_rule_proof (windW G) hnn hsum (fun p => orVec p.1 p.2)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← IndepCoupling.condHrv_indep_eq G i]
  have hcomp := condHrv_le_of_comp_proof (windW G) hnn hsum
    (fun p => (orVec p.1 p.2) i) (fun p => (pref i.val p.1, pref i.val p.2))
    (fun q : (Fin n → Bool) × (Fin n → Bool) => orVec q.1 q.2)
  have hfun : (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      orVec (pref i.val p.1) (pref i.val p.2))
      = fun p : (Fin n → Bool) × (Fin n → Bool) => pref i.val (orVec p.1 p.2) := by
    funext p
    rw [IndepCoupling.pref_orVec]
  simp only at hcomp
  rw [hfun] at hcomp
  exact hcomp

namespace Solution

theorem indep_coupling_bound {n : ℕ} (G : Finset (Fin n → Bool)) (hG : G.Nonempty) :
    ∑ i : Fin n, (∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
      ≤ Hrv (windW G) (fun p => orVec p.1 p.2) :=
  EntropyBound.indep_coupling_bound_proof G hG

end Solution

example : @EntropyBound.indep_coupling_bound = @EntropyBound.Solution.indep_coupling_bound := rfl

end EntropyBound
