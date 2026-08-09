import Erdos477.Theorems
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic
import Erdos477.Proofs.FunctionField.Basic
import Erdos477.Proofs.FunctionField.BMForms
import Erdos477.Proofs.FunctionField.Lemma31
import Erdos477.Proofs.FunctionField.Corollary32
import Erdos477.Proofs.FunctionField.Linear
import Erdos477.Proofs.HeathBrown.Basic
import Erdos477.Proofs.BadShift.Basic
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.Assembly.Basic

/-!
# Solution — the frozen theorems, restated and proved

Once a frozen theorem of `Erdos477/Theorems.lean` has a sorry-free proof
`<name>_proof` in `Erdos477/Proofs/**`, restate it here **verbatim** in
`namespace Erdos477.Solution` as

```
theorem <name> : <the frozen statement> := <name>_proof
```

`scripts/verify.py` checks `#print axioms Erdos477.Solution.<name>` for every
frozen name, and that `Erdos477.Solution.erdos_477` genuinely depends on both
assumed certificates.

Restated here — **all sixteen** frozen statements, each with a sorry-free proof:
Stage A's `zero_mem_Bset`, `Dset_neg_mem`, `pow13_inj`, `mem_Bset_of_rat_pow13`,
`sub_pow13_mem_Dset_iff`; Stage B's `Qcof_ge_half_max_pow12`,
`abs_pow13_sub_pow13_ge`; Stage C's `bm_forms_height_bound`,
`no_nonconstant_param_of_not_pow13`, `no_rational_param_of_not_mem_Bset`,
`no_linear_param`; Stage D's `hb_diagonal_count`; Stage E's `badShift_bound`;
Stage F's `greedy_tiling`; and Stage G's `good_shift_exists` and the headline
`erdos_477`.

Nothing is absent any more, so `scripts/verify.py` checks 4 and 5 cover the
whole list, and check 4b sees `Erdos477.Solution.erdos_477` depend on both
assumed certificates — `Erdos477.brownawell_masser_P1_four_term` through
`no_linear_param` ► Corollary 3.2 ► Lemma 3.1 ► `bm_forms_height_bound`, and
`Erdos477.heath_brown_diagonal_13` through `badShift_bound` ►
`hb_diagonal_count`.
-/

namespace Erdos477

namespace Solution

-- ===== Stage A — elementary layer (SKETCH §2) =====

/-- L0.1. -/
theorem zero_mem_Bset : (0 : ℤ) ∈ Bset := Erdos477.zero_mem_Bset_proof

/-- L0.2 — `D` is symmetric. -/
theorem Dset_neg_mem (d : ℤ) (hd : d ∈ Dset) : -d ∈ Dset := Erdos477.Dset_neg_mem_proof d hd

/-- L0.3 — `m ↦ m¹³` is injective on `ℤ`. -/
theorem pow13_inj : Function.Injective (fun m : ℤ => m ^ 13) := Erdos477.pow13_inj_proof

/-- L0.4 — an integer with a rational 13th root is a 13th power. -/
theorem mem_Bset_of_rat_pow13 (c : ℤ) (q : ℚ) (h : q ^ 13 = (c : ℚ)) : c ∈ Bset :=
  Erdos477.mem_Bset_of_rat_pow13_proof c q h

/-- L0.6 — membership reformulation for bad shifts. -/
theorem sub_pow13_mem_Dset_iff (c t : ℤ) : c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset :=
  Erdos477.sub_pow13_mem_Dset_iff_proof c t

-- ===== Stage B — the cofactor bound (SKETCH §4) =====

/-- L1.1 — explicit cofactor bound with `κ = 1/2`. -/
theorem Qcof_ge_half_max_pow12 (u v : ℝ) : (1 / 2) * max |u| |v| ^ 12 ≤ Qcof u v :=
  Erdos477.Qcof_ge_half_max_pow12_proof u v

/-- L1.2 — gap bound for distinct integer 13th powers. -/
theorem abs_pow13_sub_pow13_ge (u v : ℤ) (h : u ≠ v) :
    (1 / 2) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| :=
  Erdos477.abs_pow13_sub_pow13_ge_proof u v h

-- ===== Stage C — function-field exclusion, Route A (SKETCH §5.2) =====

/-- Brownawell–Masser for homogeneous binary forms, **derived** from
    `brownawell_masser_P1_four_term` via the height computation of SKETCH §5.2.1
    (`H(A₁ : ⋯ : A_r) = d` for common-degree-`d` forms with no common zero).
    Instantiated at `r = 4` (Case A) and `r = 3` (Case B) inside Lemma 3.1. -/
theorem bm_forms_height_bound {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (r d : ℕ) (hr : 3 ≤ r) (A : Fin r → MvPolynomial (Fin 2) k)
    (hA0 : ∀ i, A i ≠ 0) (hhom : ∀ i, (A i).IsHomogeneous d)
    (hcop : NoCommonProjZero A) (hsum : ∑ i, A i = 0)
    (hsub : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, A i ≠ 0)
    (hnc : ¬ IsConstantFamily A) :
    (d : ℤ) ≤ (Nat.choose (r - 1) 2 : ℤ) * ((projZeroCount (∏ i, A i) : ℤ) - 2) :=
  Erdos477.bm_forms_height_bound_proof r d hr A hA0 hhom hcop hsum hsub hnc

/-- Paper Lemma 3.1, the half the development uses: if `N ∉ ℚ¹³` then `X_N` carries
    no nonconstant `ℚ`-rational parametrized curve. SKETCH §5.2.2. -/
theorem no_nonconstant_param_of_not_pow13 (N : ℚ) (hN : N ≠ 0)
    (hpow : ¬ ∃ d : ℚ, d ^ 13 = N) (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ)
    (hA : IsParamOfXN N e A) : IsConstantFamily A :=
  Erdos477.no_nonconstant_param_of_not_pow13_proof N hN hpow e A hA

/-- Paper Corollary 3.2: for `c ∉ B` the affine surface `u¹³ − v¹³ − t¹³ = −c` has no
    nonconstant rational parametrization over `ℚ`. SKETCH §5.2.3. -/
theorem no_rational_param_of_not_mem_Bset (c : ℤ) (hc : c ∉ Bset)
    (f g h : RatFunc ℚ) (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h :=
  Erdos477.no_rational_param_of_not_mem_Bset_proof c hc f g h hfgh

/-- L2.1 — the exclusion hypothesis Heath-Brown needs, obtained from Corollary 3.2
    by homogenizing (SKETCH §5.2.3, "derivation of L2.1"). -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) (p₁ p₂ p₃ : Polynomial ℤ)
    (hsum : p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c))
    (h₁ : p₁.natDegree ≤ 1) (h₂ : p₂.natDegree ≤ 1) (h₃ : p₃.natDegree ≤ 1) :
    p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 :=
  Erdos477.no_linear_param_proof c hc p₁ p₂ p₃ hsum h₁ h₂ h₃

-- ===== Stage D — the Heath-Brown bridge (SKETCH §3, now a THEOREM) =====

/-- The sketch's "AXIOM HB" is **proved** here from the general
    `heath_brown_diagonal_13` (`USER_NOTES.md`: the specialization is a proof
    obligation, not an assumption). SKETCH §3, points 1–4. -/
theorem hb_diagonal_count (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ((diagSolutions M X).ncard : ℝ) ≤ K * X ^ ((10 : ℝ) / 13) :=
  Erdos477.hb_diagonal_count_proof M hM hexcl

-- ===== Stage E — the bad-shift estimate (SKETCH §6) =====

/-- P3.1 = paper's Proposition 4.1: `|S_c(T)| ≤ K_c · T^{5/6}`. -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) :=
  Erdos477.badShift_bound_proof c hc

-- ===== Stage F — the greedy tiling criterion (SKETCH §7) =====

/-- L4.1 = paper's Lemma 5.1, for an arbitrary `B ⊆ ℤ`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
      ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n :=
  Erdos477.greedy_tiling_proof B H

-- ===== Stage G — assembly (SKETCH §8) =====

/-- P5.1 = paper's Proposition 5.2: `B` satisfies the greedy criterion. -/
theorem good_shift_exists (C : Finset ℤ) (hC : ∀ c ∈ C, c ∉ Bset) :
    ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset :=
  Erdos477.good_shift_exists_proof C hC

/-- **HEADLINE** — Theorem 1.1 / Erdős Problem 477. -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  Erdos477.erdos_477_proof

end Solution

end Erdos477
