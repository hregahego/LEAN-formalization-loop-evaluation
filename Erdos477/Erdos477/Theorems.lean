import Erdos477.Defs

/-!
# Frozen theorem statements for Erdős Problem 477

The complete list of the 16 frozen statements, all `:= sorry`. Each renders a
claim of `SKETCH.md` faithfully and minimally and carries a stable, binding name.

**This file is FROZEN.** Its SHA-256 is pinned in `scripts/frozen.sha256`; the
proofs live in `Erdos477/Proofs/**`, are re-exposed in `Erdos477/Solution.lean`,
and are bound to these statements by `Erdos477/Discharge.lean`.
-/

namespace Erdos477

open scoped Classical

open MvPolynomial Polynomial

-- ===== Stage A — elementary layer (SKETCH §2) =====

/-- L0.1. -/
theorem zero_mem_Bset : (0 : ℤ) ∈ Bset := sorry

/-- L0.2 — `D` is symmetric. -/
theorem Dset_neg_mem (d : ℤ) (hd : d ∈ Dset) : -d ∈ Dset := sorry

/-- L0.3 — `m ↦ m¹³` is injective on `ℤ`. -/
theorem pow13_inj : Function.Injective (fun m : ℤ => m ^ 13) := sorry

/-- L0.4 — an integer with a rational 13th root is a 13th power. -/
theorem mem_Bset_of_rat_pow13 (c : ℤ) (q : ℚ) (h : q ^ 13 = (c : ℚ)) : c ∈ Bset := sorry

/-- L0.6 — membership reformulation for bad shifts. -/
theorem sub_pow13_mem_Dset_iff (c t : ℤ) : c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset := sorry

-- ===== Stage B — the cofactor bound (SKETCH §4) =====

/-- L1.1 — explicit cofactor bound with `κ = 1/2`. -/
theorem Qcof_ge_half_max_pow12 (u v : ℝ) : (1 / 2) * max |u| |v| ^ 12 ≤ Qcof u v := sorry

/-- L1.2 — gap bound for distinct integer 13th powers. -/
theorem abs_pow13_sub_pow13_ge (u v : ℤ) (h : u ≠ v) :
    (1 / 2) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| := sorry

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
    (d : ℤ) ≤ (Nat.choose (r - 1) 2 : ℤ) * ((projZeroCount (∏ i, A i) : ℤ) - 2) := sorry

/-- Paper Lemma 3.1, the half the development uses: if `N ∉ ℚ¹³` then `X_N` carries
    no nonconstant `ℚ`-rational parametrized curve. SKETCH §5.2.2. -/
theorem no_nonconstant_param_of_not_pow13 (N : ℚ) (hN : N ≠ 0)
    (hpow : ¬ ∃ d : ℚ, d ^ 13 = N) (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ)
    (hA : IsParamOfXN N e A) : IsConstantFamily A := sorry

/-- Paper Corollary 3.2: for `c ∉ B` the affine surface `u¹³ − v¹³ − t¹³ = −c` has no
    nonconstant rational parametrization over `ℚ`. SKETCH §5.2.3. -/
theorem no_rational_param_of_not_mem_Bset (c : ℤ) (hc : c ∉ Bset)
    (f g h : RatFunc ℚ) (hfgh : f ^ 13 - g ^ 13 - h ^ 13 = RatFunc.C (-(c : ℚ))) :
    IsConstRF f ∧ IsConstRF g ∧ IsConstRF h := sorry

/-- L2.1 — the exclusion hypothesis Heath-Brown needs, obtained from Corollary 3.2
    by homogenizing (SKETCH §5.2.3, "derivation of L2.1"). -/
theorem no_linear_param (c : ℤ) (hc : c ∉ Bset) (p₁ p₂ p₃ : Polynomial ℤ)
    (hsum : p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c))
    (h₁ : p₁.natDegree ≤ 1) (h₂ : p₂.natDegree ≤ 1) (h₃ : p₃.natDegree ≤ 1) :
    p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0 := sorry

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
      ((diagSolutions M X).ncard : ℝ) ≤ K * X ^ ((10 : ℝ) / 13) := sorry

-- ===== Stage E — the bad-shift estimate (SKETCH §6) =====

/-- P3.1 = paper's Proposition 4.1: `|S_c(T)| ≤ K_c · T^{5/6}`. -/
theorem badShift_bound (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := sorry

-- ===== Stage F — the greedy tiling criterion (SKETCH §7) =====

/-- L4.1 = paper's Lemma 5.1, for an arbitrary `B ⊆ ℤ`. -/
theorem greedy_tiling (B : Set ℤ)
    (H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ B) →
      ∃ b ∈ B, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ B, ∃ y ∈ B, d = x - y}) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! ab : ℤ × ℤ, ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 + ab.2 = n := sorry

-- ===== Stage G — assembly (SKETCH §8) =====

/-- P5.1 = paper's Proposition 5.2: `B` satisfies the greedy criterion. -/
theorem good_shift_exists (C : Finset ℤ) (hC : ∀ c ∈ C, c ∉ Bset) :
    ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := sorry

/-- **HEADLINE** — Theorem 1.1 / Erdős Problem 477. -/
theorem erdos_477 :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := sorry

end Erdos477
