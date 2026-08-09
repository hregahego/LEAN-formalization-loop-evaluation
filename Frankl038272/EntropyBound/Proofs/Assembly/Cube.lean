/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Proofs.Constants.Basic
import EntropyBound.Proofs.FiniteEntropy.Basic
import EntropyBound.Proofs.IndepCoupling.Basic
import EntropyBound.Proofs.SharedCoupling.Basic
import EntropyBound.Proofs.Scalar.Basic

/-!
# Stage L item L1 — the cube-side headline `frankl_cube` (#60)

This file assembles the whole argument on the Boolean cube (`SKETCH.md` Step 12,
`BLUEPRINT.md` Stage L item L1).  Everything it consumes is already proved elsewhere except
the scalar inequality (#47), which is taken here as an explicit hypothesis `hsc` whose
statement is the frozen statement of `EntropyBound.scalar_inequality` VERBATIM; the frozen
theorem `frankl_cube` is then closed by feeding `EntropyBound.scalar_inequality_proof` to
`EntropyBound.Assembly.frankl_cube_of_scalar`.

The argument: assume every coordinate has frequency `< c = 1196/3125`.  Then `E Sᵢ ≥ 1 - c`
(#53).  Both couplings are supported in `G` (#54, #57), so their entropies are at most
`log |G|` (#50); the `(9/10, 1/10)` mixture of the two coupling floors (#55, #59) is
therefore at most `log |G|`.  Coordinatewise the scalar inequality turns the `i`-th bracket
into `≥ C · E Sᵢ · Hᵢ ≥ C(1-c) Hᵢ`, and summing with the prefix decomposition (#52) gives
`log |G| ≥ C(1-c) log |G|`.  Since `C(1-c) = 1 + 929/156250000 > 1` (#1) and `log |G| ≥ 0`,
we get `|G| = 1`; the singleton then has a `true` coordinate by `hnt`, whose frequency is
`1 > c` — the contradiction.

Support lemmas live in `namespace EntropyBound.Assembly` with the `cu_` prefix.
-/

namespace EntropyBound

namespace Assembly

/-! ### Support lemmas -/

/-- Binary entropy is nonnegative on the unit interval. -/
lemma cu_Hnat_nonneg {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : 0 ≤ Hnat z := by
  have hlz : Real.log z ≤ 0 := Real.log_nonpos h0 h1
  have hlz' : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hA : 0 ≤ -z * Real.log z := by nlinarith
  have hB : 0 ≤ -(1 - z) * Real.log (1 - z) := by nlinarith
  simp only [Hnat]
  linarith

/-- The prefix entropy `Hᵢ` is nonnegative: it averages `Hnat` of probabilities. -/
lemma cu_HiFun_nonneg {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) : 0 ≤ HiFun G i := by
  simp only [HiFun]
  refine Finset.sum_nonneg fun x _ => ?_
  exact mul_nonneg (FiniteEntropy.unifW_nonneg G x)
    (cu_Hnat_nonneg (SharedCoupling.pcond_nonneg G i x) (SharedCoupling.pcond_le_one G i x))

/-! ### The assembly -/

/-- **Stage L item L1.**  The frozen statement of `frankl_cube` (#60), from the frozen
statement of `scalar_inequality` (#47) taken as a hypothesis. -/
theorem frankl_cube_of_scalar
    (hsc : ∀ {ι : Type} [Fintype ι] (w S : ι → ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      (∀ i, S i ∈ Set.Icc (0 : ℝ) 1) →
      Cval * (∑ i, w i * S i) * (∑ i, w i * Hnat (S i))
        ≤ (9 / 10) * (∑ i, ∑ j, w i * w j * Hnat (S i * S j))
          + (Real.log 2 / 10) * (∑ i, w i * (S i * gprof (S i))) ^ 2)
    {n : ℕ} (G : Finset (Fin n → Bool)) (hUC : UnionClosedCube G)
    (hne : G.Nonempty) (hnt : ∃ x ∈ G, x ≠ fun _ => false) :
    ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  -- `hcon : ∀ i, 3125 * |{x ∈ G : xᵢ = true}| < 1196 * |G|`, i.e. every frequency is `< c`.
  have hcardpos : 0 < G.card := Finset.card_pos.mpr hne
  have hcardR : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hcardpos
  -- Step 1 (#53): the assumed frequency bound becomes `E Sᵢ ≥ 1 - c`.
  have hES : ∀ i : Fin n, 1 - cval ≤ ESfun G i := by
    intro i
    have hfreq := freq_eq_one_sub_ES_proof G hne i
    have hN := hcon i
    have hR : (3125 : ℝ) * ((G.filter (fun x => x i = true)).card : ℝ)
        < 1196 * (G.card : ℝ) := by exact_mod_cast hN
    have hlt : ((G.filter (fun x => x i = true)).card : ℝ) / (G.card : ℝ) < cval := by
      rw [div_lt_iff₀ hcardR]
      simp only [cval]
      linarith
    rw [hfreq] at hlt
    linarith
  -- Step 2 (#50 + #54 / #57): both coupling entropies are at most `log |G|`.
  have hind : Hrv (windW G) (fun p => orVec p.1 p.2) ≤ Real.log (G.card : ℝ) :=
    entropy_le_log_card_proof (windW G) (IndepCoupling.windW_nonneg G)
      (IndepCoupling.windW_sum_eq_one G hne) (fun p => orVec p.1 p.2) G
      (indep_support_mem_proof G hUC)
  have hdist := shared_isDist_proof G hne
  have hsh : Hrv (wshW G) (fun p => orVec p.2.1 p.2.2) ≤ Real.log (G.card : ℝ) :=
    entropy_le_log_card_proof (wshW G) hdist.1 hdist.2 (fun p => orVec p.2.1 p.2.2) G
      (shared_support_mem_proof G hne hUC)
  -- Step 3 (#55, #59): the two coupling floors.
  have hfl1 := indep_coupling_bound_proof G hne
  have hfl2 := shared_coupling_bound_proof G hne
  have hTle : (∑ i : Fin n,
      ∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
        ≤ Real.log (G.card : ℝ) := le_trans hfl1 hind
  have hEle : Real.log 2 * (∑ i : Fin n, (Egfun G i) ^ 2) ≤ Real.log (G.card : ℝ) :=
    le_trans hfl2 hsh
  -- Step 4 (#47): the coordinatewise scalar inequality, with `E Sᵢ ≥ 1 - c` folded in.
  have hCpos : (0 : ℝ) < Cval := by simp only [Cval]; norm_num
  have hper : ∀ i : Fin n,
      Cval * (1 - cval) * HiFun G i
        ≤ (9 / 10) * (∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
          + (Real.log 2 / 10) * (Egfun G i) ^ 2 := by
    intro i
    have hkey : Cval * ESfun G i * HiFun G i
        ≤ (9 / 10) * (∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
          + (Real.log 2 / 10) * (Egfun G i) ^ 2 :=
      hsc (unifW G) (pcond G i) (FiniteEntropy.unifW_nonneg G)
        (FiniteEntropy.unifW_sum_eq_one G hne)
        (fun x => ⟨SharedCoupling.pcond_nonneg G i x, SharedCoupling.pcond_le_one G i x⟩)
    have hH := cu_HiFun_nonneg G i
    have hslack : 0 ≤ Cval * (ESfun G i - (1 - cval)) * HiFun G i :=
      mul_nonneg (mul_nonneg hCpos.le (by linarith [hES i])) hH
    nlinarith [hkey, hslack]
  -- Step 5 (#52 + #1): summing over `i` forces `log |G| = 0`.
  have hsum : Cval * (1 - cval) * (∑ i : Fin n, HiFun G i) ≤ Real.log (G.card : ℝ) := by
    calc Cval * (1 - cval) * (∑ i : Fin n, HiFun G i)
        = ∑ i : Fin n, Cval * (1 - cval) * HiFun G i := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin n, ((9 / 10) *
            (∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
            + (Real.log 2 / 10) * (Egfun G i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = (9 / 10) * (∑ i : Fin n,
            ∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y))
            + (Real.log 2 / 10) * (∑ i : Fin n, (Egfun G i) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ Real.log (G.card : ℝ) := by linarith
  rw [prefix_entropy_decomposition_proof G hne] at hsum
  have hA : Cval * (1 - cval) = 1 + 929 / 156250000 := by
    have := strict_margin_proof
    linarith
  rw [hA] at hsum
  have hLnn : 0 ≤ Real.log (G.card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hcardpos)
  have hLzero : Real.log (G.card : ℝ) = 0 := le_antisymm (by linarith) hLnn
  -- Step 6: `|G| = 1`, and the singleton's `true` coordinate has frequency `1 > c`.
  have hcard1 : G.card = 1 := by
    by_contra hne1
    have h2 : 2 ≤ G.card := by omega
    have h2R : (2 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h2
    have hmono : Real.log 2 ≤ Real.log (G.card : ℝ) := Real.log_le_log (by norm_num) h2R
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  obtain ⟨x₀, hx₀G, hx₀ne⟩ := hnt
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx₀ne
  have hitrue : x₀ i = true := by simpa using hi
  have hGeq : G = {x₀} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    rw [ha] at hx₀G ⊢
    rw [Finset.mem_singleton] at hx₀G
    rw [hx₀G]
  have hfilter : (G.filter (fun x => x i = true)).card = 1 := by
    rw [hGeq, Finset.filter_singleton, if_pos hitrue, Finset.card_singleton]
  have hbad := hcon i
  rw [hfilter, hcard1] at hbad
  omega

end Assembly

/-! ### Frozen theorem #60 — the cube-side headline

`EntropyBound.scalar_inequality_proof` (#47) is ✅ in `EntropyBound/Proofs/Scalar/Basic.lean`,
so the hypothesis of `Assembly.frankl_cube_of_scalar` is discharged outright. -/

theorem frankl_cube_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hUC : UnionClosedCube G)
    (hne : G.Nonempty) (hnt : ∃ x ∈ G, x ≠ fun _ => false) :
    ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card :=
  Assembly.frankl_cube_of_scalar EntropyBound.scalar_inequality_proof G hUC hne hnt

namespace Solution

theorem frankl_cube {n : ℕ} (G : Finset (Fin n → Bool)) (hUC : UnionClosedCube G)
    (hne : G.Nonempty) (hnt : ∃ x ∈ G, x ≠ fun _ => false) :
    ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card :=
  EntropyBound.frankl_cube_proof G hUC hne hnt

end Solution

example : @EntropyBound.frankl_cube = @EntropyBound.Solution.frankl_cube := rfl

end EntropyBound
