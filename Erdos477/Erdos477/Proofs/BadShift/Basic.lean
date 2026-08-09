import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Cofactor.Basic
import Erdos477.Proofs.HeathBrown.Basic
import Erdos477.Proofs.FunctionField.Linear

/-!
# Stage E — the bad-shift estimate: support layer (SKETCH §6 Steps 0–2)

This file contains the Stage E *support* layer only (BLUEPRINT §"Stage E" steps
E1–E3): the unfolding lemma for `badShifts`, finiteness of `diagSolutions`, the
choice of a pair `(u_t, v_t)` with `u_t ≠ v_t` attached to a bad shift, the
constant `C_c := (2(1+|c|))^{1/12}`, the exponent-critical box bound
`max(|u|,|v|), |t| ≤ C_c · T^{13/12}`, the exponent-composition identity
`(T^{13/12})^{10/13} = T^{5/6}`, and the packaging inequality
`|S_c(T)| ≤ #diagSolutions(−c, C_c·T^{13/12})`.

The frozen `badShift_bound` itself is **not** proved here: its last step needs
`no_linear_param` (Stage C4) and `hb_diagonal_count` (Stage D), neither of which
is available yet.

Support declarations live in `namespace Erdos477` and never shadow a frozen name
from `Erdos477/Defs.lean` or `Erdos477/Theorems.lean`.
-/

namespace Erdos477

open scoped Classical

/-! ## Step 0 — unfolding `badShifts` (SKETCH §6 Step 0) -/

/-- Membership in `badShifts` unfolded. `badShifts` is a *classical* `Finset.filter`
    (`PROGRESS.md` decision 3 of 2026-08-09T00:25:44Z), so this goes through
    `Finset.mem_filter`/`Finset.mem_Icc`, never through `decide`. -/
theorem mem_badShifts_iff (c T t : ℤ) :
    t ∈ badShifts c T ↔ ((-T ≤ t ∧ t ≤ T) ∧ t ^ 13 - c ∈ Dset) := by
  simp only [badShifts, Finset.mem_filter, Finset.mem_Icc]

/-- Sanity guardrail: the bad shifts fit in the integer interval `[-T, T]`. -/
theorem card_badShifts_le (c : ℤ) {T : ℤ} (hT : 0 ≤ T) :
    (badShifts c T).card ≤ 2 * T.toNat + 1 := by
  have h1 : (badShifts c T).card ≤ (Finset.Icc (-T) T).card := by
    simp only [badShifts]
    exact Finset.card_filter_le _ _
  rw [Int.card_Icc] at h1
  omega

/-! ## Finiteness of the diagonal solution sets -/

/-- An integer whose real cast has absolute value `≤ X` lies in `[-⌈X⌉, ⌈X⌉]`. -/
theorem mem_Icc_ceil_of_abs_le {n : ℤ} {X : ℝ} (h : |(n : ℝ)| ≤ X) :
    n ∈ Finset.Icc (-⌈X⌉) ⌈X⌉ := by
  rw [abs_le] at h
  have hc : X ≤ (⌈X⌉ : ℝ) := Int.le_ceil X
  have h1 : (n : ℝ) ≤ ((⌈X⌉ : ℤ) : ℝ) := le_trans h.2 hc
  have h2 : (((-⌈X⌉ : ℤ)) : ℝ) ≤ (n : ℝ) := by
    push_cast
    linarith [h.1]
  rw [Finset.mem_Icc]
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩

/-- `diagSolutions M X` is finite: each coordinate is an integer of size `≤ X`. This
    is what makes every later `Set.ncard` comparison meaningful. -/
theorem diagSolutions_finite (M : ℤ) (X : ℝ) : (diagSolutions M X).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.Icc (-⌈X⌉) ⌈X⌉) ×ˢ (Finset.Icc (-⌈X⌉) ⌈X⌉) ×ˢ (Finset.Icc (-⌈X⌉) ⌈X⌉)))
  rintro ⟨x, y, z⟩ ⟨-, hx, hy, hz⟩
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
  exact ⟨mem_Icc_ceil_of_abs_le hx, mem_Icc_ceil_of_abs_le hy, mem_Icc_ceil_of_abs_le hz⟩

/-! ## E1/E2 — from a bad shift to a difference of *distinct* thirteenth powers -/

/-- SKETCH §6 Step 1: a bad shift `t` produces `u ≠ v` with `t¹³ − c = u¹³ − v¹³`.
    `u = v` would force `c = t¹³ ∈ B`, contradicting `hc` — this is the only place
    `c ∉ Bset` is used at this level (SKETCH §9.5(3)). -/
theorem uv_of_mem_badShifts (c : ℤ) (hc : c ∉ Bset) {T t : ℤ} (ht : t ∈ badShifts c T) :
    ∃ u v : ℤ, t ^ 13 - c = u ^ 13 - v ^ 13 ∧ u ≠ v := by
  obtain ⟨-, hD⟩ := (mem_badShifts_iff c T t).mp ht
  obtain ⟨u, v, huv⟩ := hD
  refine ⟨u, v, huv, ?_⟩
  rintro rfl
  exact hc ⟨t, by linarith⟩

/-! ## E3 — the exponent-critical box bound (SKETCH §6 Step 2) -/

/-- `C_c := (2(1 + |c|))^{1/12}` — depends only on `c`, never on `T`. -/
noncomputable def Cconst (c : ℤ) : ℝ := (2 * (1 + |(c : ℝ)|)) ^ ((1 : ℝ) / 12)

theorem one_le_Cconst (c : ℤ) : 1 ≤ Cconst c := by
  have h : (1 : ℝ) ≤ 2 * (1 + |(c : ℝ)|) := by
    have := abs_nonneg ((c : ℝ))
    linarith
  calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 12) := (Real.one_rpow _).symm
    _ ≤ (2 * (1 + |(c : ℝ)|)) ^ ((1 : ℝ) / 12) :=
        Real.rpow_le_rpow (by norm_num) h (by norm_num)

theorem Cconst_pos (c : ℤ) : 0 < Cconst c := lt_of_lt_of_le zero_lt_one (one_le_Cconst c)

/-- SKETCH §6 Step 2 (the paper's (4.2)):
    `(1/2)·max(|u|,|v|)¹² ≤ |u¹³ − v¹³| = |t¹³ − c| ≤ (1 + |c|)·T¹³`, so after taking
    twelfth roots `max(|u|,|v|) ≤ C_c · T^{13/12}`; and `|t| ≤ T ≤ C_c · T^{13/12}`. -/
theorem box_bound (c : ℤ) {T t u v : ℤ} (hT : 1 ≤ T) (ht : -T ≤ t ∧ t ≤ T)
    (huv : t ^ 13 - c = u ^ 13 - v ^ 13) (hne : u ≠ v) :
    max |(u : ℝ)| |(v : ℝ)| ≤ Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12) ∧
      |(t : ℝ)| ≤ Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12) := by
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by linarith
  have htabs : |(t : ℝ)| ≤ (T : ℝ) := by
    have h1 : -(T : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.1
    have h2 : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht.2
    rw [abs_le]
    exact ⟨h1, h2⟩
  have hT13 : (1 : ℝ) ≤ (T : ℝ) ^ 13 := by
    calc (1 : ℝ) = (1 : ℝ) ^ 13 := by norm_num
      _ ≤ (T : ℝ) ^ 13 := by gcongr
  -- `T^(13/12)` is at least `T`, hence at least `1`.
  have hrpow : (T : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := by
    calc (T : ℝ) = (T : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (T : ℝ) ^ ((13 : ℝ) / 12) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hrpow0 : (0 : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := le_trans hT0 hrpow
  -- the analytic chain
  have habs13 : |(t : ℝ) ^ 13 - (c : ℝ)| ≤ (1 + |(c : ℝ)|) * (T : ℝ) ^ 13 := by
    have htri : |(t : ℝ) ^ 13 - (c : ℝ)| ≤ |(t : ℝ) ^ 13| + |(c : ℝ)| := by
      have := abs_add_le ((t : ℝ) ^ 13) (-(c : ℝ))
      simpa [sub_eq_add_neg] using this
    have h1 : |(t : ℝ) ^ 13| ≤ (T : ℝ) ^ 13 := by
      rw [abs_pow]
      gcongr
    nlinarith [abs_nonneg ((c : ℝ)), hT13, h1, htri]
  have hcast : (t : ℝ) ^ 13 - (c : ℝ) = (u : ℝ) ^ 13 - (v : ℝ) ^ 13 := by
    exact_mod_cast huv
  have key : (1 / 2) * max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ |(u : ℝ) ^ 13 - (v : ℝ) ^ 13| :=
    abs_pow13_sub_pow13_ge_proof u v hne
  rw [← hcast] at key
  have hMx0 : (0 : ℝ) ≤ max |(u : ℝ)| |(v : ℝ)| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM12 : max |(u : ℝ)| |(v : ℝ)| ^ 12 ≤ 2 * (1 + |(c : ℝ)|) * (T : ℝ) ^ 13 := by
    linarith
  have hMle : max |(u : ℝ)| |(v : ℝ)| ≤ Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12) := by
    have h2 : (max |(u : ℝ)| |(v : ℝ)| ^ (12 : ℕ)) ^ ((1 : ℝ) / 12)
        ≤ (2 * (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by positivity) hM12 (by norm_num)
    have h3 : (max |(u : ℝ)| |(v : ℝ)| ^ (12 : ℕ)) ^ ((1 : ℝ) / 12)
        = max |(u : ℝ)| |(v : ℝ)| := by
      rw [← Real.rpow_natCast (max |(u : ℝ)| |(v : ℝ)|) 12, ← Real.rpow_mul hMx0]
      norm_num
    have hTr : ((T : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 12) = (T : ℝ) ^ ((13 : ℝ) / 12) := by
      rw [← Real.rpow_natCast (T : ℝ) 13, ← Real.rpow_mul hT0]
      norm_num
    have h4 : (2 * (1 + |(c : ℝ)|) * (T : ℝ) ^ (13 : ℕ)) ^ ((1 : ℝ) / 12)
        = Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12) := by
      rw [Real.mul_rpow (by positivity) (by positivity), hTr]
      simp only [Cconst]
    rw [h3, h4] at h2
    exact h2
  refine ⟨hMle, ?_⟩
  calc |(t : ℝ)| ≤ (T : ℝ) := htabs
    _ ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := hrpow
    _ = 1 * (T : ℝ) ^ ((13 : ℝ) / 12) := (one_mul _).symm
    _ ≤ Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12) := by
        exact mul_le_mul_of_nonneg_right (one_le_Cconst c) hrpow0

/-! ## Exponent composition: `(T^{13/12})^{10/13} = T^{5/6}` -/

theorem rpow_box_compose {T : ℝ} (hT : 0 ≤ T) :
    ((T ^ ((13 : ℝ) / 12)) ^ ((10 : ℝ) / 13)) = T ^ ((5 : ℝ) / 6) := by
  rw [← Real.rpow_mul hT]
  norm_num

/-! ## Packaging: bad shifts inject into diagonal solutions -/

/-- SKETCH §6 Step 1's substitution `x := u`, `y := −v`, `z := −t` maps `badShifts c T`
    injectively into `diagSolutions (−c) (C_c · T^{13/12})` (the third coordinate
    recovers `t`; only injectivity holds and only injectivity is needed). -/
theorem badShifts_card_le_diagSolutions (c : ℤ) (hc : c ∉ Bset) {T : ℤ} (hT : 1 ≤ T) :
    ((badShifts c T).card : ℝ)
      ≤ ((diagSolutions (-c) (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12))).ncard : ℝ) := by
  have hex : ∀ t : ℤ, ∃ uv : ℤ × ℤ, t ∈ badShifts c T →
      (t ^ 13 - c = uv.1 ^ 13 - uv.2 ^ 13 ∧ uv.1 ≠ uv.2) := by
    intro t
    by_cases h : t ∈ badShifts c T
    · obtain ⟨u, v, h1, h2⟩ := uv_of_mem_badShifts c hc h
      exact ⟨(u, v), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(0, 0), fun h' => absurd h' h⟩
  choose UV hUV using hex
  have hfin := diagSolutions_finite (-c) (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12))
  have hmem : ∀ t ∈ badShifts c T,
      ((UV t).1, -(UV t).2, -t) ∈ hfin.toFinset := by
    intro t ht
    rw [Set.Finite.mem_toFinset]
    obtain ⟨huv, hne⟩ := hUV t ht
    obtain ⟨hbox, -⟩ := (mem_badShifts_iff c T t).mp ht
    obtain ⟨hmax, htabs⟩ := box_bound c hT hbox huv hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (UV t).1 ^ 13 + (-(UV t).2) ^ 13 + (-t) ^ 13 = -c
      rw [Odd.neg_pow odd_thirteen, Odd.neg_pow odd_thirteen]
      linarith
    · exact le_trans (le_max_left _ _) hmax
    · show |((-(UV t).2 : ℤ) : ℝ)| ≤ _
      push_cast
      rw [abs_neg]
      exact le_trans (le_max_right _ _) hmax
    · show |((-t : ℤ) : ℝ)| ≤ _
      push_cast
      rw [abs_neg]
      exact htabs
  have hinj : Set.InjOn (fun t : ℤ => ((UV t).1, -(UV t).2, -t)) ↑(badShifts c T) := by
    intro a _ b _ hab
    have h : -a = -b := congrArg (fun p : ℤ × ℤ × ℤ => p.2.2) hab
    omega
  have hcard : (badShifts c T).card ≤ hfin.toFinset.card :=
    Finset.card_le_card_of_injOn _ hmem hinj
  have hEq : (diagSolutions (-c) (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12))).ncard
      = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hEq]
  exact_mod_cast hcard

/-! ## Guardrails from the Stage E cheat-watch box -/

example (c : ℤ) : badShifts c 1 ⊆ ({-1, 0, 1} : Finset ℤ) := by
  intro t ht
  obtain ⟨⟨h1, h2⟩, -⟩ := (mem_badShifts_iff c 1 t).mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

example (c : ℤ) (T : ℤ) (hT : 0 ≤ T) : (badShifts c T).card ≤ 2 * T.toNat + 1 :=
  card_badShifts_le c hT

example : ((2 : ℝ) ^ ((13 : ℝ) / 12)) ^ ((10 : ℝ) / 13) = (2 : ℝ) ^ ((5 : ℝ) / 6) :=
  rpow_box_compose (by norm_num)

/-! ## E4 — the bad-shift bound, conditional on the Stage-C4 exclusion (SKETCH §6 Step 4)

The frozen `badShift_bound` (`Erdos477/Theorems.lean:95-97`) obtains its `hexcl`
input from `no_linear_param c hc` (BLUEPRINT Stage C4), which is still `sorry`
and therefore may not be cited. The lemma below is that theorem with
`no_linear_param c hc` replaced by an explicit hypothesis of *exactly* its
conclusion's shape, so that when C4 lands the frozen statement becomes the one
liner `badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)`.

It is deliberately **not** named `badShift_bound_proof`: it is conditional and
must never be mistaken for the frozen theorem. -/

/-- `c ∉ Bset` forces `-c ≠ 0`, since `0 = 0 ^ 13 ∈ Bset` (L0.5). -/
theorem neg_ne_zero_of_not_mem_Bset {c : ℤ} (hc : c ∉ Bset) : -c ≠ 0 := by
  intro h
  exact hc (by simpa using (neg_eq_zero.mp h) ▸ zero_mem_Bset_proof)

/-- **Stage E, step E4, conditional form.** With the Stage-C4 exclusion supplied as
    a hypothesis, `|S_c(T)| ≤ K · T^{5/6}` with `K` independent of `T`.

    The chain is SKETCH §6 Step 4: `badShifts_card_le_diagSolutions` maps the bad
    shifts injectively into `diagSolutions (−c) X` for the box side
    `X = C_c · T^{13/12}`, `hb_diagonal_count_proof (−c)` bounds that count by
    `K₀ · X^{10/13}`, and `rpow_box_compose` collapses
    `(T^{13/12})^{10/13}` to exactly `T^{5/6}`. -/
theorem badShift_bound_of_hexcl (c : ℤ) (hc : c ∉ Bset)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C (-c) →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := by
  -- Stage D at `M := -c`, once and for all: `K₀` does not depend on `T`.
  obtain ⟨K₀, hK₀1, hK₀⟩ :=
    hb_diagonal_count_proof (-c) (neg_ne_zero_of_not_mem_Bset hc) hexcl
  have hCpos : (0 : ℝ) < Cconst c := Cconst_pos c
  refine ⟨max 1 (K₀ * Cconst c ^ ((10 : ℝ) / 13)), le_max_left _ _, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by linarith
  -- the box side `X = C_c · T^{13/12}` and its lower bound `1 ≤ X`
  have hTr1 : (1 : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((13 : ℝ) / 12) := (Real.one_rpow _).symm
      _ ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := Real.rpow_le_rpow (by norm_num) hT1 (by norm_num)
  have hTr0 : (0 : ℝ) ≤ (T : ℝ) ^ ((13 : ℝ) / 12) := by linarith
  have hX1 : (1 : ℝ) ≤ Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12) := by
    nlinarith [one_le_Cconst c]
  -- Stage D applied at the box side, then the exponent composition
  have hsplit : (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12)) ^ ((10 : ℝ) / 13)
      = Cconst c ^ ((10 : ℝ) / 13) * (T : ℝ) ^ ((5 : ℝ) / 6) := by
    rw [Real.mul_rpow hCpos.le hTr0, rpow_box_compose hT0]
  have hD : ((diagSolutions (-c) (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12))).ncard : ℝ)
      ≤ K₀ * (Cconst c ^ ((10 : ℝ) / 13) * (T : ℝ) ^ ((5 : ℝ) / 6)) := by
    have := hK₀ (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12)) hX1
    rwa [hsplit] at this
  -- assemble
  have hTs0 : (0 : ℝ) ≤ (T : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_nonneg hT0 _
  calc ((badShifts c T).card : ℝ)
      ≤ ((diagSolutions (-c) (Cconst c * (T : ℝ) ^ ((13 : ℝ) / 12))).ncard : ℝ) :=
        badShifts_card_le_diagSolutions c hc hT
    _ ≤ K₀ * (Cconst c ^ ((10 : ℝ) / 13) * (T : ℝ) ^ ((5 : ℝ) / 6)) := hD
    _ = (K₀ * Cconst c ^ ((10 : ℝ) / 13)) * (T : ℝ) ^ ((5 : ℝ) / 6) := by ring
    _ ≤ max 1 (K₀ * Cconst c ^ ((10 : ℝ) / 13)) * (T : ℝ) ^ ((5 : ℝ) / 6) := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hTs0

/-! ## E4 — the frozen bad-shift bound (BLUEPRINT Stage E, step E4)

Stage C4 has landed (`Erdos477.no_linear_param_proof`,
`Erdos477/Proofs/FunctionField/Linear.lean`), and its conclusion is *exactly* the
`hexcl` hypothesis of `badShift_bound_of_hexcl` above, so the frozen
`badShift_bound` (`Erdos477/Theorems.lean:95-97`) is a one-liner.  The box side
is not re-derived here: it is the already-proved `Cconst c * T^{13/12}` of
`box_bound`, and the exponent stays literally `(5 : ℝ) / 6`. -/

/-- **P3.1 = paper's Proposition 4.1** (BLUEPRINT Stage E, step E4; SKETCH §6):
`|S_c(T)| ≤ K_c · T^{5/6}` with `K_c` independent of `T`.

Type-identical to the frozen `Erdos477.badShift_bound`. -/
theorem badShift_bound_proof (c : ℤ) (hc : c ∉ Bset) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) :=
  badShift_bound_of_hexcl c hc (no_linear_param_proof c hc)

end Erdos477
