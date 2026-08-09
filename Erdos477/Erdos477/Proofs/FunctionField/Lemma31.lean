import Erdos477.Proofs.FunctionField.BMForms

/-!
# Stage C step C2 — Lemma 3.1 (`no_nonconstant_param_of_not_pow13`)

This file proves `Erdos477.no_nonconstant_param_of_not_pow13_proof`, the frozen
Lemma 3.1 of the paper (`Erdos477/Theorems.lean:62-64`), following BLUEPRINT
§"Stage C" step C2 and SKETCH §5.2.2 (Cases A/B/C/D).

The set-up.  A parametrization `IsParamOfXN N e A` is base-changed to `ℂ` along
`MvPolynomial.map (algebraMap ℚ ℂ)` — exactly the map already used by the
`NoCommonProjZero` clause of `IsParamOfXN` — and the defining identity is read as
the four-term relation

```
    ∑ i, C (γ i) * (Ac i) ^ 13 = 0 ,        γ = ![1, 1, 1, -N] .
```

The case analysis of SKETCH §5.2.2 is on how many of the four terms vanish:

* **Cases A and B** (four resp. three nonzero terms, no vanishing proper
  sub-sum) are *both* handled by the single support lemma
  `Erdos477.const_ratios_of_forms`, which applies the ✅ C1 theorem
  `Erdos477.bm_forms_height_bound_proof` at `r = 4` (coefficient
  `Nat.choose 3 2 = 3`, giving `13e ≤ 12e − 6`) and at `r = 3` (coefficient
  `Nat.choose 2 2 = 1`, giving `13e ≤ 3e − 2`).  Both are impossible (already for
  `0 ≤ e`, so the `1 ≤ e` clause of `IsParamOfXN` is not even needed), hence in
  those two cases the family of ratios *is* constant — which is what the goal
  asks for.  (Case B is reduced to `r = 3` through `Fin.succAbove`, which
  enumerates the three indices other than the vanishing one.)
* **Case C** (at most two nonzero terms) closes the goal directly, through
  `Erdos477.pow13_ratio_const`.
* **Case D** (four nonzero terms, some proper sub-sum vanishes) produces a pair
  `{i, 3}` with `Ac i ^ 13 = C N * Ac 3 ^ 13`, hence `Ac i = C μ * Ac 3` and
  `μ ^ 13 = N`; the descent `Erdos477.descend_const_ratio` puts `μ` in `ℚ`,
  contradicting `hpow`.

The two workhorses are `Erdos477.const_of_pow13_const` (a rational function with
a nonzero constant `13`-th power is constant — the orders argument of SKETCH
§5.2.2, display (3.2), built on `ordP_pow`/`ordP_C` from
`Erdos477/Proofs/FunctionField/Basic.lean`) and `Erdos477.pow13_ratio_const`
(its form-level consequence, via `Erdos477.dehom` and
`Erdos477.dehom_injective_of_isHomogeneous`).

SKETCH §5.2.2 additionally identifies, inside Case D, the *companion* pair
`F¹³ + G¹³ = 0` (whence `F = −G` by `Erdos477.pow13_inj_rat`).  That step belongs
to the classification half of the paper's Lemma 3.1 — the description of the
three lines when `N ∈ ℚ¹³` — which the frozen statement does not assert; the pair
containing the index `3` already contradicts `hpow`, so it is not needed here and
`Proofs/Elementary/Basic.lean` is deliberately not imported.

Route B (the Vandermonde argument of SKETCH §5.1) is forbidden here and does not
appear; `Polynomial.abc` is not used; no new `axiom` is declared.  The only
assumed certificate reached is `Erdos477.brownawell_masser_P1_four_term`, and
only through the ✅ `Erdos477.bm_forms_height_bound_proof`.
-/

namespace Erdos477

open scoped Classical

/-! ## A rational function with a constant nonzero `13`-th power is constant -/

section RatFuncConst

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, a rational function all of whose orders at
the *finite* points vanish is constant. -/
theorem isConstRF_of_ordP_some_eq_zero {f : RatFunc k}
    (h : ∀ α : k, ordP (some α) f = 0) : IsConstRF f := by
  by_cases hf : f = 0
  · exact ⟨0, by rw [hf, map_zero]⟩
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hmult : ∀ α : k, Polynomial.rootMultiplicity α f.num
      = Polynomial.rootMultiplicity α f.denom := by
    intro α
    have := h α
    rw [ordP_some_eq] at this
    omega
  have hroots : f.num.roots = f.denom.roots := by
    refine Multiset.ext.mpr fun α => ?_
    rw [Polynomial.count_roots, Polynomial.count_roots]
    exact hmult α
  obtain ⟨b, hb⟩ : ∃ b : k, f.num.leadingCoeff = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : k, f.denom.leadingCoeff = c := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Polynomial k,
      (Multiset.map (fun x => Polynomial.X - Polynomial.C x) f.denom.roots).prod = P := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hc ▸ Polynomial.leadingCoeff_ne_zero.mpr hden
  have h1 : f.num = Polynomial.C b * P := by
    rw [← hb, ← hP, ← hroots]
    exact (IsAlgClosed.splits f.num).eq_prod_roots
  have h2 : f.denom = Polynomial.C c * P := by
    rw [← hc, ← hP]
    exact (IsAlgClosed.splits f.denom).eq_prod_roots
  have hnd : f.num = Polynomial.C (b / c) * f.denom := by
    rw [h1, h2, ← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ hc0]
  refine ⟨b / c, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom f, hnd]
  rw [map_mul, RatFunc.algebraMap_C, mul_div_assoc,
    div_self (RatFunc.algebraMap_ne_zero hden), mul_one]

/-- SKETCH §5.2.2, display (3.2): a rational function whose `13`-th power is a
nonzero constant is itself constant. -/
theorem const_of_pow13_const {f : RatFunc k} {a : k} (h : f ^ 13 = RatFunc.C a)
    (ha : a ≠ 0) : IsConstRF f := by
  have hCa : (RatFunc.C a : RatFunc k) ≠ 0 := by
    simpa using fun hc => ha (by simpa using hc)
  have hf : f ≠ 0 := by
    intro hf0
    rw [hf0] at h
    exact hCa (by simpa using h.symm)
  refine isConstRF_of_ordP_some_eq_zero fun α => ?_
  have hp := ordP_pow (some α) hf 13
  rw [h, ordP_C] at hp
  omega

end RatFuncConst

/-! ## Consequences for binary forms -/

section Forms

variable {k : Type*} [Field k]

/-- Cancel a nonzero constant factor. -/
theorem eq_C_mul_of_C_mul_eq {c d : k} (hc : c ≠ 0) {X Y : MvPolynomial (Fin 2) k}
    (h : MvPolynomial.C c * X = MvPolynomial.C d * Y) :
    X = MvPolynomial.C (d / c) * Y := by
  refine mul_left_cancel₀ (a := (MvPolynomial.C c : MvPolynomial (Fin 2) k))
    (MvPolynomial.C_eq_zero.not.mpr hc) ?_
  rw [h, ← mul_assoc, ← MvPolynomial.C_mul, mul_div_cancel₀ _ hc]

end Forms

section FormsAlgClosed

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- If two nonzero binary forms of the same degree have proportional `13`-th
powers, they are themselves proportional.  This is the form-level version of
`const_of_pow13_const`. -/
theorem pow13_ratio_const {Φ Ψ : MvPolynomial (Fin 2) k} {e : ℕ}
    (hΦ : Φ.IsHomogeneous e) (hΨ : Ψ.IsHomogeneous e) (hΦ0 : Φ ≠ 0) (hΨ0 : Ψ ≠ 0)
    {γ : k} (h : Φ ^ 13 = MvPolynomial.C γ * Ψ ^ 13) :
    ∃ μ : k, Φ = MvPolynomial.C μ * Ψ := by
  have hp0 : dehom Φ ≠ 0 := dehom_ne_zero hΦ hΦ0
  have hq0 : dehom Ψ ≠ 0 := dehom_ne_zero hΨ hΨ0
  -- the polynomial identity
  have hpoly : dehom Φ ^ 13 = Polynomial.C γ * dehom Ψ ^ 13 := by
    have hd := congrArg dehom h
    simpa [dehom] using hd
  have hγ0 : γ ≠ 0 := by
    intro hγ
    rw [hγ, map_zero, zero_mul] at hpoly
    exact hp0 (pow_eq_zero_iff (n := 13) (by norm_num) |>.mp hpoly)
  -- pass to `RatFunc k`
  set F : RatFunc k := algebraMap (Polynomial k) (RatFunc k) (dehom Φ) with hF
  set G : RatFunc k := algebraMap (Polynomial k) (RatFunc k) (dehom Ψ) with hG
  have hG0 : G ≠ 0 := RatFunc.algebraMap_ne_zero hq0
  have hrat : (F / G) ^ 13 = RatFunc.C γ := by
    have h1 : F ^ 13 = RatFunc.C γ * G ^ 13 := by
      rw [hF, hG, ← map_pow, ← map_pow, ← RatFunc.algebraMap_C, ← map_mul, hpoly]
    rw [div_pow, h1, mul_div_assoc, div_self (pow_ne_zero 13 hG0), mul_one]
  obtain ⟨μ, hμ⟩ := const_of_pow13_const hrat hγ0
  refine ⟨μ, ?_⟩
  have hpq : dehom Φ = Polynomial.C μ * dehom Ψ := by
    refine RatFunc.algebraMap_injective k ?_
    rw [map_mul, RatFunc.algebraMap_C, ← hF, ← hG, ← hμ, div_mul_cancel₀ _ hG0]
  refine dehom_injective_of_isHomogeneous hΦ ?_ ?_
  · simpa using (MvPolynomial.isHomogeneous_C (Fin 2) μ).mul hΨ
  · rw [dehom_mul, dehom_C, hpq]

end FormsAlgClosed

/-! ## Descent of a constant ratio from `ℂ` to `ℚ` -/

/-- If two `ℚ`-forms become proportional after base change to `ℂ`, the ratio is
already rational.  This is the `ratfunc_const_descends` step of BLUEPRINT C2:
compare one nonzero coefficient. -/
theorem descend_const_ratio {Φ Ψ : MvPolynomial (Fin 2) ℚ} (hΨ : Ψ ≠ 0) {μ : ℂ}
    (h : MvPolynomial.map (algebraMap ℚ ℂ) Φ
      = MvPolynomial.C μ * MvPolynomial.map (algebraMap ℚ ℂ) Ψ) :
    ∃ d : ℚ, algebraMap ℚ ℂ d = μ ∧ Φ = MvPolynomial.C d * Ψ := by
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hΨ
  have hmc : algebraMap ℚ ℂ (MvPolynomial.coeff m Ψ) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr hm
  have h1 := congrArg (MvPolynomial.coeff m) h
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at h1
  obtain ⟨d, hddef⟩ : ∃ d : ℚ,
      MvPolynomial.coeff m Φ / MvPolynomial.coeff m Ψ = d := ⟨_, rfl⟩
  have hd : algebraMap ℚ ℂ d = μ := by
    rw [← hddef, map_div₀, h1, mul_div_assoc, div_self hmc, mul_one]
  refine ⟨d, hd, ?_⟩
  refine MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective ?_
  rw [map_mul, MvPolynomial.map_C, hd, h]

/-- A family of `ℚ`-forms whose base changes are all `ℂ`-multiples of one of them
is a constant family already over `ℚ`. -/
theorem isConstantFamily_of_map_ratios {n : ℕ} {A : Fin n → MvPolynomial (Fin 2) ℚ}
    {j : Fin n} (hj : A j ≠ 0)
    (h : ∀ i, ∃ μ : ℂ, MvPolynomial.map (algebraMap ℚ ℂ) (A i)
      = MvPolynomial.C μ * MvPolynomial.map (algebraMap ℚ ℂ) (A j)) :
    IsConstantFamily A := by
  choose μ hμ using h
  choose d _ hd2 using fun i => descend_const_ratio hj (hμ i)
  exact ⟨d, A j, hd2⟩

/-! ## No proper sub-sum of three nonzero terms summing to zero can vanish -/

theorem no_vanishing_subsum_three {R : Type*} [AddCommGroup R] {T : Fin 3 → R}
    (hT : ∀ i, T i ≠ 0) (hsum : ∑ i, T i = 0) :
    ∀ J : Finset (Fin 3), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, T i ≠ 0 := by
  classical
  intro J h1 h2 hz
  have hcompl : ∑ i ∈ Jᶜ, T i = 0 := by
    have hadd := Finset.sum_add_sum_compl J T
    rw [hz, hsum] at hadd
    simpa using hadd
  have hcard3 : J.card ≠ 3 := fun hh => h2 (Finset.eq_univ_of_card J (by simpa using hh))
  have hcardJ : 1 ≤ J.card := Finset.card_pos.mpr h1
  have hJle : J.card ≤ 3 := by simpa using Finset.card_le_univ J
  have hcardc : Jᶜ.card = 3 - J.card := by simp [Finset.card_compl]
  rcases (show J.card = 1 ∨ Jᶜ.card = 1 by omega) with hh | hh
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hh
    rw [hi, Finset.sum_singleton] at hz
    exact hT i hz
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hh
    rw [hi, Finset.sum_singleton] at hcompl
    exact hT i hcompl

/-! ## Cases A and B of SKETCH §5.2.2, through `bm_forms_height_bound_proof` -/

/-- **Cases A and B of Lemma 3.1.**  For `r ∈ {3, 4}` nonzero binary forms of a
common degree `e ≥ 1` without common projective zero, whose `13`-th powers scaled
by nonzero constants sum to zero with no vanishing proper sub-sum, *all the
ratios are constant*.

This is the contrapositive packaging of BLUEPRINT C2 Cases A and B: were the
ratios not all constant, `bm_forms_height_bound_proof` would give
`13e ≤ Nat.choose (r-1) 2 * (r·e − 2)`, i.e. `13e ≤ 12e − 6` for `r = 4` and
`13e ≤ 3e − 2` for `r = 3`, both impossible. -/
theorem const_ratios_of_forms {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {r : ℕ} (hr : 3 ≤ r) (hr4 : r ≤ 4) {e : ℕ}
    (B : Fin r → MvPolynomial (Fin 2) k) (γ : Fin r → k) (i0 : Fin r)
    (hB0 : ∀ i, B i ≠ 0) (hγ : ∀ i, γ i ≠ 0)
    (hhom : ∀ i, (B i).IsHomogeneous e)
    (hcop : NoCommonProjZero B)
    (hsum : ∑ i, MvPolynomial.C (γ i) * B i ^ 13 = 0)
    (hsub : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ →
      ∑ i ∈ J, MvPolynomial.C (γ i) * B i ^ 13 ≠ 0) :
    ∃ μ : Fin r → k, ∀ i, B i = MvPolynomial.C (μ i) * B i0 := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Fin r → MvPolynomial (Fin 2) k,
      ∀ i, T i = MvPolynomial.C (γ i) * B i ^ 13 := ⟨_, fun _ => rfl⟩
  have hzero : ∀ (i : Fin r) (v : Fin 2 → k),
      MvPolynomial.eval v (T i) = 0 → MvPolynomial.eval v (B i) = 0 := by
    intro i v hv
    rw [hT i] at hv
    simp only [map_mul, map_pow, MvPolynomial.eval_C] at hv
    rcases mul_eq_zero.mp hv with h | h
    · exact absurd h (hγ i)
    · exact pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h
  have hT0 : ∀ i, T i ≠ 0 := by
    intro i h
    rw [hT i, mul_eq_zero] at h
    rcases h with h | h
    · exact hγ i (MvPolynomial.C_eq_zero.mp h)
    · exact hB0 i (pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h)
  have hhomT : ∀ i, (T i).IsHomogeneous (13 * e) := by
    intro i
    have h1 : ((B i) ^ 13).IsHomogeneous (13 * e) := by
      rw [Nat.mul_comm]
      exact (hhom i).pow 13
    have h2 := (MvPolynomial.isHomogeneous_C (Fin 2) (γ i)).mul h1
    rw [hT i]
    simpa using h2
  have hcopT : NoCommonProjZero T := fun v hv => hcop v fun i => hzero i v (hv i)
  have hsum' : ∑ i, T i = 0 := by simp only [hT]; exact hsum
  have hsub' : ∀ J : Finset (Fin r), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, T i ≠ 0 := by
    intro J h1 h2
    simp only [hT]
    exact hsub J h1 h2
  by_contra hcon
  -- the family `T` is not a constant family
  have hncT : ¬ IsConstantFamily T := by
    rintro ⟨a, Φ, hΦ⟩
    have ha0 : a i0 ≠ 0 := by
      intro h
      exact hT0 i0 (by rw [hΦ i0, h, map_zero, zero_mul])
    have hΦeq : Φ = MvPolynomial.C (γ i0 / a i0) * B i0 ^ 13 :=
      eq_C_mul_of_C_mul_eq ha0 (by rw [← hΦ i0, hT i0])
    have hratio : ∀ i, ∃ μ : k, B i = MvPolynomial.C μ * B i0 := by
      intro i
      have h1 : MvPolynomial.C (γ i) * B i ^ 13
          = MvPolynomial.C (a i * (γ i0 / a i0)) * B i0 ^ 13 := by
        rw [← hT i, hΦ i, hΦeq, ← mul_assoc, ← MvPolynomial.C_mul]
      exact pow13_ratio_const (hhom i) (hhom i0) (hB0 i) (hB0 i0)
        (eq_C_mul_of_C_mul_eq (hγ i) h1)
    choose μ hμ using hratio
    exact hcon ⟨μ, hμ⟩
  have hbm := bm_forms_height_bound_proof r (13 * e) hr T hT0 hhomT hcopT hsum' hsub' hncT
  -- the projective zeros of the product are among those of the `B i`
  have hZfin : ∀ i, {P : P1Point k | IsProjZero (B i) P}.Finite :=
    fun i => isProjZero_finite (hB0 i) (hhom i)
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin r → Finset (P1Point k), ∀ i, Z i = (hZfin i).toFinset :=
    ⟨_, fun _ => rfl⟩
  have hZcard : ∀ i, (Z i).card ≤ e := by
    intro i
    have h := projZeroCount_le_of_isHomogeneous (hB0 i) (hhom i)
    rwa [projZeroCount, Set.ncard_eq_toFinset_card _ (hZfin i), ← hZ i] at h
  have hsubset : {P : P1Point k | IsProjZero (∏ i, T i) P} ⊆ ↑(Finset.univ.biUnion Z) := by
    intro P hP
    obtain ⟨i, hi⟩ := IsProjZero_prod hP
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩)
    rw [hZ i]
    refine (hZfin i).mem_toFinset.mpr ?_
    cases P with
    | none => exact hzero i _ hi
    | some α => exact hzero i _ hi
  have hpzc : projZeroCount (∏ i, T i) ≤ r * e := by
    have h1 : projZeroCount (∏ i, T i) ≤ (Finset.univ.biUnion Z).card := by
      rw [projZeroCount, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
    have h2 : (Finset.univ.biUnion Z).card ≤ ∑ i, (Z i).card := Finset.card_biUnion_le
    have h3 : ∑ i : Fin r, (Z i).card ≤ ∑ _i : Fin r, e :=
      Finset.sum_le_sum fun i _ => hZcard i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    omega
  rcases (show r = 3 ∨ r = 4 by omega) with rfl | rfl
  · norm_num at hbm
    omega
  · norm_num at hbm
    omega

/-! ## C2 — the frozen Lemma 3.1 -/

/-- **BLUEPRINT Stage C, step C2 / SKETCH §5.2.2 (paper's Lemma 3.1).**  Type
character-identical to the frozen `Erdos477.no_nonconstant_param_of_not_pow13`
(`Erdos477/Theorems.lean:62-64`). -/
theorem no_nonconstant_param_of_not_pow13_proof (N : ℚ) (hN : N ≠ 0)
    (hpow : ¬ ∃ d : ℚ, d ^ 13 = N) (e : ℕ) (A : Fin 4 → MvPolynomial (Fin 2) ℚ)
    (hA : IsParamOfXN N e A) : IsConstantFamily A := by
  classical
  obtain ⟨-, hhom, hcop, heq⟩ := hA
  -- base change to `ℂ`
  have hφinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
  have hmapinj : Function.Injective
      (MvPolynomial.map (algebraMap ℚ ℂ) :
        MvPolynomial (Fin 2) ℚ → MvPolynomial (Fin 2) ℂ) :=
    MvPolynomial.map_injective _ hφinj
  obtain ⟨Ac, hAc⟩ : ∃ Ac : Fin 4 → MvPolynomial (Fin 2) ℂ,
      ∀ i, Ac i = MvPolynomial.map (algebraMap ℚ ℂ) (A i) := ⟨_, fun _ => rfl⟩
  have hcopAc : NoCommonProjZero Ac := by
    intro v hv
    refine hcop v fun i => ?_
    have h := hv i
    rw [hAc i] at h
    exact h
  have hAceq : ∀ i, Ac i = 0 ↔ A i = 0 := fun i => by
    rw [hAc i]; exact map_eq_zero_iff _ hmapinj
  have hhomAc : ∀ i, (Ac i).IsHomogeneous e := fun i => by
    rw [hAc i]; exact (hhom i).map _
  have hNc : (algebraMap ℚ ℂ) N ≠ 0 := (map_ne_zero_iff _ hφinj).mpr hN
  -- the four scaling constants `γ = ![1, 1, 1, -N]`
  obtain ⟨γ, hγdef⟩ : ∃ γ : Fin 4 → ℂ, γ = ![1, 1, 1, -(algebraMap ℚ ℂ) N] := ⟨_, rfl⟩
  have hγ0 : ∀ i, γ i ≠ 0 := by
    intro i
    rw [hγdef]
    fin_cases i <;> simp [hN]
  have hγ1 : ∀ i : Fin 4, i ≠ 3 → γ i = 1 := by
    intro i hi
    rw [hγdef]
    fin_cases i <;> simp_all
  have hγ3 : γ 3 = -(algebraMap ℚ ℂ) N := by rw [hγdef]; simp
  -- the four terms of the relation
  obtain ⟨T, hT⟩ : ∃ T : Fin 4 → MvPolynomial (Fin 2) ℂ,
      ∀ i, T i = MvPolynomial.C (γ i) * Ac i ^ 13 := ⟨_, fun _ => rfl⟩
  have hT0 : ∀ i, T i = 0 ↔ Ac i = 0 := by
    intro i
    rw [hT i]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (MvPolynomial.C_eq_zero.mp h) (hγ0 i)
      · exact pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h
    · intro h; rw [h]; simp
  have heqAc : Ac 0 ^ 13 + Ac 1 ^ 13 + Ac 2 ^ 13
      = MvPolynomial.C ((algebraMap ℚ ℂ) N) * Ac 3 ^ 13 := by
    have hmapped := congrArg (MvPolynomial.map (algebraMap ℚ ℂ)) heq
    simpa only [map_add, map_mul, map_pow, MvPolynomial.map_C, ← hAc] using hmapped
  have hsumT : ∑ i, T i = 0 := by
    rw [Fin.sum_univ_four]
    simp only [hT, hγ1 0 (by decide), hγ1 1 (by decide), hγ1 2 (by decide), hγ3,
      map_one, one_mul, MvPolynomial.C_neg]
    linear_combination heqAc
  have hsumC : ∑ i, MvPolynomial.C (γ i) * Ac i ^ 13 = 0 := by
    simp only [← hT]; exact hsumT
  -- `NoCommonProjZero` forbids all four forms from vanishing
  have hnotallzero : ¬ (∀ i, A i = 0) := by
    intro hall
    have h0 : ∀ i, MvPolynomial.eval ![1, 0] (Ac i) = 0 := by
      intro i; rw [hAc i, hall i]; simp
    have h1 := congrFun (hcopAc ![1, 0] h0) 0
    simp at h1
  by_cases hex : ∃ i, A i = 0
  · obtain ⟨i0, hi0⟩ := hex
    by_cases hex2 : ∃ i1, i1 ≠ i0 ∧ A i1 = 0
    · -- ===== Case C: at most two of the four forms are nonzero =====
      obtain ⟨i1, hne01, hi1⟩ := hex2
      have hpaircard : ({i0, i1} : Finset (Fin 4)).card = 2 :=
        Finset.card_pair (Ne.symm hne01)
      have hcc : (({i0, i1} : Finset (Fin 4))ᶜ).card = 2 := by
        rw [Finset.card_compl, hpaircard]; simp
      obtain ⟨l, m, hlm, hcomplEq⟩ := Finset.card_eq_two.mp hcc
      have hsumpair : ∑ i ∈ ({i0, i1} : Finset (Fin 4)), T i = 0 := by
        rw [Finset.sum_pair (Ne.symm hne01), (hT0 i0).mpr ((hAceq i0).mpr hi0),
          (hT0 i1).mpr ((hAceq i1).mpr hi1), add_zero]
      have hcompl : ∑ i ∈ ({i0, i1} : Finset (Fin 4))ᶜ, T i = 0 := by
        have hadd := Finset.sum_add_sum_compl ({i0, i1} : Finset (Fin 4)) T
        rw [hsumpair, hsumT] at hadd
        simpa using hadd
      rw [hcomplEq, Finset.sum_pair hlm] at hcompl
      have hcover : ∀ i : Fin 4, i = i0 ∨ i = i1 ∨ i = l ∨ i = m := by
        intro i
        by_cases h : i ∈ ({i0, i1} : Finset (Fin 4))
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h; tauto
        · have hmem : i ∈ ({i0, i1} : Finset (Fin 4))ᶜ := Finset.mem_compl.mpr h
          rw [hcomplEq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem; tauto
      by_cases hm0 : A m = 0
      · exfalso
        refine hnotallzero fun i => ?_
        have hTm : T m = 0 := (hT0 m).mpr ((hAceq m).mpr hm0)
        have hTl : T l = 0 := by rw [hTm, add_zero] at hcompl; exact hcompl
        have hl0 : A l = 0 := (hAceq l).mp ((hT0 l).mp hTl)
        rcases hcover i with h | h | h | h <;> rw [h] <;> assumption
      · have hAm : Ac m ≠ 0 := (hAceq m).not.mpr hm0
        have hAl : Ac l ≠ 0 := by
          intro h
          refine hAm ?_
          have hTl : T l = 0 := (hT0 l).mpr h
          rw [hTl, zero_add] at hcompl
          exact (hT0 m).mp hcompl
        have hpair : MvPolynomial.C (γ l) * Ac l ^ 13
            = MvPolynomial.C (-(γ m)) * Ac m ^ 13 := by
          rw [MvPolynomial.C_neg]
          rw [hT l, hT m] at hcompl
          linear_combination hcompl
        obtain ⟨ν, hν⟩ := pow13_ratio_const (hhomAc l) (hhomAc m) hAl hAm
          (eq_C_mul_of_C_mul_eq (hγ0 l) hpair)
        refine isConstantFamily_of_map_ratios (j := m) hm0 fun i => ?_
        rcases hcover i with h | h | h | h
        · exact ⟨0, by rw [h, hi0]; simp⟩
        · exact ⟨0, by rw [h, hi1]; simp⟩
        · exact ⟨ν, by rw [h, ← hAc l, ← hAc m]; exact hν⟩
        · exact ⟨1, by rw [h]; simp⟩
    · -- ===== Case B: exactly three nonzero forms =====
      have hrest : ∀ i, i ≠ i0 → A i ≠ 0 := fun i hne h => hex2 ⟨i, hne, h⟩
      obtain ⟨B3, hB3⟩ : ∃ B3 : Fin 3 → MvPolynomial (Fin 2) ℂ,
          ∀ j, B3 j = Ac (i0.succAbove j) := ⟨_, fun _ => rfl⟩
      obtain ⟨c3, hc3⟩ : ∃ c3 : Fin 3 → ℂ, ∀ j, c3 j = γ (i0.succAbove j) := ⟨_, fun _ => rfl⟩
      have hB30 : ∀ j, B3 j ≠ 0 := fun j => by
        rw [hB3 j]
        exact (hAceq _).not.mpr (hrest _ (Fin.succAbove_ne i0 j))
      have hc30 : ∀ j, c3 j ≠ 0 := fun j => by rw [hc3 j]; exact hγ0 _
      have hhomB3 : ∀ j, (B3 j).IsHomogeneous e := fun j => by
        rw [hB3 j]; exact hhomAc _
      have hcopB3 : NoCommonProjZero B3 := by
        intro v hv
        refine hcopAc v fun i => ?_
        by_cases h : i = i0
        · rw [h, hAc i0, hi0]; simp
        · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
          rw [← hj, ← hB3 j]
          exact hv j
      have hTi0 : T i0 = 0 := (hT0 i0).mpr ((hAceq i0).mpr hi0)
      have hsumB3 : ∑ j, MvPolynomial.C (c3 j) * B3 j ^ 13 = 0 := by
        have hsplit := Fin.sum_univ_succAbove T i0
        rw [hsumT, hTi0, zero_add] at hsplit
        simp only [hB3, hc3, ← hT]
        exact hsplit.symm
      have hsubB3 := no_vanishing_subsum_three
        (T := fun j => MvPolynomial.C (c3 j) * B3 j ^ 13)
        (fun j h => by
          rcases mul_eq_zero.mp h with h | h
          · exact hc30 j (MvPolynomial.C_eq_zero.mp h)
          · exact hB30 j (pow_eq_zero_iff (n := 13) (by norm_num) |>.mp h))
        hsumB3
      obtain ⟨μ, hμ⟩ := const_ratios_of_forms (r := 3) (by norm_num) (by norm_num)
        B3 c3 0 hB30 hc30 hhomB3 hcopB3 hsumB3 hsubB3
      refine isConstantFamily_of_map_ratios (j := i0.succAbove 0)
        (hrest _ (Fin.succAbove_ne i0 0)) fun i => ?_
      by_cases h : i = i0
      · exact ⟨0, by rw [h, hi0]; simp⟩
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
        refine ⟨μ j, ?_⟩
        rw [← hj, ← hAc _, ← hAc _, ← hB3 j, ← hB3 0]
        exact hμ j
  · -- all four forms are nonzero
    have hall : ∀ i, A i ≠ 0 := fun i h => hex ⟨i, h⟩
    have hAcall : ∀ i, Ac i ≠ 0 := fun i => (hAceq i).not.mpr (hall i)
    have hTne : ∀ i, T i ≠ 0 := fun i h => hAcall i ((hT0 i).mp h)
    by_cases hD : ∃ J : Finset (Fin 4), J.Nonempty ∧ J ≠ Finset.univ ∧ ∑ i ∈ J, T i = 0
    · -- ===== Case D: a proper sub-sum vanishes =====
      exfalso
      obtain ⟨J, hJne, hJuniv, hJ0⟩ := hD
      have hcompl : ∑ i ∈ Jᶜ, T i = 0 := by
        have hadd := Finset.sum_add_sum_compl J T
        rw [hJ0, hsumT] at hadd
        simpa using hadd
      have hcardJ : 1 ≤ J.card := Finset.card_pos.mpr hJne
      have hcard4 : J.card ≠ 4 := fun hh =>
        hJuniv (Finset.eq_univ_of_card J (by simpa using hh))
      have hJle : J.card ≤ 4 := by simpa using Finset.card_le_univ J
      have hcardc : Jᶜ.card = 4 - J.card := by simp [Finset.card_compl]
      have hno1 : ∀ K : Finset (Fin 4), ∑ i ∈ K, T i = 0 → K.card ≠ 1 := by
        intro K hK hc
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
        rw [hi, Finset.sum_singleton] at hK
        exact hTne i hK
      have hJ2 : J.card = 2 := by
        have h1 := hno1 J hJ0
        have h2 := hno1 Jᶜ hcompl
        omega
      obtain ⟨K, hKcard, hKsum, hK3⟩ :
          ∃ K : Finset (Fin 4), K.card = 2 ∧ ∑ i ∈ K, T i = 0 ∧ (3 : Fin 4) ∈ K := by
        by_cases h3 : (3 : Fin 4) ∈ J
        · exact ⟨J, hJ2, hJ0, h3⟩
        · exact ⟨Jᶜ, by omega, hcompl, Finset.mem_compl.mpr h3⟩
      obtain ⟨x, y, hxy, hKeq⟩ := Finset.card_eq_two.mp hKcard
      obtain ⟨i, hi3, hKi⟩ : ∃ i : Fin 4, i ≠ 3 ∧ K = {i, 3} := by
        rw [hKeq] at hK3
        simp only [Finset.mem_insert, Finset.mem_singleton] at hK3
        rcases hK3 with h | h
        · subst h
          exact ⟨y, fun hh => hxy hh.symm, hKeq.trans (Finset.pair_comm _ _)⟩
        · subst h
          exact ⟨x, hxy, hKeq⟩
      rw [hKi, Finset.sum_pair hi3, hT i, hT 3, hγ1 i hi3, hγ3] at hKsum
      have hpair : MvPolynomial.C (1 : ℂ) * Ac i ^ 13
          = MvPolynomial.C ((algebraMap ℚ ℂ) N) * Ac 3 ^ 13 := by
        rw [MvPolynomial.C_neg] at hKsum
        linear_combination hKsum
      have h13 : Ac i ^ 13 = MvPolynomial.C ((algebraMap ℚ ℂ) N) * Ac 3 ^ 13 := by
        have h := eq_C_mul_of_C_mul_eq (one_ne_zero (α := ℂ)) hpair
        rwa [div_one] at h
      obtain ⟨μ, hμ⟩ := pow13_ratio_const (hhomAc i) (hhomAc 3) (hAcall i) (hAcall 3) h13
      have hμ13 : MvPolynomial.C (μ ^ 13) * Ac 3 ^ 13
          = MvPolynomial.C ((algebraMap ℚ ℂ) N) * Ac 3 ^ 13 := by
        rw [← h13, hμ, mul_pow, MvPolynomial.C_pow]
      have hμN : μ ^ 13 = (algebraMap ℚ ℂ) N :=
        MvPolynomial.C_injective (Fin 2) ℂ
          (mul_right_cancel₀ (pow_ne_zero 13 (hAcall 3)) hμ13)
      obtain ⟨d, hd, -⟩ := descend_const_ratio (hall 3)
        (by rw [← hAc i, ← hAc 3]; exact hμ)
      refine hpow ⟨d, hφinj ?_⟩
      rw [map_pow, hd, hμN]
    · -- ===== Case A: four nonzero terms, no vanishing proper sub-sum =====
      have hsubC : ∀ J : Finset (Fin 4), J.Nonempty → J ≠ Finset.univ →
          ∑ i ∈ J, MvPolynomial.C (γ i) * Ac i ^ 13 ≠ 0 := by
        intro J h1 h2 hz
        refine hD ⟨J, h1, h2, ?_⟩
        simp only [hT]
        exact hz
      obtain ⟨μ, hμ⟩ := const_ratios_of_forms (r := 4) (by norm_num) (by norm_num)
        Ac γ 3 hAcall hγ0 hhomAc hcopAc hsumC hsubC
      refine isConstantFamily_of_map_ratios (j := 3) (hall 3) fun i => ?_
      exact ⟨μ i, by rw [← hAc i, ← hAc 3]; exact hμ i⟩

end Erdos477
