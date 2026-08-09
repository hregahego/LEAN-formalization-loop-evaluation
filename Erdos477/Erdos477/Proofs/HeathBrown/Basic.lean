import Erdos477.Defs

/-!
# Stage D — the Heath-Brown bridge (general axiom → diagonal count, SKETCH §3)

`SKETCH.md` §3 recommends assuming the specialized diagonal count as an axiom.
`USER_NOTES.md` **revokes** that advice: the axiom is the general Theorem 2.2
(`Erdos477.heath_brown_diagonal_13`, `Erdos477/Defs.lean:147`) and the
specialization is a proof obligation.  This file discharges it, following
`BLUEPRINT.md` §"Stage D" steps D1–D5:

* **D1** `diagForm := X₀¹³ + X₁¹³ + X₂¹³`, with `diagForm_isHomogeneous` and
  `diagForm_nonsingular`.
* **D2** `eval_diagForm` / `aeval_diagForm`.
* **D3** `not_liesOnPolyParam_of_hexcl` — under the exclusion hypothesis no
  integer point lies on a nonconstant parametrization of degree ≤ `⌊13/10⌋ = 1`.
* **D4** `hbSolutions_eq_diagSolutions` — the *explicit* transport between
  `Set (Fin 3 → ℤ)` and `Set (ℤ × ℤ × ℤ)`.
* **D5** `hb_diagonal_count_proof` — apply the axiom at `A := 1` for `X ≥ |M|`
  and absorb the bounded range `1 ≤ X < |M|` into the constant.

No sign normalization `ε_c` is needed: the axiom as transcribed takes an
arbitrary nonzero `N`, so the paper's `ε_c = sgn(−c)` disappears entirely.
-/

namespace Erdos477

open scoped Classical

open MvPolynomial Polynomial

/-! ## D1 — the diagonal form -/

/-- The diagonal ternary form `X₀¹³ + X₁¹³ + X₂¹³`. -/
noncomputable def diagForm : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.X 0 ^ 13 + MvPolynomial.X 1 ^ 13 + MvPolynomial.X 2 ^ 13

lemma diagForm_isHomogeneous : diagForm.IsHomogeneous 13 := by
  have h : ∀ i : Fin 3,
      ((MvPolynomial.X i : MvPolynomial (Fin 3) ℤ) ^ 13).IsHomogeneous 13 := by
    intro i
    simpa using (MvPolynomial.isHomogeneous_X (R := ℤ) i).pow 13
  exact ((h 0).add (h 1)).add (h 2)

/-! ## D2 — evaluation -/

lemma eval_diagForm (x : Fin 3 → ℤ) :
    MvPolynomial.eval x diagForm = x 0 ^ 13 + x 1 ^ 13 + x 2 ^ 13 := by
  simp [diagForm]

lemma aeval_diagForm {A : Type*} [CommRing A] [Algebra ℤ A] (p : Fin 3 → A) :
    MvPolynomial.aeval p diagForm = p 0 ^ 13 + p 1 ^ 13 + p 2 ^ 13 := by
  simp [diagForm]

/-- The partial derivatives of the diagonal form: `∂ᵢ = 13 · Xᵢ¹²`. -/
lemma pderiv_diagForm (i : Fin 3) :
    MvPolynomial.pderiv i diagForm = 13 * MvPolynomial.X i ^ 12 := by
  fin_cases i <;> simp [diagForm]

/-- **D1**, the content: the gradient of `diagForm` vanishes only at the origin
    of `ℂ³`.  Proved from `13 · zᵢ¹² = 0` and `(13 : ℂ) ≠ 0`, never by `decide`
    and never by inspecting finitely many `z`. -/
lemma diagForm_nonsingular : IsNonsingularTernaryForm diagForm 13 := by
  refine ⟨diagForm_isHomogeneous, ?_⟩
  intro z hz
  funext i
  have h := hz i
  rw [pderiv_diagForm i] at h
  simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_ofNat] at h
  have h12 : z i ^ 12 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  simpa using pow_eq_zero_iff (n := 12) (by norm_num) |>.mp h12

/-! ## D3 — the exclusion hypothesis kills every degree-≤1 parametrization -/

/-- `⌊13/10⌋ = 1`, so the axiom's `k / 10` really is `1`. -/
lemma thirteen_div_ten : (13 : ℕ) / 10 = 1 := by norm_num

/-- **D3.**  Under the exclusion hypothesis of `hb_diagonal_count`, *no* integer
    point lies on a nonconstant polynomial parametrization of degree ≤ 1. -/
lemma not_liesOnPolyParam_of_hexcl {M : ℤ}
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0)
    (x : Fin 3 → ℤ) : ¬ LiesOnPolyParam diagForm M 1 x := by
  rintro ⟨p, hnc, hdeg, hid, -⟩
  rw [aeval_diagForm] at hid
  obtain ⟨h0, h1, h2⟩ := hexcl (p 0) (p 1) (p 2) hid (hdeg 0) (hdeg 1) (hdeg 2)
  exact hnc (by intro i; fin_cases i <;> assumption)

/-! ## D4 — the `Fin 3 → ℤ` / `ℤ × ℤ × ℤ` transport -/

/-- The explicit transport map `(x, y, z) ↦ ![x, y, z]`. -/
def toFin3 (v : ℤ × ℤ × ℤ) : Fin 3 → ℤ := ![v.1, v.2.1, v.2.2]

lemma toFin3_injective : Function.Injective toFin3 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [toFin3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- **D4.**  With D3 in force, `hbSolutions diagForm M 1 X` is exactly the image
    of `diagSolutions M X` under `toFin3`.  Done by hand — the two sets live in
    genuinely different types (`PROGRESS.md` decision 4 of 2026-08-09T00:25:44Z). -/
lemma hbSolutions_image_diagSolutions {M : ℤ}
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0)
    (X : ℝ) : hbSolutions diagForm M 1 X = toFin3 '' diagSolutions M X := by
  ext x
  simp only [hbSolutions, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨heq, hbox, -⟩
    refine ⟨(x 0, x 1, x 2), ⟨?_, hbox 0, hbox 1, hbox 2⟩, ?_⟩
    · simpa [eval_diagForm] using heq
    · funext i; fin_cases i <;> simp [toFin3]
  · rintro ⟨⟨a, b, c⟩, ⟨heq, ha, hb, hc⟩, rfl⟩
    refine ⟨?_, ?_, not_liesOnPolyParam_of_hexcl hexcl _⟩
    · simpa [eval_diagForm, toFin3] using heq
    · intro i; fin_cases i <;> simpa [toFin3]

/-- **D4**, the cardinality form. -/
lemma hbSolutions_eq_diagSolutions {M : ℤ}
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0)
    (X : ℝ) : (diagSolutions M X).ncard = (hbSolutions diagForm M 1 X).ncard := by
  rw [hbSolutions_image_diagSolutions hexcl X,
    Set.ncard_image_of_injective _ toFin3_injective]

/-! ## D5 — the bounded range, and the theorem -/

/-- The finite box `[−|M|, |M|]³` that contains every solution once `X ≤ |M|`. -/
noncomputable def boxFinset (M : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-|M|) |M|) ×ˢ (Finset.Icc (-|M|) |M|) ×ˢ (Finset.Icc (-|M|) |M|)

/-- For `X ≤ |M|` the diagonal count is bounded by a constant depending only on
    `M`: every coordinate lies in `[−|M|, |M|]`. -/
lemma diagSolutions_ncard_le_box (M : ℤ) {X : ℝ} (hX : X ≤ |(M : ℝ)|) :
    (diagSolutions M X).ncard ≤ (boxFinset M).card := by
  have hsub : diagSolutions M X ⊆ ↑(boxFinset M) := by
    rintro ⟨a, b, c⟩ ⟨-, ha, hb, hc⟩
    have key : ∀ n : ℤ, |(n : ℝ)| ≤ X → n ∈ Finset.Icc (-|M|) |M| := by
      intro n hn
      have : ((|n| : ℤ) : ℝ) ≤ ((|M| : ℤ) : ℝ) := by
        push_cast
        exact hn.trans hX
      have : |n| ≤ |M| := by exact_mod_cast this
      rw [Finset.mem_Icc]
      exact ⟨(abs_le.mp this).1, (abs_le.mp this).2⟩
    simp only [boxFinset, Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨key a ha, key b hb, key c hc⟩
  calc (diagSolutions M X).ncard
      ≤ (↑(boxFinset M) : Set (ℤ × ℤ × ℤ)).ncard :=
        Set.ncard_le_ncard hsub (boxFinset M).finite_toSet
    _ = (boxFinset M).card := Set.ncard_coe_finset _

/-- **Stage D / SKETCH §3** — the sketch's "AXIOM HB", here a THEOREM derived
    from the general `Erdos477.heath_brown_diagonal_13`.  Type character-identical
    to the frozen `Erdos477.hb_diagonal_count` (`Erdos477/Theorems.lean:84-90`). -/
theorem hb_diagonal_count_proof (M : ℤ) (hM : M ≠ 0)
    (hexcl : ∀ p₁ p₂ p₃ : Polynomial ℤ,
      p₁ ^ 13 + p₂ ^ 13 + p₃ ^ 13 = Polynomial.C M →
      p₁.natDegree ≤ 1 → p₂.natDegree ≤ 1 → p₃.natDegree ≤ 1 →
      p₁.natDegree = 0 ∧ p₂.natDegree = 0 ∧ p₃.natDegree = 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ((diagSolutions M X).ncard : ℝ) ≤ K * X ^ ((10 : ℝ) / 13) := by
  obtain ⟨C, hCpos, hC⟩ :=
    heath_brown_diagonal_13 diagForm 13 (by norm_num) diagForm_nonsingular 1 one_pos
  refine ⟨max 1 (max C ((boxFinset M).card : ℝ)), le_max_left _ _, ?_⟩
  intro X hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hpow : (1 : ℝ) ≤ X ^ ((10 : ℝ) / 13) :=
    Real.one_le_rpow hX (by norm_num)
  have hpow0 : (0 : ℝ) ≤ X ^ ((10 : ℝ) / 13) := le_trans zero_le_one hpow
  rcases le_or_gt (|(M : ℝ)|) (1 * X) with hcase | hcase
  · -- the main range: the axiom applies
    have h := hC M hM X hX hcase
    rw [thirteen_div_ten] at h
    rw [hbSolutions_eq_diagSolutions hexcl X]
    refine h.trans (mul_le_mul ?_ (le_of_eq ?_) ?_ ?_)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · norm_num
    · rw [show ((10 : ℝ) / ((13 : ℕ) : ℝ)) = (10 : ℝ) / 13 by norm_num]
      exact hpow0
    · exact le_trans zero_le_one (le_max_left _ _)
  · -- the bounded range `1 ≤ X < |M|`: absorbed into the constant
    have hle : X ≤ |(M : ℝ)| := le_of_lt (by linarith)
    have hbox := diagSolutions_ncard_le_box M hle
    have h1 : ((diagSolutions M X).ncard : ℝ) ≤ ((boxFinset M).card : ℝ) := by
      exact_mod_cast hbox
    have h2 : ((boxFinset M).card : ℝ) ≤ max 1 (max C ((boxFinset M).card : ℝ)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    calc ((diagSolutions M X).ncard : ℝ)
        ≤ max 1 (max C ((boxFinset M).card : ℝ)) := h1.trans h2
      _ ≤ max 1 (max C ((boxFinset M).card : ℝ)) * X ^ ((10 : ℝ) / 13) := by
          nlinarith [le_max_left (1 : ℝ) (max C ((boxFinset M).card : ℝ))]

/-! ## Guardrail `example`s (BLUEPRINT Stage D cheat-watch box) -/

example : (13 : ℕ) / 10 = 1 := by norm_num

example : MvPolynomial.eval ![1, 1, 1] diagForm = 3 := by
  rw [eval_diagForm]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

example : IsNonsingularTernaryForm diagForm 13 := diagForm_nonsingular

end Erdos477
