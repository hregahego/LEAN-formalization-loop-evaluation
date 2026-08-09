/-
# Stage A (part 2) — `Prob20/Proofs/Domain/Frac.lean`

Stage A items **A6**, the frozen-#2 half of **A4**, and **A8**:

* `D_isDomain_proof` (frozen #1) — `D` is a subring of the field `K`;
* `mem_Dom_iff_mem_max_or_sub_one_mem_max_proof` (frozen #2) and `max_le_Dom` —
  `D = 𝔽₂ + 𝔪`, by a two-case analysis on the constant `c : ZMod 2`;
* `D_isFractionRing_proof` (frozen #4) — every `x ∈ K` is `(π a)/(π s)` with
  `π a, π s ∈ 𝔪 ⊆ D`, which is exactly the `IsLocalization` characterisation.

The file closes with the non-degeneracy guardrail `example : tK ∉ Dom`, i.e. the
construction did **not** silently collapse `D` onto `T`.
-/
import Prob20.Defs

namespace Prob20

/-! ## Small helpers -/

/-- The image of `A = 𝔽₂[t]` in `K` lies inside `T` (take denominator `1`). -/
theorem frac_algebraMap_mem_T (a : A) : algebraMap A K a ∈ T :=
  ⟨a, 1, S.one_mem, by simp⟩

/-- `𝔽₂` has exactly two elements. -/
theorem frac_zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

/-- In `𝔽₂`, `1 + 1 = 0` (this is what kills `t + 1` at `t = 1`). -/
theorem frac_two_eq_zero : (1 + 1 : ZMod 2) = 0 := by decide

/-- `t + 1 ≠ 0` in `𝔽₂[t]`. -/
theorem frac_X_add_one_ne_zero : (Polynomial.X + 1 : A) ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp at h0

/-- `π = t(t+1) ≠ 0` in `𝔽₂[t]`. -/
theorem frac_piA_ne_zero : (piA : A) ≠ 0 := by
  simp only [piA, ne_eq, mul_eq_zero, not_or]
  exact ⟨Polynomial.X_ne_zero, frac_X_add_one_ne_zero⟩

/-- `π ≠ 0` in `K`. -/
theorem frac_piK_ne_zero : (piK : K) ≠ 0 := by
  simp only [piK, ne_eq, map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod 2))]
  exact frac_piA_ne_zero

/-! ## A6 — frozen #1 -/

/-- **Frozen #1.** `D` is an integral domain: it is a subring of the field `K`,
so it inherits `NoZeroDivisors` and `Nontrivial`. -/
theorem D_isDomain_proof : IsDomain ↥Dom := inferInstance

/-! ## A4 (the frozen #2 half) -/

/-- `𝔪 ⊆ D` (take the constant `c = 0`). -/
theorem max_le_Dom : ∀ x : K, x ∈ maxSet → x ∈ Dom := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨0, y, hy, by simp⟩

/-- **Frozen #2.** `D = 𝔽₂ + 𝔪`, i.e. `D/𝔪 ≅ 𝔽₂`: an element of `K` lies in `D`
exactly when it is congruent to `0` or to `1` modulo `𝔪`. -/
theorem mem_Dom_iff_mem_max_or_sub_one_mem_max_proof :
    ∀ x : K, x ∈ Dom ↔ (x ∈ maxSet ∨ x - 1 ∈ maxSet) := by
  intro x
  constructor
  · rintro ⟨c, y, hy, rfl⟩
    rcases frac_zmod_two_cases c with rfl | rfl
    · exact Or.inl ⟨y, hy, by simp⟩
    · exact Or.inr ⟨y, hy, by rw [map_one, pow_one]; ring⟩
  · rintro (hx | ⟨y, hy, hxy⟩)
    · exact max_le_Dom x hx
    · refine ⟨1, y, hy, ?_⟩
      rw [pow_one] at hxy
      rw [map_one]
      linear_combination hxy

/-! ## A8 — frozen #4 (`K = Frac(D)`) -/

/-- `π·a ∈ 𝔪 ⊆ D` for every `a ∈ A`: this is the source of enough denominators
inside `D` to generate all of `K`. -/
theorem frac_pi_mul_mem_Dom (a : A) : piK * algebraMap A K a ∈ Dom :=
  max_le_Dom _ ⟨algebraMap A K a, frac_algebraMap_mem_T a, by rw [pow_one]⟩

/-- Every `z : K` is a ratio of two elements of `A` with nonzero denominator. -/
theorem frac_num_denom (z : K) :
    ∃ a s : A, algebraMap A K s ≠ 0 ∧ z * algebraMap A K s = algebraMap A K a := by
  have hσ : algebraMap A K (RatFunc.denom z) ≠ 0 := by
    simpa only [ne_eq, map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod 2))] using
      RatFunc.denom_ne_zero z
  refine ⟨RatFunc.num z, RatFunc.denom z, hσ, ?_⟩
  have hcancel := div_mul_cancel₀ (algebraMap A K (RatFunc.num z)) hσ
  rwa [RatFunc.num_div_denom z] at hcancel

/-- An element of `D` that is nonzero in `K` is a nonzerodivisor of `D`. -/
theorem frac_coe_ne_zero {d : ↥Dom} (h : (d : K) ≠ 0) : d ∈ nonZeroDivisors ↥Dom := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  intro hd
  exact h (by rw [hd]; exact ZeroMemClass.coe_zero _)

/-- **Frozen #4.** `K = Frac(D)`, so `IntD` really is the textbook `Int(D)`.
Every `z : K` is `(π a)/(π s)` with `π a`, `π s ∈ 𝔪 ⊆ D` and `π s ≠ 0`. -/
theorem D_isFractionRing_proof : IsFractionRing ↥Dom K := by
  refine (isLocalization_iff (nonZeroDivisors ↥Dom) K).mpr ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    exact nonZeroDivisors.coe_ne_zero y (ZeroMemClass.coe_eq_zero.mp h)
  · intro z
    obtain ⟨a, s, hs, hz⟩ := frac_num_denom z
    have hne : piK * algebraMap A K s ≠ 0 := mul_ne_zero frac_piK_ne_zero hs
    refine ⟨⟨⟨piK * algebraMap A K a, frac_pi_mul_mem_Dom a⟩,
      ⟨⟨piK * algebraMap A K s, frac_pi_mul_mem_Dom s⟩, frac_coe_ne_zero hne⟩⟩, ?_⟩
    change z * (piK * algebraMap A K s) = piK * algebraMap A K a
    linear_combination piK * hz
  · intro x y h
    exact ⟨1, by rw [Subtype.coe_injective h]⟩

/-! ## Guardrail — `D` did not collapse onto `T` -/

/-- `t ∉ D`: if it were, `D` would be all of `T` and every frozen statement about
the counterexample would be false. -/
example : tK ∉ Dom := by
  rintro ⟨c, y, hy, hx⟩
  obtain ⟨b, s, hs, hb⟩ := hy
  simp only [tK, piK] at hx
  rcases frac_zmod_two_cases c with rfl | rfl
  · rw [map_zero, zero_add] at hx
    have key : (Polynomial.X : A) * s = piA * b := by
      apply RatFunc.algebraMap_injective (ZMod 2)
      simp only [map_mul]
      linear_combination (algebraMap A K s) * hx + (algebraMap A K piA) * hb
    have h1 := congrArg (Polynomial.eval 1) key
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, piA, Polynomial.eval_add,
      Polynomial.eval_one, frac_two_eq_zero, mul_zero, zero_mul] at h1
    exact hs.2 h1
  · rw [map_one] at hx
    have key : (Polynomial.X : A) * s = s + piA * b := by
      apply RatFunc.algebraMap_injective (ZMod 2)
      simp only [map_mul, map_add]
      linear_combination (algebraMap A K s) * hx + (algebraMap A K piA) * hb
    have h0 := congrArg (Polynomial.eval 0) key
    simp only [Polynomial.eval_mul, Polynomial.eval_X, zero_mul, piA, Polynomial.eval_add,
      Polynomial.eval_one, zero_add, mul_one, add_zero] at h0
    exact hs.1 h0.symm

end Prob20
