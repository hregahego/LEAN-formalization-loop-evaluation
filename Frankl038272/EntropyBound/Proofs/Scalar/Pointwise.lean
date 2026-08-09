/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems

/-!
# Stage H item H4 — `scalar_inequality` (#47) in hypothesis form, plus Stage H support lemmas

`BLUEPRINT.md` Part 2 Stage H item H4, `SKETCH.md` Step 8 (8c).

This file is imported FROM `EntropyBound/Proofs/Scalar/Basic.lean` (which is the module the
root `EntropyBound.lean` reaches), so it must NOT import `Scalar/Basic.lean` itself.  It
therefore holds exactly the part of Stage H that does not need `Phi_decomposition` (#45):

* the two support lemmas `EntropyBound.Scalar.Hnat_zero` and
  `EntropyBound.Scalar.mul_enat_eq_Hnat` (used by item H3 in `Scalar/Basic.lean`);
* item **H4**, `EntropyBound.Scalar.scalar_inequality_of`, whose only hypothesis `hpt` is the
  frozen statement of `pointwise_inequality` (#46) VERBATIM and whose conclusion is the frozen
  statement of `scalar_inequality` (#47) VERBATIM.

The mathematics of (8c) is: apply `hpt` at `(S i, S j)`, weight by `wᵢwⱼ ≥ 0`, sum over
`i, j` and divide by `2`.  The three algebraic facts are `Finset.sum_mul_sum` for
`∑ᵢ∑ⱼ wᵢwⱼ Sᵢ Hₙₐₜ(Sⱼ) = (∑ wS)(∑ w Hₙₐₜ S)`, the same for the `g`-term, and the symmetry of
`s Hₙₐₜ t + t Hₙₐₜ s` under swapping `i, j` (which here is visible directly: the two halves of
the left-hand double sum are the two orders of the same product of single sums).

Note `hw1 : ∑ i, w i = 1` is genuinely unnecessary — both sides are homogeneous of degree `2`
in `w` — but it is a frozen hypothesis, so it is kept and absorbed by `have _hw1 := hw1` to
keep the `unusedVariables` linter quiet.
-/

namespace EntropyBound.Scalar

open EntropyBound

/-! ### Support lemmas -/

/-- `Hnat` vanishes at `0`: `-0 * log 0 - 1 * log 1 = 0`. -/
theorem Hnat_zero : Hnat 0 = 0 := by
  simp [Hnat]

/-- The defining relation between `enat` and `Hnat`, away from the junk value at `0`. -/
theorem mul_enat_eq_Hnat (z : ℝ) (hz : z ≠ 0) : z * enat z = Hnat z := by
  simp only [enat]
  field_simp

/-! ### H4 — the scalar inequality (#47), in `hpt` form -/

/-- **H4.**  With `hpt` the frozen statement of `pointwise_inequality` (#46), the conclusion is
the frozen statement of `scalar_inequality` (#47), VERBATIM: an ARBITRARY `Fintype ι`, an
arbitrary nonnegative weight vector `w` summing to `1`, and an arbitrary `S` with values in
`[0,1]`.  No positivity is assumed of `w i`, and no positivity of `S i` (the `S i = 0` case is
covered by `hpt`, which lives on the closed square). -/
theorem scalar_inequality_of
    (hpt : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Cval * (s * Hnat t + t * Hnat s)
        ≤ 2 * ((9 / 10) * Hnat (s * t)
          + (Real.log 2 / 10) * (s * t * gprof s * gprof t)))
    {ι : Type} [Fintype ι] (w S : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hS : ∀ i, S i ∈ Set.Icc (0 : ℝ) 1) :
    Cval * (∑ i, w i * S i) * (∑ i, w i * Hnat (S i))
      ≤ (9 / 10) * (∑ i, ∑ j, w i * w j * Hnat (S i * S j))
        + (Real.log 2 / 10) * (∑ i, w i * (S i * gprof (S i))) ^ 2 := by
  have _hw1 := hw1
  -- the pointwise inequality at `(S i, S j)`, weighted by `w i * w j ≥ 0`
  have key : ∀ i j : ι,
      w i * w j * (Cval * (S i * Hnat (S j) + S j * Hnat (S i)))
        ≤ w i * w j * (2 * ((9 / 10) * Hnat (S i * S j)
            + (Real.log 2 / 10) * (S i * S j * gprof (S i) * gprof (S j)))) := fun i j =>
    mul_le_mul_of_nonneg_left (hpt (S i) (hS i) (S j) (hS j)) (mul_nonneg (hw i) (hw j))
  have hsum :
      (∑ i, ∑ j, w i * w j * (Cval * (S i * Hnat (S j) + S j * Hnat (S i))))
        ≤ ∑ i, ∑ j, w i * w j * (2 * ((9 / 10) * Hnat (S i * S j)
            + (Real.log 2 / 10) * (S i * S j * gprof (S i) * gprof (S j)))) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
  -- regroup both double sums into products of single sums
  have hsplitL :
      (∑ i, ∑ j, w i * w j * (Cval * (S i * Hnat (S j) + S j * Hnat (S i))))
        = Cval * ∑ i, ∑ j, (w i * S i) * (w j * Hnat (S j))
          + Cval * ∑ i, ∑ j, (w i * Hnat (S i)) * (w j * S j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsplitR :
      (∑ i, ∑ j, w i * w j * (2 * ((9 / 10) * Hnat (S i * S j)
          + (Real.log 2 / 10) * (S i * S j * gprof (S i) * gprof (S j)))))
        = (9 / 5) * ∑ i, ∑ j, w i * w j * Hnat (S i * S j)
          + (Real.log 2 / 5)
            * ∑ i, ∑ j, (w i * (S i * gprof (S i))) * (w j * (S j * gprof (S j))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hAB : (∑ i, ∑ j, (w i * S i) * (w j * Hnat (S j)))
      = (∑ i, w i * S i) * (∑ j, w j * Hnat (S j)) := by
    rw [Finset.sum_mul_sum]
  have hBA : (∑ i, ∑ j, (w i * Hnat (S i)) * (w j * S j))
      = (∑ i, w i * Hnat (S i)) * (∑ j, w j * S j) := by
    rw [Finset.sum_mul_sum]
  have hDD : (∑ i, ∑ j, (w i * (S i * gprof (S i))) * (w j * (S j * gprof (S j))))
      = (∑ i, w i * (S i * gprof (S i))) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [hsplitL, hsplitR, hAB, hBA, hDD] at hsum
  linarith

end EntropyBound.Scalar
