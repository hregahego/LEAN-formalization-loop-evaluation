/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems

/-!
# Stage B, item B9 — the profile polynomials `P`, `N` and the profile `g` (`SKETCH.md` (2i))

This file discharges the three polynomial/profile obligations of `BLUEPRINT.md` Stage B9
that Stage D depends on:

* `Ppoly_pos_proof`            (#17) — `0 < P z` on `[0,1]`;
* `Npoly_eq_deriv_form_proof`  (#18) — `N = P - (1-z) P'` for **all** real `z`;
* `gprofile_sq_eq_proof`       (#19) — `g(s)^2 = 4 (1-s) P s` on `[0,1]`.

The key algebraic fact, used twice, is the factorization

`1 - s^2 (1 + (81/100)(1-s)^2) = (1-s) (1 + s - (81/100) s^2 (1-s))`,

which turns `gprof`'s radicand into `(1-s) * Ppoly s`.

Support lemmas live in `namespace EntropyBound.ProfileSpeed` (this file is owned by the
Stage D worker; `Toolbox/Basic.lean` belongs to the Stage B worker).
-/

namespace EntropyBound

open Real

namespace ProfileSpeed

/-! ### The power basis of `Ppoly` and its derivative -/

/-- `Ppoly` in the power basis: the product of the two factors of `Defs.lean` D14 expands to
`181/100 + (19/100) z - (22761/10000) z^2 + (35883/10000) z^3 - (19683/10000) z^4
+ (6561/10000) z^5`. -/
theorem Ppoly_eq_powerBasis :
    Ppoly = fun z : ℝ =>
      181 / 100 + (19 / 100) * z - (22761 / 10000) * z ^ 2 + (35883 / 10000) * z ^ 3
        - (19683 / 10000) * z ^ 4 + (6561 / 10000) * z ^ 5 := by
  funext z
  simp only [Ppoly]
  ring

/-- The derivative of `Ppoly`, as a `HasDerivAt` statement valid at every real point. -/
theorem hasDerivAt_Ppoly (z : ℝ) :
    HasDerivAt Ppoly
      (19 / 100 - (45522 / 10000) * z + (107649 / 10000) * z ^ 2 - (78732 / 10000) * z ^ 3
        + (32805 / 10000) * z ^ 4) z := by
  have h1 : HasDerivAt (fun z : ℝ => z) 1 z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have h3 : HasDerivAt (fun z : ℝ => z ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have h4 : HasDerivAt (fun z : ℝ => z ^ 4) (4 * z ^ 3) z := by
    simpa using hasDerivAt_pow 4 z
  have h5 : HasDerivAt (fun z : ℝ => z ^ 5) (5 * z ^ 4) z := by
    simpa using hasDerivAt_pow 5 z
  have key :=
    ((((((hasDerivAt_const z (181 / 100 : ℝ)).add
      (h1.const_mul (19 / 100 : ℝ))).sub
      (h2.const_mul (22761 / 10000 : ℝ))).add
      (h3.const_mul (35883 / 10000 : ℝ))).sub
      (h4.const_mul (19683 / 10000 : ℝ))).add
      (h5.const_mul (6561 / 10000 : ℝ)))
  rw [Ppoly_eq_powerBasis]
  exact key.congr_deriv (by ring)

/-- The derivative of `Ppoly` in closed form. -/
theorem deriv_Ppoly (z : ℝ) :
    deriv Ppoly z =
      19 / 100 - (45522 / 10000) * z + (107649 / 10000) * z ^ 2 - (78732 / 10000) * z ^ 3
        + (32805 / 10000) * z ^ 4 :=
  (hasDerivAt_Ppoly z).deriv

/-! ### The factorization of `gprof`'s radicand -/

/-- The algebraic identity behind `gprofile_sq_eq`:
`1 - s^2 (1 + (81/100)(1-s)^2) = (1-s) (1 + s - (81/100) s^2 (1-s))`, hence the whole
radicand of `gprof` equals `(1-s) * Ppoly s`. -/
theorem gprof_radicand_eq (s : ℝ) :
    (1 + (81 / 100) * (1 - s) ^ 2) * (1 - s ^ 2 * (1 + (81 / 100) * (1 - s) ^ 2))
      = (1 - s) * Ppoly s := by
  simp only [Ppoly]
  ring

end ProfileSpeed

/-! ### The frozen theorems of B9 -/

theorem Ppoly_pos_proof : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < Ppoly z := by
  intro z hz
  obtain ⟨h0, h1⟩ := hz
  have hA : (1 : ℝ) ≤ 1 + (81 / 100) * (1 - z) ^ 2 := by nlinarith [sq_nonneg (1 - z)]
  have hB : (1 : ℝ) ≤ 1 + z - (81 / 100) * z ^ 2 * (1 - z) := by
    nlinarith [sq_nonneg z, mul_nonneg h0 (sub_nonneg.mpr h1)]
  simp only [Ppoly]
  nlinarith

theorem Npoly_eq_deriv_form_proof :
    ∀ z : ℝ, Npoly z = Ppoly z - (1 - z) * deriv Ppoly z := by
  intro z
  rw [ProfileSpeed.deriv_Ppoly z]
  simp only [Npoly, Ppoly]
  ring

theorem gprofile_sq_eq_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, (gprof s) ^ 2 = 4 * (1 - s) * Ppoly s := by
  intro s hs
  have hP : 0 < Ppoly s := Ppoly_pos_proof s hs
  have h1 : s ≤ 1 := hs.2
  have hnn : 0 ≤ (1 + (81 / 100) * (1 - s) ^ 2) * (1 - s ^ 2 * (1 + (81 / 100) * (1 - s) ^ 2)) := by
    rw [ProfileSpeed.gprof_radicand_eq s]
    exact mul_nonneg (by linarith) hP.le
  simp only [gprof]
  rw [mul_pow, Real.sq_sqrt hnn, ProfileSpeed.gprof_radicand_eq s]
  ring

end EntropyBound

namespace EntropyBound.Solution

theorem Ppoly_pos : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < Ppoly z := EntropyBound.Ppoly_pos_proof

theorem Npoly_eq_deriv_form : ∀ z : ℝ, Npoly z = Ppoly z - (1 - z) * deriv Ppoly z :=
  EntropyBound.Npoly_eq_deriv_form_proof

theorem gprofile_sq_eq :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, (gprof s) ^ 2 = 4 * (1 - s) * Ppoly s :=
  EntropyBound.gprofile_sq_eq_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.Ppoly_pos = @EntropyBound.Solution.Ppoly_pos := rfl
example : @EntropyBound.Npoly_eq_deriv_form = @EntropyBound.Solution.Npoly_eq_deriv_form := rfl
example : @EntropyBound.gprofile_sq_eq = @EntropyBound.Solution.gprofile_sq_eq := rfl

end EntropyBound
