/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Toolbox.Poly
import EntropyBound.Proofs.ProfileSpeed.Bernstein

/-!
# Stage D — the profile speed bound `|g(s) - g(t)| ≤ (16/5) |u - v|` (`SKETCH.md` Step 4)

Hub module for the `ProfileSpeed` stage.  It imports

* `EntropyBound.Proofs.Toolbox.Poly` — B9: `Ppoly_pos` (#17), `Npoly_eq_deriv_form` (#18),
  `gprofile_sq_eq` (#19);
* `EntropyBound.Proofs.ProfileSpeed.Bernstein` — D1/D2: `Gpoly_bernstein_left` (#28),
  `Gpoly_bernstein_right` (#29), `Gpoly_pos` (#30);

and adds

* `gprofile_speed_le_proof`      (#31) — `|2 N(z) / √(P z)| ≤ 16/5` on `[0,1]` (D3), the
  derivative bound behind the Lipschitz constant `16/5`;
* `gprofile_hasDerivAt_proof`    (#20) — the chain rule for `u ↦ g(1 - u²)` on `(0,1)`.

The bridge for #20 is that on `(0,1)` the frozen `gprof (1 - u²) = 2 √((1-s) P s)|_{s = 1-u²}`
simplifies to `2 u √(P (1 - u²))`, because the radicand factors as `u² · P (1 - u²)` and
`√(u²) = u` for `u > 0`.  Since `HasDerivAt` is a local notion, the identity is transported
along `Set.Ioo 0 1 ∈ 𝓝 u` with `HasDerivAt.congr_of_eventuallyEq`; the frozen statement itself
is never restricted.
-/

namespace EntropyBound

namespace ProfileSpeed

/-- On `(0,1)` the profile at `1 - u²` has the closed form `2 u √(P (1 - u²))`. -/
theorem gprof_one_sub_sq (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    gprof (1 - u ^ 2) = 2 * u * Real.sqrt (Ppoly (1 - u ^ 2)) := by
  have hs : (1 - u ^ 2) ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hrad :
      (1 + (81 / 100) * (1 - (1 - u ^ 2)) ^ 2) *
          (1 - (1 - u ^ 2) ^ 2 * (1 + (81 / 100) * (1 - (1 - u ^ 2)) ^ 2))
        = u ^ 2 * Ppoly (1 - u ^ 2) := by
    rw [gprof_radicand_eq (1 - u ^ 2)]
    ring
  simp only [gprof]
  rw [hrad, Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu0.le]
  ring

/-- The scalar identity behind the chain rule: with `S = √P`, `S² = P` and `S ≠ 0`,
`2 S + 2u · (D · (-(2u)) / (2 S)) = 2 (P - u² D) / S`. -/
theorem speed_deriv_identity (u S P D : ℝ) (hS : S ≠ 0) (hsq : S ^ 2 = P) :
    2 * S + 2 * u * (D * (-(2 * u)) / (2 * S)) = 2 * (P - u ^ 2 * D) / S := by
  subst hsq
  field_simp
  ring

/-- The derivative of `u ↦ 2 u √(P (1 - u²))` on `(0,1)`, already in the frozen form
`2 N(1-u²) / √(P (1-u²))`. -/
theorem hasDerivAt_two_mul_sqrt (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun u : ℝ => 2 * u * Real.sqrt (Ppoly (1 - u ^ 2)))
      (2 * Npoly (1 - u ^ 2) / Real.sqrt (Ppoly (1 - u ^ 2))) u := by
  have hs : (1 - u ^ 2) ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  have hP : 0 < Ppoly (1 - u ^ 2) := Ppoly_pos_proof _ hs
  have hSpos : 0 < Real.sqrt (Ppoly (1 - u ^ 2)) := Real.sqrt_pos.mpr hP
  have hsq : Real.sqrt (Ppoly (1 - u ^ 2)) ^ 2 = Ppoly (1 - u ^ 2) := Real.sq_sqrt hP.le
  -- the inner map `u ↦ 1 - u²`
  have hinner : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
    simpa using (hasDerivAt_pow 2 u).const_sub (1 : ℝ)
  -- `Ppoly` at `1 - u²`, with the derivative written as `deriv Ppoly`
  have hPd : HasDerivAt Ppoly (deriv Ppoly (1 - u ^ 2)) (1 - u ^ 2) :=
    (hasDerivAt_Ppoly (1 - u ^ 2)).congr_deriv (deriv_Ppoly (1 - u ^ 2)).symm
  have hcomp := HasDerivAt.comp u hPd hinner
  rw [Function.comp_def] at hcomp
  have hsqrtd : HasDerivAt (fun u : ℝ => Real.sqrt (Ppoly (1 - u ^ 2)))
      (deriv Ppoly (1 - u ^ 2) * -(2 * u) / (2 * Real.sqrt (Ppoly (1 - u ^ 2)))) u :=
    hcomp.sqrt (ne_of_gt hP)
  have hlin : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have hmul := hlin.mul hsqrtd
  refine hmul.congr_deriv ?_
  have hNval : Npoly (1 - u ^ 2)
      = Ppoly (1 - u ^ 2) - u ^ 2 * deriv Ppoly (1 - u ^ 2) := by
    rw [Npoly_eq_deriv_form_proof (1 - u ^ 2)]
    ring
  rw [hNval]
  exact speed_deriv_identity u (Real.sqrt (Ppoly (1 - u ^ 2))) (Ppoly (1 - u ^ 2))
    (deriv Ppoly (1 - u ^ 2)) (ne_of_gt hSpos) hsq

end ProfileSpeed

/-! ### D3 — the derivative bound `|2 N / √P| ≤ 16/5` -/

theorem gprofile_speed_le_proof :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, |2 * Npoly z / Real.sqrt (Ppoly z)| ≤ 16 / 5 := by
  intro z hz
  have hP : 0 < Ppoly z := Ppoly_pos_proof z hz
  have hG : 0 < Gpoly z := Gpoly_pos_proof z hz
  have hS : 0 < Real.sqrt (Ppoly z) := Real.sqrt_pos.mpr hP
  have hsq : Real.sqrt (Ppoly z) ^ 2 = Ppoly z := Real.sq_sqrt hP.le
  have hN : 25 * Npoly z ^ 2 < 64 * Ppoly z := by
    simp only [Gpoly] at hG
    linarith
  have hb : (0 : ℝ) ≤ 16 / 5 * Real.sqrt (Ppoly z) := by positivity
  have hsquares : |2 * Npoly z| ^ 2 ≤ (16 / 5 * Real.sqrt (Ppoly z)) ^ 2 := by
    have hexp : (16 / 5 * Real.sqrt (Ppoly z)) ^ 2 = (256 / 25) * Ppoly z := by
      rw [mul_pow, hsq]; ring
    rw [sq_abs, hexp]
    nlinarith
  have hkey : |2 * Npoly z| ≤ 16 / 5 * Real.sqrt (Ppoly z) := by
    nlinarith [abs_nonneg (2 * Npoly z), hb, hsquares]
  rw [abs_div, abs_of_pos hS, div_le_iff₀ hS]
  exact hkey

/-! ### B9 (last item) — the chain rule for `u ↦ g(1 - u²)` -/

theorem gprofile_hasDerivAt_proof :
    ∀ u : ℝ, 0 < u → u < 1 →
      HasDerivAt (fun u => gprof (1 - u ^ 2))
        (2 * Npoly (1 - u ^ 2) / Real.sqrt (Ppoly (1 - u ^ 2))) u := by
  intro u hu0 hu1
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhds u := Ioo_mem_nhds hu0 hu1
  have heq : (fun u : ℝ => gprof (1 - u ^ 2))
      =ᶠ[nhds u] fun u : ℝ => 2 * u * Real.sqrt (Ppoly (1 - u ^ 2)) := by
    filter_upwards [hmem] with v hv using ProfileSpeed.gprof_one_sub_sq v hv.1 hv.2
  exact (ProfileSpeed.hasDerivAt_two_mul_sqrt u hu0 hu1).congr_of_eventuallyEq heq

end EntropyBound

namespace EntropyBound.Solution

theorem gprofile_speed_le :
    ∀ z ∈ Set.Icc (0 : ℝ) 1, |2 * Npoly z / Real.sqrt (Ppoly z)| ≤ 16 / 5 :=
  EntropyBound.gprofile_speed_le_proof

theorem gprofile_hasDerivAt :
    ∀ u : ℝ, 0 < u → u < 1 →
      HasDerivAt (fun u => gprof (1 - u ^ 2))
        (2 * Npoly (1 - u ^ 2) / Real.sqrt (Ppoly (1 - u ^ 2))) u :=
  EntropyBound.gprofile_hasDerivAt_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.gprofile_speed_le = @EntropyBound.Solution.gprofile_speed_le := rfl
example : @EntropyBound.gprofile_hasDerivAt = @EntropyBound.Solution.gprofile_hasDerivAt := rfl

end EntropyBound

/-! ### D4 — the Lipschitz bound `|g(s) - g(t)| ≤ (16/5) |√(1-s) - √(1-t)|`

The substitution `s = 1 - u²` turns the frozen statement into the assertion that
`φ : u ↦ g(1 - u²)` is `16/5`-Lipschitz on `[0,1]`, which is the mean value inequality
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` applied with the derivative
`φ' u = 2 N(1-u²)/√(P(1-u²))` of #20 and the bound `|φ'| ≤ 16/5` of #31.  Both are available
at the endpoints as well: on the *closed* interval the identity
`g(1 - u²) = 2 u √(P (1-u²))` holds for every `u ≥ 0` (only `√(u²) = u` is used), and the
right-hand side is differentiable wherever `P (1-u²) > 0`, which #17 guarantees for
`1 - u² ∈ [0,1]`.  Since the mean value inequality is symmetric in its two points, both
orderings `s ≤ t` and `t ≤ s` are covered simultaneously — no case is left to symmetry. -/

namespace EntropyBound

namespace ProfileSpeed

/-- The closed-form profile identity on the *closed* half line `u ≥ 0`; unlike
`gprof_one_sub_sq` this covers the endpoints `u = 0` and `u = 1`. -/
theorem gprof_one_sub_sq_of_nonneg (u : ℝ) (hu : 0 ≤ u) :
    gprof (1 - u ^ 2) = 2 * u * Real.sqrt (Ppoly (1 - u ^ 2)) := by
  have hrad :
      (1 + (81 / 100) * (1 - (1 - u ^ 2)) ^ 2) *
          (1 - (1 - u ^ 2) ^ 2 * (1 + (81 / 100) * (1 - (1 - u ^ 2)) ^ 2))
        = u ^ 2 * Ppoly (1 - u ^ 2) := by
    rw [gprof_radicand_eq (1 - u ^ 2)]
    ring
  simp only [gprof]
  rw [hrad, Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu]
  ring

/-- The derivative of `u ↦ 2 u √(P (1 - u²))`, needing only `1 - u² ∈ [0,1]` (so that
`P (1-u²) > 0`); this is the endpoint-inclusive version of `hasDerivAt_two_mul_sqrt`. -/
theorem hasDerivAt_psi (u : ℝ) (hmem : (1 - u ^ 2) ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ => 2 * u * Real.sqrt (Ppoly (1 - u ^ 2)))
      (2 * Npoly (1 - u ^ 2) / Real.sqrt (Ppoly (1 - u ^ 2))) u := by
  have hP : 0 < Ppoly (1 - u ^ 2) := Ppoly_pos_proof _ hmem
  have hSpos : 0 < Real.sqrt (Ppoly (1 - u ^ 2)) := Real.sqrt_pos.mpr hP
  have hsq : Real.sqrt (Ppoly (1 - u ^ 2)) ^ 2 = Ppoly (1 - u ^ 2) := Real.sq_sqrt hP.le
  have hinner : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-(2 * u)) u := by
    simpa using (hasDerivAt_pow 2 u).const_sub (1 : ℝ)
  have hPd : HasDerivAt Ppoly (deriv Ppoly (1 - u ^ 2)) (1 - u ^ 2) :=
    (hasDerivAt_Ppoly (1 - u ^ 2)).congr_deriv (deriv_Ppoly (1 - u ^ 2)).symm
  have hcomp := HasDerivAt.comp u hPd hinner
  rw [Function.comp_def] at hcomp
  have hsqrtd : HasDerivAt (fun u : ℝ => Real.sqrt (Ppoly (1 - u ^ 2)))
      (deriv Ppoly (1 - u ^ 2) * -(2 * u) / (2 * Real.sqrt (Ppoly (1 - u ^ 2)))) u :=
    hcomp.sqrt (ne_of_gt hP)
  have hlin : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have hmul := hlin.mul hsqrtd
  refine hmul.congr_deriv ?_
  have hNval : Npoly (1 - u ^ 2)
      = Ppoly (1 - u ^ 2) - u ^ 2 * deriv Ppoly (1 - u ^ 2) := by
    rw [Npoly_eq_deriv_form_proof (1 - u ^ 2)]
    ring
  rw [hNval]
  exact speed_deriv_identity u (Real.sqrt (Ppoly (1 - u ^ 2))) (Ppoly (1 - u ^ 2))
    (deriv Ppoly (1 - u ^ 2)) (ne_of_gt hSpos) hsq

/-- `u ∈ [0,1] → 1 - u² ∈ [0,1]`. -/
theorem one_sub_sq_mem (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    (1 - w ^ 2) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by nlinarith [hw.1, hw.2], by nlinarith [sq_nonneg w]⟩

/-- **The reparametrized Lipschitz estimate.**  `φ : u ↦ g(1 - u²)` is `16/5`-Lipschitz on
`[0,1]`; the mean value inequality treats the two points symmetrically, so no ordering
assumption is made on `u` and `v`. -/
theorem lipschitz_aux (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |gprof (1 - v ^ 2) - gprof (1 - u ^ 2)| ≤ 16 / 5 * |v - u| := by
  have hderiv : ∀ w ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun w : ℝ => gprof (1 - w ^ 2))
        (2 * Npoly (1 - w ^ 2) / Real.sqrt (Ppoly (1 - w ^ 2))) (Set.Icc (0 : ℝ) 1) w := by
    intro w hw
    refine ((hasDerivAt_psi w (one_sub_sq_mem w hw)).hasDerivWithinAt).congr ?_ ?_
    · intro y hy
      exact gprof_one_sub_sq_of_nonneg y hy.1
    · exact gprof_one_sub_sq_of_nonneg w hw.1
  have hbound : ∀ w ∈ Set.Icc (0 : ℝ) 1,
      ‖2 * Npoly (1 - w ^ 2) / Real.sqrt (Ppoly (1 - w ^ 2))‖ ≤ 16 / 5 := by
    intro w hw
    rw [Real.norm_eq_abs]
    exact gprofile_speed_le_proof _ (one_sub_sq_mem w hw)
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hu hv
  simpa [Real.norm_eq_abs] using h

end ProfileSpeed

theorem gprofile_lipschitz_proof :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |gprof s - gprof t| ≤ (16 / 5) * |Real.sqrt (1 - s) - Real.sqrt (1 - t)| := by
  intro s hs t ht
  have hs1 : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  have ht1 : (0 : ℝ) ≤ 1 - t := by linarith [ht.2]
  have hus : Real.sqrt (1 - s) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    have := Real.sqrt_le_sqrt (show (1 : ℝ) - s ≤ 1 by linarith [hs.1])
    simpa using this
  have hut : Real.sqrt (1 - t) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    have := Real.sqrt_le_sqrt (show (1 : ℝ) - t ≤ 1 by linarith [ht.1])
    simpa using this
  have hsq_s : 1 - (Real.sqrt (1 - s)) ^ 2 = s := by
    rw [Real.sq_sqrt hs1]; ring
  have hsq_t : 1 - (Real.sqrt (1 - t)) ^ 2 = t := by
    rw [Real.sq_sqrt ht1]; ring
  have h := ProfileSpeed.lipschitz_aux (Real.sqrt (1 - t)) hut (Real.sqrt (1 - s)) hus
  rw [hsq_s, hsq_t] at h
  exact h

end EntropyBound

namespace EntropyBound.Solution

theorem gprofile_lipschitz :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |gprof s - gprof t| ≤ (16 / 5) * |Real.sqrt (1 - s) - Real.sqrt (1 - t)| :=
  EntropyBound.gprofile_lipschitz_proof

end EntropyBound.Solution

namespace EntropyBound

example : @EntropyBound.gprofile_lipschitz = @EntropyBound.Solution.gprofile_lipschitz := rfl

end EntropyBound
