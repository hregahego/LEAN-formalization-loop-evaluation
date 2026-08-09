/-
# Stage A7 — `D` is a local ring with maximal ideal `𝔪`

This module implements BLUEPRINT Part 2 Stage A item **A7**, i.e. the frozen
statement #3 of `Prob20/Theorems.lean`.

The crux is elementary: if `x ∈ D` and `x ∉ 𝔪`, then `x - 1 ∈ 𝔪` (frozen #2), and
`x` misses both primes `𝔫₀`, `𝔫₁` of `T` (Stage A's
`mem_max_of_mem_Dom_of_mem_n0` / `_n1`), so writing `x = a/s` with `s ∈ S` the
numerator `a` itself lies in `S` and `x⁻¹ = s/a ∈ T`.  Then
`x⁻¹ - 1 = -(x⁻¹ · (x - 1)) ∈ 𝔪` because `𝔪` is a `T`-submodule, so `x⁻¹ ∈ D` by
frozen #2 again and `x` is a unit of `D`.  Nothing here uses any structure theory
of `T` (no PID / Dedekind / Noetherian / Krull dimension) — only divisibility in
`𝔽₂[t]`.

Support lemmas that are not named by the blueprint are prefixed `loc_`.
-/
import Prob20.Defs
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac

namespace Prob20

/-! ### Elementary facts about `𝔪` -/

/-- `𝔪ʲ` absorbs multiplication by elements of `T` (it is a `↥T`-submodule of `K`). -/
theorem loc_mul_mem_maxPow {j : ℕ} {c x : K} (hc : c ∈ T) (hx : x ∈ maxPow j) :
    c * x ∈ maxPow j :=
  Submodule.smul_mem _ (⟨c, hc⟩ : ↥T) hx

/-- `1 ∉ 𝔪`: the maximal ideal is proper.  (Same script as the guardrail `example` in
`Prob20/Proofs/Domain/Basic.lean`; reproved here as a named lemma.) -/
theorem loc_one_not_mem_max : (1 : K) ∉ maxSet := by
  intro h
  have h2 : algebraMap A K 1 * (algebraMap A K 1)⁻¹ ∈ maxPow 1 := by simpa using h
  rw [mem_maxPow_iff 1 1 S.one_mem 1, pow_one] at h2
  have h3 : (Polynomial.X : A) ∣ 1 := dom_X_dvd_piA.trans h2
  rw [dom_X_dvd_iff] at h3
  simp only [Polynomial.eval_one] at h3
  exact one_ne_zero h3

/-- An element outside `𝔪` is nonzero. -/
theorem loc_ne_zero_of_not_mem_max {x : K} (h : x ∉ maxSet) : x ≠ 0 := by
  rintro rfl
  exact h (Submodule.zero_mem _)

/-! ### The crux: `x ∈ D`, `x ∉ 𝔪` implies `x⁻¹ ∈ D` -/

/-- If `x ∈ D` lies outside `𝔪` then `x` misses both primes of `T`, so its numerator lies
in `S` and `x⁻¹ ∈ T`. -/
theorem loc_inv_mem_T (x : K) (hx : x ∈ Dom) (hnm : x ∉ maxSet) : x⁻¹ ∈ T := by
  have hn0 : ¬ mem_n0 x := fun h => hnm (mem_max_of_mem_Dom_of_mem_n0 x hx h)
  have hn1 : ¬ mem_n1 x := fun h => hnm (mem_max_of_mem_Dom_of_mem_n1 x hx h)
  obtain ⟨a, s, hs, rfl⟩ := dom_eq_div_of_mem_T (Dom_le_T hx)
  rw [dom_mem_n0_iff a s hs] at hn0
  rw [dom_mem_n1_iff a s hs] at hn1
  have ha : a ∈ S := (mem_S_iff_not_dvd a).2 ⟨hn0, hn1⟩
  have hrw : (algebraMap A K a * (algebraMap A K s)⁻¹)⁻¹
      = algebraMap A K s * (algebraMap A K a)⁻¹ := by
    rw [mul_inv, inv_inv, mul_comm]
  rw [hrw]
  exact T.mul_mem (algebraMap_mem_T s) (inv_algebraMap_mem_T a ha)

/-- The key computation: `x ∈ D` with `x ∉ 𝔪` has its inverse back in `D`, because
`x⁻¹ - 1 = -(x⁻¹ · (x - 1))` and `𝔪` is a `T`-submodule. -/
theorem loc_inv_mem_Dom (x : K) (hx : x ∈ Dom) (hnm : x ∉ maxSet) : x⁻¹ ∈ Dom := by
  have hxne : x ≠ 0 := loc_ne_zero_of_not_mem_max hnm
  have hinvT : x⁻¹ ∈ T := loc_inv_mem_T x hx hnm
  have hw : x - 1 ∈ maxSet :=
    ((mem_Dom_iff_mem_max_or_sub_one_mem_max_proof x).1 hx).resolve_left hnm
  have key : x⁻¹ - 1 = -(x⁻¹ * (x - 1)) := by
    field_simp
    ring
  rw [mem_Dom_iff_mem_max_or_sub_one_mem_max_proof, key]
  exact Or.inr (Submodule.neg_mem _ (loc_mul_mem_maxPow hinvT hw))

/-- The units of `D` are exactly the elements outside `𝔪`. -/
theorem loc_isUnit_iff (d : ↥Dom) : IsUnit d ↔ (d : K) ∉ maxSet := by
  constructor
  · intro hu hmem
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 hu
    have hcoe : (d : K) * (e : K) = 1 := by
      have := congrArg (fun z : ↥Dom => (z : K)) he
      simpa using this
    have : (1 : K) ∈ maxSet := by
      rw [← hcoe, mul_comm]
      exact loc_mul_mem_maxPow (Dom_le_T e.2) hmem
    exact loc_one_not_mem_max this
  · intro h
    have hinv : (d : K)⁻¹ ∈ Dom := loc_inv_mem_Dom (d : K) d.2 h
    refine isUnit_iff_exists_inv.2 ⟨⟨(d : K)⁻¹, hinv⟩, Subtype.ext ?_⟩
    change (d : K) * (d : K)⁻¹ = 1
    exact mul_inv_cancel₀ (loc_ne_zero_of_not_mem_max h)

/-! ### A7 — frozen #3 -/

/-- **Frozen #3.** `D` is a local ring, and its maximal ideal is exactly `maxD` (= `𝔪`). -/
theorem D_isLocalRing_proof :
    ∃ h : IsLocalRing ↥Dom, @IsLocalRing.maximalIdeal ↥Dom _ h = maxD := by
  haveI hloc : IsLocalRing ↥Dom := by
    refine IsLocalRing.of_nonunits_add ?_
    intro a b ha hb hab
    have ha' : (a : K) ∈ maxSet := not_not.1 fun h => ha ((loc_isUnit_iff a).2 h)
    have hb' : (b : K) ∈ maxSet := not_not.1 fun h => hb ((loc_isUnit_iff b).2 h)
    refine (loc_isUnit_iff (a + b)).1 hab ?_
    rw [Subring.coe_add]
    exact Submodule.add_mem _ ha' hb'
  refine ⟨hloc, ?_⟩
  ext d
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, loc_isUnit_iff, not_not]
  exact Iff.rfl

/-! ### Guardrails -/

/-- The maximal ideal is proper: `1 ∉ maxD`.  (If `maxD = ⊤` the statement of #3 would be
vacuous bookkeeping rather than a local-ring statement.) -/
example : maxD ≠ ⊤ := by
  intro h
  have h1 : (1 : ↥Dom) ∈ maxD := h ▸ Submodule.mem_top
  exact loc_one_not_mem_max h1

/-- `π` is a nonunit of `D`. -/
example : ¬ IsUnit (⟨piK, max_le_Dom piK ⟨1, T.one_mem, by simp⟩⟩ : ↥Dom) := by
  rw [loc_isUnit_iff, not_not]
  exact ⟨1, T.one_mem, by simp⟩

end Prob20
