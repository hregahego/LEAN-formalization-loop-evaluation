/-
# Prob27b — Stage E support file

Stage E of `BLUEPRINT.md` Part 2: lifting `F` to `A` and landing `P` in `Int(A)`
(items E1–E6, `SKETCH.md` Step 4).

Proves the three frozen theorems

* **13** `Ftilde_eval_mem_pi : ∀ x : A, ∃ y : A, Ftilde.eval x = pi • y`,
* **14** `P_integerValued : IsIntegerValued P`,
* **15** `constE_integerValued : IsIntegerValued (Polynomial.C (iota (RAlg.e : A)))`.

Every helper lives in `namespace Prob27b.StageE`; nothing is added to
`namespace Prob27b.RAlg` (closed after Stage A).  The noncommutativity discipline
of the `📝 decision` entry is respected throughout: `F`/`Ftilde`/`P` are built
from `Polynomial.monomial`, so only `Polynomial.eval_monomial`, `eval_add`,
`eval_C`, `map_monomial`, `coeff_monomial` are used — never `eval_mul`,
`eval_C_mul`, `eval_pow`, `aeval` or `evalRingHom` on `Polynomial A`/`Polynomial B`.
-/
import Prob27b.Proofs.StageA.Basic
import Prob27b.Proofs.StageB.Basic
import Prob27b.Proofs.StageD.Basic

namespace Prob27b

namespace StageE

open Polynomial

/-! ## Reduction of the two basis coefficients of `F̃` (A6 specialised to `redPi`) -/

/-- `redPi = RAlg.map (Polynomial.evalRingHom 0)` fixes `e`. -/
theorem redPi_e : redPi (RAlg.e : A) = RAlg.e := RAlg.map_e _

/-- `redPi` fixes `u`. -/
theorem redPi_u : redPi (RAlg.u : A) = RAlg.u := RAlg.map_u _

/-! ## E1 — `F̃` reduces to `F` -/

/-- **E1.**  `F̃.map redPi = F`.  Note the `X⁴` coefficient is `e + u`, so this
genuinely needs `map_add` on top of `RAlg.map_e` / `RAlg.map_u`. -/
theorem Ftilde_map_redPi : Ftilde.map redPi = F := by
  simp only [Ftilde, F, Polynomial.map_add, Polynomial.map_monomial, map_add, redPi_e, redPi_u]

/-! ## E2 — evaluation commutes with a coefficient ring hom -/

/-- **E2.**  For any `RingHom φ : S →+* T` between semirings (no commutativity
assumed — this is what lets us apply it to the noncommutative `A →+* R` and
`A →+* B`), `(p.map φ).eval (φ x) = φ (p.eval x)`. -/
theorem eval_map_hom {S T : Type} [Semiring S] [Semiring T] (φ : S →+* T)
    (p : Polynomial S) (x : S) : (p.map φ).eval (φ x) = φ (p.eval x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-! ## E4 — evaluation commutes with a central scalar -/

/-- **E4.**  `(c • p).eval x = c • p.eval x` for `c : K` and `p : Polynomial B`.
`Polynomial.smul_eq_C_mul` is *not* usable here (`C c` is not central in
`Polynomial B`); the proof goes by `Polynomial.induction_on'` and
`smul_mul_assoc`, which is legitimate because `K` is central in the `K`-algebra
`B`. -/
theorem eval_smul (c : K) (p : Polynomial B) (x : B) : (c • p).eval x = c • p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [smul_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.smul_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial,
        smul_mul_assoc]

/-! ## `RAlg.map` is scalar-semilinear -/

/-- Coefficientwise functoriality against the scalar action: `map φ (d • y) = φ d • map φ y`.
Used at `φ = algebraMap D K` to turn `iota (pi • y)` into `algebraMap D K pi • iota y`. -/
theorem map_smul {k l : Type} [CommRing k] [CommRing l] (φ : k →+* l) (d : k) (y : RAlg k) :
    RAlg.map φ (d • y) = φ d • RAlg.map φ y := by
  ext i
  simp [map_mul]

/-! ## `1/π · π = 1` in `K` -/

/-- `π ≠ 0` in `K`: `π = X ≠ 0` in `D` and `algebraMap D K` is injective
(`IsFractionRing.injective`). -/
theorem pi_ne_zero_K : algebraMap D K pi ≠ 0 := by
  have h : (pi : D) ≠ 0 := Polynomial.X_ne_zero
  exact (map_ne_zero_iff (algebraMap D K) (IsFractionRing.injective D K)).mpr h

/-- **The key scalar identity.**  `invPi * algebraMap D K pi = 1`, from
`inv_mul_cancel₀` in the field `K`.  Everything about `P` being integer valued is
*derived* from this — it is never assumed. -/
theorem invPi_mul_pi : invPi * algebraMap D K pi = 1 :=
  inv_mul_cancel₀ pi_ne_zero_K

end StageE

/-! ## E3 — frozen 13 -/

/-- **Frozen 13** (`Ftilde_eval_mem_pi`).  For **every** `x : A`,
`F̃(x) ∈ πA`: reduce mod `π`, land on `F.eval (redPi x) = 0` by E2 + E1 +
`F_isNullPoly`, then use the `→` direction of the frozen iff `redPi_eq_zero_iff`. -/
theorem Ftilde_eval_mem_pi_proof : ∀ x : A, ∃ y : A, Ftilde.eval x = pi • y := by
  intro x
  refine (Prob27b.redPi_eq_zero_iff_proof (Ftilde.eval x)).mp ?_
  rw [← StageE.eval_map_hom redPi Ftilde x, StageE.Ftilde_map_redPi]
  exact Prob27b.F_isNullPoly_proof _

/-! ## E5 — frozen 14 -/

/-- **Frozen 14** (`P_integerValued`).  For **every** `x : A`,
`P(ι x) = invPi • ι (F̃(x)) = invPi • ι (π • y) = (invPi * π) • ι y = ι y ∈ range ι`.
The `invPi` factor of the frozen `P` is kept throughout; the cancellation is
derived from `StageE.invPi_mul_pi`. -/
theorem P_integerValued_proof : IsIntegerValued P := by
  intro x
  obtain ⟨y, hy⟩ := Ftilde_eval_mem_pi_proof x
  refine ⟨y, ?_⟩
  rw [P, StageE.eval_smul, StageE.eval_map_hom iota Ftilde x, hy,
    show iota (pi • y) = algebraMap D K pi • iota y from StageE.map_smul _ _ _,
    smul_smul, StageE.invPi_mul_pi, one_smul]

/-! ## E6 — frozen 15 -/

/-- **Frozen 15** (`constE_integerValued`).  The *constant* polynomial with
coefficient `ι e` evaluates to `ι e` everywhere (`Polynomial.eval_C`). -/
theorem constE_integerValued_proof : IsIntegerValued (Polynomial.C (iota (RAlg.e : A))) := by
  intro x
  rw [Polynomial.eval_C]
  exact ⟨RAlg.e, rfl⟩

/-! ## Cheat-watch guardrail — the `1/π` really is in `P`

`P.coeff 3 = invPi • ι e ≠ ι e`, so `P` has **not** been silently re-derived
without its `invPi` factor (which would make it trivially integer valued and gut
Step 5). -/
example : (P : Polynomial B).coeff 3 ≠ iota (RAlg.e : A) := by
  intro h
  have hP3 : (P : Polynomial B).coeff 3 = invPi • iota (RAlg.e : A) := by
    simp [P, Ftilde, Polynomial.coeff_smul, Polynomial.coeff_monomial]
  rw [hP3] at h
  have h0 : (invPi • iota (RAlg.e : A)).coeff 0 = (iota (RAlg.e : A)).coeff 0 := by rw [h]
  have hinv : invPi = 1 := by
    simpa [iota, RAlg.e, RAlg.single] using h0
  have hpiK : algebraMap D K pi = 1 := by
    have hm := StageE.invPi_mul_pi
    rw [hinv, one_mul] at hm
    exact hm
  have hpi1 : (pi : D) = 1 := IsFractionRing.injective D K (by rw [hpiK, map_one])
  have hev := congrArg (Polynomial.eval (0 : ZMod 2)) hpi1
  simp [pi] at hev

end Prob27b

/-! ## Frozen restatements (global rule (f)) — verbatim from `Prob27b/Theorems.lean` -/

namespace Prob27b.Solution

/-- **Frozen 13.** `F̃(a) ∈ πA` for **every** `a ∈ A` (Step 4). -/
theorem Ftilde_eval_mem_pi : ∀ x : A, ∃ y : A, Ftilde.eval x = pi • y :=
  Prob27b.Ftilde_eval_mem_pi_proof

/-- **Frozen 14.** `P = F̃/π ∈ Int(A)` (Step 4). -/
theorem P_integerValued : IsIntegerValued P := Prob27b.P_integerValued_proof

/-- **Frozen 15.** The constant polynomial `e` belongs to `Int(A)` (Step 4). -/
theorem constE_integerValued : IsIntegerValued (Polynomial.C (iota (RAlg.e : A))) :=
  Prob27b.constE_integerValued_proof

end Prob27b.Solution
