/-
# Prob27b — Stage B support file

Stage B of `BLUEPRINT.md` Part 2: `F` is a null polynomial on `R` (B1–B2) —
SKETCH Step 2, the **milestone heart** of the counterexample.

`F = uX² + eX³ + (e+u)X⁴ + eX⁵ + eX⁶ ∈ R[X]` is built from `Polynomial.monomial`
(frozen modeling decision 8), so evaluation is governed by `Polynomial.eval_add`
and `Polynomial.eval_monomial` **only**: `eval_mul`, `eval_C_mul`, `eval_pow` and
`aeval` all need a commutative coefficient ring and are unavailable over the
noncommutative `R`.

The main theorem is the frozen `F_isNullPoly : ∀ r : R, F.eval r = 0`, proved by
a genuine exhaustive kernel computation over all `2⁸ = 256` elements of `R`
(`decide`; `native_decide` is banned).  All helper lemmas live in
`namespace Prob27b.StageB`.
-/
import Prob27b.Defs

namespace Prob27b

namespace StageB

/-! ## B1 — evaluating `F`

The only rewrite rules used are `Polynomial.eval_add` and
`Polynomial.eval_monomial` (`(monomial n a).eval x = a * x ^ n`), which multiply
the coefficient on the **left** — exactly the *right* null-polynomial notion of
SKETCH Step 2. -/

/-- **B1.** The value of `F` at `r : R`, coefficients on the left. -/
theorem F_eval (r : R) :
    F.eval r = RAlg.u * r ^ 2 + RAlg.e * r ^ 3 + (RAlg.e + RAlg.u) * r ^ 4
      + RAlg.e * r ^ 5 + RAlg.e * r ^ 6 := by
  simp only [F, Polynomial.eval_add, Polynomial.eval_monomial]

/-- The `X²`-coefficient of `F` is `u`; used only to see that `F ≠ 0`, i.e. that
the milestone below is not vacuous. -/
theorem F_coeff_two : (F : Polynomial R).coeff 2 = RAlg.u := by
  simp [F, Polynomial.coeff_monomial]

/-! ### Guardrails

`F` really does vanish at the Step-3/Step-5 witness `a₀ = u + v`, and `F` is not
the zero polynomial — so `F_isNullPoly` is a statement with content. -/

example : F.eval ((RAlg.u : R) + RAlg.v) = 0 := by
  rw [StageB.F_eval]; decide

example : (F : Polynomial R) ≠ 0 := by
  intro h
  have h2 : (F : Polynomial R).coeff 2 = 0 := by rw [h, Polynomial.coeff_zero]
  rw [StageB.F_coeff_two] at h2
  exact absurd h2 (by decide)

end StageB

/-! ## B2 — the milestone: `F` is a right null polynomial of `R`

`R` is a `256`-element type carrying the **computable** `Fintype` and
`DecidableEq` instances of `Defs.lean` (frozen modeling decision 6), so after
rewriting with `B1` the statement `∀ r : R, u * r² + e * r³ + (e+u) * r⁴ +
e * r⁵ + e * r⁶ = 0` is decided by the kernel.  This is the sketch's own
exhaustive computation over **all** `r ∈ R`, not a sample: nothing about `r` is
assumed.  `maxRecDepth` must be raised (PROGRESS 📝 decision, item 12). -/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- The `decide` below is an exhaustive check over all `2⁸ = 256` elements of `R`,
-- five `8`-vector products each; whnf-ing that decision procedure costs far more
-- than the default heartbeat budget allows.
/-- **Frozen 3 (MILESTONE).** `F ∈ K(R)`: `F` vanishes at *every* element of `R`
(SKETCH Step 2). -/
theorem F_isNullPoly_proof : IsNullPoly F := by
  intro r
  rw [StageB.F_eval]
  revert r
  decide

end Prob27b

/-! ## Verbatim restatement of the frozen statement (global rule (f)) -/

namespace Prob27b.Solution

/-- **Frozen 3.** `F ∈ K(R)`: `F` vanishes at **every** element of `R` (Step 2). -/
theorem F_isNullPoly : IsNullPoly F := Prob27b.F_isNullPoly_proof

end Prob27b.Solution
