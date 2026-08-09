/-
# Prob27b — Stage C support file

Stage C of `BLUEPRINT.md` Part 2, items **C1–C2** (SKETCH Step 3): the frozen
theorem `Fe_eval_ne_zero`.

The whole point of Step 3 — and the trap this problem is built around — is that
`R` is **noncommutative**, so

  `(p * Polynomial.C c).eval x = p.eval x * c`   is **FALSE** here

(`u * e = 0` while `e * u = u`).  The multiplication by the constant `e` must
therefore be pushed onto the **coefficients** first (C1, `StageC.Fe_eq`), and only
then evaluated (C2).  Concretely, in `F = uX² + eX³ + (e+u)X⁴ + eX⁵ + eX⁶` the
`X²` term *dies* (`u * e = 0`) while the `X⁴` term *survives* (`(e+u) * e = e`),
giving `F·e = eX³ + eX⁴ + eX⁵ + eX⁶`, whose value at `a₀ = u + v` is
`e·(s + w) = s ≠ 0`.

Item **C3** (`nullPoly_not_rightIdeal`) is deliberately NOT attempted here: it
consumes `F_isNullPoly`, which is being proved concurrently in
`Prob27b/Proofs/StageB/Basic.lean`.

Every helper lives in `namespace Prob27b.StageC`; only the `_proof` declaration
for the frozen name sits directly in `namespace Prob27b`.  Nothing is declared in
`namespace Prob27b.RAlg` and no other `Proofs/` file is imported (Stages A, B, D
are being written in parallel).
-/
import Prob27b.Defs
import Prob27b.Proofs.StageB.Basic

namespace Prob27b

namespace StageC

/-! ## Local element identities in `R`

Each of these is a statement about *specific* elements of the finite ring `R`, so
the kernel can settle it by `decide` (the `DecidableEq (RAlg k)` and
`Fintype (RAlg k)` instances of `Defs.lean` are the computable ones).  They are
proved locally rather than imported from Stage A, which is being written
concurrently. -/

/-- `u · e = 0`: the path `u` ends at the vertex `f`, so it cannot be continued by
the vertex idempotent `e`.  This is what kills the `X²` term of `F·e`. -/
theorem u_mul_e : (RAlg.u : R) * RAlg.e = 0 := by decide

/-- `e · e = e`: `e` is idempotent. -/
theorem e_mul_e : (RAlg.e : R) * RAlg.e = RAlg.e := by decide

/-- `(e + u) · e = e`: this is what makes the `X⁴` term of `F·e` **survive**.  Note
that the frozen `X⁴` coefficient of `F` really is `e + u`, not `e`. -/
theorem eu_mul_e : ((RAlg.e : R) + RAlg.u) * RAlg.e = RAlg.e := by decide

/-- `(u + v)² = p + q`. -/
theorem a0_sq : ((RAlg.u : R) + RAlg.v) ^ 2 = RAlg.p + RAlg.q := by decide

/-- `(u + v)³ = s + w`. -/
theorem a0_cube : ((RAlg.u : R) + RAlg.v) ^ 3 = RAlg.s + RAlg.w := by decide

/-- `(u + v)⁴ = 0`: every path of length `4` is truncated away. -/
theorem a0_pow_four : ((RAlg.u : R) + RAlg.v) ^ 4 = 0 := by decide

/-- `(u + v)⁵ = 0`, from `a0_pow_four`. -/
theorem a0_pow_five : ((RAlg.u : R) + RAlg.v) ^ 5 = 0 := by
  rw [pow_succ, a0_pow_four, zero_mul]

/-- `(u + v)⁶ = 0`, from `a0_pow_five`. -/
theorem a0_pow_six : ((RAlg.u : R) + RAlg.v) ^ 6 = 0 := by
  rw [pow_succ, a0_pow_five, zero_mul]

/-- `e · (s + w) = s`: `s = uvu` starts at `e`, `w = vuv` starts at `f`. -/
theorem e_mul_sw : (RAlg.e : R) * (RAlg.s + RAlg.w) = RAlg.s := by decide

/-- `s ≠ 0` in `R` — the reason the whole counterexample works. -/
theorem s_ne_zero : (RAlg.s : R) ≠ 0 := by decide

/-! ## C1 — the right multiple `F · e`, computed on the **coefficients** -/

/-- **C1.**  `F · e = eX³ + eX⁴ + eX⁵ + eX⁶`.

Proved coefficientwise with `Polynomial.coeff_mul_C` (multiplication by a constant
polynomial acts on each coefficient **on the right**), so the noncommutativity of
`R` is handled honestly: the `X²` coefficient `u` becomes `u * e = 0`, and the
`X⁴` coefficient `e + u` becomes `(e + u) * e = e`. -/
theorem Fe_eq : F * Polynomial.C (RAlg.e : R) =
    Polynomial.monomial 3 (RAlg.e : R) + Polynomial.monomial 4 (RAlg.e : R)
      + Polynomial.monomial 5 (RAlg.e : R) + Polynomial.monomial 6 (RAlg.e : R) := by
  ext n
  simp only [F, Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_monomial,
    add_mul, ite_mul, zero_mul, u_mul_e, e_mul_e, ite_self, zero_add, add_zero]

/-- Guardrail (BLUEPRINT Stage C cheat watch): the `X²` coefficient of `F · e` really
does vanish.  Were `(p * C c).eval x = p.eval x * c` used instead, this term would
survive and the proof below would be measuring the wrong element. -/
example : (F * Polynomial.C (RAlg.e : R)).coeff 2 = 0 := by
  rw [Polynomial.coeff_mul_C]
  have hF : F.coeff 2 = (RAlg.u : R) := by simp [F, Polynomial.coeff_monomial]
  rw [hF, u_mul_e]

/-- Guardrail: the `X⁴` coefficient of `F · e` is `e`, i.e. it does **not** vanish —
the frozen `X⁴` coefficient of `F` is `e + u`, and `(e + u) * e = e`. -/
example : (F * Polynomial.C (RAlg.e : R)).coeff 4 = RAlg.e := by
  rw [Polynomial.coeff_mul_C]
  have hF : F.coeff 4 = (RAlg.e : R) + RAlg.u := by simp [F, Polynomial.coeff_monomial]
  rw [hF, eu_mul_e]

/-! ## C2 — the value of `F · e` at the witness `a₀ = u + v` -/

/-- **C2, computation step.**  `(F · e)(u + v) = s`.

Only `Polynomial.eval_add` and `Polynomial.eval_monomial` are used — `eval_mul`,
`eval_C_mul` and `aeval` all require a commutative coefficient ring and are
unavailable over `R`. -/
theorem Fe_eval_a0 :
    (F * Polynomial.C (RAlg.e : R)).eval ((RAlg.u : R) + RAlg.v) = RAlg.s := by
  rw [Fe_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_monomial]
  rw [a0_cube, a0_pow_four, a0_pow_five, a0_pow_six, mul_zero, add_zero, add_zero, add_zero,
    e_mul_sw]

end StageC

/-! ## The frozen theorem -/

/-- **Frozen 4** (`Fe_eval_ne_zero`).  `(F · e)(u + v) = s ≠ 0`.

The witness `u + v` is essential: every *basis* element of `R` gives `0`, so the
statement would be unprovable there rather than merely weaker. -/
theorem Fe_eval_ne_zero_proof :
    (F * Polynomial.C (RAlg.e : R)).eval ((RAlg.u : R) + RAlg.v) ≠ 0 := by
  rw [StageC.Fe_eval_a0]
  exact StageC.s_ne_zero

end Prob27b

/-! ## Verbatim restatement for `Prob27b.Solution` (global rule (f)) -/

namespace Prob27b.Solution

/-- **Frozen 4.** `(F·e)(u+v) ≠ 0` (Step 3). -/
theorem Fe_eval_ne_zero :
    (F * Polynomial.C (RAlg.e : R)).eval ((RAlg.u : R) + RAlg.v) ≠ 0 :=
  Prob27b.Fe_eval_ne_zero_proof

end Prob27b.Solution

/-! # Stage C, item C3 — appended in iteration 2

This section supersedes the remark in the file header above: `F_isNullPoly` is now
proved (`Prob27b/Proofs/StageB/Basic.lean`, ✅), so `Prob27b.Proofs.StageB.Basic` is
imported and C3 is available as the MILESTONE assembly of Step 3.

`K(R)`, the set of *right* null polynomials of `R`, fails to be a right ideal of
`R[X]`: the null polynomial `F` has a right multiple by the **constant** `e` which
is no longer null.  Both halves are already established — `F ∈ K(R)` is
`Prob27b.F_isNullPoly_proof` (a genuine check over all `2⁸` elements of `R`) and
`F·e ∉ K(R)` is witnessed at `a₀ = u + v` by `Prob27b.Fe_eval_ne_zero_proof`,
whose value there is `s ≠ 0`.
-/

namespace Prob27b

/-- **Frozen 5** (`nullPoly_not_rightIdeal`).  Some right null polynomial of `R`
has a right multiple by a constant polynomial that is not a right null polynomial;
i.e. `K(R)` is **not** a right ideal of `R[X]` (SKETCH Step 3, conclusion).

Witnesses: `p = F` and `c = RAlg.e`.  The order of the product is the frozen one,
`p * Polynomial.C c` — the failure is genuinely one-sided (`u * e = 0` but
`e * u = u`), and `Polynomial.C c * p` would be a different statement. -/
theorem nullPoly_not_rightIdeal_proof :
    ∃ (p : Polynomial R) (c : R), IsNullPoly p ∧ ¬ IsNullPoly (p * Polynomial.C c) :=
  ⟨Prob27b.F, RAlg.e, Prob27b.F_isNullPoly_proof,
    fun h => Prob27b.Fe_eval_ne_zero_proof (h _)⟩

end Prob27b

/-! ## Verbatim restatement for `Prob27b.Solution` (global rule (f)) -/

namespace Prob27b.Solution

/-- **Frozen 5.** `K(R)` is not a right ideal of `R[X]`: some null polynomial has a
right multiple by a constant that is not null (Step 3, conclusion). -/
theorem nullPoly_not_rightIdeal :
    ∃ (p : Polynomial R) (c : R), IsNullPoly p ∧ ¬ IsNullPoly (p * Polynomial.C c) :=
  Prob27b.nullPoly_not_rightIdeal_proof

end Prob27b.Solution
