/-
Problem 30(c) — the 15 frozen theorem statements.

FROZEN FILE.  Every statement below renders a claim of `SKETCH.md` faithfully and
minimally, and its name is binding (`scripts/harness.json`, `Discharge.lean`,
`Solution.lean`, `scripts/verify.py` all refer to these names).  All proofs are
`sorry` here on purpose: the real proofs live in `Prob30c/Proofs/**` and are
bound to these statements by `Discharge.lean`.  After SETUP this file is never
edited again; it is byte-pinned in `scripts/frozen.sha256`.
-/
import Prob30c.Defs

namespace Prob30c

open Polynomial Finset

/-- Problem statement · faithfulness of the `I[X]` model. -/
theorem mem_polyExt_iff {R : Type*} [CommRing R] (I : Ideal R) (p : Polynomial R) :
    p ∈ polyExt I ↔ ∀ n, p.coeff n ∈ I := sorry

/-- Problem statement · `n`-absorbing is monotone, so `ω` is the unique threshold. -/
theorem isNAbsorbing_succ {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (h : IsNAbsorbing I n) : IsNAbsorbing I (n + 1) := sorry

/-- Step 1 · `J³ = 0`. -/
theorem Jid_pow_three_eq_bot (q : ℕ) : (Jid Dbase tD q) ^ 3 = ⊥ := sorry

/-- Step 1 · `J² = W = Du₁ + Du₂ + (D/t^q)s`. -/
theorem Jid_sq_eq_Wid (q : ℕ) : (Jid Dbase tD q) ^ 2 = Wid Dbase tD q := sorry

/-- Step 1 · `A_q` is finite over the Noetherian ring `D`, hence Noetherian. -/
theorem isNoetherianRing_A (q : ℕ) : IsNoetherianRing (A q) := sorry

/-- Step 2 · the characteristic-2 cancellation: a product of two elements of `J`
    that lies in the `s`-line already lies in `t · (s-line)`. -/
theorem s_component_cancellation (q : ℕ) (x y : A q)
    (hx : x ∈ Jid Dbase tD q) (hy : y ∈ Jid Dbase tD q)
    (h : x * y ∈ Ideal.span {sElt q}) :
    x * y ∈ Ideal.span {tElt q * sElt q} := sorry

/-- Step 3 (lower bound) · `s · t · … · t` is an irredundant zero-product of
    length `q+1`, so `0` is not `q`-absorbing in `A_q`. -/
theorem not_isNAbsorbing_A_q (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (⊥ : Ideal (A q)) q := sorry

/-- Step 4 · `f · g = X(1+X)s` in `A_q[X]` — the free `u₁`- and `u₂`-parts cancel. -/
theorem fPoly_mul_gPoly (q : ℕ) :
    fPoly q * gPoly q = C (sElt q) * (X + X ^ 2) := sorry

/-- Step 5 (lower bound) · `f, g, t, …, t` is an irredundant zero-product of length
    `q+2` in `A_q[X]`, so `0[X]` is not `(q+1)`-absorbing. -/
theorem not_isNAbsorbing_polyExt_A_succ_q (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (polyExt (⊥ : Ideal (A q))) (q + 1) := sorry

/-- Step 3 (upper bound) · every irredundant zero-product in `A_q` has length
    `≤ q+1`, i.e. `0` is `(q+1)`-absorbing. -/
theorem isNAbsorbing_A_succ_q (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (⊥ : Ideal (A q)) (q + 1) := sorry

/-- Step 6 (upper bound) · the same valuation argument over `D[X]`: `0[X]` is
    `(q+2)`-absorbing in `A_q[X]`. -/
theorem isNAbsorbing_polyExt_A_succ_succ_q (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (polyExt (⊥ : Ideal (A q))) (q + 2) := sorry

/-- Step 3 · `ω_{A_q}(0) = q+1`. -/
theorem omegaAbs_A (q : ℕ) (hq : 2 ≤ q) : omegaAbs (⊥ : Ideal (A q)) = q + 1 := sorry

/-- Step 6 · `ω_{A_q[X]}(0[X]) = q+2`. -/
theorem omegaAbs_polyExt_A (q : ℕ) (hq : 2 ≤ q) :
    omegaAbs (polyExt (⊥ : Ideal (A q))) = q + 2 := sorry

/-- Conclusion · for every `n ≥ 3` the Noetherian ring `A (n-1)` has
    `ω_A(0) = n` and `ω_{A[X]}(0[X]) = n+1`. -/
theorem gap_family (n : ℕ) (hn : 3 ≤ n) :
    IsNoetherianRing (A (n - 1)) ∧
      omegaAbs (⊥ : Ideal (A (n - 1))) = n ∧
      omegaAbs (polyExt (⊥ : Ideal (A (n - 1)))) = n + 1 := sorry

/-- HEADLINE · Problem 30(c) has a negative answer: `ω_{R[X]}(I[X]) = ω_R(I)` fails. -/
theorem polyAbsorbingConj_false : ¬ PolyAbsorbingConj := sorry

end Prob30c
