/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Constants.LogEnclose
import EntropyBound.Proofs.Toolbox.Qseries
import EntropyBound.Proofs.Toolbox.Aseries

/-!
# Stage E item E3 — enclosure API for `Ader_lower_middle` (#35)

This file provides the reusable, `Real.sqrt`-free machinery used by
`EntropyBound/Proofs/EntropySpeed/Boxes{Low,High}.lean` and
`EntropyBound/Proofs/EntropySpeed/Middle.lean` to prove the frozen theorem

```
Ader_lower_middle : ∀ z : ℝ, 1/10 ≤ z → z ≤ 99999/100000 →
  8/9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)
```

Contents (all in `namespace EntropyBound.EntropySpeed`):

* `ader_ge_of_box` — the square-free reduction: it suffices to certify
  `0 < nlo ≤ Qser z - (1-z) * Qder z`, `Qser z ≤ qhi` and `64 * qhi ≤ 81 * nlo ^ 2`.
* `Qser_mono`, `Qder_mono` — both series are increasing on `[0, 1)`, termwise.
* `Qder_closed` — the closed form of `Qder`, obtained by differentiating the closed
  form of `Qser` (frozen #11) and matching against frozen #13 `Qser_hasDerivAt`.
* `log_ge_of` / `log_le_of` — certified rational enclosures of `Real.log x` for
  arbitrary positive rational `x`, obtained from the shared
  `EntropyBound.Constants.logLo`/`logHi` artanh certificates after a `2 ^ k` shift
  (this is what keeps the artanh argument in `[1, 2)`, where the series converges
  geometrically with ratio `≤ 1/9`).
* `Qser_ge_of`, `Qser_le_of`, `Qder_le_of` — turn a pair of `Real.log` enclosures at a
  rational point into rational bounds on `Qser`/`Qder` there.
* `box_bound` — the per-box certificate combining all of the above.
-/

noncomputable section

open scoped BigOperators

namespace EntropyBound.EntropySpeed

open EntropyBound.Constants

/-! ### The square-free reduction -/

/-- Square-free reduction of `8/9 ≤ N / √Q`. -/
theorem ader_ge_of_box {NQ Q nlo qhi : ℝ} (hnlo : 0 < nlo) (hN : nlo ≤ NQ)
    (hQ0 : 0 < Q) (hQ : Q ≤ qhi) (hcert : 64 * qhi ≤ 81 * nlo ^ 2) :
    8 / 9 ≤ NQ / Real.sqrt Q := by
  have hz : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ0
  have hsq : Real.sqrt Q ≤ Real.sqrt qhi := Real.sqrt_le_sqrt hQ
  have hkey : Real.sqrt qhi ≤ 9 * nlo / 8 := by
    have h1 : qhi ≤ (9 * nlo / 8) ^ 2 := by nlinarith
    have h2 : Real.sqrt qhi ≤ Real.sqrt ((9 * nlo / 8) ^ 2) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  rw [le_div_iff₀ hz]
  nlinarith [hsq, hz]

/-! ### Monotonicity of `Qser` and `Qder` -/

theorem Qser_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    Qser x ≤ Qser y := by
  have hy0 : 0 ≤ y := le_trans hx hxy
  refine Summable.tsum_le_tsum (fun j => ?_) (Toolbox.summable_Qser_term hx (le_trans hxy hy))
    (Toolbox.summable_Qser_term hy0 hy)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (by positivity)

theorem Qder_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    Qder x ≤ Qder y := by
  have hy0 : 0 ≤ y := le_trans hx hxy
  refine Summable.tsum_le_tsum (fun m => ?_) (Toolbox.summable_Qder_term hx (lt_of_le_of_lt hxy hy))
    (Toolbox.summable_Qder_term hy0 hy)
  have hp : x ^ (2 * m + 1) ≤ y ^ (2 * m + 1) := pow_le_pow_left₀ hx hxy _
  have hc : (0:ℝ) ≤ 2 * ((m : ℝ) + 1) := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (by positivity)

/-! ### Certified rational enclosures of `Real.log` at arbitrary positive rationals

`EntropyBound.Constants.logLo`/`logHi` converge like `|yOf a| ^ (2 J + 1)` with
`yOf a = (a-1)/(a+1)`, so they are only useful when `a` is close to `1`.  The two lemmas
below remove that restriction by the exact identity `log x = log (x * 2 ^ k) - k * log 2`:
choosing `k` with `x * 2 ^ k ∈ [1, 2)` puts `yOf (x * 2 ^ k) ∈ [0, 1/3]`, where the artanh
series converges with ratio `≤ 1/9` per term. -/

private theorem log_shift (x : ℚ) (k : ℕ) (hx : 0 < x) :
    Real.log ((x * 2 ^ k : ℚ) : ℝ) = Real.log (x : ℝ) + k * Real.log 2 := by
  have hx0 : ((x : ℝ)) ≠ 0 := by exact_mod_cast hx.ne'
  have h2 : ((2:ℝ) ^ k) ≠ 0 := by positivity
  push_cast
  rw [Real.log_mul hx0 h2, Real.log_pow]

/-- Certified rational **lower** bound for `Real.log x`, `x` an arbitrary positive rational. -/
theorem log_ge_of (x c : ℚ) (k J J2 : ℕ) (hx : 0 < x)
    (h : c ≤ logLo (x * 2 ^ k) J - (k : ℚ) * logHi 2 J2) :
    (c : ℝ) ≤ Real.log (x : ℝ) := by
  have hxk : (0:ℚ) < x * 2 ^ k := by positivity
  have h1 : ((logLo (x * 2 ^ k) J : ℚ) : ℝ) ≤ Real.log ((x * 2 ^ k : ℚ) : ℝ) :=
    logLo_le _ _ hxk
  have h2 : Real.log ((2:ℚ) : ℝ) ≤ ((logHi 2 J2 : ℚ) : ℝ) := le_logHi 2 J2 (by norm_num)
  rw [log_shift x k hx] at h1
  have hc : (c : ℝ) ≤ ((logLo (x * 2 ^ k) J : ℚ) : ℝ) - (k : ℝ) * ((logHi 2 J2 : ℚ) : ℝ) := by
    exact_mod_cast h
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2' : Real.log 2 ≤ ((logHi 2 J2 : ℚ) : ℝ) := by simpa using h2
  nlinarith [hc, h1, h2', hk]

/-- Certified rational **upper** bound for `Real.log x`, `x` an arbitrary positive rational. -/
theorem log_le_of (x c : ℚ) (k J J2 : ℕ) (hx : 0 < x)
    (h : logHi (x * 2 ^ k) J - (k : ℚ) * logLo 2 J2 ≤ c) :
    Real.log (x : ℝ) ≤ (c : ℝ) := by
  have hxk : (0:ℚ) < x * 2 ^ k := by positivity
  have h1 : Real.log ((x * 2 ^ k : ℚ) : ℝ) ≤ ((logHi (x * 2 ^ k) J : ℚ) : ℝ) :=
    le_logHi _ _ hxk
  have h2 : ((logLo 2 J2 : ℚ) : ℝ) ≤ Real.log ((2:ℚ) : ℝ) := logLo_le 2 J2 (by norm_num)
  rw [log_shift x k hx] at h1
  have hc : ((logHi (x * 2 ^ k) J : ℚ) : ℝ) - (k : ℝ) * ((logLo 2 J2 : ℚ) : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast h
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2' : ((logLo 2 J2 : ℚ) : ℝ) ≤ Real.log 2 := by simpa using h2
  nlinarith [hc, h1, h2', hk]


/-! ### The closed form of `Qder`

`Qser` has the closed form `Q z = ψ z / z ^ 2` with
`ψ z = (1+z) log (1+z) + (1-z) log (1-z)` (frozen #11), and `ψ' z = log (1+z) - log (1-z)`.
Differentiating and matching against frozen #13 `Qser_hasDerivAt` gives
`Q' z = (-(2+z) log (1+z) - (2-z) log (1-z)) / z ^ 3`. -/

/-- `ψ z = (1+z) log (1+z) + (1-z) log (1-z)` is differentiable on `(-1,1)`
with derivative `log (1+z) - log (1-z)`. -/
theorem hasDerivAt_psiC {z : ℝ} (hz1 : -1 < z) (hz2 : z < 1) :
    HasDerivAt (fun w : ℝ => (1 + w) * Real.log (1 + w) + (1 - w) * Real.log (1 - w))
      (Real.log (1 + z) - Real.log (1 - z)) z := by
  have h1p : (0:ℝ) < 1 + z := by linarith
  have h1m : (0:ℝ) < 1 - z := by linarith
  have hu : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add (1:ℝ)
  have hv : HasDerivAt (fun w : ℝ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1:ℝ)
  have hlu : HasDerivAt (fun w : ℝ => Real.log (1 + w)) (1 / (1 + z)) z := hu.log h1p.ne'
  have hlv : HasDerivAt (fun w : ℝ => Real.log (1 - w)) (-1 / (1 - z)) z := hv.log h1m.ne'
  have h := (hu.mul hlu).add (hv.mul hlv)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The closed form of the termwise derivative series `Qder`. -/
theorem Qder_closed {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Qder z = (-((2 + z) * Real.log (1 + z)) - (2 - z) * Real.log (1 - z)) / z ^ 3 := by
  have hz1' : (-1:ℝ) < z := by linarith
  have hpsi := hasDerivAt_psiC hz1' hz1
  have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hz2ne : z ^ 2 ≠ 0 := by positivity
  have hdiv := hpsi.div hsq hz2ne
  -- the closed form agrees with `Qser` on a neighbourhood of `z`
  have hloc : (fun w : ℝ => ((1 + w) * Real.log (1 + w) + (1 - w) * Real.log (1 - w)) / w ^ 2)
      =ᶠ[nhds z] Qser := by
    filter_upwards [Ioo_mem_nhds hz0 hz1] with w hw
    exact (Qser_closed_form_proof w hw.1 hw.2).symm
  have hQ := hdiv.congr_of_eventuallyEq hloc.symm
  have huniq := hQ.unique (Qser_hasDerivAt_proof z hz0.le hz1)
  rw [← huniq]
  field_simp
  ring

/-! ### From `Real.log` enclosures at a rational point to bounds on `Qser`, `Qder` -/

/-- Certified lower bound for `Qser z` from lower bounds on `log (1±z)`. -/
theorem Qser_ge_of {z lo1 lo2 c : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h1 : lo1 ≤ Real.log (1 + z)) (h2 : lo2 ≤ Real.log (1 - z))
    (hc : c * z ^ 2 ≤ (1 + z) * lo1 + (1 - z) * lo2) : c ≤ Qser z := by
  rw [Qser_closed_form_proof z hz0 hz1, le_div_iff₀ (by positivity)]
  have e1 : (1 + z) * lo1 ≤ (1 + z) * Real.log (1 + z) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have e2 : (1 - z) * lo2 ≤ (1 - z) * Real.log (1 - z) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

/-- Certified upper bound for `Qser z` from upper bounds on `log (1±z)`. -/
theorem Qser_le_of {z hi1 hi2 c : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h1 : Real.log (1 + z) ≤ hi1) (h2 : Real.log (1 - z) ≤ hi2)
    (hc : (1 + z) * hi1 + (1 - z) * hi2 ≤ c * z ^ 2) : Qser z ≤ c := by
  rw [Qser_closed_form_proof z hz0 hz1, div_le_iff₀ (by positivity)]
  have e1 : (1 + z) * Real.log (1 + z) ≤ (1 + z) * hi1 :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have e2 : (1 - z) * Real.log (1 - z) ≤ (1 - z) * hi2 :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

/-- Certified upper bound for `Qder z`.  Both coefficients of the closed-form numerator are
negative, so only **lower** bounds on `log (1±z)` are needed. -/
theorem Qder_le_of {z lo1 lo2 c : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (h1 : lo1 ≤ Real.log (1 + z)) (h2 : lo2 ≤ Real.log (1 - z))
    (hc : -((2 + z) * lo1) - (2 - z) * lo2 ≤ c * z ^ 3) : Qder z ≤ c := by
  rw [Qder_closed hz0 hz1, div_le_iff₀ (by positivity)]
  have e1 : (2 + z) * lo1 ≤ (2 + z) * Real.log (1 + z) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have e2 : (2 - z) * lo2 ≤ (2 - z) * Real.log (1 - z) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

/-! ### The per-box certificate -/

/-- The per-box certificate.  On a closed rational box `[a,b] ⊆ (0,1)`, monotonicity of
`Qser` and `Qder` turns the three endpoint enclosures `qa ≤ Qser a`, `Qser b ≤ qb`,
`Qder b ≤ db` into the uniform bound `8/9 ≤ Ader z` for **every** `z` of the box. -/
theorem box_bound {a b qa qb db : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1)
    (hQa : qa ≤ Qser a) (hQb : Qser b ≤ qb) (hDb : Qder b ≤ db)
    (hpos : 0 < qa - (1 - a) * db) (hcert : 64 * qb ≤ 81 * (qa - (1 - a) * db) ^ 2) :
    ∀ z : ℝ, a ≤ z → z ≤ b → 8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by
  intro z haz hzb
  have hz0 : 0 < z := lt_of_lt_of_le ha0 haz
  have hz1 : z < 1 := lt_of_le_of_lt hzb hb1
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hD0 : 0 ≤ Qder z := (Qder_upper_bounds_proof z hz0.le hz1).1
  have hDb0 : 0 ≤ db := le_trans (Qder_upper_bounds_proof b hb0.le hb1).1 hDb
  have hQlo : qa ≤ Qser z := le_trans hQa (Qser_mono ha0.le haz hz1.le)
  have hQhi : Qser z ≤ qb := le_trans (Qser_mono hz0.le hzb hb1.le) hQb
  have hDz : Qder z ≤ db := le_trans (Qder_mono hz0.le hzb hb1) hDb
  have hqa0 : 0 < qa := by nlinarith
  have hQ0 : 0 < Qser z := lt_of_lt_of_le hqa0 hQlo
  have hN : qa - (1 - a) * db ≤ Qser z - (1 - z) * Qder z := by nlinarith
  exact ader_ge_of_box hpos hN hQ0 hQhi hcert

end EntropyBound.EntropySpeed

end
