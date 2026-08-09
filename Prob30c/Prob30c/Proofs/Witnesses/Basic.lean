/-
Stage D -- the explicit witnesses (D1-D4).

* D1  `pow_tElt_mul_sElt_eq_zero_iff` : `t^k · s = 0 ↔ q ≤ k`.
* D2  `not_isNAbsorbing_A_q_proof` (FROZEN `not_isNAbsorbing_A_q`) : the family
      `s, t, …, t` of length `q+1` is an irredundant zero-product in `A q`.
* D3  `fPoly_mul_gPoly_proof` (FROZEN `fPoly_mul_gPoly`) : `f · g = (X + X²)·s`
      -- the characteristic-two cancellation of the free `u₁`/`u₂` parts.
* D4  `not_isNAbsorbing_polyExt_A_succ_q_proof` (FROZEN
      `not_isNAbsorbing_polyExt_A_succ_q`) : the family `f, g, t, …, t` of length
      `q+2` is an irredundant zero-product in `A q [X]`.

Nothing here edits `Defs.lean` or `Theorems.lean`, and no frozen statement gains a
hypothesis: `hq : 2 ≤ q` is the sketch's own hypothesis.
-/
import Prob30c.Proofs.Absorbing.Basic
import Prob30c.Proofs.Model.Basic

namespace Prob30c

open Polynomial

/-! ## A `Finset` helper used by every product computation below -/

/-- A product of a family that is constant on `S` is a power of that constant. -/
theorem prod_const_of_forall_eq {ι M : Type*} [CommMonoid M] (S : Finset ι)
    (f : ι → M) (c : M) (h : ∀ i ∈ S, f i = c) : ∏ i ∈ S, f i = c ^ S.card := by
  rw [Finset.prod_congr rfl h, Finset.prod_const]

/-! ## D1 — the `s`-line is *exactly* `t^q`-torsion -/

/-- `t^k · s = 0` iff `q ≤ k`.  (The hypothesis `1 ≤ q` of BLUEPRINT D1 is not
needed: for `q = 0` the ring `D/t^0` is trivial and both sides hold.) -/
theorem pow_tElt_mul_sElt_eq_zero_iff (q k : ℕ) :
    tElt q ^ k * sElt q = 0 ↔ q ≤ k :=
  (Alg.tElt_pow_mul_sElt_eq_zero_iff (B := Dbase) (τ := tD) (q := q) k).trans <| by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · intro h
      have hdeg := Polynomial.natDegree_le_of_dvd h (pow_ne_zero k Polynomial.X_ne_zero)
      rwa [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hdeg
    · intro h
      exact pow_dvd_pow _ h

/-! ## Characteristic two in `A q` -/

/-- `A q` is an algebra over `D = 𝔽₂[t]`, hence has characteristic two. -/
theorem two_eq_zero_A (q : ℕ) : (2 : A q) = 0 :=
  calc (2 : A q) = algebraMap Dbase (A q) 2 := (map_ofNat _ 2).symm
    _ = algebraMap Dbase (A q) 0 := congrArg _ CharTwo.two_eq_zero
    _ = 0 := map_zero _

/-- The char-two identity that kills the free `u₁`- and `u₂`-parts of `f · g`. -/
theorem add_self_eq_zero_A {q : ℕ} (z : A q) : z + z = 0 := by
  rw [← two_mul, two_eq_zero_A, zero_mul]

/-! ## Coordinates of the elements appearing in the witnesses -/

theorem α₁_e₁_mul_tElt_pow (q k : ℕ) : Alg.α₁ (e₁ q * tElt q ^ k) = tD ^ k := by
  show Alg.α₁ (Alg.e₁ Dbase tD q * Alg.tElt Dbase tD q ^ k) = tD ^ k
  rw [Alg.tElt_pow, Alg.α₁_mul, Alg.fst_e₁, Alg.α₁_algebraMap, Alg.fst_algebraMap,
    Alg.α₁_e₁, mul_zero, zero_add, mul_one]

theorem α₂_e₂_mul_tElt_pow (q k : ℕ) : Alg.α₂ (e₂ q * tElt q ^ k) = tD ^ k := by
  show Alg.α₂ (Alg.e₂ Dbase tD q * Alg.tElt Dbase tD q ^ k) = tD ^ k
  rw [Alg.tElt_pow, Alg.α₂_mul, Alg.fst_e₂, Alg.α₂_algebraMap, Alg.fst_algebraMap,
    Alg.α₂_e₂, mul_zero, zero_add, mul_one]

/-- `t^k ≠ 0` in `A q`: its `D`-component is `t^k ≠ 0` in the domain `D`. -/
theorem tElt_pow_ne_zero (q k : ℕ) : (tElt q : A q) ^ k ≠ 0 := by
  intro hcon
  refine pow_ne_zero k (Polynomial.X_ne_zero (R := F2)) ?_
  have h : Alg.α₁ (e₁ q * tElt q ^ k) = Alg.α₁ ((0 : A q)) := by
    rw [hcon, mul_zero]
  rwa [α₁_e₁_mul_tElt_pow, Alg.α₁_zero] at h

/-! ## D3 — `f · g = (X + X²) · s` (FROZEN `fPoly_mul_gPoly`) ★ MILESTONE ★ -/

/-- Frozen statement `fPoly_mul_gPoly`, proved.  The four coefficients of `f · g`
are `e₂e₁`, `e₂e₁ + e₂² + e₃e₁`, `e₂² + e₂e₃ + e₃e₁ + e₃e₂` and `e₃e₂ + e₃²`;
the multiplication table turns them into `0`, `2u₂ + s`, `2u₁ + 2u₂ + s`, `2u₁`,
and characteristic two removes every `u`-term. -/
theorem fPoly_mul_gPoly_proof (q : ℕ) :
    fPoly q * gPoly q = C (sElt q) * (X + X ^ 2) := by
  have hexp : fPoly q * gPoly q
      = C (e₂ q * e₁ q)
        + C (e₂ q * e₁ q + e₂ q * e₂ q + e₃ q * e₁ q) * X
        + C (e₂ q * e₂ q + e₂ q * e₃ q + e₃ q * e₁ q + e₃ q * e₂ q) * X ^ 2
        + C (e₃ q * e₂ q + e₃ q * e₃ q) * X ^ 3 := by
    simp only [fPoly, gPoly, Polynomial.C_add, Polynomial.C_mul]
    ring
  have hc0 : e₂ q * e₁ q = 0 := Alg.e₂_mul_e₁
  have hc1 : e₂ q * e₁ q + e₂ q * e₂ q + e₃ q * e₁ q = sElt q := by
    simp only [Prob30c.e₁, Prob30c.e₂, Prob30c.e₃, Prob30c.sElt,
      Alg.e₂_mul_e₁, Alg.e₂_mul_e₂, Alg.e₃_mul_e₁]
    linear_combination add_self_eq_zero_A (Alg.u₂ Dbase tD q)
  have hc2 : e₂ q * e₂ q + e₂ q * e₃ q + e₃ q * e₁ q + e₃ q * e₂ q = sElt q := by
    simp only [Prob30c.e₁, Prob30c.e₂, Prob30c.e₃, Prob30c.sElt,
      Alg.e₂_mul_e₂, Alg.e₂_mul_e₃, Alg.e₃_mul_e₁, Alg.e₃_mul_e₂]
    linear_combination add_self_eq_zero_A (Alg.u₂ Dbase tD q)
      + add_self_eq_zero_A (Alg.u₁ Dbase tD q)
  have hc3 : e₃ q * e₂ q + e₃ q * e₃ q = 0 := by
    simp only [Prob30c.e₂, Prob30c.e₃, Alg.e₃_mul_e₂, Alg.e₃_mul_e₃]
    exact add_self_eq_zero_A _
  rw [hexp, hc1, hc2, hc3, hc0]
  simp only [map_zero]
  ring

/-! ## D2 — `s · t · … · t` is irredundant (FROZEN `not_isNAbsorbing_A_q`) -/

/-- The Step-3 witness family `s, t, …, t` (`q` copies of `t`). -/
noncomputable def stFamily (q : ℕ) : Fin (q + 1) → A q :=
  fun i => if i = 0 then sElt q else tElt q

theorem stFamily_zero (q : ℕ) : stFamily q 0 = sElt q := if_pos rfl

theorem stFamily_ne (q : ℕ) {i : Fin (q + 1)} (hi : i ≠ 0) : stFamily q i = tElt q :=
  if_neg hi

/-- Dropping the `s`-factor leaves `t^q`. -/
theorem prod_stFamily_erase_zero (q : ℕ) :
    ∏ i ∈ Finset.univ.erase (0 : Fin (q + 1)), stFamily q i = tElt q ^ q := by
  rw [prod_const_of_forall_eq _ _ (tElt q)
      (fun _ hi => stFamily_ne q (Finset.mem_erase.1 hi).1),
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- Dropping one of the `t`-factors leaves `s · t^(q-1)`. -/
theorem prod_stFamily_erase_ne (q : ℕ) {j : Fin (q + 1)} (hj : j ≠ 0) :
    ∏ i ∈ Finset.univ.erase j, stFamily q i = sElt q * tElt q ^ (q - 1) := by
  have h0 : (0 : Fin (q + 1)) ∈ Finset.univ.erase j :=
    Finset.mem_erase.2 ⟨Ne.symm hj, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h0, stFamily_zero,
    prod_const_of_forall_eq _ _ (tElt q)
      (fun _ hi => stFamily_ne q (Finset.mem_erase.1 hi).1),
    Finset.card_erase_of_mem h0, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- The full product is `s · t^q = 0`. -/
theorem prod_stFamily (q : ℕ) : ∏ i, stFamily q i = sElt q * tElt q ^ q := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (q + 1))), stFamily_zero,
    prod_stFamily_erase_zero]

/-- Frozen statement `not_isNAbsorbing_A_q`, proved. -/
theorem not_isNAbsorbing_A_q_proof (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (⊥ : Ideal (A q)) q := by
  have hq1 : 1 ≤ q := le_trans one_le_two hq
  rw [absorbing_iff_no_irredundant]
  intro h
  refine h ⟨stFamily q, ?_, ?_⟩
  · rw [Ideal.mem_bot, prod_stFamily, mul_comm, tElt_pow_mul_sElt]
  · intro j hj
    rw [Ideal.mem_bot] at hj
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [prod_stFamily_erase_zero] at hj
      exact tElt_pow_ne_zero q q hj
    · rw [prod_stFamily_erase_ne q hj0,
        mul_comm (sElt q) (tElt q ^ (q - 1))] at hj
      exact tElt_pow_pred_mul_sElt_ne_zero hq1 hj

/-! ## D4 — `f · g · t · … · t` is irredundant
    (FROZEN `not_isNAbsorbing_polyExt_A_succ_q`) -/

/-- The Step-5 witness family `f, g, t, …, t` (`q` copies of `t`). -/
noncomputable def fgtFamily (q : ℕ) : Fin (q + 1 + 1) → Polynomial (A q) :=
  fun i => if i = 0 then fPoly q else if i = 1 then gPoly q else C (tElt q)

theorem fgtFamily_zero (q : ℕ) : fgtFamily q 0 = fPoly q := if_pos rfl

theorem one_ne_zero_Fin (q : ℕ) : (1 : Fin (q + 1 + 1)) ≠ 0 := by simp

theorem fgtFamily_one (q : ℕ) : fgtFamily q 1 = gPoly q := by
  show (if (1 : Fin (q + 1 + 1)) = 0 then fPoly q else
      if (1 : Fin (q + 1 + 1)) = 1 then gPoly q else C (tElt q)) = gPoly q
  rw [if_neg (one_ne_zero_Fin q)]
  exact if_pos rfl

theorem fgtFamily_ne (q : ℕ) {i : Fin (q + 1 + 1)} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    fgtFamily q i = C (tElt q) := by
  simp only [fgtFamily, if_neg h0, if_neg h1]

theorem prod_fgtFamily_const (q : ℕ) (S : Finset (Fin (q + 1 + 1)))
    (h0 : (0 : Fin (q + 1 + 1)) ∉ S) (h1 : (1 : Fin (q + 1 + 1)) ∉ S) :
    ∏ i ∈ S, fgtFamily q i = C (tElt q) ^ S.card :=
  prod_const_of_forall_eq _ _ _ fun _ hi =>
    fgtFamily_ne q (fun hz => h0 (hz ▸ hi)) (fun hz => h1 (hz ▸ hi))

/-- Dropping `f` leaves `g · t^q`. -/
theorem prod_fgtFamily_erase_zero (q : ℕ) :
    ∏ i ∈ Finset.univ.erase (0 : Fin (q + 1 + 1)), fgtFamily q i
      = gPoly q * C (tElt q) ^ q := by
  have h1mem : (1 : Fin (q + 1 + 1)) ∈ Finset.univ.erase (0 : Fin (q + 1 + 1)) :=
    Finset.mem_erase.2 ⟨one_ne_zero_Fin q, Finset.mem_univ _⟩
  have hcard : ((Finset.univ.erase (0 : Fin (q + 1 + 1))).erase 1).card = q := by
    rw [Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  rw [← Finset.mul_prod_erase _ _ h1mem, fgtFamily_one,
    prod_fgtFamily_const q _ (by simp) (by simp), hcard]

/-- Dropping `g` leaves `f · t^q`. -/
theorem prod_fgtFamily_erase_one (q : ℕ) :
    ∏ i ∈ Finset.univ.erase (1 : Fin (q + 1 + 1)), fgtFamily q i
      = fPoly q * C (tElt q) ^ q := by
  have h0mem : (0 : Fin (q + 1 + 1)) ∈ Finset.univ.erase (1 : Fin (q + 1 + 1)) :=
    Finset.mem_erase.2 ⟨Ne.symm (one_ne_zero_Fin q), Finset.mem_univ _⟩
  have hcard : ((Finset.univ.erase (1 : Fin (q + 1 + 1))).erase 0).card = q := by
    rw [Finset.card_erase_of_mem h0mem, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  rw [← Finset.mul_prod_erase _ _ h0mem, fgtFamily_zero,
    prod_fgtFamily_const q _ (by simp) (by simp), hcard]

/-- Dropping one of the `t`-factors leaves `f · g · t^(q-1)`. -/
theorem prod_fgtFamily_erase_other (q : ℕ) {j : Fin (q + 1 + 1)} (hj0 : j ≠ 0)
    (hj1 : j ≠ 1) :
    ∏ i ∈ Finset.univ.erase j, fgtFamily q i
      = fPoly q * (gPoly q * C (tElt q) ^ (q - 1)) := by
  have h0mem : (0 : Fin (q + 1 + 1)) ∈ Finset.univ.erase j :=
    Finset.mem_erase.2 ⟨Ne.symm hj0, Finset.mem_univ _⟩
  have h1mem : (1 : Fin (q + 1 + 1)) ∈ (Finset.univ.erase j).erase 0 :=
    Finset.mem_erase.2 ⟨one_ne_zero_Fin q,
      Finset.mem_erase.2 ⟨Ne.symm hj1, Finset.mem_univ _⟩⟩
  have hcard : (((Finset.univ.erase j).erase 0).erase 1).card = q - 1 := by
    rw [Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem h0mem,
      Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  rw [← Finset.mul_prod_erase _ _ h0mem, fgtFamily_zero,
    ← Finset.mul_prod_erase _ _ h1mem, fgtFamily_one,
    prod_fgtFamily_const q _ (by simp) (by simp), hcard]

/-- The full product `f · g · t^q` vanishes, by D3 and `t^q s = 0`. -/
theorem prod_fgtFamily_eq_zero (q : ℕ) : ∏ i, fgtFamily q i = 0 := by
  have hfull : ∏ i, fgtFamily q i = fPoly q * (gPoly q * C (tElt q) ^ q) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (q + 1 + 1))),
      fgtFamily_zero, prod_fgtFamily_erase_zero]
  have hrw : fPoly q * (gPoly q * C (tElt q) ^ q)
      = C (sElt q * tElt q ^ q) * (X + X ^ 2) := by
    rw [← mul_assoc, fPoly_mul_gPoly_proof]
    simp only [Polynomial.C_mul, Polynomial.C_pow]
    ring
  rw [hfull, hrw, mul_comm (sElt q) (tElt q ^ q), tElt_pow_mul_sElt, map_zero,
    zero_mul]

/-- Dropping `f` leaves a nonzero polynomial: its `X⁰`-coefficient is
`e₁ · t^q`, whose `e₁`-coordinate is `t^q ≠ 0`. -/
theorem gPoly_mul_tElt_pow_ne_zero (q : ℕ) : gPoly q * C (tElt q) ^ q ≠ 0 := by
  intro hcon
  have h : (gPoly q * C (tElt q) ^ q).coeff 0 = 0 := by
    rw [hcon]; exact Polynomial.coeff_zero 0
  rw [← Polynomial.C_pow, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero] at h
  have hg0 : (gPoly q).coeff 0 = e₁ q := by simp [gPoly]
  rw [hg0] at h
  refine pow_ne_zero q (Polynomial.X_ne_zero (R := F2)) ?_
  have h2 : Alg.α₁ (e₁ q * tElt q ^ q) = Alg.α₁ ((0 : A q)) := by rw [h]
  rwa [α₁_e₁_mul_tElt_pow, Alg.α₁_zero] at h2

/-- Dropping `g` leaves a nonzero polynomial: its `X⁰`-coefficient is
`e₂ · t^q`, whose `e₂`-coordinate is `t^q ≠ 0`. -/
theorem fPoly_mul_tElt_pow_ne_zero (q : ℕ) : fPoly q * C (tElt q) ^ q ≠ 0 := by
  intro hcon
  have h : (fPoly q * C (tElt q) ^ q).coeff 0 = 0 := by
    rw [hcon]; exact Polynomial.coeff_zero 0
  rw [← Polynomial.C_pow, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero] at h
  have hf0 : (fPoly q).coeff 0 = e₂ q := by simp [fPoly]
  rw [hf0] at h
  refine pow_ne_zero q (Polynomial.X_ne_zero (R := F2)) ?_
  have h2 : Alg.α₂ (e₂ q * tElt q ^ q) = Alg.α₂ ((0 : A q)) := by rw [h]
  rwa [α₂_e₂_mul_tElt_pow, Alg.α₂_zero] at h2

/-- Dropping one of the `t`-factors leaves a nonzero polynomial: its
`X¹`-coefficient is `t^(q-1) · s ≠ 0`. -/
theorem fPoly_mul_gPoly_mul_tElt_pow_ne_zero (q : ℕ) (hq : 1 ≤ q) :
    fPoly q * (gPoly q * C (tElt q) ^ (q - 1)) ≠ 0 := by
  intro hcon
  have hrw : fPoly q * (gPoly q * C (tElt q) ^ (q - 1))
      = C (sElt q * tElt q ^ (q - 1)) * (X + X ^ 2) := by
    rw [← mul_assoc, fPoly_mul_gPoly_proof]
    simp only [Polynomial.C_mul, Polynomial.C_pow]
    ring
  rw [hrw] at hcon
  have h : (C (sElt q * tElt q ^ (q - 1)) * (X + X ^ 2) : Polynomial (A q)).coeff 1
      = 0 := by
    rw [hcon]; exact Polynomial.coeff_zero 1
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_X_one,
    Polynomial.coeff_X_pow, if_neg (by norm_num), add_zero, mul_one] at h
  rw [mul_comm (sElt q) (tElt q ^ (q - 1))] at h
  exact tElt_pow_pred_mul_sElt_ne_zero hq h

/-- Frozen statement `not_isNAbsorbing_polyExt_A_succ_q`, proved. -/
theorem not_isNAbsorbing_polyExt_A_succ_q_proof (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (polyExt (⊥ : Ideal (A q))) (q + 1) := by
  have hq1 : 1 ≤ q := le_trans one_le_two hq
  rw [polyExt_bot, absorbing_iff_no_irredundant]
  intro h
  refine h ⟨fgtFamily q, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact prod_fgtFamily_eq_zero q
  · intro j hj
    rw [Ideal.mem_bot] at hj
    rcases eq_or_ne j 0 with rfl | hj0
    · rw [prod_fgtFamily_erase_zero] at hj
      exact gPoly_mul_tElt_pow_ne_zero q hj
    · rcases eq_or_ne j 1 with rfl | hj1
      · rw [prod_fgtFamily_erase_one] at hj
        exact fPoly_mul_tElt_pow_ne_zero q hj
      · rw [prod_fgtFamily_erase_other q hj0 hj1] at hj
        exact fPoly_mul_gPoly_mul_tElt_pow_ne_zero q hq1 hj

end Prob30c
