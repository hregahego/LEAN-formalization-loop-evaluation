/-
Stage F -- `A_q[X] ≅ Alg (D[X]) (C t) q` and the `q+2` upper bound (F1-F3).

This module delivers **F1 and F2**: the coefficient equivalence
`(D/(t^q))[X] ≃+* D[X]/((C t)^q)`, the two base facts about the polynomial base
ring `D[X] = 𝔽₂[t][X]` that Stage F3 will need, and the transfer isomorphism
`transferEquiv q : A_q[X] ≃+* Alg (D[X]) (C t) q`.

F3 (`isNAbsorbing_polyExt_A_succ_succ_q`) consumes Stage E's generic,
`hcanc`-free irredundant-length bound and is deliberately not attempted here.

Cheat-watch note: nothing in this file may presuppose the characteristic-2
cancellation of Stage C at the base `Polynomial Dbase` -- that statement is
FALSE there, and that asymmetry is exactly what makes the counterexample work.
-/
import Prob30c.Defs
import Prob30c.Proofs.Model.Basic
import Prob30c.Proofs.Bound.Basic

namespace Prob30c

open Polynomial

/-! ## F1a — the ideal `((C t)^q)` is the extension of `(t^q)` along `C` -/

/-- `Ideal.span {(C t)^q} = (Ideal.span {t^q}).map C` inside `D[X]`. -/
theorem span_C_pow_eq_map (q : ℕ) :
    Ideal.span {(Polynomial.C tD : Polynomial Dbase) ^ q}
      = (Ideal.span {tD ^ q}).map (Polynomial.C : Dbase →+* Polynomial Dbase) := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

/-! ## F1b — the coefficient equivalence `(D/(t^q))[X] ≃+* D[X]/((C t)^q)` -/

/-- **F1b.**  `(D/(t^q))[X] ≃+* D[X]/((C t)^q)`.

Both directions come from Mathlib's `Ideal.polynomialQuotientEquivQuotientPolynomial`
(applied to the ideal `(t^q) ⊆ D`), corrected by the `Ideal.quotEquivOfEq` induced
by `span_C_pow_eq_map`; in particular `map_add`, `map_mul` and both inverse laws
are Mathlib's, not hand-built. -/
noncomputable def quoPolyEquiv (q : ℕ) :
    Polynomial (Quo Dbase tD q) ≃+* Quo (Polynomial Dbase) (Polynomial.C tD) q :=
  (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {tD ^ q})).trans
    (Ideal.quotEquivOfEq (span_C_pow_eq_map q).symm)

/-- The forward direction of `quoPolyEquiv` on a polynomial reduced coefficientwise:
it is just reduction mod `((C t)^q)`. -/
theorem quoPolyEquiv_map_mk (q : ℕ) (f : Polynomial Dbase) :
    quoPolyEquiv q (f.map (Ideal.Quotient.mk (Ideal.span {tD ^ q})))
      = Ideal.Quotient.mk (Ideal.span {(Polynomial.C tD : Polynomial Dbase) ^ q}) f := by
  rw [quoPolyEquiv, RingEquiv.trans_apply,
    Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk]
  rfl

/-- The inverse direction of `quoPolyEquiv` on the class of a polynomial: it is
coefficientwise reduction mod `(t^q)`. -/
theorem quoPolyEquiv_symm_mk (q : ℕ) (f : Polynomial Dbase) :
    (quoPolyEquiv q).symm
        (Ideal.Quotient.mk (Ideal.span {(Polynomial.C tD : Polynomial Dbase) ^ q}) f)
      = f.map (Ideal.Quotient.mk (Ideal.span {tD ^ q})) :=
  (quoPolyEquiv q).symm_apply_eq.2 (quoPolyEquiv_map_mk q f).symm

/-- `quoPolyEquiv` is compatible with the two constant-coefficient inclusions. -/
theorem quoPolyEquiv_C (q : ℕ) (a : Dbase) :
    quoPolyEquiv q (Polynomial.C (Ideal.Quotient.mk (Ideal.span {tD ^ q}) a))
      = Ideal.Quotient.mk (Ideal.span {(Polynomial.C tD : Polynomial Dbase) ^ q})
          (Polynomial.C a) := by
  rw [← Polynomial.map_C (Ideal.Quotient.mk (Ideal.span {tD ^ q})), quoPolyEquiv_map_mk]

/-! ## F1c — the two base facts at the polynomial base `D[X]` -/

/-- `C t` is a prime element of `D[X] = 𝔽₂[t][X]`: `t` is prime in the UFD
`D = 𝔽₂[t]`, and `C` preserves primality of constants. -/
theorem prime_C_tD : Prime (Polynomial.C tD : Polynomial Dbase) :=
  (Polynomial.prime_C_iff).2 Polynomial.prime_X

/-- `D[X]` is an integral domain.  Instance search already finds this (`Dbase` is a
domain and `Polynomial.instIsDomain` applies); the term is recorded only so that
Stage F3 can cite it by name. -/
theorem isDomain_polyDbase : IsDomain (Polynomial Dbase) := inferInstance

/-! ## F2 — the transfer isomorphism `A_q[X] ≃+* Alg (D[X]) (C t) q`

The two rings have the *same* seven coordinates, read in the two possible orders:
an element of `A_q[X]` is a polynomial whose coefficients carry seven `D`-
(resp. `D/(t^q)`-) coordinates, while an element of `Alg (D[X]) (C t) q` carries
seven `D[X]`- (resp. `D[X]/((C t)^q)`-) coordinates.  Transposing is a bijection;
the content of `F2` is that it is a *ring* map, i.e. that the frozen bilinear
multiplication table of `Jmod` is compatible with polynomial convolution.  That is
checked on monomials in `transferTo_monomial_mul` and propagated by bilinearity.

Nothing below refers to Stage C: the map is built from the coefficient
equivalence `quoPolyEquiv` (F1) alone, and in particular does not assume the
characteristic-2 cancellation over `D[X]`. -/

/-- `quoPolyEquiv` on a monomial with reduced coefficient. -/
theorem quoPolyEquiv_monomial_mk (q : ℕ) (n : ℕ) (c : Dbase) :
    quoPolyEquiv q (monomial n (Ideal.Quotient.mk (Ideal.span {tD ^ q}) c))
      = Ideal.Quotient.mk (Ideal.span {(Polynomial.C tD : Polynomial Dbase) ^ q})
          (monomial n c) := by
  rw [← Polynomial.map_monomial (f := Ideal.Quotient.mk (Ideal.span {tD ^ q})),
    quoPolyEquiv_map_mk]

/-- `quoPolyEquiv` turns the `D`-action on a coefficient into the `D[X]`-action,
splitting the degree as `n + m`. -/
theorem quoPolyEquiv_monomial_smul (q : ℕ) (n m : ℕ) (d : Dbase) (c : Quo Dbase tD q) :
    quoPolyEquiv q (monomial (n + m) (d • c))
      = (monomial n d : Polynomial Dbase) • quoPolyEquiv q (monomial m c) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Jmod.quo_smul_mk, quoPolyEquiv_monomial_mk, quoPolyEquiv_monomial_mk,
    Jmod.quo_smul_mk, Polynomial.monomial_mul_monomial]

/-- The same statement with the two degrees exchanged on the right. -/
theorem quoPolyEquiv_monomial_smul' (q : ℕ) (n m : ℕ) (d : Dbase) (c : Quo Dbase tD q) :
    quoPolyEquiv q (monomial (n + m) (d • c))
      = (monomial m d : Polynomial Dbase) • quoPolyEquiv q (monomial n c) := by
  rw [Nat.add_comm n m, quoPolyEquiv_monomial_smul]

namespace Transfer

/-! ### Coefficientwise transport of an additive map along `Polynomial` -/

/-- Apply an additive map to every coefficient of a polynomial.  (`Polynomial.map`
only handles ring homomorphisms; the seven coordinate maps of `Alg B τ q` and the
seven coordinate inclusions are merely additive.) -/
noncomputable def cmap {M N : Type} [Semiring M] [Semiring N] (f : M →+ N)
    (p : Polynomial M) : Polynomial N :=
  ⟨⟨Finsupp.mapRange f f.map_zero p.toFinsupp.coeff⟩⟩

@[simp] theorem coeff_cmap {M N : Type} [Semiring M] [Semiring N] (f : M →+ N)
    (p : Polynomial M) (n : ℕ) : (cmap f p).coeff n = f (p.coeff n) := rfl

theorem cmap_add {M N : Type} [Semiring M] [Semiring N] (f : M →+ N)
    (p r : Polynomial M) : cmap f (p + r) = cmap f p + cmap f r := by
  ext n; simp

theorem cmap_monomial {M N : Type} [Semiring M] [Semiring N] (f : M →+ N)
    (n : ℕ) (a : M) : cmap f (monomial n a) = monomial n (f a) := by
  ext m
  simp only [coeff_cmap, Polynomial.coeff_monomial]
  split <;> simp

/-! ### The seven coordinates as additive maps, and the seven coordinate injections -/

section Coords

variable {B : Type} [CommRing B] {τ : B} {q : ℕ}

/-- Assemble an element of `Alg B τ q` from its seven coordinates. -/
def mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) : Alg B τ q := ⟨b, a₁, a₂, a₃, c₁, c₂, s⟩

@[simp] theorem fst_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    (mkAlg b a₁ a₂ a₃ c₁ c₂ s).fst = b := rfl
@[simp] theorem α₁_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    Alg.α₁ (mkAlg b a₁ a₂ a₃ c₁ c₂ s) = a₁ := rfl
@[simp] theorem α₂_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    Alg.α₂ (mkAlg b a₁ a₂ a₃ c₁ c₂ s) = a₂ := rfl
@[simp] theorem α₃_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    Alg.α₃ (mkAlg b a₁ a₂ a₃ c₁ c₂ s) = a₃ := rfl
@[simp] theorem γ₁_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    Alg.γ₁ (mkAlg b a₁ a₂ a₃ c₁ c₂ s) = c₁ := rfl
@[simp] theorem γ₂_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    Alg.γ₂ (mkAlg b a₁ a₂ a₃ c₁ c₂ s) = c₂ := rfl
@[simp] theorem σ_mkAlg (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q) :
    Alg.σ (mkAlg b a₁ a₂ a₃ c₁ c₂ s) = s := rfl

theorem mkAlg_add (b a₁ a₂ a₃ c₁ c₂ : B) (s : Quo B τ q)
    (b' a₁' a₂' a₃' c₁' c₂' : B) (s' : Quo B τ q) :
    mkAlg b a₁ a₂ a₃ c₁ c₂ s + mkAlg b' a₁' a₂' a₃' c₁' c₂' s'
      = mkAlg (b + b') (a₁ + a₁') (a₂ + a₂') (a₃ + a₃') (c₁ + c₁') (c₂ + c₂') (s + s') := rfl

theorem mkAlg_eta (x : Alg B τ q) :
    mkAlg x.fst (Alg.α₁ x) (Alg.α₂ x) (Alg.α₃ x) (Alg.γ₁ x) (Alg.γ₂ x) (Alg.σ x) = x := rfl

/-- The `1`-coordinate of `Alg B τ q`, as an additive map. -/
def fstAH : Alg B τ q →+ B := AddMonoidHom.mk' (fun x : Alg B τ q => x.fst) (fun _ _ => rfl)
/-- The `e₁`-coordinate, as an additive map. -/
def α₁AH : Alg B τ q →+ B := AddMonoidHom.mk' Alg.α₁ (fun _ _ => rfl)
/-- The `e₂`-coordinate, as an additive map. -/
def α₂AH : Alg B τ q →+ B := AddMonoidHom.mk' Alg.α₂ (fun _ _ => rfl)
/-- The `e₃`-coordinate, as an additive map. -/
def α₃AH : Alg B τ q →+ B := AddMonoidHom.mk' Alg.α₃ (fun _ _ => rfl)
/-- The `u₁`-coordinate, as an additive map. -/
def γ₁AH : Alg B τ q →+ B := AddMonoidHom.mk' Alg.γ₁ (fun _ _ => rfl)
/-- The `u₂`-coordinate, as an additive map. -/
def γ₂AH : Alg B τ q →+ B := AddMonoidHom.mk' Alg.γ₂ (fun _ _ => rfl)
/-- The `s`-coordinate, as an additive map. -/
def σAH : Alg B τ q →+ Quo B τ q := AddMonoidHom.mk' Alg.σ (fun _ _ => rfl)

@[simp] theorem fstAH_apply (x : Alg B τ q) : fstAH x = x.fst := rfl
@[simp] theorem α₁AH_apply (x : Alg B τ q) : α₁AH x = Alg.α₁ x := rfl
@[simp] theorem α₂AH_apply (x : Alg B τ q) : α₂AH x = Alg.α₂ x := rfl
@[simp] theorem α₃AH_apply (x : Alg B τ q) : α₃AH x = Alg.α₃ x := rfl
@[simp] theorem γ₁AH_apply (x : Alg B τ q) : γ₁AH x = Alg.γ₁ x := rfl
@[simp] theorem γ₂AH_apply (x : Alg B τ q) : γ₂AH x = Alg.γ₂ x := rfl
@[simp] theorem σAH_apply (x : Alg B τ q) : σAH x = Alg.σ x := rfl

/-- The inclusion of the `1`-coordinate, as an additive map. -/
def injFst : B →+ Alg B τ q :=
  AddMonoidHom.mk' (fun b => mkAlg b 0 0 0 0 0 0) (by intro x y; rw [mkAlg_add]; simp)
/-- The inclusion of the `e₁`-coordinate, as an additive map. -/
def injE₁ : B →+ Alg B τ q :=
  AddMonoidHom.mk' (fun b => mkAlg 0 b 0 0 0 0 0) (by intro x y; rw [mkAlg_add]; simp)
/-- The inclusion of the `e₂`-coordinate, as an additive map. -/
def injE₂ : B →+ Alg B τ q :=
  AddMonoidHom.mk' (fun b => mkAlg 0 0 b 0 0 0 0) (by intro x y; rw [mkAlg_add]; simp)
/-- The inclusion of the `e₃`-coordinate, as an additive map. -/
def injE₃ : B →+ Alg B τ q :=
  AddMonoidHom.mk' (fun b => mkAlg 0 0 0 b 0 0 0) (by intro x y; rw [mkAlg_add]; simp)
/-- The inclusion of the `u₁`-coordinate, as an additive map. -/
def injU₁ : B →+ Alg B τ q :=
  AddMonoidHom.mk' (fun b => mkAlg 0 0 0 0 b 0 0) (by intro x y; rw [mkAlg_add]; simp)
/-- The inclusion of the `u₂`-coordinate, as an additive map. -/
def injU₂ : B →+ Alg B τ q :=
  AddMonoidHom.mk' (fun b => mkAlg 0 0 0 0 0 b 0) (by intro x y; rw [mkAlg_add]; simp)
/-- The inclusion of the `s`-coordinate, as an additive map. -/
def injS : Quo B τ q →+ Alg B τ q :=
  AddMonoidHom.mk' (fun s => mkAlg 0 0 0 0 0 0 s) (by intro x y; rw [mkAlg_add]; simp)

@[simp] theorem injFst_apply (b : B) : (injFst b : Alg B τ q) = mkAlg b 0 0 0 0 0 0 := rfl
@[simp] theorem injE₁_apply (b : B) : (injE₁ b : Alg B τ q) = mkAlg 0 b 0 0 0 0 0 := rfl
@[simp] theorem injE₂_apply (b : B) : (injE₂ b : Alg B τ q) = mkAlg 0 0 b 0 0 0 0 := rfl
@[simp] theorem injE₃_apply (b : B) : (injE₃ b : Alg B τ q) = mkAlg 0 0 0 b 0 0 0 := rfl
@[simp] theorem injU₁_apply (b : B) : (injU₁ b : Alg B τ q) = mkAlg 0 0 0 0 b 0 0 := rfl
@[simp] theorem injU₂_apply (b : B) : (injU₂ b : Alg B τ q) = mkAlg 0 0 0 0 0 b 0 := rfl
@[simp] theorem injS_apply (s : Quo B τ q) : (injS s : Alg B τ q) = mkAlg 0 0 0 0 0 0 s := rfl

end Coords

/-! ### The two maps, and the four laws -/

/-- The forward transfer map: read the seven coordinates of the coefficients of
`p : A_q[X]` as seven polynomials. -/
noncomputable def transferTo (q : ℕ) (p : Polynomial (A q)) :
    Alg (Polynomial Dbase) (Polynomial.C tD) q :=
  mkAlg (cmap fstAH p) (cmap α₁AH p) (cmap α₂AH p) (cmap α₃AH p) (cmap γ₁AH p)
    (cmap γ₂AH p) (quoPolyEquiv q (cmap σAH p))

/-- The backward transfer map: read the coefficients of the seven coordinate
polynomials of `z` as the seven coordinates of the coefficients of a polynomial. -/
noncomputable def transferInv (q : ℕ) (z : Alg (Polynomial Dbase) (Polynomial.C tD) q) :
    Polynomial (A q) :=
  cmap injFst z.fst + cmap injE₁ (Alg.α₁ z) + cmap injE₂ (Alg.α₂ z) + cmap injE₃ (Alg.α₃ z)
    + cmap injU₁ (Alg.γ₁ z) + cmap injU₂ (Alg.γ₂ z)
    + cmap injS ((quoPolyEquiv q).symm (Alg.σ z))

theorem coeff_transferInv (q : ℕ) (z : Alg (Polynomial Dbase) (Polynomial.C tD) q) (n : ℕ) :
    (transferInv q z).coeff n =
      mkAlg (z.fst.coeff n) ((Alg.α₁ z).coeff n) ((Alg.α₂ z).coeff n) ((Alg.α₃ z).coeff n)
        ((Alg.γ₁ z).coeff n) ((Alg.γ₂ z).coeff n)
        (((quoPolyEquiv q).symm (Alg.σ z)).coeff n) := by
  simp only [transferInv, Polynomial.coeff_add, coeff_cmap, injFst_apply, injE₁_apply,
    injE₂_apply, injE₃_apply, injU₁_apply, injU₂_apply, injS_apply, mkAlg_add]
  simp

theorem transferInv_transferTo (q : ℕ) (p : Polynomial (A q)) :
    transferInv q (transferTo q p) = p := by
  refine Polynomial.ext fun n => ?_
  rw [coeff_transferInv]
  simp only [transferTo, fst_mkAlg, α₁_mkAlg, α₂_mkAlg, α₃_mkAlg, γ₁_mkAlg, γ₂_mkAlg,
    σ_mkAlg, RingEquiv.symm_apply_apply, coeff_cmap, fstAH_apply, α₁AH_apply, α₂AH_apply,
    α₃AH_apply, γ₁AH_apply, γ₂AH_apply, σAH_apply]
  exact mkAlg_eta (p.coeff n)

theorem transferTo_transferInv (q : ℕ) (z : Alg (Polynomial Dbase) (Polynomial.C tD) q) :
    transferTo q (transferInv q z) = z := by
  have hσ : cmap σAH (transferInv q z) = (quoPolyEquiv q).symm (Alg.σ z) := by
    refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  refine Alg.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [transferTo, fst_mkAlg, α₁_mkAlg, α₂_mkAlg, α₃_mkAlg, γ₁_mkAlg, γ₂_mkAlg, σ_mkAlg]
  · refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  · refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  · refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  · refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  · refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  · refine Polynomial.ext fun n => ?_; simp [coeff_transferInv]
  · rw [hσ, RingEquiv.apply_symm_apply]

theorem transferTo_add (q : ℕ) (p r : Polynomial (A q)) :
    transferTo q (p + r) = transferTo q p + transferTo q r := by
  simp only [transferTo, cmap_add, map_add, mkAlg_add]

theorem transferTo_monomial (q : ℕ) (n : ℕ) (a : A q) :
    transferTo q (monomial n a)
      = mkAlg (monomial n a.fst) (monomial n (Alg.α₁ a)) (monomial n (Alg.α₂ a))
          (monomial n (Alg.α₃ a)) (monomial n (Alg.γ₁ a)) (monomial n (Alg.γ₂ a))
          (quoPolyEquiv q (monomial n (Alg.σ a))) := by
  simp only [transferTo, cmap_monomial, fstAH_apply, α₁AH_apply, α₂AH_apply, α₃AH_apply,
    γ₁AH_apply, γ₂AH_apply, σAH_apply]

theorem transferTo_C (q : ℕ) (a : A q) :
    transferTo q (Polynomial.C a)
      = mkAlg (Polynomial.C a.fst) (Polynomial.C (Alg.α₁ a)) (Polynomial.C (Alg.α₂ a))
          (Polynomial.C (Alg.α₃ a)) (Polynomial.C (Alg.γ₁ a)) (Polynomial.C (Alg.γ₂ a))
          (quoPolyEquiv q (Polynomial.C (Alg.σ a))) := by
  rw [show (Polynomial.C a : Polynomial (A q)) = monomial 0 a from
      (Polynomial.monomial_zero_left (a := a)).symm, transferTo_monomial]
  simp only [Polynomial.monomial_zero_left]

theorem transferTo_X (q : ℕ) :
    transferTo q (X : Polynomial (A q))
      = algebraMap (Polynomial Dbase) (Alg (Polynomial Dbase) (Polynomial.C tD) q) X := by
  rw [show (X : Polynomial (A q)) = monomial 1 1 from Polynomial.monomial_one_one_eq_X.symm,
    transferTo_monomial]
  refine Alg.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [Polynomial.monomial_one_one_eq_X]

/-- The heart of F2: the frozen bilinear multiplication table of `Jmod` is
compatible with the convolution product of polynomials.  Checked on all seven
coordinates. -/
theorem transferTo_monomial_mul (q : ℕ) (n m : ℕ) (a b : A q) :
    transferTo q (monomial n a * monomial m b)
      = transferTo q (monomial n a) * transferTo q (monomial m b) := by
  rw [Polynomial.monomial_mul_monomial]
  simp only [transferTo_monomial]
  refine Alg.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [fst_mkAlg, Unitization.fst_mul, Polynomial.monomial_mul_monomial]
  · simp only [fst_mkAlg, α₁_mkAlg, Alg.α₁_mul, map_add, Polynomial.monomial_mul_monomial]
    rw [Nat.add_comm m n]
  · simp only [fst_mkAlg, α₂_mkAlg, Alg.α₂_mul, map_add, Polynomial.monomial_mul_monomial]
    rw [Nat.add_comm m n]
  · simp only [fst_mkAlg, α₃_mkAlg, Alg.α₃_mul, map_add, Polynomial.monomial_mul_monomial]
    rw [Nat.add_comm m n]
  · simp only [fst_mkAlg, α₂_mkAlg, α₃_mkAlg, γ₁_mkAlg, Alg.γ₁_mul, map_add,
      Polynomial.monomial_mul_monomial]
    rw [Nat.add_comm m n]
  · simp only [fst_mkAlg, α₁_mkAlg, α₂_mkAlg, α₃_mkAlg, γ₂_mkAlg, Alg.γ₂_mul, map_add,
      Polynomial.monomial_mul_monomial]
    rw [Nat.add_comm m n]
  · simp only [fst_mkAlg, α₁_mkAlg, α₃_mkAlg, σ_mkAlg, Alg.σ_mul, map_add,
      Polynomial.monomial_mul_monomial, quoPolyEquiv_monomial_mk]
    rw [quoPolyEquiv_monomial_smul, quoPolyEquiv_monomial_smul']

theorem transferTo_mul (q : ℕ) (p r : Polynomial (A q)) :
    transferTo q (p * r) = transferTo q p * transferTo q r := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p₁ p₂ h₁ h₂
    rw [add_mul, transferTo_add, transferTo_add, h₁, h₂, add_mul]
  · intro n a
    refine Polynomial.induction_on' r ?_ ?_
    · intro r₁ r₂ h₁ h₂
      rw [mul_add, transferTo_add, transferTo_add, h₁, h₂, mul_add]
    · intro m b
      exact transferTo_monomial_mul q n m a b

end Transfer

open Transfer in
/-- **F2.**  The transfer isomorphism `A_q[X] ≃+* Alg (D[X]) (C t) q`.

It is a genuine `RingEquiv`: `map_add'` is `Transfer.transferTo_add`, `map_mul'`
is `Transfer.transferTo_mul` (proved from the monomial case
`Transfer.transferTo_monomial_mul`, which checks all seven coordinates of the
frozen multiplication table against polynomial convolution), and *both* inverse
laws — `Transfer.transferInv_transferTo` and `Transfer.transferTo_transferInv` —
are proved.  Nothing here uses the Stage-C cancellation, which is FALSE at the
base `Polynomial Dbase`. -/
noncomputable def transferEquiv (q : ℕ) :
    Polynomial (A q) ≃+* Alg (Polynomial Dbase) (Polynomial.C tD) q where
  toFun := transferTo q
  invFun := transferInv q
  left_inv := transferInv_transferTo q
  right_inv := transferTo_transferInv q
  map_mul' := transferTo_mul q
  map_add' := transferTo_add q

@[simp] theorem transferEquiv_apply (q : ℕ) (p : Polynomial (A q)) :
    transferEquiv q p = Transfer.transferTo q p := rfl

@[simp] theorem transferEquiv_symm_apply (q : ℕ)
    (z : Alg (Polynomial Dbase) (Polynomial.C tD) q) :
    (transferEquiv q).symm z = Transfer.transferInv q z := rfl

/-- `transferEquiv` on constants: it is the coefficientwise `C`-inclusion, with
`quoPolyEquiv` (F1) on the `s`-coordinate.  Together with `transferEquiv_X` this
pins the map down completely, since `C` and `X` generate `A_q[X]` as a ring. -/
theorem transferEquiv_C (q : ℕ) (a : A q) :
    transferEquiv q (Polynomial.C a)
      = Transfer.mkAlg (Polynomial.C a.fst) (Polynomial.C (Alg.α₁ a))
          (Polynomial.C (Alg.α₂ a)) (Polynomial.C (Alg.α₃ a)) (Polynomial.C (Alg.γ₁ a))
          (Polynomial.C (Alg.γ₂ a)) (quoPolyEquiv q (Polynomial.C (Alg.σ a))) :=
  Transfer.transferTo_C q a

/-- `transferEquiv` sends the variable `X` of `A_q[X]` to the variable `X` of the
new base ring `D[X]`. -/
theorem transferEquiv_X (q : ℕ) :
    transferEquiv q (X : Polynomial (A q))
      = algebraMap (Polynomial Dbase) (Alg (Polynomial Dbase) (Polynomial.C tD) q) X :=
  Transfer.transferTo_X q

/-! ## F3 — the frozen `isNAbsorbing_polyExt_A_succ_succ_q`

The `q + 2` upper bound at the polynomial base.  Note carefully which Stage-E
bound is used: `irredundant_len_le_generic`, the one that does **not** assume the
characteristic-2 cancellation `hcanc`.  At `B = Polynomial Dbase`,
`τ = Polynomial.C tD` that cancellation is FALSE (`hcanc_polyDbase_false`), and
that asymmetry between `Dbase` (where `q + 1` holds) and `Polynomial Dbase`
(where only `q + 2` holds) is exactly the counterexample of Problem 30(c). -/

/-- The zero ideal of `Alg B τ q` is `(q+2)`-absorbing whenever `B` is a domain
and `τ` is prime — no cancellation hypothesis.  This is Stage E's generic bound
`irredundant_len_le_generic` repackaged through Stage A's `absorbing_iff_no_irredundant`,
exactly as `isNAbsorbing_A_succ_q_proof` repackages the `hcanc` version. -/
theorem isNAbsorbing_bot_Alg_generic {B : Type} [CommRing B] [IsDomain B] {τ : B}
    (hτ : Prime τ) {q : ℕ} (hq : 1 ≤ q) :
    IsNAbsorbing (⊥ : Ideal (Alg B τ q)) (q + 2) := by
  rw [absorbing_iff_no_irredundant]
  rintro ⟨a, ha, hj⟩
  have h0 : ∏ i, a i = 0 := Ideal.mem_bot.1 ha
  have hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0 := fun j h =>
    hj j (Ideal.mem_bot.2 h)
  have hlen := irredundant_len_le_generic hτ hq a h0 hirr
  omega

/-- Frozen statement `isNAbsorbing_polyExt_A_succ_succ_q`, proved: `0[X]` is
`(q+2)`-absorbing in `A_q[X]`.  `polyExt ⊥ = ⊥` (Stage A) reduces the claim to the
zero ideal of `A_q[X] ≃+* Alg (D[X]) (C t) q` (F2's `transferEquiv`), where the
generic — `hcanc`-free — Stage E bound applies with `Prime (C tD)` from `prime_C_tD`
and `IsDomain (Polynomial Dbase)` from instance search. -/
theorem isNAbsorbing_polyExt_A_succ_succ_q_proof (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (polyExt (⊥ : Ideal (A q))) (q + 2) := by
  rw [polyExt_bot]
  exact isNAbsorbing_congr_ringEquiv (transferEquiv q).symm
    (isNAbsorbing_bot_Alg_generic prime_C_tD (by omega))

end Prob30c
