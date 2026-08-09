/-
# Prob27b — Stage A support file

Stage A of `BLUEPRINT.md` Part 2: the algebra `RAlg` and the finite ring `R`
(items A1–A6).

Everything here is proved for a **general** `[CommRing k]` (except A4/A5, which
are statements about `R = RAlg (ZMod 2)` itself), so that Stages B–F get the same
API over `ZMod 2`, `D` and `K` alike.
-/
import Prob27b.Defs

namespace Prob27b

/-! ## Stage A cheat-watch guardrails

These fix the multiplication convention **before** anything is built on top of
it: paths compose left to right (`e·u = u`, `u·e = 0`, `u·v = p`, `u·q = s`),
`1 = e + f ≠ e`, and `s ≠ 0`.  All are kernel-checked by `decide` over the
256-element ring `R`. -/

example : (RAlg.u : R) * RAlg.v = RAlg.p := by decide
example : (RAlg.u : R) * RAlg.e = 0 := by decide
example : (RAlg.e : R) * RAlg.u = RAlg.u := by decide
example : (RAlg.u : R) * RAlg.q = RAlg.s := by decide
example : ((RAlg.u : R) + RAlg.v) ^ 4 = 0 := by decide
example : (1 : R) ≠ RAlg.e := by decide
example : (RAlg.s : R) ≠ 0 := by decide

namespace RAlg

variable {k l : Type} [CommRing k] [CommRing l]

/-! ## A1 — the public coordinate API

The `Defs.lean` versions (`cm0 … cm7`) are `private` + `local`, so the public
`RAlg.coeff_mul_*` names are free.  Every one is `rfl`. -/

@[simp] theorem coeff_add (x y : RAlg k) (i : Fin 8) :
    (x + y).coeff i = x.coeff i + y.coeff i := rfl

@[simp] theorem coeff_neg (x : RAlg k) (i : Fin 8) : (-x).coeff i = -x.coeff i := rfl

@[simp] theorem coeff_smul (c : k) (x : RAlg k) (i : Fin 8) :
    (c • x).coeff i = c * x.coeff i := rfl

@[simp] theorem coeff_zero (i : Fin 8) : (0 : RAlg k).coeff i = 0 := by fin_cases i <;> rfl

@[simp] theorem coeff_one (i : Fin 8) :
    (1 : RAlg k).coeff i = ![1, 1, 0, 0, 0, 0, 0, 0] i := rfl

@[simp] theorem coeff_single (i j : Fin 8) (c : k) :
    (single i c).coeff j = if j = i then c else 0 := rfl

@[simp] theorem coeff_mul_zero (x y : RAlg k) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := rfl

@[simp] theorem coeff_mul_one (x y : RAlg k) :
    (x * y).coeff 1 = x.coeff 1 * y.coeff 1 := rfl

@[simp] theorem coeff_mul_two (x y : RAlg k) :
    (x * y).coeff 2 = x.coeff 0 * y.coeff 2 + x.coeff 2 * y.coeff 1 := rfl

@[simp] theorem coeff_mul_three (x y : RAlg k) :
    (x * y).coeff 3 = x.coeff 1 * y.coeff 3 + x.coeff 3 * y.coeff 0 := rfl

@[simp] theorem coeff_mul_four (x y : RAlg k) :
    (x * y).coeff 4 = x.coeff 0 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 4 * y.coeff 0 :=
  rfl

@[simp] theorem coeff_mul_five (x y : RAlg k) :
    (x * y).coeff 5 = x.coeff 1 * y.coeff 5 + x.coeff 3 * y.coeff 2 + x.coeff 5 * y.coeff 1 :=
  rfl

@[simp] theorem coeff_mul_six (x y : RAlg k) : (x * y).coeff 6 =
    x.coeff 0 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 4 * y.coeff 2 + x.coeff 6 * y.coeff 1 :=
  rfl

@[simp] theorem coeff_mul_seven (x y : RAlg k) : (x * y).coeff 7 =
    x.coeff 1 * y.coeff 7 + x.coeff 3 * y.coeff 4 + x.coeff 5 * y.coeff 3 + x.coeff 7 * y.coeff 0 :=
  rfl

/-! ## A2 — the basis products

The frozen table of `Defs.lean`, spelled out for the eight basis paths.  These
are the only products the rest of the development needs. -/

theorem e_mul_e : (e : RAlg k) * e = e := by ext i; fin_cases i <;> simp [e]

theorem e_mul_f : (e : RAlg k) * f = 0 := by ext i; fin_cases i <;> simp [e, f]

theorem e_mul_u : (e : RAlg k) * u = u := by ext i; fin_cases i <;> simp [e, u]

theorem u_mul_e : (u : RAlg k) * e = 0 := by ext i; fin_cases i <;> simp [e, u]

theorem u_mul_f : (u : RAlg k) * f = u := by ext i; fin_cases i <;> simp [f, u]

theorem u_mul_u : (u : RAlg k) * u = 0 := by ext i; fin_cases i <;> simp [u]

theorem u_mul_v : (u : RAlg k) * v = p := by ext i; fin_cases i <;> simp [u, v, p]

theorem v_mul_u : (v : RAlg k) * u = q := by ext i; fin_cases i <;> simp [u, v, q]

theorem u_mul_q : (u : RAlg k) * q = s := by ext i; fin_cases i <;> simp [u, q, s]

theorem p_mul_u : (p : RAlg k) * u = s := by ext i; fin_cases i <;> simp [u, p, s]

theorem v_mul_p : (v : RAlg k) * p = w := by ext i; fin_cases i <;> simp [v, p, w]

theorem q_mul_v : (q : RAlg k) * v = w := by ext i; fin_cases i <;> simp [v, q, w]

theorem u_mul_p : (u : RAlg k) * p = 0 := by ext i; fin_cases i <;> simp [u, p]

theorem u_mul_w : (u : RAlg k) * w = 0 := by ext i; fin_cases i <;> simp [u, w]

theorem v_mul_q : (v : RAlg k) * q = 0 := by ext i; fin_cases i <;> simp [v, q]

theorem s_mul_v : (s : RAlg k) * v = 0 := by ext i; fin_cases i <;> simp [s, v]

theorem e_mul_s : (e : RAlg k) * s = s := by ext i; fin_cases i <;> simp [e, s]

theorem e_mul_w : (e : RAlg k) * w = 0 := by ext i; fin_cases i <;> simp [e, w]

/-- The Step-3 identity `(e + u)·e = e`: this is why the `X⁴` coefficient of `F`
survives right multiplication by `e` while the `X²` one dies. -/
theorem eu_mul_e : ((e : RAlg k) + u) * e = e := by ext i; fin_cases i <;> simp [e, u]

/-- `1 = e + f` — in particular `1 ≠ e`, the ring is not local at `e`. -/
theorem one_eq_e_add_f : (1 : RAlg k) = e + f := by ext i; fin_cases i <;> simp [e, f]

/-! ## A3 — the powers of `a₀ = u + v` -/

theorem a0_sq : ((u : RAlg k) + v) ^ 2 = p + q := by
  rw [pow_two]; ext i; fin_cases i <;> simp [u, v, p, q]

theorem a0_cube : ((u : RAlg k) + v) ^ 3 = s + w := by
  rw [pow_succ, a0_sq]; ext i; fin_cases i <;> simp [u, v, p, q, s, w]

theorem a0_pow_four : ((u : RAlg k) + v) ^ 4 = 0 := by
  rw [pow_succ, a0_cube]; ext i; fin_cases i <;> simp [u, v, s, w]

theorem a0_pow_five : ((u : RAlg k) + v) ^ 5 = 0 := by
  rw [pow_succ, a0_pow_four, zero_mul]

theorem a0_pow_six : ((u : RAlg k) + v) ^ 6 = 0 := by
  rw [pow_succ, a0_pow_five, zero_mul]

/-- The Step-3 punchline in element form: `e·(u+v)³ = e·(s+w) = s`. -/
theorem e_mul_a0_cubed : (e : RAlg k) * ((u : RAlg k) + v) ^ 3 = s := by
  rw [a0_cube, mul_add, e_mul_s, e_mul_w, add_zero]

/-! ## A6 — functoriality on the basis -/

@[simp] theorem coeff_map (φ : k →+* l) (x : RAlg k) (i : Fin 8) :
    (map φ x).coeff i = φ (x.coeff i) := rfl

theorem map_single (φ : k →+* l) (i : Fin 8) (c : k) :
    map φ (single i c) = single i (φ c) := by
  ext j; simp only [coeff_map, coeff_single]; split_ifs <;> simp

theorem map_e (φ : k →+* l) : map φ (e : RAlg k) = e := by
  simp only [e, map_single, _root_.map_one]

theorem map_f (φ : k →+* l) : map φ (f : RAlg k) = f := by
  simp only [f, map_single, _root_.map_one]

theorem map_u (φ : k →+* l) : map φ (u : RAlg k) = u := by
  simp only [u, map_single, _root_.map_one]

theorem map_v (φ : k →+* l) : map φ (v : RAlg k) = v := by
  simp only [v, map_single, _root_.map_one]

theorem map_p (φ : k →+* l) : map φ (p : RAlg k) = p := by
  simp only [p, map_single, _root_.map_one]

theorem map_q (φ : k →+* l) : map φ (q : RAlg k) = q := by
  simp only [q, map_single, _root_.map_one]

theorem map_s (φ : k →+* l) : map φ (s : RAlg k) = s := by
  simp only [s, map_single, _root_.map_one]

theorem map_w (φ : k →+* l) : map φ (w : RAlg k) = w := by
  simp only [w, map_single, _root_.map_one]

end RAlg

/-! ## A4 — `Nat.card R = 2 ^ 8` (frozen 1) -/

/-- **Frozen 1.**  `R` has `2⁸` elements: it is the set of coordinate vectors
`Fin 8 → ZMod 2`, transported along `RAlg.equivFun`. -/
theorem R_card_eq_proof : Nat.card R = 2 ^ 8 := by
  rw [Nat.card_congr (RAlg.equivFun (k := ZMod 2)), Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-! ## A5 — `R` is not commutative (frozen 2) -/

/-- **Frozen 2.**  `u·v = p ≠ q = v·u`, so `R` is noncommutative — checked in the
kernel inside `R` itself, not in some auxiliary algebra. -/
theorem R_not_commutative_proof : ∃ x y : R, x * y ≠ y * x :=
  ⟨RAlg.u, RAlg.v, by decide⟩

end Prob27b

/-! ## The clean restatements of the frozen Stage-A theorems -/

namespace Prob27b.Solution

/-- **Frozen 1.** `R` has `2⁸` elements (Step 1, "size `2⁸`"). -/
theorem R_card_eq : Nat.card R = 2 ^ 8 := Prob27b.R_card_eq_proof

/-- **Frozen 2.** `R` is noncommutative (Step 1, "noncommutative"). -/
theorem R_not_commutative : ∃ x y : R, x * y ≠ y * x := Prob27b.R_not_commutative_proof

end Prob27b.Solution
