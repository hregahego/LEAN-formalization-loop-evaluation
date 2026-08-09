/-
# Prob27b — FROZEN definitions

Problem 27(b): `Int(A)` need not be a ring even when `D` has finite residue rings.

`D = 𝔽₂[π] = Polynomial (ZMod 2)`, `K = 𝔽₂(π) = RatFunc (ZMod 2)`, and `R`, `A`,
`B` are the **same** 8-dimensional structure-constant algebra `RAlg k` — the path
algebra of `e ⟶u f ⟶v e` truncated in degree `≥ 4` — over `𝔽₂`, `D` and `K`
respectively.

This file is **frozen** after SETUP: its SHA-256 is pinned in
`scripts/frozen.sha256` and it may never be edited during the proving phase.
Every modeling decision recorded in `BLUEPRINT.md` Part −1 §2 is realised here.
`USER_NOTES.md` permits **no assumed axioms**, so this file declares none.
-/
import Mathlib

namespace Prob27b

/-! ## D1 — `RAlg k`, the truncated path algebra with coefficients in `k` -/

/-- The truncated path algebra of the quiver `e ⟶u f ⟶v e` with coefficients in
`k`, presented by its eight structure constants.

Basis index: `0 = e`, `1 = f`, `2 = u`, `3 = v`, `4 = p = uv`, `5 = q = vu`,
`6 = s = uvu`, `7 = w = vuv`.

MODELING DECISION: a `structure` wrapper (not `def RAlg k := Fin 8 → k`), so
instance search can never unfold it and pick up `Pi.ring`'s *componentwise*
multiplication. -/
structure RAlg (k : Type) [CommRing k] where
  /-- The coordinate vector in the frozen basis `e, f, u, v, p, q, s, w`. -/
  coeff : Fin 8 → k

namespace RAlg

variable {k l : Type} [CommRing k] [CommRing l]

/-- Componentwise extensionality (D4). -/
@[ext] theorem ext {x y : RAlg k} (h : ∀ i, x.coeff i = y.coeff i) : x = y := by
  cases x; cases y; simp only [mk.injEq]; exact funext h

/-! ## D2 — the frozen structure-constant table -/

/-- The zero element `⟨![0,0,0,0,0,0,0,0]⟩`. -/
protected def zero : RAlg k := ⟨![0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- The unit `1 = e + f = ⟨![1,1,0,0,0,0,0,0]⟩`.  Note `1 ≠ RAlg.e`. -/
protected def one : RAlg k := ⟨![1, 1, 0, 0, 0, 0, 0, 0]⟩

/-- Componentwise addition. -/
protected def add (x y : RAlg k) : RAlg k := ⟨fun i => x.coeff i + y.coeff i⟩

/-- Componentwise negation. -/
protected def neg (x : RAlg k) : RAlg k := ⟨fun i => -x.coeff i⟩

/-- Componentwise subtraction. -/
protected def sub (x y : RAlg k) : RAlg k := ⟨fun i => x.coeff i - y.coeff i⟩

/-- Componentwise `ℕ`-scaling. -/
protected def nsmul (n : ℕ) (x : RAlg k) : RAlg k := ⟨fun i => n • x.coeff i⟩

/-- Componentwise `ℤ`-scaling. -/
protected def zsmul (n : ℤ) (x : RAlg k) : RAlg k := ⟨fun i => n • x.coeff i⟩

/-- Componentwise `k`-scaling. -/
protected def smul (c : k) (x : RAlg k) : RAlg k := ⟨fun i => c * x.coeff i⟩

/-- Multiplication, given by the frozen structure constants of the truncated path
algebra.  Paths compose **left to right**: `u : e → f`, `v : f → e`, and `x·y` is
"first `x`, then `y`", zero when `end x ≠ start y` or when the length reaches `4`.
Hence `e·u = u`, `u·e = 0`, `u·v = p`, `v·u = q`, `u·q = s`, `p·u = s`,
`v·p = w`, `q·v = w`, `s·f = s`, `w·e = w`. -/
protected def mul (x y : RAlg k) : RAlg k := ⟨![
  x.coeff 0 * y.coeff 0,
  x.coeff 1 * y.coeff 1,
  x.coeff 0 * y.coeff 2 + x.coeff 2 * y.coeff 1,
  x.coeff 1 * y.coeff 3 + x.coeff 3 * y.coeff 0,
  x.coeff 0 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 4 * y.coeff 0,
  x.coeff 1 * y.coeff 5 + x.coeff 3 * y.coeff 2 + x.coeff 5 * y.coeff 1,
  x.coeff 0 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 4 * y.coeff 2 + x.coeff 6 * y.coeff 1,
  x.coeff 1 * y.coeff 7 + x.coeff 3 * y.coeff 4 + x.coeff 5 * y.coeff 3 + x.coeff 7 * y.coeff 0]⟩

instance instZero : Zero (RAlg k) := ⟨RAlg.zero⟩
instance instOne : One (RAlg k) := ⟨RAlg.one⟩
instance instAdd : Add (RAlg k) := ⟨RAlg.add⟩
instance instNeg : Neg (RAlg k) := ⟨RAlg.neg⟩
instance instMul : Mul (RAlg k) := ⟨RAlg.mul⟩
instance instSMul : SMul k (RAlg k) := ⟨RAlg.smul⟩

/-! ### Private coordinate lemmas, used only to discharge the instances below.

They are `private` on purpose: `BLUEPRINT.md` Stage A owns the public
`RAlg.coeff_mul_*` API, and nothing in `Defs.lean` may pre-empt those names. -/

@[local simp] private theorem cz (i : Fin 8) : (0 : RAlg k).coeff i = 0 := by
  fin_cases i <;> rfl
@[local simp] private theorem ca (x y : RAlg k) (i : Fin 8) :
    (x + y).coeff i = x.coeff i + y.coeff i := rfl
@[local simp] private theorem cn (x : RAlg k) (i : Fin 8) : (-x).coeff i = -x.coeff i := rfl
@[local simp] private theorem cs (c : k) (x : RAlg k) (i : Fin 8) :
    (c • x).coeff i = c * x.coeff i := rfl
@[local simp] private theorem csub (x y : RAlg k) (i : Fin 8) :
    (RAlg.sub x y).coeff i = x.coeff i - y.coeff i := rfl
@[local simp] private theorem cns (n : ℕ) (x : RAlg k) (i : Fin 8) :
    (RAlg.nsmul n x).coeff i = n • x.coeff i := rfl
@[local simp] private theorem czs (n : ℤ) (x : RAlg k) (i : Fin 8) :
    (RAlg.zsmul n x).coeff i = n • x.coeff i := rfl
@[local simp] private theorem co0 : (1 : RAlg k).coeff 0 = 1 := rfl
@[local simp] private theorem co1 : (1 : RAlg k).coeff 1 = 1 := rfl
@[local simp] private theorem co2 : (1 : RAlg k).coeff 2 = 0 := rfl
@[local simp] private theorem co3 : (1 : RAlg k).coeff 3 = 0 := rfl
@[local simp] private theorem co4 : (1 : RAlg k).coeff 4 = 0 := rfl
@[local simp] private theorem co5 : (1 : RAlg k).coeff 5 = 0 := rfl
@[local simp] private theorem co6 : (1 : RAlg k).coeff 6 = 0 := rfl
@[local simp] private theorem co7 : (1 : RAlg k).coeff 7 = 0 := rfl
@[local simp] private theorem cm0 (x y : RAlg k) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := rfl
@[local simp] private theorem cm1 (x y : RAlg k) :
    (x * y).coeff 1 = x.coeff 1 * y.coeff 1 := rfl
@[local simp] private theorem cm2 (x y : RAlg k) :
    (x * y).coeff 2 = x.coeff 0 * y.coeff 2 + x.coeff 2 * y.coeff 1 := rfl
@[local simp] private theorem cm3 (x y : RAlg k) :
    (x * y).coeff 3 = x.coeff 1 * y.coeff 3 + x.coeff 3 * y.coeff 0 := rfl
@[local simp] private theorem cm4 (x y : RAlg k) :
    (x * y).coeff 4 = x.coeff 0 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 4 * y.coeff 0 := rfl
@[local simp] private theorem cm5 (x y : RAlg k) :
    (x * y).coeff 5 = x.coeff 1 * y.coeff 5 + x.coeff 3 * y.coeff 2 + x.coeff 5 * y.coeff 1 := rfl
@[local simp] private theorem cm6 (x y : RAlg k) : (x * y).coeff 6 =
    x.coeff 0 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 4 * y.coeff 2 + x.coeff 6 * y.coeff 1 :=
  rfl
@[local simp] private theorem cm7 (x y : RAlg k) : (x * y).coeff 7 =
    x.coeff 1 * y.coeff 7 + x.coeff 3 * y.coeff 4 + x.coeff 5 * y.coeff 3 + x.coeff 7 * y.coeff 0 :=
  rfl

/-! ## D3 — the instances (all discharged here; no `sorry` in this file) -/

/-- `RAlg k` is an associative, **noncommutative**, unital ring with `1 = e + f`. -/
instance instRing : Ring (RAlg k) where
  add := (· + ·)
  add_assoc a b c := by ext i; simp; ring
  zero := 0
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp; ring
  neg := (- ·)
  sub := RAlg.sub
  sub_eq_add_neg a b := by ext i; exact sub_eq_add_neg _ _
  nsmul := RAlg.nsmul
  nsmul_zero x := by ext i; simp
  nsmul_succ n x := by ext i; simp; ring
  zsmul := RAlg.zsmul
  zsmul_zero' x := by ext i; simp
  zsmul_succ' n x := by ext i; simp; ring
  zsmul_neg' n x := by ext i; simp; ring
  neg_add_cancel a := by ext i; simp
  mul := (· * ·)
  mul_assoc a b c := by ext i; fin_cases i <;> simp <;> ring
  one := 1
  one_mul a := by ext i; fin_cases i <;> simp
  mul_one a := by ext i; fin_cases i <;> simp
  left_distrib a b c := by ext i; fin_cases i <;> simp <;> ring
  right_distrib a b c := by ext i; fin_cases i <;> simp <;> ring
  zero_mul a := by ext i; fin_cases i <;> simp
  mul_zero a := by ext i; fin_cases i <;> simp

/-- The coordinate equivalence `RAlg k ≃ (Fin 8 → k)` (D4). -/
def equivFun : RAlg k ≃ (Fin 8 → k) where
  toFun := RAlg.coeff
  invFun := RAlg.mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- MODELING DECISION: this must be the **computable** decidable equality — never
`Classical.decEq` — or Stage B's kernel `decide` stops reducing. -/
instance instDecidableEq [DecidableEq k] : DecidableEq (RAlg k) := fun x y =>
  decidable_of_iff (x.coeff = y.coeff) ⟨fun h => by ext i; rw [h], fun h => by rw [h]⟩

/-- MODELING DECISION: this must be the **computable** `Fintype` transported along
`equivFun` — never `Fintype.ofFinite` — or Stage B's kernel `decide` stops
reducing. -/
instance instFintype [Fintype k] [DecidableEq k] : Fintype (RAlg k) :=
  Fintype.ofEquiv _ RAlg.equivFun.symm

/-- The structural map `k → RAlg k`, `c ↦ c • 1 = c·e + c·f`; its image is central
because scalars act componentwise. -/
def coeHom : k →+* RAlg k where
  toFun c := ⟨![c, c, 0, 0, 0, 0, 0, 0]⟩
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' a b := by ext i; fin_cases i <;> simp
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' a b := by ext i; fin_cases i <;> simp

@[local simp] private theorem cc (c : k) (i : Fin 8) :
    (RAlg.coeHom c).coeff i = ![c, c, 0, 0, 0, 0, 0, 0] i := rfl

/-- `RAlg k` is a `k`-algebra; `Module k (RAlg k)` and `SMul k (RAlg k)` come from
here (and agree definitionally with `RAlg.smul`). -/
instance instAlgebra : Algebra k (RAlg k) where
  algebraMap := RAlg.coeHom
  smul := (· • ·)
  commutes' r x := by ext i; fin_cases i <;> simp <;> ring
  smul_def' r x := by ext i; fin_cases i <;> simp

/-! ## D5, D6 — `single` and the eight basis paths -/

/-- The element with coefficient `c` in slot `i` and `0` elsewhere. -/
def single (i : Fin 8) (c : k) : RAlg k := ⟨fun j => if j = i then c else 0⟩

/-- The idempotent path `e` (the vertex `e`).  Note `RAlg.e ≠ 1`. -/
def e : RAlg k := single 0 1
/-- The idempotent path `f` (the vertex `f`). -/
def f : RAlg k := single 1 1
/-- The arrow `u : e → f`. -/
def u : RAlg k := single 2 1
/-- The arrow `v : f → e`. -/
def v : RAlg k := single 3 1
/-- The path `p = uv : e → e`. -/
def p : RAlg k := single 4 1
/-- The path `q = vu : f → f`. -/
def q : RAlg k := single 5 1
/-- The path `s = uvu : e → f`. -/
def s : RAlg k := single 6 1
/-- The path `w = vuv : f → e`. -/
def w : RAlg k := single 7 1

/-! ## D7 — functoriality -/

/-- Coefficientwise functoriality, as a `RingHom` (needed so that `iota` and
`redPi` transport products and so that `Polynomial.map` applies). -/
def map (φ : k →+* l) : RAlg k →+* RAlg l where
  toFun x := ⟨fun i => φ (x.coeff i)⟩
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' a b := by ext i; fin_cases i <;> simp
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' a b := by ext i; fin_cases i <;> simp

end RAlg

/-! ## D8, D9 — the arithmetic setting `D`, `K`, `π`, `R`, `A`, `B`

MODELING DECISION: these are `abbrev`s, so every Mathlib instance on
`Polynomial (ZMod 2)`, `RatFunc (ZMod 2)` and `RAlg _` applies without
re-declaration.  `K` is Mathlib's genuine field of rational functions
(`IsFractionRing D K` holds), not a hand-rolled localization. -/

/-- `D = 𝔽₂[π]`. -/
abbrev D : Type := Polynomial (ZMod 2)

/-- `K = 𝔽₂(π)`, the fraction field of `D`. -/
abbrev K : Type := RatFunc (ZMod 2)

/-- The uniformiser `π = X ∈ D`. -/
noncomputable def pi : D := Polynomial.X

/-- `R = RAlg 𝔽₂`, the finite ring of Step 1 (size `2⁸`). -/
abbrev R : Type := RAlg (ZMod 2)

/-- `A = RAlg D`; this is the sketch's `A = D ⊗_{𝔽₂} R`, presented by the same
structure constants (its free-module content is frozen as `A_isFreeOfRankEight`). -/
abbrev A : Type := RAlg D

/-- `B = RAlg K`; this is the fraction algebra `K ⊗_D A`, where `Int(A)` lives. -/
abbrev B : Type := RAlg K

/-! ## D10, D11, D12 — the three coefficient maps -/

/-- The embedding `A ↪ B` induced by `D ↪ K`. -/
noncomputable def iota : A →+* B := RAlg.map (algebraMap D K)

/-- Reduction mod `π`, realising `A/πA ≅ R` without a noncommutative quotient. -/
noncomputable def redPi : A →+* R := RAlg.map (Polynomial.evalRingHom 0)

/-- `1/π ∈ K`, the scalar that turns `F̃` into `P`. -/
noncomputable def invPi : K := (algebraMap D K pi)⁻¹

/-! ## D13, D14, D15, D16 — the polynomials

MODELING DECISION: built with `Polynomial.monomial n c`, not `C c * X ^ n`.
`Polynomial.eval` is `p.sum fun n c => c * x ^ n`, so coefficients multiply on the
**left** — exactly the sketch's `F(r) = u r² + e r³ + …`, i.e. the notion of a
*right* null polynomial.  Over the noncommutative `R` only `eval_monomial`,
`eval_add` and `eval_C` are available. -/

/-- `F = uX² + eX³ + (e+u)X⁴ + eX⁵ + eX⁶ ∈ R[X]` (Step 2). -/
noncomputable def F : Polynomial R :=
  Polynomial.monomial 2 RAlg.u + Polynomial.monomial 3 RAlg.e
    + Polynomial.monomial 4 (RAlg.e + RAlg.u)
    + Polynomial.monomial 5 RAlg.e + Polynomial.monomial 6 RAlg.e

/-- `F̃ ∈ A[X]`, the literal lift of `F` (each `𝔽₂`-coefficient `1` becomes
`1 : D`) (Step 4). -/
noncomputable def Ftilde : Polynomial A :=
  Polynomial.monomial 2 RAlg.u + Polynomial.monomial 3 RAlg.e
    + Polynomial.monomial 4 (RAlg.e + RAlg.u)
    + Polynomial.monomial 5 RAlg.e + Polynomial.monomial 6 RAlg.e

/-- `P = F̃/π ∈ B[X]`, rendered as the `K`-scalar multiple `invPi • (F̃.map ι)`. -/
noncomputable def P : Polynomial B := invPi • (Ftilde.map iota)

/-- The witness `a₀ = u + v ∈ A` at which `P·e` fails to be integral (Step 5). -/
noncomputable def a0 : A := RAlg.u + RAlg.v

/-! ## D17, D18 — the two predicates

MODELING DECISION: `IsNullPoly` is the sketch's `K(R)`, the set of **right null
polynomials** — `∀ r : R`, unrestricted.  `IsIntegerValued` is the textbook
`Int(A) = {P ∈ B[X] : P(a) ∈ A for all a ∈ A}`: the polynomial lives in `B[X]`
(so `π` may sit in a denominator), `x` ranges over **all** of `A`, and "lands in
`A`" is membership in `Set.range iota`. -/

/-- `p ∈ K(R)`: `p` is a right null polynomial of `R`. -/
def IsNullPoly (p : Polynomial R) : Prop := ∀ r : R, p.eval r = 0

/-- `p ∈ Int(A)`: `p ∈ B[X]` takes every element of `A` into `A`. -/
def IsIntegerValued (p : Polynomial B) : Prop :=
  ∀ x : A, p.eval (iota x) ∈ Set.range iota

end Prob27b
