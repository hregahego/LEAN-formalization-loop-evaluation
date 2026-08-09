/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import Mathlib

/-!
# Frozen definitions for the `1196/3125` entropy bound

This file is **FROZEN**: after the SETUP stage it is never edited again, and its SHA-256 is
pinned in `scripts/frozen.sha256`.  Every object needed by the frozen theorem statements of
`EntropyBound/Theorems.lean` is defined here, in dependency order, following
`BLUEPRINT.md` Part -1 §2.

Modeling decisions (binding for every later stage):

* Everything is in **natural-log units**; the base-2 quantities `h`, `e` of `SKETCH.md`
  never appear, and every conversion factor `Real.log 2` is written out explicitly.
* Probability is **finitary**: a distribution is a nonnegative weight function on a
  `Fintype` summing to `1`, and every expectation is a `Finset.sum`.  No `MeasureTheory`,
  no `PMF`, no `ProbabilityTheory` entropy.
* All numeric constants are exact rationals coerced into `ℝ`; never `Float`.
* `USER_NOTES.md` permits **no** assumed-certificate axioms, so this file declares no
  `axiom`s at all.
-/

namespace EntropyBound

/-! ### Combinatorics -/

/-- A finite family of finite sets is union-closed when it contains the union of any two of
its members.  This is the textbook predicate verbatim, over an arbitrary `DecidableEq` type. -/
def UnionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- The union on the Boolean cube: coordinatewise `or`. -/
def orVec {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool := fun i => x i || y i

/-- The cube-side mirror of `UnionClosed`. -/
def UnionClosedCube {n : ℕ} (G : Finset (Fin n → Bool)) : Prop :=
  ∀ x ∈ G, ∀ y ∈ G, orVec x y ∈ G

/-- The length-`i` prefix of `x`, represented as a masked full vector: coordinates below `i`
are kept, coordinates from `i` on are set to `false`. -/
def pref {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if (j : ℕ) < i then x j else false

/-! ### Exact rational constants -/

/- Everything below is real-valued, hence noncomputable. -/
noncomputable section

/-- The headline frequency constant `c = 1196/3125 = 0.38272`. -/
def cval : ℝ := 1196 / 3125

/-- The scalar-inequality constant `C = 81001/50000 = 1.62002`. -/
def Cval : ℝ := 81001 / 50000

/-- The coupling strength `λ = 9/10`. -/
def lam : ℝ := 9 / 10

/-! ### Scalar analysis: entropy, kernel, profile -/

/-- Natural-log binary entropy `-z log z - (1-z) log (1-z)`, defined directly from
`Real.log`.  Mathlib's `Real.log 0 = 0` supplies the junk-value convention `0 log 0 = 0`. -/
def Hnat (z : ℝ) : ℝ := -z * Real.log z - (1 - z) * Real.log (1 - z)

/-- The normalized entropy `e(s) = H(s)/s`.  Total function; `enat 0 = 0` by `x / 0 = 0`. -/
def enat (s : ℝ) : ℝ := Hnat s / s

/-- The coupling kernel `q(s,t) = s t (1 + λ² (1-s)(1-t))` with `λ² = 81/100`. -/
def qker (s t : ℝ) : ℝ := s * t * (1 + (81 / 100) * (1 - s) * (1 - t))

/-- The coupling profile `g(s)`, defined by the square root of the product form. -/
def gprof (s : ℝ) : ℝ :=
  2 * Real.sqrt ((1 + (81 / 100) * (1 - s) ^ 2) *
    (1 - s ^ 2 * (1 + (81 / 100) * (1 - s) ^ 2)))

/-! ### Series objects

All series are honest `tsum`s over `ℕ`, reindexed to start at `0`; the `+1`/`+2` shifts in
the denominators are part of the frozen text. -/

/-- The auxiliary series `f(z) = ∑_{k ≥ 1} zᵏ / (k (k+1))`. -/
def fser (z : ℝ) : ℝ := ∑' m : ℕ, z ^ (m + 1) / ((m + 1) * (m + 2))

/-- The series `Q(z) = ∑_{j ≥ 0} z^{2j} / ((j+1)(2j+1))`. -/
def Qser (z : ℝ) : ℝ := ∑' j : ℕ, z ^ (2 * j) / ((j + 1) * (2 * j + 1))

/-- The termwise derivative of `Qser`. -/
def Qder (z : ℝ) : ℝ := ∑' m : ℕ, (2 * (m + 1)) * z ^ (2 * m + 1) / ((m + 2) * (2 * m + 3))

/-- The entropy-speed profile `A(u)`. -/
def Aser (u : ℝ) : ℝ :=
  Real.sqrt (∑' m : ℕ, (1 - (1 - u ^ 2) ^ (m + 1)) ^ 2 / ((m + 1) * (m + 2)))

/-! ### Certificate polynomials and Bernstein data -/

/-- The degree-5 profile polynomial `P`, in factored form. -/
def Ppoly (z : ℝ) : ℝ := (1 + (81 / 100) * (1 - z) ^ 2) * (1 + z - (81 / 100) * z ^ 2 * (1 - z))

/-- The degree-5 certificate polynomial `N = P - (1-z) P'`, by the explicit power basis of
`SKETCH.md` (4a). -/
def Npoly (z : ℝ) : ℝ :=
  81 / 50 + (24661 / 5000) * z - (43983 / 2500) * z ^ 2 + (27783 / 1250) * z ^ 3
    - (6561 / 500) * z ^ 4 + (19683 / 5000) * z ^ 5

/-- The degree-10 certificate polynomial `G = 64 P - 25 N²`. -/
def Gpoly (z : ℝ) : ℝ := 64 * Ppoly z - 25 * (Npoly z) ^ 2

/-- The Bernstein basis polynomial `C(m,k) xᵏ (1-x)^{m-k}` over `ℝ`. -/
def bern (m k : ℕ) (x : ℝ) : ℝ := (m.choose k : ℝ) * x ^ k * (1 - x) ^ (m - k)

/-- The symmetric `5 × 5` Bernstein coefficient matrix of `SKETCH.md` (3d); `0` outside
`[0,4]²`. -/
def cR : ℕ → ℕ → ℝ
  | 0, 0 => 5119741 / 1000000
  | 0, 1 => 24661 / 10000
  | 0, 2 => 14887 / 10000
  | 0, 3 => 1
  | 0, 4 => 1
  | 1, 0 => 24661 / 10000
  | 1, 1 => 9744659 / 8000000
  | 1, 2 => 36787 / 40000
  | 1, 3 => 319 / 400
  | 1, 4 => 1
  | 2, 0 => 14887 / 10000
  | 2, 1 => 36787 / 40000
  | 2, 2 => 3191251 / 4000000
  | 2, 3 => 31387 / 40000
  | 2, 4 => 1
  | 3, 0 => 1
  | 3, 1 => 319 / 400
  | 3, 2 => 31387 / 40000
  | 3, 3 => 319 / 400
  | 3, 4 => 1
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | _, _ => 0

/-- The determinant quotient `R(s,t)`, defined by its Bernstein expansion. -/
def Rpoly (s t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 5, ∑ l ∈ Finset.range 5, cR k l * bern 4 k s * bern 4 l t

/-- The degree-10 Bernstein coefficient vector `b` for `G(x/2)` (`SKETCH.md` 4b). -/
def bGl : ℕ → ℝ
  | 0 => 5023 / 100
  | 1 => 3086259 / 100000
  | 2 => 2740346279 / 180000000
  | 3 => 1487513279 / 240000000
  | 4 => 2530002779 / 840000000
  | 5 => 8124178271 / 2016000000
  | 6 => 10339753661 / 1344000000
  | 7 => 49104267221 / 3840000000
  | 8 => 53149568879 / 2880000000
  | 9 => 30879396079 / 1280000000
  | 10 => 30120271679 / 1024000000
  | _ => 0

/-- The degree-10 Bernstein coefficient vector `b'` for `G(1/2 + x/2)` (`SKETCH.md` 4b). -/
def bGr : ℕ → ℝ
  | 0 => 30120271679 / 1024000000
  | 1 => 88842566237 / 2560000000
  | 2 => 456352242227 / 11520000000
  | 3 => 168042175337 / 3840000000
  | 4 => 157752434729 / 3360000000
  | 5 => 282661663 / 5760000
  | 6 => 419806997 / 8400000
  | 7 => 1850591 / 37500
  | 8 => 837863 / 18000
  | 9 => 10077 / 250
  | 10 => 28
  | _ => 0

/-! ### The Step 7 / Step 8 scalar functions -/

/-- The diagonal slack `D(s)` of `SKETCH.md` Step 7, in natural-log units. -/
def Dfun (s : ℝ) : ℝ :=
  (9 / 10) * enat (s ^ 2) - Cval * enat s + (Real.log 2 / 10) * (gprof s) ^ 2

/-- The two-variable functional `Φ(s,t)` of `SKETCH.md` (8a), in natural-log units. -/
def Phi (s t : ℝ) : ℝ :=
  2 * ((9 / 10) * enat (s * t) + (Real.log 2 / 10) * (gprof s * gprof t))
    - Cval * (enat s + enat t)

/-! ### Finitary probability

A distribution is a nonnegative weight function on a `Fintype` summing to `1`; a random
variable is a function out of the index type; entropy is the entropy of the pushforward. -/

/-- Shannon entropy (natural log) of a finite weight vector. -/
def entropyW {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ := ∑ i, -(w i) * Real.log (w i)

/-- The pushforward law of a random variable `Z` under the weight vector `w`. -/
def law {ι β : Type*} [Fintype ι] [DecidableEq β] (w : ι → ℝ) (Z : ι → β) : β → ℝ :=
  fun b => ∑ i, if Z i = b then w i else 0

/-- The entropy of a finite random variable. -/
def Hrv {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β] (w : ι → ℝ) (Z : ι → β) : ℝ :=
  entropyW (law w Z)

/-- Conditional entropy, *defined* as the difference `H(Z, W) - H(W)`. -/
def condHrv {ι β γ : Type*} [Fintype ι] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] (w : ι → ℝ) (Z : ι → β) (W : ι → γ) : ℝ :=
  Hrv w (fun i => (Z i, W i)) - Hrv w W

/-- The uniform distribution on `G`, as a weight vector on the whole cube. -/
def unifW {n : ℕ} (G : Finset (Fin n → Bool)) : (Fin n → Bool) → ℝ :=
  fun x => if x ∈ G then 1 / (G.card : ℝ) else 0

/-- `p_i(v)`: the conditional probability that coordinate `i` is `false`, given that the
length-`i` prefix agrees with that of `v`.  Unsupported prefixes get the junk value `0`. -/
def pcond {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (v : Fin n → Bool) : ℝ :=
  let A := G.filter (fun x => pref i.val x = pref i.val v)
  let B := A.filter (fun x => x i = false)
  if A.card = 0 then 0 else (B.card : ℝ) / (A.card : ℝ)

/-- The prefix entropy `H_i = E H(S_i)`. -/
def HiFun {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) : ℝ :=
  ∑ x, unifW G x * Hnat (pcond G i x)

/-- The expectation `E S_i`. -/
def ESfun {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) : ℝ :=
  ∑ x, unifW G x * pcond G i x

/-- The expectation `E [S_i g(S_i)]`. -/
def Egfun {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) : ℝ :=
  ∑ x, unifW G x * (pcond G i x * gprof (pcond G i x))

/-- The weights of the independent coupling `(X', Y')` of `SKETCH.md` Step 10. -/
def windW {n : ℕ} (G : Finset (Fin n → Bool)) : ((Fin n → Bool) × (Fin n → Bool)) → ℝ :=
  fun p => unifW G p.1 * unifW G p.2

/-- The sign-modified zero-probability `s ± λ s (1-s)`, with `true ↦ +λ`, `false ↦ -λ`. -/
def pmod {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool) (v : Fin n → Bool) : ℝ :=
  pcond G i v + (if σ then (9 : ℝ) / 10 else -((9 : ℝ) / 10)) *
    (pcond G i v * (1 - pcond G i v))

/-- The modified transition kernel `π_i(v, b; σ)`. -/
def kern {n : ℕ} (G : Finset (Fin n → Bool)) (i : Fin n) (σ : Bool) (v : Fin n → Bool)
    (b : Bool) : ℝ :=
  if b = false then pmod G i σ v else 1 - pmod G i σ v

/-- The joint law of `(U, X̃, Ỹ)` for the shared-sign coupling of `SKETCH.md` (11a), given by
the explicit product formula, so that `X̃` and `Ỹ` are manifestly i.i.d. given the signs. -/
def wshW {n : ℕ} (G : Finset (Fin n → Bool)) :
    ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) → ℝ :=
  fun p => (1 / 2 : ℝ) ^ n * (∏ i, kern G i (p.1 i) p.2.1 (p.2.1 i)) *
    (∏ i, kern G i (p.1 i) p.2.2 (p.2.2 i))

end

end EntropyBound
