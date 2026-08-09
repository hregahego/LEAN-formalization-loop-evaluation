# Blueprint: Problem 30(c) — polynomial extension can raise the absorbing number

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
For each `q ≥ 2` we build an explicit finite-rank `𝔽₂[t]`-algebra `A_q = D·1 ⊕ De₁ ⊕
De₂ ⊕ De₃ ⊕ Du₁ ⊕ Du₂ ⊕ (D/t^q)s` (`D = 𝔽₂[t]`) whose augmentation ideal `J`
satisfies `J³ = 0`, and we compute the absorbing number of the zero ideal on both
sides of the polynomial extension: `ω_{A_q}(0) = q+1` but `ω_{A_q[X]}(0) = q+2`.
The single idea that makes it work is a **characteristic-2 cancellation
obstruction**: for constants `x, y ∈ J`, if `xy` has no `u₁`/`u₂`-part then its
`s`-part is forced to be divisible by `t` (a 64-case `𝔽₂` check); over `D[X]` the
residue field grows from `𝔽₂` to `𝔽₂[X]` and the obstruction disappears — witnessed
explicitly by `f = e₂ + Xe₃`, `g = (1+X)e₁ + (X+X²)e₂ + X²e₃` with
`fg = X(1+X)s`. One extra factor of `t` is therefore available in `A_q[X]`, and the
longest irredundant zero-product grows by exactly one.

- **Headline target (frozen theorem `polyAbsorbingConj_false`).** `¬ PolyAbsorbingConj`,
  where the frozen definition
  `PolyAbsorbingConj : Prop := ∀ (R : Type) [CommRing R] (I : Ideal R), omegaAbs (polyExt I) = omegaAbs I`
  is the literal statement of Problem 30(c) (`ω_{R[X]}(I[X]) = ω_R(I)`), with
  `omegaAbs` the frozen absorbing number `ω` and `polyExt I` the frozen model of
  `I[X]`. The headline is witnessed by the concrete family: the companion frozen
  theorem `gap_family` states that for every `n ≥ 3` the explicit ring `A (n-1)` is
  Noetherian with `omegaAbs ⊥ = n` and `omegaAbs (polyExt ⊥) = n + 1`, and the two
  half-statements `omegaAbs_A` (`ω_{A_q}(0) = q+1`) and `omegaAbs_polyExt_A`
  (`ω_{A_q[X]}(0) = q+2`) are frozen on their own. `polyAbsorbingConj_false` alone is
  *weaker* than the sketch's claim (it does not record Noetherianity or the exact
  values), which is exactly why the companions are frozen too — see the cheat watch
  in Stage G.
- **Recommended intermediate milestone (prove first):** `s_component_cancellation`
  (Step 2) together with `not_isNAbsorbing_A_q` and `fPoly_mul_gPoly`
  (Steps 3-lower and 4). These are the mathematical heart: the char-2 obstruction and
  the explicit polynomial pair that defeats it. They are small, self-contained, and
  once they are `✅` the whole construction is known to be the intended one; the rest
  is a (long) valuation/divisibility bookkeeping argument.
- **Setting / ground assumptions:** everything is commutative algebra over
  `D = Polynomial (ZMod 2)`; no analysis, no inequalities beyond `ℕ`-arithmetic, no
  cardinality theory. Two ambient base rings occur: `D` and `D[X]`, both **domains**
  in which `t` is **prime**; that is the only property of the base the upper-bound
  argument uses. The construction is *not* presented by generators and relations —
  it is an explicit direct sum, so nothing has to be proved "non-collapsing". The
  quantifier `∀ q ≥ 2` is genuine: no theorem may be proved for a single `q`.

> **Why this is tractable.** The ring is a *unitalization* `A = B ⋉ J` of a
> square-nilpotent-ish `B`-module `J` (`J·J ⊆ W`, `W·J = 0`), so Mathlib's
> `Unitization` supplies every ring axiom for free and the multiplication is a single
> symmetric bilinear formula on six coordinates. The char-2 lemma is a 64-case
> `decide` over `ZMod 2`. The absorbing upper bound, which reads like a valuation
> argument in the sketch, can be rewritten to use **only prime divisibility** (`τ ∣ dᵢ`
> for every non-`J` factor, then `τ^{m-2} ∣ …`), so no `multiplicity` API is needed.
> The real risks are (a) **mis-modeling** — writing the multiplication table wrong, or
> letting `Dq = D/t^q` degenerate, so that the "counterexample" is a ring where
> everything is zero; (b) **weakening** — proving the `q+1`-absorbing statement only
> for `q = 2`, or proving `ω_{A[X]}(0) ≥ q+2` and calling it `= q+2`; and (c) the one
> genuinely hard piece of engineering, the transfer isomorphism
> `A_q[X] ≅ A(D[X], t, q)` that makes Step 6 rigorous (the sketch merely says
> "repeating the valuation argument"). Deep mathematics is *not* the risk here.

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is to produce a compiling skeleton in which **every
`Definition` and every `Theorem` statement is written and frozen**, with all
proofs `:= sorry`. Once frozen, `Defs.lean` and `Theorems.lean` are **never
edited again** during the proving phase. Everything proved later lives in
support files and may not change a single character of the frozen statements.

### 1. Create the Lean project

```bash
cd /Users/siyua/dev/opensource-validation-runs/Prob30c-refactors
lake +leanprover/lean4:v4.32.0 new Prob30c math
# pin Mathlib in lakefile + lake-manifest to the matching rev, i.e.
#   require "leanprover-community" / "mathlib" @ git "v4.32.0"
# and make sure Prob30c/lean-toolchain reads  leanprover/lean4:v4.32.0
lake exe cache get
lake build            # must succeed on the bare skeleton before anything else
```

(`v4.32.0` and its matching Mathlib tag are available locally; if `lake exe cache
get` cannot fetch a cache for that pair, drop to the newest toolchain/Mathlib tag
that *does* have a cache, and record the choice as a `📝` entry in `PROGRESS.md`.
Never proceed without a working `lake exe cache get` — building Mathlib from
source is not an option here.)

Layout (every project follows this shape):

```
Prob30c-refactors/
  Prob30c/
    Defs.lean          -- FROZEN after this stage: every object the proof needs
    Theorems.lean      -- FROZEN after this stage: the 15 frozen statements (sorry)
    Proofs/
      Absorbing/       -- Stage A: the ω / n-absorbing API, I[X] faithfulness
      Model/           -- Stage B: the ring A_q, its multiplication table, J³ = 0
      Cancellation/    -- Stage C: the characteristic-2 s-component obstruction
      Witnesses/       -- Stage D: t^q·s, f·g = X(1+X)s, the two lower bounds
      Bound/           -- Stage E: the generic irredundant-length upper bound
      Transfer/        -- Stage F: A_q[X] ≅ A(D[X], t, q), the q+2 upper bound
      Headline/        -- Stage G: ω values, gap_family, refutation of the conjecture
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `Prob30c.Solution`, proven (clean names)
  Prob30c.lean         -- imports everything
  SKETCH.md            -- the problem + NL proof sketch (math source of truth)
  BLUEPRINT.md         -- this file
  USER_NOTES.md        -- user's special instructions / permitted assumed-axioms
  PROGRESS.md          -- append-only work log (workers write here; see §4)
  TASKS.md             -- append-only delegation log (the Plan agent writes here; see §5)
  REVIEW.md            -- append-only audit log (the Review agent writes here; see §5)
  scripts/
    verify.py          -- the verification harness
    harness.json       -- project / problem / frozen-theorem names
    frozen.sha256      -- SHA-256 pins of Defs.lean + Theorems.lean
    ALLOWED_AXIOMS.txt -- axiom allowlist init.py derives from USER_NOTES.md
```

All support declarations live in `namespace Prob30c` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface;
`Solution.lean` re-exposes each as `Prob30c.Solution.<name>` after it is proven,
and `Discharge.lean` machine-checks that each proof has *exactly* the frozen type
(`@Frozen = @Proof := rfl`).

`USER_NOTES.md` for this problem says **"None — no assumed axioms."** So the
strict default applies: `scripts/ALLOWED_AXIOMS.txt` stays empty, no `axiom`
declaration may appear anywhere in the project, and every solved theorem must
`#print axioms` to exactly `{propext, Classical.choice, Quot.sound}` (or fewer).

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.** For each
definition record the Lean rendering and the **MODELING DECISION**.

```lean
import Mathlib

namespace Prob30c

open Polynomial Finset
```

**D1 — `IsNAbsorbing`.**

```lean
/-- `I` is `n`-absorbing: whenever a product of `n+1` elements lies in `I`,
    already `n` of the factors have their product in `I`. -/
def IsNAbsorbing {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) : Prop :=
  ∀ a : Fin (n + 1) → R, (∏ i, a i) ∈ I →
    ∃ S : Finset (Fin (n + 1)), S.card = n ∧ (∏ i ∈ S, a i) ∈ I
```

> **MODELING DECISION.** This is the *literal* Anderson–Badawi definition quoted in
> `SKETCH.md`: an indexed family of `n+1` factors (repetitions allowed, since `a` is
> a function, not a set) and a sub-family of exactly `n` of the *positions*. Rejected
> alternatives: (i) `∃ j, ∏ i ∈ univ.erase j, a i ∈ I` — equivalent (a `Finset` of
> `Fin (n+1)` with card `n` *is* an `erase`), but it reads as a different definition,
> so it is demoted to a support lemma `absorbing_iff_exists_drop` in Stage A;
> (ii) quantifying over `Multiset R` of card `n+1` — same content, worse API;
> (iii) requiring the `aᵢ` to be *distinct* — that would be a genuinely different
> (weaker) notion and is FORBIDDEN. Note `IsNAbsorbing I 0` holds iff `1 ∈ I`, which
> is why `omegaAbs` restricts to positive `n`.

**D2 — `omegaAbs` (the absorbing number `ω_R(I)`).**

```lean
/-- `ω_R(I)`: the least positive `n` for which `I` is `n`-absorbing (`0` if none). -/
noncomputable def omegaAbs {R : Type*} [CommRing R] (I : Ideal R) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ IsNAbsorbing I n}
```

> **MODELING DECISION.** `Nat.sInf` of the set of admissible `n`, matching "least
> positive integer `n`". `sInf ∅ = 0`, so `omegaAbs I = 0` encodes "`I` is not
> `n`-absorbing for any `n`" — a sentinel value that can never be confused with a
> real answer because every value we prove is `≥ 3`. Rejected: `Nat.find`
> (needs a `Decidable` instance we do not have) and `⊤ : ℕ∞` (would force `ℕ∞`
> arithmetic through every statement). `noncomputable` is unavoidable and harmless:
> no `decide` is ever run on `omegaAbs`.

**D3 — `polyExt` (the ideal `I[X]`).**

```lean
/-- `I[X] ⊆ R[X]`, modelled as the ideal generated by the constants from `I`. -/
def polyExt {R : Type*} [CommRing R] (I : Ideal R) : Ideal (Polynomial R) :=
  I.map (Polynomial.C : R →+* Polynomial R)
```

> **MODELING DECISION.** `Ideal.map C` is the Mathlib-idiomatic `I[X]`. It is
> *equal* to `{p | ∀ n, p.coeff n ∈ I}` — the textbook description — and the frozen
> theorem `mem_polyExt_iff` (Stage A, via `Polynomial.mem_map_C_iff`) is exactly the
> guardrail that certifies this. Rejected: defining `polyExt` by the coefficient
> condition and then proving it is an ideal (more work, same object); and
> `Ideal.comap`-based tricks (wrong direction).

**D4 — `PolyAbsorbingConj` (Problem 30(c) itself).**

```lean
/-- Anderson–Badawi Conjecture C2 / Problem 30(c): `ω_{R[X]}(I[X]) = ω_R(I)`. -/
def PolyAbsorbingConj : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), omegaAbs (polyExt I) = omegaAbs I
```

> **MODELING DECISION.** Quantified over *all* commutative rings in `Type` and *all*
> ideals, exactly as the problem states it — no Noetherian hypothesis, no restriction
> to `I = 0`. Universe `Type` (not `Type*`) keeps the statement a single `Prop` and
> is harmless: the counterexample `A q` lives in `Type`. Deliberately *not* stated as
> an `∃`-refutation, so that the headline is the negation of the conjecture verbatim.

**D5 — the base ring `D = 𝔽₂[t]`.**

```lean
abbrev F2 : Type := ZMod 2
abbrev Dbase : Type := Polynomial F2
/-- The variable `t` of `D = 𝔽₂[t]` (kept separate from the `X` of `A_q[X]`). -/
abbrev tD : Dbase := Polynomial.X
```

> **MODELING DECISION.** `abbrev`s, so all Mathlib instances (`CommRing`,
> `IsDomain`, `EuclideanDomain`, `UniqueFactorizationMonoid`, `CharP _ 2`) apply with
> no transport. `tD` is an alias for `Polynomial.X` purely to keep the two variables
> `t ∈ D` and `X ∈ A_q[X]` visually distinct — they are *different* variables and
> conflating them is the single easiest way to write a wrong statement.

**D6 — the torsion coefficient ring `B/τ^q`.**

```lean
/-- `B ⧸ (τ^q)`; for `B = D`, `τ = t` this is the `D/t^qD` of the sketch. -/
abbrev Quo (B : Type) [CommRing B] (τ : B) (q : ℕ) : Type :=
  B ⧸ Ideal.span {τ ^ q}
```

**D7 — the augmentation module `Jmod` with its multiplication.**

```lean
/-- Coordinates `(a₁, a₂, a₃, c₁, c₂, σ)` of `a₁e₁ + a₂e₂ + a₃e₃ + c₁u₁ + c₂u₂ + σs`. -/
def Jmod (B : Type) [CommRing B] (τ : B) (q : ℕ) : Type :=
  B × B × B × B × B × Quo B τ q

instance (B) [CommRing B] (τ : B) (q : ℕ) : AddCommGroup (Jmod B τ q) :=
  inferInstanceAs (AddCommGroup (B × B × B × B × B × Quo B τ q))
instance (B) [CommRing B] (τ : B) (q : ℕ) : Module B (Jmod B τ q) :=
  inferInstanceAs (Module B (B × B × B × B × B × Quo B τ q))

/-- The multiplication table `e₁e₃ = u₂+s`, `e₂² = u₂`, `e₂e₃ = e₃² = u₁`,
    all other `eᵢeⱼ = 0`, and `u₁, u₂, s` annihilate `J`. -/
instance (B) [CommRing B] (τ : B) (q : ℕ) : Mul (Jmod B τ q) :=
  ⟨fun x y =>
    (0, 0, 0,
     x.2.1 * y.2.2.1 + x.2.2.1 * y.2.1 + x.2.2.1 * y.2.2.1,   -- u₁ : a₂b₃ + a₃b₂ + a₃b₃
     x.1 * y.2.2.1 + x.2.2.1 * y.1 + x.2.1 * y.2.1,           -- u₂ : a₁b₃ + a₃b₁ + a₂b₂
     Ideal.Quotient.mk _ (x.1 * y.2.2.1 + x.2.2.1 * y.1))⟩    -- s  : a₁b₃ + a₃b₁

instance (B) [CommRing B] (τ : B) (q : ℕ) : NonUnitalCommRing (Jmod B τ q) := by
  sorry -- SETUP: fill in; all fields are `Prod.ext` + `ring`, associativity is `0 = 0`
instance (B) [CommRing B] (τ : B) (q : ℕ) : IsScalarTower B (Jmod B τ q) (Jmod B τ q) := sorry
instance (B) [CommRing B] (τ : B) (q : ℕ) : SMulCommClass B (Jmod B τ q) (Jmod B τ q) := sorry
```

> **MODELING DECISION.** (i) `Jmod` is a **`def` on a nested `Prod`**, not a
> `structure`: the nested product hands us `AddCommGroup` and `Module B` by
> `inferInstanceAs`, while being a `def` (not `abbrev`) lets us install *our* `Mul`
> instead of `Prod`'s componentwise one. Cost: coordinates are `x.2.2.1`-style;
> readability is recovered by support projections `a₁ a₂ a₃ c₁ c₂ σ` and a
> `Jmod.ext` lemma defined in `Proofs/Model/`. Rejected: a named `structure`
> (readable, but every algebraic instance must be hand-written or transported).
> (ii) The three `eᵢeⱼ` bilinear forms are recorded **once**, here, and are the sole
> source of truth for the multiplication table; they are *symmetric*, which is what
> makes `mul_comm` true, and they are characteristic-independent (char 2 is used only
> in Stage C/D, never in the table). (iii) The output has zero `e`-coordinates and the
> inputs' `c₁, c₂, σ` never occur on the right-hand side — that *is* the encoding of
> "`J² = W`" and "`W·J = 0`", hence of `J³ = 0`; associativity is therefore literally
> `0 = 0`. (iv) The construction is parametric in `(B, τ)` **on purpose**: Stage F
> instantiates it at `B = D[X]`, `τ = C t`, which is what makes Step 6 provable
> without re-running the whole argument.

**D8 — the ring `A(B, τ, q)` and the counterexample `A q`.**

```lean
/-- `B ⋉ Jmod B τ q`: the sketch's `A_q` over a general base. -/
abbrev Alg (B : Type) [CommRing B] (τ : B) (q : ℕ) : Type := Unitization B (Jmod B τ q)

/-- The counterexample ring `A_q = D1 ⊕ De₁ ⊕ De₂ ⊕ De₃ ⊕ Du₁ ⊕ Du₂ ⊕ (D/t^q)s`. -/
abbrev A (q : ℕ) : Type := Alg Dbase tD q
```

> **MODELING DECISION.** `Unitization B M` (Mathlib) gives `CommRing (Alg B τ q)`
> from `NonUnitalCommRing (Jmod …) + Module + IsScalarTower + SMulCommClass` — every
> ring axiom, including associativity and distributivity, comes from Mathlib and is
> **never `sorry`ed**. Rejected: (i) a hand-rolled 7-component `structure` with a
> hand-proved `CommRing` instance (hundreds of lines of `ring`, and easy to get
> subtly wrong); (ii) presenting `A_q` as `D[E₁,E₂,E₃,U₁,U₂,S]/(relations)` — this
> looks closest to the sketch's prose but would require proving that the quotient does
> *not* collapse (a normal-form / Gröbner argument), which is strictly harder than the
> mathematics we are trying to formalize. `Alg`/`A` are `abbrev`s so `Unitization`'s
> instances (`CommRing`, `Algebra B`, `Module B`) flow through untouched.

**D9 — the generators.**

```lean
namespace Alg
variable (B : Type) [CommRing B] (τ : B) (q : ℕ)

def e₁ : Alg B τ q := Unitization.inr (1, 0, 0, 0, 0, 0)
def e₂ : Alg B τ q := Unitization.inr (0, 1, 0, 0, 0, 0)
def e₃ : Alg B τ q := Unitization.inr (0, 0, 1, 0, 0, 0)
def u₁ : Alg B τ q := Unitization.inr (0, 0, 0, 1, 0, 0)
def u₂ : Alg B τ q := Unitization.inr (0, 0, 0, 0, 1, 0)
def sElt : Alg B τ q := Unitization.inr (0, 0, 0, 0, 0, Ideal.Quotient.mk _ 1)
def tElt : Alg B τ q := algebraMap B (Alg B τ q) τ
end Alg

abbrev e₁ (q : ℕ) : A q := Alg.e₁ Dbase tD q
abbrev e₂ (q : ℕ) : A q := Alg.e₂ Dbase tD q
abbrev e₃ (q : ℕ) : A q := Alg.e₃ Dbase tD q
abbrev u₁ (q : ℕ) : A q := Alg.u₁ Dbase tD q
abbrev u₂ (q : ℕ) : A q := Alg.u₂ Dbase tD q
abbrev sElt (q : ℕ) : A q := Alg.sElt Dbase tD q
abbrev tElt (q : ℕ) : A q := Alg.tElt Dbase tD q
```

> **MODELING DECISION.** Generators are defined at the *generic* base and aliased at
> `D`, so the multiplication-table lemmas of Stage B are proved once and reused by
> Stage F. `tElt` is the image of the scalar `t` under `algebraMap`, i.e. `t·1`, and is
> a **non-zero-divisor on the free part** — never confuse it with `Polynomial.X` of
> `A q[X]`.

**D10 — the ideals `J` and `W`.**

```lean
/-- `J`: the augmentation ideal, i.e. the kernel of `A → B`. -/
def Jid (B : Type) [CommRing B] (τ : B) (q : ℕ) : Ideal (Alg B τ q) :=
  RingHom.ker (Unitization.fstHom B (Jmod B τ q) : Alg B τ q →+* B)

/-- `W = Du₁ + Du₂ + (D/t^q)s`. -/
def Wid (B : Type) [CommRing B] (τ : B) (q : ℕ) : Ideal (Alg B τ q) :=
  Ideal.span {Alg.u₁ B τ q, Alg.u₂ B τ q, Alg.sElt B τ q}
```

> **MODELING DECISION.** `J = ker(fst)` is exactly "`A_q` minus its `D·1` summand",
> which is the sketch's `J`; a support lemma `mem_Jid_iff : x ∈ Jid … ↔ x.fst = 0`
> makes this usable. Rejected: `Ideal.span {e₁,e₂,e₃,u₁,u₂,s}` — the same ideal, but
> membership would then need a spanning argument on every use. `W` *is* taken as a
> span, because Stage B proves `Jid² = Wid` and spans are the convenient side of that
> equation; note `Ideal.span {sElt} = (D/t^q)·s` because `J` annihilates `s`, and
> `Ideal.span {tElt * sElt} = t·(D/t^q)·s` likewise — this is what makes the frozen
> Step-2 statement faithful.

**D11 — the two polynomials of Step 4.**

```lean
/-- `f = e₂ + X e₃ ∈ A_q[X]`. -/
def fPoly (q : ℕ) : Polynomial (A q) := C (e₂ q) + C (e₃ q) * X
/-- `g = (1+X)e₁ + (X+X²)e₂ + X² e₃ ∈ A_q[X]`. -/
def gPoly (q : ℕ) : Polynomial (A q) :=
  C (e₁ q) * (1 + X) + C (e₂ q) * (X + X ^ 2) + C (e₃ q) * X ^ 2
```

> **MODELING DECISION.** Written with `C`/`X` in `Polynomial (A q)` exactly as the
> sketch writes them, coefficients on the left. `X` here is `Polynomial.X` **of
> `A q[X]`**; the base variable is `tD`. Do not "simplify" `1 + X` to `X + 1` etc. in
> the frozen file — the frozen text must mirror Step 4 literally.

A definition once frozen is binding: later stages may *characterize* it with
support lemmas but may never redefine or silently swap it.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook notion**,
> quantified exactly as the source states it. Concretely, for this problem:
> `IsNAbsorbing` must quantify over **all** families `Fin (n+1) → R` (not over
> distinct elements, not over a finite list of examples); `omegaAbs` must be the
> **least** admissible `n` (not "some `n` that works"); `polyExt` must be `I[X]`
> and this must be *proved* (`mem_polyExt_iff`), not asserted; `PolyAbsorbingConj`
> must range over all rings and all ideals. The multiplication table in `Jmod` must
> contain **all** of `e₁e₃ = u₂+s`, `e₂² = u₂`, `e₂e₃ = u₁`, `e₃² = u₁` and **none**
> of the products the sketch sets to `0`: dropping the `+ s` in `e₁e₃`, or the
> `a₂b₂` in the `u₂` slot, silently destroys the counterexample. `Quo B τ q` with
> `q = 0` is the zero ring — that is why every quantitative theorem carries the
> sketch's own hypothesis `2 ≤ q` and no theorem may be stated for a fixed `q`.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each statement must render a claim of
`SKETCH.md` **faithfully and minimally**, must have a **stable, binding name**
(referenced by `verify.py`, `Discharge.lean`, `Solution.lean`, `init.py`), and the
list must include the headline claim.

```lean
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
```

Map to `SKETCH.md`:

| frozen name | sketch step |
| ----------- | ----------- |
| `mem_polyExt_iff` | Problem Statement (`I[X]`) |
| `isNAbsorbing_succ` | Problem Statement (`ω` = least `n`, monotone family) |
| `Jid_pow_three_eq_bot`, `Jid_sq_eq_Wid`, `isNoetherianRing_A` | Step 1 |
| `s_component_cancellation` | Step 2 |
| `not_isNAbsorbing_A_q` | Step 3, lower bound |
| `isNAbsorbing_A_succ_q` | Step 3, upper bound (Cases 1–3) |
| `omegaAbs_A` | Step 3, boxed conclusion |
| `fPoly_mul_gPoly` | Step 4 |
| `not_isNAbsorbing_polyExt_A_succ_q` | Step 5 |
| `isNAbsorbing_polyExt_A_succ_succ_q` | Step 6 |
| `omegaAbs_polyExt_A` | Step 6, boxed conclusion |
| `gap_family` | Claimed Resolution + Conclusion box |
| `polyAbsorbingConj_false` | Conclusion (negative solution to Problem 30(c)) |

**Why these 15.** The *decidable heart* is `s_component_cancellation` (a 64-case
`ZMod 2` check after reducing to constant coefficients) and `fPoly_mul_gPoly` (a
finite computation in the multiplication table) — together they are the entire
mathematical content of "the obstruction exists over `𝔽₂` and dies over `𝔽₂[X]`".
The *support* statements are `mem_polyExt_iff` and `isNAbsorbing_succ` (they make
`ω` and `I[X]` mean what the problem says they mean — without them the headline
could be true for a silly reason), plus the three Step-1 structural facts. The
*hard engineering* is `isNAbsorbing_A_succ_q` and `isNAbsorbing_polyExt_A_succ_succ_q`
(the case analysis and the transfer isomorphism). The *payoff* is
`polyAbsorbingConj_false`, propped up by `gap_family` so that the refutation is
recorded at full strength (explicit, Noetherian, exact values, all `n ≥ 3`).

**Re-build gate.** After freezing, `lake build` must succeed (everything is
`sorry`, but the *statements* must typecheck; the `NonUnitalCommRing (Jmod …)`
instance in `Defs.lean` must be **genuinely proved during SETUP**, not left
`sorry` — see the cheat watch, a `sorry` outside `Theorems.lean` fails
`verify.py` check 2 anyway). Do not write a line of proof until the skeleton
compiles. Record the SHA-256 of `Defs.lean` and `Theorems.lean` into
`scripts/frozen.sha256`, then log a PROGRESS entry: "SETUP frozen, skeleton
builds, pins recorded."

### 4. Progress logging (`PROGRESS.md`, append-only — MANDATORY)

There is a single shared log at the repo root, **`PROGRESS.md`**. It is the
project's memory: it is read by an auditor (see below) and by freshly launched
agents that have **no prior context** and must figure out, from the log alone,
what is done, what is in progress, and where they should start. Treat it as the
first thing you read and the last thing you write.

**Inviolable rules (read before doing anything):**

- **APPEND ONLY. NEVER delete, edit, overwrite, reword, or "tidy up" any
  existing entry — not your own, not anyone else's, not ever.** The log is an
  immutable history. If something you wrote earlier turns out to be wrong, do
  **not** remove it: append a *new* entry that corrects it (`📝 decision`,
  noting "supersedes the entry at <timestamp>"). Deleting or rewriting history
  is itself treated as a cheating signal in the audit.
- **Every entry is timestamped and stage-annotated.** Get the real UTC time with
  `date -u +"%Y-%m-%dT%H:%M:%SZ"` — do not invent or approximate timestamps.
- **One entry per event, newest appended at the bottom**, in this exact format.
  Write every line flush left, exactly as shown. The `Agent:` label must contain
  `agent-iter<N>` so the entry can be attributed to its iteration, and lemma or
  definition names on the `Next:` line must be wrapped in `backticks` — the
  recurring-crux stall guard counts backticked identifiers:

```
## <UTC timestamp> — <stage/item, e.g. "Stage C · <lemma name>">
Agent: agent-iter<N>-<k>
Status: ✅ proved | ⚠️ blocked | 🔧 in progress | 📝 decision
Check: <#print axioms result, lake build result, or n/a>
Note: <one or two lines — what you did, key lemma used, or exactly what blocks you>
Next: <for a ✅/⚠️ entry: what work this unblocks or what a follow-up agent should do next, with exact lemma/file names to build on; "n/a" only if truly terminal>
```

- **The `Next:` line is mandatory on every `✅` and `⚠️` entry.** Point the next
  agent at the related work: which stage is now unblocked, the exact names of the
  lemmas/defs you produced that they will consume, and any gotcha you hit. A fresh
  agent with no context should be able to read the latest entries and know exactly
  where to start — this is what makes sessions resumable.

- **Log at least when you:** (a) start work on a stage (`🔧 in progress`, so two
  agents don't collide on the same lemma), (b) finish/close a lemma or stage
  (`✅`, with the `#print axioms` output as `Check:`), (c) hit a blocker (`⚠️` —
  write the *exact* failing goal/error, then move to the next independent
  target rather than thrashing), or (d) make a non-obvious modeling or proof
  decision (`📝`). Append a prominent entry at each milestone.
- **Never fake a `✅`.** Only mark proved what compiles with a clean
  `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`; no
  `sorryAx`, no `native_decide`/`Lean.ofReduceBool`). A `✅` that does not match
  the actual build state is the most serious audit failure.
- **Do not stop to ask for confirmation between stages — work straight through**,
  logging as you go.

**Why this matters (do not skip):** `PROGRESS.md` is the input to a
**faithfulness / cheating audit conducted by the orchestrator, not by you.** The
auditor cross-checks every `✅` entry against the actual Lean source and axiom
output, and checks that no frozen file or earlier log entry was tampered with.
An accurate, complete, append-only log protects your work from being thrown out;
a log with gaps, edited history, or unsupported `✅`s causes the whole stage to
be re-audited or discarded.

### 5. The iteration loop & agent-onboarding protocol

After SETUP, the project is driven by an **orchestrator** that runs repeated
iterations. Each iteration has three phases, executed by short-lived agents that
share **no memory** beyond the files on disk — they coordinate entirely through
`TASKS.md`, `PROGRESS.md`, and `REVIEW.md` (all append-only):

1. **PLAN** — one agent reads `REVIEW.md` (the auditor's prior findings — its
   "Required follow-ups" are top priority), `PROGRESS.md` (what is `✅`/`🔧`/`⚠️`/
   `📝`), `SKETCH.md`, and `BLUEPRINT.md`. It chooses the most valuable batch of
   work that respects the dependency graph, splits it across **up to 4 parallel
   workers with NON-OVERLAPPING files**, and **appends a `## Iteration N` block to
   `TASKS.md`** with one `Agent k:` line per active worker (inactive workers
   omitted). It writes no proofs.
2. **WORKERS** — up to 4 agents run **in parallel**, one per `Agent k:` line.
   Each owns only the files its line assigns (this is what makes parallelism
   collision-free).
3. **REVIEW** — one independent, adversarial auditor re-runs the build, `#print
   axioms`, and `scripts/verify.py`, checks faithfulness against `SKETCH.md`/
   `BLUEPRINT.md`, and **appends a `## Review — Iteration N` block to `REVIEW.md`**
   ending in `Verdict: COMPLETE | INCOMPLETE`. Every 5th iteration is a full-
   project audit. The loop ends when a verdict is `COMPLETE` and a final full
   audit confirms it.

**Worker onboarding ritual — do this BEFORE writing any code:**

1. **Read `TASKS.md`**, find `## Iteration N`, then your own `Agent k:` line.
   *That line is your assignment* — the files you own and the lemmas to produce.
   Ignore the other agents' lines (they are running right now in parallel).
2. **Read `PROGRESS.md` end to end.** Respect every `✅` (done — reuse, don't
   redo), `🔧` (another agent holds it — do not touch), `⚠️` (blocked), and `📝`
   (a fixed modeling/proof decision you must follow).
3. **Read the `BLUEPRINT.md` stage(s) your task names — including the Cheat-watch
   box — and the cited `SKETCH.md` step(s).** Do not work from the stage title
   alone; the cheat-watch boxes are binding.
4. **Append a `🔧 in progress` entry** to `PROGRESS.md` claiming your work, then
   work only on your assigned files, then append `✅`/`⚠️` as you go.

**Dependency discipline.** Respect the order graph in "Suggested formalization
order"; the Plan agent must never assign work whose prerequisites are not yet
`✅`. Workers must **never edit the frozen `Defs.lean`/`Theorems.lean`** and must
**never weaken a frozen statement** (see the cardinal cheat rule below) — if a
task seems to need that, append a `⚠️` entry describing the obstacle and stop,
rather than touching a frozen file.

---

## Part 0 — What Mathlib already gives you (reuse, do not rebuild)

| Need                                            | Mathlib handle                                                                   |
| ----------------------------------------------- | -------------------------------------------------------------------------------- |
| the field `𝔽₂`                                  | `ZMod 2` (`Field`, `DecidableEq`, `Fintype`, `CharP (ZMod 2) 2`)                  |
| `D = 𝔽₂[t]`, domain, UFD, `t` prime             | `Polynomial (ZMod 2)`, `Polynomial.X`, `Polynomial.prime_X`                       |
| `t ∣ p ↔ p(0) = 0`                              | `Polynomial.X_dvd_iff`, `Polynomial.coeff_zero_eq_eval_zero`, `Polynomial.mul_coeff_zero` |
| `D/t^qD`                                        | `B ⧸ Ideal.span {τ^q}`, `Ideal.Quotient.mk`, `Ideal.Quotient.eq_zero_iff_mem`     |
| `t^k ∈ (t^q)` ⟺ `t^q ∣ t^k`                     | `Ideal.mem_span_singleton`, `pow_dvd_pow_iff`                                     |
| unitalization `B ⋉ J`, all ring axioms          | `Unitization B M`: `inl`, `inr`, `fst`, `snd`, `fstHom`, `instCommRing`, `instAlgebra`, `Unitization.ext` |
| the augmentation ideal                          | `RingHom.ker (Unitization.fstHom …)`                                              |
| `I[X]` and its coefficient description          | `Ideal.map C`, **`Polynomial.mem_map_C_iff`**, `Ideal.map_bot`, `Ideal.mem_bot`   |
| polynomial arithmetic in `A_q[X]`               | `Polynomial.C_mul`, `Polynomial.coeff_mul`, `Polynomial.ext_iff`, `Polynomial.coeff_C_mul` |
| `(B/I)[X] ≅ B[X]/I[X]`                          | `Ideal.polynomialQuotientEquivQuotientPolynomial` (Stage F)                       |
| `C τ` prime in `B[X]`                           | `Polynomial.prime_C_iff` (needs `B` a UFD)                                        |
| prime divisibility bookkeeping                  | `Prime.dvd_of_dvd_pow`, `Prime.pow_dvd_of_dvd_mul_left/right`, `dvd_mul_of_dvd_left`, `pow_dvd_pow` |
| Noetherian transfer                             | `Polynomial.isNoetherianRing` (Hilbert basis), `Module.Finite`, `isNoetherian_of_tower`, `isNoetherianRing_iff` |
| `ω` as a least element of a set of `ℕ`          | `Nat.sInf_mem`, `Nat.sInf_le`, `Nat.not_mem_of_lt_sInf`, `le_antisymm`            |
| finite products over `Fin n` / `Finset`         | `Finset.prod_erase_mul`, `Finset.mul_prod_erase`, `Finset.prod_congr`, `Fin.prod_univ_succ` |
| transport a statement along a ring iso          | `RingEquiv`, `RingEquiv.map_eq_zero_iff`, `map_prod`                              |

**The two nontrivial dependencies the whole proof hinges on** are
`Unitization` (it supplies the entire `CommRing` structure of `A_q`, so no ring
axiom is ever hand-proved) and `Polynomial.mem_map_C_iff` (it certifies that
`polyExt` really is `I[X]`). Stage F adds a third,
`Ideal.polynomialQuotientEquivQuotientPolynomial`.

**Machinery you can avoid.** (i) The sketch phrases Step 3/6 with the `t`-adic
*valuation* `v = v_t(a)`; you do **not** need `multiplicity`/`emultiplicity`/
`Valuation`. Every use can be rewritten as prime divisibility: irredundancy forces
`τ ∣ dᵢ` for each factor outside `J`, hence `τ^{m-2} ∣ (∏_{j≠i₀} dⱼ)·a`, and
`τ^q ∤ (∏_{j≠i₀} dⱼ)·a` then bounds `m` directly. (ii) You do not need Gröbner
bases, normal forms, or any "the presentation does not collapse" argument, because
`A_q` is built as an explicit direct sum rather than as a quotient. (iii) You do not
need tensor products for `A_q[X]`: Stage F builds one explicit `RingEquiv`.

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #   | Object                            | Role                                                                     |
| --- | --------------------------------- | ------------------------------------------------------------------------ |
| D1  | `IsNAbsorbing I n : Prop`         | the Anderson–Badawi `n`-absorbing predicate, literal rendering            |
| D2  | `omegaAbs I : ℕ`                  | `ω_R(I)`, the least positive `n` with `I` `n`-absorbing                   |
| D3  | `polyExt I : Ideal R[X]`          | the ideal `I[X]`, as `I.map C`                                            |
| D4  | `PolyAbsorbingConj : Prop`        | Problem 30(c) itself; the headline negates this                           |
| D5  | `F2`, `Dbase`, `tD`               | `𝔽₂`, `D = 𝔽₂[t]`, the variable `t`                                       |
| D6  | `Quo B τ q`                       | `B ⧸ (τ^q)`; the torsion coefficient ring of the `s`-summand             |
| D7  | `Jmod B τ q` + `Mul`/ring instances | the augmentation module with the sketch's multiplication table          |
| D8  | `Alg B τ q`, `A q`                | `B ⋉ Jmod B τ q` and the counterexample `A_q` (`B = D`, `τ = t`)          |
| D9  | `e₁ e₂ e₃ u₁ u₂ sElt tElt`        | the generators, generic and specialised to `D`                           |
| D10 | `Jid B τ q`, `Wid B τ q`          | `J = ker(A → B)` and `W = Du₁ + Du₂ + (D/t^q)s`                          |
| D11 | `fPoly q`, `gPoly q`              | `f = e₂ + Xe₃` and `g = (1+X)e₁ + (X+X²)e₂ + X²e₃` in `A_q[X]`            |

---

## Part 2 — Theorems and lemmas to prove (in order)

### Stage A — the absorbing-number API (`Proofs/Absorbing/`)

Goal: make `IsNAbsorbing`, `omegaAbs` and `polyExt` usable, and deliver the frozen
theorems `mem_polyExt_iff` and `isNAbsorbing_succ`. Base-ring-independent; can start
immediately and in parallel with everything else.

**A1 — `absorbing_iff_exists_drop`.** `IsNAbsorbing I n ↔ ∀ a : Fin (n+1) → R,
(∏ i, a i) ∈ I → ∃ j, (∏ i ∈ univ.erase j, a i) ∈ I`. Forward: a `Finset` of
`Fin (n+1)` with `card = n` is `univ.erase j` for the unique missing `j`
(`Finset.eq_erase_of_card_...`; or take `j` from `Finset.exists_of_card_lt` on the
complement). Backward: `Finset.card_erase_of_mem` + `Finset.card_univ`,
`Fintype.card_fin`. This is the working form used by every later stage.

**A2 — `absorbing_iff_no_irredundant`.** `IsNAbsorbing I n ↔ ¬ ∃ a : Fin (n+1) → R,
(∏ i, a i) ∈ I ∧ ∀ j, (∏ i ∈ univ.erase j, a i) ∉ I`. Immediate from A1 by
`push_neg`. Specialised at `I = ⊥` this is the bridge to Stage E's length bound.

**A3 — `isNAbsorbing_succ` (FROZEN).** Given `a : Fin (n+2) → R` with product in `I`,
apply the hypothesis to the family `Fin (n+1) → R` that keeps `a 0, …, a (n-1)` and
replaces the last slot by `a n * a (n+1)` (i.e. `Fin.snoc`/`Fin.cons` reindexing).
Pull back the resulting `n`-subset: if it contains the merged slot, its preimage has
`n+1` elements; if not, it has `n` elements and can be enlarged by any unused index
(products with more factors stay in `I` because `I` is an ideal). Budget the
reindexing carefully — this is the fiddliest `Finset`/`Fin` lemma in the project.

**A4 — `mem_polyExt_iff` (FROZEN).** `Polynomial.mem_map_C_iff` verbatim (check the
exact orientation and `Ideal.map`-vs-`span` form in the local Mathlib).

**A5 — `polyExt_bot`.** `polyExt (⊥ : Ideal R) = ⊥` via `Ideal.map_bot`; plus
`mem_polyExt_bot_iff : p ∈ polyExt ⊥ ↔ p = 0`.

**A6 — `omegaAbs_eq_succ_of`.** If `IsNAbsorbing I (n+1)` and `¬ IsNAbsorbing I n`
then `omegaAbs I = n + 1`. `≤` from `Nat.sInf_le` (membership of `n+1`); `≥` from:
any `m < n+1` in the set is positive and `n`-absorbing after `n - m` applications of
A3 (`isNAbsorbing_succ`), contradicting `¬ IsNAbsorbing I n`. Formalise the "iterate
A3" step as its own lemma `isNAbsorbing_of_le : m ≤ n → IsNAbsorbing I m →
IsNAbsorbing I n` (induction on `n - m`).

**A7 — `isNAbsorbing_congr_ringEquiv`.** For `e : R ≃+* S`,
`IsNAbsorbing (⊥ : Ideal R) n → IsNAbsorbing (⊥ : Ideal S) n`. Transport the family
along `e.symm`, use `map_prod` and `RingEquiv.map_eq_zero_iff`. Stage F depends on
this.

> **Cheat watch (Stage A).** `isNAbsorbing_succ` must be proved for **arbitrary**
> `R, I, n` — no `[IsDomain R]`, no `n ≥ 1`, no `I ≠ ⊤`. Do **not** "simplify" A1 by
> redefining `IsNAbsorbing`: the frozen `Finset`-card form is the definition and A1
> is a *theorem* about it. `omegaAbs_eq_succ_of` must genuinely use both bounds — a
> proof of `omegaAbs I = n+1` that only shows `IsNAbsorbing I (n+1)` (i.e. only
> `Nat.sInf_le`) is wrong and would let the headline through with no lower bound at
> all. Guardrail `example`s: `IsNAbsorbing (⊥ : Ideal ℤ) 1` (a domain's zero ideal is
> prime, hence 1-absorbing); `¬ IsNAbsorbing (⊥ : Ideal (ZMod 4)) 1` and
> `IsNAbsorbing (⊥ : Ideal (ZMod 4)) 2` (so `omegaAbs (⊥ : Ideal (ZMod 4)) = 2` —
> a cheap end-to-end test of D1, D2 and A6 before the real ring exists).

### Stage B — the ring `A_q` and its multiplication table (`Proofs/Model/`)

Goal: coordinates, the full multiplication table, `J³ = 0`, `J² = W`, Noetherianity.
Delivers frozen `Jid_pow_three_eq_bot`, `Jid_sq_eq_Wid`, `isNoetherianRing_A`. Proved
at the **generic base `(B, τ)`** wherever possible, so Stage F reuses it.

**B1 — instances.** Complete `NonUnitalCommRing (Jmod B τ q)`,
`IsScalarTower`, `SMulCommClass` (these are stated in `Defs.lean` and must be
*proved* during SETUP, not deferred). All fields reduce to `Prod.ext` +
`ring`/`Quotient.sound`; `mul_assoc` is `0 = 0` because the product has zero
`e`-coordinates. Then `CommRing (Alg B τ q)` and `Algebra B (Alg B τ q)` come from
`Unitization`.

**B2 — coordinates.** Support projections `α₁ α₂ α₃ γ₁ γ₂ σ : Alg B τ q → …` (compose
`Unitization.snd` with `Prod` projections), plus `Alg.ext_iff` (equality is
equality of the seven coordinates: `fst` and the six above) and
`simp` lemmas for the coordinates of `0, 1, +, •, algebraMap, e₁, …, tElt`.
This is the file every later stage computes in — make it complete and `simp`-normal.

**B3 — the multiplication table.** `e₁*e₁ = 0`, `e₁*e₂ = 0`, `e₁*e₃ = u₂ + sElt`,
`e₂*e₂ = u₂`, `e₂*e₃ = u₁`, `e₃*e₃ = u₁`, and `w * z = 0` for `w ∈ {u₁,u₂,sElt}`,
`z ∈ {e₁,e₂,e₃,u₁,u₂,sElt}`. Each is `Unitization.ext` + `decide`/`ring` on
coordinates. **Also prove the non-degeneracy guardrails**: `u₁ q ≠ 0`, `u₂ q ≠ 0`,
`sElt q ≠ 0` for `q ≥ 1`, `tElt q ^ q * sElt q = 0`, `tElt q ^ (q-1) * sElt q ≠ 0`
for `q ≥ 1`, and `(1 : A q) ≠ 0` — without these the "counterexample" could be the
zero ring.

**B4 — the general product formula.** `mul_coord : (x * y).γ₁ = x.fst * y.γ₁ + y.fst *
x.γ₁ + (α₂ x * α₃ y + α₃ x * α₂ y + α₃ x * α₃ y)` and similarly for `γ₂`, `σ`, `αᵢ`
(`(x*y).αᵢ = x.fst * y.αᵢ + y.fst * x.αᵢ`). Everything downstream is an instance of
this one formula; derive it once from the `Unitization` multiplication.

**B5 — `Jid` characterisation.** `mem_Jid_iff : x ∈ Jid B τ q ↔ x.fst = 0`
(`RingHom.mem_ker`). Then `mul_mem_Wid : x ∈ Jid → y ∈ Jid → x*y ∈ Wid` (the product
has zero `e`-coordinates) and `Wid_mul_Jid : w ∈ Wid → z ∈ Jid → w * z = 0`.

**B6 — `Jid_pow_three_eq_bot` (FROZEN).** `Ideal.pow_le_pow`/`Ideal.mul_le` reduce
`J^3 = J^2 * J ≤ ⊥` to generators: for `x,y,z ∈ J`, `(x*y)*z = 0` by B5.
Use `Ideal.span`-free reasoning: `Ideal.pow_eq_bot_iff`-style or
`le_antisymm (Ideal.mul_le.2 …) bot_le` after rewriting `pow_succ`.

**B7 — `Jid_sq_eq_Wid` (FROZEN).** `≤` from B5. `≥`: `u₁ = e₃*e₃`, `u₂ = e₂*e₂`,
`sElt = e₁*e₃ + e₂*e₂` (char 2!), all products of two elements of `J`, so the three
span-generators lie in `J^2`; conclude with `Ideal.span_le`.

**B8 — `isNoetherianRing_A` (FROZEN).** `Module.Finite Dbase (A q)` (spanned by
`1, e₁, e₂, e₃, u₁, u₂, sElt`; or transport the `Prod` module structure), hence
`IsNoetherian Dbase (A q)` (Hilbert basis gives `IsNoetherianRing Dbase`), hence
`IsNoetherian (A q) (A q)` by `isNoetherian_of_tower Dbase`, i.e.
`IsNoetherianRing (A q)` via `isNoetherianRing_iff`.

> **Cheat watch (Stage B).** The non-degeneracy guardrails in B3 are **mandatory**:
> a model in which `sElt = 0`, or in which `Quo` accidentally collapses, would make
> every later theorem true and the whole project vacuous — prove `sElt q ≠ 0` and
> `tElt q ^ (q-1) * sElt q ≠ 0` *before* claiming any stage `✅`. Do not "fix" a
> failing table entry by editing `Defs.lean` (frozen) — if a table entry does not
> match `SKETCH.md`, that is a `⚠️` blocker, not a licence to re-freeze. `Jid_sq_eq_Wid`
> must be a genuine **equality** of ideals: proving only `J² ≤ W` (the easy half)
> and calling it done is a weakening. `Jid_pow_three_eq_bot` must be `= ⊥`, not
> `≤ Wid` or "for the specific generators". Noetherianity must be proved, not
> assumed via an `IsNoetherianRing` instance conjured by `sorry`/`axiom`.

### Stage C — the characteristic-2 cancellation, Step 2 (`Proofs/Cancellation/`) ★ MILESTONE ★

Goal: the frozen `s_component_cancellation`, plus the reusable coefficient-level
statement Stage E consumes. This is one of the two mathematical hearts.

**C1 — `f2_cancel` (the whole content, 64 cases).**
```lean
theorem f2_cancel : ∀ α₁ α₂ α₃ β₁ β₂ β₃ : ZMod 2,
    α₂*β₃ + α₃*β₂ + α₃*β₃ = 0 → α₁*β₃ + α₃*β₁ + α₂*β₂ = 0 → α₁*β₃ + α₃*β₁ = 0 := by
  decide
```
(Kernel `decide` over `(ZMod 2)^6`; `native_decide` is BANNED and unnecessary.)
The mathematical reading: if `α₂β₂ ≠ 0` then `α₂ = β₂ = 1`, and the first equation
becomes `β₃ + α₃ + α₃β₃ = 0`, which over `𝔽₂` forces `α₃ = β₃ = 0`, whence
`α₁β₃ + α₃β₁ = 0` anyway; otherwise the second equation gives it directly.

**C2 — `dvd_s_of_u_vanish`.** For `a₁ a₂ a₃ b₁ b₂ b₃ : Dbase`, if
`a₂b₃ + a₃b₂ + a₃b₃ = 0` and `a₁b₃ + a₃b₁ + a₂b₂ = 0` then `tD ∣ a₁b₃ + a₃b₁`.
Proof: `Polynomial.X_dvd_iff` turns the goal into `(a₁b₃+a₃b₁).coeff 0 = 0`; apply
`Polynomial.mul_coeff_zero` and `Polynomial.coeff_add` to both hypotheses and to the
goal, then `exact f2_cancel _ _ _ _ _ _ h₁' h₂'`. **This is the exact shape Stage E
takes as a hypothesis**, so state it in this form and do not specialise it.

**C3 — `s_component_cancellation` (FROZEN).** Unfold: `x*y ∈ Ideal.span {sElt q}`
means (Stage B coordinates + `Ideal.mem_span_singleton`-style analysis, or directly
`Ideal.span {sElt q} = {z | z.fst = 0 ∧ z.αᵢ = 0 ∧ z.γⱼ = 0}`) that the `u₁`- and
`u₂`-coordinates of `x*y` vanish. By B4 those are the two hypotheses of C2 (the
`fst`-parts vanish because `x, y ∈ J`). C2 gives `tD ∣ (σ-lift)`, and the conclusion
`x*y ∈ Ideal.span {tElt q * sElt q}` follows because that ideal is exactly
`{z | z.fst = 0, z.αᵢ = 0, z.γⱼ = 0, z.σ ∈ tD • Quo …}`.
Support lemmas `mem_span_sElt_iff` and `mem_span_t_sElt_iff` (proved from
`Ideal.mem_span_singleton` + the fact that `Ideal.span {w} = Dbase ∙ w` when
`Jid * w = 0`) are the reusable part; put them in this file.

> **Cheat watch (Stage C).** The hypothesis is `x, y ∈ J` for **arbitrary** `x, y` —
> not for generators `eᵢ`, not for elements with zero `W`-part. Do not add
> `x = y` or coefficient hypotheses. The conclusion is membership in
> `span {tElt * sElt}`, i.e. **divisibility by `t` after passing to `D/t^q`** — do
> not weaken it to `x*y ∈ span {sElt}` (trivial) or to `x*y ≠ sElt`. `f2_cancel`
> must be proved by kernel `decide` over all 64 tuples; proving it for the six
> tuples that show up in Step 4, or `sorry`ing one branch, defeats the entire
> counterexample. Finally: this lemma is **false over `D[X]`** (that is the point of
> the problem) — so it must be stated for `A q` / `Dbase` only, and Stage E must take
> it as an explicit *hypothesis*, never as a global fact about `Alg B τ q`.

### Stage D — the explicit witnesses, Steps 3-lower / 4 / 5 (`Proofs/Witnesses/`) ★ MILESTONE ★

Goal: the two irredundant zero-products and the polynomial identity. Delivers frozen
`not_isNAbsorbing_A_q`, `fPoly_mul_gPoly`, `not_isNAbsorbing_polyExt_A_succ_q`.
Depends only on Stage A (A1/A2/A5) and Stage B — **independent of Stage C and E**,
so it runs in parallel with them.

**D1 — `pow_t_smul_s`.** `tElt q ^ k * sElt q = 0 ↔ q ≤ k` (for the `→` direction use
`Ideal.Quotient.eq_zero_iff_mem` + `Ideal.mem_span_singleton` + `pow_dvd_pow_iff`).
Corollaries: `tElt q ^ q * sElt q = 0`, `tElt q ^ (q-1) * sElt q ≠ 0` (`q ≥ 1`).

**D2 — `not_isNAbsorbing_A_q` (FROZEN).** Use A2 with the family
`a : Fin (q+1) → A q`, `a 0 = sElt q`, `a i = tElt q` for `i ≠ 0`. Product
`= tElt^q * sElt = 0`. For irredundancy: dropping index `0` leaves `tElt q ^ q`,
nonzero because `fst (tElt q ^ q) = tD ^ q ≠ 0` in the domain `D`; dropping any
`j ≠ 0` leaves `tElt q ^ (q-1) * sElt q ≠ 0` by D1. Compute both products with
`Finset.prod_congr` + `Finset.prod_const` on `univ.erase j`.

**D3 — `fPoly_mul_gPoly` (FROZEN).** Expand `fPoly * gPoly` with `Polynomial.ext`
over coefficients (`f₀ = e₂, f₁ = e₃`; `g₀ = e₁, g₁ = e₁+e₂, g₂ = e₂+e₃`) and apply
the Stage-B table coefficientwise:
`(fg)₀ = e₂e₁ = 0`, `(fg)₁ = e₂(e₁+e₂) + e₃e₁ = u₂ + (u₂+s) = s`,
`(fg)₂ = e₂(e₂+e₃) + e₃(e₁+e₂) = (u₂+u₁) + (u₂+s+u₁) = s`, `(fg)₃ = e₃(e₂+e₃) = u₁+u₁ = 0`.
Char 2 is what kills the `u`-terms. Easiest route: `ring_nf` to a normal form in
`C (eᵢ) * X^k`, then rewrite with the table and `two_smul`/`CharTwo.add_self_eq_zero`.

**D4 — `not_isNAbsorbing_polyExt_A_succ_q` (FROZEN).** Rewrite `polyExt ⊥ = ⊥` (A5)
and use A2 with `a : Fin (q+2) → (A q)[X]`, `a 0 = fPoly q`, `a 1 = gPoly q`,
`a i = C (tElt q)` otherwise. Product `= C (tElt q)^q * (fPoly*gPoly) =
C (tElt^q * sElt) * (X+X²) = 0` by D3 and D1. Irredundancy: dropping `0` leaves
`C (tElt^q) * gPoly`, whose `X⁰`-coefficient is `tElt^q * e₁ ≠ 0` (the `α₁`-coordinate
is `tD^q ≠ 0`); dropping `1` leaves `C (tElt^q) * fPoly` with `X⁰`-coefficient
`tElt^q * e₂ ≠ 0`; dropping any `i ≥ 2` leaves
`C (tElt^{q-1}) * (fPoly*gPoly) = C (tElt^{q-1} * sElt) * (X+X²)`, whose
`X¹`-coefficient is `tElt^{q-1} * sElt ≠ 0` by D1.

> **Cheat watch (Stage D).** Every statement is `∀ q ≥ 2` — proving `q = 2` (or
> `q = 3`) by `decide` and asserting the general case is the most tempting cheat in
> this project and is FORBIDDEN. Irredundancy must be checked for **every** dropped
> index, including the two special ones; showing only "the full product is 0" proves
> nothing (`0` is `n`-absorbing for many `n`). `fPoly_mul_gPoly` must be an
> **equality** in `A_q[X]` — not "the `u`-parts vanish", not a statement about
> coefficients only. Do not replace `f`, `g` by other polynomials that happen to work;
> they are frozen in `Defs.lean` and the sketch names them. And do not weaken
> `¬ IsNAbsorbing … (q+1)` to `¬ IsNAbsorbing … q` (a *different*, weaker claim once
> monotonicity is in play).

### Stage E — the generic irredundant-length bound, Step 3-upper (`Proofs/Bound/`) ★ HARDEST MATH ★

Goal: the case analysis of `SKETCH.md` Step 3, done **once at the generic base**
`(B, τ)` with `[IsDomain B]` and `Prime τ`, then instantiated at `B = D`. Delivers
frozen `isNAbsorbing_A_succ_q`. Depends on Stage A (A1/A2), Stage B, Stage C (C2).

Setting for the whole file: `m : ℕ`, `a : Fin m → Alg B τ q`, `h0 : ∏ i, a i = 0`,
`hirr : ∀ j, ∏ i ∈ univ.erase j, a i ≠ 0`. Write `dᵢ = (a i).fst ∈ B` and
`Jset = {i | dᵢ = 0}` (the factors lying in `J`).

**E1 — `fst_prod`.** `(∏ i, a i).fst = ∏ i, dᵢ` (`Unitization.fstHom` is a ring hom,
`map_prod`). Hence **Case 0**: if `Jset = ∅` then `∏ dᵢ ≠ 0` in the domain `B`, so
`∏ a i ≠ 0` — contradiction. So `Jset ≠ ∅`.

**E2 — Case 1 (`3 ≤ Jset.card`) ⟹ `m ≤ 3`.** Three factors in `J` multiply to `0`
(Stage B6). If `m ≥ 4` pick `j ∉` those three; the product over `univ.erase j` still
contains all three, hence is `0` — contradicting `hirr`. Formalise "the product over a
set containing three `J`-indices is 0" as
`prod_eq_zero_of_three_J : i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ → i₁,i₂,i₃ ∈ S → (∀ … ∈ J) →
∏ i ∈ S, a i = 0` (peel the three factors with `Finset.mul_prod_erase` three times).

**E3 — the collapse lemma.** If `S` contains exactly the `J`-indices `i₁, i₂` (two of
them) then `∏ i ∈ S, a i = (∏ i ∈ S \ {i₁,i₂}, dᵢ) • (a i₁ * a i₂)`; and if it
contains exactly one, `i₁`, then `∏ i ∈ S, a i = (∏ dᵢ) • a i₁ + Σ …` collapses to
`(∏_{i ∈ S \ {i₁}} dᵢ) • a i₁` **once** we know `a i₁ ∈ W` (see E5). Proof: expand
each non-`J` factor as `algebraMap dᵢ + (its J-part)`, and kill every term with three
`J`-factors by B6 and every term with two `J`-factors times a `W`-element by B5.
This is the bookkeeping core of the stage; state it as
`prod_eq_smul_of_two_J` / `prod_eq_smul_of_one_J` and prove it by induction on the
finset of non-`J` indices.

**E4 — Case 2 (`Jset.card = 2`) ⟹ `m ≤ q + 1`** (uses C2). Let `x = a i₁, y = a i₂`,
`c = ∏_{i ∉ Jset} dᵢ ≠ 0`. From `h0` and E3, `c • (x*y) = 0`. Coordinates:
`c * (x*y).γⱼ = 0` in the domain `B` with `c ≠ 0` gives `(x*y).γ₁ = (x*y).γ₂ = 0`,
i.e. exactly the two hypotheses of C2; so `τ ∣ a` for a lift `a` of `(x*y).σ`
(over `B = D`; **at the generic base this is a hypothesis of the theorem**). Also
`c • (x*y) = 0` gives `τ^q ∣ c * a`. Now: (i) for each non-`J` index `i`, `τ ∣ dᵢ` —
otherwise `Prime.pow_dvd_of_dvd_mul_left` gives `τ^q ∣ (c/dᵢ) * a`, making the
`erase i` product `0`, contradicting `hirr`; (ii) fix any non-`J` index `i₀`; then
`τ^{m-3} ∣ ∏_{i ∉ Jset, i ≠ i₀} dᵢ` and `τ ∣ a`, so `τ^{m-2} ∣ (∏_{i≠i₀} dᵢ) * a`;
(iii) `hirr i₀` says the `erase i₀` product is nonzero, i.e. `τ^q ∤ (∏_{i≠i₀} dᵢ)*a`,
forcing `m - 2 ≤ q - 1`, i.e. `m ≤ q + 1`. (Handle `m ≤ 2` separately — trivial since
`q ≥ 2`.) **No `multiplicity` API is needed anywhere in this argument.**

**E5 — Case 3 (`Jset.card = 1`) ⟹ `m ≤ q + 1`.** Let `x = a i₁`, `c = ∏_{i≠i₁} dᵢ ≠ 0`.
The `e`-coordinates of the product are `c * x.αⱼ`, so `x.αⱼ = 0` (domain), i.e.
`x ∈ W`; then all cross terms die (B5) and the product is `c • x`. The `u`-coordinates
give `x.γⱼ = 0`, so `x` is in the `s`-line, `x.σ = [a]`, and `τ^q ∣ c * a`. Repeat
E4(i)–(iii) verbatim with `a` in place of `x*y` and `m-1` non-`J` factors: each
`τ ∣ dᵢ`, so `τ^{m-2} ∣ (∏_{i≠i₀} dᵢ)`, and `hirr i₀` forces `m - 2 ≤ q - 1`.
(Here `τ ∣ a` is **not** available — and not needed.)

**E6 — `irredundant_len_le` (generic).** Combining E1–E5:
under `[IsDomain B]`, `Prime τ`, `1 ≤ q`, every irredundant zero-product has
`m ≤ q + 2`; and **if additionally** the cancellation hypothesis
`hcanc : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : B, a₂*b₃+a₃*b₂+a₃*b₃ = 0 → a₁*b₃+a₃*b₁+a₂*b₂ = 0 →
τ ∣ (a₁*b₃+a₃*b₁)` holds, then `m ≤ q + 1`. (Without `hcanc`, E4 only yields
`τ^{m-3} ∣ (∏_{i≠i₀} dᵢ) * a`, hence `m ≤ q + 2` — this weaker generic bound is
exactly what Stage F needs, so **prove both versions in this file**.)

**E7 — `isNAbsorbing_A_succ_q` (FROZEN).** Instantiate E6 at `B = Dbase`, `τ = tD`
(`Polynomial.prime_X`, `hcanc := C2`) with `m = q + 2`, and convert via A2.

> **Cheat watch (Stage E).** The statement is `∀ q ≥ 2`, `∀` families — an argument
> that works "for the families we care about" is worthless here, because this is the
> *upper* bound and it is what makes `ω = q+1` rather than `≥ q+1`. Do **not** add
> hypotheses to the frozen theorem (no "assume no factor is a unit", no "assume the
> `aᵢ` are in `J ∪ D`"). Case 0 (**no** factor in `J`) and the small-`m` edge cases
> (`m ≤ 2`) must be handled, not waved through — the sketch omits Case 0 and you must
> supply it. The `τ ∣ dᵢ` steps genuinely need `Prime τ` (`Prime.pow_dvd_of_dvd_mul_left`),
> not `Irreducible τ` and not "`D` is a PID" hand-waving. Do not import Stage C's
> conclusion as a *global* fact: it must enter E6 as the explicit hypothesis `hcanc`,
> because Stage F instantiates the same lemma at a base where `hcanc` is FALSE. And
> never replace the ideal-membership `∈ ⊥` by `= 0` in a way that silently changes
> the frozen statement — convert with `Ideal.mem_bot`, keep the frozen text.

### Stage F — the polynomial transfer, Step 6 (`Proofs/Transfer/`) ★ HARDEST ENGINEERING ★

Goal: make Step 6 ("repeating the valuation argument over `D[X]`") rigorous by
exhibiting `A_q[X] ≅ Alg (D[X]) (C t) q` and pushing E6's generic bound across.
Delivers frozen `isNAbsorbing_polyExt_A_succ_succ_q`. Depends on Stage A (A5, A7),
Stage B, Stage E (E6, generic version).

**F1 — the coefficient equivalence.** `Quo Dbase tD q |>.Polynomial ≃+* Quo (Polynomial Dbase) (C tD) q`,
i.e. `(D/(t^q))[X] ≃+* D[X]/((C t)^q)`, from
`Ideal.polynomialQuotientEquivQuotientPolynomial` plus
`Ideal.span {(C tD)^q} = (Ideal.span {tD^q}).map C` (`Ideal.map_span`, `map_pow`).

**F2 — the transfer isomorphism.**
`transferEquiv q : Polynomial (A q) ≃+* Alg (Polynomial Dbase) (C tD) q`.
Build the forward map with `Polynomial.eval₂RingHom ψ ξ` where
`ψ : A q →+* Alg (D[X]) (C tD) q` is the coefficientwise `C`-inclusion (a ring hom:
check on coordinates, using that the bilinear forms commute with `C`) and
`ξ = algebraMap (D[X]) _ Polynomial.X`. Build the inverse coordinatewise: an element
of `Alg (D[X]) (C tD) q` is seven `D[X]`- (resp. `D[X]/(Ct)^q`-) coordinates, each of
which is a polynomial in `X` with coefficients in `D` (resp. `D/t^q` via F1); reassemble
with `Polynomial.sum`. Prove `left_inv`/`right_inv` by `Polynomial.ext` on coefficients
+ `Alg.ext_iff`. *Alternative route if this stalls:* skip the bijection and instead
prove directly that `Polynomial (A q)` satisfies the seven structural facts E1–E5 need
(`fst` ring hom to the domain `D[X]`, coordinates, `J³ = 0`, `W·J = 0`, the product
formula, `τ`-torsion of the `s`-coordinate) by re-deriving them coefficientwise; then
re-run E6 there. Record whichever route you take as a `📝` entry.

**F3 — `isNAbsorbing_polyExt_A_succ_succ_q` (FROZEN).** `polyExt ⊥ = ⊥` (A5); apply
E6's **generic** (`hcanc`-free) bound at `B = Polynomial Dbase`, `τ = C tD`
(`Polynomial.prime_C_iff` + `Polynomial.prime_X`; `IsDomain` is automatic) to get
`m ≤ q + 2` for irredundant zero-products in `Alg (D[X]) (C tD) q`; transport along
`transferEquiv` with A7; convert with A2 at `n = q + 2`.

> **Cheat watch (Stage F).** `transferEquiv` must be an **isomorphism of rings**, both
> directions proved — a one-sided hom, or an "obvious" `Equiv` with `sorry`ed
> `map_mul`, invalidates the whole stage. Do **not** apply Stage C / the `hcanc`
> version of E6 at the base `D[X]`: `hcanc` is *false* there (that is precisely the
> content of Step 4/`fPoly_mul_gPoly`), and using it would "prove" `ω_{A[X]} = q+1`,
> silently contradicting Stage D. Do not weaken this theorem to `≥`-only statements or
> quietly drop it: without it `omegaAbs_polyExt_A` is unprovable and `gap_family`
> would have to be faked. If F2 stalls, take the alternative route in F2 — do **not**
> "resolve" the stall by adding a hypothesis to the frozen statement.

### Stage G — the absorbing numbers and the headline (`Proofs/Headline/`)

Goal: assemble. Delivers frozen `omegaAbs_A`, `omegaAbs_polyExt_A`, `gap_family`,
`polyAbsorbingConj_false`. Depends on everything.

**G1 — `omegaAbs_A` (FROZEN).** `omegaAbs_eq_succ_of` (A6) applied to
`isNAbsorbing_A_succ_q` (E7) and `not_isNAbsorbing_A_q` (D2).

**G2 — `omegaAbs_polyExt_A` (FROZEN).** `omegaAbs_eq_succ_of` applied to
`isNAbsorbing_polyExt_A_succ_succ_q` (F3) and `not_isNAbsorbing_polyExt_A_succ_q` (D4);
note `q + 2 = (q + 1) + 1`.

**G3 — `gap_family` (FROZEN).** Set `q = n - 1`; from `3 ≤ n` get `2 ≤ q` and
`q + 1 = n`, `q + 2 = n + 1` (`Nat.sub_add_cancel`, `omega`). Combine
`isNoetherianRing_A`, G1, G2.

**G4 — `polyAbsorbingConj_false` (FROZEN).** Assume `h : PolyAbsorbingConj`;
specialise at `R = A 2`, `I = ⊥` to get `omegaAbs (polyExt ⊥) = omegaAbs ⊥`, i.e.
`4 = 3` by G1/G2 at `q = 2`; `omega`/`simp` closes it.

> **Cheat watch (Stage G).** `polyAbsorbingConj_false` on its own is a *weaker*
> statement than the sketch's claim (it does not record that the counterexample is
> Noetherian, nor the exact values, nor that they exist for every `n ≥ 3`) — that is
> why `gap_family`, `omegaAbs_A`, `omegaAbs_polyExt_A` and `isNoetherianRing_A` are
> frozen alongside it and must all be proved. Do not "prove" the headline by
> specialising `PolyAbsorbingConj` to a ring where `omegaAbs` is `0` (the `sInf ∅`
> sentinel): the refutation must come from two *computed* values, which is what G1/G2
> supply. `gap_family` must be `∀ n ≥ 3`, not `n = 3`. And `omegaAbs_A` must not be
> obtained by unfolding `sInf` into a `decide`-style computation on a fixed `q`.

### Discharge & Solution (after the frozen theorems are proved)

In `Prob30c/Solution.lean`, restate each frozen theorem **verbatim** in
`namespace Prob30c.Solution` and set it `:= <name>_proof` (the sorry-free
declaration from `Proofs/`). In `Prob30c/Discharge.lean`, for each pair write
`example : @Prob30c.<name> = @Prob30c.Solution.<name> := rfl` — this compiles
**iff** the proof has *exactly* the frozen proposition (machine-checked no-drift).
`verify.py` checks both modules build and that
`#print axioms Prob30c.Solution.<name>` is clean for every one of the 15 frozen
names.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems, Jmod ring instances PROVED, skeleton builds, pins recorded)
      │
      ├────────────────────────────┬──────────────────────────────┐
      ▼                            ▼                              ▼
Stage A  (Absorbing API)      Stage B  (Model: table,        [independent — run
  A1 A2 A3✦ A4✦ A5 A6 A7        J³=0✦ J²=W✦ Noeth✦)           in parallel, 2 agents]
      │                            │
      │                            ├──────────────┐
      │                            ▼              ▼
      │                       Stage C ★       Stage D ★
      │                       (char-2         (t^q s, f·g = X(1+X)s✦,
      │                        cancel ✦)       both lower bounds ✦✦)
      │                            │              │
      └──────────┬─────────────────┘              │   ← MILESTONE: after C + D the
                 ▼                                │     counterexample is verified
            Stage E  (generic bound; ✦ q+1-absorbing)     to be non-degenerate
                 │                                │
                 ├────────────────┐               │
                 ▼                │               │
            Stage F  (transfer iso; ✦ q+2-absorbing)
                 │                │               │
                 └────────────────┴───────┬───────┘
                                          ▼
                              Stage G  (ω values ✦✦, gap_family ✦, HEADLINE ✦)
                                          │        (#print axioms clean)
                                          ▼
                              Discharge.lean + Solution.lean
```

- **Parallelism.** A and B are independent and should be started together. C and D
  are independent of each other (both need B; D also needs A1/A2/A5). E needs A + B +
  C. F needs A + B + E. G needs everything. A comfortable 4-worker split for the first
  iterations is: `A1–A3` | `A4–A7` | `B1–B4` | `B5–B8`; then `C` | `D1–D2` | `D3–D4` |
  `B`-leftovers; then `E3–E5` split by case | `F1–F2`.
- **Milestone.** After Stage C + Stage D the mathematical heart is done and the
  construction is certified non-degenerate; `not_isNAbsorbing_A_q`,
  `fPoly_mul_gPoly` and `not_isNAbsorbing_polyExt_A_succ_q` are already citable.
- **Hardest engineering:** Stage F (the transfer isomorphism) — budget the most time
  there. **Hardest mathematics:** Stage E (the four-case length bound, especially the
  E3 collapse lemma). Stage A3 (`isNAbsorbing_succ`) is deceptively fiddly `Fin`/
  `Finset` surgery — do not leave it to the last iteration.
- **Note.** The headline `polyAbsorbingConj_false` is reachable via A → B → C → D → E
  → G *without* Stage F only if `omegaAbs_polyExt_A` is dropped — it is **not**
  dropped (it is frozen), so Stage F is mandatory. Prove the rest first anyway: a
  project that is complete except for F is a far better outcome than one that stalls
  in F with the witnesses unproved.

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them, and the problem-specific
traps are appended at the end.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem must be hypothesis-free wherever the source claim is unconditional.
  Forbidden moves: adding `(h : …)` to a frozen statement; proving a `∀ x`
  (or `∀ x y`) claim only for generators / a finite subset and claiming the
  general case; replacing an equality with a one-sided inclusion. If a sub-proof
  seems to need an assumption, **derive it or restructure** — do not weaken the
  statement. (Downstream stages typically instantiate these at *arbitrary*
  elements, so a quiet weakening breaks the assembly silently.) The only
  hypotheses permitted in this project's frozen theorems are `2 ≤ q` / `3 ≤ n`,
  which `SKETCH.md` itself states.

- **Keep every predicate the textbook definition — do not soften it.** Quantifiers
  must match the source exactly (e.g. "for all finite families" must not become
  "for `n ≤ 2`" or "for one fixed family"); genuine finite generation /
  exactness / etc. must not be replaced by a cardinality-bounded or
  "I-couldn't-find-it" surrogate. A softened predicate can make the headline
  vacuous.

- **Get the modeling right once, in SETUP, and freeze it.** A dropped or extra
  relation/hypothesis in a frozen definition silently changes the object and can
  break the proof downstream. Validate the core modeling facts *before* freezing,
  with small guardrail `example`s: here, that `sElt q ≠ 0`, `u₁ q ≠ 0`, `u₂ q ≠ 0`,
  `tElt q ^ (q-1) * sElt q ≠ 0` (`q ≥ 1`), `(1 : A q) ≠ 0`, and that the six table
  entries `e₁e₁ = 0`, `e₁e₂ = 0`, `e₁e₃ = u₂ + sElt`, `e₂e₂ = u₂`, `e₂e₃ = u₁`,
  `e₃e₃ = u₁` all hold as stated.

- **Discharge ring/structure axioms once — never `sorry` them.** `CommRing (A q)`
  comes from `Unitization`; the only thing you supply is
  `NonUnitalCommRing (Jmod B τ q)` (+ `IsScalarTower`, `SMulCommClass`), all of
  whose fields are `Prod.ext` + `ring`, with `mul_assoc` literally `0 = 0`. If you
  feel the urge to `sorry` associativity or commutativity, you modeled the object
  wrong. (And a `sorry` outside `Theorems.lean` fails `verify.py` check 2 outright.)

- **Keep module-side and ring-side objects distinct.** `Jid` is an `Ideal (Alg …)`;
  `Jmod` is the underlying `B`-module; `Wid` is a `span`. The `s`-coordinate lives in
  `Quo B τ q`, its lifts live in `B` — do not conflate a coordinate with a lift.
  Likewise keep `tD : Dbase`, `tElt q : A q` and `C (tElt q) : (A q)[X]` apart, and
  never confuse `tD` with the `X` of `A_q[X]`.

- **`decide` budget — and `native_decide` is BANNED.** The only intended `decide` is
  `f2_cancel` (64 tuples in `(ZMod 2)^6`) and small table entries. Do **not** try to
  `decide` anything quantified over `Dbase`, `Quo`, `A q`, or `Polynomial` — those are
  infinite and/or `noncomputable` and will not reduce. `native_decide` adds a
  compiler-trust axiom and would dirty `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen during proving (pinned in `scripts/frozen.sha256`). If a
  *definition* seems missing (coordinate projections, `mem_Jid_iff`, the transfer
  equiv), it belongs in a `Proofs/` support file. If a *statement* seems wrong, stop
  and re-read `SKETCH.md`.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no `native_decide`/
  `ofReduceBool`. `USER_NOTES.md` permits **no** assumed certificates for this
  problem, so `scripts/ALLOWED_AXIOMS.txt` is empty and **any** `axiom` declaration
  anywhere in the project is a hard failure.

- **Assumed certificates go in as `axiom`s, never as hypotheses.** Not applicable
  here (none are permitted), and this never relaxes the cardinal rule above.

- **Problem-specific traps.**
  1. **Vacuity.** If `Quo` collapses (`q = 0`), or a table entry is dropped, or `sElt`
     is secretly `0`, then every frozen theorem about `A q` becomes easy and
     meaningless. The Stage-B non-degeneracy guardrails are the defence; run them
     first.
  2. **Using Stage C at the wrong base.** `s_component_cancellation` is TRUE over
     `D = 𝔽₂[t]` and FALSE over `D[X]` — that asymmetry *is* the counterexample.
     Stage E must receive it as the explicit hypothesis `hcanc`; if it ever leaks in
     as a global `simp` lemma or an instance, Stage F will "prove" `q+1` and the
     project silently self-contradicts.
  3. **`≥` masquerading as `=`.** Steps 3 and 6 each need *both* bounds. It is easy
     to prove the lower bounds (Stage D) and then assert `ω = q+1` / `ω = q+2`; the
     upper bounds (Stages E, F) are 80% of the work and cannot be skipped.
     `omegaAbs_eq_succ_of` is designed so that a missing bound makes the proof fail.
  4. **Fixing `q`.** Every quantitative claim is `∀ q ≥ 2` (equivalently `∀ n ≥ 3`).
     A `decide`-style proof at `q = 2` proves nothing about the family.
  5. **Char 2.** `𝔽₂` is used in exactly two places: `f2_cancel` (where `𝔽₂`'s
     smallness is essential) and the cancellations `u₂ + u₂ = 0`, `u₁ + u₁ = 0` in
     `fPoly_mul_gPoly` / `Jid_sq_eq_Wid` (`sElt = e₁e₃ + e₂e₂`). Do not silently
     import `CharTwo` facts elsewhere, and do not "generalise" the base field to `𝔽_p`
     — the counterexample is specific to `𝔽₂`.
  6. **`I[X]` vs `I·R[X]` vs `⊥`.** The frozen polynomial-side statements are about
     `polyExt (⊥ : Ideal (A q))`, deliberately, so the reader sees `I[X]`. Rewrite it
     to `⊥` (A5) only *inside* proofs, never in a frozen statement.
  7. **The conjecture must stay general.** `PolyAbsorbingConj` quantifies over all
     rings and ideals; refuting it is therefore the *weakest* form of the result,
     which is why the Noetherian, explicit, `∀ n ≥ 3` content is frozen separately in
     `gap_family`. Do not "simplify" the project by dropping those.
  8. **The sketch's own caveat.** `SKETCH.md` notes that this contradicts a
     long-standing conjecture and should be independently verified. Formalize what the
     sketch claims, faithfully; if a step turns out to be **false in Lean**, that is a
     finding, not a bug to route around — append a `⚠️` entry with the exact failing
     goal and the counter-computation, and do **not** patch it by weakening a frozen
     statement.
