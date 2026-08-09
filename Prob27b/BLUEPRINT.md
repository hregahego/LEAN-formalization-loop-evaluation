# Blueprint: Problem 27(b) — `Int(A)` need not be a ring even when `D` has finite residue rings

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
Over `D = 𝔽₂[π]` (which has finite residue rings) we build the finite
noncommutative `𝔽₂`-algebra `R` = path algebra of `e ⟶u f ⟶v e` truncated in
degree ≥ 4, exhibit an explicit polynomial `F ∈ R[X]` that vanishes at *every*
element of `R` but whose right multiple `F·e` does not, and then transport this
failure along `A = D ⊗_{𝔽₂} R = R[π]`: dividing the lift `F̃` by `π` produces
`P ∈ Int(A)` with `P·e ∉ Int(A)`. The single idea that makes it work is that
`K(R)` (the right null-polynomials of `R`) fails to be a right ideal, and `Int(A)`
is a `π`-scaled copy of that failure.

- **Headline target (frozen theorem `prob27b_counterexample`).** One conjunction
  asserting *all* hypotheses of the conjecture together with its failure:
  `D` has finite residue rings (`∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)`), `A` is
  finite free over `D` (`Nonempty (Basis (Fin 8) D A)`), `A` is torsion-free
  (`NoZeroSMulDivisors D A`), and
  `∃ p q : Polynomial B, IsIntegerValued p ∧ IsIntegerValued q ∧ ¬ IsIntegerValued (p * q)`.
  Every predicate it mentions (`D`, `A`, `B`, `IsIntegerValued`) is frozen in
  `Defs.lean`. It is witnessed concretely: the companion frozen theorems
  `P_integerValued`, `constE_integerValued` and `Pe_not_integerValued` exhibit the
  witness pair `(P, C (iota RAlg.e))`, and `D_hasFiniteResidueRings`,
  `A_isFreeOfRankEight`, `A_torsionFree` are frozen on their own so the
  hypothesis side cannot be quietly dropped.
- **Recommended intermediate milestone (prove first):**
  `nullPoly_not_rightIdeal` — `∃ p c, IsNullPoly p ∧ ¬ IsNullPoly (p * C c)`, i.e.
  Steps 1–3 of the sketch: `K(R)` is not a right ideal of `R[X]`. This is the
  mathematical heart; once it is proved everything after it is `π`-bookkeeping.
  It is a citable result on its own.
- **Setting / ground assumptions:** characteristic 2 throughout;
  `𝔽₂ = ZMod 2`, `D = 𝔽₂[π] = Polynomial (ZMod 2)`, `K = 𝔽₂(π) = RatFunc (ZMod 2)`.
  `R` is an **8-dimensional associative noncommutative** `𝔽₂`-algebra with unit
  `1 = e + f` (not a domain, not commutative, not local). `A` and `B` are the same
  8 structure constants with coefficients in `D` and `K`. Explicitly *not*
  involved: no analysis, no inequalities, no cardinal arithmetic, no tensor
  products, no quiver/path-algebra library, no Gröbner bases. Everything is
  either a finite `decide` over `2⁸ = 256` elements or componentwise algebra in
  `Fin 8`.

> **Why this is tractable.** The whole counterexample lives in one explicit
> 8-dimensional algebra whose multiplication is a fixed table of structure
> constants, so every ring axiom is `ext i; fin_cases i <;> ring` and the one
> genuinely quantified statement (`F` kills every `r ∈ R`) is a decidable
> proposition over a 256-element computable type. The real risk is **not** the
> mathematics: it is (a) **mis-modeling** — getting the path-composition order
> backwards, which silently produces a *different* algebra in which `F` is not
> null; (b) **assuming commutativity** — `Polynomial.eval_mul` is false here, and
> `(p * C c).eval x = p.eval x * c` is false here, and both are seductive; and
> (c) **over-reach in the headline** — dropping the finite-residue-ring conjunct,
> or defining `Int(A)` inside `A[X]` rather than `B[X]`, either of which makes the
> statement no longer a counterexample to Problem 27(b).

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is to produce a compiling skeleton in which **every
`Definition` and every `Theorem` statement is written and frozen**, with all
proofs `:= sorry`. Once frozen, `Defs.lean` and `Theorems.lean` are **never
edited again** during the proving phase. Everything proved later lives in
support files and may not change a single character of the frozen statements.

### 1. Create the Lean project

```bash
cd <project-dir>
lake +leanprover/lean4:v4.31.0 new Prob27b math
# pin Mathlib in lakefile + lake-manifest to the matching rev, then:
lake exe cache get
lake build            # must succeed on the bare skeleton before anything else
```

Pin `lean-toolchain` to `leanprover/lean4:v4.31.0` and pin the Mathlib dependency
to the Mathlib revision whose own `lean-toolchain` is exactly that version (read
it off the Mathlib commit before pinning — a mismatch makes `lake exe cache get`
useless and forces a multi-hour source build). Record the chosen toolchain and
Mathlib rev in the first `PROGRESS.md` entry.

Layout:

```
<project-dir>/
  Prob27b/
    Defs.lean          -- FROZEN after this stage: every object the proof needs
    Theorems.lean      -- FROZEN after this stage: the frozen theorem statements (sorry)
    Proofs/
      StageA/          -- Stage A: the algebra RAlg and the finite ring R
      StageB/          -- Stage B: F is a null polynomial on R
      StageC/          -- Stage C: K(R) is not a right ideal of R[X]
      StageD/          -- Stage D: the arithmetic setting D, A, B, redPi
      StageE/          -- Stage E: lifting F to A and landing P in Int(A)
      StageF/          -- Stage F: P·e leaves Int(A); the headline
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `Prob27b.Solution`, proven (clean names)
  Prob27b.lean         -- imports everything
  SKETCH.md            -- the problem + NL proof sketch (math source of truth)
  BLUEPRINT.md         -- this file
  USER_NOTES.md        -- user's special instructions / permitted assumed-axioms
  PROGRESS.md          -- append-only work log (workers write here; see §4)
  TASKS.md             -- append-only delegation log (the Plan agent writes here; see §5)
  REVIEW.md            -- append-only audit log (the Review agent writes here; see §5)
  scripts/
    verify.py          -- the verification harness
    frozen.sha256      -- SHA-256 pins of Defs.lean + Theorems.lean
    ALLOWED_AXIOMS.txt -- axiom allowlist init.py derives from USER_NOTES.md
```

All support declarations live in `namespace Prob27b` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface;
`Solution.lean` re-exposes each as `Prob27b.Solution.<name>` after it is
proven, and `Discharge.lean` machine-checks that each proof has *exactly* the
frozen type (`@Frozen = @Proof := rfl`).

`USER_NOTES.md` says **"None — no assumed axioms"**, so `ALLOWED_AXIOMS.txt` is
empty and the strict policy applies: `{propext, Classical.choice, Quot.sound}`
only, and no `axiom` declaration anywhere in the project.

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.** For each
definition record the Lean rendering and the **MODELING DECISION**.

`Defs.lean` must be **completely proof-complete**: `sorry` is allowed *only* in
`Theorems.lean`, so every instance declared here (including `Ring (RAlg k)`) must
be fully discharged during SETUP. Budget for that — it is the single largest
piece of SETUP work.

---

**§2.1 `RAlg k` — the truncated path algebra with coefficients in `k`.**

```lean
/-- Basis index: 0 = e, 1 = f, 2 = u, 3 = v, 4 = p = uv, 5 = q = vu,
    6 = s = uvu, 7 = w = vuv. -/
structure RAlg (k : Type) [CommRing k] where
  coeff : Fin 8 → k
```

with, for `x y : RAlg k`,

```lean
protected def mul (x y : RAlg k) : RAlg k := ⟨![
  x.coeff 0 * y.coeff 0,
  x.coeff 1 * y.coeff 1,
  x.coeff 0 * y.coeff 2 + x.coeff 2 * y.coeff 1,
  x.coeff 1 * y.coeff 3 + x.coeff 3 * y.coeff 0,
  x.coeff 0 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 4 * y.coeff 0,
  x.coeff 1 * y.coeff 5 + x.coeff 3 * y.coeff 2 + x.coeff 5 * y.coeff 1,
  x.coeff 0 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 4 * y.coeff 2 + x.coeff 6 * y.coeff 1,
  x.coeff 1 * y.coeff 7 + x.coeff 3 * y.coeff 4 + x.coeff 5 * y.coeff 3 + x.coeff 7 * y.coeff 0]⟩
```

`0 = ⟨![0,0,0,0,0,0,0,0]⟩`, `1 = ⟨![1,1,0,0,0,0,0,0]⟩` (i.e. `1 = e + f`),
`add`/`neg`/`smul` componentwise.

*Derivation of the table (do not re-derive it — this is the frozen convention).*
Paths are written **left to right**: `u : e → f`, `v : f → e`, and `x·y` is the
concatenation "first `x`, then `y`", zero when `end x ≠ start y` or when the
length reaches 4. Hence `e·u = u`, `u·e = 0`, `u·v = p`, `v·u = q`, `u·q = s`,
`p·u = s`, `v·p = w`, `q·v = w`, `s·f = s`, `w·e = w`, and every product of total
length ≥ 4 is `0`. Reading off the coefficient of each basis path in `x·y` gives
exactly the eight lines above.

> **MODELING DECISION (RAlg).** `R`, `A`, `B` are the *same* structure-constant
> algebra over three different coefficient rings, so `RAlg` is parametrised by a
> `CommRing k` and instantiated three times. Rejected alternatives:
> (i) three unrelated hand-written types — triples the ring-axiom work and makes
> the coefficientwise maps `iota`/`redPi` impossible to state uniformly;
> (ii) `Algebra.TensorProduct D R` for `A` — mathematically the definition in the
> sketch, but tensor products give no computable basis, no `decide`, and a
> painful `Ring` instance; the isomorphism `D ⊗_{𝔽₂} R ≅ RAlg D` is exactly the
> statement that `RAlg` is defined by structure constants, and `A_isFreeOfRankEight`
> is the frozen theorem that pins the free-module content of that identification;
> (iii) a subalgebra of `Matrix (Fin 2) (Fin 2) (k[t]/(t⁴))` — gets associativity
> for free but requires a quotient ring and closure proofs, a net loss;
> (iv) `def RAlg k := Fin 8 → k` (no `structure` wrapper) — **rejected outright**:
> instance search would unfold the `def` and pick up `Pi.ring`'s *componentwise*
> multiplication, silently giving the wrong ring.
> Consequences later stages must respect: `RAlg k` is **not** commutative, has
> zero divisors, and its unit is `e + f` (so `RAlg.e ≠ 1`).

**§2.2 Instances on `RAlg k`.** `AddCommGroup`, `Ring`, `Module k`, `Algebra k`,
plus `DecidableEq` and `Fintype` (the latter two used for the 256-case `decide`).

```lean
@[ext] theorem RAlg.ext {x y : RAlg k} (h : ∀ i, x.coeff i = y.coeff i) : x = y
def RAlg.equivFun : RAlg k ≃ (Fin 8 → k) := ⟨RAlg.coeff, RAlg.mk, fun _ => rfl, fun _ => rfl⟩
instance [DecidableEq k] : DecidableEq (RAlg k) :=
  fun x y => decidable_of_iff (x.coeff = y.coeff) ⟨fun h => by ext i; rw [h], fun h => by rw [h]⟩
instance [Fintype k] [DecidableEq k] : Fintype (RAlg k) := Fintype.ofEquiv _ RAlg.equivFun.symm
```

Every `Ring` field is discharged by `ext i; fin_cases i <;> simp [RAlg.mul, …] <;> ring`.
`mul_assoc` is the only laborious one (eight polynomial identities in 24
variables; each closes by `ring`). `Algebra k (RAlg k)` sends `c ↦ c • 1`; it is
central because scalars act componentwise.

> **MODELING DECISION (instances).** `DecidableEq` and `Fintype` must be the
> **computable** instances above. Never use `Classical.decEq` or
> `Classical.dec`: kernel `decide` will not reduce through them and Stage B dies.

**§2.3 Basis elements and `single`.**

```lean
def RAlg.single (i : Fin 8) (c : k) : RAlg k := ⟨fun j => if j = i then c else 0⟩
def RAlg.e : RAlg k := RAlg.single 0 1      -- likewise f, u, v, p, q, s, w at 1..7
```

`k` is **implicit** on `RAlg.e … RAlg.w`, so `(RAlg.e : R)`, `(RAlg.e : A)` and
`(RAlg.e : B)` all elaborate; this is what lets one name denote "the same" basis
element over `𝔽₂`, `D` and `K`.

**§2.4 Functoriality.**

```lean
def RAlg.map (φ : k →+* l) : RAlg k →+* RAlg l   -- ⟨fun i => φ (x.coeff i)⟩, componentwise
```

with the ring-hom fields proved componentwise (`φ` is multiplicative and additive
and the structure constants are `0`/`1`, so each of the eight lines is immediate).

> **MODELING DECISION (map).** `RAlg.map` is a `RingHom`, not merely a function:
> `iota` and `redPi` must transport products, and `Polynomial.map` requires a
> `RingHom`.

**§2.5 The arithmetic setting.**

```lean
abbrev D : Type := Polynomial (ZMod 2)      -- 𝔽₂[π]
abbrev K : Type := RatFunc (ZMod 2)         -- 𝔽₂(π)
noncomputable def pi : D := Polynomial.X
abbrev R : Type := RAlg (ZMod 2)
abbrev A : Type := RAlg D
abbrev B : Type := RAlg K
noncomputable def iota  : A →+* B := RAlg.map (algebraMap D K)
noncomputable def redPi : A →+* R := RAlg.map (Polynomial.evalRingHom 0)
noncomputable def invPi : K := (algebraMap D K pi)⁻¹
```

> **MODELING DECISION (setting).** `D`, `K`, `R`, `A`, `B` are `abbrev`s, so every
> Mathlib instance on `Polynomial (ZMod 2)`, `RatFunc (ZMod 2)` and `RAlg _`
> applies without re-declaration. `K` is Mathlib's genuine field of rational
> functions (`IsFractionRing D K` holds), **not** a localization hand-rolled for
> convenience; `B` is the *fraction algebra* `K ⊗_D A`, and the frozen theorem
> `B_fraction_algebra` pins that down so `B` cannot silently be replaced by `A`.
> `redPi` is reduction mod `π`: `Polynomial.evalRingHom 0 : D →+* ZMod 2` has
> kernel `(π)`, and `redPi` realises the sketch's `A/πA ≅ R` without needing
> two-sided-ideal quotients (Mathlib's `Ideal.Quotient` ring structure needs a
> commutative ring, and `A` is noncommutative) — the isomorphism is frozen instead
> as the pair `redPi_surjective` + `redPi_eq_zero_iff`.

**§2.6 The polynomials.**

```lean
noncomputable def F : Polynomial R :=
  Polynomial.monomial 2 RAlg.u + Polynomial.monomial 3 RAlg.e
  + Polynomial.monomial 4 (RAlg.e + RAlg.u)
  + Polynomial.monomial 5 RAlg.e + Polynomial.monomial 6 RAlg.e
noncomputable def Ftilde : Polynomial A := <the same five monomials, coefficients in A>
noncomputable def P : Polynomial B := invPi • (Ftilde.map iota)
noncomputable def a0 : A := RAlg.u + RAlg.v
```

> **MODELING DECISION (polynomials).** Built with `Polynomial.monomial n c`, not
> `C c * X ^ n`. `Polynomial.eval` is `p.sum fun n c => c * x ^ n` — coefficients
> multiply on the **left**, which is exactly the sketch's convention
> `F(r) = u r² + e r³ + …` and exactly what "right null polynomial" means. Over a
> noncommutative coefficient ring `Polynomial.eval_mul` and `eval_C_mul` are
> unavailable/false, but `Polynomial.eval_monomial : (monomial n c).eval x = c * x ^ n`
> holds for any semiring — so the monomial form is the one that computes.
> `Ftilde` is the literal lift of `F` (each `𝔽₂`-coefficient `1` replaced by
> `1 : D`), and `P = F̃/π` is rendered as the `K`-scalar multiple `invPi • …`
> rather than as a division in some ad-hoc quotient.

**§2.7 The two predicates.**

```lean
def IsNullPoly (p : Polynomial R) : Prop := ∀ r : R, p.eval r = 0
def IsIntegerValued (p : Polynomial B) : Prop := ∀ x : A, p.eval (iota x) ∈ Set.range iota
```

> **MODELING DECISION (predicates).** `IsNullPoly` is the sketch's `K(R)`, the set
> of **right null polynomials**: `∀ r`, unrestricted, with `eval` as above.
> `IsIntegerValued` is the textbook `Int(A) = {P ∈ B[X] : P(a) ∈ A for all a ∈ A}`:
> the polynomial lives in `B[X]` (coefficients may have `π` in the denominator),
> `x` ranges over **all** of `A`, and "lands in `A`" is membership in
> `Set.range iota` — with `iota_injective` frozen so that this really is a copy
> of `A` inside `B`.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook
> notion**, quantified exactly as the source states it. Do not weaken the `∀ r : R`
> in `IsNullPoly` or the `∀ x : A` in `IsIntegerValued` to a finite family, a
> subalgebra, or the basis elements. Do not define `IsIntegerValued` on
> `Polynomial A` (that would make `P` unrepresentable and the whole result
> vacuous). Do not replace `Set.range iota` by "some element of `B`" or by a
> divisibility side condition. Do not make `RAlg` commutative, and do not let the
> `Fintype`/`DecidableEq` instances become classical. A "simplification" here can
> make the headline vacuous.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each statement must render a claim of
`SKETCH.md` **faithfully and minimally**, carry a **stable, binding name**, and
the list must include the **headline**. The seventeen frozen names, in the order
the stages prove them (this is also the order in `scripts/harness.json`):

| # | Frozen name | Statement (schematically) | Sketch step |
| - | ----------- | ------------------------- | ----------- |
| 1 | `R_card_eq` | `Nat.card R = 2 ^ 8` | Step 1 ("size `2⁸`") |
| 2 | `R_not_commutative` | `∃ x y : R, x * y ≠ y * x` | Step 1 ("noncommutative") |
| 3 | `F_isNullPoly` | `IsNullPoly F` | Step 2 |
| 4 | `Fe_eval_ne_zero` | `(F * Polynomial.C (RAlg.e : R)).eval ((RAlg.u : R) + RAlg.v) ≠ 0` | Step 3 |
| 5 | `nullPoly_not_rightIdeal` | `∃ (p : Polynomial R) (c : R), IsNullPoly p ∧ ¬ IsNullPoly (p * Polynomial.C c)` | Step 3 conclusion |
| 6 | `D_hasFiniteResidueRings` | `∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)` | preamble + Step 4 |
| 7 | `A_isFreeOfRankEight` | `Nonempty (Basis (Fin 8) D A)` | Step 4 ("finite free over `D`") |
| 8 | `A_torsionFree` | `NoZeroSMulDivisors D A` | Step 4 ("torsion-free") |
| 9 | `iota_injective` | `Function.Injective iota` | Step 4 (`A ↪ B`) |
| 10 | `B_fraction_algebra` | `∀ b : B, ∃ (x : A) (d : D), d ≠ 0 ∧ (algebraMap D K d) • b = iota x` | Step 4 (`B = K ⊗_D A`) |
| 11 | `redPi_surjective` | `Function.Surjective redPi` | Step 4 (`A/πA ≅ R`) |
| 12 | `redPi_eq_zero_iff` | `∀ x : A, redPi x = 0 ↔ ∃ y : A, x = pi • y` | Step 4 (`A/πA ≅ R`) |
| 13 | `Ftilde_eval_mem_pi` | `∀ x : A, ∃ y : A, Ftilde.eval x = pi • y` | Step 4 (`F̃(a) ∈ πA`) |
| 14 | `P_integerValued` | `IsIntegerValued P` | Step 4 (`P ∈ Int(A)`) |
| 15 | `constE_integerValued` | `IsIntegerValued (Polynomial.C (iota (RAlg.e : A)))` | Step 4 (`e ∈ Int(A)`) |
| 16 | `Pe_not_integerValued` | `¬ IsIntegerValued (P * Polynomial.C (iota (RAlg.e : A)))` | Step 5 |
| 17 | `prob27b_counterexample` | the headline conjunction below | Conclusion |

The headline, verbatim in shape:

```lean
theorem prob27b_counterexample :
    (∀ I : Ideal D, I ≠ ⊥ → Finite (D ⧸ I)) ∧
    Nonempty (Basis (Fin 8) D A) ∧
    NoZeroSMulDivisors D A ∧
    (∃ p q : Polynomial B,
        IsIntegerValued p ∧ IsIntegerValued q ∧ ¬ IsIntegerValued (p * q)) := sorry
```

**Why these seventeen.** The *decidable heart* is 3 and 4: `F_isNullPoly` is a
`∀` over the 256 elements of `R` and `Fe_eval_ne_zero` is a single evaluation —
between them they say precisely "`F ∈ K(R)`, `Fe ∉ K(R)`". Item 5 is the
milestone they combine into. Items 1–2 are **faithfulness guardrails** for Step 1:
if the multiplication table were mistyped into something commutative or
degenerate, they would fail, and without them a broken `R` could still make
3–5 accidentally true. Items 6–12 are the *setting* — 6 is what makes this a
counterexample to Problem 27(b) at all (the conjecture assumes finite residue
rings), 7–8 are the sketch's own list of properties of `A`, and 9–12 are the
structural facts (`A ↪ B`, `B = K ⊗_D A`, `A/πA ≅ R`) that make `Int(A)` the
textbook object rather than a convenient surrogate. Item 13 is the transport of
the heart across `redPi`; 14–16 are Steps 4–5 verbatim; 17 is the payoff and is
the only theorem a reader needs to cite.

**Re-build gate.** After freezing, `lake build` must succeed (everything is
`sorry`, but the *statements* must typecheck). Do not write a line of proof until
the skeleton compiles. Record the SHA-256 of `Defs.lean` and `Theorems.lean`
into `scripts/frozen.sha256`, then log a PROGRESS entry: "SETUP frozen, skeleton
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

| Need                                                | Mathlib handle                                                                 |
| --------------------------------------------------- | ------------------------------------------------------------------------------ |
| the field `𝔽₂`                                      | `ZMod 2` (`Field`, `Fintype`, computable `DecidableEq`)                        |
| `D = 𝔽₂[π]`                                         | `Polynomial (ZMod 2)`, `Polynomial.X`                                          |
| `K = 𝔽₂(π)` and `D ↪ K`                             | `RatFunc (ZMod 2)`, `IsFractionRing D K`, `algebraMap D K` (injective)          |
| polynomial ring over a **noncommutative** coefficient ring | `Polynomial R` for `[Semiring R]` (`AddMonoidAlgebra R ℕ`, `X` central)  |
| evaluation with left coefficients                   | `Polynomial.eval` / `eval₂`, `Polynomial.eval_monomial`, `Polynomial.eval_add`  |
| right multiplication by a constant                  | `Polynomial.coeff_mul_C`, `Polynomial.map_mul`, `Polynomial.map_C`              |
| pushing coefficients along a ring hom               | `Polynomial.map`, `Polynomial.eval₂_at_apply` / `Polynomial.eval_map`           |
| `𝔽₂[X]` is a PID                                    | `EuclideanDomain` ⇒ `IsPrincipalIdealRing`, `Submodule.IsPrincipal.span_singleton_generator` |
| finiteness of `𝔽₂[X]/(g)`                           | `AdjoinRoot.powerBasis`, `Ideal.quotEquivOfEq`, `FiniteDimensional.fintypeOfFintype` (or `Module.finite_of_finite`) |
| `X ∣ p ↔ p(0) = 0`                                  | `Polynomial.X_dvd_iff`, `Polynomial.coeff_zero_eq_eval_zero`                    |
| clearing a common denominator over a finite family  | `IsLocalization.exist_integer_multiples`, `IsLocalization.IsInteger`            |
| free module of rank 8 / a basis                     | `Pi.basisFun`, `Basis.map`, `LinearEquiv.ofBijective`                           |
| torsion-freeness                                    | `NoZeroSMulDivisors`, `Function.Injective.noZeroSMulDivisors`                   |
| the 256-case check                                  | `Fintype`/`DecidableEq` on `Fin 8 → ZMod 2`, kernel `decide`, `Fintype.decidableForallFintype` |
| `Fin 8` vectors and case splitting                  | `Matrix.cons` notation `![…]`, `Fin.cases`, `fin_cases`, `Matrix.cons_val_*` simp set |
| scalars on polynomials                              | `Polynomial.module` (`Module K (Polynomial B)` from `Module K B`)               |

**The two nontrivial dependencies the whole proof hinges on** are (i) `RatFunc`
together with `IsFractionRing D K` — everything about "denominator `π`" is read
off `algebraMap D K` being injective and `X` not being a unit in `D`; and (ii)
`Polynomial.eval_monomial`, the one evaluation lemma that survives
noncommutativity.

**Machinery you can avoid.** No `TensorProduct`: `A = D ⊗_{𝔽₂} R` is realised as
`RAlg D` and the tensor content is captured by `A_isFreeOfRankEight`. No
`Ideal.Quotient` on the noncommutative `A`: `A/πA ≅ R` is captured by
`redPi_surjective` + `redPi_eq_zero_iff`. No quiver / path-algebra library
(Mathlib has `Quiver.Path` but no path *algebra* ring): structure constants
instead. No `Polynomial.aeval` (it needs commutativity).

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #   | Object                                | Role                                                                 |
| --- | ------------------------------------- | -------------------------------------------------------------------- |
| D1  | `RAlg (k) : Type` (structure, `coeff : Fin 8 → k`) | the truncated path algebra with coefficients in `k`     |
| D2  | `RAlg.mul/one/zero/add/neg/smul`      | the frozen structure-constant table (§2.1)                            |
| D3  | `Ring`, `Module k`, `Algebra k`, `DecidableEq`, `Fintype` instances | make `RAlg k` a genuine noncommutative `k`-algebra, computably |
| D4  | `RAlg.ext`, `RAlg.equivFun`           | componentwise extensionality; the `Fin 8 → k` coordinate equivalence  |
| D5  | `RAlg.single i c`                     | the element with coefficient `c` in slot `i`                          |
| D6  | `RAlg.e/f/u/v/p/q/s/w`                | the eight basis paths (`k` implicit, so they live over `𝔽₂`, `D`, `K`) |
| D7  | `RAlg.map (φ : k →+* l)`              | coefficientwise functoriality, as a `RingHom`                         |
| D8  | `D`, `K`, `pi`                        | `𝔽₂[π]`, `𝔽₂(π)`, the uniformiser `π = X`                            |
| D9  | `R`, `A`, `B`                         | `RAlg (ZMod 2)`, `RAlg D`, `RAlg K`                                   |
| D10 | `iota : A →+* B`                      | the embedding `A ↪ K ⊗_D A`                                           |
| D11 | `redPi : A →+* R`                     | reduction mod `π`, realising `A/πA ≅ R`                               |
| D12 | `invPi : K`                           | `1/π`, the scalar that turns `F̃` into `P`                            |
| D13 | `F : Polynomial R`                    | `uX² + eX³ + (e+u)X⁴ + eX⁵ + eX⁶` (Step 2)                            |
| D14 | `Ftilde : Polynomial A`               | the lift of `F` to `A[X]` (Step 4)                                    |
| D15 | `P : Polynomial B`                    | `invPi • (Ftilde.map iota)` = `F̃/π` (Step 4)                         |
| D16 | `a0 : A`                              | the witness `u + v` at which `Pe` fails to be integral (Step 5)       |
| D17 | `IsNullPoly`                          | the set `K(R)` of right null polynomials of `R`                       |
| D18 | `IsIntegerValued`                     | membership in `Int(A) ⊆ B[X]`                                         |

---

## Part 2 — Theorems and lemmas to prove (in order)

### Stage A — the algebra `RAlg` and the finite ring `R` (`Proofs/StageA/`)

Goal: the reusable multiplication API for `RAlg k`, the explicit products the
later stages need, and the two Step 1 guardrail theorems `R_card_eq` and
`R_not_commutative`.

**A1 — `RAlg.coeff_mul`.** `(x * y).coeff i = <the i-th line of §2.1>`, as eight
`@[simp]` lemmas (`coeff_mul_zero`, …, `coeff_mul_seven`) or one lemma plus
`fin_cases`. Everything downstream is `simp [RAlg.coeff_mul_*]`.

**A2 — `RAlg.single_mul_single`.** `single i c * single j d = single (i*j) (c*d)`
when the paths compose, `= 0` otherwise. Simplest honest route: prove the
sixteen basis products the proof actually uses as separate `@[simp]` lemmas —
`e_mul_e = e`, `e_mul_f = 0`, `e_mul_u = u`, `u_mul_e = 0`, `u_mul_f = u`,
`u_mul_u = 0`, `u_mul_v = p`, `v_mul_u = q`, `u_mul_q = s`, `p_mul_u = s`,
`v_mul_p = w`, `q_mul_v = w`, `u_mul_p = 0`, `u_mul_w = 0`, `v_mul_q = 0`,
`s_mul_v = 0` — each by `ext i; fin_cases i <;> simp [RAlg.single, RAlg.mul]`.
Also `one_eq_e_add_f : (1 : RAlg k) = RAlg.e + RAlg.f`.

**A3 — `a0_pow`.** Over any `k`: `(RAlg.u + RAlg.v) ^ 2 = RAlg.p + RAlg.q`,
`(RAlg.u + RAlg.v) ^ 3 = RAlg.s + RAlg.w`, `(RAlg.u + RAlg.v) ^ 4 = 0`. Prove
generically in `k` (they hold over `ℤ` already), so both `R` and `A` get them.
Then `e_mul_a0_cubed : RAlg.e * (RAlg.u + RAlg.v) ^ 3 = RAlg.s`.

**A4 — `R_card_eq`.** `Nat.card R = 2 ^ 8`. Via `RAlg.equivFun`:
`Nat.card_congr`, `Nat.card_fun`/`Fintype.card_fun`, `ZMod.card`. (`Nat.card` is
used rather than `Fintype.card` so the statement does not depend on which
`Fintype` instance is in scope.)

**A5 — `R_not_commutative`.** Witnesses `RAlg.u`, `RAlg.v`: `u*v = p`, `v*u = q`,
and `p ≠ q` because their 4th coefficients differ (`1 ≠ 0` in `ZMod 2`). `decide`
also closes it.

**A6 — `RAlg.map` computation lemmas.** `RAlg.map φ (single i c) = single i (φ c)`,
hence `RAlg.map φ RAlg.e = RAlg.e` and likewise for the other seven basis
elements. Needed by Stages D and E.

> **Cheat watch (Stage A).** The multiplication table is the whole problem: a
> transposed convention (`u·v` vs `v·u`) yields a *different* algebra in which `F`
> is **not** null, so a later stage would be proving a false statement and would
> stall — do not "fix" it by editing `Defs.lean` (frozen) or by adjusting `F`.
> Confirm the convention with guardrail `example`s **before** anything else:
> `example : (RAlg.u : R) * RAlg.v = RAlg.p := by decide`,
> `example : (RAlg.u : R) * RAlg.e = 0 := by decide`,
> `example : (RAlg.e : R) * RAlg.u = RAlg.u := by decide`,
> `example : (RAlg.u : R) * RAlg.q = RAlg.s := by decide`,
> `example : ((RAlg.u : R) + RAlg.v) ^ 4 = 0 := by decide`,
> `example : (1 : R) ≠ RAlg.e := by decide`,
> `example : (RAlg.s : R) ≠ 0 := by decide`.
> Do **not** prove `R_not_commutative` by exhibiting a pair in some *other*
> algebra, and do not prove `R_card_eq` by re-defining `R`. Do not add
> `[CommRing]`-flavoured `simp` lemmas (`mul_comm` on `RAlg`) — they are false.
> Requires a clean `#print axioms` for A4 and A5.

### Stage B — `F` is a null polynomial on `R` (`Proofs/StageB/`) · **MILESTONE (heart)**

Goal: the frozen theorem `F_isNullPoly : ∀ r : R, F.eval r = 0` — Step 2.

**B1 — `F_eval`.** `F.eval r = RAlg.u * r ^ 2 + RAlg.e * r ^ 3
+ (RAlg.e + RAlg.u) * r ^ 4 + RAlg.e * r ^ 5 + RAlg.e * r ^ 6`, by
`simp [F, Polynomial.eval_add, Polynomial.eval_monomial]`. **Only**
`eval_monomial`/`eval_add` may be used — `eval_mul`, `eval_C_mul` and `eval_pow`
need a commutative coefficient ring and are not available.

**B2 — `F_isNullPoly` (primary route).** `intro r; rw [F_eval]; revert r; decide`.
`R` is a 256-element computable `Fintype` with computable `DecidableEq`, and each
case is five products of 8-vectors over `ZMod 2`; this is well within the kernel's
budget. If `decide` is too slow, raise `maxRecDepth`/`maxHeartbeats` first.

**B2′ — fallback route (structural, if `decide` stalls).** Write
`r.coeff 0 = α`, `r.coeff 1 = β` and case on `α, β ∈ ZMod 2` (`Fin.cases` /
`omega` / `decide` on the two-element type). In each of the four cases prove the
sketch's identity `RAlg.e * (r^3 + r^4 + r^5 + r^6) = RAlg.u * (r^2 + r^4)`
componentwise with `RAlg.coeff_mul` + `ring` + `ZMod.pow_card`-style `x^2 = x`
(`ZMod 2`: `sq` is the identity). Both sides equal `(r.coeff 2 * r.coeff 3) • s`
when `(α,β) ∈ {(0,0),(1,1)}` and vanish when `(α,β) ∈ {(1,0),(0,1)}`; char 2 then
gives `F.eval r = 0`. This is the sketch's own argument — it is a genuine
exhaustive case split over **all** `r`, not a sample.

> **Cheat watch (Stage B).** `native_decide` is **BANNED** — it would add
> `Lean.ofReduceBool` to `#print axioms`. Do not prove `F_isNullPoly` only for
> the basis elements, only for `r` of the four displayed shapes, or only for
> `r = a0`: the frozen statement is `∀ r : R` and downstream `Ftilde_eval_mem_pi`
> instantiates it at `redPi x` for an *arbitrary* `x : A`, so any restriction
> breaks the assembly. Do not weaken `F.eval r = 0` to "`F.eval r` is nilpotent"
> or "`F.eval r ∈ Jacobson radical`". Do not silently change `F` (it is frozen);
> in particular the `X⁴` coefficient is `e + u`, not `e` or `u`.
> Guardrails: `example : F.eval (RAlg.u + RAlg.v) = 0 := by decide` (after `B1`),
> and `example : F ≠ 0 := by …` so the milestone is not vacuous.
> Requires a clean `#print axioms Prob27b.F_isNullPoly`.

### Stage C — `K(R)` is not a right ideal of `R[X]` (`Proofs/StageC/`) · **MILESTONE**

Goal: the frozen theorems `Fe_eval_ne_zero` and `nullPoly_not_rightIdeal` —
Step 3. Depends on Stages A and B.

**C1 — `Fe_coeff`.** `(F * Polynomial.C (RAlg.e : R)).coeff n = F.coeff n * RAlg.e`
by `Polynomial.coeff_mul_C`, hence
`F * C RAlg.e = monomial 3 RAlg.e + monomial 4 RAlg.e + monomial 5 RAlg.e + monomial 6 RAlg.e`
(the `X²` coefficient dies because `u * e = 0`, and `(e+u) * e = e`). Prove it by
`Polynomial.ext` + `coeff_mul_C` + `Polynomial.coeff_monomial`, using A2.

**C2 — `Fe_eval_ne_zero`.** With C1 and `eval_monomial`,
`(F * C RAlg.e).eval (RAlg.u + RAlg.v) = RAlg.e * (a^3 + a^4 + a^5 + a^6)` with
`a = u+v`; by A3 `a^4 = a^5 = a^6 = 0` and `a^3 = s + w`, so the value is
`e * (s + w) = s ≠ 0`. Finish with `decide` on `(RAlg.s : R) ≠ 0`.

**C3 — `nullPoly_not_rightIdeal`.** `⟨F, RAlg.e, F_isNullPoly, fun h => Fe_eval_ne_zero (h _)⟩`.

> **Cheat watch (Stage C).** The **fatal** shortcut here is
> `(p * C c).eval x = p.eval x * c` — **false** over a noncommutative coefficient
> ring, and it is exactly the step the sketch is careful about (`ue = 0` but
> `eu ≠ 0`). Multiply the *coefficients* on the right first (C1), then evaluate.
> Equally: do not use `Polynomial.eval_mul`/`Polynomial.eval_geom_series`/`aeval`
> — none apply. Do not weaken `nullPoly_not_rightIdeal` to "`K(R)` is not a
> two-sided ideal" or to "`K(R)` is not closed under multiplication"; the claim
> is failure of **right** ideal-ness, witnessed by a right multiple by a
> **constant** polynomial. Do not replace the witness `u + v` by a basis element
> (every basis element gives `0`, so the statement would be unprovable, not
> merely weaker). Guardrail: `example : (F * Polynomial.C (RAlg.e : R)).coeff 2 = 0 := by decide`.
> Requires a clean `#print axioms` for both frozen names.

### Stage D — the arithmetic setting `D`, `A`, `B`, `redPi` (`Proofs/StageD/`)

Goal: the six frozen theorems 6–12 that certify the setting is the one Problem
27(b) is about. Independent of Stages B and C — run it in parallel with them.

**D1 — `D_hasFiniteResidueRings`.** `𝔽₂[X]` is a `EuclideanDomain`, hence a
`IsPrincipalIdealRing`; take `g = Submodule.IsPrincipal.generator I`, so
`I = Ideal.span {g}` and `g ≠ 0` (else `I = ⊥`). Transport along
`Ideal.quotEquivOfEq` to `AdjoinRoot g`, get `AdjoinRoot.powerBasis (hg : g ≠ 0)`
(needs `Field (ZMod 2)` ✓), which gives a finite `ZMod 2`-basis; conclude with
`FiniteDimensional.fintypeOfFintype` (or `Module.finite_of_finite`) plus
`Finite.of_equiv`.

**D2 — `A_isFreeOfRankEight`.** `Nonempty (Basis (Fin 8) D A)`: `RAlg.equivFun`
is `D`-linear, so `(Pi.basisFun D (Fin 8)).map equivFunₗ.symm` is the basis.
State/derive the linear-equiv version `RAlg.equivFunₗ : RAlg k ≃ₗ[k] (Fin 8 → k)`
as a support def in `Proofs/StageD/`.

**D3 — `A_torsionFree`.** `NoZeroSMulDivisors D A`: `d • x = 0` iff
`d * x.coeff i = 0` for all `i`; `D` is a domain, so `d ≠ 0` forces every
coefficient to vanish. Or transport through `RAlg.equivFunₗ` with
`Function.Injective.noZeroSMulDivisors`.

**D4 — `iota_injective`.** `algebraMap D K` is injective
(`IsFractionRing.injective` / `NoZeroDivisors` + `IsLocalization`), and `RAlg.map`
of an injective map is injective componentwise (use `RAlg.ext`).

**D5 — `B_fraction_algebra`.** For `b : B`, apply
`IsLocalization.exist_integer_multiples (nonZeroDivisors D) Finset.univ b.coeff`
to get one `d` in the non-zero-divisor submonoid with
`IsLocalization.IsInteger D (algebraMap D K d * b.coeff i)` for every `i`; assemble
`x : A` from the integer preimages and note `d ≠ 0` in a domain. (Alternative:
`d = ∏ i, (b.coeff i).denom` with `RatFunc.num_div_denom`.)

**D6 — `redPi_surjective`.** `Polynomial.evalRingHom 0 : D →+* ZMod 2` is
surjective (`Polynomial.C` is a section: `eval 0 (C c) = c`), and `RAlg.map` of a
surjective map is surjective componentwise.

**D7 — `redPi_eq_zero_iff`.** `redPi x = 0 ↔ ∀ i, (x.coeff i).eval 0 = 0`
(by `RAlg.ext` and `RAlg.map`) `↔ ∀ i, Polynomial.X ∣ x.coeff i` (by
`Polynomial.coeff_zero_eq_eval_zero` and `Polynomial.X_dvd_iff`) `↔ ∃ y : A, x = pi • y`
(choose the quotients componentwise; the reverse direction is immediate).
Together D6+D7 are the sketch's `A/πA ≅ R`.

> **Cheat watch (Stage D).** `D_hasFiniteResidueRings` is what makes this a
> counterexample to Problem 27(b) *at all* — do not weaken it to "for `I` maximal",
> "for `I = (π)`", or "for `I` generated by a monic polynomial"; the frozen `∀ I ≠ ⊥`
> is the textbook "has finite residue rings". `redPi_eq_zero_iff` is an **iff**:
> proving only `⇐` (the trivial direction) is a silent weakening that would make
> Stage E unprovable. `B_fraction_algebra` must produce a **single** `d` valid for
> the whole element, not one per coefficient, and must assert `d ≠ 0`. Do not
> prove `A_torsionFree` by adding a hypothesis, and do not replace
> `Nonempty (Basis (Fin 8) D A)` by `Module.Free D A` alone (that drops the rank,
> which is the sketch's "finite free"). Guardrail:
> `example : redPi (RAlg.s : A) = (RAlg.s : R) := by …` and
> `example : ¬ (∃ y : A, (RAlg.s : A) = pi • y) := by …` (the Step-5 divisibility
> fact, in its `A`-side form).
> Requires a clean `#print axioms` for all six/seven frozen names.

### Stage E — lifting `F` to `A`; `P ∈ Int(A)` (`Proofs/StageE/`)

Goal: frozen theorems `Ftilde_eval_mem_pi`, `P_integerValued`,
`constE_integerValued` — Step 4. Depends on Stages A, B, D.

**E1 — `Ftilde_map_redPi`.** `Ftilde.map redPi = F`: `Polynomial.map` of a
monomial is a monomial (`Polynomial.map_monomial`) and `redPi` sends each `A`-side
basis element to the corresponding `R`-side one (A6).

**E2 — `eval_map_hom`.** For a `RingHom φ : S →+* T` and `p : Polynomial S`,
`(p.map φ).eval (φ x) = φ (p.eval x)`. Use `Polynomial.eval₂_at_apply` /
`Polynomial.eval_map` if available for noncommutative `S`, `T`; otherwise prove it
directly by `Polynomial.induction_on'` (additive case + `map_monomial`, using
`φ (c * x^n) = φ c * φ x ^ n`).

**E3 — `Ftilde_eval_mem_pi`.** For `x : A`,
`redPi (Ftilde.eval x) = (Ftilde.map redPi).eval (redPi x) = F.eval (redPi x) = 0`
by E2, E1, `F_isNullPoly`; then `redPi_eq_zero_iff` gives `y : A` with
`Ftilde.eval x = pi • y`.

**E4 — `eval_smul`.** `((c : K) • p).eval x = c • p.eval x` for `p : Polynomial B`:
`Polynomial.smul_eq_C_mul` is unavailable (needs central `C c`), so prove it by
`Polynomial.induction_on'` using `smul_mul_assoc` (legitimate: `K` is central in
the `K`-algebra `B`).

**E5 — `P_integerValued`.** For `x : A`:
`P.eval (iota x) = invPi • (Ftilde.map iota).eval (iota x) = invPi • iota (Ftilde.eval x)`
(E4, E2) `= invPi • iota (pi • y) = invPi • ((algebraMap D K pi) • iota y) = iota y`
using `invPi * algebraMap D K pi = 1`, which needs `algebraMap D K pi ≠ 0`
(injectivity of `algebraMap` + `Polynomial.X_ne_zero`). So the value is in
`Set.range iota`.

**E6 — `constE_integerValued`.** `(Polynomial.C b).eval x = b` (`Polynomial.eval_C`),
so the value is `iota RAlg.e ∈ Set.range iota` — immediate. Keep it honest: it is
the *constant* polynomial with coefficient `iota RAlg.e`, matching "the constant
polynomial `e` also belongs to `Int(A)`".

> **Cheat watch (Stage E).** Do not prove `P_integerValued` by shrinking the
> quantifier (it is `∀ x : A`, not `∀ x ∈ span of basis`). Do not "prove" it by
> redefining `P` without the `invPi` factor — a `P` with coefficients already in
> `A` is trivially integer-valued and makes Step 5 false, gutting the
> counterexample; `P` is frozen, check with
> `example : P.coeff 3 ≠ iota (RAlg.e : A) := by …`. Do not invoke
> `Polynomial.eval_mul`/`aeval`/`Polynomial.evalRingHom` on `Polynomial B`
> (noncommutative). `invPi • iota (pi • y) = iota y` must be *derived* from
> `invPi * algebraMap D K pi = 1`, not assumed — and that in turn needs `π ≠ 0`
> in `K`, which is where `iota_injective` earns its keep.
> Requires a clean `#print axioms` for all three frozen names.

### Stage F — `P·e ∉ Int(A)`; the headline (`Proofs/StageF/`) · **HEADLINE**

Goal: frozen theorems `Pe_not_integerValued` and `prob27b_counterexample` —
Step 5 and the Conclusion. Depends on every earlier stage.

**F1 — `Pe_eq`.** `P * Polynomial.C (iota RAlg.e) = invPi • ((Ftilde * Polynomial.C RAlg.e).map iota)`,
by `Polynomial.ext` + `Polynomial.coeff_mul_C` + `Polynomial.coeff_smul` +
`Polynomial.coeff_map` and `iota` being a ring hom.

**F2 — `Ftilde_e_eval_a0`.** `(Ftilde * Polynomial.C RAlg.e).eval a0 = (RAlg.s : A)`
— the `A`-side copy of C1+C2, proved the same way from A2/A3 (which were stated
generically in `k`, so they apply verbatim over `D`).

**F3 — `s_div_pi_not_integral`.** `invPi • iota (RAlg.s : A) ∉ Set.range iota`.
If it equalled `iota y`, comparing the 6th coefficient gives
`invPi = algebraMap D K (y.coeff 6)`, hence
`algebraMap D K (y.coeff 6 * pi) = 1 = algebraMap D K 1`, so `y.coeff 6 * pi = 1`
by injectivity, i.e. `X` is a unit in `𝔽₂[X]` — contradiction via
`Polynomial.isUnit_iff` / a `natDegree` count. **This is the sketch's "`s` is not
divisible by `π` because `A` is `D`-free on `e,f,u,v,p,q,s,w`".**

**F4 — `Pe_not_integerValued`.** Instantiate the hypothetical
`IsIntegerValued (P * C (iota RAlg.e))` at `x = a0`; by F1, E4, E2 and F2 the
value is `invPi • iota (RAlg.s : A)`, contradicting F3.

**F5 — `prob27b_counterexample`.** Assemble:
`⟨D_hasFiniteResidueRings, A_isFreeOfRankEight, A_torsionFree,
  P, Polynomial.C (iota RAlg.e), P_integerValued, constE_integerValued,
  Pe_not_integerValued⟩`.

> **Cheat watch (Stage F).** The headline is a **conjunction**: do not drop the
> finite-residue-rings / free / torsion-free conjuncts (they are the conjecture's
> hypotheses — without them the existential is not a counterexample to anything),
> and do not replace the existential's `IsIntegerValued p ∧ IsIntegerValued q ∧ ¬ …`
> by `¬ (IsIntegerValued p ∧ IsIntegerValued q → …)` or by an unwitnessed
> non-membership. Do not prove `Pe_not_integerValued` by claiming a value is
> "clearly not in `A`" — *compute* it (F2) and then *derive* the contradiction from
> `X` not being a unit (F3); "not obviously in the range" is not a proof. Do not
> reorder the product to `C (iota RAlg.e) * P` (left multiplication by `e` gives a
> *different*, integer-valued polynomial — the failure is one-sided, exactly as in
> Stage C). Guardrail: `example : IsIntegerValued (Polynomial.C (iota (RAlg.e : A)) * P) → True := fun _ => trivial`
> is *not* a substitute; instead assert the asymmetry you rely on by keeping F4's
> product in the frozen order.
> Requires a clean `#print axioms Prob27b.prob27b_counterexample`.

### Discharge & Solution (after the frozen theorems are proved)

In `Prob27b/Solution.lean`, restate each frozen theorem **verbatim** in
`namespace Prob27b.Solution` and set it `:= <name>_proof` (the sorry-free
declaration from `Proofs/`). In `Prob27b/Discharge.lean`, for each pair write
`example : @<Frozen> = @<Proof> := rfl` — this compiles **iff** the proof has
*exactly* the frozen proposition (machine-checked no-drift). `verify.py` checks
both modules build and that `#print axioms Prob27b.Solution.<name>` is clean for
every frozen name.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems, skeleton builds, pins recorded)
  · the Ring instance on RAlg is discharged HERE — no sorry outside Theorems.lean
      │
      ▼
Stage A  (mult. table, basis products, a0 powers, R_card_eq, R_not_commutative)
      │
      ├──────────────► Stage B  (F_isNullPoly)            ── MILESTONE (heart)
      │                     │
      │                     ▼
      │                Stage C  (Fe_eval_ne_zero,
      │                          nullPoly_not_rightIdeal) ── MILESTONE (citable)
      │                     │
      └──► Stage D  (D_hasFiniteResidueRings, A_isFreeOfRankEight, A_torsionFree,
           (independent    iota_injective, B_fraction_algebra,
            of B and C)    redPi_surjective, redPi_eq_zero_iff)
                            │
              Stage B ──────┴──────► Stage E  (Ftilde_eval_mem_pi, P_integerValued,
                                               constE_integerValued)
                                          │
                                          ▼
                                     Stage F  ──► HEADLINE  (#print axioms clean)
                                          │        prob27b_counterexample
                                          ▼
                            Discharge.lean + Solution.lean
```

- **Parallelisable:** Stage D is independent of Stages B and C (it only needs
  Stage A's `RAlg.map` lemmas), so B/C and D run concurrently. Within Stage A,
  A1–A3 (the table) and A4–A5 (the guardrail theorems) are independent. Within
  Stage D, D1 (finite residue rings) is independent of D2–D7 and is the natural
  fourth worker.
- **Milestone:** after Stage C a citable result already exists —
  `nullPoly_not_rightIdeal`, i.e. Steps 1–3 of the sketch in full.
- **Hardest engineering:** (1) SETUP's `Ring (RAlg k)` instance, especially
  `mul_assoc` (eight `ring` goals, verified consistent by hand — see §2.1);
  (2) Stage B's kernel `decide` over 256 elements (have the B2′ fallback ready);
  (3) Stage D1's finite-residue-ring chain, which is the only place that touches
  unfamiliar Mathlib API (`AdjoinRoot.powerBasis`, `FiniteDimensional.fintypeOfFintype`).
  Budget effort accordingly; everything else is componentwise bookkeeping.

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them, and append any problem-
specific traps below them.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem must be hypothesis-free wherever the source claim is unconditional.
  Forbidden moves: adding `(h : …)` to a frozen statement; proving a `∀ x`
  (or `∀ x y`) claim only for generators / a finite subset and claiming the
  general case; replacing an equality with a one-sided inclusion. If a sub-proof
  seems to need an assumption, **derive it or restructure** — do not weaken the
  statement. (Downstream stages typically instantiate these at *arbitrary*
  elements, so a quiet weakening breaks the assembly silently.)

- **Keep every predicate the textbook definition — do not soften it.** Quantifiers
  must match the source exactly (e.g. "for all finite families" must not become
  "for `n ≤ 2`" or "for one fixed family"); genuine finite generation /
  exactness / etc. must not be replaced by a cardinality-bounded or
  "I-couldn't-find-it" surrogate. A softened predicate can make the headline
  vacuous.

- **Get the modeling right once, in SETUP, and freeze it.** A dropped or extra
  relation/hypothesis in a frozen definition silently changes the object and can
  break the proof downstream. Validate the core modeling facts (a basis, a
  dimension, a key relation) *before* freezing, with small guardrail `example`s
  that confirm the structure is the intended one (and that "live" relations do
  not secretly collapse distinct nonzero elements to zero, etc.).

- **Discharge ring/structure axioms once — never `sorry` them.** Inherit them
  from Mathlib (quotients, matrices, existing instances) or discharge them by
  `decide` on a finite model. If you feel the urge to `sorry` associativity or
  commutativity, you modeled the object wrong. Use Mathlib's existing `CommRing`/
  module instances rather than hand-rolling multiplication.

- **Keep module-side and ring-side objects distinct.** When a proof bridges two
  kinds of object (an ideal vs a submodule, a ring element vs its image under a
  hom), fix the precise Lean form of each in `Defs.lean` and do not conflate them
  — mixing them up is the most likely *silent* modeling bug.

- **`decide` budget — and `native_decide` is BANNED.** Finite single-element
  identities are kernel-`decide`-able; a doubly-quantified `∀` over a large finite
  type is usually **not** (it can blow up exponentially) — prove those
  structurally and reserve `decide` for the small finite lemma underneath. Only
  `decide` over genuinely **computable** types (e.g. `ZMod n`, `Fin n`,
  `Fin n → ZMod m`); a `noncomputable` model will not reduce. `native_decide`
  adds a compiler-trust axiom and would dirty `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen during proving (pinned in `scripts/frozen.sha256`). If a
  *definition* seems missing, it belongs in a `Proofs/` support file. If a
  *statement* seems wrong, stop and re-read `SKETCH.md` — the frozen statements
  are deliberately the minimal faithful rendering of the sketch, so a mismatch
  means a modeling bug to fix *before* re-freezing, not a hypothesis to bolt on.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no `native_decide`/
  `ofReduceBool` — **plus** any assumed-certificate axioms the user permitted in
  `USER_NOTES.md` (their names are recorded in `scripts/ALLOWED_AXIOMS.txt`). For
  this problem `USER_NOTES.md` says **"None — no assumed axioms"**, so the
  allowlist is exactly the standard three and **no `axiom` declaration may appear
  anywhere in the project**. Any axiom outside that allowlist is banned. This is
  checked per theorem by `verify.py` (checks 2 and 4).

- **Assumed certificates go in as `axiom`s, never as hypotheses.** A fact that is
  routine but prohibitively expensive to prove in Lean (a large factorization, an
  explicit interpolant, a numeric certificate) may be assumed — but ONLY if the
  user described it in `USER_NOTES.md`, and ONLY as a Lean `axiom` declared in
  `Defs.lean` during SETUP (so it shows up in `#print axioms` and is checked
  deterministically). It is then exempt from the axiom ban via
  `scripts/ALLOWED_AXIOMS.txt`. This NEVER relaxes the cardinal rule above:
  certificates are never bolted onto a frozen theorem as a hypothesis `(h : …)`.

**Problem-specific traps.**

- **Path-composition order is the single highest-risk modeling choice.** The
  frozen convention is left-to-right (`u : e → f`, so `e·u = u`, `u·e = 0`,
  `u·v = p`, `v·u = q`). Under the opposite convention the algebra is the
  *opposite ring*, `F` is no longer a right null polynomial, and Stage B is
  literally false. The Stage-A guardrail `example`s exist to catch this in
  minutes rather than after Stage E.

- **Noncommutativity is load-bearing, and the standard `Polynomial` API quietly
  assumes it away.** `Polynomial.eval_mul`, `eval_C_mul`, `eval_pow`, `aeval`,
  `evalRingHom` all need a commutative coefficient ring. The *only* evaluation
  lemmas in play are `eval_monomial`, `eval_add`, `eval_C`, plus the two
  hand-proved bridges `eval_map_hom` (E2) and `eval_smul` (E4). If a proof needs
  `p.eval x * c = (p * C c).eval x`, it is wrong — that identity is precisely
  what fails and is why the counterexample exists.

- **`Int(A)` must live in `B[X]`, not `A[X]`.** `P = F̃/π` has a genuine `π` in
  the denominator. A model where `Int(A) ⊆ A[X]` makes `P` inexpressible and
  makes the whole statement trivially true and mathematically empty. Likewise `B`
  must really be the fraction algebra (`B_fraction_algebra`) and `A` must really
  embed in it (`iota_injective`) — otherwise "`Pe ∉ Int(A)`" could hold for a
  degenerate reason.

- **Do not lose the conjecture's hypotheses.** Problem 27(b) is a *conditional*
  claim ("`Int(A)` is a ring when `D` has finite residue rings"). Refuting it
  requires `D_hasFiniteResidueRings` **and** the failure. A headline that only
  exhibits the failure refutes nothing; that is why the frozen headline is a
  conjunction and why `D_hasFiniteResidueRings`, `A_isFreeOfRankEight`,
  `A_torsionFree` are frozen separately.

- **The failure is one-sided.** `K(R)` fails to be a **right** ideal; `F·e ∉ K(R)`
  while `e·F` is harmless. Keep every product in the frozen order
  (`F * C e`, `P * C (iota e)`), and keep the witness `a = u + v` — no basis
  element or scalar witness works, because `(Fe)(r) = 0` for all `r` with
  `r.coeff 2 * r.coeff 3 = 0`.

- **`1 ≠ e`.** The unit of `R` is `e + f`. Every `simp` call that treats `RAlg.e`
  as the identity, or that rewrites `RAlg.e * x` to `x`, is wrong. `R` is not
  local, not a domain, and not commutative; do not reach for `Ring`-theoretic
  lemmas that assume otherwise.

- **Instances must stay computable.** If `DecidableEq (RAlg k)` or
  `Fintype (RAlg k)` is ever obtained classically (`Classical.decEq`,
  `Fintype.ofFinite`), Stage B's `decide` silently stops reducing and agents will
  be tempted to reach for `native_decide`. Both instances are frozen in
  `Defs.lean` in their computable form for exactly this reason.



