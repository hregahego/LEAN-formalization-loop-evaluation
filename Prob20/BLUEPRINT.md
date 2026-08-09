# Blueprint: Problem 20 — θₙ : Int(D)^⊗ⁿ → Int(Dⁿ) is neither injective nor surjective

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
We build the Cahen–Fontana–Frisch–Glaz counterexample domain explicitly inside the
rational function field `K = 𝔽₂(t)`: `T` is the semilocal PID `𝔽₂[t]` localized away
from the two primes `(t)` and `(t+1)`, `π = t(t+1)`, `𝔪 = πT`, and `D = 𝔽₂ + 𝔪`.
Every claim of the sketch is then a statement about explicit rational functions, and
**both halves of the proof are driven by one single lemma**: for an integer-valued
`f ∈ Int(D)` with `f(0) = 0`, the value `f(u_N)` lies in `𝔪` for the test points
`u_N = t(t+1)ᴺ` once `N` is large (a one-line valuation estimate at the prime `(t+1)`,
combined with `D ∩ 𝔫₁ = 𝔪`). Non-injectivity falls out by evaluating a putative
representation `p = Σ mᵢfᵢ` at `u_N`; non-surjectivity falls out by applying the mixed
finite difference `F ↦ F(u,u) − F(u,0) − F(0,u) + F(0,0)` to a putative representation
of `P(X,Y) = g(XY)`.

- **Headline target (frozen theorem `theta_not_injective_not_surjective`).** For the
  explicit domain `Prob20.Dom = 𝔽₂ + t(t+1)·T ⊆ K` and **every** `n ≥ 2` (rendered as
  `n+2`), the canonical map `θ_{n+2}` is *not injective* and *not surjective onto*
  `Int(Dⁿ⁺²)`:
  `¬ Function.Injective (theta (n+2)) ∧ ∃ F ∈ IntDn (n+2), F ∉ LinearMap.range (theta (n+2))`.
  The objects it references — `Dom`, `IntD = Int(D)`, `IntDn n = Int(Dⁿ)`, `theta` — are
  all frozen in `Defs.lean`, and `Int`/`θ` are defined **generically** for an arbitrary
  domain (`IntPoly`, `IntMv`, `theta`), then instantiated at `Dom`, so the headline
  cannot be satisfied by an ad-hoc `D`-specific surrogate. Two companion frozen
  theorems make the headline airtight: `theta_apply_tprod` (θ really is
  `f₁⊗⋯⊗fₙ ↦ ∏ᵢ fᵢ(Xᵢ)`) and `theta_mem_intMv` (θ really lands in `Int(Dⁿ)`), plus
  `D_isFractionRing` (`K` really is `Frac(D)`, so `IntD` really is the textbook
  `Int(D)`).
- **Recommended intermediate milestone (prove first):** Stage D's
  `p_not_mem_max_int` — `p = X²+X ∉ 𝔪·Int(D)`. It is the mathematical heart (it is the
  first place the two-branch structure of `T` is used against the one-dimensional
  residue field of `D`), it forces the whole valuation toolkit of Stage A into
  existence, and the "eventually small at `u_N`" submodule it produces is reused
  verbatim in Stage F for non-surjectivity.
- **Setting / ground assumptions:** everything happens in characteristic 2, inside the
  single field `K = RatFunc (ZMod 2)`. Coefficients are `𝔽₂`; the base ring `A = 𝔽₂[t]`
  is a PID with `Polynomial.eval 0` / `Polynomial.eval 1` detecting the two relevant
  primes. **No analysis, no inequalities beyond `ℕ`-arithmetic on exponents, no
  cardinality arguments, nothing infinite-dimensional is ever diagonalized.** The only
  non-elementary Mathlib machinery is `PiTensorProduct` (for `Int(D)^{⊗n}`) and
  `RatFunc`/`IsFractionRing`.

> **Why this is tractable.** Every object is explicit: the domain, the two test-point
> families, and the four polynomials `p, q, g, P` are written down, and each of the
> sketch's "valuation arguments" reduces to a divisibility statement in `𝔽₂[t]`
> (`m ∈ 𝔪ᵏ ↔ πᵏ ∣ numerator`). No structure theory of `Int(D)` is needed — we never
> need a basis, a generating set, or finiteness of anything. The real risk is **not**
> mathematics: it is (i) **mis-modeling** `𝔪·Int(D)`, `Int(Dⁿ)` or `θₙ` so that a
> frozen statement becomes weaker than the sketch's claim (e.g. defining `θₙ` with an
> unconstrained codomain and forgetting to freeze `theta_apply_tprod`, after which the
> zero map "answers" the problem); (ii) **over-reach** — assuming `f(u) ∈ 𝔪` for *all*
> `u ∈ 𝔪` rather than for large `N`, which is exactly the statement we do *not* know
> and must not use; and (iii) `PiTensorProduct` API friction, which is engineering,
> not mathematics.

---

## Part −1 — Setting up the repository (the SETUP stage)

The goal of this stage is to produce a compiling skeleton in which **every
`Definition` and every `Theorem` statement is written and frozen**, with all
proofs `:= sorry`. Once frozen, `Defs.lean` and `Theorems.lean` are **never
edited again** during the proving phase. Everything proved later lives in
support files and may not change a single character of the frozen statements.

### 1. Create the Lean project

```bash
cd Prob20-refactors
lake +leanprover/lean4:v4.31.0 new Prob20 math
cd Prob20
# pin Mathlib in lakefile.toml + lake-manifest.json to the rev whose
# lean-toolchain is exactly leanprover/lean4:v4.31.0, then:
lake exe cache get
lake build            # must succeed on the bare skeleton before anything else
```

Layout (every project follows this shape; rename only the bracketed parts):

```
Prob20/
  Prob20/
    Defs.lean          -- FROZEN after this stage: every object the proof needs
    Theorems.lean      -- FROZEN after this stage: the frozen theorem statements (sorry)
    Proofs/
      Domain/          -- Stage A: T, π, 𝔪ᵏ, D = 𝔽₂+𝔪; domain/local/fraction-field facts
      Theta/           -- Stage B: Int(D), Int(Dⁿ), the multilinear map, θₙ
      KeyPolys/        -- Stage C: p, q, g, P and their membership facts
      Vanishing/       -- Stage D: the test points, the key vanishing lemma, p,tp,(t+1)p ∉ 𝔪R
      Injectivity/     -- Stage E: the functionals λ, μ, τ ≠ 0, θₙ(τ) = 0
      Surjectivity/    -- Stage F: the mixed finite difference, P ∉ im θₙ
      Headline/        -- Stage G: assembly of the headline theorem
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `Prob20.Solution`, proven (clean names)
  Prob20.lean          -- imports everything
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

All support declarations live in `namespace Prob20` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface;
`Solution.lean` re-exposes each as `Prob20.Solution.<name>` after it is
proven, and `Discharge.lean` machine-checks that each proof has *exactly* the
frozen type (`@Frozen = @Proof := rfl`).

`USER_NOTES.md` for this problem says **"None — no assumed axioms."** Therefore
`scripts/ALLOWED_AXIOMS.txt` is empty, no `axiom` declaration may appear anywhere in
the project, and every solved theorem must print exactly within
`{propext, Classical.choice, Quot.sound}`.

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.** For each
definition record the Lean rendering and the **MODELING DECISION**.

Global abbreviations (no content, but they fix the universe of discourse):

```lean
abbrev F : Type := ZMod 2                    -- k = 𝔽₂
abbrev A : Type := Polynomial (ZMod 2)       -- A = k[t]
abbrev K : Type := RatFunc (ZMod 2)          -- K = Frac(A) = 𝔽₂(t)
noncomputable def tK : K := algebraMap A K Polynomial.X
```

> **MODELING DECISION (ambient field).** Everything — `T`, `𝔪`, `D`, `Int(D)` — is
> built as a sub-object of the *single* concrete field `K = RatFunc (ZMod 2)`, rather
> than as an abstract localization `S⁻¹A` with a separate `IsFractionRing` transport.
> Rejected alternative: `T := Localization S` with `K := FractionRing T`. That gives
> the localization API for free but forces every element comparison through
> `IsLocalization.mk'` and an isomorphism `FractionRing T ≃ RatFunc 𝔽₂`; since *all*
> of our arguments are explicit computations with named rational functions
> (`t(t+1)ᴺ`, `(X²+X)/π`, …), the sub-object model is strictly cheaper. Consequence a
> later stage must respect: `T`, `Dom` are `Subring K`, so their element type is
> `↥T`, `↥Dom` and coercions `(x : K)` appear everywhere; state support lemmas about
> *elements of `K` together with a membership hypothesis*, not about `↥T`, wherever
> possible.

**D1 `S : Submonoid A`** — the multiplicative set `A ∖ ((t) ∪ (t+1))`:

```lean
def S : Submonoid A where
  carrier := {a | a.eval 0 ≠ 0 ∧ a.eval 1 ≠ 0}
  one_mem' := …; mul_mem' := …
```

> **MODELING DECISION.** `a ∉ (t) ∪ (t+1)` is rendered as
> `a.eval 0 ≠ 0 ∧ a.eval 1 ≠ 0`. This is *equivalent* over `𝔽₂` (`X − c ∣ a ↔ a(c) = 0`,
> and `t+1 = t−1` in characteristic 2) and is by far the most computable form — both
> `one_mem'` and `mul_mem'` are `simp`. Rejected: `a ∉ Ideal.span {X} ∪ Ideal.span {X+1}`
> (equivalent, but every use needs `Polynomial.dvd_iff_isRoot`). A Stage-A support lemma
> `mem_S_iff_not_dvd` must record the equivalence so nothing is lost.

**D2 `T : Subring K`** — the semilocal PID `S⁻¹A`:

```lean
def T : Subring K where
  carrier := {x | ∃ a : A, ∃ s ∈ S, algebraMap A K s * x = algebraMap A K a}
  …
```

> **MODELING DECISION.** The `∃ a, ∃ s ∈ S, s·x = a` form (rather than
> `x = a / s`) makes the closure proofs pure algebra (common denominators) with no
> division and no `≠ 0` side conditions. The two maximal ideals `𝔫₀ = tT`,
> `𝔫₁ = (t+1)T` are **not** frozen as separate definitions: they are only ever used
> through the Stage-A support predicates `mem_n0`, `mem_n1` (defined in
> `Proofs/Domain/`), because no frozen statement mentions them.

**D3 `piA : A`, `piK : K`, `maxPow : ℕ → Submodule ↥T K`** — `π = t(t+1)` and the
powers `𝔪ᵏ = πᵏT`:

```lean
def piA : A := Polynomial.X * (Polynomial.X + 1)
noncomputable def piK : K := algebraMap A K piA
noncomputable def maxPow (j : ℕ) : Submodule ↥T K where
  carrier := {x | ∃ y ∈ T, x = piK ^ j * y}
  …
noncomputable abbrev maxSet : Submodule ↥T K := maxPow 1
```

> **MODELING DECISION.** `𝔪` and `𝔪²` are the *same* definition at `j = 1, 2`, as a
> `Submodule ↥T K` (i.e. the fractional-ideal-style `πʲT ⊆ K`), **not** as
> `Ideal ↥T`. Reason: every statement in which `𝔪` occurs
> (`p(d) ∈ 𝔪`, `Δ ∈ 𝔪²`, `𝔪·Int(D)`) is about elements of `K`, and `Submodule ↥T K`
> lets us say that without coercing through `↥T`. It is a `↥Dom`-submodule as well
> via `Submodule.restrictScalars` once `Dom ≤ T` is known (Stage A must supply the
> `IsScalarTower ↥Dom ↥T K` instance). The single characterization lemma
> `mem_maxPow_iff : s ∈ S → (algebraMap A K a * (algebraMap A K s)⁻¹ ∈ maxPow j ↔ piA ^ j ∣ a)`
> is the workhorse of Stages D and F and is proved once in Stage A.

**D4 `Dom : Subring K`** — the pullback domain `D = k + 𝔪`:

```lean
noncomputable def Dom : Subring K where
  carrier := {x | ∃ c : ZMod 2, ∃ y ∈ T, x = algebraMap (ZMod 2) K c + piK * y}
  …
```

> **MODELING DECISION.** `D = 𝔽₂ + 𝔪` is rendered literally as "constant plus an
> element of `𝔪`". `D/𝔪 ≅ 𝔽₂` is then *definitional* rather than a quotient
> computation, which is what makes the residue arithmetic (`x²+x ∈ 𝔪` for `x ∈ D`, and
> `D ∩ 𝔫₁ = 𝔪`) short. The maximal ideal of `Dom` as an honest ideal,
> `maxD : Ideal ↥Dom := {d | (d : K) ∈ maxSet}`, is also frozen here because
> `D_isLocalRing` refers to it. Rejected: defining `D` as a pullback
> `T ×_{T/𝔪} 𝔽₂` via `RingHom.eqLocus`/fiber product — faithful, but every membership
> proof would then have to be transported through the pullback.

**D5 `IntPoly` — `Int(R)` for a *general* domain** (the textbook definition):

```lean
def IntPoly (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr] :
    Subalgebra R (Polynomial Kr) where
  carrier := {f | ∀ d : R, f.eval (algebraMap R Kr d) ∈ (algebraMap R Kr).range}
  …
noncomputable abbrev IntD : Subalgebra ↥Dom (Polynomial K) := IntPoly ↥Dom K
```

> **MODELING DECISION (generality).** `Int` and `θ` are defined for an **arbitrary**
> ring/field pair `(R, Kr)` with `Algebra R Kr`, and only then instantiated at
> `(↥Dom, K)`. This is what makes the headline a genuine answer to Problem 20 rather
> than a statement about a bespoke object. `IsFractionRing R Kr` is deliberately **not**
> a typeclass argument (it is not needed for the definition to typecheck, and requiring
> it would force an unproved instance into `Defs.lean`); faithfulness is instead secured
> by the *frozen theorem* `D_isFractionRing : IsFractionRing ↥Dom K`, which certifies
> that for our instantiation `Kr` really is `Frac(D)`. `Algebra ↥Dom K` comes from
> `Dom.subtype.toAlgebra` (declared in `Defs.lean`; it needs no proof).

**D6 `IntMv` — `Int(Rⁿ)`:**

```lean
def IntMv (R Kr : Type) [CommRing R] [Field Kr] [Algebra R Kr] (n : ℕ) :
    Subalgebra R (MvPolynomial (Fin n) Kr) where
  carrier := {G | ∀ v : Fin n → R,
                MvPolynomial.eval (fun i => algebraMap R Kr (v i)) G ∈ (algebraMap R Kr).range}
  …
noncomputable abbrev IntDn (n : ℕ) : Subalgebra ↥Dom (MvPolynomial (Fin n) K) := IntMv ↥Dom K n
```

> **MODELING DECISION.** `Int(Dⁿ) = {F ∈ K[X₁..Xₙ] : F(Dⁿ) ⊆ D}` is quantified over
> **all** `v : Fin n → R` — never over a subset, never over one variable at a time.

**D7 `theta` — the canonical map θₙ:**

```lean
noncomputable def thetaMul (R Kr) [CommRing R] [Field Kr] [Algebra R Kr] (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => ↥(IntPoly R Kr)) (MvPolynomial (Fin n) Kr) :=
  { toFun := fun f => ∏ i, Polynomial.aeval (MvPolynomial.X i) ((f i : Polynomial Kr)), … }

noncomputable def theta (R Kr) [CommRing R] [Field Kr] [Algebra R Kr] (n : ℕ) :
    (⨂[R] (_ : Fin n), ↥(IntPoly R Kr)) →ₗ[R] MvPolynomial (Fin n) Kr :=
  PiTensorProduct.lift (thetaMul R Kr n)
```

> **MODELING DECISION (the most important one in the project).** θₙ is frozen as an
> `R`-**linear** map into the *ambient* `MvPolynomial (Fin n) Kr`, **not** as an
> `AlgHom` into `↥(IntMv …)`. Three reasons. (i) A corestriction to `↥(IntMv …)` would
> need the proof `theta_mem_intMv` *inside* `Defs.lean`, which is not allowed (no
> `sorry` there, and the proof is a Stage-B lemma). (ii) Injectivity and surjectivity
> of a map are properties of the underlying function, and "surjective onto `Int(Dⁿ)`"
> is rendered exactly by `∃ F ∈ IntDn n, F ∉ LinearMap.range (theta n)` — nothing is
> weakened, because `theta_mem_intMv` (frozen) proves the range does lie in
> `Int(Dⁿ)`. (iii) It removes any dependence on `PiTensorProduct`'s commutative-algebra
> instance, which is the one piece of Mathlib API whose availability we do not want to
> bet the project on. **Faithfulness is not lost:** an `R`-linear map out of
> `⨂[R] Fin n, Int(R)` is *uniquely determined* by its values on pure tensors, so the
> frozen theorem `theta_apply_tprod`
> (`theta n (tprod R f) = ∏ i, aeval (X i) (f i)`) pins `theta` to be exactly the
> sketch's `f₁⊗⋯⊗fₙ ↦ ∏ fᵢ(Xᵢ)` and nothing else. Without that frozen theorem the
> whole result would be vacuous (the zero map is neither injective nor surjective), so
> `theta_apply_tprod` is a *mandatory* frozen statement.

**D8 the key polynomials:**

```lean
noncomputable def p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X
noncomputable def q : Polynomial K := Polynomial.C piK⁻¹ * p          -- (X²+X)/π
noncomputable def g : Polynomial K := q ^ 2 + q
noncomputable def bigP (n : ℕ) : MvPolynomial (Fin (n + 2)) K :=
  Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1) g            -- P(X,Y) = g(XY)
```

> **MODELING DECISION (`n ≥ 2` as `n + 2`).** Every statement about "all `n ≥ 2`" is
> frozen as `∀ n : ℕ, … (n + 2)`. This is logically equivalent to `∀ n, 2 ≤ n → …` and
> it lets `bigP` mention the variables `(0 : Fin (n+2))` and `(1 : Fin (n+2))` without
> carrying a `2 ≤ n` hypothesis into a *definition* (`Fin n` may be empty). This is a
> re-indexing, **not** a weakening: `n+2` ranges over exactly `{2,3,4,…}`.

**D9 `maxSmulInt : Submodule ↥Dom (Polynomial K)`** — the module `𝔪·Int(D)`:

```lean
noncomputable def maxSmulInt : Submodule ↥Dom (Polynomial K) :=
  Submodule.span ↥Dom {G | ∃ c : K, c ∈ maxSet ∧ ∃ f ∈ IntD, G = Polynomial.C c * f}
```

> **MODELING DECISION.** `𝔪R` is the `D`-submodule of `K[X]` spanned by the products
> `c·f` (`c ∈ 𝔪`, `f ∈ R`) — the textbook `𝔪R`. It is deliberately a submodule of the
> *ambient* `Polynomial K` rather than of `↥IntD`: that way the frozen non-membership
> statements can be about `p`, `C tK * p`, `C (tK+1) * p : Polynomial K` directly,
> with no membership certificate needed inside `Defs.lean`. Note that
> `Submodule.span_le` / `Submodule.smul_le`-style reasoning on the *generators* is the
> only way these statements are ever used, so no "finite sum extraction" is required.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook
> notion**, quantified exactly as the source states it. Specifically here:
> `IntPoly`/`IntMv` quantify over **all** `d : R` / **all** `v : Fin n → R` — never a
> finite sample, never "for `d` in a generating set"; `maxSmulInt` is the span of
> **all** products `c·f`, not of a chosen finite family; `theta` must be `lift` of the
> genuine product `∏ᵢ fᵢ(Xᵢ)` — a definition that drops a factor, or fixes `n = 2`,
> makes everything downstream vacuous. Do not weaken a `∀` to a finite or fixed family,
> do not replace an equality with a one-sided inclusion, and do not add a hypothesis
> that the source claim does not have. A "simplification" here can make the headline
> vacuous.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each statement must render a claim of
`SKETCH.md` **faithfully and minimally**, have a **stable, binding name**, and the
list must include the headline.

| # | Frozen name | Statement (schematic) | `SKETCH.md` step |
| - | ----------- | --------------------- | ---------------- |
| 1 | `D_isDomain` | `IsDomain ↥Dom` | "Let `D` be an integral domain"; the witness must *be* a domain |
| 2 | `mem_Dom_iff_mem_max_or_sub_one_mem_max` | `∀ x : K, x ∈ Dom ↔ (x ∈ maxSet ∨ x - 1 ∈ maxSet)` | `D/𝔪 ≅ 𝔽₂` (Counterexample Domain) |
| 3 | `D_isLocalRing` | `IsLocalRing ↥Dom` together with `IsLocalRing.maximalIdeal ↥Dom = maxD` | "`D` is a … local domain", `𝔪` its maximal ideal |
| 4 | `D_isFractionRing` | `IsFractionRing ↥Dom K` | `K = Frac(D) = 𝔽₂(t)` |
| 5 | `theta_apply_tprod` | `∀ n f, theta ↥Dom K n (tprod ↥Dom f) = ∏ i, aeval (X i) (f i : K[X])` | the display `f₁⊗⋯⊗fₙ ↦ ∏ fᵢ(Xᵢ)` |
| 6 | `theta_mem_intMv` | `∀ n x, theta ↥Dom K n x ∈ IntDn n` | "`θₙ : Int(D)^⊗ⁿ → Int(Dⁿ)`" is well defined |
| 7 | `p_eval_mem_max` | `∀ x : K, x ∈ Dom → p.eval x ∈ maxSet` | Key Observation: `p(D) ⊆ 𝔪` |
| 8 | `smul_p_mem_int` | `∀ c : K, c ∈ T → Polynomial.C c * p ∈ IntD` | Key Observation: `cp ∈ R` for `c ∈ T` |
| 9 | `g_mem_int` | `g ∈ IntD` | Failure of Surjectivity: `g ∈ R` |
| 10 | `bigP_mem_intMv` | `∀ n, bigP n ∈ IntDn (n+2)` | Failure of Surjectivity: `P ∈ Int(D²)` |
| 11 | `p_not_mem_max_int` | `p ∉ maxSmulInt` | Key Observation: `p ∉ 𝔪R` |
| 12 | `t_mul_p_not_mem_max_int` | `Polynomial.C tK * p ∉ maxSmulInt` | Key Observation: `tp ∉ 𝔪R` |
| 13 | `t_add_one_mul_p_not_mem_max_int` | `Polynomial.C (tK + 1) * p ∉ maxSmulInt` | Key Observation: `(t+1)p ∉ 𝔪R` |
| 14 | `theta_not_injective` | `∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n+2))` | Failure of Injectivity |
| 15 | `bigP_not_mem_range` | `∀ n : ℕ, bigP n ∉ LinearMap.range (theta ↥Dom K (n+2))` | Failure of Surjectivity |
| 16 | `theta_not_surjective` | `∀ n : ℕ, ∃ F ∈ IntDn (n+2), F ∉ LinearMap.range (theta ↥Dom K (n+2))` | Failure of Surjectivity |
| 17 | `theta_not_injective_not_surjective` | `∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n+2)) ∧ ∃ F ∈ IntDn (n+2), F ∉ LinearMap.range (theta ↥Dom K (n+2))` | **HEADLINE** / Conclusion box |

**Why these 17.** Theorems 1–4 certify that the *witness is what the sketch says it
is* (an integral domain, local, with residue field `𝔽₂` and fraction field `K`); without
them "Int(D)" would not be the textbook object and the answer would be about the wrong
ring. Theorems 5–6 certify that `theta` is *the canonical map* — 5 is the single most
important anti-cheat statement in the project (see D7). Theorems 7–10 are the explicit
constructions of the sketch (the Key Observation and the polynomial `g`, `P`).
Theorems 11–13 are the **decidable heart**: the three non-memberships that *are*
(over `𝔽₂`, exactly) the linear independence of `p̄, t̄p̄` in `R/𝔪R`. Theorems 14–16 are
the two payoffs, and 17 is the headline that a reader cites.

> **MODELING DECISION (linear independence).** The sketch's "`p̄` and `tp̄` are linearly
> independent in `R/𝔪R`" is frozen as the three non-memberships 11–13 rather than as a
> `LinearIndependent` statement over `D/𝔪`. Over `𝔽₂ = D/𝔪` the only nontrivial linear
> combinations of `{p̄, t̄p̄}` are `p̄`, `t̄p̄`, `p̄ + t̄p̄ = ((t+1)p)‾`, so the three
> non-memberships and linear independence are **equivalent** — nothing is weakened —
> and the non-membership form avoids freezing a quotient-module-over-a-residue-field
> construction into `Defs.lean`. The `LinearIndependent` form is still *produced*, as a
> Stage-E support lemma, because it is what feeds the dual-functional argument.

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
## <UTC timestamp> — <stage/item, e.g. "Stage D · `p_not_mem_max_int`">
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

| Need                                          | Mathlib handle                                                                 |
| --------------------------------------------- | ------------------------------------------------------------------------------ |
| `k[t]` and `𝔽₂(t)`                            | `Polynomial (ZMod 2)`, `RatFunc (ZMod 2)`, `RatFunc.instField`                   |
| `Frac(k[t]) = k(t)`                            | `RatFunc.instIsFractionRing` (`algebraMap (Polynomial F) (RatFunc F)` is injective) |
| `X − c ∣ f ↔ f(c) = 0`                        | `Polynomial.dvd_iff_isRoot`, `Polynomial.IsRoot`                                 |
| unique factorization / "`πʲ ∣ a`" bookkeeping | `Polynomial` is a `EuclideanDomain`/`UniqueFactorizationMonoid`; `pow_dvd_pow`, `IsCoprime`, `Polynomial.isCoprime_of_isUnit_of...` |
| splitting off a prime power from a denominator | `multiplicity` / `emultiplicity` + `pow_multiplicity_dvd`, or `UniqueFactorizationMonoid.exists_eq_pow_mul_and_not_dvd` |
| localizing away from two primes                | not needed abstractly — `T` is the explicit `Subring K` of D2                     |
| subrings, submodules, spans                    | `Subring`, `Subalgebra`, `Submodule.span`, `Submodule.span_le`, `Submodule.restrictScalars` |
| "`D` is local"                                 | `IsLocalRing`, `IsLocalRing.of_isUnit_or_isUnit_of_add_one`, `IsLocalRing.maximalIdeal` |
| `K = Frac(D)`                                  | `IsFractionRing.of_field`-style criteria: `IsFractionRing.mk'`, `IsLocalization.of_surjective`, or the primitive `IsFractionRing` constructor (`map_units`, `surj`, `exists_of_eq`) |
| univariate/multivariate polynomials, evaluation | `Polynomial.eval`, `Polynomial.aeval`, `MvPolynomial.eval`, `MvPolynomial.aeval`, `MvPolynomial.X` |
| `f ↦ f(Xᵢ)` as an algebra map                  | `Polynomial.aeval (MvPolynomial.X i) : K[X] →ₐ[K] MvPolynomial (Fin n) K`         |
| the `n`-fold tensor power over `D`             | `PiTensorProduct` (`⨂[R] i, M i`), `PiTensorProduct.tprod`, `PiTensorProduct.lift`, `PiTensorProduct.lift.tprod`, `PiTensorProduct.induction_on` |
| multilinear maps                               | `MultilinearMap`, `MultilinearMap.mk`, `Finset.prod_update_of_mem` (for `map_add`/`map_smul` at one coordinate) |
| linear functionals & extension                 | `Module.Dual`, `LinearMap.exists_extend`, `Basis.mk`, `Basis.coord`, `LinearIndependent` |
| the `𝔽₂`-structure on `R/𝔪R`                   | `CharP`/characteristic two: `AddCommGroup.zmodModule` (a group with `2 • x = 0` is a `ZMod 2`-module), or the `Algebra (ZMod 2) ↥Dom` route |
| eventual statements ("for all large `N`")      | plain `∃ N₀, ∀ N ≥ N₀, …`, or `Filter.Eventually … Filter.atTop` (`Filter.eventually_atTop`, `Filter.Eventually.and`) |

**The one or two nontrivial dependencies.** (i) `PiTensorProduct.lift` +
`PiTensorProduct.lift.tprod` + `PiTensorProduct.induction_on` — these three carry all of
Stages B, E, F. (ii) `LinearMap.exists_extend` (extend a functional from a
2-dimensional subspace of `R/𝔪R` to the whole space) — the only "abstract" step in the
project.

**Machinery you can avoid.** The sketch's language mentions the semilocal PID `T`, its
two maximal ideals, the pullback square, and `Tor`-free tensor talk. **None of that
theory is needed**: `T` is used only through `mem_maxPow_iff` (a divisibility test in
`𝔽₂[t]`), and "linear independence in `R/𝔪R`" is reduced to three explicit
non-memberships. Do **not** develop a theory of `Int(D)`, of semilocal rings, of Krull
dimension, or of pullback/conductor squares — every one of those is a detour.

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #  | Object | Role |
| -- | ------ | ---- |
| D1 | `S : Submonoid A` | `A ∖ ((t) ∪ (t+1))`, rendered as `a(0) ≠ 0 ∧ a(1) ≠ 0` |
| D2 | `T : Subring K` | `S⁻¹A ⊆ K`: the semilocal PID the whole construction sits in |
| D3 | `piA`, `piK`, `maxPow j`, `maxSet` | `π = t(t+1)`; `𝔪ʲ = πʲT` as a `↥T`-submodule of `K` (`j = 1, 2` are the only uses) |
| D4 | `Dom : Subring K`, `maxD : Ideal ↥Dom` | the counterexample domain `D = 𝔽₂ + 𝔪` and its maximal ideal |
| D5 | `IntPoly R Kr`, `IntD` | `Int(R) = {f ∈ Kr[X] : f(R) ⊆ R}` (generic), instantiated at `D` |
| D6 | `IntMv R Kr n`, `IntDn n` | `Int(Rⁿ) = {F ∈ Kr[X₁..Xₙ] : F(Rⁿ) ⊆ R}` (generic), instantiated at `D` |
| D7 | `thetaMul`, `theta` | the multilinear map `f ↦ ∏ᵢ fᵢ(Xᵢ)` and `θₙ = PiTensorProduct.lift` of it |
| D8 | `p`, `q`, `g`, `bigP n` | `X²+X`, `(X²+X)/π`, `q²+q`, and `P(X,Y) = g(XY)` in `Fin (n+2)` variables |
| D9 | `maxSmulInt` | `𝔪·Int(D)` as a `↥Dom`-submodule of `K[X]` |

Support objects that are **not** frozen (they live in `Proofs/`, and may be refactored
freely): the test-point families `u₁ N = t(t+1)ᴺ` and `u₀ N = tᴺ(t+1)`, the primes
`𝔫₀`, `𝔫₁`, the residue map `rho : ↥Dom →+* ZMod 2`, the quotient `V = ↥IntD ⧸ 𝔪R`, the
functionals `λ`, `μ`, `ν`, the tensor `τ`, and the "eventually in `𝔪ʲ`" submodules.

---

## Part 2 — Theorems and lemmas to prove (in order)

### Stage A — the domain `D` and its arithmetic (`Proofs/Domain/`)

Goal: the complete elementary toolkit for `S`, `T`, `𝔪ʲ`, `Dom`, and the frozen
theorems `D_isDomain`, `mem_Dom_iff_mem_max_or_sub_one_mem_max`, `D_isLocalRing`,
`D_isFractionRing`. Everything later is stated in terms of these lemmas, so get their
shapes right.

**A1 — `mem_T_iff`, `mem_S_iff_not_dvd`, `T_le_…`.** Unfolding lemmas: `x ∈ T ↔ ∃ a s,
s ∈ S ∧ algebraMap A K s * x = algebraMap A K a`; `a ∈ S ↔ ¬(X ∣ a) ∧ ¬(X + 1 ∣ a)`
(via `Polynomial.dvd_iff_isRoot`, remembering `X + 1 = X - 1` over `𝔽₂`). Also
`algebraMap A K a ∈ T` for every `a`, and `(algebraMap A K s)⁻¹ ∈ T` for `s ∈ S`.

**A2 — `mem_maxPow_iff` (the workhorse).** For `a : A`, `s ∈ S`, `j : ℕ`:
`algebraMap A K a * (algebraMap A K s)⁻¹ ∈ maxPow j ↔ piA ^ j ∣ a`.
Proof: `⇐` is immediate. `⇒`: from `a/s = πʲ·(b/s')` get `a·s' = πʲ·b·s` in `A`; `π` is
coprime to `s'` (`s' ∈ S` means `X ∤ s'` and `X+1 ∤ s'`), so `πʲ ∣ a` by unique
factorization (`X` and `X+1` are prime in `𝔽₂[t]`; use `Prime.dvd_of_dvd_pow` /
`IsCoprime.dvd_of_dvd_mul_right` — note `X` and `X+1` are coprime to each other, so
handle the two prime powers separately and recombine). Add the two corollaries used
constantly later: `piK ^ j * y ∈ maxPow j` for `y ∈ T`, and `maxPow (j+1) ≤ maxPow j`.

**A3 — the two primes.** `mem_n0 x := ∃ a s, s ∈ S ∧ X ∣ a ∧ x = a/s` and `mem_n1`
likewise with `X + 1`; prove `maxSet = 𝔫₀ ⊓ 𝔫₁` in the form
`x ∈ maxSet ↔ x ∈ 𝔫₀ ∧ x ∈ 𝔫₁` (this is CRT for `π = t(t+1)`, i.e. `t ∣ a ∧ (t+1) ∣ a ↔
t(t+1) ∣ a` — `IsCoprime.mul_dvd`), and that `𝔫₀`, `𝔫₁` are prime `↥T`-submodules
(`x*y ∈ 𝔫ᵢ → x ∈ 𝔫ᵢ ∨ y ∈ 𝔫ᵢ`).

**A4 — `mem_Dom_iff_mem_max_or_sub_one_mem_max` (frozen #2), `Dom_le_T`,
`max_le_Dom`.** Immediate from D4 by `ZMod 2` case analysis (`c = 0` or `c = 1`;
`decide` on `ZMod 2`). Also the two facts that make Stage D work:
`mem_max_of_mem_Dom_of_mem_n1 : x ∈ Dom → x ∈ 𝔫₁ → x ∈ maxSet` and its `𝔫₀` twin
(proof: `x = c + πy`; if `c = 1` then `1 ∈ 𝔫₁`, contradiction with `𝔫₁ ≠ ⊤`).

**A5 — residue arithmetic.** `mul_self_add_self_mem_max : x ∈ T → x * x + x ∈ maxSet`
(both residue fields of `T` are `𝔽₂`: `x(x+1) ∈ 𝔫₀` because in `A/(t) ≅ 𝔽₂` every
element satisfies `a² = a`; same at `𝔫₁`; then A3). This single lemma yields both
`p_eval_mem_max` and `g_mem_int` in Stage C.

**A6 — `D_isDomain` (frozen #1).** `Dom` is a subring of a field: use
`Subring.instIsDomain` / `NoZeroDivisors` inherited from `K`.

**A7 — `D_isLocalRing` (frozen #3).** Nonunits of `↥Dom` = `maxD`. Key computation: if
`x ∈ Dom` and `x ∉ maxSet` then `x = 1 + w` with `w ∈ 𝔪`; then `x` is a unit of `T`
(`x ∉ 𝔫₀`, `x ∉ 𝔫₁`, so `x⁻¹ ∈ T` by A2/A3) and `x⁻¹ = 1 + w'` with
`w' = w·x⁻¹·(-1) ∈ 𝔪` (`𝔪` is a `T`-ideal), hence `x⁻¹ ∈ Dom`. Conclude with
`IsLocalRing.of_isUnit_or_isUnit_of_add_one` or by showing `maxD` is the set of
nonunits (`IsLocalRing.of_unique_max_ideal`), and prove the companion
`IsLocalRing.maximalIdeal ↥Dom = maxD`.

**A8 — `D_isFractionRing` (frozen #4).** Every `x ∈ K` is a ratio of two elements of
`Dom`: write `x = a/s` with `a, s : A`, `s ≠ 0`. Since `A ⊆ T` (A1), both `π·a` and
`π·s` lie in `𝔪 ⊆ Dom` (A2/A4), `π·s ≠ 0`, and `x = (π a)/(π s)`. Feed this to the
`IsFractionRing` constructor (`map_units`: a
nonzero `d ∈ Dom` is invertible in `K`; `surj`: the display above; `exists_of_eq`:
injectivity of `↥Dom → K`, which is `Subtype.coe_injective`).

> **Cheat watch (Stage A).** (i) `mem_maxPow_iff` must be an **iff** — the `⇐`
> direction alone is useless and the `⇒` direction is where all the content is; do not
> "prove" the `⇒` direction by adding a hypothesis such as `s = 1` or `a ∈ S`. (ii)
> `D_isLocalRing` must produce the maximal ideal `maxD` **as defined in `Defs.lean`**,
> not some convenient other ideal. (iii) `D_isFractionRing` is what makes `IntD` the
> textbook `Int(D)`; it may **not** be replaced by "`K` is *a* field containing `D`".
> (iv) Never assume `T` is a PID/Dedekind/Noetherian and never invoke Krull dimension:
> if a proof wants that, it has taken a detour — every fact needed here is a
> divisibility statement in `𝔽₂[t]`. Guardrail `example`s to include:
> `example : piK ∈ maxSet`, `example : (1 : K) ∉ maxSet`, `example : tK ∉ Dom`
> (the last one confirms `Dom ≠ T`, i.e. that the construction did not silently
> collapse).

### Stage B — `Int(D)`, `Int(Dⁿ)` and the canonical map θₙ (`Proofs/Theta/`)

Goal: frozen `theta_apply_tprod` (#5) and `theta_mem_intMv` (#6), plus the `IntPoly`
API the later stages consume.

**B1 — `mem_IntPoly_iff`, `mem_IntMv_iff`, and closure lemmas.** `f ∈ IntD ↔ ∀ x ∈ Dom,
f.eval x ∈ Dom` (rephrasing the `∀ d : ↥Dom` / `RingHom.range` form of D5 in terms of
elements of `K` with a membership hypothesis — do this once, everything downstream uses
it). Same for `IntMv`. Add: constants `C c ∈ IntD` for `c ∈ Dom`, and `X ∈ IntD`.

**B2 — `thetaMul` is well defined.** Prove `map_add`/`map_update_smul` at each
coordinate for `f ↦ ∏ i, aeval (X i) (f i)`: split the product with
`Finset.prod_update_of_mem` (or `Finset.mul_prod_erase`) at the updated index, then use
that `Polynomial.aeval (X i)` is additive/`↥Dom`-linear (it is `K`-algebra, hence
`↥Dom`-linear via `IsScalarTower ↥Dom K (MvPolynomial (Fin n) K)`, which must be
supplied as an instance here).

**B3 — `theta_apply_tprod` (frozen #5).** `PiTensorProduct.lift.tprod` — should be
`simp [theta, thetaMul, PiTensorProduct.lift.tprod]`. **Do not** let this become
`rfl`-by-luck: if it does not go through, the definition of `thetaMul` in `Defs.lean` is
wrong and the project must be re-frozen (SETUP bug), not patched downstream.

**B4 — `theta_mem_intMv` (frozen #6).** `IntDn (n)` is a subalgebra, hence its carrier
is a `↥Dom`-submodule; so `LinearMap.range (theta n) ≤ (IntDn n).toSubmodule` follows
from checking pure tensors, via `PiTensorProduct.induction_on` (or
`LinearMap.range_le_iff` + `PiTensorProduct.span_tprod_eq_top`). On a pure tensor:
`(∏ i, aeval (X i) (f i))` evaluated at `v : Fin n → Dom` is `∏ i, (f i).eval (v i) ∈ Dom`
since each `f i ∈ IntD` — use `MvPolynomial.eval` of a product and
`Polynomial.eval_aeval`-style commutation (`MvPolynomial.eval_aeval` may need to be
proved by `Polynomial.induction_on`).

> **Cheat watch (Stage B).** (i) `theta_mem_intMv` must be proved for **all** `x` in the
> tensor power, via the submodule/induction argument — proving it only for pure tensors
> and stopping is a silent gap. (ii) The `∀ v : Fin n → ↥Dom` in `IntMv` may not be
> specialized (e.g. to `v` with all-but-two coordinates `0`) *in the definition or in
> #6*; such specializations are legitimate only *inside* Stage F's contradiction
> argument. (iii) Resist "simplifying" `theta` to the `n = 2` case or to an `AlgHom`
> — the frozen statement is `∀ n`. (iv) Guardrail: `example : theta ↥Dom K 1 (tprod _
> ![⟨1, _⟩]) = 1` and an `example` computing `theta` on a 2-fold pure tensor of `C c`s,
> to confirm the product-of-`fᵢ(Xᵢ)` shape really came out.

### Stage C — the polynomials `p`, `q`, `g`, `P` (`Proofs/KeyPolys/`)

Goal: frozen `p_eval_mem_max` (#7), `smul_p_mem_int` (#8), `g_mem_int` (#9),
`bigP_mem_intMv` (#10). This is the "Key Observation" and the first half of "Failure of
Surjectivity" of `SKETCH.md`.

**C1 — `p_eval_mem_max` (#7).** `p.eval x = x² + x = x(x+1)`; for `x ∈ Dom ⊆ T` this is
A5. (`Polynomial.eval_add`, `eval_pow`, `eval_X`.)

**C2 — `smul_p_mem_int` (#8).** For `c ∈ T` and `x ∈ Dom`: `(C c * p).eval x =
c · p.eval x ∈ T · 𝔪 ⊆ 𝔪 ⊆ Dom` — uses that `maxSet` is a `↥T`-submodule (D3) and
`max_le_Dom` (A4). Specialize to `p`, `C tK * p`, `C (tK + 1) * p ∈ IntD` as named
corollaries (`p_mem_int`, `t_mul_p_mem_int`, `t_add_one_mul_p_mem_int`) — Stage E needs
them as *elements of `↥IntD`*.

**C3 — `q_eval_mem_T`.** For `x ∈ Dom`: `q.eval x = (p.eval x)/π ∈ T` (from #7:
`p.eval x = π·y`, `y ∈ T`, and `π ≠ 0` so `piK⁻¹ * (piK * y) = y`). Note `q ∉ IntD`;
do not claim otherwise.

**C4 — `g_mem_int` (#9).** `g.eval x = (q.eval x)² + q.eval x ∈ 𝔪` by A5 applied to
`q.eval x ∈ T` (C3); `𝔪 ⊆ Dom`. This is exactly the sketch's "both residue fields of `T`
are `𝔽₂`" step.

**C5 — `bigP_mem_intMv` (#10).** `bigP n = aeval (X 0 * X 1) g`; evaluation at
`v : Fin (n+2) → ↥Dom` gives `g.eval (v 0 * v 1)` (needs the `aeval`/`eval` commutation
lemma from B4), and `v 0 * v 1 ∈ Dom` since `Dom` is a subring, so #9's pointwise form
applies. Record `bigP_eval : MvPolynomial.eval w (bigP n) = g.eval (w 0 * w 1)` as a
standalone support lemma — Stage F uses it four times.

> **Cheat watch (Stage C).** (i) `smul_p_mem_int` is stated for **all** `c ∈ T`; do not
> prove it only for `c ∈ {1, t, t+1}` and rename it. (ii) `g_mem_int` must go through
> `q.eval x ∈ T` for **every** `x ∈ Dom` — the temptation is to check `x = 0, π, …` and
> generalize; that is a proof of nothing. (iii) `bigP_mem_intMv` must quantify over all
> `v`, including those where `v 0 * v 1` is a unit. (iv) Do **not** "fix" a failure here
> by adding `x ≠ 0` or `x ∈ 𝔪` hypotheses: `Int` is about all of `D`. Guardrails:
> `example : q ∉ IntD` is *not* required, but `example : g.eval 0 = 0` and
> `example : p.eval piK ∈ maxSet` are cheap and catch sign/`π` slips.

### Stage D — the vanishing lemma and the three non-memberships ★ MILESTONE (`Proofs/Vanishing/`)

Goal: frozen `p_not_mem_max_int` (#11), `t_mul_p_not_mem_max_int` (#12),
`t_add_one_mul_p_not_mem_max_int` (#13). **This is the mathematical heart of the whole
project** and the engine of Stage F as well. It replaces the sketch's one-line "a
valuation argument shows …" with the following completely explicit argument.

**D.1 — the test points.** `u1 N := tK * (tK + 1) ^ N` and `u0 N := tK ^ N * (tK + 1)`
(`N : ℕ`, `N ≥ 1`). Facts: `u1 N ∈ maxSet` and `u0 N ∈ maxSet` for `N ≥ 1` (A2, since
`π = t(t+1) ∣ t(t+1)ᴺ`); hence both lie in `Dom`.

**D.2 — `eval_mem_n1_of_large` (the estimate).** For **any** `h : Polynomial K` with
`h.eval 0 = 0` there is `N₀` such that for all `N ≥ N₀`, `h.eval (u1 N) ∈ 𝔫₁`.
Proof: write `h = X * h₁` (`Polynomial.X_dvd_iff` / `h.eval 0 = h.coeff 0 = 0`), so
`h.eval (u1 N) = u1 N * h₁.eval (u1 N)`. Choose a common denominator for the finitely
many coefficients of `h₁`: `h₁ = Σ a_j X^j` with `a_j = b_j / s` for a single `s ∈ S`
and `b_j : A` (clear denominators over the finite `support`; every element of `K` is
`b/s'` with `s'` arbitrary nonzero in `A`, so factor `s' = (t+1)^e * s''` and take
`N₀ := e + 1`). Then `(t+1)^{N} ∣ numerator` while `(t+1)^{e}` is all the `(t+1)` in the
denominator, so `h.eval (u1 N) ∈ 𝔫₁` as soon as `N ≥ e + 1`. **Nothing here uses
`h ∈ IntD`** — it is a pure "small at `t+1`" estimate. State it in the `∃ N₀, ∀ N ≥ N₀`
form (or `∀ᶠ N in atTop`). Twin lemma `eval_mem_n0_of_large` with `u0` and `𝔫₀`.

**D.3 — `eval_sub_eval_zero_mem_max` (the key lemma).** For `f ∈ IntD`:
`∀ᶠ N, f.eval (u1 N) - f.eval 0 ∈ maxSet` (and the `u0` twin).
Proof: `h := f - C (f.eval 0)` satisfies `h.eval 0 = 0` and `h ∈ IntD` (C-style closure,
since `f.eval 0 ∈ Dom`). By D.2, `h.eval (u1 N) ∈ 𝔫₁` eventually; and
`h.eval (u1 N) ∈ Dom` because `u1 N ∈ Dom`. Now A4's
`mem_max_of_mem_Dom_of_mem_n1` gives `h.eval (u1 N) ∈ 𝔪`. ∎
*This is the only place where "`D` has residue field `𝔽₂` while `T` has two branches" is
used, and it is why the counterexample works.*

**D.4 — the "eventually in `𝔪²`" submodule.** For a test family `u ∈ {u1, u0}` define
`Ev u : Submodule ↥Dom (Polynomial K)` with carrier
`{G | ∀ᶠ N in atTop, G.eval (u N) - G.eval 0 ∈ maxPow 2}`. It **is** a submodule:
`G ↦ G.eval (u N) - G.eval 0` is `↥Dom`-linear for each `N`, `maxPow 2` is a
`↥Dom`-submodule (restrict scalars along `Dom ≤ T`), and an intersection of eventual
conditions is eventual (`Filter.Eventually.and`).

**D.5 — `maxSmulInt ≤ Ev u`.** By `Submodule.span_le` it suffices to check a generator
`G = C c * f` with `c ∈ 𝔪`, `f ∈ IntD`:
`G.eval (u N) - G.eval 0 = c * (f.eval (u N) - f.eval 0) ∈ 𝔪 · 𝔪 = 𝔪²` eventually, by D3.
(Multiplication `maxPow 1 * maxPow 1 ≤ maxPow 2` is A2 bookkeeping.)

**D.6 — the three non-memberships (frozen #11, #12, #13).** By D.5 it is enough to exhibit,
for each of `p`, `tp`, `(t+1)p`, a test family and **infinitely many** `N` with
`G.eval (u N) - G.eval 0 ∉ maxPow 2`. With `G.eval 0 = 0` in all three cases:
- `p`: `p.eval (u1 N) = u1 N (u1 N + 1) = t(t+1)ᴺ · (t(t+1)ᴺ + 1)`. Its numerator has
  exactly **one** factor `t` (the second factor is `≢ 0 mod t`, as `eval 0` of it is
  `1`), so `π² = t²(t+1)² ∤` it: `∉ maxPow 2` by A2. Hence `p ∉ Ev u1 ⊇ maxSmulInt`.
- `(t+1)p`: same test family; `(t+1)·p.eval (u1 N)` still has exactly one factor `t`.
- `tp`: the `u1` family does **not** work (`t·p.eval (u1 N)` has two factors of `t`);
  use the **swapped** family `u0 N = tᴺ(t+1)` instead, where `t·p.eval (u0 N)` has
  exactly one factor of `t+1`. This asymmetry is not an accident — record it as a `📝`
  PROGRESS entry so no later agent "unifies" the three proofs and breaks one.

> **Cheat watch (Stage D).** (i) ★ **Never strengthen D.3 to "`f.eval u - f.eval 0 ∈ 𝔪`
> for all `u ∈ 𝔪`".** That statement is *not known* and is *not* what the sketch proves;
> the whole argument is asymptotic in `N`. Any proof that drops the `∀ᶠ N` is a bug, not
> a simplification. (ii) The non-memberships must be about `maxSmulInt` **as frozen**
> (the span over *all* generators `c·f`); do not silently prove the weaker "`p` is not a
> single product `c·f`". (iii) Do not replace `𝔪²` in D.4 by `𝔪` — with `𝔪` the argument
> collapses (`p.eval (u1 N) ∈ 𝔪` is *true*), which is precisely the trap the sketch's
> "valuation argument" hides. (iv) Do not add `N ≥ 1`-style hypotheses to a *frozen*
> statement; they belong inside the proof. (v) Guardrails:
> `example : p.eval (u1 1) ∉ maxPow 2` and `example : p.eval (u1 1) ∈ maxSet` — together
> they show the argument lives exactly between `𝔪` and `𝔪²`.

### Stage E — failure of injectivity (`Proofs/Injectivity/`)

Goal: frozen `theta_not_injective` (#14). Sketch section "Failure of Injectivity".

**E1 — the residue hom.** `rho : ↥Dom →+* ZMod 2` sending `d ↦ 0` if `(d:K) ∈ maxSet`
and `1` otherwise (well defined by A4/#2; ring-hom laws by `ZMod 2` case analysis).
Install `Module ↥Dom (ZMod 2)` via `Module.compHom` **as a scoped/`letI` instance in this
file only** (a global instance risks diamonds with `Algebra ↥Dom K`).

**E2 — `V := ↥IntD ⧸ 𝔪R` is an `𝔽₂`-vector space, and `p̄, tp̄` are independent.**
Take `mR' : Submodule ↥Dom ↥IntD` to be the comap of `maxSmulInt` along
`IntD.toSubmodule.subtype`, `V := ↥IntD ⧸ mR'`. `V` is a `ZMod 2`-module because
`char K = 2` (`AddCommGroup.zmodModule`, `2 • x = 0`). Linear independence of
`![p̄, tp̄]`: an `𝔽₂`-combination is one of `0, p, tp, (t+1)p` (`decide` over
`Fin 2 → ZMod 2`), and #11/#12/#13 say the last three are not in `𝔪R`.

**E3 — the two functionals.** `W := span (ZMod 2) {p̄, tp̄}` with basis `Basis.mk` from
E2; `λ₀ := (W.basis).coord 0`, `μ₀ := (W.basis).coord 1`; extend both to
`λ, μ : V →ₗ[ZMod 2] ZMod 2` with `LinearMap.exists_extend`. Compose with
`↥IntD → V` to get additive maps `Λ, Μ : ↥IntD → ZMod 2` with
`Λ p = 1, Λ (tp) = 0, Μ p = 0, Μ (tp) = 1`, and (crucially)
`Λ (d • f) = rho d * Λ f` — because `d • f - rho d • f ∈ 𝔪R` (as `d - rho d ∈ 𝔪`).
Also `ν : ↥IntD → ZMod 2`, `ν f := rho ⟨f.eval 0, _⟩` (`f.eval 0 ∈ Dom` since `0 ∈ Dom`),
which is `↥Dom`-linear and satisfies `ν 1 = 1`.

**E4 — the separating functional on the tensor power.** For `n' = n + 2`, define the
`↥Dom`-multilinear map `Ψ : (Fin n' → ↥IntD) → ZMod 2`,
`Ψ f = Λ (f 0) * Μ (f 1) * ∏ (i : Fin n', 2 ≤ i.val), ν (f i)` and let
`Φ := PiTensorProduct.lift Ψ`. Multilinearity is E3's scaling laws plus `rho`
multiplicativity.

**E5 — `τ ≠ 0` and `theta τ = 0`.** With
`a := fun i => if i = 0 then t_mul_p else if i = 1 then p_elt else 1` and `b` the same
with the first two entries swapped (elements of `↥IntD` by C2), set
`τ := tprod ↥Dom a - tprod ↥Dom b`. Then `Φ τ = Λ(tp)Μ(p) - Λ(p)Μ(tp) = 0 - 1 = 1 ≠ 0`,
so `τ ≠ 0`. And by frozen #5,
`theta τ = aeval (X 0) (C tK * p) * aeval (X 1) p * ∏_{i≥2} 1
        - aeval (X 0) p * aeval (X 1) (C tK * p) = C tK * (…) - C tK * (…) = 0`
(pull the constant `tK` out of `aeval`, then `sub_self`).

**E6 — `theta_not_injective` (#14).** `theta τ = 0 = theta 0` with `τ ≠ 0`.

> **Cheat watch (Stage E).** (i) ★ `τ ≠ 0` must be proved by exhibiting the functional
> `Φ`; "`tprod a ≠ tprod b` because `a ≠ b`" is **false** in a tensor product and is the
> single most likely fake proof here. (ii) `Λ, Μ` must come from #11–#13 — do not
> postulate a functional with prescribed values (that is assuming the theorem), and do
> not weaken to "`R/𝔪R` has dimension ≥ 2 for some reason". (iii) The `n ≥ 2` case must
> use the *same* `τ` padded with `1`s and the `ν`-factors: do not prove only `n = 2` and
> claim `∀ n`. (iv) Do not replace `¬Injective` by "`ker ≠ ⊥` for `n = 2`". (v) Guardrail:
> `example : Φ (tprod ↥Dom a) = 1` and `example : Φ (tprod ↥Dom b) = 0`, which catch a
> mis-ordered `Λ`/`Μ`.

### Stage F — failure of surjectivity (`Proofs/Surjectivity/`)

Goal: frozen `bigP_not_mem_range` (#15) and `theta_not_surjective` (#16). Sketch section
"Failure of Surjectivity".

**F1 — the mixed finite difference.** For `N : ℕ` let `w N : Fin (n+2) → K` be the point
`(u1 N, u1 N, 0, …, 0)`, and define the four evaluation points obtained by replacing the
0th and/or 1st coordinate with `0`. Set
`Δ N : MvPolynomial (Fin (n+2)) K →ₗ[↥Dom] K`,
`Δ N F = F(u,u,0…) - F(u,0,0…) - F(0,u,0…) + F(0,0,0…)` (a `↥Dom`-linear combination of
four `MvPolynomial.eval`s, each `↥Dom`-linear).

**F2 — `range (theta (n+2)) ≤ EvMv` where `EvMv := {F | ∀ᶠ N, Δ N F ∈ maxPow 2}`.**
`EvMv` is a `↥Dom`-submodule (same argument as D4). By
`PiTensorProduct.induction_on`/`LinearMap.range_le_iff` it suffices to check a pure
tensor, where frozen #5 gives `F = ∏ i, aeval (X i) (f i)` and the four evaluations
factor:
`Δ N F = (∏_{i≥2} (f i).eval 0) * ((f 0).eval (u1 N) - (f 0).eval 0) * ((f 1).eval (u1 N) - (f 1).eval 0)`.
The first factor lies in `Dom` (each `(f i).eval 0 ∈ Dom`), and each of the other two
lies in `𝔪` eventually by **D.3**. Hence `Δ N F ∈ Dom·𝔪·𝔪 ⊆ 𝔪²` eventually.
*(This telescoping identity is the whole "mixed finite-difference argument" of the
sketch; prove it as a separate algebraic lemma `mixed_difference_prod`.)*

**F3 — `bigP n ∉ EvMv`.** `Δ N (bigP n) = g.eval (u1 N * u1 N) - g.eval 0 - g.eval 0 +
g.eval 0 = g.eval ((u1 N)²)` (using C5's `bigP_eval` and `g.eval 0 = 0`). Compute
`g.eval y = q.eval y * (q.eval y + 1)` with `y = (u1 N)²`: `q.eval y = y(y+1)/π` has
numerator with exactly **one** factor of `t` (`y = t²(t+1)^{2N}`, so `y(y+1)/π` has
`t²/t = t¹`), and `q.eval y + 1` has none; so `π² ∤` the numerator and
`g.eval ((u1 N)²) ∉ maxPow 2` — for **every** `N ≥ 1`, which contradicts an eventual
statement.

**F4 — `bigP_not_mem_range` (#15)** is F2 + F3, and **`theta_not_surjective` (#16)** is
`⟨bigP n, bigP_mem_intMv n, bigP_not_mem_range n⟩`.

> **Cheat watch (Stage F).** (i) ★ The contradiction must use the frozen
> `maxSmulInt`-free formulation: `F ∈ range θ` means `F = θ x` for **some** `x` in the
> tensor power, not "`F` is a single product `f(X)h(Y)`" — hence the induction in F2 is
> mandatory. (ii) `Δ` must be the **mixed second difference** (all four terms); dropping
> a term makes F2 false. (iii) Do not weaken #16 to "`θ` is not surjective onto
> `K[X₁..Xₙ]`" — that is trivially true and answers nothing; the witness must be proved
> to lie in `Int(Dⁿ)` (#10). (iv) The extra variables must be handled by evaluating them
> at `0` *inside the proof*; do not redefine `bigP` to live in 2 variables and claim the
> general `n`. (v) Guardrail: `example : g.eval ((u1 1)^2) ∉ maxPow 2` and
> `example : g.eval ((u1 1)^2) ∈ maxSet`.

### Stage G — the headline (`Proofs/Headline/`)

**G1 — `theta_not_injective_not_surjective` (#17).** `fun n => ⟨theta_not_injective n,
theta_not_surjective n⟩`. Require a clean `#print axioms` here and at the end of every
stage above.

> **Cheat watch (Stage G).** The headline is a conjunction over **all** `n : ℕ` (i.e.
> all `n ≥ 2`). It must be assembled from #14 and #16 as frozen — not re-proved for a
> single `n`, and not restated with an extra hypothesis. A `#print axioms
> Prob20.Solution.theta_not_injective_not_surjective` showing anything beyond
> `propext, Classical.choice, Quot.sound` means the project is **not** done.

### Discharge & Solution (after the frozen theorems are proved)

In `Prob20/Solution.lean`, restate each frozen theorem **verbatim** in
`namespace Prob20.Solution` and set it `:= <name>_proof` (the sorry-free
declaration from `Proofs/`). In `Prob20/Discharge.lean`, for each pair write
`example : @Prob20.<name> = @Prob20.Solution.<name> := rfl` — this compiles **iff** the
proof has *exactly* the frozen proposition (machine-checked no-drift). `verify.py`
checks both modules build and that `#print axioms Prob20.Solution.<name>` is clean for
every frozen name.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems, skeleton builds, pins recorded)
      │
      ├────────────────────────────────┐
      ▼                                ▼
Stage A  (Domain: T, 𝔪ʲ, Dom,     Stage B  (Theta: Int, Intⁿ, θₙ,
          #1 #2 #3 #4)                      #5 #6)          ← independent of A
      │                                │
      ▼                                │
Stage C  (KeyPolys: #7 #8 #9 #10) ◄────┘
      │
      ▼
Stage D  ★ MILESTONE (Vanishing: D.3 key lemma, #11 #12 #13)
      │
      ├───────────────► Stage E  (Injectivity: #14)   ─┐
      │                                                │  (E and F independent
      └───────────────► Stage F  (Surjectivity: #15 #16)┘   → run in parallel)
                                                        │
                                                        ▼
                                            Stage G  HEADLINE #17
                                            (#print axioms clean)
                                                        │
                                                        ▼
                                       Discharge.lean + Solution.lean
```

- **Independent / parallelizable:** A and B can start simultaneously (B needs only D5–D7
  from `Defs.lean`); C needs A5 and B1; **E and F are independent of each other** and are
  the natural 2-worker split once D lands. Within A, the four frozen theorems
  (#1–#4) are independent of one another after A1–A4.
- **Milestone:** the end of **Stage D**. Once `p_not_mem_max_int` and its two siblings are
  `✅`, the mathematically novel part of the problem is done and both payoffs are
  bookkeeping. D.3 (`eval_sub_eval_zero_mem_max`) is the single lemma to get right; it is
  reused verbatim in F2.
- **Hardest engineering (budget accordingly):** Stage B4 (`theta_mem_intMv`, the
  `PiTensorProduct.induction_on` + `aeval`/`eval` commutation) and Stage E2–E4 (the
  quotient `V`, its `ZMod 2`-module structure, `LinearMap.exists_extend`, and the
  `PiTensorProduct.lift` of a `ZMod 2`-valued multilinear map). Neither is deep, both are
  API-friction; expect the majority of iterations there. Stage D is the hardest
  *mathematics* but the shortest Lean.

---

## Notes, risks, and cheats to watch out for

These are **general anti-cheat principles** — keep them, and the problem-specific traps
follow below them.

- **★ NEVER assume something as a hypothesis (the cardinal rule).** Every frozen
  theorem must be hypothesis-free wherever the source claim is unconditional.
  Forbidden moves: adding `(h : …)` to a frozen statement; proving a `∀ x`
  (or `∀ x y`) claim only for generators / a finite subset and claiming the
  general case; replacing an equality with a one-sided inclusion. If a sub-proof
  seems to need an assumption, **derive it or restructure** — do not weaken the
  statement. (Downstream stages typically instantiate these at *arbitrary*
  elements, so a quiet weakening breaks the assembly silently.)

- **Keep every predicate the textbook definition — do not soften it.** Quantifiers
  must match the source exactly: `Int(D)` quantifies over **all** `d ∈ D`, `Int(Dⁿ)`
  over **all** `v ∈ Dⁿ`, `𝔪·Int(D)` is the span of **all** products, and the headline is
  over **all** `n ≥ 2`. A softened predicate can make the headline vacuous.

- **Get the modeling right once, in SETUP, and freeze it.** A dropped or extra
  relation/hypothesis in a frozen definition silently changes the object and can
  break the proof downstream. Validate the core modeling facts *before* freezing, with
  small guardrail `example`s: `piK ∈ maxSet`, `(1:K) ∉ maxSet`, `tK ∈ T`, `tK ∉ Dom`,
  `piK * tK ∈ Dom`, `p.eval piK ∈ maxSet`. If `tK ∈ Dom` ever typechecks as `True`, the
  domain collapsed to `T` and every frozen statement below is wrong.

- **Discharge ring/structure axioms once — never `sorry` them.** All ring structure here
  is inherited (`RatFunc`, `Polynomial`, `MvPolynomial`, `Subring`, `Subalgebra`,
  `PiTensorProduct`). If you feel the urge to `sorry` associativity, distributivity, or
  a `Submodule` closure law, you modeled the object wrong.

- **Keep module-side and ring-side objects distinct.** This project mixes four scalar
  rings — `𝔽₂`, `↥Dom`, `↥T`, `K` — over the same carrier `K` / `K[X]`. Fix in
  `Defs.lean` which submodule is over which (`maxPow j : Submodule ↥T K`,
  `maxSmulInt : Submodule ↥Dom (Polynomial K)`) and convert only through
  `Submodule.restrictScalars` with an explicit `IsScalarTower`. Conflating `↥Dom`- and
  `↥T`-spans is the most likely *silent* modeling bug here (`𝔪·Int(D)` over `T` would be
  a strictly larger module and would make #11–#13 **false**).

- **`decide` budget — and `native_decide` is BANNED.** `decide` is appropriate for
  `ZMod 2` case splits and for the four `Fin 2 → ZMod 2` combinations in E2. It is
  **not** appropriate for anything involving `RatFunc`, `Polynomial K`, `Subring`
  membership, or `PiTensorProduct` — those are `noncomputable` and will not reduce.
  `native_decide` adds a compiler-trust axiom and would dirty `#print axioms` — never
  use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen during proving (pinned in `scripts/frozen.sha256`). If a
  *definition* seems missing, it belongs in a `Proofs/` support file. If a
  *statement* seems wrong, stop and re-read `SKETCH.md`.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no `native_decide`/
  `ofReduceBool`. `USER_NOTES.md` for this problem permits **no** assumed certificates,
  so `scripts/ALLOWED_AXIOMS.txt` is empty and **no `axiom` declaration may appear
  anywhere in this project.** `Classical.choice` will appear (via
  `LinearMap.exists_extend`, `Basis.mk`, and `noncomputable` definitions) and that is
  fine.

- **Assumed certificates go in as `axiom`s, never as hypotheses** — and here, not at
  all: `USER_NOTES.md` says "None — no assumed axioms". Do not add one, and do not edit
  `USER_NOTES.md` (the user owns it). If a stage seems to require an assumed fact,
  append a `⚠️` PROGRESS entry instead.

**Problem-specific traps.**

1. **The `∀ᶠ N` in the key lemma is load-bearing.** `f.eval u - f.eval 0 ∈ 𝔪` is proved
   only for the *specific* test points `u1 N` / `u0 N` with `N` large. It is **not**
   known for all `u ∈ 𝔪`, and assuming it would be assuming a much stronger (possibly
   false) statement. Any proof of D.3 that does not mention `N` is wrong.

2. **`𝔪` vs `𝔪²`.** Every non-membership in this project is an "exactly one factor of
   `t` (or of `t+1`)" statement: the witnesses *do* lie in `𝔪` and fail only in `𝔪²`.
   Off-by-one in the exponent of `π` silently turns a true statement into a false one
   (or into a trivial one). Recompute the two factorizations by hand before trusting a
   `simp`: `p.eval (t(t+1)ᴺ) = t(t+1)ᴺ·(t(t+1)ᴺ+1)`, and with `y = (t(t+1)ᴺ)²`,
   `q.eval y = y(y+1)/π = t(t+1)^{2N-1}(y+1)` and `g.eval y = (q.eval y)·(q.eval y + 1)`
   — the point in both cases being *exactly one* factor of `t`, since `y+1` and
   `q.eval y + 1` are units at `t`.

3. **`tp` needs the swapped test family.** `p` and `(t+1)p` are separated by `u1 N =
   t(t+1)ᴺ`; `tp` is **not** — it needs `u0 N = tᴺ(t+1)`. A worker who "refactors the
   three proofs into one" will produce a false lemma or a stuck goal. This is recorded
   as a `📝` decision in Stage D6.

4. **θ could be trivialized.** If `theta` were defined (or re-proved) as anything other
   than `lift (f ↦ ∏ fᵢ(Xᵢ))`, the headline would be worthless — the zero map is
   neither injective nor surjective. `theta_apply_tprod` (#5) is the frozen guard; treat
   any failure to prove it as a SETUP bug requiring a re-freeze, never as something to
   route around.

5. **Non-surjectivity must be *onto `Int(Dⁿ)`*.** The witness `bigP` must be certified
   by #10 to lie in `Int(Dⁿ)`. "Not surjective onto `K[X₁..Xₙ]`" is trivial and answers
   nothing.

6. **The witness's extra adjectives are deliberately out of scope.** `SKETCH.md`'s "Main
   Result" describes `D` as *one-dimensional Noetherian local*. We freeze `D_isDomain`
   (#1), `D_isLocalRing` (#3), the residue-field statement (#2) and `D_isFractionRing`
   (#4) — everything that is needed for `Int(D)`, `Int(Dⁿ)` and `θₙ` to be the textbook
   objects and for the answer to Problem 20 to be complete. **"Noetherian" and
   "dimension one" are not frozen**: they are properties of the particular witness, not
   part of Problem 20's question ("is θₙ always injective / surjective?"), and proving
   them would require Eakin–Nagata and `ringKrullDim` API for no gain in the answer.
   This is a *scope* decision, recorded here so no agent mistakes it for a weakening:
   no frozen statement is weaker than the corresponding sketch claim. Do **not** add
   these as hypotheses anywhere; if a future user wants them, they are a new stage, not
   an edit to a frozen file.

7. **The headline uses an explicit witness, not a `∃ (D : Type) …`.** The frozen
   headline is about the concrete `Prob20.Dom`, with `Int`/`θ` defined generically
   (D5–D7) and instantiated at it. This is *stronger* than an existential over domains
   (it exhibits the witness) and avoids `∃`-bound instance arguments, which are painful
   and error-prone in Lean. It is a complete negative answer to both questions of
   Problem 20 precisely **because** `IntPoly`, `IntMv`, `theta` are the general
   definitions — never replace them by `Dom`-specific ad-hoc versions.

8. **Characteristic 2 hides sign errors.** `-1 = 1`, `x - y = x + y`, `t + 1 = t - 1`.
   This is convenient but it means a sign slip cannot be detected by inspection; prefer
   `sub` forms that match Mathlib lemma statements and let `ring`/`simp` normalize.

