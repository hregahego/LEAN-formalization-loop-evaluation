# Blueprint: a positive definite weighted tree with a unique low-weight vertex contains an irreducible vertex

A roadmap for formalizing, in **Lean 4 + Mathlib**, the result in `SKETCH.md`.
The whole argument is a chain of inductions over *rooted* weighted trees. We
model a finite weighted tree as a **labelled rooted inductive tree** `RTree`
(labels in `ℕ`, weights in `ℤ`), read its lattice `L(T)` off as integer-valued
functions on labels, and define the *capacity* `γ(C)` by the Schur recursion
`γ(node w c) = 1 / (w − Σ γ(cᵢ))` rather than by inverting a matrix. Every
lemma of the sketch is then a structural induction on `RTree`, and the one place
where "rooted" would lose generality — Theorem 1 pivots at the unique bad vertex
`v`, not at whatever vertex the presentation happens to be rooted at — is
repaired by an explicit **re-rooting** stage that produces an `RTree` rooted at
any prescribed vertex carrying *literally the same* bilinear form (the labels
never move, only the parent/child orientation does).

- **Headline target (frozen theorem `tree_has_irreducible_vertex`).** For every
  `T : RTree` whose vertex labels are `Nodup`, whose form is positive definite
  (`PosDef T`), and which has a vertex `v` that is the **unique** vertex with
  `wt T u < deg T u`, there is a vertex `u ∈ verts T` whose basis vector is
  irreducible: `Irred T (basis u)`. All of `verts`, `wt`, `deg`, `PosDef`,
  `Irred`, `basis` are frozen in `Defs.lean`. The pivoted half-statement
  `pointed_root_irreducible` (same conclusion, hypothesis "every non-root vertex
  `u` satisfies `deg T u ≤ wt T u`") is frozen on its own and is what the
  re-rooting theorem `exists_reroot_at` is glued to.
- **Recommended intermediate milestone (prove first):** `rooted_estimate` —
  Lemma 3 of the sketch, `0 ≤ B C x x − (2k+1)·x(ρ) + γ(C)·k·(k+1)` for every
  admissible rooted `C`, every integer vector `x` and every `k : ℤ`. It is the
  mathematical heart: everything after it (Corollary 1, the `p ≥ 1` and `p = 0`
  cases of Theorem 1) is bookkeeping on top of it, and it is citable on its own.
- **Setting / ground assumptions:** Everything is finite and combinatorial.
  Coefficients: the lattice is `ℕ → ℤ` (integer vectors indexed by vertex
  labels); capacities and the auxiliary "dual" vectors live in `ℚ`. **No
  analysis, no ℝ, no matrices, no `Matrix.det`/`Matrix.inv`, no `SimpleGraph`,
  no `Finset` cardinality arguments** — the tree is an inductive datatype and all
  sums are `List.sum`. There is one genuine inequality-with-cases argument
  (`τ ∉ (k, k+1)` versus `k < τ < k+1`) and one denominator-clearing argument
  (positive definiteness over ℤ ⇒ over ℚ); nothing else needs ordered-field
  machinery beyond `linarith`/`nlinarith`.

> **Why this is tractable.** Every object in the sketch that looks analytic is
> actually a rational recursion: the capacity is `1/(w − Σγᵢ)`, the "dual vector"
> `ρ^#` is a recursively-defined `ℕ → ℚ`, and `dist(τ, ℤ)` is only ever compared
> against **one explicit integer** `M = w(ρ)·a − Σ sᵢ`, so no `Int.fract`/floor
> API is needed. The real risk is **mis-modeling**, in three specific places.
> (i) *Nonzero-ness*: a lattice vector is `ℕ → ℤ`, so "x ≠ 0" must mean
> `NonzeroOn T x` (nonzero at some vertex **of `T`**) — using `x ≠ 0` as
> functions would let junk supported off the tree act as a witness and would make
> the headline false. (ii) *Reducibility*: the decomposition `x = a + b` must be
> required only **on `verts T`**, otherwise the ∃-witness set shrinks and `Irred`
> becomes a strictly weaker (easier) claim. (iii) *Rootedness*: `pointed_root_irreducible`
> alone is **not** the theorem — the sketch's `v` is an arbitrary vertex, so
> `exists_reroot_at` is mandatory, not decoration.

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
lake +leanprover/lean4:v4.31.0 new TreeIrred math
cd TreeIrred
# pin Mathlib in lakefile.toml + lake-manifest.json to the rev whose
# lean-toolchain is exactly v4.31.0 (copy Mathlib's own lean-toolchain file
# into ./lean-toolchain so the two agree byte for byte), then:
lake exe cache get
lake build            # must succeed on the bare skeleton before anything else
```

Layout (every project follows this shape):

```
<project-dir>/
  TreeIrred/
    Defs.lean          -- FROZEN after this stage: every object the proof needs
    Theorems.lean      -- FROZEN after this stage: the 13 frozen statements (sorry)
    Proofs/
      Model/           -- Stage A: form/verts/edges API, Gram-matrix sanity
      NormOne/         -- Stage B: Lemma 1 for an abstract integral lattice
      Capacity/        -- Stage C: γ recursion, 0 < γ < 1  (Lemma 2)
      PosDef/          -- Stage D: rational form, dual vector ρ^#, positive definiteness
      RootedEstimate/  -- Stage E: Lemma 3, the mathematical heart
      RootBound/       -- Stage F: Corollary 1
      Reroot/          -- Stage G: pivot / rerootAt, form-invariance
      Pointed/         -- Stage H: Theorem 1 with the bad vertex at the root
      Main/            -- Stage I: the headline, bad vertex arbitrary
    Discharge.lean     -- pairs each frozen statement with its proof via `@Frozen = @Proof := rfl`
    Solution.lean      -- restates each frozen theorem in `TreeIrred.Solution`, proven
  TreeIrred.lean       -- imports everything
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

All support declarations live in `namespace TreeIrred` (never shadow a frozen
name). The frozen theorems are the only "theorem-facing" surface;
`Solution.lean` re-exposes each as `TreeIrred.Solution.<name>` after it is
proven, and `Discharge.lean` machine-checks that each proof has *exactly* the
frozen type (`@Frozen = @Proof := rfl`).

### 2. Freeze the Definitions (`Defs.lean`)

Define every object the proof needs, **in dependency order**. **Make decisive
modeling choices here and write them down — they cannot change later.**

`Defs.lean` opens with `import Mathlib` and `namespace TreeIrred`.

**D1 `RTree` — the labelled rooted weighted tree.**

```lean
inductive RTree : Type
  | node (label : ℕ) (weight : ℤ) (children : List RTree)

def RTree.root    : RTree → ℕ           | .node a _ _ => a
def RTree.wtRoot  : RTree → ℤ           | .node _ w _ => w
def RTree.kids    : RTree → List RTree  | .node _ _ c => c
```

> **MODELING DECISION (D1).** A finite weighted tree is presented as a *labelled
> rooted* inductive tree: each node carries a vertex **label** `a : ℕ` and a
> **weight** `w : ℤ`, and the child list is a `List RTree`. Three choices are
> being made and are binding.
> *(a) Rooted inductive vs. graph.* The entire sketch (Lemmas 2, 3, Corollary 1,
> Theorem 1) is a recursion "root + list of child subtrees". Modelling `T` as a
> `SimpleGraph`/`Fin n` adjacency matrix would force us to build connected
> components of `T \ {v}` and re-derive the recursion; the inductive type *is*
> that recursion. **No generality is lost**: every finite weighted tree is the
> underlying tree of some `RTree` (root it anywhere), and Stage G proves that
> re-rooting changes nothing we ever measure.
> *(b) Labels, not addresses.* Nodes carry explicit `ℕ` labels and the lattice is
> `ℕ → ℤ`, **not** `List ℕ`-addresses and not a dependent `Vec : RTree → Type`.
> This is the decision that makes re-rooting cheap: `pivot` permutes the
> `vwts`/`edges` lists but never renames a vertex, so the bilinear form of the
> re-rooted tree is *literally the same function*, and no transport-of-structure
> is needed anywhere.
> *(c) Nested `List RTree` vs. mutual `RTree`/`RForest`.* We take the nested
> inductive so that all of Mathlib's `List` API (`map`, `flatMap`, `sum`, `Perm`,
> `countP`, `Nodup`, `eraseIdx`, `attach`) is available; the price is that
> recursive definitions need `c.attach` plus `decreasing_by … List.sizeOf_lt_of_mem`
> (or `termination_by structural`) and that we must hand-build the induction
> principle D2. A mutual `RForest` would give free induction but would force us
> to re-implement every list operation — rejected.

**D2 `RTree.recAll` — the induction principle.** The auto-generated `RTree.rec`
for a nested inductive carries two motives (`motive_1 : RTree → Sort`,
`motive_2 : List RTree → Sort`). Package it once, here, in the shape every proof
in this project uses:

```lean
@[elab_as_elim]
def RTree.recAll {motive : RTree → Sort*}
    (h : ∀ a w c, (∀ t ∈ c, motive t) → motive (.node a w c)) : ∀ t, motive t
```

> **MODELING DECISION (D2).** Built from `RTree.rec` with
> `motive_2 := fun c => ∀ t ∈ c, motive t` (nil case: `List.not_mem_nil`; cons
> case: `List.mem_cons` split). Frozen here because **every** later induction
> uses `induction T using RTree.recAll`; if it lived in a `Proofs/` file the
> stages could not run in parallel.

**D3 `vwts`, `verts`, `wt` — the vertex data.**

```lean
def vwts : RTree → List (ℕ × ℤ)
  | .node a w c => (a, w) :: c.attach.flatMap (fun t => vwts t.1)

def verts (T : RTree) : List ℕ := (vwts T).map Prod.fst
def wt (T : RTree) (u : ℕ) : ℤ := ((vwts T).lookup u).getD 0
```

> **MODELING DECISION (D3).** Vertices are collected as a **list** (order and
> multiplicity visible) rather than a `Finset`, because every sum in the form is
> a `List.sum` and because re-rooting is proved via `List.Perm`. `wt` is a
> `List.lookup` with default `0`: outside `verts T` the weight is `0` and is
> never read (the form only ever touches labels in `vwts`/`edges`). Genuine
> tree-hood — labels pairwise distinct — is **not** baked into the type; it is
> the hypothesis `(verts T).Nodup`, supplied wherever it is mathematically
> needed. Rejected alternative: a subtype bundling `Nodup`, which would make
> `pivot` and `rerootAt` carry proofs through every recursive call.

**D4 `edges`, `Adj`, `deg` — the unrooted combinatorics.**

```lean
def edges : RTree → List (ℕ × ℕ)
  | .node a _ c => c.map (fun t => (a, t.root)) ++ c.attach.flatMap (fun t => edges t.1)

def Adj (T : RTree) (u v : ℕ) : Prop := (u, v) ∈ edges T ∨ (v, u) ∈ edges T
def deg (T : RTree) (u : ℕ) : ℕ := (edges T).countP (fun e => e.1 = u || e.2 = u)
```

> **MODELING DECISION (D4).** `edges` lists each edge **once**, oriented
> parent → child. `Adj` symmetrises it, and `deg` is the number of incident
> edges — i.e. the degree `d_T(x)` of the *unrooted* tree, exactly as `SKETCH.md`
> uses it (the sketch's `d_T(x) = ch(x) + 1` identity for non-root `x` is then a
> **lemma**, Stage A, not a definition). Do **not** define `deg` as
> "number of children (+1)" — that would silently bake the rooting into the
> headline hypothesis and is the single easiest way to cheat this problem.

**D5 `Admissible` — the sketch's admissible rooted tree.**

```lean
def Admissible : RTree → Prop
  | .node _ w c => 2 ≤ w ∧ (c.length : ℤ) + 1 ≤ w ∧ ∀ t ∈ c, Admissible t
```

> **MODELING DECISION (D5).** `SKETCH.md` defines *admissible* as "positive
> definite **and** every weight ≥ 2 **and** `w(x) ≥ ch(x) + 1`". We **drop the
> positive-definiteness clause**: it is redundant, and Stage D *proves* it
> (`admissible_posDef`). Dropping a conjunct from a hypothesis makes every lemma
> that assumes `Admissible` **strictly stronger**, and makes the one place that
> must *establish* admissibility (Stage H) strictly easier — so this is a
> strengthening, never a weakening. `c.length` is `ch(ρ)`, the number of children
> of the root; the `∀ t ∈ c` clause propagates both conditions to every vertex.

**D6 `form`, `B`, `BQ`, `basis` — the lattice and its bilinear form.**

```lean
def form {R : Type} [CommRing R] (T : RTree) (x y : ℕ → R) : R :=
  ((vwts T).map (fun p => (p.2 : R) * x p.1 * y p.1)).sum
    - ((edges T).map (fun e => x e.1 * y e.2 + x e.2 * y e.1)).sum

abbrev B  (T : RTree) (x y : ℕ → ℤ) : ℤ := form T x y
abbrev BQ (T : RTree) (x y : ℕ → ℚ) : ℚ := form T x y

def basis {R : Type} [CommRing R] (u : ℕ) : ℕ → R := fun v => if v = u then 1 else 0
```

> **MODELING DECISION (D6).** The lattice `L(T)` is modelled as **all** functions
> `ℕ → R`; the form reads only labels occurring in `vwts T`/`edges T`, so two
> functions agreeing on `verts T` give the same value (`form_congr`, Stage A) —
> the model is "functions modulo off-tree junk", and every statement that
> mentions equality or nonzero-ness of lattice vectors must therefore be phrased
> **relative to `verts T`** (see D7). The edge summand
> `x e.1 * y e.2 + x e.2 * y e.1` is **symmetric under swapping the endpoints**;
> this is deliberate and is what makes `pivot` (which reverses exactly one edge)
> preserve the form on the nose. The form is defined once, generically over
> `[CommRing R]`, and instantiated at `ℤ` (the lattice) and `ℚ` (capacities,
> dual vectors, Schur positivity) — one definition, one set of algebraic lemmas,
> and a single cast lemma `form_cast` bridging them. Rejected alternatives:
> `Finsupp` (buys nothing, costs `Finsupp.sum` friction) and a `Matrix`
> presentation (would drag in `Matrix.inv` for the capacity — precisely what the
> Schur recursion lets us avoid).

**D7 `NonzeroOn`, `PosDef`, `Reducible`, `Irred` — lattice-relative predicates.**

```lean
def NonzeroOn (T : RTree) (x : ℕ → ℤ) : Prop := ∃ u ∈ verts T, x u ≠ 0

def PosDef (T : RTree) : Prop := ∀ x : ℕ → ℤ, NonzeroOn T x → 0 < B T x x

def Reducible (T : RTree) (x : ℕ → ℤ) : Prop :=
  ∃ a b : ℕ → ℤ, NonzeroOn T a ∧ NonzeroOn T b ∧
    (∀ u ∈ verts T, x u = a u + b u) ∧ 0 ≤ B T a b

def Irred (T : RTree) (x : ℕ → ℤ) : Prop := ¬ Reducible T x
```

> **MODELING DECISION (D7) — the most delicate one in the project.** "`a ≠ 0` in
> `L(T)`" is `NonzeroOn T a`, **not** `a ≠ (0 : ℕ → ℤ)`: a function supported
> entirely off the tree is zero in `L(T)` but nonzero as a function, and
> admitting it as a witness would make `Irred` false for every vertex (take
> `a = basis v`, `b =` off-tree junk, `B T a b = 0 ≥ 0`). Symmetrically, the
> splitting condition is `∀ u ∈ verts T, x u = a u + b u` and **not**
> `x = a + b`: `Reducible` is an `∃`, so restricting the witnesses would make
> `Irred` *easier* to prove — a silent weakening of the headline. `PosDef` is
> stated over **ℤ** (the weakest, most conservative reading of "the associated
> form is positive definite"); the equivalent ℚ-statement is *derived* in Stage D
> (`posDefQ_of_posDef`), never assumed.

**D8 `gamma` — the capacity.**

```lean
def gamma : RTree → ℚ
  | .node _ w c => 1 / ((w : ℚ) - (c.attach.map (fun t => gamma t.1)).sum)
```

> **MODELING DECISION (D8).** `SKETCH.md` *defines* `γ(C) = (Q_C⁻¹)_{ρρ}` and
> *proves* the recursion `γ = 1/(w(ρ) − Σ γ(Cᵢ))` by a Schur complement. We
> **take the recursion as the definition** and discharge the obligation in the
> other direction: the frozen theorem `capacity_spec` exhibits a rational vector
> `u` with `BQ C u y = y (root C)` for **all** `y` and `BQ C u u = gamma C` —
> i.e. `u = Q_C⁻¹ e_ρ` and `γ = (Q_C⁻¹)_{ρρ}`, which is the sketch's definition
> stated without ever mentioning a matrix or its inverse. This is what keeps the
> definitional swap honest, and it is a **binding obligation**: `capacity_spec`
> is not optional decoration. If `w − Σγᵢ = 0` the Lean division convention
> gives `gamma = 0`; that case never occurs under `Admissible` (Stage C's
> `capacity_denom_pos`) and no lemma may rely on it.

**D9 `LatRed`, `LatIrred` — reducibility in an abstract integral lattice.**

```lean
def LatRed {M : Type} [AddCommGroup M] (F : M → M → ℤ) (x : M) : Prop :=
  ∃ a b : M, a ≠ 0 ∧ b ≠ 0 ∧ x = a + b ∧ 0 ≤ F a b

def LatIrred {M : Type} [AddCommGroup M] (F : M → M → ℤ) (x : M) : Prop := ¬ LatRed F x
```

> **MODELING DECISION (D9).** Lemma 1 of the sketch is stated for an arbitrary
> positive definite integral lattice, so we render it that way: an
> `AddCommGroup M` with an integer-valued form `F`. Freeness/finite rank are
> *not* assumed (the proof does not use them, and omitting them strengthens the
> lemma). Here `a ≠ 0` genuinely is the group's zero — there is no ambient
> vertex set — which is exactly why the tree-side predicates in D7 must be
> separate definitions rather than instances of this one.

> **Cheat watch (Defs).** Every predicate must be the **genuine textbook
> notion**, quantified exactly as `SKETCH.md` states it. Concretely, for this
> problem: (i) `deg` must be the unrooted degree read off `edges`, never
> "children + 1"; (ii) `NonzeroOn`/`Reducible` must be relative to `verts T`
> (D7) — both the "`a ≠ 0`" and the "`x = a + b`" clauses; (iii) `Admissible`
> may drop positive definiteness (it is proved) but may **not** drop `2 ≤ w` or
> weaken `ch + 1 ≤ w` to `ch ≤ w`; (iv) `Reducible` requires `0 ≤ B T a b`, not
> `0 < B T a b`; (v) `gamma` is the recursion of D8 and its identification with
> `(Q_C⁻¹)_{ρρ}` is owed as `capacity_spec`. A "simplification" in any of these
> makes the headline vacuous.

### 3. Freeze the Theorems (`Theorems.lean`)

Write the **COMPLETE** list of frozen theorem statements, all `:= sorry`. After
writing them, `Theorems.lean` is frozen. Each statement must render a claim of
`SKETCH.md` faithfully and minimally, have a stable binding name, and typecheck.

```lean
import TreeIrred.Defs
namespace TreeIrred

-- 1 · model sanity: `form` really is the Gram matrix SKETCH.md describes
theorem form_gram_entries (T : RTree) (hnd : (verts T).Nodup) (u v : ℕ)
    (hu : u ∈ verts T) (hv : v ∈ verts T) :
    (u = v → B T (basis u) (basis v) = wt T u) ∧
    (u ≠ v → Adj T u v → B T (basis u) (basis v) = -1) ∧
    (u ≠ v → ¬ Adj T u v → B T (basis u) (basis v) = 0) := sorry

-- 2 · Lemma 1
theorem norm_one_irreducible {M : Type} [AddCommGroup M] (F : M → M → ℤ)
    (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
    (hsymm : ∀ x y : M, F x y = F y x)
    (hpd : ∀ x : M, x ≠ 0 → 0 < F x x)
    (x : M) (hx : F x x = 1) : LatIrred F x := sorry

-- 3 · Lemma 2, the capacity recursion
theorem capacity_node_formula (a : ℕ) (w : ℤ) (c : List RTree) :
    gamma (RTree.node a w c) = 1 / ((w : ℚ) - (c.map gamma).sum) := sorry

-- 4 · Lemma 2, the Schur denominator is positive
theorem capacity_denom_pos (C : RTree) (hC : Admissible C) :
    0 < (C.wtRoot : ℚ) - (C.kids.map gamma).sum := sorry

-- 5,6 · Lemma 2, 0 < γ(C) < 1
theorem capacity_pos (C : RTree) (hC : Admissible C) : 0 < gamma C := sorry
theorem capacity_lt_one (C : RTree) (hC : Admissible C) : gamma C < 1 := sorry

-- 7 · γ really is (Q_C⁻¹)_{ρρ}: the dual vector ρ# exists and has square γ
theorem capacity_spec (C : RTree) (hnd : (verts C).Nodup) (hC : Admissible C) :
    ∃ u : ℕ → ℚ, (∀ y : ℕ → ℚ, BQ C u y = y C.root) ∧ BQ C u u = gamma C := sorry

-- 8 · admissible ⇒ positive definite (the clause dropped from `Admissible`)
theorem admissible_posDef (C : RTree) (hC : Admissible C) : PosDef C := sorry

-- 9 · Lemma 3, the rooted estimate  ★ MILESTONE
theorem rooted_estimate (C : RTree) (hC : Admissible C) (x : ℕ → ℤ) (k : ℤ) :
    0 ≤ (B C x x : ℚ) - (2 * k + 1) * (x C.root : ℚ) + gamma C * k * (k + 1) := sorry

-- 10 · Corollary 1
theorem admissible_root_bound (C : RTree) (hC : Admissible C)
    (x : ℕ → ℤ) (hx : NonzeroOn C x) : 0 < B C x x - x C.root := sorry

-- 11 · re-rooting loses nothing
theorem exists_reroot_at (T : RTree) (u : ℕ) (hu : u ∈ verts T) :
    ∃ T' : RTree, T'.root = u ∧ (verts T').Perm (verts T) ∧
      (∀ v : ℕ, wt T' v = wt T v) ∧ (∀ v : ℕ, deg T' v = deg T v) ∧
      (∀ x y : ℕ → ℤ, B T' x y = B T x y) := sorry

-- 12 · Theorem 1 with the bad vertex at the root
theorem pointed_root_irreducible (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :
    ∃ u ∈ verts T, Irred T (basis u) := sorry

-- 13 · Theorem 1  ★ HEADLINE
theorem tree_has_irreducible_vertex (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)
    (v : ℕ) (hv : v ∈ verts T)
    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :
    ∃ u ∈ verts T, Irred T (basis u) := sorry
```

Mapping to `SKETCH.md`:

| # | frozen name | renders |
| - | ----------- | ------- |
| 1 | `form_gram_entries` | the sketch's "`Q_C` is the Gram matrix of `C` in the vertex basis" (diagonal `w`, off-diagonal `−1` on edges, `0` otherwise) |
| 2 | `norm_one_irreducible` | Lemma 1 |
| 3 | `capacity_node_formula` | the displayed recursion of Lemma 2 |
| 4 | `capacity_denom_pos` | `w(ρ) − Σ γ(Cᵢ) > 0`, the inequality inside Lemma 2's induction |
| 5 | `capacity_pos` | `0 < γ(C)` |
| 6 | `capacity_lt_one` | `γ(C) < 1` |
| 7 | `capacity_spec` | the sketch's *definition* `γ(C) = (Q_C⁻¹)_{ρρ}`, plus `(ρ^#)² = γ` from Corollary 1's proof |
| 8 | `admissible_posDef` | the "positive definite" clause of *admissible*, proved rather than assumed |
| 9 | `rooted_estimate` | Lemma 3 |
| 10 | `admissible_root_bound` | Corollary 1 |
| 11 | `exists_reroot_at` | the sketch's "root `Cᵢ` at `ρᵢ`" / "orient every edge away from `ρ`" — the licence to choose where the tree is rooted |
| 12 | `pointed_root_irreducible` | Theorem 1's body, after the bad vertex has been made the root |
| 13 | `tree_has_irreducible_vertex` | Theorem 1 |

**Why these 13.** #9 is the decidable *heart* — Lemma 3 carries the whole
argument, and #10 is a three-line consequence of it (see Stage F). #3–#8 are the
capacity infrastructure that #9 consumes; #7 and #8 additionally discharge the
two definitional debts incurred in `Defs.lean` (that our recursive `γ` is the
sketch's matrix-inverse entry, and that our slimmed `Admissible` still implies
positive definiteness). #1 and #11 are the *faithfulness anchors* for the
model: #1 says the form we defined is the sketch's Gram matrix, #11 says our
rooted presentation is not a special case. #2 is the weight-one escape hatch,
#12 the assembled contradiction argument, and #13 the payoff.

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
## <UTC timestamp> — <stage/item, e.g. "Stage C · capacity_lt_one">
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
   collision-free). Stages A, B, C and G are mutually independent and are the
   natural first batch of four.
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

| Need                                              | Mathlib handle |
| ------------------------------------------------- | -------------- |
| finite vertex/edge collections, sums              | `List`, `List.sum`, `List.map`, `List.flatMap`, `List.sum_append`, `List.sum_map_add` |
| recursion through a nested `List` constructor     | `List.attach`, `List.sizeOf_lt_of_mem`, `decreasing_by`/`termination_by structural` |
| re-rooting invariance                             | `List.Perm`, `List.Perm.sum_eq`, `List.perm_append_comm`, `List.perm_middle`, `List.Perm.countP_eq`, `List.Perm.nodup_iff` |
| distinct vertex labels                            | `List.Nodup`, `List.Nodup.cons`, `List.nodup_append`, `List.disjoint_left` |
| degree as an incidence count                      | `List.countP`, `List.countP_append`, `List.countP_eq_zero` |
| weight lookup                                     | `List.lookup`, `Option.getD`, `List.lookup_cons` |
| rational arithmetic for `γ`                       | `ℚ` as a `LinearOrderedField`; `div_pos`, `one_div`, `div_lt_one`, `lt_div_iff₀`, `sub_pos` |
| clearing denominators (ℤ-PD ⇒ ℚ-PD)               | `Rat.den`, `Rat.den_dvd`, `Rat.num_div_den`, `Nat.lcm`, `List.foldr`, `Rat.den_dvd_iff`-style divisibility, `Int.cast_injective` |
| casting `B` (ℤ) into `BQ` (ℚ)                     | `Int.cast_sum`/`push_cast`, `Int.cast_mul`, `Int.cast_le`, `Int.cast_lt`, `exact_mod_cast` |
| the two-consecutive-integers / case inequalities  | `linarith`, `nlinarith`, `mul_nonneg`, `mul_nonpos_iff`, `abs_le`, `le_abs_self`, `neg_abs_le`, `abs_sub_comm`, `min_le_iff` |
| bilinear bookkeeping in the abstract lattice      | plain `AddCommGroup` API (`sub_eq_add_neg`, `neg_add_cancel`) — **no** `BilinForm` needed |
| generic-over-`R` form                             | `CommRing`, `Int.cast` (`IntCast R`), `Finset`-free `List.sum` lemmas |

The **two nontrivial dependencies** the project hinges on are (i) `List.Perm` and
its `sum`/`countP` transfer lemmas — they are what make Stage G (re-rooting)
cheap — and (ii) the ℚ ordered-field API used by `linarith`/`nlinarith` in
Stages C–F.

Machinery you can **avoid**: `Matrix`, `Matrix.det`, `Matrix.inv`, Schur
complements (the sketch's matrix computation is replaced by the `gamma`
recursion plus `capacity_spec`), `SimpleGraph`/`SimpleGraph.IsTree`/connected
components (replaced by the inductive `RTree`), `InnerProductSpace`/Cauchy–Schwarz
(Corollary 1 is derived from Lemma 3 at `k = 1` and `k = −1`; see Stage F), and
`Int.fract`/`round` (the distance-to-ℤ step is done against one explicit integer).

---

## Part 1 — New objects to define (all in `Defs.lean`, frozen)

| #  | Object | Role |
| -- | ------ | ---- |
| D1 | `RTree : Type` (+ `root`, `wtRoot`, `kids`) | labelled rooted weighted tree; the carrier of every induction |
| D2 | `RTree.recAll` | the "root + all children" induction principle used by every proof |
| D3 | `vwts`, `verts`, `wt` | vertex/weight list, vertex-label list, weight lookup |
| D4 | `edges`, `Adj`, `deg` | edge list (parent→child), symmetric adjacency, **unrooted** degree `d_T` |
| D5 | `Admissible : RTree → Prop` | `2 ≤ w` and `ch + 1 ≤ w` at every vertex (positive definiteness proved, not assumed) |
| D6 | `form {R} [CommRing R]`, `B`, `BQ`, `basis` | the Gram bilinear form over any `CommRing`, instantiated at ℤ and ℚ; vertex basis vectors |
| D7 | `NonzeroOn`, `PosDef`, `Reducible`, `Irred` | lattice-relative nonzero-ness, positive definiteness over ℤ, reducibility (`x = a + b` **on `verts T`**, `a·b ≥ 0`), irreducibility |
| D8 | `gamma : RTree → ℚ` | capacity via the Schur recursion `1/(w − Σ γᵢ)` |
| D9 | `LatRed`, `LatIrred` | reducibility/irreducibility in an abstract integral lattice (for Lemma 1) |

Objects deliberately **not** frozen (they are proof infrastructure and live in
`Proofs/`, so that a later stage may refine them): the dual vector `dual`
(Stage D), the one-step `pivot` and iterated `rerootAt`/`addrOf` (Stage G), and
the sub-child counter used by `admissible_of_deg` (Stage H). Every frozen
*statement* is expressible without them.

---

## Part 2 — Theorems and lemmas to prove (in order)

### Stage A — the form API and the Gram-matrix sanity check (`Proofs/Model/`)

Goal: the computational vocabulary every other stage speaks, plus frozen
`form_gram_entries`.

**A1 — `vwts_node`, `verts_node`, `edges_node`.** `@[simp]` unfolding lemmas
rewriting `c.attach.flatMap (fun t => f t.1)` into `c.flatMap f` (use
`List.attach`'s `map`/`flatMap` simp set, or prove
`c.attach.flatMap (fun t => f t.1) = c.flatMap f` once by induction on `c`).
Everything downstream should be able to `simp [verts_node, edges_node]`.

**A2 — `form_node`.** The expansion the whole sketch runs on:
`form (.node a w c) x y = w * x a * y a + (c.map (fun t => form t x y)).sum
   − (c.map (fun t => x a * y t.root + x t.root * y a)).sum`.
Proof: `simp [form, vwts_node, edges_node, List.sum_append, List.sum_map_add]`
plus `ring_nf`. This is the single most-used lemma in the project.

**A3 — algebraic lemmas.** `form_comm` (symmetry), `form_add_left`,
`form_add_right`, `form_neg_left`, `form_sub_left`, `form_zero_left`; each by
`induction T using RTree.recAll` + `A2` + `ring`, or directly from the
`vwts`/`edges` definition by `List.sum_map_add`.

**A4 — `form_congr` and `form_vanish`.** If `∀ u ∈ verts T, x u = x' u` then
`form T x y = form T x' y` (and symmetrically); if `∀ u ∈ verts T, x u = 0` then
`form T x y = 0`. Needs `edges_subset_verts`: both endpoints of every edge lie in
`verts T`. These are what make the "functions modulo off-tree junk" model work.

**A5 — `form_cast`.** `((B T x y : ℤ) : ℚ) = BQ T (fun u => (x u : ℚ)) (fun u => (y u : ℚ))`
by `push_cast` through the two `List.sum`s.

**A6 — local structure (all under `(verts T).Nodup`).** For `T = .node a w c`
and `t ∈ c`:
`verts_node_nodup_disjoint` (the `verts t` are pairwise disjoint and avoid `a`);
`wt_sub : u ∈ verts t → wt T u = wt t u`;
`deg_sub : u ∈ verts t → u ≠ t.root → deg T u = deg t u`;
`deg_subroot : deg T t.root = deg t t.root + 1`;
`deg_root : deg T a = c.length`;
`form_basis_sub : (∀ u ∈ verts t, x u = 0) → form t x y = 0` (a special case of A4).

**A7 — frozen `form_gram_entries`.** Diagonal: only the `(u,w)` entry of `vwts`
survives (`Nodup` kills duplicates) and no edge is a loop, so the value is
`wt T u`. Off-diagonal: the `vwts` sum vanishes, and each edge `e` contributes
`1` exactly when `{e.1, e.2} = {u, v}`; `Nodup` gives at most one such edge, so
the total is `−1` when adjacent and `0` otherwise.

> **Cheat watch (Stage A).** `form_gram_entries` is the anchor that says our
> `form` **is** the sketch's `Q_C`; do not "simplify" it by dropping `hu`/`hv`,
> by assuming `Adj` is decidable and collapsing the three conjuncts into one
> `if`-expression with a `Classical` instance (the frozen statement is fixed
> anyway), or by proving only the diagonal case. Do **not** prove `A4`
> (`form_congr`) with an extra hypothesis such as "`x` and `x'` agree
> everywhere" — the entire point is agreement on `verts T` **only**. Do not
> redefine `deg` in a `Proofs/` file as `children + 1`; `deg_sub`/`deg_subroot`
> must be *derived* from the frozen `edges`-based definition. Guardrail:
> `example : deg (.node 0 3 [.node 1 2 [], .node 2 2 []]) 0 = 2 := by decide` and
> `example : deg (.node 0 3 [.node 1 2 [.node 3 2 []]]) 1 = 2 := by decide`.

### Stage B — Lemma 1 in an abstract integral lattice (`Proofs/NormOne/`)

Goal: frozen `norm_one_irreducible`. **No dependencies** — can run in the first
parallel batch.

**B1 — frozen `norm_one_irreducible`.** Assume `LatRed F x`, i.e. `x = a + b`
with `a, b ≠ 0` and `0 ≤ F a b`. From `hadd` + `hsymm` derive
`F x x = F a a + 2 * F a b + F b b` (expand `F (a+b) (a+b)` twice, once in each
argument; additivity in the second argument comes from `hsymm` + `hadd`). With
`hpd a ha : 0 < F a a` and `hpd b hb : 0 < F b b` over **ℤ** we get
`F a a ≥ 1`, `F b b ≥ 1`, hence `F x x ≥ 2`, contradicting `hx : F x x = 1`.
`omega`/`linarith` closes it.

> **Cheat watch (Stage B).** The statement must stay at the abstract
> `AddCommGroup M` level — do **not** re-specialise it to `M := ℕ → ℤ` or to a
> tree, and do not add `[Module ℤ M]`, freeness, finite rank, or a `BilinForm`
> bundling; the sketch's Lemma 1 assumes only a positive definite *integral*
> form. Do not strengthen `0 ≤ F a b` to `0 < F a b`. The integrality step
> (`0 < F a a → 1 ≤ F a a`) is the whole content — it must come from `ℤ`, not
> from an added hypothesis `1 ≤ F a a`.

### Stage C — the capacity: Lemma 2 (`Proofs/Capacity/`)

Goal: frozen `capacity_node_formula`, `capacity_denom_pos`, `capacity_pos`,
`capacity_lt_one`. Depends only on `Defs.lean`.

**C1 — `capacity_node_formula`.** Rewrite `c.attach.map (fun t => gamma t.1)`
to `c.map gamma` (same helper as A1), then `rfl`/`simp [gamma]`.

**C2 — the simultaneous induction.** Prove by `RTree.recAll` the conjunction
`Admissible C → 0 < gamma C ∧ gamma C < 1` together with the denominator bound.
Concretely, for `C = .node a w c` with `hC : Admissible C`:
IH gives `∀ t ∈ c, 0 < gamma t ∧ gamma t < 1`; hence
`(c.map gamma).sum < c.length` (by `List.sum_lt_sum`-style induction on `c`, or
`List.sum_le_sum` with the strict version) and `0 ≤ (c.map gamma).sum`. With
`(c.length : ℤ) + 1 ≤ w` this yields `w − Σ γᵢ > w − c.length ≥ 1 > 0`, so
`gamma C = 1/(w − Σγᵢ) > 0` (`div_pos`) and `< 1` (`div_lt_one` with denominator
`> 1`). Split the result into the three frozen statements.
*Watch the `c = []` case*: the sum is `0` and `w ≥ 2` gives `γ = 1/w ≤ 1/2 < 1` —
the same computation, no separate base case needed.

> **Cheat watch (Stage C).** `capacity_lt_one` must hold for **every** admissible
> `C`, including `c = []`; do not prove it only for `c ≠ []` and patch the base
> case by assuming `w ≥ 3`. Do not weaken `< 1` to `≤ 1` — Stage E's final
> inequality `γ·α·β ≤ α·β` needs the strict form. `capacity_denom_pos` must be
> `0 < w − Σγᵢ`, not `0 ≤`, and must not be obtained by *assuming*
> `gamma C ≠ 0`. Do not add `(verts C).Nodup` here: none of Lemma 2 needs it,
> and an unnecessary hypothesis would have to be discharged in Stage H.

### Stage D — rational form, the dual vector `ρ^#`, positive definiteness (`Proofs/PosDef/`)

Goal: frozen `capacity_spec` and `admissible_posDef`; support lemmas
`psd_gamma`, `dual`, `dual_apply`, `posDefQ_of_posDef` that Stages F and H
consume. Depends on A + C.

**D1 — `dual : RTree → (ℕ → ℚ)`,** the vector `ρ^#`, scaled so it can recurse:

```lean
def dualScaled : RTree → ℚ → (ℕ → ℚ)
  | .node a w c, s => fun u =>
      if u = a then s * gamma (.node a w c)
      else (c.attach.map (fun t => dualScaled t.1 (s * gamma (.node a w c)) u)).sum
def dual (C : RTree) : ℕ → ℚ := dualScaled C 1
```

**D2 — `dual_apply` (the defining property).** For `(verts C).Nodup` and
`Admissible C`: `∀ y : ℕ → ℚ, BQ C (dualScaled C s) y = s * y C.root`, by
`RTree.recAll`. The computation, with `u = dualScaled C s`, `γ = gamma C`,
`γᵢ = gamma Cᵢ`: `u(ρ) = sγ`, `u(ρᵢ) = sγ·γᵢ` and `BQ Cᵢ u y = sγ · y(ρᵢ)` by IH,
so by `form_node`
`BQ C u y = w·sγ·y(ρ) − Σᵢ(sγ·y(ρᵢ) + sγγᵢ·y(ρ)) + Σᵢ sγ·y(ρᵢ) = sγ(w − Σγᵢ)·y(ρ) = s·y(ρ)`
using `γ·(w − Σγᵢ) = 1` (`capacity_node_formula` + `capacity_denom_pos`, so the
denominator is nonzero). `Nodup` is used twice: `u` vanishes off `verts C`
(`dual_vanish`, a companion induction) and the `if`-branch at `ρ` is not shadowed
by a child.

**D3 — frozen `capacity_spec`.** Take `u := dual C`. The first conjunct is D2 at
`s = 1`; the second is D2 applied with `y := u`, giving
`BQ C u u = u C.root = gamma C`.

**D4 — `psd_gamma` (support).** `Admissible C → ∀ (x : ℕ → ℚ) (t : ℚ),
0 ≤ BQ C x x − 2*t*x C.root + gamma C * t^2`, by `RTree.recAll`. Step: with
`a := x ρ`, apply the IH to each `Cᵢ` at parameter `a` to get
`BQ Cᵢ x x − 2*a*x ρᵢ ≥ −γᵢ*a²`; then by `form_node`
`BQ C x x ≥ (w − Σγᵢ)a² = a²/γ`, so the target is
`≥ a²/γ − 2ta + γt² = (a − γt)²/γ ≥ 0` (`div_nonneg`, `sq_nonneg`,
`capacity_pos`). *This subsumes the base case* (`c = []` gives `Σ = 0`).

**D5 — frozen `admissible_posDef`.** Two halves, both by `RTree.recAll`.
(i) `0 ≤ B C x x` for integer `x`: cast with `form_cast` and use D4 at `t = 0`.
(ii) `NonzeroOn C x → B C x x ≠ 0`: from `form_node`,
`B C x x = Σᵢ(B Cᵢ x x − 2a·sᵢ + γᵢa²) + a²/γ` (an identity in ℚ), each bracket
`≥ 0` by D4 and the last term `≥ 0`; if the total is `0` then `a = x ρ = 0` and
every bracket vanishes, so with `a = 0` each `B Cᵢ x x = 0`, and the IH forces
`x` to vanish on every `verts Cᵢ` — contradicting `NonzeroOn`. Combine: `0 ≤` and
`≠ 0` give `0 <`.

**D6 — `posDefQ_of_posDef` (support, used by Stage H).**
`PosDef T → ∀ x : ℕ → ℚ, (∃ u ∈ verts T, x u ≠ 0) → 0 < BQ T x x`.
Let `N : ℤ` be the `lcm` of `(x u).den` over `u ∈ verts T` (a `List.foldr Nat.lcm 1`
over `verts T`), so `N ≠ 0` and `(N : ℚ) * x u` is an integer for every
`u ∈ verts T`. Put `y u := ((N : ℚ) * x u).num`. Then `y` agrees with `N • x` on
`verts T`, so by `form_congr` + bilinearity `((B T y y : ℤ) : ℚ) = N² * BQ T x x`;
`NonzeroOn T y` holds at the witness, so `0 < B T y y`, and `N² > 0` gives the
claim.

> **Cheat watch (Stage D).** `capacity_spec`'s first conjunct is `∀ y : ℕ → ℚ` —
> proving it only for `y = dual C`, only for basis vectors, or only for `y`
> supported on `verts C` is a weakening that destroys its role as the
> identification `γ = (Q_C⁻¹)_{ρρ}`. `admissible_posDef` must produce **strict**
> positivity from `NonzeroOn` (not `0 ≤`, and not "`x ≠ 0` as a function"); the
> `≠ 0` half is the real content — do not stop at `psd_gamma`. In D6 do not
> "simplify" by *assuming* `x` is integer-valued or by adding a denominator
> hypothesis: clearing denominators is the whole lemma. Never introduce a
> `noncomputable` choice of `N` via `Classical.choice` over an unbounded set —
> `N` is an explicit `List.foldr lcm`.

### Stage E — the rooted estimate, Lemma 3 (`Proofs/RootedEstimate/`) ★ MILESTONE

Goal: frozen `rooted_estimate`. Depends on A + C. This is the mathematical
heart; budget the most effort here.

Induction by `RTree.recAll` on `C = .node a w c`, with `hC : Admissible C`,
`x : ℕ → ℤ`, `k : ℤ`. Notation: `A := x a` (the sketch's `a`), `sᵢ := x (Cᵢ).root`,
`γᵢ := gamma Cᵢ`, `γ := gamma C`.

**E1 — the two IH instantiations.** Apply the IH to each `Cᵢ` at `k := A` and at
`k := A − 1`:
`B Cᵢ x x − 2*A*sᵢ ≥ sᵢ − γᵢ*A*(A+1)` and `B Cᵢ x x − 2*A*sᵢ ≥ −sᵢ − γᵢ*A*(A−1)`.

**E2 — `child_lower_bound`.** Taking the max of E1's two bounds,
`B Cᵢ x x − 2*A*sᵢ ≥ −γᵢ*A² + |sᵢ − γᵢ*A|`
(`le_max_iff` / `abs_le'`-style case split on the sign of `sᵢ − γᵢ*A`; both
branches are `linarith` from E1).

**E3 — summing.** With `D := (c.map (fun t => |x t.root − gamma t * A|)).sum` and
`form_node` (cast to ℚ by `form_cast`):
`(B C x x : ℚ) ≥ (w − Σγᵢ)*A² + D = A²/γ + D`
(the last equality by `capacity_node_formula` + `capacity_denom_pos`). Hence,
setting `τ := A/γ`, the goal reduces to `0 ≤ γ*(τ − k)*(τ − k − 1) + D`.

**E4 — case `τ ∉ (k, k+1)`.** If `τ ≤ k` or `k + 1 ≤ τ` then
`(τ − k)*(τ − k − 1) ≥ 0` (`mul_nonneg` / `mul_nonneg_of_nonpos_nonpos`), and
`D ≥ 0` (`List.sum_nonneg` of `abs_nonneg`), so the goal is `linarith`.

**E5 — case `k < τ < k + 1`.** Put `α := τ − k`, `β := k + 1 − τ`; then
`0 < α, β < 1`, `α + β = 1` and `γ*(τ−k)*(τ−k−1) = −γ*α*β`.
*The integer witness.* Let `M := w*A − Σᵢ sᵢ : ℤ`. Then
`(M : ℚ) = w*A − Σ sᵢ` and `τ = (w − Σγᵢ)*A`, so
`τ − M = Σᵢ (sᵢ − γᵢ*A)`, whence
`D = Σ|sᵢ − γᵢA| ≥ |Σ(sᵢ − γᵢA)| = |τ − M|` (`List.abs_sum_le_sum_abs`).
*Distance to ℤ.* Since `M : ℤ` and `k < τ < k+1`: if `M ≤ k` then
`|τ − M| = τ − M ≥ τ − k = α`; if `k + 1 ≤ M` then `|τ − M| ≥ M − τ ≥ β`
(`Int.lt_iff_add_one_le` to rule out `k < M < k+1`). So `D ≥ min α β`.
*Finish.* `α*β ≤ min α β` (as `α, β ≤ 1`) and `γ < 1` (`capacity_lt_one`) give
`γ*α*β ≤ α*β ≤ min α β ≤ D`, i.e. `0 ≤ −γ*α*β + D`. `nlinarith` closes it once
the four facts `0 < α`, `0 < β`, `α + β = 1`, `0 < γ < 1` are in context.

**E6 — the leaf case is not special.** When `c = []`, `D = 0` and `M = w*A`, so
E5's `D ≥ min α β > 0` is contradictory and E4 applies (`τ = w*A ∈ ℤ`). Write
the proof so that E4/E5 cover `c = []` uniformly — **do not** add a separate
base case with a bespoke `(Wm − k)(Wm − k − 1) ≥ 0` argument.

> **Cheat watch (Stage E).** `rooted_estimate` quantifies over **every** integer
> vector `x` and **every** `k : ℤ` — no restriction to `k ≥ 0`, to `x` supported
> on `verts C`, to `x C.root ≥ 0`, or to non-leaf `C`. The `|sᵢ − γᵢA|` term
> (`D`) may not be dropped or replaced by `0`: without it the `k < τ < k+1` case
> is false. `D ≥ |τ − M|` must be proved via the **triangle inequality against a
> genuine integer** `M = w*A − Σsᵢ`; do not replace it by an appeal to an
> unproved "distance to ℤ" lemma, and do not introduce `Int.fract`/`round` to
> fake it. The step `α*β ≤ min α β` needs `α, β ≤ 1`, which needs `α + β = 1` —
> derive it, do not assume it. Finally, this statement is used downstream at
> `k = 1`, `k = 0`, `k = −1` and `k = p ≥ 1`: a version proved "for large `k`"
> silently breaks Stages F and H.

### Stage F — Corollary 1 (`Proofs/RootBound/`)

Goal: frozen `admissible_root_bound`. Depends on D + E.

**F1 — case `x C.root ≤ 0`.** `admissible_posDef` gives `0 < B C x x`, and
`x C.root ≤ 0`, so `0 < B C x x − x C.root` by `linarith`.

**F2 — case `1 ≤ x C.root`.** Apply `rooted_estimate` at `k = 1`:
`0 ≤ (B C x x : ℚ) − 3*x C.root + 2*gamma C`, i.e.
`B C x x ≥ 3*x C.root − 2*γ > 3*x C.root − 2` (`capacity_lt_one`). With
`x C.root ≥ 1` we get `3*x C.root − 2 ≥ x C.root`, hence
`B C x x > x C.root`. Cast back to ℤ with `exact_mod_cast`.

> **Cheat watch (Stage F).** This is the sketch's Corollary 1, whose informal
> proof goes through `ρ^#` and Cauchy–Schwarz. **Replacing that route by
> `rooted_estimate` at `k = 1` is a legitimate change of proof, not of
> statement** — the frozen statement is unchanged and the strictness is genuine.
> What is *not* allowed: weakening the conclusion to `0 ≤ B C x x − x C.root`
> (that is just `rooted_estimate` at `k = 0` and is useless in Stage H's `p = 0`
> case, which needs the **strict** inequality to derive a contradiction);
> restricting to `x C.root ≥ 0`; or replacing `NonzeroOn C x` by `x ≠ 0`. Both
> cases must be covered — `x C.root ≤ 0` genuinely needs `admissible_posDef`, so
> do not close it by `positivity` hand-waving.

### Stage G — re-rooting (`Proofs/Reroot/`)

Goal: frozen `exists_reroot_at`. Depends only on A (and can start in the first
parallel batch, deferring the A-lemmas it cites).

**G1 — `pivot : RTree → ℕ → RTree`,** moving the root one step onto child `i`:

```lean
def pivot : RTree → ℕ → RTree
  | .node a w c, i =>
      match c[i]? with
      | none => .node a w c
      | some (.node b w' d) => .node b w' (d ++ [.node a w (c.eraseIdx i)])
```

**G2 — `pivot` invariance.** For `i < c.length`:
`(vwts (pivot T i)).Perm (vwts T)` and — the key point — the *multiset of
unordered* edges is unchanged: `edges (pivot T i)` is a permutation of
`edges T` with the single pair `(a, b)` replaced by `(b, a)`. Prove
`(edges (pivot T i)).Perm ((a, b) :: rest)` and
`(edges T).Perm ((a, b) :: rest)` for the same `rest`, then conclude
`form (pivot T i) x y = form T x y` from `List.Perm.sum_eq` plus the
**swap-symmetry of the edge summand** (`x e.1 * y e.2 + x e.2 * y e.1`). The
same `Perm`s give `verts`, `wt` (via `List.Perm` + `Nodup` for `lookup`), and
`deg` (via `List.Perm.countP_eq` and the fact that the swapped pair has the same
incidence test) unchanged.

**G3 — `rerootAt : RTree → List ℕ → RTree`,** iterated pivoting along an address:
`rerootAt t [] = t`, `rerootAt t (i :: q) = rerootAt (pivot t i) q`. Structural
recursion on the address list — **not** on the tree, which does not shrink.
Invariance for `rerootAt` follows from G2 by induction on the address.

**G4 — `addrOf : RTree → ℕ → Option (List ℕ)`,** the address of a label
(`addrOf (.node a _ c) u = if u = a then some [] else first success over
`c.zipIdx`), with `addrOf_root : addrOf T u = some p → (rerootAt T p).root = u`
proved by induction on `p` alongside `addrOf_isSome : u ∈ verts T → (addrOf T u).isSome`.
*Care*: after `pivot t i`, the sub-address `q` still points at the same vertex
because the pivoted node's original children are the **prefix** of the new child
list — state this explicitly as `pivot_addr_stable` and prove it before G3's
invariance.

**G5 — frozen `exists_reroot_at`.** Take `T' := rerootAt T p` for
`p := (addrOf T u).get …`; the five conjuncts are G3 + G4.

> **Cheat watch (Stage G).** This stage is what stops `pointed_root_irreducible`
> from being a special case, so it must be **genuinely general**: `u` ranges over
> all of `verts T`, and the conclusion must include `∀ x y, B T' x y = B T x y`
> (equality of the forms **as functions on all of `ℕ → ℤ`**, not merely on
> vectors supported on `verts T`, and not merely an isomorphism-up-to-relabelling).
> Do not weaken `(verts T').Perm (verts T)` to `verts T' ⊆ verts T` or to an
> equality of `List.toFinset` — Stage I uses the `Perm` to transport `Nodup`.
> Do not add `(verts T).Nodup` as a hypothesis unless a proof genuinely needs it
> (the `Perm`-based arguments should not). Guardrail: on a concrete 3-vertex
> path, `example : (rerootAt (.node 0 2 [.node 1 2 [.node 2 2 []]]) [0,0]).root = 2 := by decide`
> and check `edges`/`deg` agree by `decide`.

### Stage H — Theorem 1 with the bad vertex at the root (`Proofs/Pointed/`)

Goal: frozen `pointed_root_irreducible`. Depends on A + B + C + D + E + F.

**H1 — weights are positive.** For `u ∈ verts T`, `form_gram_entries` gives
`B T (basis u) (basis u) = wt T u`, and `NonzeroOn T (basis u)` holds, so
`hpd` gives `0 < wt T u`.

**H2 — the weight-one escape.** If some `u ∈ verts T` has `wt T u = 1`, then
`B T (basis u) (basis u) = 1` and `Irred T (basis u)` follows by the Stage-B
argument transported to the concrete lattice: given a `Reducible` witness
`(a, b)`, `form_congr` lets us replace `basis u` by `a + b` inside `B`, and
`B T (a+b) (a+b) = B T a a + 2*B T a b + B T b b ≥ 1 + 0 + 1 = 2 ≠ 1` using
`hpd` on `a` and on `b` (`NonzeroOn`, ℤ-integrality). Record this as
`weight_one_irred`. *(Optionally instantiate the frozen `norm_one_irreducible`
at `M := verts T →₀ ℤ`; the direct four-line repeat is acceptable and is the
recommended route — but the frozen abstract lemma must still be proved.)*

**H3 — all weights ≥ 2, and `Admissible` for each child subtree.** Otherwise H2
finishes. Write `T = .node v W c`. Prove the helper
`admissible_of_deg : (verts t).Nodup → (∀ x ∈ verts t, 2 ≤ wt t x) →
 (∀ x ∈ verts t, x ≠ t.root → (deg t x : ℤ) ≤ wt t x) →
 ((deg t t.root : ℤ) + 1 ≤ wt t t.root) → Admissible t`
by `RTree.recAll` (for the root, `deg t t.root = t.kids.length`; for a child
subtree `t'`, `deg t t'.root = deg t' t'.root + 1` supplies its own root
condition). Then for each `t ∈ c`: `hgood` at `t.root` gives
`deg T t.root ≤ wt T t.root`, and `deg_subroot` turns it into
`deg t t.root + 1 ≤ wt t t.root`; `hgood` + `deg_sub` handles the non-root
vertices; H3's `2 ≤ wt` handles the weights. Hence `Admissible t`.

**H4 — Schur positivity `0 < W − Σ γᵢ`.** Build the rational vector
`X := fun u => if u = v then 1 else (c.map (fun t => dual t u)).sum`. By D2,
`BQ t X X = gamma t` and `X t.root = gamma t` for each `t ∈ c` (using `Nodup` so
the branches do not interfere and `dual_vanish` off each subtree), so by
`form_node` `BQ T X X = W − 2*Σγᵢ + Σγᵢ = W − Σγᵢ`. Since `X v = 1 ≠ 0` and
`v ∈ verts T`, `posDefQ_of_posDef` gives `0 < BQ T X X`.

**H5 — the contradiction.** Suppose `Reducible T (basis v)` with witness
`(a, b)`. Set `z := −b` (pointwise). From `∀ u ∈ verts T, basis v u = a u + b u`
and `form_congr`, `0 ≤ B T a b` becomes `B T z z + B T (basis v) z ≤ 0`, with
`NonzeroOn T z` and `NonzeroOn T (fun u => −(basis v u) − z u)` (these are `b ≠ 0`
and `a ≠ 0`).
*Normalisation.* Let `p := z v`. If `p ≤ −1`, replace `z` by
`z' := fun u => −(basis v u) − z u`; a `form_add/neg` computation gives
`B T z' z' + B T (basis v) z' = B T z z + B T (basis v) z`, `z' v = −1 − p ≥ 0`,
and the two `NonzeroOn` facts swap. So WLOG `0 ≤ p`.
*Row formula.* `B T (basis v) z = W*p − Σᵢ sᵢ` where `sᵢ := z tᵢ.root`
(`form_node` + `form_vanish`, since `basis v` vanishes on every `verts tᵢ` by
`Nodup`).
*Expansion.* `B T z z + B T (basis v) z = W*p*(p+1) + Σᵢ (B tᵢ z z − (2p+1)*sᵢ)`.
*Case `1 ≤ p`.* `rooted_estimate` at `k := p` gives
`B tᵢ z z − (2p+1)*sᵢ ≥ −γᵢ*p*(p+1)`, so the total is
`≥ (W − Σγᵢ)*p*(p+1) > 0` by H4 — contradiction.
*Case `p = 0`.* The total is `Σᵢ (B tᵢ z z − sᵢ)`, each summand `≥ 0` (it is `0`
when `z` vanishes on `verts tᵢ`, and `> 0` otherwise by
`admissible_root_bound`). `NonzeroOn T z` with `z v = 0` forces `z` to be nonzero
on some `verts tᵢ` (`verts T = v :: c.flatMap verts`), so the total is `> 0` —
contradiction.
Hence `Irred T (basis v)`, and `v ∈ verts T`, giving the existential.

> **Cheat watch (Stage H).** The `p ≤ −1` normalisation is a genuine
> *substitution*, not a WLOG one may assume: prove
> `B T z' z' + B T (basis v) z' = B T z z + B T (basis v) z` explicitly, and
> re-derive **both** `NonzeroOn` facts for `z'` — dropping either one is how the
> `p = 0` case silently becomes unprovable. Do not assume `0 ≤ p` outright, and
> do not assume `W < c.length` (the badness of `v` is *not* used; only H4 is).
> H4 must come from `hpd` via `posDefQ_of_posDef` — do **not** assume
> `0 < W − Σγᵢ`, and do not derive it from `Admissible T` (`T` is **not**
> admissible; `v` is exactly the vertex that violates it). In H3, `Admissible t`
> must be established for **every** `t ∈ c` and **every** vertex inside it, not
> just for the child roots. The conclusion is `∃ u ∈ verts T, Irred T (basis u)`
> — the witness is `v` in the main case but the **weight-one vertex** in H2;
> do not "simplify" by claiming the root always works.

### Stage I — the headline (`Proofs/Main/`)

Goal: frozen `tree_has_irreducible_vertex`. Depends on G + H (+ A).

**I1 — transport.** Apply `exists_reroot_at T v hv` to get `T'` with
`T'.root = v`, `verts T' ~ verts T`, and `wt`, `deg`, `B` unchanged. Then
`(verts T').Nodup` (`List.Perm.nodup_iff`), `PosDef T'` (unfold `PosDef`;
`NonzeroOn T' = NonzeroOn T` by the `Perm`, and `B T' = B T`), and the `hgood`
hypothesis of Stage H: for `u ∈ verts T'`, `u ≠ v`, the `huniq` hypothesis gives
`¬(wt T u < deg T u)`, i.e. `deg T u ≤ wt T u`, i.e. `deg T' u ≤ wt T' u`.

**I2 — conclude.** `pointed_root_irreducible T' …` yields `u ∈ verts T'` with
`Irred T' (basis u)`. Transport back: `u ∈ verts T` by the `Perm`, and
`Irred T (basis u)` because `Reducible T (basis u) ↔ Reducible T' (basis u)`
(same `B`, same `verts` up to `Perm`, hence same `NonzeroOn` and same
"agree on `verts`" condition).

> **Cheat watch (Stage I).** The headline's `huniq` is an **iff** at every
> vertex; only the `→` direction is consumed, but the statement must keep both —
> it is what `SKETCH.md` assumes ("`v` is the *unique* such vertex", Remark 1).
> Do not replace `huniq` by the weaker-looking-but-different
> `∀ u ∈ verts T, u ≠ v → deg T u ≤ wt T u` (that would drop `v`'s own badness
> and change the theorem), and do not strengthen it by additionally assuming
> `wt T v < deg T v` as a separate hypothesis — it is already the `←` direction.
> The conclusion must be `∃ u ∈ verts T`, i.e. *some* vertex of `T`; proving
> `Irred T (basis v)` and claiming the existential is fine **only** in the branch
> where that is actually established (H2 may hand back a different vertex). Do
> not bypass Stage G by re-stating the headline with `v = T.root`.

### Discharge & Solution (after the frozen theorems are proved)

In `TreeIrred/Solution.lean`, restate each of the 13 frozen theorems **verbatim**
in `namespace TreeIrred.Solution` and set it `:= <name>_proof` (the sorry-free
declaration from `Proofs/`). In `TreeIrred/Discharge.lean`, for each pair write
`example : @<Frozen> = @<Proof> := rfl` — this compiles **iff** the proof has
*exactly* the frozen proposition (machine-checked no-drift). `verify.py` checks
both modules build and that `#print axioms TreeIrred.Solution.<name>` is clean
for every frozen name.

---

## Suggested formalization order

```
SETUP (freeze Defs + Theorems, skeleton builds, pins recorded)
      │
      ├──────────────┬──────────────┬──────────────┐
      ▼              ▼              ▼              ▼
  Stage A        Stage B        Stage C        Stage G          (4-way parallel,
  Model          NormOne        Capacity       Reroot            fully independent)
  form API       Lemma 1        Lemma 2        exists_reroot_at
      │                            │              │
      └──────────┬─────────────────┘              │
                 ▼                                │
            Stage D  PosDef                       │
            capacity_spec, admissible_posDef      │
                 │                                │
                 ├──────────────┐                 │
                 │              ▼                 │
                 │         Stage E  RootedEstimate│   ★ MILESTONE (Lemma 3)
                 │              │                 │
                 └──────┬───────┘                 │
                        ▼                         │
                   Stage F  RootBound             │
                   admissible_root_bound          │
                        │                         │
                        ▼                         │
                   Stage H  Pointed               │
                   pointed_root_irreducible       │
                        │                         │
                        └───────────┬─────────────┘
                                    ▼
                              Stage I  Main
                       tree_has_irreducible_vertex   (#print axioms clean)
                                    │
                                    ▼
                     Discharge.lean + Solution.lean
```

- **Independent (parallelisable):** A, B, C, G is the natural first batch of four.
  Later, E and D6/`posDefQ_of_posDef` can proceed in parallel once C is `✅`.
- **Milestone:** Stage E (`rooted_estimate`). Once it is `✅` the project already
  contains a citable result and everything downstream is assembly.
- **Hardest engineering:** Stage E (the `k < τ < k+1` case analysis) and Stage G
  (the `Perm` bookkeeping for `pivot`). Budget accordingly; Stages B, C and F are
  each a few dozen lines.
- **Watch the ℤ/ℚ boundary:** Stages C–E live in ℚ, Stages F/H state results in
  ℤ. `form_cast` (A5) is the only bridge — prove it early and use
  `exact_mod_cast`/`push_cast` everywhere rather than re-deriving casts.

---

## Notes, risks, and cheats to watch out for

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
  break the proof downstream. Validate the core modeling facts *before* freezing,
  with small guardrail `example`s: on the 3-vertex path
  `P := .node 0 2 [.node 1 2 [.node 2 2 []]]`, check by `decide`/`norm_num` that
  `verts P = [0,1,2]`, `deg P 1 = 2`, `deg P 0 = 1`, `B P (basis 0) (basis 1) = -1`,
  `B P (basis 0) (basis 2) = 0`, `B P (basis 1) (basis 1) = 2`, and
  `gamma P = 1/(2 - 1/(2 - 1/2)) = 3/4`.

- **Discharge ring/structure axioms once — never `sorry` them.** All algebraic
  identities here are `List.sum`/`CommRing` manipulations: close them with
  `simp [form_node] ; ring`, never by assuming bilinearity or symmetry of `form`.
  If you feel the urge to `sorry` `form_add_left`, the `vwts`/`edges` unfolding
  lemmas (A1) are missing.

- **Keep module-side and ring-side objects distinct.** Here the analogous trap is
  **ℤ vs ℚ** and **`B` vs `BQ`**: `rooted_estimate` and `psd_gamma` are ℚ
  statements about integer vectors, `admissible_root_bound` and `PosDef` are ℤ
  statements. Always go through `form_cast`; never state a ℚ lemma and use it as
  if it were the ℤ one (`0 < (q : ℚ)` for an integer `q` gives `1 ≤ q`, and that
  integrality step is used in Stage B — do not lose it by staying in ℚ).

- **`decide` budget — and `native_decide` is BANNED.** `decide` is fine for the
  concrete guardrail `example`s above (small closed `RTree` literals over `ℕ`/`ℤ`
  reduce). It is **useless** for anything quantified over `RTree`, `ℕ → ℤ` or
  `ℚ` — those are infinite/`noncomputable`-adjacent. `native_decide` adds a
  compiler-trust axiom and would dirty `#print axioms` — never use it.

- **Don't touch the frozen files after SETUP.** `Defs.lean` and `Theorems.lean`
  are byte-frozen during proving (pinned in `scripts/frozen.sha256`). If a
  *definition* seems missing (`dual`, `pivot`, `rerootAt`, `admissible_of_deg`),
  it belongs in a `Proofs/` support file — the blueprint deliberately keeps them
  out of `Defs.lean`. If a *statement* seems wrong, stop and re-read `SKETCH.md`.

- **Keep `#print axioms` clean.** Every solved theorem must depend only on
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no `native_decide`/
  `ofReduceBool` — **plus** any assumed-certificate axioms the user permitted in
  `USER_NOTES.md` (their names are recorded in `scripts/ALLOWED_AXIOMS.txt`).
  For this problem `USER_NOTES.md` says **"None — no assumed axioms"**, so the
  allowlist is exactly the standard three and **no `axiom` declaration may appear
  anywhere in the project**.

- **Assumed certificates go in as `axiom`s, never as hypotheses.** Not applicable
  here (none are permitted), and this NEVER relaxes the cardinal rule above.

**Problem-specific traps.**

1. **The junk-support trap (highest risk).** `ℕ → ℤ` has vectors living off the
   tree. Every "nonzero" is `NonzeroOn`, every "`x = a + b`" is "on `verts T`".
   If a worker ever writes `a ≠ 0` or `x = a + b` for tree vectors in a support
   lemma feeding `Irred`, the headline becomes false or trivial. Re-read D7.
2. **Rootedness.** `pointed_root_irreducible` is **not** the theorem. Stage G is
   load-bearing. Any route that quietly makes `v = T.root` a hypothesis of the
   headline is a cheat.
3. **Degree must be unrooted.** `deg` counts incident `edges`. The identity
   `d_T(x) = ch(x) + 1` (for `x` below the pivot) is a **lemma** proved in Stage
   A/H; baking it into the definition would make `hgood`/`huniq` mean something
   weaker than `SKETCH.md`.
4. **`Admissible` dropped positive definiteness.** That is a *strengthening* and
   is discharged by `admissible_posDef`. Do not re-add the clause to make Stage D
   easy, and do not use `PosDef C` as a hypothesis anywhere it is not given.
5. **`gamma` is a definition, not a theorem.** The debt this creates is
   `capacity_spec`. Proving `capacity_spec` only for the diagonal, or only for
   `y := dual C`, leaves the identification with `(Q_C⁻¹)_{ρρ}` unproved and the
   definitional swap unjustified.
6. **The `p ≤ −1` reflection.** `z ↦ −v − z` swaps the roles of `a` and `b`; both
   `NonzeroOn` conditions must survive the swap. This is the step where a
   plausible-looking `wlog` tactic invocation will silently lose a hypothesis.
7. **`D` must not be discarded.** In Stage E the `Σ|sᵢ − γᵢA|` term is the entire
   reason the `k < τ < k+1` case closes. A proof that reaches
   `0 ≤ γ(τ−k)(τ−k−1)` and stops is wrong, not incomplete.
8. **Leaf trees.** `c = []` occurs everywhere (`Σ = 0`, `D = 0`, `deg root = 0`).
   Every induction must be written so the empty-children case is the *same*
   computation, not a special case bolted on afterwards.
