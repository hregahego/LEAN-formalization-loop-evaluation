# TASKS — Problem 6 - a positive definite weighted tree with a unique vertex of weight below its degree contains an irreducible vertex formalization

Append-only work-delegation log for 4 parallel worker agents. The Plan agent
appends one "## Iteration N" block per loop iteration. Each block has a one-line
goal then "Agent k: ..." lines (one per ACTIVE worker; inactive agents are
omitted). NEVER edit or delete an existing block.

## Iteration 1
Open the four mutually-independent leaves of the BLUEPRINT dependency graph
(Stages A · Model, B · NormOne, C · Capacity, G · Reroot — the prescribed first
4-way parallel batch), discharging 7 of the 13 frozen theorems: `form_gram_entries`,
`norm_one_irreducible`, `capacity_node_formula`, `capacity_denom_pos`, `capacity_pos`,
`capacity_lt_one`, `exists_reroot_at`. Nothing is ✅ yet beyond SETUP, so every agent
may use ONLY `TreeIrred/Defs.lean` + Mathlib + lemmas it proves in its OWN file.

RULES BINDING ON ALL FOUR AGENTS (from BLUEPRINT Part −1 §4/§5 and PROGRESS 📝 decisions):
(R1) NEVER edit `TreeIrred/Defs.lean` or `TreeIrred/Theorems.lean` (SHA-pinned), never
weaken/restate a frozen statement, never add a hypothesis to one. Prove each frozen
statement as a NEW declaration named `<frozen_name>_proof` whose type is CHARACTER-FOR-
CHARACTER the frozen statement in `TreeIrred/Theorems.lean` (a later `Discharge.lean`
iteration will check `example : @<Frozen> = @<Proof> := rfl`). Do NOT touch
`TreeIrred/Solution.lean` or `TreeIrred/Discharge.lean` this iteration (shared files;
they are filled in a later iteration).
(R2) Write ONLY in the single file your line assigns. Do NOT import another agent's
`Proofs/` file — all four are being written concurrently this iteration. Import
`TreeIrred.Defs` only. Do not create new files.
(R3) `sorry` may not survive in anything you log as ✅. `native_decide` is BANNED. No
`axiom` declaration anywhere (`USER_NOTES.md`: "None — no assumed axioms"); every ✅ must
`#print axioms` to exactly `{propext, Classical.choice, Quot.sound}` (`Classical.choice`
is expected — `RTree.recAll` is noncomputable, see PROGRESS 📝 decision (3)).
(R4) `vwts`, `edges`, `gamma` are defined by WELL-FOUNDED recursion (`c.attach` +
`decreasing_by`), so they do NOT reduce by `rfl`/`decide`. PROGRESS 📝 decision (2)/(5)
SUPERSEDES the `by decide` guardrails written in BLUEPRINT's cheat-watch boxes: close
concrete guardrail `example`s with `simp`/`norm_num [P, verts, edges, deg, gamma,
RTree.root]`, never `decide`.
(R5) All declarations go inside `namespace TreeIrred`; never shadow a frozen name. Keep
lines under 100 chars (Mathlib style linters are live; only `linter.style.header` is off).
(R6) Onboarding ritual: read `PROGRESS.md` end to end, append a `🔧 in progress` entry
claiming your file BEFORE editing, then append `✅`/`⚠️` entries as you go, in the exact
format of BLUEPRINT Part −1 §4 (`Agent: agent-iter1-<k>`, real UTC timestamp from
`date -u +"%Y-%m-%dT%H:%M:%SZ"`, mandatory `Next:` line with backticked lemma names).
PROGRESS.md is APPEND-ONLY — never edit or delete an existing entry.

Agent 1: OWNS `TreeIrred/Proofs/Model/Basic.lean` (only). Stage A of BLUEPRINT Part 2
("the form API and the Gram-matrix sanity check"), items A1–A7; respect its Cheat-watch
box verbatim. Produce, in this order: (A1) the two list helpers
`attach_flatMap_eq : ∀ {α β} (c : List α) (f : α → List β), c.attach.flatMap (fun t => f t.1) = c.flatMap f`
and `attach_map_eq : ∀ {α β} (c : List α) (f : α → β), c.attach.map (fun t => f t.1) = c.map f`
(one `List` induction each), then `@[simp]` unfolding lemmas `vwts_node`, `verts_node`,
`edges_node` for `.node a w c` stated with `c.flatMap`/`c.map` (NOT `c.attach`). These
are the keystone: without them nothing in this project unfolds — prove them FIRST and
log them ✅ separately so the other stages can cite them next iteration. (A2) `form_node`:
`form (.node a w c) x y = (w:R) * x a * y a + (c.map (fun t => form t x y)).sum
 - (c.map (fun t => x a * y t.root + x t.root * y a)).sum` (via `simp [form, vwts_node,
edges_node, List.sum_append, List.sum_map_add]` + `ring_nf`); state it generically over
`{R} [CommRing R]`. (A3) `form_comm`, `form_add_left`, `form_add_right`, `form_neg_left`,
`form_sub_left`, `form_zero_left` (`induction T using RTree.recAll` + A2 + `ring`).
(A4) `edges_subset_verts` (both endpoints of every edge lie in `verts T`), then
`form_congr` — `(∀ u ∈ verts T, x u = x' u) → form T x y = form T x' y` — and its
right-hand twin and `form_vanish` (`(∀ u ∈ verts T, x u = 0) → form T x y = 0`). The
hypothesis MUST be agreement on `verts T` ONLY (BLUEPRINT D6/D7, trap 1); an "agree
everywhere" version is worthless downstream. (A5) `form_cast :
((B T x y : ℤ) : ℚ) = BQ T (fun u => (x u : ℚ)) (fun u => (y u : ℚ))` by `push_cast`
through both `List.sum`s — this is the ONLY ℤ/ℚ bridge in the project. (A6) under
`(verts T).Nodup`, for `T = .node a w c` and `t ∈ c`: `verts_node_nodup_disjoint`,
`wt_sub`, `deg_sub`, `deg_subroot : deg T t.root = deg t t.root + 1`,
`deg_root : deg T a = c.length`, `form_basis_sub`. `deg` MUST stay the frozen
`edges`-based unrooted `countP` — deriving `d_T(x) = ch(x)+1` is the point; redefining
`deg` as "children + 1" is BLUEPRINT trap 3 and an automatic audit failure.
(A7) `form_gram_entries_proof`, the frozen statement #1 (Theorems.lean:15-19) — all
three conjuncts (diagonal `wt T u`, `-1` on adjacent pairs, `0` otherwise); do not drop
`hu`/`hv` and do not prove only the diagonal case. Guardrails to include as `example`s
(per R4, by `norm_num`, not `decide`), on `P := .node 0 2 [.node 1 2 [.node 2 2 []]]`:
`verts P = [0,1,2]`, `deg P 1 = 2`, `deg P 0 = 1`, `B P (basis 0) (basis 1) = -1`,
`B P (basis 0) (basis 2) = 0`, `B P (basis 1) (basis 1) = 2`; plus
`deg (.node 0 3 [.node 1 2 [], .node 2 2 []]) 0 = 2`. SKETCH.md: the sentence "where
`Q_C` is the Gram matrix of `C` in the vertex basis" (SKETCH.md:23-27) is exactly what
A7 anchors. If A6/A7 stall, still land A1–A5 and log ✅ for them individually — A1/A2
alone unblock Stages C, D, E, G next iteration.

Agent 2: OWNS `TreeIrred/Proofs/NormOne/Basic.lean` (only). Stage B of BLUEPRINT Part 2
(item B1) — frozen theorem #2 `norm_one_irreducible` (Theorems.lean:22-26), rendering
SKETCH.md Lemma 1 ("Norm-one elements are irreducible", SKETCH.md:7-15). Produce
`norm_one_irreducible_proof` with the frozen type:
`{M : Type} [AddCommGroup M] (F : M → M → ℤ) (hadd : ∀ x y z : M, F (x + y) z = F x z + F y z)
(hsymm : ∀ x y : M, F x y = F y x) (hpd : ∀ x : M, x ≠ 0 → 0 < F x x) (x : M)
(hx : F x x = 1) : LatIrred F x`. Path: unfold `LatIrred`/`LatRed` (frozen, Defs.lean:153-157),
intro the witness `⟨a, b, ha, hb, rfl, hab⟩`; derive additivity in the SECOND argument
from `hsymm` + `hadd`; expand `F (a+b) (a+b) = F a a + 2 * F a b + F b b`; from
`hpd a ha : 0 < F a a` over **ℤ** get `1 ≤ F a a` (and likewise for `b`) — this
integrality step is the entire content of the lemma; conclude `F x x ≥ 2`, contradicting
`hx`, by `omega`/`linarith`. Respect BLUEPRINT's Stage B Cheat-watch box: stay at the
abstract `AddCommGroup M` level — do NOT specialise `M` to `ℕ → ℤ` or to a tree, do NOT
add `[Module ℤ M]`/freeness/finite-rank/`BilinForm`, do NOT strengthen `0 ≤ F a b` to
`0 < F a b`, and do NOT add a hypothesis `1 ≤ F a a` (it must be derived from ℤ). This
stage has NO dependencies — do not import or wait on any other `Proofs/` file. It is a
short proof: after logging it ✅ with `#print axioms`, stop; do not wander into other
stages' files.

Agent 3: OWNS `TreeIrred/Proofs/Capacity/Basic.lean` (only). Stage C of BLUEPRINT Part 2
(items C1–C2) — frozen theorems #3–#6, rendering SKETCH.md Lemma 2 (SKETCH.md:31-53).
Produce `capacity_node_formula_proof`, `capacity_denom_pos_proof`, `capacity_pos_proof`,
`capacity_lt_one_proof`, with the frozen types at Theorems.lean:29-39. NOTE: Agent 1 is
writing the shared `attach`-unfolding helpers in `Proofs/Model/Basic.lean` AT THE SAME
TIME — you may NOT import that file this iteration, so prove your own copy of
`c.attach.map (fun t => gamma t.1) = c.map gamma` INSIDE your file under a nested
`namespace Capacity` (e.g. `Capacity.attach_map_gamma`) so the two never clash; a later
iteration will deduplicate. Path: (C1) `capacity_node_formula_proof` — rewrite
`c.attach.map (fun t => gamma t.1)` to `c.map gamma` with your helper, then
`simp [gamma]`. (C2) one simultaneous induction by `induction C using RTree.recAll`
proving `Admissible C → 0 < gamma C ∧ gamma C < 1`, carrying the denominator bound: for
`C = .node a w c`, the IH gives `∀ t ∈ c, 0 < gamma t ∧ gamma t < 1`, hence
`0 ≤ (c.map gamma).sum` and `(c.map gamma).sum < c.length` (list induction on `c`), and
`Admissible` (Defs.lean:97-98) supplies `(c.length : ℤ) + 1 ≤ w`, so
`w - Σγᵢ > w - c.length ≥ 1 > 0`; then `div_pos` and `div_lt_one` with denominator `> 1`.
Split the result into the four frozen statements. The `c = []` case must be the SAME
computation (sum `= 0`, `w ≥ 2`, `γ = 1/w ≤ 1/2 < 1`) — BLUEPRINT trap 8. Respect Stage
C's Cheat-watch box: `capacity_lt_one` must cover EVERY admissible `C` including leaves
(no `c ≠ []` restriction, no `w ≥ 3` patch); `< 1` may NOT be weakened to `≤ 1` (Stage E
needs the strict form); `capacity_denom_pos` must be `0 <`, not `0 ≤`, and must NOT be
obtained by assuming `gamma C ≠ 0`; and do NOT add `(verts C).Nodup` as a hypothesis —
none of Lemma 2 needs it and it would have to be discharged in Stage H. Guardrail
`example`s per R4 (`norm_num [gamma]`, NOT `decide`):
`gamma (.node 0 2 [.node 1 2 [.node 2 2 []]]) = 3/4` and
`gamma (.node 0 3 [.node 1 2 [], .node 2 2 []]) = 1/2`.

Agent 4: OWNS `TreeIrred/Proofs/Reroot/Basic.lean` (only). Stage G of BLUEPRINT Part 2
(items G1–G5) — frozen theorem #11 `exists_reroot_at` (Theorems.lean:57-60), rendering
SKETCH.md's licence to "root `Cᵢ` at `ρᵢ`" / "orient every edge away from `ρ`"
(SKETCH.md:19, 187-193). This is the load-bearing stage that stops the rooted
presentation from losing generality (BLUEPRINT trap 2) and, with Stage E, the hardest
engineering in the project — budget accordingly. NOTE: Agent 1 is writing
`Proofs/Model/Basic.lean` concurrently; you may NOT import it, so prove whatever
`vwts`/`edges`/`form` unfolding you need INSIDE your file under a nested
`namespace Reroot` (e.g. `Reroot.vwts_node`, `Reroot.edges_node`, `Reroot.form_node`) so
names never clash with Agent 1's top-level ones; a later iteration deduplicates. Path:
(G1) define `pivot : RTree → ℕ → RTree` moving the root one step onto child `i`, exactly
as BLUEPRINT G1 gives it (`match c[i]? with | none => .node a w c | some (.node b w' d)
 => .node b w' (d ++ [.node a w (c.eraseIdx i)])`). (G2) for `i < c.length`, prove
`(vwts (pivot T i)).Perm (vwts T)` and that the edge MULTISET is unchanged up to
reversing the single pair `(a,b) ↦ (b,a)`: exhibit one `rest` with
`(edges (pivot T i)).Perm ((b,a) :: rest)` and `(edges T).Perm ((a,b) :: rest)`, then get
`form (pivot T i) x y = form T x y` from `List.Perm.sum_eq` plus the SWAP-SYMMETRY of the
frozen edge summand `x e.1 * y e.2 + x e.2 * y e.1` (Defs.lean:106-108 — this symmetry is
deliberate and is what makes pivoting preserve the form on the nose). The same `Perm`s
give `verts`, `wt` (`List.Perm` + `Nodup`-free `lookup` handling) and `deg`
(`List.Perm.countP_eq`, the swapped pair having the same incidence test) unchanged.
(G3) `rerootAt : RTree → List ℕ → RTree` by structural recursion on the ADDRESS LIST
(`rerootAt t [] = t`, `rerootAt t (i :: q) = rerootAt (pivot t i) q`) — NOT on the tree,
which does not shrink; lift G2's invariance along the address by induction. (G4)
`addrOf : RTree → ℕ → Option (List ℕ)`, with `addrOf_isSome : u ∈ verts T → (addrOf T u).isSome`
and `addrOf_root : addrOf T u = some p → (rerootAt T p).root = u`; prove
`pivot_addr_stable` FIRST (after `pivot t i`, a sub-address `q` still points at the same
vertex because the pivoted node's original children are a PREFIX of the new child list).
(G5) `exists_reroot_at_proof`: take `T' := rerootAt T p` for `p` from `addrOf`. Respect
Stage G's Cheat-watch box: `u` must range over ALL of `verts T`; the conclusion must keep
`∀ x y : ℕ → ℤ, B T' x y = B T x y` as an equality of forms on ALL of `ℕ → ℤ` (not merely
on vectors supported on `verts T`, not an isomorphism-up-to-relabelling); keep
`(verts T').Perm (verts T)` — do NOT weaken it to `⊆` or to `List.toFinset` equality
(Stage I transports `Nodup` along it); and do NOT add `(verts T).Nodup` as a hypothesis,
the `Perm` arguments should not need it. Guardrail per R4 (`norm_num`, NOT `decide`):
on `P := .node 0 2 [.node 1 2 [.node 2 2 []]]`, `(rerootAt P [0,0]).root = 2` and
`edges`/`deg` of the re-rooted tree agree with `P`'s. If the full chain stalls, land and
log ✅ the pieces separately (`pivot` + G2 invariance is already substantial progress and
is exactly what G3–G5 consume), and log a ⚠️ naming the precise failing goal.

## Iteration 2
Clear REVIEW.md's required follow-ups and open the next layer of the BLUEPRINT
dependency graph: wire the 7 already-proved frozen theorems into `Solution.lean`/
`Discharge.lean` (so the harness stops scoring them zero and drift is caught early),
and attack the two now-unblocked stages D (`capacity_spec`, `admissible_posDef`) and
E (`rooted_estimate` ★ MILESTONE), plus the three Stage-H helpers that depend only on
the already-✅ Stages A/B. Advances BLUEPRINT Stages D, E, H (partial) and the
Discharge/Solution wiring.

RULES BINDING ON ALL AGENTS THIS ITERATION (carried over from Iteration 1's R1–R6,
with the Solution/Discharge clause of R1 amended for Agent 3 only):
(R1) NEVER edit `TreeIrred/Defs.lean` or `TreeIrred/Theorems.lean` (SHA-pinned in
`scripts/frozen.sha256`), never weaken/restate a frozen statement, never add a
hypothesis to one. Prove each frozen statement as a NEW declaration `<frozen_name>_proof`
whose type is CHARACTER-FOR-CHARACTER the frozen statement in `TreeIrred/Theorems.lean`.
ONLY Agent 3 may touch `TreeIrred/Solution.lean` and `TreeIrred/Discharge.lean`; no one
else may open those two files.
(R2) Write ONLY in the file(s) your own line assigns. You MAY import the four
Iteration-1 modules that are ✅ and frozen-in-place this iteration —
`TreeIrred.Proofs.Model.Basic`, `TreeIrred.Proofs.NormOne.Basic`,
`TreeIrred.Proofs.Capacity.Basic`, `TreeIrred.Proofs.Reroot.Basic` — but you may NOT
import `TreeIrred.Proofs.PosDef.Basic`, `.RootedEstimate.Basic`, `.RootBound.Basic`,
`.Pointed.Basic` or `.Main.Basic` (they are being written concurrently or are empty).
Do not create new files.
(R3) `sorry` may not survive in anything you log as ✅. `native_decide` is BANNED. No
`axiom` declaration anywhere (`USER_NOTES.md`: "None — no assumed axioms"); every ✅ must
`#print axioms` to exactly `{propext, Classical.choice, Quot.sound}` (`Classical.choice`
is expected — `RTree.recAll` is noncomputable, PROGRESS 📝 decision (3)).
(R4) `vwts`, `edges`, `gamma` are WELL-FOUNDED recursions (`c.attach` + `decreasing_by`)
and do NOT reduce by `rfl`/`decide`. PROGRESS 📝 decision (2)/(5) SUPERSEDES the
`by decide` guardrails in BLUEPRINT's cheat-watch boxes: close concrete guardrail
`example`s with `simp`/`norm_num [P, verts, edges, deg, gamma, RTree.root]`, never
`decide`. Unfold a node with the ✅ `@[simp]` lemmas `TreeIrred.vwts_node`,
`TreeIrred.verts_node`, `TreeIrred.edges_node`, `TreeIrred.form_node` and the ✅
`TreeIrred.capacity_node_formula_proof` — do NOT re-prove `attach`-map helpers, use
`TreeIrred.attach_flatMap_eq` / `TreeIrred.attach_map_eq` from
`TreeIrred/Proofs/Model/Basic.lean`.
(R5) All declarations go inside `namespace TreeIrred` (nested sub-namespaces such as
`TreeIrred.PosDef` are encouraged to avoid clashes); never shadow a frozen name. Keep
lines under 100 chars (Mathlib style linters are live; only `linter.style.header` is off).
(R6) Onboarding ritual: read `PROGRESS.md` end to end, append a `🔧 in progress` entry
claiming your file(s) BEFORE editing, then append `✅`/`⚠️` entries as you go, in the
exact format of BLUEPRINT Part −1 §4 (`Agent: agent-iter2-<k>`, real UTC timestamp from
`date -u +"%Y-%m-%dT%H:%M:%SZ"`, mandatory `Next:` line with backticked lemma names).
(R7) BUILD DISCIPLINE (REVIEW.md required follow-up — a concurrent-lake race destroyed
`.lake/packages/mathlib` in Iteration 1). Build ONLY your own module target, e.g.
`lake build TreeIrred.Proofs.PosDef.Basic`; do NOT run a bare `lake build`, `lake update`
or `lake exe cache get`. If you see `unknown target` or a missing `.lake/packages/mathlib`,
repair with exactly
`cp -Rc /Users/siyua/dev/opensource-validation-runs/Erdos477-refactors/.lake/packages/mathlib /Users/siyua/dev/opensource-validation-runs/GPTP6-refactors/.lake/packages/mathlib`
(PROGRESS.md 2026-08-09T14:21:40Z), never by re-resolving the manifest.
(R8) BINDING MATHEMATICAL FACT (PROGRESS.md 2026-08-09T14:38:50Z, supersedes BLUEPRINT
G2): a one-step `pivot` does NOT preserve `wt` without `(verts T).Nodup`. No stage may
assume it, and no stage may add `(verts T).Nodup` to a frozen statement that does not
already carry it.

Agent 1: OWNS `TreeIrred/Proofs/RootedEstimate/Basic.lean` (that file ONLY).
PRODUCE the frozen theorem #9 `rooted_estimate` as `TreeIrred.rooted_estimate_proof`,
with the type character-for-character `TreeIrred/Theorems.lean:49-50`:
`theorem rooted_estimate (C : RTree) (hC : Admissible C) (x : ℕ → ℤ) (k : ℤ) :`
`  0 ≤ (B C x x : ℚ) - (2 * k + 1) * (x C.root : ℚ) + gamma C * k * (k + 1)`.
This is BLUEPRINT's ★ MILESTONE (Stage E) and SKETCH.md Lemma 3 (SKETCH.md:57-141) —
budget the most effort here.
PATH — follow BLUEPRINT Part 2 Stage E (E1–E6, BLUEPRINT.md:770-826) literally. One
`induction C using RTree.recAll` on `C = .node a w c`; write `A := x a`, `sᵢ := x t.root`,
`γᵢ := gamma t` for `t ∈ c`, `γ := gamma C`. (E1) instantiate the IH on each `t ∈ c` at
`k := A` and at `k := A - 1`. (E2) `child_lower_bound`: take the max of the two bounds to
get `(B t x x : ℚ) - 2*A*sᵢ ≥ -γᵢ*A^2 + |sᵢ - γᵢ*A|` by a case split on the sign of
`sᵢ - γᵢ*A`, each branch `linarith`. (E3) sum with `form_node` (cast ℤ→ℚ by `form_cast`)
and set `D := (c.map (fun t => |(x t.root : ℚ) - gamma t * A|)).sum`, `τ := A/γ`, reducing
the goal to `0 ≤ γ*(τ-k)*(τ-k-1) + D` via `capacity_node_formula_proof` +
`capacity_denom_pos_proof`. (E4) case `τ ≤ k ∨ k+1 ≤ τ`: `mul_nonneg` + `D ≥ 0`
(`List.sum_nonneg`, `abs_nonneg`), `linarith`. (E5) case `k < τ < k+1`: put
`α := τ-k`, `β := k+1-τ`, derive `α+β = 1`, `0 < α,β < 1`; the integer witness is
`M := w*A - Σᵢ sᵢ : ℤ` (an honest `ℤ`), `D ≥ |τ - M|` by `List.abs_sum_le_sum_abs`, then
`|τ - M| ≥ min α β` by `Int.lt_iff_add_one_le` ruling out `k < M < k+1`; finish with
`α*β ≤ min α β` and `γ < 1` (`capacity_lt_one_proof`), `nlinarith`. (E6) write E4/E5 so
`c = []` is covered by the SAME computation — no bespoke base case.
MAY USE (all ✅, import `TreeIrred.Proofs.Model.Basic` and `TreeIrred.Proofs.Capacity.Basic`):
`form_node`, `form_cast`, `form_add_left`, `form_sub_left`, `form_neg_left`, `form_comm`,
`form_congr`, `form_vanish`, `vwts_node`/`verts_node`/`edges_node`, `attach_map_eq`;
`capacity_node_formula_proof`, `capacity_denom_pos_proof`, `capacity_pos_proof`,
`capacity_lt_one_proof`, and the sharper internal `TreeIrred.Capacity.key`
(`1 < (C.wtRoot : ℚ) - (C.kids.map gamma).sum`) plus `Capacity.sum_le_length` /
`Capacity.sum_lt_of_le`. Gotcha from PROGRESS: `rcases` does NOT destructure
`hC : Admissible (.node a w c)` — `rw [Admissible] at hC` first.
CHEAT-WATCH (BLUEPRINT.md:816-826, BINDING): `x` and `k` stay FULLY general — no `k ≥ 0`,
no support restriction on `x`, no `x C.root ≥ 0`, no non-leaf restriction (it is used
downstream at `k = 1, 0, -1` and `k = p ≥ 1`). The `D = Σ|sᵢ - γᵢA|` term may NOT be
dropped or replaced by `0` — without it the `k < τ < k+1` case is FALSE (trap 7). `D ≥
|τ - M|` must go through the triangle inequality against the genuine integer
`M = w*A - Σsᵢ`; do NOT use `Int.fract`/`round` or an unproved "distance to ℤ" lemma.
Derive `α + β = 1`, do not assume it. Do NOT add `(verts C).Nodup` (the frozen statement
has none). If the full induction stalls, land and log ✅ the reusable pieces separately
(E2's `child_lower_bound` and E3's reduction are each substantial), and log a ⚠️ naming
the exact failing goal.

Agent 2: OWNS `TreeIrred/Proofs/PosDef/Basic.lean` (that file ONLY).
PRODUCE the frozen theorems #7 and #8 as `TreeIrred.capacity_spec_proof` and
`TreeIrred.admissible_posDef_proof`, types character-for-character
`TreeIrred/Theorems.lean:42-43` and `:46`:
`theorem capacity_spec (C : RTree) (hnd : (verts C).Nodup) (hC : Admissible C) :`
`  ∃ u : ℕ → ℚ, (∀ y : ℕ → ℚ, BQ C u y = y C.root) ∧ BQ C u u = gamma C`
`theorem admissible_posDef (C : RTree) (hC : Admissible C) : PosDef C`;
plus the support lemmas Stages F and H consume, all in a nested `namespace PosDef` or at
top level under `TreeIrred`: `dualScaled`, `dual`, `dual_vanish`, `dual_apply`,
`psd_gamma`, `posDefQ_of_posDef`.
PATH — BLUEPRINT Part 2 Stage D, items D1–D6 (BLUEPRINT.md:702-768), rendering SKETCH.md's
`ρ^#` (SKETCH.md:153-159) and the Schur block computation (SKETCH.md:41-47). (D1) define
`dualScaled : RTree → ℚ → (ℕ → ℚ)` and `dual C := dualScaled C 1` exactly as
BLUEPRINT.md:710-715 (`c.attach` + `decreasing_by simp_wf; have h := List.sizeOf_lt_of_mem
t.2; omega`, as in `Defs.lean`). (D2) `dual_apply`: under `(verts C).Nodup` and
`Admissible C`, `∀ s (y : ℕ → ℚ), BQ C (dualScaled C s) y = s * y C.root`, by
`RTree.recAll` + `form_node`, using `γ*(w - Σγᵢ) = 1` from `capacity_node_formula_proof`
+ `capacity_denom_pos_proof`; the companion induction `dual_vanish` (`dualScaled C s`
vanishes off `verts C`) is what makes the `Nodup` bookkeeping work. (D3)
`capacity_spec_proof := ⟨dual C, D2 at s = 1, D2 with y := dual C⟩` (the second conjunct
is `BQ C u u = u C.root = gamma C`). (D4) `psd_gamma : Admissible C → ∀ (x : ℕ → ℚ)
(t : ℚ), 0 ≤ BQ C x x - 2*t*(x C.root) + gamma C * t^2` by `RTree.recAll`, completing the
square as `(a - γt)^2/γ ≥ 0` (`div_nonneg`, `sq_nonneg`, `capacity_pos_proof`); note this
needs NO `Nodup` and subsumes the leaf case. (D5) `admissible_posDef_proof`: `0 ≤ B C x x`
from D4 at `t = 0` through `form_cast`, then the `≠ 0` half by the `form_node` identity
`B C x x = Σᵢ(B Cᵢ x x - 2a·sᵢ + γᵢa²) + a²/γ` — if the total is `0` then `a = x C.root = 0`
and every bracket vanishes, so the IH forces `x` to vanish on every `verts Cᵢ`,
contradicting `NonzeroOn`. (D6) `posDefQ_of_posDef : PosDef T → ∀ x : ℕ → ℚ,
(∃ u ∈ verts T, x u ≠ 0) → 0 < BQ T x x`, clearing denominators with the EXPLICIT
`N := (verts T).foldr (fun u n => Nat.lcm (x u).den n) 1`.
MAY USE (all ✅, import `TreeIrred.Proofs.Model.Basic` and `TreeIrred.Proofs.Capacity.Basic`):
`form_node`, `form_cast`, `form_congr`, `form_congr_right`, `form_vanish`,
`form_add_left`/`form_add_right`/`form_neg_left`/`form_sub_left`/`form_zero_left`,
`form_comm`, `edges_subset_verts`, `vwts_node`/`verts_node`/`edges_node`,
`verts_node_nodup_disjoint`, `verts_node_root_not_mem`, `verts_child_nodup`, `wt_sub`,
`attach_map_eq`/`attach_flatMap_eq`; `capacity_node_formula_proof`,
`capacity_denom_pos_proof`, `capacity_pos_proof`, `capacity_lt_one_proof`,
`TreeIrred.Capacity.key`. Gotcha: `rw [Admissible] at hC` before destructuring.
CHEAT-WATCH (BLUEPRINT.md:759-768, BINDING): `capacity_spec`'s first conjunct is
`∀ y : ℕ → ℚ` — proving it only for `y = dual C`, only for basis vectors, or only for `y`
supported on `verts C` destroys its role as the identification `γ = (Q_C⁻¹)_{ρρ}` (D8
debt / trap 5) and is a weakening. `admissible_posDef` must produce STRICT positivity
from `NonzeroOn` (not `0 ≤`, and not "`x ≠ 0` as a function") — the `≠ 0` half is the
real content, do NOT stop at `psd_gamma`, and do NOT add `(verts C).Nodup` to it (the
frozen #8 has no `Nodup`; only #7 does). In D6 do not assume `x` is integer-valued or add
a denominator hypothesis, and do not pick `N` by `Classical.choice` — it is an explicit
`foldr lcm`. Do NOT re-add positive definiteness to `Admissible` (trap 4). If the whole
stage does not land, ship `dual`+`dual_apply`+`capacity_spec_proof` first (it is the
self-contained half) and log a ⚠️ with the exact failing goal for D5.

Agent 3: OWNS `TreeIrred/Solution.lean` and `TreeIrred/Discharge.lean` (those two files
ONLY — no `Proofs/` file, no frozen file). This clears REVIEW.md Iteration 1's FIRST
required follow-up (REVIEW.md:68): seven gate-verified proofs currently score ZERO on
`scripts/verify.py` because `Solution.lean` is still an empty namespace.
PRODUCE, in `namespace TreeIrred.Solution` inside `TreeIrred/Solution.lean`, a verbatim
restatement of these SEVEN frozen theorems — copy each statement CHARACTER-FOR-CHARACTER
from `TreeIrred/Theorems.lean` (do not retype from memory, do not reorder or rename
binders) and close each with `:= TreeIrred.<name>_proof`:
`form_gram_entries` (Theorems.lean:15-19, proof at `TreeIrred/Proofs/Model/Basic.lean:647`),
`norm_one_irreducible` (:22-26, `Proofs/NormOne/Basic.lean:43`),
`capacity_node_formula` (:29-30, `Proofs/Capacity/Basic.lean:83`),
`capacity_denom_pos` (:33-34, `Proofs/Capacity/Basic.lean:87`),
`capacity_pos` (:37, `Proofs/Capacity/Basic.lean:92`),
`capacity_lt_one` (:39, `Proofs/Capacity/Basic.lean:95`),
`exists_reroot_at` (:57-60, `Proofs/Reroot/Basic.lean:415`).
Then in `TreeIrred/Discharge.lean`, add for each of those seven the no-drift gate
`example : @TreeIrred.<name> = @TreeIrred.<name>_proof := rfl` AND
`example : @TreeIrred.<name> = @TreeIrred.Solution.<name> := rfl`.
Do NOT add any of the other six names (`capacity_spec`, `admissible_posDef`,
`rooted_estimate`, `admissible_root_bound`, `pointed_root_irreducible`,
`tree_has_irreducible_vertex`) — their `_proof`s do not exist yet and adding them would
break the build for everyone.
PATH / BUILD ISOLATION (mandatory, this is what keeps you collision-free): `Solution.lean`
currently imports all nine `Proofs/**` modules, four of which Agents 1/2/4 are editing
right now. `Solution.lean` is NOT frozen, so EDIT ITS IMPORT LIST DOWN to exactly
`import TreeIrred.Theorems`, `import TreeIrred.Proofs.Model.Basic`,
`import TreeIrred.Proofs.NormOne.Basic`, `import TreeIrred.Proofs.Capacity.Basic`,
`import TreeIrred.Proofs.Reroot.Basic` (a later iteration re-adds the rest as those
stages land; leave a one-line comment saying so). Leave `TreeIrred.lean` and
`Discharge.lean`'s single `import TreeIrred.Solution` alone. Build with
`lake build TreeIrred.Discharge` ONLY — never a bare `lake build` (R7), which would try
to compile the three files being written concurrently.
VERIFY before logging ✅: `lake build TreeIrred.Discharge` succeeds with zero errors and
zero warnings, and `#print axioms TreeIrred.Solution.<name>` for all seven gives exactly
`[propext, Classical.choice, Quot.sound]` (or a subset — `norm_one_irreducible` gives
`[propext, Quot.sound]`). Record all seven axiom lines in your PROGRESS `Check:` field.
CHEAT-WATCH (BLUEPRINT.md:1011-1019 "Discharge & Solution", plus BLUEPRINT.md:1076-1083
the cardinal rule): the restatement must be the frozen proposition EXACTLY — do not
generalise a binder, do not drop `hnd`/`hu`/`hv`, do not turn an explicit argument into
an instance-implicit one. The `rfl` gates are the machine check; if one fails to
type-check, that is a genuine drift finding — do NOT "fix" it by editing the restatement
to match the proof, and NEVER edit `Theorems.lean`. Instead log a ⚠️ in PROGRESS.md
naming the offending `_proof` and its actual type.

Agent 4: OWNS `TreeIrred/Proofs/Pointed/Basic.lean` (that file ONLY).
Stage H's frozen theorem #12 `pointed_root_irreducible` is BLOCKED this iteration (it
needs Stages D, E, F). Your job is the three Stage-H sub-results that depend ONLY on the
already-✅ Stages A and B, so that next iteration's Stage H is pure assembly. Do NOT
attempt `pointed_root_irreducible_proof` and do NOT leave a `sorry` in the file.
PRODUCE, inside `namespace TreeIrred` (nested `namespace Pointed` recommended):
(1) `Pointed.wt_pos : (verts T).Nodup → PosDef T → ∀ u ∈ verts T, 0 < wt T u`
    — BLUEPRINT H1 (BLUEPRINT.md:912-914) / SKETCH.md:181. Route: `form_gram_entries_proof`
    at `u = v` gives `B T (basis u) (basis u) = wt T u`, and `NonzeroOn T (basis u)` holds
    at `u` itself, so `hpd` gives `0 < wt T u`.
(2) `Pointed.weight_one_irred : (verts T).Nodup → PosDef T → u ∈ verts T → wt T u = 1 →
    Irred T (basis u)`
    — BLUEPRINT H2 (BLUEPRINT.md:916-924) / SKETCH.md:183. Route: unfold `Irred`/
    `Reducible` (Defs.lean:130-135), take the witness `(a, b)` with
    `∀ z ∈ verts T, basis u z = a z + b z`, `NonzeroOn T a`, `NonzeroOn T b`,
    `0 ≤ B T a b`; use `form_congr`/`form_congr_right` to replace `basis u` by the
    pointwise sum inside `B` (the hypothesis is agreement on `verts T` ONLY — never
    "agrees everywhere", trap 1), expand with `form_add_left`/`form_add_right`/`form_comm`
    to `B T a a + 2*B T a b + B T b b`, and conclude `≥ 2 ≠ 1` from `hpd a`, `hpd b` over
    ℤ (`0 < n → 1 ≤ n` by `omega` — the integrality step must come from ℤ, not from an
    added hypothesis). You MAY instead instantiate the ✅ frozen
    `norm_one_irreducible_proof`, but the direct repeat is the recommended route.
(3) `Pointed.admissible_of_deg : (verts t).Nodup → (∀ x ∈ verts t, 2 ≤ wt t x) →
    (∀ x ∈ verts t, x ≠ t.root → (deg t x : ℤ) ≤ wt t x) →
    ((deg t t.root : ℤ) + 1 ≤ wt t t.root) → Admissible t`
    — BLUEPRINT H3 (BLUEPRINT.md:926-936) / SKETCH.md:187-199, verbatim that signature.
    Route: `RTree.recAll`; at the root use `deg_root : deg (.node a w c) a = c.length` to
    turn the fourth hypothesis into `(c.length : ℤ) + 1 ≤ w`; for a child subtree `t' ∈ c`
    use `deg_subroot : deg (.node a w c) t'.root = deg t' t'.root + 1` to supply `t'`'s own
    root condition and `deg_sub` + `wt_sub` to relay the non-root vertices, and
    `verts_child_nodup` for its `Nodup`.
MAY USE (all ✅, import `TreeIrred.Proofs.Model.Basic` and `TreeIrred.Proofs.NormOne.Basic`
— and NOTHING from `Proofs/PosDef`, `Proofs/RootedEstimate`, `Proofs/RootBound`,
`Proofs/Main`, per R2): `form_gram_entries_proof`, `form_node`, `form_congr`,
`form_congr_right`, `form_vanish`, `form_add_left`/`form_add_right`/`form_neg_left`/
`form_sub_left`/`form_zero_left`, `form_comm`, `root_mem_verts`, `mem_verts_of_mem_child`,
`verts_node`/`vwts_node`/`edges_node`, `verts_child_nodup`, `verts_node_nodup_disjoint`,
`verts_node_root_not_mem`, `kids_nodup`, `wt_sub`, `deg_root`, `deg_subroot`, `deg_sub`,
`deg_node`, `deg_eq_zero_of_not_mem`; `norm_one_irreducible_proof`, `NormOne.add_right`,
`NormOne.expand_add`.
CHEAT-WATCH (BLUEPRINT.md:968-980 Stage H, plus D7/trap 1 at BLUEPRINT.md:258-282): every
"nonzero" is `NonzeroOn T ·` relative to `verts T`, never `≠ 0` as a function, and the
splitting condition is `∀ u ∈ verts T, x u = a u + b u`, never `x = a + b` — writing
either the wrong way makes `Irred` a strictly weaker claim and the headline false. In (3)
`Admissible t` must be established for EVERY vertex inside `t`, not just for the child
roots, and `deg` stays the frozen unrooted `edges`-based `countP` — the identity
`d_T(x) = ch(x) + 1` must be DERIVED from `deg_subroot`/`deg_root`, never assumed or
redefined (trap 3). Do not add positive definiteness back into `Admissible` (trap 4).
Include a `norm_num` guardrail (R4, never `decide`) that `admissible_of_deg` applies to
the concrete star `.node 0 3 [.node 1 2 [], .node 2 2 []]`. If (2) or (3) stalls, land
whichever of (1)/(2)/(3) compiles and log a ⚠️ with the exact failing goal.

## Iteration 3
Close the last three frozen theorems' mathematical content and finish REVIEW.md's
required wiring: Stage F (`admissible_root_bound`, #10) is landed outright, while Stage H
(#12) and Stage I (#13) are landed as their FULL proofs parameterised on the frozen
statement of the stage below them (which is being written concurrently in another agent's
file, so it may not be imported this iteration) — advances BLUEPRINT Stages F, H, I and
the Discharge/Solution wiring.

RULES BINDING ON ALL AGENTS THIS ITERATION (carried over from Iterations 1–2, R1–R7,
with R2's import fence updated for the new set of ✅ modules):
(R1) NEVER edit `TreeIrred/Defs.lean` or `TreeIrred/Theorems.lean` (SHA-pinned in
`scripts/frozen.sha256`), never weaken/restate a frozen statement, never add a hypothesis
to one. Prove each frozen statement as a NEW declaration `<frozen_name>_proof` whose type
is CHARACTER-FOR-CHARACTER the frozen statement in `TreeIrred/Theorems.lean`. ONLY Agent 3
may touch `TreeIrred/Solution.lean` and `TreeIrred/Discharge.lean`; no one else may open
those two files.
(R2) Write ONLY in the file(s) your own line assigns. You MAY import the SIX modules that
are ✅ and untouched this iteration — `TreeIrred.Proofs.Model.Basic`,
`TreeIrred.Proofs.NormOne.Basic`, `TreeIrred.Proofs.Capacity.Basic`,
`TreeIrred.Proofs.Reroot.Basic`, `TreeIrred.Proofs.PosDef.Basic`,
`TreeIrred.Proofs.RootedEstimate.Basic` — but you may NOT import
`TreeIrred.Proofs.RootBound.Basic`, `.Pointed.Basic` or `.Main.Basic`: those three are
being written concurrently by Agents 1, 2 and 4. Do not create or delete files, and do not
edit a module you do not own (in particular do NOT do the optional helper dedup in
`Capacity/Basic.lean` or `Reroot/Basic.lean` — other agents are compiling them).
(R3) `sorry` may not survive in anything you log as ✅. `native_decide` is BANNED. No
`axiom` declaration anywhere (`USER_NOTES.md`: "None — no assumed axioms"); every ✅ must
`#print axioms` to exactly `{propext, Classical.choice, Quot.sound}` (`Classical.choice`
is expected — `RTree.recAll` is noncomputable, PROGRESS 📝 decision (3)).
(R4) `vwts`, `edges`, `gamma`, `dualScaled` are WELL-FOUNDED recursions (`c.attach` +
`decreasing_by`) and do NOT reduce by `rfl`/`decide`. Close concrete guardrail `example`s
with `simp`/`norm_num [P, verts, edges, deg, gamma, RTree.root, Admissible]`, NEVER
`decide`. Unfold a node with the ✅ `@[simp]` lemmas `TreeIrred.vwts_node`,
`TreeIrred.verts_node`, `TreeIrred.edges_node`, `TreeIrred.form_node`,
`TreeIrred.capacity_node_formula_proof`, `TreeIrred.dualScaled_node` — do NOT re-prove
`attach`-map helpers, use `TreeIrred.attach_flatMap_eq` / `TreeIrred.attach_map_eq`.
(R5) All declarations go inside `namespace TreeIrred` (nested sub-namespaces such as
`TreeIrred.RootBound`, `TreeIrred.Pointed`, `TreeIrred.Main` are encouraged); never shadow
a frozen name. Keep lines under 100 chars (Mathlib style linters are live).
(R6) Onboarding ritual: read `PROGRESS.md` end to end, append a `🔧 in progress` entry
claiming your file(s) BEFORE editing, then append `✅`/`⚠️` entries as you go, in the exact
format of BLUEPRINT Part −1 §4 (`Agent: agent-iter3-<k>`, real UTC timestamp from
`date -u +"%Y-%m-%dT%H:%M:%SZ"`, mandatory `Next:` line with backticked lemma names).
(R7) BUILD DISCIPLINE (two mathlib incidents in two iterations, PROGRESS.md:74-79 and
:179-184). Always give `lake` an ABSOLUTE path or run it from the verified project root
(`pwd` first — a shell `cd` persists between tool calls), and build ONLY your own module
target, e.g. `lake build TreeIrred.Proofs.RootBound.Basic`; NEVER a bare `lake build`,
`lake update` or `lake exe cache get`. If you see `unknown target`, first re-check `pwd`
and `ls -d .lake/packages/mathlib` — PROGRESS.md:179-184 records that the "missing
mathlib" is usually a stale cwd, and that re-running the `cp -Rc` repair onto an EXISTING
destination CORRUPTS the checkout on case-insensitive APFS.
(R8) Two gotchas every agent will hit, from PROGRESS.md: `rcases`/`obtain` does NOT
destructure `hC : Admissible (.node a w c)` and `refine ⟨_,_,_⟩` does not see through an
`Admissible` GOAL — `rw [Admissible] at hC` / `rw [Admissible]` first (keep an unrewritten
copy of `hC`, the capacity lemmas need it); and `rw [form_congr …]` does not fire on a goal
stated with the abbreviations `B`/`BQ` — insert `change form T … = …` first.

Agent 1: OWNS `TreeIrred/Proofs/RootBound/Basic.lean` (that file ONLY; it is currently a
14-line stub).
PRODUCE frozen theorem #10 as `TreeIrred.admissible_root_bound_proof`, type
character-for-character `TreeIrred/Theorems.lean:53-54`:
`theorem admissible_root_bound (C : RTree) (hC : Admissible C)`
`    (x : ℕ → ℤ) (hx : NonzeroOn C x) : 0 < B C x x - x C.root`.
PATH — BLUEPRINT Part 2 Stage F, items F1–F2 (BLUEPRINT.md:828-850), which is SKETCH.md
Corollary 1 (SKETCH.md:145-169). Case split on `x C.root` with `le_or_lt`/`omega`.
(F1) `x C.root ≤ 0`: `TreeIrred.admissible_posDef_proof C hC x hx : 0 < B C x x`, so
`linarith`/`omega` closes `0 < B C x x - x C.root`.
(F2) `1 ≤ x C.root`: instantiate `TreeIrred.rooted_estimate_proof C hC x 1`, giving
`0 ≤ (B C x x : ℚ) - 3 * (x C.root : ℚ) + gamma C * 1 * (1 + 1)`; with
`TreeIrred.capacity_lt_one_proof C hC : gamma C < 1` this yields
`(x C.root : ℚ) < (B C x x : ℚ)` by `linarith` (the slack is `2*(1 - gamma C) > 0`
together with `3*x C.root - 2 ≥ x C.root`, which needs `1 ≤ x C.root`). Come back to ℤ
with `exact_mod_cast` / `push_cast` (`Int.cast_lt`), then `omega`.
Equivalent alternative if the cast bookkeeping fights you (BOTH are legitimate, pick one):
SKETCH.md:153-167's own route — `TreeIrred.psd_gamma C hC (fun u => (x u : ℚ))
(t := (x C.root : ℚ) / gamma C)` is the Cauchy–Schwarz substitute and gives
`(x C.root : ℚ)^2 / gamma C ≤ BQ C x x`, then `gamma C < 1` and `1 ≤ x C.root` finish;
bridge ℤ→ℚ with `TreeIrred.form_cast`, and `TreeIrred.capacity_pos_proof` for `gamma C > 0`
whenever you divide.
MAY USE (all ✅; import `TreeIrred.Proofs.Model.Basic`, `TreeIrred.Proofs.Capacity.Basic`,
`TreeIrred.Proofs.PosDef.Basic`, `TreeIrred.Proofs.RootedEstimate.Basic` — and NOTHING
from `Proofs/RootBound` siblings, `Proofs/Pointed`, `Proofs/Main`, per R2):
`rooted_estimate_proof`, `admissible_posDef_proof`, `capacity_pos_proof`,
`capacity_lt_one_proof`, `capacity_denom_pos_proof`, `capacity_node_formula_proof`,
`capacity_spec_proof`, `psd_gamma`, `PosDef.posDefQ`, `posDefQ_of_posDef`,
`PosDef.form_node_split`, `PosDef.form_smul_left`, `form_cast`, `form_node`, `form_congr`,
`form_vanish`, `form_add_left`/`form_sub_left`/`form_neg_left`/`form_comm`,
`RootedEstimate.core`, `RootedEstimate.sum_map_le`/`sum_map_nonneg`.
CHEAT-WATCH (BLUEPRINT.md:841-850, BINDING): the conclusion must stay STRICT
`0 < B C x x - x C.root` — `0 ≤ …` is just `rooted_estimate` at `k = 0` and is USELESS to
Stage H's `p = 0` case, which is where the headline actually gets its contradiction. The
hypothesis stays `NonzeroOn C x` (nonzero at some vertex of `verts C`), never `x ≠ 0` as a
function; do NOT restrict to `x C.root ≥ 0`; do NOT add `(verts C).Nodup` (frozen #10 has
none); BOTH cases must be genuinely proved — `x C.root ≤ 0` needs `admissible_posDef_proof`
and may not be waved through by `positivity`. Add a `norm_num` guardrail (R4, never
`decide`) applying the theorem to `P := .node 0 2 [.node 1 2 [.node 2 2 []]]` at a concrete
nonzero `x` such as `basis 0`.

Agent 2: OWNS `TreeIrred/Proofs/Pointed/Basic.lean` (that file ONLY; it already contains
your ✅ predecessors `Pointed.wt_pos`, `Pointed.form_split_diag`, `Pointed.weight_one_irred`,
`Pointed.admissible_of_deg` — do not weaken or delete them, append below them).
PRODUCE (i) `TreeIrred.Pointed.schur_pos` (BLUEPRINT H4) and (ii) the whole of frozen #12
parameterised on frozen #10, named `TreeIrred.Pointed.pointed_root_irreducible_of_rootBound`,
with EXACTLY this signature (the `hRB` binder is frozen #10 `TreeIrred/Theorems.lean:53-54`
written in arrow form, so that next iteration `… TreeIrred.admissible_root_bound_proof`
closes it in one line — you may NOT import Agent 1's file this iteration):
`theorem Pointed.pointed_root_irreducible_of_rootBound`
`    (hRB : ∀ (C : RTree), Admissible C → ∀ (x : ℕ → ℤ), NonzeroOn C x →`
`      0 < B C x x - x C.root)`
`    (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)`
`    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :`
`    ∃ u ∈ verts T, Irred T (basis u)`
Do NOT write `pointed_root_irreducible_proof` this iteration and do NOT leave a `sorry`.
PATH — BLUEPRINT Part 2 Stage H, items H2–H5 (BLUEPRINT.md:916-966) = SKETCH.md Theorem 1
(SKETCH.md:181-261). Destructure `T` as `.node v W c` (so `T.root = v`,
`verts T = v :: c.flatMap verts` by `verts_node`).
(a) Weight-one escape: `by_cases` on `∃ u ∈ verts T, wt T u = 1`; in the positive branch
the witness is that `u` and `Pointed.weight_one_irred` finishes. Otherwise `Pointed.wt_pos
T hnd hpd` upgrades to `∀ u ∈ verts T, 2 ≤ wt T u` (`0 < n` and `n ≠ 1` over ℤ is `omega`).
(b) `Admissible t` for EVERY `t ∈ c` (H3): feed `Pointed.admissible_of_deg t` with
`verts_child_nodup`, `wt_sub` (to see `wt T x = wt t x` for `x ∈ verts t`), `deg_sub` for
`x ∈ verts t`, `x ≠ t.root`, and `deg_subroot hnd ht : deg T t.root = deg t t.root + 1`
to turn `hgood` at `t.root` into `(deg t t.root : ℤ) + 1 ≤ wt t t.root`
(`verts_node_root_not_mem` gives `x ≠ v` for every `x ∈ verts t`, which is what licenses
`hgood`); the `2 ≤ wt` hypothesis comes from (a) plus `mem_verts_of_mem_child`.
(c) `Pointed.schur_pos` (H4, BLUEPRINT.md:938-943): with
`X : ℕ → ℚ := fun u => if u = v then 1 else (c.map (fun t => dual t u)).sum`, use
`dual_apply` (needs `(verts t).Nodup` + `Admissible t`, both from (b)) and `dual_vanish`
(dual of one child vanishes off that child's `verts`, so by `verts_node_nodup_disjoint`
the branches do not interfere and `X` agrees with `dual t` on `verts t`) to get
`BQ t X X = gamma t` and `X t.root = gamma t`; then `form_node` gives
`BQ T X X = (W : ℚ) - 2*Σγᵢ + Σγᵢ = W - Σγᵢ`. Since `X v = 1 ≠ 0` and `v ∈ verts T`,
`posDefQ_of_posDef T hpd X ⟨v, root_mem_verts, by simp⟩` gives
`0 < (W : ℚ) - (c.map gamma).sum`. State it as
`Pointed.schur_pos : ∀ (v : ℕ) (W : ℤ) (c : List RTree), (verts (.node v W c)).Nodup →
PosDef (.node v W c) → (∀ t ∈ c, Admissible t) → 0 < (W : ℚ) - (c.map gamma).sum`.
(d) H5 (BLUEPRINT.md:945-966): `rintro` a `Reducible T (basis v)` witness `⟨a, b, ha, hb,
hsplit, hab⟩`, set `z := fun u => -(b u)`. `Pointed.form_split_diag`/`form_congr` +
`form_add_left`/`form_neg_left` turn `0 ≤ B T a b` into `B T z z + B T (basis v) z ≤ 0`,
with `NonzeroOn T z` (from `hb`) and `NonzeroOn T (fun u => -(basis v u) - z u)` (from
`ha`). NORMALISATION: with `p := z v`, if `p ≤ -1` replace `z` by
`z' := fun u => -(basis v u) - z u` and PROVE the identity
`B T z' z' + B T (basis v) z' = B T z z + B T (basis v) z` explicitly (a `form_add/neg` +
`form_gram_entries_proof` computation), noting `z' v = -1 - p ≥ 0` and that the two
`NonzeroOn` facts swap; so WLOG `0 ≤ p`. ROW FORMULA: `B T (basis v) z = W*p - Σᵢ sᵢ` with
`sᵢ := z tᵢ.root`, from `form_node` + `form_vanish` (`basis v` vanishes on every
`verts tᵢ` by `hnd`). EXPANSION: `B T z z + B T (basis v) z = W*p*(p+1) +
Σᵢ (B tᵢ z z - (2p+1)*sᵢ)` (`form_node` + `form_congr` to restrict `z` to each `verts tᵢ`).
CASE `1 ≤ p`: `rooted_estimate_proof tᵢ (b) z p` gives `B tᵢ z z - (2p+1)*sᵢ ≥
-γᵢ*p*(p+1)` (in ℚ; bridge with `form_cast`), so the total is `≥ (W - Σγᵢ)*p*(p+1) > 0`
by (c) — contradicts `≤ 0`. CASE `p = 0`: the total is `Σᵢ (B tᵢ z z - sᵢ)`, each summand
`≥ 0` — it is `0` when `z` vanishes on `verts tᵢ` (`form_vanish`), and `> 0` otherwise by
`hRB tᵢ (b) z ⟨…⟩`; `NonzeroOn T z` with `z v = 0` and `verts T = v :: c.flatMap verts`
forces some `tᵢ` with `z` nonzero on `verts tᵢ`, so the total is `> 0` — contradiction.
Hence `Irred T (basis v)` and the witness is `v` (`root_mem_verts`).
MAY USE (all ✅; import `TreeIrred.Proofs.Model.Basic`, `TreeIrred.Proofs.NormOne.Basic`,
`TreeIrred.Proofs.Capacity.Basic`, `TreeIrred.Proofs.PosDef.Basic`,
`TreeIrred.Proofs.RootedEstimate.Basic` — NOT `Proofs/RootBound`, NOT `Proofs/Main`, per
R2): your own `Pointed.wt_pos`/`form_split_diag`/`weight_one_irred`/`admissible_of_deg`;
`form_gram_entries_proof`, `form_node`, `form_cast`, `form_congr`, `form_congr_right`,
`form_vanish`, `form_add_left`/`form_add_right`/`form_neg_left`/`form_sub_left`/
`form_zero_left`, `form_comm`, `verts_node`/`vwts_node`/`edges_node`, `root_mem_verts`,
`mem_verts_of_mem_child`, `verts_child_nodup`, `verts_node_nodup_disjoint`,
`verts_node_root_not_mem`, `kids_nodup`, `wt_sub`, `deg_root`, `deg_subroot`, `deg_sub`;
`capacity_pos_proof`, `capacity_lt_one_proof`, `capacity_node_formula_proof`,
`capacity_denom_pos_proof`, `Capacity.key`; `dual`, `dualScaled`, `dualScaled_node`,
`dualScaled_root`, `dual_apply`, `dual_vanish`, `psd_gamma`, `posDefQ_of_posDef`,
`PosDef.posDefQ`, `PosDef.form_node_split`, `PosDef.form_smul_left`,
`PosDef.sum_pos_of_mem`/`sum_nonneg_of_mem`; `rooted_estimate_proof`,
`RootedEstimate.sum_map_le`/`sum_map_nonneg`/`abs_sum_le_sum_abs`/`sum_diff`;
`admissible_posDef_proof`, `capacity_spec_proof`.
CHEAT-WATCH (BLUEPRINT.md:968-980 Stage H, plus D7/trap 1 at BLUEPRINT.md:258-282): the
`p ≤ -1` normalisation is a genuine SUBSTITUTION — prove the identity and RE-DERIVE BOTH
`NonzeroOn` facts for `z'`; dropping either is exactly how the `p = 0` case silently
becomes unprovable, and "WLOG `0 ≤ p`" without the identity is a cheat. Do NOT assume
`0 ≤ p`, do NOT assume `W < c.length` (`v`'s badness is NOT used anywhere — only (c)), and
`0 < W - Σγᵢ` must come from `hpd` via `posDefQ_of_posDef`, NEVER from `Admissible T`
(`T` is NOT admissible — `v` is precisely the vertex violating it) and never assumed. In
(b) `Admissible t` must hold for EVERY vertex inside `t`, not just child roots, and `deg`
stays the frozen unrooted `edges`-based `countP` (`d_T(x) = ch(x)+1` is DERIVED from
`deg_root`/`deg_subroot`, trap 3). Every "nonzero" is `NonzeroOn T ·`, never `≠ 0` as a
function, and the splitting hypothesis is `∀ u ∈ verts T, x u = a u + b u`, never
`x = a + b` (trap 1). The conclusion is `∃ u ∈ verts T, Irred T (basis u)` — in branch (a)
the witness is the WEIGHT-ONE vertex, not the root; do not "simplify" by always returning
the root. If (d) stalls, land (a)+(b)+(c) and any completed case of (d) as separately
named ✅ lemmas (e.g. `Pointed.expand_z`, `Pointed.case_p_pos`, `Pointed.case_p_zero`) and
log a ⚠️ naming the exact failing goal — do NOT leave a `sorry`.

Agent 3: OWNS `TreeIrred/Solution.lean` and `TreeIrred/Discharge.lean` (those two files
ONLY; nobody else may open them).
PRODUCE the wiring REVIEW.md Iteration-2 required follow-up #1 (REVIEW.md:91) demands, for
the THREE frozen theorems that became ✅ in Iteration 2 and are still scoring zero on
`scripts/verify.py` Checks 4/5: `capacity_spec`, `admissible_posDef`, `rooted_estimate`.
PATH: (1) In `TreeIrred/Solution.lean` re-add `import TreeIrred.Proofs.PosDef.Basic` and
`import TreeIrred.Proofs.RootedEstimate.Basic` (leave the three remaining stage imports —
`RootBound`, `Pointed`, `Main` — commented out/absent, they are being written right now and
importing them would couple your build to theirs). (2) Append to `namespace
TreeIrred.Solution`, copied CHARACTER-FOR-CHARACTER out of `TreeIrred/Theorems.lean`
(binder names, order, implicitness, every hypothesis — change NOTHING):
`theorem capacity_spec` (Theorems.lean:42-43) `:= TreeIrred.capacity_spec_proof C hnd hC`,
`theorem admissible_posDef` (:46) `:= TreeIrred.admissible_posDef_proof C hC`,
`theorem rooted_estimate` (:49-50) `:= TreeIrred.rooted_estimate_proof C hC x k`,
following exactly the style of the seven already wired at `Solution.lean:31-68`. (3) In
`TreeIrred/Discharge.lean` append the six matching gates, in the existing pattern:
`example : @TreeIrred.capacity_spec = @TreeIrred.capacity_spec_proof := rfl`
`example : @TreeIrred.capacity_spec = @TreeIrred.Solution.capacity_spec := rfl`
and likewise for `admissible_posDef` and `rooted_estimate` (20 gates total afterwards).
(4) Update the doc-comments in both files so they say the remaining THREE unwired names are
`admissible_root_bound`, `pointed_root_irreducible`, `tree_has_irreducible_vertex`.
Build with `lake build TreeIrred.Discharge` ONLY (R7) — never a bare `lake build`, which
would compile Agents 1/2/4's in-flight files through `TreeIrred.lean`.
MAY USE: `TreeIrred.capacity_spec_proof`, `TreeIrred.admissible_posDef_proof`,
`TreeIrred.rooted_estimate_proof` (all ✅ in Iteration 2, and REVIEW.md:79 records that all
three `@frozen = @proof := rfl` gates were independently verified by the auditor, so this
is mechanical).
CHEAT-WATCH (BLUEPRINT.md:1011-1019): a restatement must be the frozen proposition
verbatim — if a `rfl` gate FAILS to type-check, that is a genuine drift finding: log it as
⚠️ naming the offending `_proof` and its actual elaborated type, and do NOT edit the
restatement to match the proof, and NEVER edit `TreeIrred/Theorems.lean`. Note for your
`Check:` line: `verify.py` Check 4 emits ONE file containing all 13 `#print axioms`, so it
will keep reporting "no axiom output" until all 13 `Solution.<name>` exist — that is
EXPECTED this iteration, not a regression (REVIEW.md:68).

Agent 4: OWNS `TreeIrred/Proofs/Main/Basic.lean` (that file ONLY; it is currently a
14-line stub).
PRODUCE the whole of frozen #13 parameterised on frozen #12, named
`TreeIrred.Main.tree_has_irreducible_vertex_of_pointed`, with EXACTLY this signature (the
`hP` binder is frozen #12 `TreeIrred/Theorems.lean:63-65` written in arrow form, so that
next iteration `… TreeIrred.pointed_root_irreducible_proof` closes it in one line — you may
NOT import Agent 2's file this iteration):
`theorem Main.tree_has_irreducible_vertex_of_pointed`
`    (hP : ∀ (T : RTree), (verts T).Nodup → PosDef T →`
`      (∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) →`
`      ∃ u ∈ verts T, Irred T (basis u))`
`    (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)`
`    (v : ℕ) (hv : v ∈ verts T)`
`    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :`
`    ∃ u ∈ verts T, Irred T (basis u)`
Do NOT write `tree_has_irreducible_vertex_proof` this iteration and do NOT leave a `sorry`.
PATH — BLUEPRINT Part 2 Stage I, items I1–I2 (BLUEPRINT.md:982-997), and PROGRESS.md:128
(the Stage-G author's own recipe). (I1) `obtain ⟨T', hroot, hperm, hwt, hdeg, hB⟩ :=
TreeIrred.exists_reroot_at_proof T v hv`. Transport each hypothesis to `T'`:
`(verts T').Nodup` from `hperm` + `hnd` (`List.Perm.nodup` / `List.Perm.nodup_iff`; mind the
direction — `hperm : (verts T').Perm (verts T)`, so you want `hperm.symm`); `PosDef T'` by
unfolding `PosDef`/`NonzeroOn` and rewriting membership with `hperm.mem_iff` and the form
with `hB`; the Stage-H hypothesis `∀ u ∈ verts T', u ≠ T'.root → (deg T' u : ℤ) ≤ wt T' u`
from `hroot : T'.root = v`, `hperm.mem_iff`, `hwt`, `hdeg` and the `→` direction of
`huniq` (`u ∈ verts T`, `u ≠ v`, so `¬ (wt T u < deg T u)`, i.e. `deg T u ≤ wt T u`, by
`not_lt`/`omega`). (I2) Apply `hP T' …` to get `⟨u, hu', hirr'⟩`, then transport BACK:
`u ∈ verts T` by `hperm.mem_iff`, and `Irred T (basis u)` by showing
`Reducible T (basis u) → Reducible T' (basis u)` (same witnesses `a, b`; `NonzeroOn`
transports by `hperm.mem_iff`, the splitting condition `∀ w ∈ verts T', basis u w = a w +
b w` by `hperm.mem_iff`, and `0 ≤ B T' a b` by `hB`) and contradicting `hirr'`.
MAY USE (all ✅; import `TreeIrred.Proofs.Model.Basic` and `TreeIrred.Proofs.Reroot.Basic` —
and NOTHING from `Proofs/RootBound`, `Proofs/Pointed`, per R2): `exists_reroot_at_proof`,
`Reroot.form_eq_of_perms`, `Reroot.deg_eq_of_ekey_perm`, `Reroot.wt_eq_of_lookup_eq`,
`Reroot.exists_relabel`; `verts_node`, `root_mem_verts`, `form_congr`, `form_congr_right`,
`form_vanish`, `form_comm`, `form_add_left`; plus Mathlib's `List.Perm.nodup`,
`List.Perm.nodup_iff`, `List.Perm.mem_iff`.
CHEAT-WATCH (BLUEPRINT.md:999-1009 Stage I, and PROGRESS.md:116-121): `huniq` stays an
IFF at every vertex — do NOT replace it by `∀ u ∈ verts T, u ≠ v → deg T u ≤ wt T u` (that
drops `v`'s own badness and changes the theorem) and do NOT add `wt T v < deg T v` as a
separate hypothesis (it is already the `←` direction); only the `→` direction is consumed,
which is fine. Do NOT bypass Stage G by assuming `v = T.root`, and do NOT add any
hypothesis to the `hP` binder beyond frozen #12's four. BINDING (PROGRESS.md:116-121):
never assume that a one-step pivot preserves `wt` — obtain the rerooted tree ONLY from
`exists_reroot_at_proof`. Add a `norm_num` guardrail (R4, never `decide`) exercising the
transport on the concrete path `P := .node 0 2 [.node 1 2 [.node 2 2 []]]` at `v := 2`
(e.g. that `exists_reroot_at_proof P 2 …` yields a tree whose `deg`/`wt`/`B` agree with
`P`'s), so the statement is demonstrably non-vacuous. If the `Irred` transport stalls,
land the reusable pieces separately (`Main.reducible_transport`, `Main.posDef_transport`,
`Main.nonzeroOn_transport`) and log a ⚠️ with the exact failing goal — do NOT leave a
`sorry`.

## Iteration 4
Close the last three frozen theorems and wire ALL THIRTEEN into `Solution.lean`/`Discharge.lean`, taking `scripts/verify.py` from `RESULT: FAIL (2 issues)` to `RESULT: PASS`. Advances BLUEPRINT Stage H (#12), Stage I (#13) and the Discharge/Solution wiring stage; clears REVIEW.md Iteration-3 required follow-ups 1, 2 and 3 (REVIEW.md:112-114). ZERO mathematical content remains — every step below is a one-line term application whose `rfl` gate the auditor has already verified independently. SINGLE AGENT BY DESIGN: the wiring gap has now recurred three iterations in a row purely because `Solution.lean` was owned by an agent running concurrently with the agents landing the `_proof`s (REVIEW.md:107, REVIEW.md:113 "do NOT give `Solution.lean` to a separate agent running concurrently"). Do the four steps in the stated order.

Agent 1: OWNS EXACTLY FOUR FILES — `TreeIrred/Proofs/Pointed/Basic.lean`, `TreeIrred/Proofs/Main/Basic.lean`, `TreeIrred/Solution.lean`, `TreeIrred/Discharge.lean`. No other agent runs this iteration, so there is no concurrent-write hazard; do NOT touch any other file, and NEVER `TreeIrred/Defs.lean` or `TreeIrred/Theorems.lean` (both are SHA-pinned in `scripts/frozen.sha256`).
  STEP 1 — frozen #12 `pointed_root_irreducible`. In `TreeIrred/Proofs/Pointed/Basic.lean` add `import TreeIrred.Proofs.RootBound.Basic` to the existing import block (it is now ✅ and this is no longer forbidden), and append at TOP level inside `namespace TreeIrred` (NOT inside `namespace Pointed`), copying the statement character-for-character from `TreeIrred/Theorems.lean:63-65`:
    `theorem pointed_root_irreducible_proof (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)`
    `    (hgood : ∀ u ∈ verts T, u ≠ T.root → (deg T u : ℤ) ≤ wt T u) :`
    `    ∃ u ∈ verts T, Irred T (basis u) :=`
    `  TreeIrred.Pointed.pointed_root_irreducible_of_rootBound TreeIrred.admissible_root_bound_proof T hnd hpd hgood`
  Leave the four Iteration-2 lemmas and all of Iteration-3's `Pointed.*` content byte-identical — you are only adding one import and one theorem. Build with `lake build TreeIrred.Proofs.Pointed.Basic`.
  STEP 2 — frozen #13 `tree_has_irreducible_vertex` ★ HEADLINE. In `TreeIrred/Proofs/Main/Basic.lean` add `import TreeIrred.Proofs.Pointed.Basic` and append at TOP level inside `namespace TreeIrred` (NOT inside `namespace Main`), character-for-character from `TreeIrred/Theorems.lean:68-71`:
    `theorem tree_has_irreducible_vertex_proof (T : RTree) (hnd : (verts T).Nodup) (hpd : PosDef T)`
    `    (v : ℕ) (hv : v ∈ verts T)`
    `    (huniq : ∀ u ∈ verts T, (wt T u < (deg T u : ℤ) ↔ u = v)) :`
    `    ∃ u ∈ verts T, Irred T (basis u) :=`
    `  TreeIrred.Main.tree_has_irreducible_vertex_of_pointed TreeIrred.pointed_root_irreducible_proof T hnd hpd v hv huniq`
  Build with `lake build TreeIrred.Proofs.Main.Basic`.
  STEP 3 — wire all three into `TreeIrred/Solution.lean` (currently 10 of 13, ends at line 85 `end TreeIrred.Solution`). Add the three missing imports `import TreeIrred.Proofs.RootBound.Basic`, `import TreeIrred.Proofs.Pointed.Basic`, `import TreeIrred.Proofs.Main.Basic` (replacing the "deliberately absent" comment at Solution.lean:8-10), update the doc-comment at Solution.lean:23-26 to say all thirteen are wired, and append inside `namespace TreeIrred.Solution`, in numeric order, each restatement copied character-for-character out of `TreeIrred/Theorems.lean` (binder names, order, implicitness, every hypothesis — nothing generalised, nothing dropped, NOTHING ADDED):
    `theorem admissible_root_bound` (Theorems.lean:53-54) `:= TreeIrred.admissible_root_bound_proof C hC x hx` — place it between `rooted_estimate` and `exists_reroot_at`;
    `theorem pointed_root_irreducible` (Theorems.lean:63-65) `:= TreeIrred.pointed_root_irreducible_proof T hnd hpd hgood`;
    `theorem tree_has_irreducible_vertex` (Theorems.lean:68-71) `:= TreeIrred.tree_has_irreducible_vertex_proof T hnd hpd v hv huniq`.
  STEP 4 — six new gates in `TreeIrred/Discharge.lean`, in the existing two-per-name pattern, so it carries 24: `example : @TreeIrred.admissible_root_bound = @TreeIrred.admissible_root_bound_proof := rfl` and `… = @TreeIrred.Solution.admissible_root_bound := rfl` (as item `-- 10`, before the existing `-- 11 · exists_reroot_at` block), then the same pair for `pointed_root_irreducible` (`-- 12`) and `tree_has_irreducible_vertex` (`-- 13`) at the end. Update the doc-comment at Discharge.lean:15-18. Build with `lake build TreeIrred.Discharge`, then finally run `scripts/verify.py` and quote its verbatim output in your PROGRESS.md `Check:` line — Checks 4 and 5 must now pass for all 13 names (Check 4's "no axiom output" was expected only while some `Solution.<name>` was missing; it must NOT persist now that all 13 exist). Also record `#print axioms TreeIrred.Solution.tree_has_irreducible_vertex` (run out-of-tree via `lake env lean` on a scratch file in `/tmp`; never leave a `#print` in a project file) — it must be exactly `[propext, Classical.choice, Quot.sound]`, and `shasum -a 256 TreeIrred/Defs.lean TreeIrred/Theorems.lean` must still match `scripts/frozen.sha256`.
  MAY USE (all ✅ and sorry-free, verified by the auditor at REVIEW.md:102-105): `TreeIrred.admissible_root_bound_proof` (`Proofs/RootBound/Basic.lean:40`), `TreeIrred.Pointed.pointed_root_irreducible_of_rootBound` (`Proofs/Pointed/Basic.lean:351`), `TreeIrred.Main.tree_has_irreducible_vertex_of_pointed` (`Proofs/Main/Basic.lean:70`), and the ten `<name>_proof`s already wired in `Solution.lean:31-84`.
  SKETCH: this closes SKETCH.md Theorem 1 (the pointed form at SKETCH.md:241-259 and the re-rooting reduction at SKETCH.md:175-177 + Remark 1); no new SKETCH step is invoked — the mathematics is already formalized.
  CHEAT-WATCH (BLUEPRINT.md Stage H and Stage I boxes, plus BLUEPRINT.md:1011-1019 for the Discharge stage): a restatement must be the frozen proposition VERBATIM. `huniq` stays the frozen IFF at every vertex; `hgood` keeps `u ≠ T.root`; `admissible_root_bound`'s conclusion stays the STRICT `0 < B C x x - x C.root` with hypothesis `NonzeroOn C x`; do NOT add `(verts T).Nodup` to any statement that does not already carry it, and never assume a one-step pivot preserves `wt` (PROGRESS.md:116-121 — the rerooted tree comes only from `exists_reroot_at_proof`). If ANY `rfl` gate fails to type-check, that is a genuine drift finding: log it as ⚠️ in PROGRESS.md naming the offending `_proof` and its actual elaborated type — do NOT edit the restatement to match the proof, do NOT weaken anything, and NEVER edit `TreeIrred/Theorems.lean`. No `sorry`, no `axiom`, no `decide`/`native_decide` tactic, no deprecated `push_neg`; guardrails by `norm_num`/`simp` only; every line under 100 chars. Since you are the only agent, run `lake build` targets serially (never a bare `lake build` until Step 4, and never `lake update`/`lake exe cache get`); if `.lake/packages/mathlib` ever goes missing, repair it with the `cp -Rc` recipe at PROGRESS.md:74-79 rather than re-resolving the manifest.
