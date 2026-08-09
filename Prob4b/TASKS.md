# TASKS — Problem 4(b): a finite-conductor ring that is not quasi-coherent formalization

Append-only work-delegation log for 4 parallel worker agents. The Plan agent
appends one "## Iteration N" block per loop iteration. Each block has a one-line
goal then "Agent k: ..." lines (one per ACTIVE worker; inactive agents are
omitted). NEVER edit or delete an existing block.

## Iteration 1
Day-1 batch of BLUEPRINT's "Parallelism map": build the dependency-free foundations —
Stage A's normal form `nf`/`basisB` (BLUEPRINT Part 2 Stage A, A3/A4), Stage A's cheap
relation/Noetherian/`m³ = 0` lemmas (A1/A2/A5/A6-bridge), Stage F's dependency-free
converse (F6, frozen theorem 19) together with Stage D's `iota` support lemmas (D1/D2),
and Stage E's `Ramp` infrastructure (E0). REVIEW.md's only block is the INIT
faithfulness audit, verdict FAITHFUL with "Findings: none" — there are no required
follow-ups to clear. Nothing is `✅` in PROGRESS.md yet beyond SETUP, so this batch takes
only work whose prerequisites are the frozen `Defs.lean` alone.

RULES BINDING ON ALL FOUR AGENTS THIS ITERATION (read before writing code):
  * Complete the worker onboarding ritual of BLUEPRINT.md Part −1 §5: read this Agent
    line, read PROGRESS.md end to end (in particular the two SETUP `📝 decision` entries
    at 2026-08-09T16:27:31Z — the D0–D5 modeling decisions there are binding and must
    never be re-derived or changed), read the BLUEPRINT stage section named in your line
    INCLUDING its Cheat-watch box, then append a `🔧 in progress` PROGRESS entry claiming
    your files, then work, then append `✅`/`⚠️` entries. Use
    `date -u +"%Y-%m-%dT%H:%M:%SZ"` for timestamps; wrap lemma names in backticks on the
    `Next:` line; PROGRESS.md is append-only.
  * NEVER edit `Prob4b/Defs.lean` or `Prob4b/Theorems.lean` (SHA-pinned in
    `scripts/frozen.sha256`), never weaken or restate a frozen statement with an extra
    hypothesis, and never use another agent's file.
  * `sorry` is banned outside `Prob4b/Theorems.lean` (`scripts/verify.py` Check 2 greps
    for it), as are `native_decide` and any `axiom` declaration (`USER_NOTES.md`: "None —
    no assumed axioms"; `scripts/ALLOWED_AXIOMS.txt` is empty). Leave your file
    COMPILING at every point where you stop: if a lemma defeats you, delete the attempt,
    keep the file building, and log a `⚠️` entry with the exact failing goal. Never cite a
    frozen `Prob4b.<name>` from `Theorems.lean` in a proof — they are all still `sorry`
    and doing so would silently poison `#print axioms` with `sorryAx`.
  * Do NOT touch `Prob4b/Solution.lean` or `Prob4b/Discharge.lean` this iteration — they
    are shared files and wiring them in parallel would collide. Produce your frozen
    theorems as `<name>_proof` declarations in your own file; a later iteration wires
    them. State this hand-off explicitly on your PROGRESS `Next:` line.
  * All declarations live in `namespace Prob4b`; never shadow a frozen name (append
    `_proof` for a frozen theorem, e.g. `B_relation_proof`). `lakefile.toml` leaves
    `weak.linter.mathlibStandardSet` ON, so every file needs the 4-line copyright header,
    a module docstring right after the imports, a docstring on every declaration, and
    lines ≤ 100 characters — otherwise `lake build` emits warnings and verify.py Check 3
    fails.
  * `Balg`, `Mmod`, `Cring`, `Ramp` are NONCOMPUTABLE (`Ideal.Quotient` /
    `Submodule.Quotient` / `Classical.choose`): `decide` does not reduce on them. Finite
    checks must be transported into `Idx → ZMod 2` or `Fin 4 → ZMod 2`.
  * Finish with `lake build <your module target>` (e.g.
    `lake build Prob4b.Proofs.StageA_Algebra.Basic`) clean, and paste the
    `#print axioms Prob4b.<name>_proof` output (must be exactly
    `propext, Classical.choice, Quot.sound`, no `sorryAx`) into the `Check:` line of your
    `✅` PROGRESS entry. Never mark `✅` what does not compile cleanly.

Agent 1: OWNS the single NEW file `Prob4b/Proofs/StageA_Algebra/NormalForm.lean` (create
  it; it must `import Prob4b.Defs` only). Do NOT edit
  `Prob4b/Proofs/StageA_Algebra/Basic.lean` — Agent 2 owns it and is editing it in
  parallel — and in particular do NOT add an import of your file to it; instead put
  "wire `import Prob4b.Proofs.StageA_Algebra.NormalForm` into
  `Prob4b/Proofs/StageA_Algebra/Basic.lean`" on your PROGRESS `Next:` line, since until
  that is done your module is reachable only via the explicit target
  `lake build Prob4b.Proofs.StageA_Algebra.NormalForm` (which you MUST run and get clean)
  and not via the root `Prob4b.lean`.
  TASK: BLUEPRINT Part 2 Stage A steps **A3 (the normal form — "the hardest engineering
  in the project", budget accordingly) and A4**, following SKETCH.md Step 1
  (`B = F₂[a,b,c,d]/((a,b,c,d)³, ad+bc)`). Produce, with these exact names:
    - `Idx : Type` := `Unit ⊕ Fin 4 ⊕ Fin 9`, a 14-element `Fintype`/`DecidableEq` index
      for the monomial basis `1; a,b,c,d; a², ab, ac, ad, b², bd, c², cd, d²` (note `bc`
      is deliberately NOT in the list — the relation makes `bc = ad`);
    - `nfPol : Pol →ₗ[ZMod 2] (Idx → ZMod 2)`, the `Finsupp`-linear extension sending a
      monomial of total degree ≥ 3 to `0`, a monomial of degree ≤ 2 to its own basis
      vector, and `bc` to the basis vector of `ad`;
    - `nfPol_relIdeal_le_ker : relIdeal ≤ LinearMap.ker nfPol` (elements of `relIdeal` are
      `p·μ` with `μ` a degree-3 monomial — every monomial of the product has degree ≥ 3 —
      plus `q·(ad+bc)`; split `q` into its constant term, which gives
      `ad + bc ↦ e_ad + e_ad = 0` in char 2, and its positive-degree part, which gives
      only degree ≥ 3 monomials);
    - `nf : Balg →ₗ[ZMod 2] (Idx → ZMod 2)` (descend `nfPol` through
      `Ideal.Quotient` / `Submodule.liftQ`);
    - `sec : (Idx → ZMod 2) →ₗ[ZMod 2] Balg` sending each index to the class of the
      corresponding monomial;
    - `nf_sec : nf ∘ₗ sec = LinearMap.id` (a 14-case `decide`/`fin_cases` on `Idx`, all
      inside the computable type `Idx → ZMod 2`) AND `sec_nf : sec ∘ₗ nf = LinearMap.id`
      (surjectivity of `sec`: the 14 monomial classes span `Balg` because every monomial
      of degree ≥ 3 is `0` and `bc = ad`). BOTH directions are mandatory — Cheat-watch
      (d): with only one you can prove `x ≠ 0` from `nf x ≠ 0` but not `x = 0` from
      `nf x = 0`, and Stage B needs both;
    - `basisB : Basis Idx (ZMod 2) Balg` packaging the pair;
    - the evaluation simp lemmas `nf_one`, `nf_xa`, `nf_xb`, `nf_xc`, `nf_xd`, and the
      degree-2 ones `nf_xa_mul_xa`, `nf_xa_mul_xb`, `nf_xa_mul_xc`, `nf_xa_mul_xd`,
      `nf_xb_mul_xb`, `nf_xb_mul_xc`, `nf_xb_mul_xd`, `nf_xc_mul_xc`, `nf_xc_mul_xd`,
      `nf_xd_mul_xd` — these are what Stages B and C compute with;
    - the frozen theorem 1 as `B_nontrivial_proof : Nontrivial Balg`, derived from
      `nf 1 ≠ 0` / `basisB`.
  CHEAT-WATCH (BLUEPRINT Stage A box — binding): (a) do NOT replace `Balg` by a
  hand-tabulated `Fin 14 → ZMod 2` ring "for `decide`-ability" — that redefines a frozen
  object; (b) `B_nontrivial_proof` must NOT be `by decide`, `native_decide`, or `simp` on
  faith — it must come from the explicit functional `nf`; (d) two-sided inverse as above;
  (e) keep these guardrail `example`s in the file:
  `example : nf (xa * xd) = nf (xb * xc)` (the relation is live) and
  `example : xa * xb ≠ 0` (the degree-2 part did not collapse).
  `decide` budget: 256 cases is fine, 4096 cases times a span-membership search is not —
  factor the check; if a `decide` times out, restructure, never switch to `native_decide`.
  MAY USE: `Prob4b/Defs.lean` only (nothing else is `✅` yet).

Agent 2: OWNS `Prob4b/Proofs/StageA_Algebra/Basic.lean` (the existing SETUP placeholder,
  already imported by `Prob4b.lean` and `Prob4b/Solution.lean`, so it is covered by a
  plain `lake build`). Keep its `import Prob4b.Defs` as the ONLY import — do NOT add
  `import Prob4b.Proofs.StageA_Algebra.NormalForm` this iteration (Agent 1 is creating
  that file in parallel; wiring it is a later iteration's job). Do not create other files.
  TASK: BLUEPRINT Part 2 Stage A steps **A1, A2, A5** plus the D0 bridge lemma, following
  SKETCH.md Step 1. Produce, with these exact names:
    - `B_relation_proof : xa * xd + xb * xc = 0` (frozen theorem 2) — via
      `Ideal.Quotient.eq_zero_iff_mem` and `Ideal.subset_span` / `le_sup_right` into
      `relIdeal = mPol ^ 3 ⊔ Ideal.span {X 0 * X 3 + X 1 * X 2}`;
    - `B_relation' : xa * xd = xb * xc` (char 2: `-1 = 1`) — later stages use the equation
      form constantly;
    - `mB_eq_map : mB = Ideal.map (Ideal.Quotient.mk relIdeal) mPol`;
    - `B_maximalIdeal_pow_three_proof : mB ^ 3 = ⊥` (frozen theorem 4) — route:
      `mB ^ 3 = Ideal.map _ (mPol ^ 3) ≤ Ideal.map _ relIdeal = ⊥` via `Ideal.map_pow`
      and `Ideal.map_eq_bot_iff_le_ker`. It must be proved for the IDEAL POWER `mB ^ 3`
      (which includes coefficients), not for "products of three of the four generators"
      — Cheat-watch (c);
    - `mul_mem_mB_three : ∀ {x y z : Balg}, x ∈ mB → y ∈ mB → z ∈ mB → x * y * z = 0`
      (corollary of the previous, used all over Stages B/C);
    - `B_isNoetherianRing_proof : IsNoetherianRing Balg` (frozen theorem 3) —
      `MvPolynomial.isNoetherianRing` (Hilbert basis; `Fin 4` is a `Fintype`, `ZMod 2` a
      field) then
      `isNoetherianRing_of_surjective Pol Balg (Ideal.Quotient.mk relIdeal)
      Ideal.Quotient.mk_surjective`. If that transfer lemma's name has drifted at Mathlib
      rev `fabf563a`, find the current spelling with `exact?`/`loogle` and log the route
      you used as a `📝` PROGRESS entry (do NOT fall back on a `sorry`d instance);
    - `mem_ann : ∀ {S : Type*} [CommRing S] (x y : S), y ∈ ann x ↔ y * x = 0` — the D0
      bridge lemma BLUEPRINT Part −1 §2 (D0) explicitly requires Stage A to produce and
      log, via `Submodule.mem_colon` + `Ideal.mem_span_singleton`. Every later stage reads
      `ann` through it.
  CHEAT-WATCH: never prove any of these by `decide`/`native_decide` on `Balg` (it is
  noncomputable). Do not "fix" a failing guardrail by changing the guardrail — a failure
  here means the construction collapsed and must be reported as `⚠️`.
  MAY USE: `Prob4b/Defs.lean` only (nothing else is `✅` yet); in particular do NOT use
  `nf`, which Agent 1 is building in parallel.

Agent 3: OWNS `Prob4b/Proofs/StageF_Headline/Basic.lean` AND
  `Prob4b/Proofs/StageD_Idealization/Basic.lean` (both existing SETUP placeholders,
  already imported by `Prob4b.lean`/`Solution.lean`). Do not touch any other file. Both
  tasks below depend on NOTHING from Stages A/B/C, which is why they are paired here.
  TASK 3a (in `StageF_Headline/Basic.lean`) — BLUEPRINT Part 2 Stage F step **F6**,
  SKETCH.md preamble "Recall" (lines 5–17). Produce:
    - `iInf_fin_two : ∀ {S : Type*} [CommRing S] (x y : S),
      (⨅ i, Ideal.span {![x, y] i} : Ideal S) = Ideal.span {x} ⊓ Ideal.span {y}`
      (support; `Fin.cases`/`iInf` over `Fin 2` — `le_antisymm` with `iInf_le` and
      `le_iInf`);
    - `quasiCoherent_imp_finiteConductor_proof :
      ∀ {S : Type u} [inst : CommRing S], QuasiCoherent S → FiniteConductor S`
      (frozen theorem 19) — given `⟨h₁, h₂⟩`, produce `⟨h₁, fun x y => ?_⟩` by applying
      `h₂ 2 ![x, y]` and rewriting with `iInf_fin_two`. It MUST be stated with the
      universe variable `u` and the instance binder exactly as frozen, so it is the
      general implication and not the `Ramp` instance. `Prob4b/Solution.lean` sets
      `linter.unusedVariables false` for this shape; add the same `set_option` locally if
      the linter complains about `inst`.
  TASK 3b (in `StageD_Idealization/Basic.lean`) — BLUEPRINT Part 2 Stage D steps **D1 and
  D2** (support lemmas only; `C_ann_eq`/`C_pair_inter`/`C_isNoetherianRing`/
  `C_triple_defect` are NOT in scope, they need Stage C). SKETCH.md Step 4. Produce:
    - `map_iota_eq : ∀ J : Ideal Balg, Ideal.map iota J =
      {c : Cring | c.fst ∈ J ∧ c.snd ∈ (smulTop J : Submodule Balg Mmod)}` (as an ideal
      equality, i.e. via `Ideal.ext`/`SetLike.ext` and membership) — `≤` by
      `Ideal.map_le_iff_le_comap` on generators; `≥` by writing
      `c = TrivSqZeroExt.inl c.fst + TrivSqZeroExt.inr c.snd` and expanding `c.snd` as a
      finite sum `Σ jₖ • nₖ` with `jₖ ∈ J` (`Submodule.smul_induction_on`), each term
      being `iota jₖ * TrivSqZeroExt.inr nₖ`;
    - `iota_mem_map_iff : ∀ (J : Ideal Balg) (z : Balg),
      iota z ∈ Ideal.map iota J ↔ z ∈ J` (Stage E consumes this);
    - `span_iota_eq : ∀ x : Balg, Ideal.span {iota x} =
      {c : Cring | c.fst ∈ Ideal.span {x} ∧
       c.snd ∈ (smulTop (Ideal.span {x}) : Submodule Balg Mmod)}` — the `J = span {x}`
      case of D1, worth its own name because `iota x * (z, n) = (x*z, x • n)`;
    - the arithmetic simp lemmas you need for the above, e.g.
      `iota_apply_fst`/`iota_apply_snd` and `iota_mul_eq` (`iota x * c = (x * c.fst,
      x • c.snd)`), stated via `TrivSqZeroExt.fst_mul`/`snd_mul`/`fst_inl`/`snd_inl`.
  CHEAT-WATCH (Stage D box (b), (d) — binding): the right-hand sides are EXTENSIONS of
  ideals of `B` (`Ideal.map iota`), not "ideals of `C` containing the image"; do not
  substitute a `Ideal.comap`-flavoured surrogate. Never conflate `iota x` with `x`, or
  `TrivSqZeroExt.inr uElt` with `uElt`, or `smulTop (Ideal.span {x}) :
  Submodule Balg Mmod` with `Ideal.span {x} : Ideal Balg` — mixing the module side and the
  ring side is the most likely SILENT bug in this project. `Cring` is noncomputable: no
  `decide`. The guardrail `example : (1 : Cring) ≠ 0` needs `Nontrivial Balg`, which is
  Agent 1's `B_nontrivial_proof` and is NOT available yet — do not attempt it, note it on
  your `Next:` line instead.
  MAY USE: `Prob4b/Defs.lean` only (nothing else is `✅` yet).

Agent 4: OWNS `Prob4b/Proofs/StageE_Amplify/Basic.lean` (the existing SETUP placeholder,
  already imported by `Prob4b.lean`/`Solution.lean`). Do not touch any other file.
  TASK: BLUEPRINT Part 2 Stage E step **E0 only** (`Ramp` infrastructure). `R_ann_fg`
  (E1), `R_pair_inter_fg` (E2) and `R_finiteConductor` (E3) are explicitly OUT OF SCOPE —
  they need `B_isNoetherianRing`, `C_isNoetherianRing`, `C_ann_eq` and `C_pair_inter`,
  none of which is `✅`. Everything below needs only `Prob4b/Defs.lean` D5 and the
  `CommRing` structure. SKETCH.md Step 5 (`R = Δ(B) + C^(ℕ) ⊆ C^ℕ`). Produce, with these
  exact names:
    - `mem_Rsub_iff : ∀ f : ℕ → Cring, f ∈ Rsub ↔ ∃ x : Balg, {n | f n ≠ iota x}.Finite`
      (unfold the frozen carrier once, then never unfold it again);
    - `tail_unique : ∀ (f : Ramp) (x y : Balg), {n | (f : ℕ → Cring) n ≠ iota x}.Finite →
      {n | (f : ℕ → Cring) n ≠ iota y}.Finite → x = y` — two cofinite sets meet, so pick
      `n` outside the (finite) union using `Set.Finite.union` + `Set.infinite_univ` /
      `Set.Infinite.nonempty`, giving `iota x = f n = iota y`, then conclude with
      injectivity of `iota` (`TrivSqZeroExt.inl_injective`, or apply
      `TrivSqZeroExt.fst`);
    - `tailValue : Ramp → Balg` defined by `Classical.choose` on the carrier witness,
      with `tailValue_spec : ∀ f : Ramp,
      {n | (f : ℕ → Cring) n ≠ iota (tailValue f)}.Finite` and the characterisation
      `tailValue_eq_of : ∀ (f : Ramp) (x : Balg),
      {n | (f : ℕ → Cring) n ≠ iota x}.Finite → tailValue f = x` (from `tail_unique`);
    - `tailValue_diag : ∀ x : Balg, tailValue (diag x) = x`, `tailValue_zero`,
      `tailValue_one`, and the ring-hom lemmas `tailValue_add`, `tailValue_mul`;
    - `exc : Ramp → Set ℕ` := `{n | (f : ℕ → Cring) n ≠ iota (tailValue f)}`, with
      `exc_finite : ∀ f : Ramp, (exc f).Finite` and
      `apply_eq_of_not_mem_exc : ∀ (f : Ramp) (n : ℕ), n ∉ exc f →
      (f : ℕ → Cring) n = iota (tailValue f)`;
    - `coordAt (n : ℕ) (c : Cring) : Ramp` — the element that is `c` at `n` and `0`
      elsewhere (its tail value is `0`), with simp lemmas `coordAt_apply_self`,
      `coordAt_apply_ne`, `coordAt_mul`
      (`coordAt n c * f = coordAt n (c * (f : ℕ → Cring) n)`), and `coordAt_add`;
    - `offSet (S : Set ℕ) (hS : S.Finite) (x : Balg) : Ramp` — equal to `iota x` off `S`
      and `0` on `S` (use `Classical.dec` / `open scoped Classical` for the membership
      test), with `offSet_apply_mem`, `offSet_apply_not_mem`, and
      `tailValue_offSet : tailValue (offSet S hS x) = x`;
    - `mem_ideal_span_finset : ∀ (s : Finset Ramp) (h : Ramp), h ∈ Ideal.span (↑s : Set Ramp)
      ↔ ∃ g : Ramp → Ramp, h = ∑ i ∈ s, g i * i` (a thin wrapper on
      `Submodule.mem_span_finset`, consumed by Stage F's F4).
  CHEAT-WATCH (Stage E box — binding, even though E1/E2 are out of scope): (b) `Ramp` is
  NOT Noetherian — that is exactly what Stage F refutes — so never introduce a lemma or
  instance asserting it; every finiteness must trace back to `B`/`C` Noetherianity plus a
  finite exceptional set. (f) the guardrail `example : (diag xa : Ramp) ≠ 0` needs
  `B_nontrivial` and `example : uAt 0 ≠ (0 : Ramp)` needs `M_u_ne_zero`; NEITHER is `✅`
  yet, so do not attempt them — record them on your `Next:` line for a later iteration.
  Also do not confuse `Δ(B) + C^(ℕ)` with `C^(ℕ)` or `C^ℕ`: the carrier's tail value is an
  element of `Balg` seen through `iota`, never an arbitrary element of `Cring`.
  MAY USE: `Prob4b/Defs.lean` only (nothing else is `✅` yet).

## Iteration 2
Clear REVIEW.md's required follow-ups 1/2/5 (WIRE the five already-proved frozen theorems
into `Discharge.lean`/`Solution.lean` so Check 4 drops 20 → 15, and add the now-unblocked
guardrail `example`s), then attack the two remaining pieces of REAL mathematics whose only
prerequisite is the `✅` Stage A normal form: BLUEPRINT Stage B (**B1 `B_colon_two_gen`,
the MILESTONE / "mathematical heart"**, and **B2 `B_triple_inter_eq_bot`**, which is
independent of B1) and the Stage-A-only half of Stage C (**C3 `M_u_mem_triple`,
C4 `M_u_ne_zero`**), plus Stage D's dependency-free **D5 `C_isNoetherianRing`**.
Stage C's C1/C2 (`M_ann_eq`, `M_pair_inter`), C5, D3/D4/D6, and all of E1/E2/E3 and
F1–F5/F7 are deliberately OUT OF SCOPE this iteration — every one of them consumes
`B_colon_two_gen` or `B_triple_inter_eq_bot`, which are being proved right now.

RULES BINDING ON ALL AGENTS THIS ITERATION (read before writing code):
  * Complete the worker onboarding ritual of BLUEPRINT.md Part −1 §5: read your own
    `Agent k:` line below (ignore the others — they are running in parallel), read
    PROGRESS.md END TO END (in particular the two SETUP `📝 decision` entries at
    2026-08-09T16:27:31Z, whose D0–D5 modeling choices are binding; the `📝` colon-API
    entry at 2026-08-09T16:42:30Z, which fixes how `ann`/`colonI` may be unfolded; and the
    two spelling decisions on the `Next:` line of the 2026-08-09T17:01:26Z entry —
    `nfPol_relIdeal_le_ker` is a SET inclusion with usable form
    `nfPol_eq_zero_of_mem_relIdeal`, and the basis type is `Module.Basis`, not `Basis`),
    then read the BLUEPRINT stage section your line names INCLUDING its Cheat-watch box,
    then append a `🔧 in progress` PROGRESS entry claiming your files, then work, then
    append `✅`/`⚠️` entries. Timestamps from `date -u +"%Y-%m-%dT%H:%M:%SZ"`; backtick
    every lemma name on the `Next:` line; PROGRESS.md is APPEND-ONLY.
  * NEVER edit `Prob4b/Defs.lean` or `Prob4b/Theorems.lean` (SHA-pinned in
    `scripts/frozen.sha256`), never weaken/restate a frozen statement or add a hypothesis
    to it, and never edit a file another agent owns.
  * `sorry` is banned outside `Prob4b/Theorems.lean`, as are `native_decide` and any
    `axiom` declaration (`USER_NOTES.md`: "None — no assumed axioms";
    `scripts/ALLOWED_AXIOMS.txt` is empty). Leave every file you own COMPILING at every
    point where you stop: if a lemma defeats you, delete the attempt, keep the file
    building, and log a `⚠️` entry quoting the exact failing goal.
  * NEVER cite a still-`sorry` frozen name from `Theorems.lean` in a proof (that silently
    poisons `#print axioms` with `sorryAx`). Use the `_proof` declarations instead. The
    following are `✅` sorry-free and MAY be used: `B_nontrivial_proof`, `nf`, `sec`,
    `nf_sec`, `sec_nf`, `basisB`, `nf_one`, `nf_xa`…`nf_xd`, the ten `nf_x?_mul_x?`
    lemmas, `nfPol`, `nfPol_eq_zero_of_mem_relIdeal` (all in
    `Prob4b/Proofs/StageA_Algebra/NormalForm.lean`); `B_relation_proof`, `B_relation'`,
    `B_neg_eq`, `B_two_eq_zero`, `mB_eq_map`, `B_maximalIdeal_pow_three_proof`,
    `mul_mem_mB_three`, `B_isNoetherianRing_proof`, `mem_ann` (in
    `Prob4b/Proofs/StageA_Algebra/Basic.lean`); `map_iota_eq`, `mem_map_iota_iff`,
    `iota_mem_map_iff`, `span_iota_eq`, `mem_span_iota_iff`, `iota_mul_eq`,
    `map_iota_span_singleton`, `smul_mem_smulTop` (in
    `Prob4b/Proofs/StageD_Idealization/Basic.lean`); the whole E0 layer in
    `Prob4b/Proofs/StageE_Amplify/Basic.lean`; `iInf_fin_two` and
    `quasiCoherent_imp_finiteConductor_proof` (in
    `Prob4b/Proofs/StageF_Headline/Basic.lean`). NOT yet proved and NOT usable:
    `B_colon_two_gen`, `B_triple_inter_eq_bot`, `M_ann_eq`, `M_pair_inter`, `M_u_ne_zero`,
    `M_u_mem_triple`, `M_triple_defect`, `C_*`, `R_*` and the headline.
  * All declarations live in `namespace Prob4b`; never shadow a frozen name (append
    `_proof` for a frozen theorem). Because several files share this namespace, DO NOT
    invent a support-lemma name another agent's line below also claims — the per-agent
    name prefixes given below are binding.
  * `lakefile.toml` leaves `weak.linter.mathlibStandardSet` ON: every file needs the
    4-line copyright header, a module docstring right after the imports, a docstring on
    every declaration, and lines ≤ 100 characters, or `lake build` warns and verify.py
    Check 3 fails.
  * `Balg`, `Mmod`, `Cring`, `Ramp` are NONCOMPUTABLE (`Ideal.Quotient` /
    `Submodule.Quotient` / `Classical.choose`): `decide` does NOT reduce on them. Every
    finite check must be transported through `nf` into `Idx → ZMod 2` (or into
    `Fin 4 → ZMod 2`), which IS computable. Budget: 256 cases fine, 4096 cases times a
    span-membership search is not — factor the check. If a `decide` times out,
    restructure; NEVER switch to `native_decide`.
  * PARALLEL-BUILD NOTE: `Prob4b.lean` imports the Stage A–F `Basic.lean` modules, so a
    full `lake build` compiles files other agents are editing right now. Judge your own
    work by `lake build <your module target>` and treat errors originating in files you do
    not own as transient artifacts of a parallel edit — report them, never "fix" them.
  * Finish with `lake build <your module target>` clean and paste the
    `#print axioms Prob4b.<name>` output (must be exactly `propext, Classical.choice,
    Quot.sound`, no `sorryAx`) into the `Check:` line of your `✅` PROGRESS entry.

Agent 1: OWNS `Prob4b.lean`, `Prob4b/Discharge.lean`, `Prob4b/Solution.lean` (the three
  SHARED wiring files — no other agent may touch them) AND
  `Prob4b/Proofs/StageD_Idealization/Basic.lean`. Do not touch any other file.
  TASK 1a — REVIEW.md "Required follow-ups" 1 and 2, do this FIRST and completely before
  starting 1b. (i) Add `import Prob4b.Proofs.StageA_Algebra.NormalForm` to BOTH
  `Prob4b.lean` and `Prob4b/Solution.lean` (that module is currently ORPHANED — imported
  by nothing — so plain `lake build` never compiles it and its five sorry-free results are
  invisible to the harness). (ii) In `Prob4b/Discharge.lean` add exactly these five gates
    `example : @Prob4b.B_nontrivial = @Prob4b.B_nontrivial_proof := rfl`
    `example : @Prob4b.B_relation = @Prob4b.B_relation_proof := rfl`
    `example : @Prob4b.B_isNoetherianRing = @Prob4b.B_isNoetherianRing_proof := rfl`
    `example : @Prob4b.B_maximalIdeal_pow_three = @Prob4b.B_maximalIdeal_pow_three_proof := rfl`
    `example : @Prob4b.quasiCoherent_imp_finiteConductor =
       @Prob4b.quasiCoherent_imp_finiteConductor_proof := rfl`
  (REVIEW.md line 68 confirms all five already typecheck — this is mechanical.)
  (iii) In `Prob4b/Solution.lean` replace the right-hand side of the five forwarding stubs
  `B_nontrivial` (line 38), `B_relation` (41), `B_isNoetherianRing` (44),
  `B_maximalIdeal_pow_three` (47) and `quasiCoherent_imp_finiteConductor` (116-118) by
  `_root_.Prob4b.<name>_proof`, leaving EVERYTHING to the left of `:=` byte-identical
  (statements, docstrings, `set_option linter.unusedVariables false`, `universe u` and the
  `namespace Prob4b.Solution` block all stay exactly as they are). (iv) Run
  `python3 scripts/verify.py` and confirm Check 4 drops from 20 `sorryAx` names to 15 (the
  15 still-unproved frozen names); paste the Check-4 line into your `✅` PROGRESS entry.
  TASK 1b (in `Prob4b/Proofs/StageD_Idealization/Basic.lean`) — BLUEPRINT Part 2 Stage D
  step **D5**, SKETCH.md Step 4 ("controlled by the Noetherian ring `B`"). Add
  `import Prob4b.Proofs.StageA_Algebra.Basic` and
  `import Prob4b.Proofs.StageA_Algebra.NormalForm` to that file (it currently imports only
  `Prob4b.Defs`) and produce `C_isNoetherianRing_proof : IsNoetherianRing Cring` (frozen
  theorem 12). PRIMARY ROUTE: `Cring = TrivSqZeroExt Balg Mmod` is a finitely generated
  `Balg`-module (`Mmod` is a quotient of `Fin 4 → Balg`, hence f.g.; `Cring ≃ₗ[Balg] Balg ×
  Mmod`), and `Balg` is Noetherian (`B_isNoetherianRing_proof`), so `Cring` is a Noetherian
  `Balg`-module (`Module.Finite` + `isNoetherian_of_fg_of_noetherian'` /
  `IsNoetherian.iff_fg`); then every ideal `I : Ideal Cring`, viewed as a `Balg`-submodule
  by `Submodule.restrictScalars Balg`, is f.g., and the same finite set generates `I` as a
  `Cring`-ideal (`Ideal.span s ≤ I` since `s ⊆ I`, and `I ≤ Submodule.span Balg s ≤
  Ideal.span s`) — spell this out as a support lemma `fg_of_fg_restrictScalars`, then use
  `isNoetherianRing_iff_ideal_fg` (check the live spelling with `exact?`/`loogle` at
  Mathlib rev `fabf563a`). FALLBACK ROUTE if the transfer fights you: `Balg` is a FINITE
  type (`basisB : Module.Basis Idx (ZMod 2) Balg` with `Fintype Idx`, so
  `Module.Basis.equivFun` gives `Balg ≃ₗ (Idx → ZMod 2)`), hence `Mmod` and `Cring` are
  finite, and every ideal of a finite ring is f.g. because the ideal's own (finite)
  underlying set generates it. Log whichever route worked as a `📝` PROGRESS entry.
  Also add the now-unblocked Stage D guardrail `example : (1 : Cring) ≠ 0` (REVIEW
  follow-up 5; it needs `Nontrivial Balg`, i.e. `B_nontrivial_proof`, which is now
  importable). The second Stage D guardrail
  `example : (TrivSqZeroExt.inr uElt : Cring) ≠ 0` needs `M_u_ne_zero`, which Agent 4 is
  proving in parallel — do NOT attempt it, record it on your `Next:` line.
  If and only if `C_isNoetherianRing_proof` compiles clean, ALSO wire it (a sixth gate in
  `Discharge.lean` and the sixth stub replacement in `Solution.lean` at line 86), and
  re-run `scripts/verify.py` expecting 14 remaining `sorryAx` names.
  CHEAT-WATCH (BLUEPRINT Stage D box (c) — binding): do NOT obtain `C_isNoetherianRing` by
  declaring an instance backed by a `sorry`ed helper, and do NOT weaken it to "`Cring` is
  Noetherian as a `Balg`-module" — Stage E needs finite generation of `Cring`-IDEALS.
  Do not conflate `iota x` with `x`, or `TrivSqZeroExt.inr uElt` with `uElt`.
  MAY USE: everything in the `✅` list of the binding rules above.

Agent 2: OWNS `Prob4b/Proofs/StageB_Colon/Basic.lean` (the SETUP placeholder — already
  imported by `Prob4b.lean` and `Prob4b/Solution.lean`, so it is covered by a plain
  `lake build`). Replace its `import Prob4b.Defs` line by
  `import Prob4b.Proofs.StageA_Algebra.Basic` and
  `import Prob4b.Proofs.StageA_Algebra.NormalForm` (both transitively import
  `Prob4b.Defs`). Do NOT create or edit `Prob4b/Proofs/StageB_Colon/TripleInter.lean` —
  Agent 3 owns it — and do not touch `Prob4b/Proofs/StageA_Algebra/*`.
  TASK: BLUEPRINT Part 2 Stage A step **A6** followed by Stage B step **B1**, the project
  MILESTONE, following SKETCH.md Step 2 (lines 99-113: `(I : m) = I + m²` for every ideal
  generated by at most two elements). Produce, with these exact names:
    - `mem_mB_iff : ∀ x : Balg, x ∈ mB ↔ nf x (Sum.inl ()) = 0` ("`x` has zero constant
      term"); `⊆` from `mB = span {xa,xb,xc,xd}` and the `nf` evaluation lemmas, `⊇` by
      writing `x = sec (nf x)` (`sec_nf`) and observing that every basis index other than
      `Sum.inl ()` maps to a monomial lying in `mB`;
    - `isUnit_of_not_mem_mB : ∀ x : Balg, x ∉ mB → IsUnit x` — if the constant term is `1`
      then `x = 1 + y` with `y ∈ mB`, and `(1 + y) * (1 + y + y * y) = 1` because
      `y * y * y = 0` (`mul_mem_mB_three`) and char 2 (`B_neg_eq`, `B_two_eq_zero`);
    - `B_colon_two_gen_proof : ∀ x y : Balg,
      colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2` (frozen theorem 5).
  PATH (BLUEPRINT Stage B, B1 — follow it in exactly this order and log each step as you
  close it): `⊇` is easy — `I ≤ (I : m)` because `I * mB ⊆ I`, and `mB ^ 2 ≤ (I : m)`
  because `mB ^ 2 * mB = mB ^ 3 = ⊥` (`B_maximalIdeal_pow_three_proof`); use
  `Submodule.mem_colon` and `sup_le`. The CONTENT is `⊆`, via: (1) UNIT CASE — if `x ∉ mB`
  or `y ∉ mB` then that generator is a unit by `isUnit_of_not_mem_mB`, so
  `Ideal.span {x, y} = ⊤` and both sides are `⊤`. (2) Assume `x, y ∈ mB` and take
  `t ∈ (I : m)`; show `t ∈ mB` (if `t` were a unit then `mB ≤ I`, but `I`'s image in
  `mB / mB ^ 2` is spanned by two elements while `mB / mB ^ 2` has the four independent
  basis vectors `a, b, c, d` — a `nf`/`basisB` dimension count); split `t = t₁ + t₂` with
  `t₂ ∈ mB ^ 2` via `nf`, and since `mB ^ 2 ≤ RHS` it suffices to handle the degree-1 part
  `t₁`. (3) Split `x = x₁ + x₂`, `y = y₁ + y₂` the same way and prove the support lemma
  describing `I ⊓ mB ^ 2` (BLUEPRINT B1 step 3), using `mB ^ 2 * mB = 0`. (4) The core
  finite linear algebra, transported through `nf` into `Idx → ZMod 2`: for `0 ≠ s` in the
  degree-1 space `V = ⟨a,b,c,d⟩` the map `V → W, w ↦ s * w` is INJECTIVE (`ad + bc` is an
  irreducible quadratic form over `F₂`, so it is not a product of two linear forms), and
  for `s, s'` independent in `V`, `dim (s·V ⊓ s'·V) = 2`. (5) Conclude
  `t₁ ∈ Ideal.span {x, y} ⊔ mB ^ 2` by the dimension count of BLUEPRINT B1 step 4,
  handling the degenerate sub-cases `y₁ = 0`, `y₁ = x₁`, `x₁ = y₁ = 0` separately (in the
  last, `I ⊆ mB ^ 2` has `F₂`-dimension ≤ 2 while `t₁ · V` has dimension 4).
  NAMING (binding, to avoid a namespace clash with Agent 3 who is computing in the same
  degree-2 space in parallel): prefix EVERY support lemma you introduce for step (4) and
  the dimension counts with `colon_` — e.g. `colon_mul_inj_of_ne_zero`,
  `colon_dim_inter_eq_two`, `colon_deg_split`. `mem_mB_iff` and `isUnit_of_not_mem_mB` are
  yours alone and keep those exact names.
  CHEAT-WATCH (BLUEPRINT Stage B box — binding): (a) `B_colon_two_gen` is a `∀ x y : Balg`
  statement over the WHOLE ring — proving it only for `x, y ∈ {xa, xb, xc, xd, xa+xb}`, or
  only for `x, y ∈ mB`, or only "for the `I` we actually use", is the single most tempting
  cheat in this project and would silently make Stage C false-but-derivable; the unit case
  and the degenerate `x₁, y₁` cases are PART OF THE THEOREM. (b) do not prove `⊇` and stop
  — the content is `⊆`; watch for accidentally proving `colonI I mB = ⊤`. (d) do not weaken
  `Ideal.span {x, y}` to `Ideal.span {x}`. (e) keep these two guardrail `example`s in the
  file: `example : colonI (⊥ : Ideal Balg) mB = mB ^ 2` (the `I = 0` instance — if this
  fails your reduction is wrong) and
  `example : xa * xb ∈ Ideal.span {xa} ⊓ Ideal.span {xb}` (the pairwise intersection is not
  zero — if you "prove" it is, you have collapsed `B`).
  If B1 defeats you, land `mem_mB_iff`, `isUnit_of_not_mem_mB` and whichever `colon_*`
  step lemmas DO compile, keep the file building, and log a `⚠️` entry quoting the exact
  goal you could not close — those step lemmas are the strictly-simpler cruxes the next
  iteration will resume from.
  MAY USE: everything in the `✅` list of the binding rules above (in particular all of
  `nf`, `sec_nf`, `basisB`, `mul_mem_mB_three`, `B_relation'`). Do NOT use Agent 3's
  `B_triple_inter_eq_bot` — it is being proved in parallel and B1 does not need it.

Agent 3: OWNS the single NEW file `Prob4b/Proofs/StageB_Colon/TripleInter.lean` (create
  it; it must import `Prob4b.Proofs.StageA_Algebra.Basic` and
  `Prob4b.Proofs.StageA_Algebra.NormalForm` and NOTHING else). Do NOT edit
  `Prob4b/Proofs/StageB_Colon/Basic.lean` — Agent 2 owns it and is editing it right now —
  and do NOT add an import of your file anywhere; put "wire
  `import Prob4b.Proofs.StageB_Colon.TripleInter` into `Prob4b.lean` and
  `Prob4b/Solution.lean`" on your PROGRESS `Next:` line instead, since until then your
  module is reachable only via the explicit target
  `lake build Prob4b.Proofs.StageB_Colon.TripleInter`, which you MUST run and get clean.
  TASK: BLUEPRINT Part 2 Stage B step **B2** (explicitly independent of B1, which is why it
  runs in parallel), following SKETCH.md Step 3 (line 123: `aB ∩ bB ∩ (a+b)B = 0`).
  Produce `B_triple_inter_eq_bot_proof :
  Ideal.span {xa} ⊓ Ideal.span {xb} ⊓ Ideal.span {xa + xb} = (⊥ : Ideal Balg)`
  (frozen theorem 6).
  PATH: `B` is graded, so for `s` in the degree-1 space `V = ⟨a,b,c,d⟩` we have
  `s · B = F₂·s ⊕ s·V` (degree ≥ 3 dies by `B_maximalIdeal_pow_three_proof` /
  `mul_mem_mB_three`). Take `z` in the triple intersection and compute its `nf` coordinates:
  the degree-1 components give `⟨a⟩ ⊓ ⟨b⟩ = 0` in `V`, so the degree-1 component of `z`
  vanishes; for the degree-2 components, `a·V ⊓ b·V = ⟨ab, ad⟩` while
  `(a+b)·V = ⟨a² + ab, ab + b², ac + ad, ad + bd⟩`, and expanding `λ·ab + μ·ad` in the
  latter basis forces the coefficients of `a²`, `b²`, `ac`, `bd` to vanish, hence
  `λ = μ = 0`. All of this is coordinate arithmetic in `Idx → ZMod 2` through `nf`; recall
  `bc` is NOT a basis index (`nf_xb_mul_xc = nf_xa_mul_xd = Pi.single adIdx 1`), and use
  `sec_nf` to get `z = 0` from `nf z = 0` (this is exactly why Cheat-watch (d) demanded the
  two-sided inverse).
  NAMING (binding, to avoid a namespace clash with Agent 2 who is computing in the same
  degree-2 space in parallel): prefix EVERY support lemma you introduce with `tri_` — e.g.
  `tri_mem_span_singleton_nf`, `tri_deg2_inter`, `tri_coeff_eq_zero`. Do NOT define
  `mem_mB_iff` or `isUnit_of_not_mem_mB` (Agent 2 owns those names) and do not define any
  `colon_*` lemma.
  CHEAT-WATCH (BLUEPRINT Stage B box (c) — binding): the result must be `= ⊥`, NOT
  `≤ mB ^ 2` and not "contains no unit" — a one-sided inclusion breaks Stage F, where every
  element of `J` must have finite support. `Balg` is noncomputable: no `decide` on it;
  transport every finite check through `nf`, and keep each `decide` under a few hundred
  cases (factor rather than enumerating `V³`). `native_decide` is banned.
  MAY USE: everything in the `✅` list of the binding rules above. Do NOT use Agent 2's
  `B_colon_two_gen` / `mem_mB_iff` / `isUnit_of_not_mem_mB` — they are being proved in
  parallel and B2 does not need them.

Agent 4: OWNS `Prob4b/Proofs/StageC_Module/Basic.lean` AND
  `Prob4b/Proofs/StageE_Amplify/Basic.lean` (both already imported by `Prob4b.lean` and
  `Prob4b/Solution.lean`). Do not touch any other file.
  TASK 4a (in `Prob4b/Proofs/StageC_Module/Basic.lean`; replace its `import Prob4b.Defs`
  by `import Prob4b.Proofs.StageA_Algebra.Basic` and
  `import Prob4b.Proofs.StageA_Algebra.NormalForm`) — BLUEPRINT Part 2 Stage C steps **C0
  (the parts that do not need Stage B), C3 and C4**, following SKETCH.md Step 3
  (lines 131-148). C1 `M_ann_eq`, C2 `M_pair_inter` and C5 `M_triple_defect` are OUT OF
  SCOPE: the first two consume `B_colon_two_gen` and the third consumes
  `B_triple_inter_eq_bot`, both of which are being proved in parallel right now — do not
  attempt them and do not restate them. Produce, with these exact names:
    - `mem_Nsub : ∀ w : Fin 4 → Balg, w ∈ Nsub ↔ ∃ t : Balg, w = t • vvec`
      (`Submodule.mem_span_singleton`);
    - `smulTop_span_singleton_mem : ∀ (x : Balg) (m : Mmod),
      m ∈ (smulTop (Ideal.span {x}) : Submodule Balg Mmod) ↔ ∃ n : Mmod, x • n = m`
      (the D0 shape BLUEPRINT Part −1 §2 requires Stage C to record; `≥` is
      `Submodule.smul_mem_smul` + `Submodule.mem_top`, `≤` is `Submodule.smul_induction_on`
      plus `Ideal.mem_span_singleton`);
    - `M_u_mem_triple_proof : uElt ∈ (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) ⊓
      smulTop (Ideal.span {xb}) ⊓ smulTop (Ideal.span {xa + xb})` (frozen theorem 10),
      using EXACTLY the three witnesses frozen in the SETUP `📝` D3 decision — do not go
      looking for others: `uElt = xb • ⟦![0, xa + xb, 0, xc + xd]⟧` (exact in `B⁴`),
      `uElt = (xa + xb) • ⟦![0, xb, 0, xd]⟧` (exact in `B⁴`, uses `B_relation'`,
      `xa * xd = xb * xc`), and `uElt = xa • ⟦![xb, xb, xd, xd]⟧` (valid only in the
      QUOTIENT: at the `B⁴` level `![0, xa*xb + xb*xb, 0, xb*xc + xb*xd] =
      xa • ![xb, xb, xd, xd] + xb • vvec`, so check all four coordinates and correct by
      `xb • vvec ∈ Nsub`, using `xa * xd + xb * xc = 0` in coordinate 3 and
      `xa * xd = xb * xc` in coordinate 4);
    - `M_u_ne_zero_proof : uElt ≠ 0` (frozen theorem 9). This means
      `![0, xa*xb + xb*xb, 0, xb*xc + xb*xd] ∉ Nsub`, i.e. there is NO `t : Balg` with
      `t • vvec = ![0, xa*xb + xb*xb, 0, xb*xc + xb*xd]`. Route (BLUEPRINT C4): coordinate
      2 forces the degree-1 part of `t` to be exactly `xa + xb` — writing
      `t₁ = λ₁a + λ₂b + λ₃c + λ₄d`, the product `t₁ * xb = λ₁ab + λ₂b² + λ₃ad + λ₄bd`
      (`bc = ad`) must equal `ab + b²`, and `ab, b², ad, bd` are four DISTINCT basis
      vectors, so `λ = (1,1,0,0)`; the constant term of `t` must vanish because otherwise
      coordinate 2 would have a degree-1 part. But then coordinate 1 gives
      `t * xa = (xa + xb) * xa = a² + ab ≠ 0`, contradicting the required `0`. Every step
      is an `nf` coordinate computation.
  CHEAT-WATCH (BLUEPRINT Stage C box — binding): (c) `M_u_ne_zero` must be a genuine
  non-membership COMPUTED through `nf`, never `by decide` (`Mmod` is not computable), never
  `by simp` on faith, and never obtained by assuming `Nsub ≠ ⊤`; a proof that does not
  mention `nf`/`basisB` is by definition suspect. (d) do not "simplify" `uElt` to an easier
  element — it is frozen. (e) do not conflate `Nsub : Submodule Balg (Fin 4 → Balg)` with
  an ideal of `Balg`, nor `smulTop (Ideal.span {x}) : Submodule Balg Mmod` with
  `Ideal.span {x} : Ideal Balg` — mixing the module side and the ring side is the most
  likely SILENT bug in this stage. (f) keep the guardrail `example`
  `example : (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) ≠ ⊥` in the file — if `aM`
  is zero you have collapsed `M`.
  TASK 4b (in `Prob4b/Proofs/StageE_Amplify/Basic.lean`) — REVIEW.md required follow-up 5,
  the two deferred Stage E guardrails of BLUEPRINT Stage E cheat-watch (f). Add
  `import Prob4b.Proofs.StageA_Algebra.NormalForm` and produce
  `example : (diag xa : Ramp) ≠ 0` (now unblocked: it needs `Nontrivial Balg`, i.e.
  `B_nontrivial_proof`, plus `nf_xa ≠ 0` and injectivity of `iota`). Then, ONLY IF your
  own `M_u_ne_zero_proof` compiled clean in task 4a, add
  `import Prob4b.Proofs.StageC_Module.Basic` and `example : uAt 0 ≠ (0 : Ramp)` (via
  injectivity of `TrivSqZeroExt.inr` at coordinate `0`, `Subtype.ext_iff`/`funext`). If
  `M_u_ne_zero_proof` did not land, skip the second `example`, leave the file compiling,
  and say so on your `Next:` line. Do NOT add, restate or use any lemma or instance
  asserting that `Ramp` is Noetherian — it is NOT (Stage F refutes exactly that), and
  every finiteness in that file must keep tracing back to a finite exceptional set
  (BLUEPRINT Stage E cheat-watch (b)). Change nothing else in the existing E0 layer.
  MAY USE: everything in the `✅` list of the binding rules above (in particular
  `B_relation'`, `mul_mem_mB_three`, `nf` and its evaluation lemmas, `sec_nf`,
  `B_nontrivial_proof`, and the E0 layer already in your Stage E file).

## Iteration 3
Goal: (i) clear REVIEW.md iteration-2 required follow-ups 1–2 (wiring the three
already-proved-but-unwired frozen theorems) and follow-up 3 (the now-unblocked Stage C5 /
Stage D6 / Stage F chain, which does NOT depend on `B_colon_two_gen`), landing frozen
theorems 11, 15, 17, 18 and taking verify.py Check 4 from 6 PASS to 11 PASS; and (ii) attack
the ONE remaining wall, `B_colon_two_gen` (frozen theorem 5), by discharging its two named
finite-linear-algebra leaves in two NEW, independent files. Advances BLUEPRINT Stages C
(C5), D (D6), F (F1–F5) and B (B1's two open sub-cases).

BINDING RULES FOR EVERY AGENT THIS ITERATION (read BLUEPRINT.md Part −1 §4/§5 first):
  * NEVER edit `Prob4b/Defs.lean` or `Prob4b/Theorems.lean` (byte-frozen, SHA-pinned).
    Never restate a frozen theorem with an added hypothesis, a specialization, or an
    inclusion in place of an equality.
  * `sorry`, `native_decide`, `axiom`, `admit`, `opaque`, `unsafe`, `implemented_by`,
    `debug.skipKernelTC` are BANNED anywhere. `scripts/ALLOWED_AXIOMS.txt` is empty:
    `#print axioms` on every declaration you produce must report exactly
    `[propext, Classical.choice, Quot.sound]` (or less).
  * If you cannot finish a lemma, DELETE the incomplete attempt so your module compiles
    clean, and append a `⚠️ blocked` entry to PROGRESS.md quoting the exact failing goal.
    Never leave a `sorry`.
  * `decide` is allowed ONLY on small statements in the computable types `ZMod 2` / `Fin n`
    / `Bool` / `Nat` — never on `Balg`, `Mmod`, `Cring`, `Ramp` (all noncomputable).
  * Prove a frozen statement under the name `<name>_proof` in your own file; never cite the
    still-`sorry` frozen name `Prob4b.<name>` inside a proof.
  * Touch ONLY the files listed on your own `Agent k:` line. `Prob4b.lean`,
    `Prob4b/Discharge.lean` and `Prob4b/Solution.lean` belong to Agent 1 ALONE this
    iteration. If `lake build` reports errors in a file you do not own, that is another
    agent's in-flight edit — wait and rebuild, do not fix it.
  * House style (or `lake build` warns and verify.py Check 3 fails): 4-line copyright
    header, module docstring after the imports, a docstring on every declaration, lines
    ≤ 100 characters.
  * Append a `🔧 in progress` claim entry to PROGRESS.md before you start and a
    `✅ proved` / `⚠️ blocked` entry (with `Check:` = `lake build` + `#print axioms`
    results, and a mandatory `Next:`) when you stop. Never edit an existing entry.
  * ALREADY `✅` AND FREELY USABLE (do not re-prove): Stage A — `nf`, `sec`, `sec_nf_apply`,
    `basisB`, `nf_one`, `nf_xa`…`nf_xd` and the ten `nf_x?_mul_x?`, `B_relation_proof`,
    `B_relation' : xa * xd = xb * xc`, `B_two_eq_zero`, `B_neg_eq`, `mB_eq_map`,
    `B_maximalIdeal_pow_three_proof`, `mul_mem_mB_three`, `B_isNoetherianRing_proof`,
    `B_nontrivial_proof`, `mem_ann`; Stage B — `mem_mB_iff`, `isUnit_of_not_mem_mB`,
    `colon_lin`, `colon_co`, `colon_deg_split`, `colon_span_pair_desc`, `colon_mulc`,
    `colon_nf_lin_mul_quad`, `colon_mul_inj_of_ne_zero`, `colon_lin_injective`,
    `colon_lin_eq_zero_iff`, `colon_sq_mul`, `colon_le_colonI`, `colon_bot_eq`,
    `colon_sq_case`, `colon_lin_mul_mem`, `colon_mB_not_two_gen`,
    `B_triple_inter_eq_bot_proof`, `tri_mem_span_singleton`; Stage C — `mem_Nsub`,
    `smulTop_span_singleton_mem`, `M_u_mem_triple_proof`, `M_u_ne_zero_proof`,
    `mu_mul_gen`, `mu_coeff_mul_xa`, `mu_coeff_mul_xb`; Stage D — `mem_map_iota_iff`,
    `iota_mem_map_iff`, `map_iota_span_singleton`, `mem_span_iota_iff`, `iota_mul_eq`,
    `iota_apply_fst`/`_snd`, `smul_mem_smulTop`, `finite_Balg`/`_Mmod`/`_Cring`,
    `C_isNoetherianRing_proof`; Stage E — `mem_Rsub_iff`, `tail_unique`, `tailValue`,
    `tailValue_spec`, `tailValue_eq_of`, `tailValue_eq_of_apply`, `exc`, `exc_finite`,
    `apply_eq_of_not_mem_exc`, `tailValue_diag/_zero/_one/_add/_mul`, `coordAt` +
    `coordAt_apply_self`/`_apply_ne`/`_mul`/`_add`, `offSet` + `offSet_apply_mem`/
    `_apply_not_mem`/`tailValue_offSet`, `mem_ideal_span_finset`, `iota_injective`,
    `Ramp_ext`, `diag_apply`, `coe_add_apply`/`coe_mul_apply`/`coe_zero_apply`; Stage F —
    `iInf_fin_two`, `quasiCoherent_imp_finiteConductor_proof`.
  * STILL OPEN AND OFF-LIMITS THIS ITERATION (nobody may state or assume them):
    `B_colon_two_gen` (frozen 5), `M_ann_eq` (7), `M_pair_inter` (8), `C_ann_eq` (13),
    `C_pair_inter` (14), `R_finiteConductor` (16), `exists_finiteConductor_not_quasiCoherent`
    (20). Do NOT assume any of them; they are blocked on frozen theorem 5.
  * `Prob4b/Proofs/StageB_Colon/Basic.lean` is READ-ONLY for everyone this iteration (its
    `B_colon_two_gen` assembly is deferred to the next iteration, once Agents 3 and 4 land
    its two missing leaves).

Agent 1: OWNS `Prob4b.lean`, `Prob4b/Discharge.lean`, `Prob4b/Solution.lean`,
  `Prob4b/Proofs/StageC_Module/Basic.lean`, `Prob4b/Proofs/StageD_Idealization/Basic.lean`.
  These are the only shared/wiring files in the project — no other agent may touch them, and
  you must APPEND to the two Stage C/D proof files only (never modify or re-order an
  existing declaration there: Agent 2 imports both while you work).
  TASK 1a (DO THIS FIRST — REVIEW.md iteration-2 required follow-ups 1 and 2; the auditor
  has already run all three `rfl` gates and confirmed they typecheck, so this is mechanical):
  (i) add `import Prob4b.Proofs.StageB_Colon.TripleInter` to BOTH `Prob4b.lean` (next to the
  existing `import Prob4b.Proofs.StageB_Colon.Basic`) and `Prob4b/Solution.lean` — that
  module is currently ORPHANED, so plain `lake build` never compiles it; (ii) add to
  `Prob4b/Discharge.lean` the three gates
  `example : @Prob4b.B_triple_inter_eq_bot = @Prob4b.B_triple_inter_eq_bot_proof := rfl`,
  `example : @Prob4b.M_u_ne_zero = @Prob4b.M_u_ne_zero_proof := rfl`,
  `example : @Prob4b.M_u_mem_triple = @Prob4b.M_u_mem_triple_proof := rfl` (each with a
  docstring, matching the existing gate style); (iii) in `Prob4b/Solution.lean` repoint the
  three forwarding stubs `B_triple_inter_eq_bot`, `M_u_ne_zero`, `M_u_mem_triple` at
  `_root_.Prob4b.<name>_proof`, leaving EVERYTHING to the left of `:=` byte-identical;
  (iv) run `python3 scripts/verify.py` and confirm Check 4 goes 6 PASS / 14 FAIL →
  9 PASS / 11 FAIL. Report the Check 4 tally verbatim in PROGRESS.md.
  TASK 1b (BLUEPRINT Stage C step **C5**, frozen theorem 11, in
  `Prob4b/Proofs/StageC_Module/Basic.lean`): add `import Prob4b.Proofs.StageB_Colon.TripleInter`
  to that file and prove
  `M_triple_defect_proof : (smulTop (Ideal.span {xa}) : Submodule Balg Mmod) ⊓
  smulTop (Ideal.span {xb}) ⊓ smulTop (Ideal.span {xa + xb}) ≠
  smulTop (Ideal.span {xa} ⊓ Ideal.span {xb} ⊓ Ideal.span {xa + xb})` — the statement must be
  copied verbatim from `Prob4b/Theorems.lean:71-74`. Route (BLUEPRINT C5, "two lines"):
  rewrite the RHS with `B_triple_inter_eq_bot_proof` to `smulTop (⊥ : Ideal Balg)`, which is
  `⊥` (`smulTop I` is defeq `I • ⊤`, so `Submodule.bot_smul`); the LHS contains `uElt` by
  `M_u_mem_triple_proof` and `uElt ≠ 0` by `M_u_ne_zero_proof`, so the two submodules differ.
  Prefix any new support lemma `mu_` (the file's existing convention).
  TASK 1c (BLUEPRINT Stage D step **D6**, frozen theorem 15, in
  `Prob4b/Proofs/StageD_Idealization/Basic.lean`): add
  `import Prob4b.Proofs.StageC_Module.Basic` and `import Prob4b.Proofs.StageB_Colon.TripleInter`
  and prove `C_triple_defect_proof : Ideal.span {iota xa} ⊓ Ideal.span {iota xb} ⊓
  Ideal.span {iota (xa + xb)} ≠ (Ideal.span {xa} ⊓ Ideal.span {xb} ⊓
  Ideal.span {xa + xb}).map iota`, verbatim from `Prob4b/Theorems.lean:90-92`. Route
  (BLUEPRINT D6): the RHS is `(⊥ : Ideal Balg).map iota = ⊥` by `B_triple_inter_eq_bot_proof`
  + `Ideal.map_bot`; for the LHS use your own `mem_span_iota_iff` on `TrivSqZeroExt.inr uElt`
  (its `fst` is `0 ∈ Ideal.span {s}`, its `snd` is `uElt ∈ smulTop (Ideal.span {s})` by
  `M_u_mem_triple_proof`) for each of `s = xa, xb, xa + xb`, and `TrivSqZeroExt.inr uElt ≠ 0`
  from `M_u_ne_zero_proof` (`TrivSqZeroExt.inr` is injective — `congrArg TrivSqZeroExt.snd`).
  Also add the deferred BLUEPRINT Stage D cheat-watch (e) guardrail
  `example : (TrivSqZeroExt.inr uElt : Cring) ≠ 0` (REVIEW.md follow-up 5, now unblocked).
  TASK 1d (wire your own two results, LAST): add the two gates
  `example : @Prob4b.M_triple_defect = @Prob4b.M_triple_defect_proof := rfl` and
  `example : @Prob4b.C_triple_defect = @Prob4b.C_triple_defect_proof := rfl` to
  `Prob4b/Discharge.lean`, repoint the matching two stubs in `Prob4b/Solution.lean`, re-run
  `python3 scripts/verify.py` and report the Check 4 tally (expected 11 PASS / 9 FAIL, or 13
  PASS if Agent 2's Stage F results have landed and you also wire `R_triple_inter_not_fg` /
  `R_not_quasiCoherent` — do that too if and only if their `_proof` terms exist on disk and
  `lake build` is clean). FINALLY, if `Prob4b/Proofs/StageB_Colon/LinAlg.lean` and/or
  `Prob4b/Proofs/StageB_Colon/LinAlgRank2.lean` exist and build clean, add their imports to
  `Prob4b.lean` ONLY (they contain no frozen `_proof`, so `Solution.lean` needs nothing) so
  they do not start next iteration orphaned; if they do not exist yet, say so on `Next:`.
  CHEAT-WATCH (BLUEPRINT Stage C box (b)/(e)/(f) and Stage D box (b)/(d)/(e), binding):
  `M_triple_defect` and `C_triple_defect` are `≠` statements whose whole content is that the
  LHS is strictly bigger — do not prove them by weakening either side. Keep the module side
  (`smulTop … : Submodule Balg Mmod`, `TrivSqZeroExt.inr`) and the ring side
  (`Ideal.span … : Ideal Balg`, `iota`, `TrivSqZeroExt.inl`) distinct, and never conflate
  `iota x` with `x` or `TrivSqZeroExt.inr uElt` with `uElt`. The RHS of D6 must stay the
  honest extension `Ideal.map iota`, not an `Ideal.comap` surrogate. Do not "simplify"
  `uElt` — it is frozen.

Agent 2: OWNS `Prob4b/Proofs/StageF_Headline/Basic.lean` (and NO other file). Deliver
  BLUEPRINT Stage F steps **F1–F5**, i.e. frozen theorems 17 (`R_triple_inter_not_fg`) and
  18 (`R_not_quasiCoherent`). Both are INDEPENDENT of the blocked `B_colon_two_gen`. Change
  the file's imports to `Prob4b.Proofs.StageB_Colon.TripleInter`,
  `Prob4b.Proofs.StageC_Module.Basic`, `Prob4b.Proofs.StageD_Idealization.Basic` and
  `Prob4b.Proofs.StageE_Amplify.Basic`, keep the existing `iInf_fin_two` and
  `quasiCoherent_imp_finiteConductor_proof` byte-identical (they are already `✅` and wired),
  and prefix every new support lemma `hf_`. Deliver, in this order:
    * `iInf_fin_three {S : Type*} [CommRing S] (x y z : S) :
      (⨅ i, Ideal.span {![x, y, z] i} : Ideal S) = Ideal.span {x} ⊓ Ideal.span {y} ⊓
      Ideal.span {z}` — the `Fin 3` analogue of the existing `iInf_fin_two`, same proof
      shape (`le_antisymm` + `iInf_le _ 0/1/2` and `fin_cases i`); note the RHS bracketing
      must match frozen theorem 17's `(A ⊓ B) ⊓ C`. (REVIEW.md iteration-2 follow-up 4.)
    * **F1** `uAt_mem_triple (n : ℕ) : uAt n ∈ Ideal.span {diag xa} ⊓ Ideal.span {diag xb} ⊓
      Ideal.span {diag (xa + xb)}`. For each `s ∈ {xa, xb, xa + xb}`: `TrivSqZeroExt.inr uElt
      ∈ Ideal.span {iota s}` by `mem_span_iota_iff` (its `fst` is `0`, its `snd` is `uElt`,
      which lies in `smulTop (Ideal.span {s})` by `M_u_mem_triple_proof`); then
      `Ideal.mem_span_singleton'` gives `c : Cring` with `c * iota s = TrivSqZeroExt.inr uElt`,
      and `diag s * coordAt n c = uAt n` by `Ramp_ext` + `coordAt_apply_self`/`_apply_ne`
      (at `n` it is `iota s * c`, elsewhere `0`).
    * **F2** `uAt_ne_zero (n : ℕ) : uAt n ≠ 0` — evaluate at coordinate `n`, then
      `TrivSqZeroExt.inr uElt ≠ 0` from `M_u_ne_zero_proof` (`congrArg TrivSqZeroExt.snd`).
      (Stage E already has this for `n = 0` as a guardrail; generalise it here, do not edit
      the Stage E file.)
    * **F3** `support_of_mem_triple (h : Ramp) (hh : h ∈ Ideal.span {diag xa} ⊓
      Ideal.span {diag xb} ⊓ Ideal.span {diag (xa + xb)}) : tailValue h = 0`. For each of the
      three, `h = diag s * r`; off the FINITE set `exc h ∪ exc r` (its complement in `ℕ` is
      nonempty because a finite set cannot cover `ℕ` — the argument already used inside
      `tail_unique`) we get `iota (tailValue h) = iota s * iota (tailValue r) =
      iota (s * tailValue r)`, so `tailValue h = s * tailValue r ∈ Ideal.span {s}` by
      `iota_injective`. Hence `tailValue h ∈ Ideal.span {xa} ⊓ Ideal.span {xb} ⊓
      Ideal.span {xa + xb} = ⊥` by `B_triple_inter_eq_bot_proof`.
    * **F4** `R_triple_inter_not_fg_proof`, the verbatim statement of
      `Prob4b/Theorems.lean:102-104`. Suppose the ideal is `Ideal.span ↑s` for a
      `s : Finset Ramp`. Put `T := ⋃ h ∈ s, exc h`, finite by `exc_finite` +
      `Set.Finite.biUnion` (each generator lies in the triple intersection, so F3 gives it
      tail value `0` and `exc h` IS its support). By `mem_ideal_span_finset` every element of
      the span is a finite combination `∑ r_h * h`, and `(r_h * h) k = r_h k * h k = 0` for
      `k ∉ exc h`; so every element of the ideal vanishes outside `T`. Pick `n ∉ T` (`ℕ` is
      infinite), and F1 puts `uAt n` in the ideal while `(uAt n) n = TrivSqZeroExt.inr uElt
      ≠ 0` by F2. Contradiction.
    * **F5** `R_not_quasiCoherent_proof : ¬ QuasiCoherent Ramp`, verbatim from
      `Prob4b/Theorems.lean:107`: `rintro ⟨h₁, h₂⟩`, instantiate `h₂ 3
      ![diag xa, diag xb, diag (xa + xb)]`, rewrite with `iInf_fin_three`, and close with F4.
  Do NOT prove or wire anything into `Prob4b.lean`/`Discharge.lean`/`Solution.lean` (Agent 1
  owns those); state on your `Next:` line which `_proof` names are ready to be wired.
  CHEAT-WATCH (BLUEPRINT Stage F box, binding): (a) `R_not_quasiCoherent` must negate the
  FROZEN `QuasiCoherent`, quantified over every `n : ℕ` and every family — do not restate it
  as "the specific triple is not f.g."; frozen theorem 17 exists separately precisely so both
  appear. (b) "every finitely generated ideal is supported on finitely many coordinates" must
  be PROVED from `mem_ideal_span_finset`/`Submodule.mem_span_finset`, never asserted, and you
  may not assume the generators are the `uAt n`. (c) F3 must use the equality
  `B_triple_inter_eq_bot_proof` (`= ⊥`); an inclusion `≤ mB ^ 2` leaves a nonzero tail and
  the argument collapses. Also BLUEPRINT Stage E cheat-watch (b): do NOT state, use or
  introduce any lemma or instance asserting `Ramp` is Noetherian or finite — it is neither,
  and this file is exactly what refutes it; every finiteness must come from a finite
  exceptional set.

Agent 3: OWNS the NEW file `Prob4b/Proofs/StageB_Colon/LinAlg.lean` (and NO other file;
  `Prob4b/Proofs/StageB_Colon/Basic.lean` is read-only, import it, never edit it). Imports:
  `Prob4b.Proofs.StageB_Colon.Basic` (which transitively brings Stage A) and nothing else.
  Prefix every declaration `lin1_`. GOAL — the RANK-1 leaf of `B_colon_two_gen`, named in
  PROGRESS.md 2026-08-09T18:02:38Z `Next:` step (1) as `colon_dim_inter_le` and in BLUEPRINT
  Stage B step B1.4 as `dim_inter_eq_two`. It is a PURE finite statement about the explicit
  `ZMod 2` multiplication table `colon_mulc : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) →
  (Fin 9 → ZMod 2)` already proved in `StageB_Colon/Basic.lean:272` — no `Balg`, no ideals.
  Primary target:
  `lin1_inter_card_le (s s' : Fin 4 → ZMod 2) (hs : s ≠ 0) (hs' : s' ≠ 0) (hne : s ≠ s') :
   (Finset.univ.filter (fun z => ∃ w, colon_mulc s z = colon_mulc s' w)).card ≤ 4`
  (equivalently, and equally acceptable: any three elements `z₁ z₂ z₃` of that set satisfy
  `z₁ = 0 ∨ z₂ = 0 ∨ z₃ = 0 ∨ z₁ = z₂ ∨ z₁ = z₃ ∨ z₂ = z₃ ∨ z₁ + z₂ + z₃ = 0`, i.e. the set
  is an `F₂`-subspace of dimension ≤ 2). Over `F₂`, "`s, s'` independent" is exactly
  `s ≠ 0 ∧ s' ≠ 0 ∧ s ≠ s'`. MATHEMATICAL CONTENT: with `V = ⟨a,b,c,d⟩` and `W` the 9-dim
  degree-2 part of `B` (basis `a², ab, ac, ad(=bc), b², bd, c², cd, d²`), the set is
  `{z | s·z ∈ s'·V}`, and `dim (s·V ∩ s'·V) = 2` exactly (e.g. `a·V ∩ b·V = ⟨ab, ad⟩`,
  with `ad = bc` supplying the second vector); the answer is `span {s'}` enlarged by at most
  one vector `z₀` solving `s·z₀ + s'·w₀ = ad + bc` in `Sym² V`, so the bound is `≤ 4`
  elements. HARD CONSTRAINT (measured, PROGRESS.md:197): a naive `decide` over
  `(Fin 4 → ZMod 2)³` with an inner span-membership search did NOT terminate in 13 minutes
  of kernel evaluation — do not re-run it. Suggested routes, in order: (1) cheapen the
  arithmetic before enumerating — `ZMod 2` is `Fin 2` and every kernel operation on it goes
  through `Nat.mod`, whereas `Bool` (`xor`/`&&`) and `Nat` bit operations evaluate far faster
  in the kernel; define a `Bool`- or `Nat`-bitmask mirror of `colon_mulc`, prove the bridge
  to `colon_mulc` by a cheap 256-case `decide` (`∀ s z : Fin 4 → ZMod 2`, one `Fin 9`
  coordinate at a time), and run the enumeration in the cheap encoding; (2) a structural
  `Module.finrank` argument over `ZMod 2` inside `Fin 9 → ZMod 2`, using the already-`✅`
  `colon_mul_inj_of_ne_zero` (so `z ↦ colon_mulc s z` is injective, hence
  `dim (s·V) = 4`) together with `Submodule.finrank_sup_add_finrank_inf_eq`; (3) reduce to a
  per-pair statement: there are only `16 × 16` pairs `(s, s')`, so a lemma proved uniformly
  in `s'` and case-split on `s` is much cheaper than a triply-quantified check. Any
  equivalent-strength final statement is acceptable, but you MUST record its exact verbatim
  form in your PROGRESS.md `✅` entry, since the next iteration's assembler consumes it.
  STRETCH GOAL, only after the primary target compiles clean: in the SAME file, use it to
  discharge the rank-1 sub-case of `B_colon_two_gen` as
  `lin1_rank_one_case (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB) (hcy : colon_co y = 0)
   (ht : t ∈ colonI (Ideal.span {x, y}) mB) : t ∈ Ideal.span {x, y} ⊔ mB ^ 2`, following
  PROGRESS.md 2026-08-09T18:02:38Z: `colon_mem_mB_of_mem_colonI` puts `t ∈ mB`,
  `colon_deg_split` writes `t = colon_lin (colon_co t) + w` with `w ∈ mB ^ 2`,
  `colon_lin_mul_mem` + `colon_span_pair_desc` turn `t · mB ⊆ (x, y)` into the coordinate
  hypothesis, and the ψ-linearity argument forces `{z | colon_mulc (colon_co t) z ∈
  Img (colon_co x)}` to have ≥ 8 elements unless `colon_co t ∈ {0, colon_co x}`. Do NOT
  attempt the rank-2 case (Agent 4 owns it) and do NOT state or assume
  `B_colon_two_gen` itself.
  CHEAT-WATCH (BLUEPRINT Stage B box, binding): `B_colon_two_gen` is a `∀ x y : Balg`
  statement over the WHOLE ring — proving it only for `x, y ∈ {xa, xb, xc, xd}`, only for
  `x, y ∈ mB`, or only "for the `I` we actually use" is the single most tempting cheat in
  this project. Your rank-1 lemma is allowed to carry the rank hypothesis `colon_co y = 0`
  ONLY because it is an explicitly-scoped sub-case lemma, never a frozen statement; do not
  name it `B_colon_two_gen_proof` and do not wire it anywhere. `native_decide` is banned; if
  a `decide` times out, restructure, do not switch tactic.

Agent 4: OWNS the NEW file `Prob4b/Proofs/StageB_Colon/LinAlgRank2.lean` (and NO other file;
  `Prob4b/Proofs/StageB_Colon/Basic.lean` is read-only, import it, never edit it). Imports:
  `Prob4b.Proofs.StageB_Colon.Basic` and nothing else. Prefix every declaration `lin2_`.
  GOAL — the RANK-2 leaf of `B_colon_two_gen`, named in PROGRESS.md 2026-08-09T18:02:38Z
  `Next:` step (2) (`colon_triple_sum` / "`Img st ⊄ Img cx + Img cy`") and in BLUEPRINT
  Stage B step B1.4. Like Agent 3's, it is a PURE finite statement about the explicit table
  `colon_mulc` from `StageB_Colon/Basic.lean:272` — no `Balg`, no ideals. Primary target:
  `lin2_not_mem_sum (cx cy t : Fin 4 → ZMod 2) (h1 : cx ≠ 0) (h2 : cy ≠ 0) (h3 : cx ≠ cy)
   (h4 : t ≠ 0) (h5 : t ≠ cx) (h6 : t ≠ cy) (h7 : t ≠ cx + cy) :
   ∃ z : Fin 4 → ZMod 2, ∀ u v : Fin 4 → ZMod 2,
     colon_mulc t z ≠ colon_mulc cx u + colon_mulc cy v`
  (over `F₂`, `h1`–`h3` say `cx, cy` are independent and `h4`–`h7` say
  `t ∉ span {cx, cy}`). MATHEMATICAL CONTENT: in `Sym² V` the ideal `(l₁, l₂)` is prime, so
  `l₃ · V ⊆ l₁V + l₂V` forces `l₃ ∈ ⟨l₁, l₂⟩`; passing to `W = Sym² V / ⟨ad + bc⟩` costs one
  dimension, handled by the linear map `m ↦ (coefficient of ad + bc in l₃ m)` whose kernel
  has dimension ≥ 3 > 2 = dim ⟨l₁, l₂⟩. HARD CONSTRAINT (measured, PROGRESS.md:197): the
  dual-certificate `decide` — `∀ cx cy t` (4096 triples) `∃ c : Fin 9 → ZMod 2` (512
  certificates) with `M c ⬝ cx = 0`, `M c ⬝ cy = 0`, `M c ⬝ t ≠ 0` — is TRUE and would settle
  this, but it did NOT terminate in 13 minutes of kernel evaluation and was killed. Do not
  re-run it unchanged. Suggested routes, in order: (1) keep that dual-certificate shape but
  make the kernel arithmetic cheap — `ZMod 2` is `Fin 2` and each operation costs a `Nat.mod`,
  while `Bool` (`xor`/`&&`) and `Nat` bitmask/`Nat.xor`/`Nat.land` operations evaluate orders
  of magnitude faster in the kernel; mirror `colon_mulc` and the symmetric matrix `M c`
  (entries `M₀₀ = c₀`, `M₀₁ = c₁`, `M₀₂ = c₂`, `M₀₃ = M₁₂ = c₃`, `M₁₁ = c₄`, `M₁₃ = c₅`,
  `M₂₂ = c₆`, `M₂₃ = c₇`, `M₃₃ = c₈`) in the cheap encoding, bridge back with a 256-case
  `decide`, and enumerate there; (2) make the certificate EXPLICIT instead of existential:
  the symmetric bilinear forms whose radical contains `cx` and `cy` and which satisfy the
  one linear constraint `β(e₀,e₃) = β(e₁,e₂)` form a space of dimension ≥ 2, while those
  additionally killing `t` form a space of dimension ≤ 1 — turning `∃ c` (512 cases) into a
  small rank computation and cutting the search by two orders of magnitude; (3) a
  `Module.finrank` argument over `ZMod 2` in `Fin 9 → ZMod 2`: `colon_mul_inj_of_ne_zero`
  (already `✅`) gives `dim (s·V) = 4` for `s ≠ 0`, `colon_mulc cx cy ≠ 0` lies in
  `cx·V ∩ cy·V` so `dim (cx·V + cy·V) ≤ 7` by `Submodule.finrank_sup_add_finrank_inf_eq`,
  and the remaining content is the ≥ 8 lower bound on `dim (t·V + cx·V + cy·V)`. Any
  equivalent-strength final statement is acceptable, but you MUST record its exact verbatim
  form in your PROGRESS.md `✅` entry, since the next iteration's assembler consumes it. If
  you cannot close it, DELETE the attempt, leave the file compiling (or absent), and log a
  `⚠️ blocked` entry naming the exact failing goal and the measured cost of whatever
  enumeration you tried — that measurement is itself the deliverable for the next iteration.
  Do NOT attempt the rank-1 case (Agent 3 owns it) and do NOT state or assume
  `B_colon_two_gen` itself.
  CHEAT-WATCH (BLUEPRINT Stage B box, binding): the eventual `B_colon_two_gen` is a
  `∀ x y : Balg` statement over the WHOLE ring; your lemma may carry the independence and
  non-membership hypotheses ONLY because it is an explicitly-scoped sub-case lemma, never a
  frozen statement — do not name it `B_colon_two_gen_proof` and do not wire it anywhere.
  `native_decide` is banned; if a `decide` times out, restructure, do not switch tactic.

## Iteration 4
Close the one remaining wall — frozen theorem 5 `B_colon_two_gen` (BLUEPRINT Stage B, B1), whose every
leaf is now `✅` on disk — and, in parallel, build the entire downstream chain C1/C2 → D3/D4 → E1/E2/E3
(BLUEPRINT Stages C, D, E) in *hypothesis-parametrized* form so that the moment frozen 5 lands the
remaining six `sorryAx` names (7, 8, 13, 14, 16, 20) are one-line instantiations rather than four more
serial iterations. Also clears REVIEW.md iteration-3 required follow-up 1 (the missing `C_triple_defect`
no-drift gate).

GLOBAL RULES for all four agents this iteration (re-read BLUEPRINT Part −1 §4/§5 before starting):
never edit `Prob4b/Defs.lean` or `Prob4b/Theorems.lean`; never weaken, specialize, or add a hypothesis to
a frozen statement; no `sorry`, `native_decide`, `axiom`, `admit`, `opaque`, `unsafe`, `implemented_by`,
`debug.skipKernelTC` anywhere; every `decide` must be on the computable `ZMod 2`/`Fin n`/`Nat` side and
NEVER on `Balg`/`Mmod`/`Cring`/`Ramp`; the only admissible axioms are `propext`, `Classical.choice`,
`Quot.sound` (`USER_NOTES.md`: "None — no assumed axioms"). Every file needs the 4-line copyright header,
a module docstring after the imports, a docstring on every declaration, and lines ≤ 100 characters, or
`lake build` warns and verify.py Check 3 fails. APPEND-ONLY to the files you own: do not rewrite or delete
existing declarations. Only Agent 1 may touch `Prob4b.lean`, `Prob4b/Discharge.lean`, `Prob4b/Solution.lean`;
nobody else may touch a file another agent owns, even to read-and-fix. If `lake build` reports an error in a
file you do NOT own, that is another agent's in-flight edit — wait 60 s and retry, never edit it. Append a
`🔧` claim entry and a `✅`/`⚠️` result entry to `PROGRESS.md` (append-only, get timestamps with
`date -u +"%Y-%m-%dT%H:%M:%SZ"`), and on `⚠️` record the FAILING GOAL VERBATIM. Verify your work with
`lake build <your module>` and `#print axioms` run in a scratch importer under `/tmp` (never added to the repo).

Agent 1: OWNS the NEW file `Prob4b/Proofs/StageB_Colon/ColonAssembly.lean` plus the three shared wiring files
`Prob4b.lean`, `Prob4b/Discharge.lean`, `Prob4b/Solution.lean`. `Prob4b/Proofs/StageB_Colon/Basic.lean`,
`LinAlg.lean` and `LinAlgRank2.lean` are READ-ONLY for you — do NOT add the assembly to `Basic.lean`
(REVIEW.md iteration-3 follow-up 2 says to, but that would be an IMPORT CYCLE: `LinAlg.lean` and
`LinAlgRank2.lean` both `import Prob4b.Proofs.StageB_Colon.Basic`). The new file must have exactly the two
imports `Prob4b.Proofs.StageB_Colon.LinAlg` and `Prob4b.Proofs.StageB_Colon.LinAlgRank2` (which transitively
give you `StageB_Colon.Basic` and Stage A). PRODUCE: `B_colon_two_gen_proof :
∀ x y : Balg, colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2` — the statement byte-identical to
frozen theorem 5 (`Prob4b/Theorems.lean:44-45`), i.e. SKETCH.md:99-105 "(I : m) = I + m² for every ideal I
generated by at most two elements". PATH (this is an ASSEMBLY; every ingredient is already `✅` — do NOT
introduce a new leaf lemma and do NOT re-attempt any finite enumeration): (i) `⊇` is `colon_le_colonI I`
(`StageB_Colon/Basic.lean:494`). (ii) `⊆`, unit case: if `x ∉ mB` or `y ∉ mB` then `isUnit_of_not_mem_mB`
(`Basic.lean:146`) makes a generator a unit, so `Ideal.span {x, y} = ⊤` (`Ideal.eq_top_of_isUnit_mem`) and
both sides are `⊤`. (iii) `⊆`, `x, y ∈ mB`, DEPENDENT branch (`colon_co x = 0 ∨ colon_co y = 0 ∨
colon_co x = colon_co y` — over `F₂` this disjunction IS linear dependence): closed outright by
`lin1_rank_le_one_case (x y t : Balg) (hx : x ∈ mB) (hy : y ∈ mB) (hdep : …) (ht : t ∈ colonI (Ideal.span {x, y}) mB) :
t ∈ Ideal.span {x, y} ⊔ mB ^ 2` (`StageB_Colon/LinAlg.lean`). (iv) `⊆`, `x, y ∈ mB`, INDEPENDENT (rank-2)
branch — the only new work, and it mirrors the already-written proof of `lin1_rank_le_one_case` step for
step: put `cx := colon_co x`, `cy := colon_co y`, `st := colon_co t`; `colon_mem_mB_of_mem_colonI`
(`Basic.lean:574`) gives `t ∈ mB`; `colon_deg_split` (`Basic.lean:229`) writes `t = colon_lin st + w` with
`w ∈ mB ^ 2`; `colon_lin_mul_mem` (`Basic.lean:586`) + `colon_span_pair_desc` (`Basic.lean:367`) give, for
every `z`, `α β u v` with `colon_lin st * colon_lin z = α • x + β • y + colon_lin u * x + colon_lin v * y`;
apply `colon_co` to kill everything but `α • cx + β • cy = 0`, then `lin2_smul_eq_zero`
(`StageB_Colon/LinAlgRank2.lean`) gives `α = β = 0`; apply the degree-two coordinate map `lin1_q e :=
fun j => nf e (Sum.inr (Sum.inr j))` with its ALREADY-PROVED support lemmas `lin1_q_add`, `lin1_q_smul`,
`lin1_q_lin_mul`, `lin1_mulc_add_left`, `lin1_mulc_add_right`, `lin1_mulc_comm` (all in `LinAlg.lean`; reuse,
do not re-prove) to reach `∀ z, colon_mulc st z = colon_mulc u cx + colon_mulc v cy`; contradict it by
instantiating at the witness `z` of `lin2_not_mem_sum' (cx cy t : Fin 4 → ZMod 2) (h1 : cx ≠ 0) (h2 : cy ≠ 0)
(h3 : cx ≠ cy) (h4 : t ≠ 0) (h5 : t ≠ cx) (h6 : t ≠ cy) (h7 : t ≠ cx + cy) : ∃ z, ∀ u v, colon_mulc t z ≠
colon_mulc u cx + colon_mulc v cy` (`LinAlgRank2.lean`; use `lin2_mulc_comm` if an orientation mismatches).
That yields `st ∈ {0, cx, cy, cx + cy}`; in each of the four cases `t` lands in `Ideal.span {x, y} ⊔ mB ^ 2`
(e.g. `st = cx` gives `t - x ∈ mB ^ 2` via `colon_deg_split` applied to `x`). ALREADY-`✅` RESULTS YOU MAY
USE: everything in `StageB_Colon/Basic.lean` (`colon_le_colonI`, `isUnit_of_not_mem_mB`, `mem_mB_iff`,
`colon_mem_mB_sq_iff`, `colon_mem_mB_of_mem_colonI`, `colon_deg_split`, `colon_lin`, `colon_co`,
`colon_mulc`, `colon_lin_mul_mem`, `colon_span_pair_desc`, `colon_sq_case`, `colon_bot_eq`), all `lin1_*`
(`LinAlg.lean`), all `lin2_*` (`LinAlgRank2.lean`), and Stage A's `B_relation'`, `mul_mem_mB_three`,
`B_two_eq_zero`, `nf`/`sec`/`basisB`, `mem_ann`. BLUEPRINT CHEAT-WATCH (Stage B) YOU MUST RESPECT
(BLUEPRINT.md:690-705): (a) keep the genuine `∀ x y : Balg` over the WHOLE ring — the unit case and the
degenerate cases are PART of the theorem, no added hypothesis, no restriction to `x, y ∈ mB`; (b) the
content is `⊆`, do not prove `⊇` and stop, and watch for accidentally proving `colonI I mB = ⊤`; (d) do not
weaken `span {x, y}` to `span {x}`. Keep the two mandated guardrail `example`s reachable (they already live
in `Basic.lean`). THEN WIRE, in this order, and only if `lake build Prob4b.Proofs.StageB_Colon.ColonAssembly`
is clean: (1) add `import Prob4b.Proofs.StageB_Colon.ColonAssembly` to BOTH `Prob4b.lean` (next to the other
StageB imports) and `Prob4b/Solution.lean`; (2) add to `Prob4b/Discharge.lean` the gate
`example : @Prob4b.B_colon_two_gen = @Prob4b.B_colon_two_gen_proof := rfl` AND the MISSING gate
`example : @Prob4b.C_triple_defect = @Prob4b.C_triple_defect_proof := rfl` (REVIEW.md iteration-3 required
follow-up 1 — `C_triple_defect_proof` is at `Prob4b/Proofs/StageD_Idealization/Basic.lean:205` and the
reviewer confirmed the gate typechecks; that is a one-line addition to `Discharge.lean` ONLY, do not touch
the Stage D file); (3) in `Prob4b/Solution.lean:52-54` repoint the `B_colon_two_gen` stub from
`_root_.Prob4b.B_colon_two_gen` to `_root_.Prob4b.B_colon_two_gen_proof`, leaving every byte to the LEFT of
`:=` unchanged. Finally run `python3 scripts/verify.py` and report the Check 4 count (expected 13 PASS /
7 FAIL → 14 PASS / 6 FAIL) in your `✅` PROGRESS entry. If the rank-2 branch defeats you, delete the
incomplete attempt so the module builds clean, log `⚠️` with the verbatim failing goal, and STILL do wiring
step (2)'s `C_triple_defect` gate.

Agent 2: OWNS `Prob4b/Proofs/StageC_Module/Basic.lean` (APPEND ONLY — the existing `mem_Nsub`,
`smulTop_span_singleton_mem`, `mu_*`, `M_u_mem_triple_proof`, `M_u_ne_zero_proof`, `M_triple_defect_proof`
must stay byte-identical). Do NOT add any import (the current three suffice). BLUEPRINT Stage C steps
C0/C1/C2 (BLUEPRINT.md:714-735), SKETCH.md Step 2. Frozen theorem 5 is being proved IN PARALLEL by Agent 1
and is NOT yet `✅`, so you must take it as an explicit HYPOTHESIS with this exact spelling, reused verbatim
in both targets: `(hB1 : ∀ x y : Balg, colonI (Ideal.span {x, y}) mB = Ideal.span {x, y} ⊔ mB ^ 2)`.
PRODUCE, with statements otherwise BYTE-IDENTICAL to frozen theorems 7 and 8 (`Prob4b/Theorems.lean:54` and
`:57-60`): (1) `mu_ann_eq_of_colon (hB1 : …) : ∀ x : Balg, annM Mmod x = smulTop (ann x)`; (2)
`mu_pair_inter_of_colon (hB1 : …) : ∀ x y : Balg, (smulTop (Ideal.span {x}) : Submodule Balg Mmod) ⊓
smulTop (Ideal.span {y}) = smulTop (Ideal.span {x} ⊓ Ideal.span {y})`. Also produce the C0 support lemma
`mu_ann_vvec (hB1 : …) (t : Balg) : (∀ i, t * vvec i = 0) ↔ t ∈ mB ^ 2` — the `←` direction is Stage A's
`mul_mem_mB_three` / `B_maximalIdeal_pow_three_proof` alone, and the `→` direction is the `x = y = 0`
instance of `hB1` (`Ideal.span {(0 : Balg), 0} = ⊥`, so `colonI ⊥ mB = mB ^ 2`), after turning
`∀ i, t * vvec i = 0` into `∀ z ∈ mB, t * z = 0` by `Submodule.span_induction` on
`mB = Ideal.span {xa, xb, xc, xd}`. PATH for C1 (BLUEPRINT.md:720-725): `⊇` is formal; for `⊆` take
`m̄ = ⟦p⟧` with `x • m̄ = 0`, so `x • p = t • vvec` for some `t` (`mem_Nsub`); each coordinate gives
`t * vvec i = x * p i ∈ Ideal.span {x, x}`, so `hB1 x x` puts `t ∈ Ideal.span {x, x} ⊔ mB ^ 2`; write
`t = x * s + z` with `z ∈ mB ^ 2`, so `z • vvec = 0` by `mu_ann_vvec`, hence `x • (p - s • vvec) = 0`
coordinatewise, i.e. `p - s • vvec ∈ (ann x) • (⊤ : Submodule Balg (Fin 4 → Balg))`, and its class is `m̄`.
PATH for C2 (BLUEPRINT.md:727-735, the `Tor₁ = 0` argument of SKETCH.md Step 2 without `Tor`): `⊇` is
`Submodule.smul_mono`; for `⊆` let `m̄ = x • ⟦p⟧ = y • ⟦q⟧`, so `x • p - y • q = t • vvec`; coordinatewise
`t * vvec i ∈ Ideal.span {x, y}`, so `hB1 x y` gives `t = x * α + y * β + z` with `z ∈ mB ^ 2` and
`z • vvec = 0`; put `p' := p - α • vvec`, `q' := q + β • vvec`, so `⟦p'⟧ = ⟦p⟧`, `⟦q'⟧ = ⟦q⟧` and
`x • p' = y • q'` EXACTLY in `B⁴`; then each `x * p' i = y * q' i ∈ Ideal.span {x} ⊓ Ideal.span {y}`, so the
class of `x • p'`, which is `m̄`, lies in `smulTop (Ideal.span {x} ⊓ Ideal.span {y})`. ALREADY-`✅` RESULTS
YOU MAY USE: `mem_Nsub`, `smulTop_span_singleton_mem` (this file); Stage A's `mem_ann`,
`mul_mem_mB_three`, `B_maximalIdeal_pow_three_proof`, `B_relation'`, `nf`; Stage D's
`smul_mem_smulTop` is NOT available to you (wrong direction of the import graph) — reprove the one-liner
`Submodule.smul_mem_smul h Submodule.mem_top` inline if you need it. BLUEPRINT CHEAT-WATCH (Stage C)
YOU MUST RESPECT (BLUEPRINT.md:759-773): (a) both targets are `∀ x` / `∀ x y` over the WHOLE of `Balg`, never
only `x, y ∈ {xa, xb, xa + xb}`; (b) both are EQUALITIES and the formal inclusion is worth nothing — check
which direction your proof actually does; (e) never conflate `Nsub : Submodule Balg (Fin 4 → Balg)` with an
ideal of `Balg`, nor `smulTop (Ideal.span {x}) : Submodule Balg Mmod` with `Ideal.span {x} : Ideal Balg`
(the most likely SILENT bug in this stage). NAMING/WIRING DISCIPLINE: do NOT name anything
`M_ann_eq_proof`/`M_pair_inter_proof` while it still carries `hB1`, do NOT state or assume
`B_colon_two_gen` under its frozen name, and do NOT touch `Prob4b/Discharge.lean` or `Prob4b/Solution.lean`.
ONLY IF, at the moment you finish, `lake build Prob4b.Proofs.StageB_Colon.ColonAssembly` is clean AND that
file contains `B_colon_two_gen_proof`, you may additionally add `import Prob4b.Proofs.StageB_Colon.ColonAssembly`
to your file and derive the unconditional `M_ann_eq_proof := mu_ann_eq_of_colon B_colon_two_gen_proof` and
`M_pair_inter_proof := mu_pair_inter_of_colon B_colon_two_gen_proof`; report in PROGRESS whether you did, so
Agent 1 or the next iteration can wire them.

Agent 3: OWNS `Prob4b/Proofs/StageD_Idealization/Basic.lean` (APPEND ONLY — every existing declaration,
including `C_isNoetherianRing_proof` and `C_triple_defect_proof`, must stay byte-identical; do NOT add or
remove imports). BLUEPRINT Stage D steps D3/D4 (BLUEPRINT.md:793-800), SKETCH.md:180-192. Frozen theorems 7
and 8 are being proved IN PARALLEL by Agent 2 and are NOT yet `✅`, so take them as explicit HYPOTHESES with
these exact spellings: `(hM7 : ∀ x : Balg, annM Mmod x = smulTop (ann x))` and
`(hM8 : ∀ x y : Balg, (smulTop (Ideal.span {x}) : Submodule Balg Mmod) ⊓ smulTop (Ideal.span {y}) =
smulTop (Ideal.span {x} ⊓ Ideal.span {y}))`. PRODUCE, with statements otherwise BYTE-IDENTICAL to frozen
theorems 13 and 14 (`Prob4b/Theorems.lean:82` and `:85-87`): (1) `di_ann_eq_of_M (hM7 : …) :
∀ x : Balg, ann (iota x) = (ann x).map iota`; (2) `di_pair_inter_of_M (hM8 : …) : ∀ x y : Balg,
Ideal.span {iota x} ⊓ Ideal.span {iota y} = (Ideal.span {x} ⊓ Ideal.span {y}).map iota`. PATH for D3: by
`iota_mul_fst`/`iota_mul_snd` (already `✅` in your file, `iota x * c = (x * c.fst, x • c.snd)`), a `c : Cring`
annihilates `iota x` iff `c.fst ∈ ann x` (use `mem_ann`) and `c.snd ∈ annM Mmod x`; rewrite the latter by
`hM7` to `c.snd ∈ smulTop (ann x)`; that pair of conditions is exactly `mem_map_iota_iff (ann x) c`
(`:92`), which is membership in `(ann x).map iota`. Use `TrivSqZeroExt.ext` / `TrivSqZeroExt.ext_iff` to
split `iota x * c = 0` into its two components. PATH for D4: `mem_span_iota_iff` (`:142`) says
`c ∈ Ideal.span {iota x} ↔ c.fst ∈ Ideal.span {x} ∧ c.snd ∈ smulTop (Ideal.span {x})`, so the LHS is
`{c | c.fst ∈ xB ⊓ yB ∧ c.snd ∈ xM ⊓ yM}`; rewrite the second conjunct by `hM8` to
`c.snd ∈ smulTop (Ideal.span {x} ⊓ Ideal.span {y})`; then `mem_map_iota_iff (Ideal.span {x} ⊓ Ideal.span {y})`
is exactly the RHS. Prove both by `Ideal.ext` + `Submodule.mem_inf`. ALREADY-`✅` RESULTS YOU MAY USE, all in
your own file: `iota_apply`, `iota_apply_fst`, `iota_apply_snd`, `iota_mul_fst`, `iota_mul_snd`,
`iota_mul_eq`, `smul_mem_smulTop`, `mem_map_iota_iff`, `map_iota_eq`, `iota_mem_map_iff`,
`map_iota_span_singleton`, `span_iota_eq`, `mem_span_iota_iff`, `mem_span_iota_inr`; plus Stage A's `mem_ann`.
BLUEPRINT CHEAT-WATCH (Stage D) YOU MUST RESPECT (BLUEPRINT.md:819-831): (a) both targets are `∀ x` / `∀ x y`
over ALL of `Balg` — Stage E instantiates them at arbitrary tail values, so no restriction to `xa, xb`;
(b) the right-hand sides must stay the honest extension `Ideal.map iota`, never an `Ideal.comap`-flavoured
surrogate; (d) never conflate `iota x` with `x`, nor `TrivSqZeroExt.inr uElt` with `uElt`. NAMING/WIRING
DISCIPLINE: do NOT name anything `C_ann_eq_proof`/`C_pair_inter_proof` while it still carries `hM7`/`hM8`,
and do NOT touch `Prob4b/Discharge.lean` or `Prob4b/Solution.lean`. ONLY IF, at the moment you finish,
`lake build Prob4b.Proofs.StageC_Module.Basic` is clean AND that file contains unconditional
`M_ann_eq_proof`/`M_pair_inter_proof`, you may derive `C_ann_eq_proof := di_ann_eq_of_M M_ann_eq_proof` and
`C_pair_inter_proof := di_pair_inter_of_M M_pair_inter_proof`; report in PROGRESS whether you did.

Agent 4: OWNS `Prob4b/Proofs/StageE_Amplify/Basic.lean` (APPEND ONLY — the whole existing E0 layer must stay
byte-identical). You MUST add the single import `Prob4b.Proofs.StageD_Idealization.Basic` to that file (it
currently imports only Stage A `NormalForm` and Stage C `Basic`); Agent 3 is appending to the Stage D file in
parallel, so if `lake build` fails inside `StageD_Idealization/Basic.lean`, wait 60 s and retry — never edit
it. BLUEPRINT Stage E steps E1/E2/E3 (BLUEPRINT.md:857-893), SKETCH.md:223-249 "Why R is finite-conductor";
this is BLUEPRINT's self-declared HARDEST BOOKKEEPING in the project. Frozen theorems 13 and 14 are being
proved IN PARALLEL by Agent 3 and are NOT yet `✅`, so take them as explicit HYPOTHESES with these exact
spellings: `(hC13 : ∀ x : Balg, ann (iota x) = (ann x).map iota)` and `(hC14 : ∀ x y : Balg,
Ideal.span {iota x} ⊓ Ideal.span {iota y} = (Ideal.span {x} ⊓ Ideal.span {y}).map iota)`. PRODUCE, in this
priority order: (1) `re_ann_fg_of_C (hC13 : …) : ∀ f : Ramp, (ann f).FG`; (2) `re_pair_inter_fg_of_C
(hC14 : …) : ∀ f g : Ramp, (Ideal.span {f} ⊓ Ideal.span {g} : Ideal Ramp).FG`; (3)
`re_finiteConductor_of_C (hC13 : …) (hC14 : …) : FiniteConductor Ramp := ⟨re_ann_fg_of_C hC13,
re_pair_inter_fg_of_C hC14⟩` — statement otherwise byte-identical to frozen theorem 16
(`Prob4b/Theorems.lean:97`), with `Ramp`'s canonical `Subring.toCommRing` instance and no bespoke instance.
PATH for E1 (BLUEPRINT.md:857-871): set `x := tailValue f`, `S := exc f` (finite by `exc_finite`); take a
finite generating set `w₁…w_k` of `ann x : Ideal Balg` (exists by the `✅` `B_isNoetherianRing_proof`) and,
for each `n ∈ S`, a finite generating set of `ann (f n) : Ideal Cring` (exists by the `✅`
`C_isNoetherianRing_proof`); claim `ann f = Ideal.span ({offSet S _ w_j} ∪ {coordAt n c_{n,i}})`. `⊇`: each
listed element kills `f` coordinatewise (off `S`, `iota x * iota w_j = iota (x * w_j) = 0`; on `S`,
`f n * c_{n,i} = 0`). `⊆`: given `g` with `f * g = 0`, put `z := tailValue g`; off `S ∪ exc g` we get
`iota x * iota z = 0`, hence `x * z = 0` by `iota_injective`, i.e. `z ∈ ann x`; write `z = Σ β_j w_j`; then
`g' := g - Σ diag(β_j) * offSet S _ w_j` has FINITE support inside `S ∪ exc g`, and at each `n` in that
support `g' n ∈ ann (f n)` — off `S` this is where `hC13` is used (it puts `g' n ∈ (ann x).map iota`, then
rewrite through the `offSet` generators); finally `g' = Σ_{n ∈ supp} coordAt n (g' n)`, a finite sum inside
the span. PATH for E2 (BLUEPRINT.md:873-891): same shape with `S := exc f ∪ exc g`, `w_j` generating
`Ideal.span {x} ⊓ Ideal.span {y}` in `Balg` and `c_{n,i}` generating `Ideal.span {f n} ⊓ Ideal.span {g n}` in
`Cring`; for `⊇` note `w_j = x * x'` gives `f * offSet S _ x' = offSet S _ w_j`; for `⊆`, given `h = f * s =
g * t`, off `S ∪ exc h` use `hC14` plus `iota_mem_map_iff` (Stage D, `✅`) to get
`tailValue h ∈ Ideal.span {x} ⊓ Ideal.span {y}`, subtract the `offSet` part, and finish on the finite
remaining support. ALREADY-`✅` RESULTS YOU MAY USE: the whole E0 layer in your own file (`mem_Rsub_iff`,
`iota_injective`, `Ramp_ext`, `tail_unique`, `tailValue`, `tailValue_spec`, `tailValue_eq_of`,
`tailValue_eq_of_apply`, `exc`, `mem_exc_iff`, `exc_finite`, `apply_eq_of_not_mem_exc`, `coordAt`,
`coordAt_mul`, `coordAt_add`, `offSet`, `offSet_coe`, `mem_ideal_span_finset`), Stage D's `iota_mem_map_iff`
/ `mem_map_iota_iff` / `C_isNoetherianRing_proof`, and Stage A's `B_isNoetherianRing_proof` / `mem_ann`.
BLUEPRINT CHEAT-WATCH (Stage E) YOU MUST RESPECT (BLUEPRINT.md:895-908): (a) `FiniteConductor Ramp` is `∀ f`
and `∀ f g` over the WHOLE ring — never only for `f, g` in the image of `diag`, never only for finitely
supported `f`, never only for `tailValue f ≠ 0`; the MIXED case is the whole point of SKETCH Step 5; (b) do
NOT introduce, assume, or use any statement or instance saying `Ramp` is Noetherian or finite — that is
exactly what frozen theorem 17 refutes, and a `grep` for it is part of the audit; every finiteness must come
from `B`/`C` Noetherian plus the finite exceptional set; (c) do not replace `Ideal.FG` by "generated by the
`w_j`" without proving the reverse inclusion — `⊆` is the content; (d) the tail argument needs `hC14` at
ARBITRARY `x, y`, so if you find yourself wanting `x, y ∈ {xa, xb}` you have mis-structured the proof;
(e) do not assume `exc s`/`exc t`/`exc h` are contained in `S` — handle them separately, finiteness is all
you need. NAMING/WIRING DISCIPLINE: do NOT name anything `R_finiteConductor_proof` while it still carries
`hC13`/`hC14`, and do NOT touch `Prob4b/Discharge.lean` or `Prob4b/Solution.lean`. This is a large task: if
only E1 lands, log `✅` for E1 and `⚠️` for E2 with the VERBATIM failing goal — that is an acceptable
outcome; do not `sorry` anything, delete an incomplete attempt so the module builds clean.

## Iteration 5
Close the run: land the six remaining `sorryAx` frozen statements (7, 8, 13, 14, 16, 20) and
wire all twenty. This finishes BLUEPRINT Stage D steps D3/D4, Stage F step F7, and the
"Discharge & Solution" section. REVIEW.md iteration-4 "Required follow-ups" 1–3 are the whole
task; follow-up 3 is binding — **no new mathematics is to be invented this iteration**, every
term below is already verified by the auditor to typecheck and to bind to the frozen type.

Agent 1: OWNS exactly four files — `Prob4b/Proofs/StageD_Idealization/Basic.lean`,
`Prob4b/Proofs/StageF_Headline/Basic.lean`, `Prob4b/Discharge.lean`, `Prob4b/Solution.lean`
(no other agent runs this iteration, so there is no collision risk, but do not touch any other
file, and NEVER touch `Prob4b/Defs.lean` or `Prob4b/Theorems.lean`).

  (A) APPEND to the end of `Prob4b/Proofs/StageD_Idealization/Basic.lean` (inside its existing
  `namespace Prob4b`, keeping every existing line byte-identical; NO new import is needed — the
  file already imports `Prob4b.Proofs.StageC_Module.Basic`, which is where `M_ann_eq_proof`
  (`StageC_Module/Basic.lean:462`) and `M_pair_inter_proof` (`:467`) live):
    * `theorem C_ann_eq_proof : ∀ x : Balg, ann (iota x) = (ann x).map iota :=`
      `di_ann_eq_of_M M_ann_eq_proof`
      (`di_ann_eq_of_M` is at `StageD_Idealization/Basic.lean:243`; its hypothesis is frozen
      theorem 7 verbatim and its conclusion is frozen theorem 13 verbatim).
    * `theorem C_pair_inter_proof : ∀ x y : Balg, Ideal.span {iota x} ⊓ Ideal.span {iota y} =`
      `(Ideal.span {x} ⊓ Ideal.span {y}).map iota := di_pair_inter_of_M M_pair_inter_proof`
      (`di_pair_inter_of_M` is at `:264`).
    Copy the statements verbatim from `Prob4b/Theorems.lean:82` and `:85-87` so the no-drift
    gates in (C) pass. Each declaration needs a `/-- ... -/` docstring and lines ≤ 100 chars
    (the mathlib linter set is ON; a warning fails verify.py Check 3).
    SKETCH step: SKETCH.md:176-192 (`(0:_C x) = (0:_B x)C` and `xC ∩ yC = (xB ∩ yB)C`).
    BLUEPRINT: Stage D steps D3/D4 (BLUEPRINT.md:793-800). Cheat-watch (Stage D) that this
    must respect: (a) keep the genuine `∀ x` / `∀ x y` over all of `Balg`; (b) the RHS stays
    the honest extension `Ideal.map iota` — no `Ideal.comap` surrogate; (d) never conflate
    `iota x` with `x`.

  (B) APPEND to the end of `Prob4b/Proofs/StageF_Headline/Basic.lean` (inside its existing
  `namespace Prob4b`; NO new import is needed — the file already imports
  `Prob4b.Proofs.StageE_Amplify.Basic`, which holds `R_finiteConductor_proof` at
  `StageE_Amplify/Basic.lean:755`, and `R_not_quasiCoherent_proof` is in this same file at
  `:214`):
    * `theorem exists_finiteConductor_not_quasiCoherent_proof :`
      `∃ (S : Type) (inst : CommRing S), @FiniteConductor S inst ∧ ¬ @QuasiCoherent S inst :=`
      `⟨Ramp, inferInstance, R_finiteConductor_proof, R_not_quasiCoherent_proof⟩`
      — statement copied verbatim from `Prob4b/Theorems.lean:114-116`.
    SKETCH step: SKETCH.md:296-320 (Conclusion). BLUEPRINT: Stage F step F7
    (BLUEPRINT.md:952-954). Cheat-watch (Stage F) that this must respect: (d) `Ramp` must
    carry its CANONICAL `CommRing` instance from `Subring.toCommRing` — `inferInstance`
    supplies exactly that, so do NOT introduce a bespoke instance to make anything typecheck;
    (e) do not substitute a different, easier witness ring.

  (C) APPEND six no-drift gates to `Prob4b/Discharge.lean` (keep the existing 14 gates
  byte-identical, and UPDATE the module docstring at `:22-29` so it lists all 20 — the
  iteration-3 review flagged a docstring/content mismatch here before):
    `example : @Prob4b.M_ann_eq = @Prob4b.M_ann_eq_proof := rfl` (frozen 7),
    `example : @Prob4b.M_pair_inter = @Prob4b.M_pair_inter_proof := rfl` (8),
    `example : @Prob4b.C_ann_eq = @Prob4b.C_ann_eq_proof := rfl` (13),
    `example : @Prob4b.C_pair_inter = @Prob4b.C_pair_inter_proof := rfl` (14),
    `example : @Prob4b.R_finiteConductor = @Prob4b.R_finiteConductor_proof := rfl` (16),
    `example : @Prob4b.exists_finiteConductor_not_quasiCoherent =`
    `  @Prob4b.exists_finiteConductor_not_quasiCoherent_proof := rfl` (20).
    Place them so the file reads in frozen-statement order.

  (D) REPOINT exactly six stubs in `Prob4b/Solution.lean` — currently
  `Prob4b/Solution.lean:63` (`M_ann_eq`), `:70` (`M_pair_inter`), `:92` (`C_ann_eq`),
  `:98` (`C_pair_inter`), `:107` (`R_finiteConductor`), `:126`
  (`exists_finiteConductor_not_quasiCoherent`) — each of which still forwards to the `sorry`d
  frozen name (e.g. `:= _root_.Prob4b.M_ann_eq`). Change ONLY the term to the right of `:=`,
  to `_root_.Prob4b.<name>_proof`. Every byte to the LEFT of `:=` must stay identical to
  `Prob4b/Theorems.lean`; do not touch the other 14 stubs, the imports, or the docstring
  header beyond noting the state. No new import is needed (`Solution.lean` already imports
  the Stage D, E and F modules).

  Already-✅ results this agent may use, all sorry-free and axiom-clean on disk
  (`[propext, Classical.choice, Quot.sound]`), independently re-verified by the iteration-4
  auditor: `M_ann_eq_proof`, `M_pair_inter_proof`, `di_ann_eq_of_M`, `di_pair_inter_of_M`,
  `R_finiteConductor_proof`, `R_not_quasiCoherent_proof`. Do NOT re-prove or restate any of
  them, do not add hypotheses to anything, do not introduce any `axiom` (USER_NOTES.md:47 —
  "None — no assumed axioms"), and do not use `sorry`, `native_decide`, `admit`, `opaque`,
  `unsafe` or `debug.skipKernelTC` anywhere.

  VERIFICATION before writing PROGRESS.md: run `lake build` (must be
  "Build completed successfully", 0 errors, and exactly the 20 expected
  `Theorems.lean` sorry warnings and nothing else — no linter warnings from the edited
  files), then `python3 scripts/verify.py`. EXPECTED OUTCOME: Check 4 moves from
  14 PASS / 6 FAIL to 20 PASS / 0 FAIL and the run reports `RESULT: PASS`. Also run
  `#print axioms Prob4b.Solution.exists_finiteConductor_not_quasiCoherent` in a scratch
  importer under `/tmp` (never add a file to the repo) and confirm it reports exactly
  `[propext, Classical.choice, Quot.sound]` with no `sorryAx`. Append one `🔧` claim entry and
  one `✅` entry to `PROGRESS.md` (append-only; quote the verify.py RESULT line verbatim).
