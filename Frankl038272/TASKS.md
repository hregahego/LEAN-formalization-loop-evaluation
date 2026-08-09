# TASKS — Frankl union-closed families: some element has frequency >= 1196/3125 = 0.38272 (entropy method) formalization

Append-only work-delegation log for 4 parallel worker agents. The Plan agent
appends one "## Iteration N" block per loop iteration. Each block has a one-line
goal then "Agent k: ..." lines (one per ACTIVE worker; inactive agents are
omitted). NEVER edit or delete an existing block.

## Iteration 1
Open the analysis track from the frozen skeleton: discharge Stage A in full plus every
dependency-free leaf of Stages B, C and D (both exact Bernstein certificates), which are the
only stages whose prerequisites are already ✅ (SETUP). Advances BLUEPRINT Stages A, B, C, D.

GLOBAL RULES FOR ALL FOUR AGENTS THIS ITERATION (binding, read before coding).
(a) NEVER edit `EntropyBound/Defs.lean`, `EntropyBound/Theorems.lean` (SHA-pinned),
`EntropyBound.lean` (root import file), `EntropyBound/Solution.lean` or
`EntropyBound/Discharge.lean` — all five are shared or frozen; three other agents are
running in parallel right now, so touching a file you do not own loses work.
(b) You may create NEW files only inside the directories your line names, and each new file
must be reachable from the module graph by an `import` added to a `Basic.lean` YOU own
(`EntropyBound.lean` already imports every `Proofs/<Stage>/Basic.lean`).
(c) For each frozen theorem `t` you prove: write `theorem t_proof : <statement copied
VERBATIM from Theorems.lean> := by …` in `namespace EntropyBound` in one of your files;
then in the SAME file add `namespace EntropyBound.Solution` with the verbatim restatement
`theorem t : <same statement> := EntropyBound.t_proof`, and the no-drift gate
`example : @EntropyBound.t = @EntropyBound.Solution.t := rfl`. Do NOT add the restatement
for a theorem you did not finish (a `sorry` there is a hard verify.py failure).
(d) ALL support/helper lemmas go in your own sub-namespace (`namespace EntropyBound.Constants`
/ `.Toolbox` / `.RankOne` / `.ProfileSpeed` as your line says), NEVER bare in
`namespace EntropyBound` — parallel agents would otherwise clash on names like `bern_nonneg`.
(e) Banned everywhere: `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`,
`implemented_by`, `debug.skipKernelTC` (`scripts/ALLOWED_AXIOMS.txt` is EMPTY — USER_NOTES.md
permits no assumed certificates). `#print axioms EntropyBound.Solution.<t>` must print only
`propext, Classical.choice, Quot.sound`. Real-valued `def`s need `noncomputable section`.
(f) `lake build` must be clean (the only warnings allowed are the `declaration uses 'sorry'`
ones coming from `Theorems.lean`). Toolchain/Mathlib pins must not be bumped:
`leanprover/lean4:v4.31.0`, Mathlib rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
(g) Follow the BLUEPRINT worker-onboarding ritual: append a `🔧 in progress` entry to
`PROGRESS.md` claiming your files BEFORE coding, then `✅`/`⚠️` entries as you go, with
`Agent: agent-iter1-<k>`, a real `date -u +"%Y-%m-%dT%H:%M:%SZ"` timestamp, the
`#print axioms` output on the `Check:` line, and a mandatory `Next:` line with backticked
lemma names. PROGRESS.md is append-only. Nothing is ✅ yet except SETUP, so you may rely on
NO other stage's results — everything you need must come from `Defs.lean` + Mathlib + your
own file.

Agent 1: OWNS `EntropyBound/Proofs/Constants/Basic.lean` and may create
`EntropyBound/Proofs/Constants/LogEnclose.lean` (import it from `Constants/Basic.lean`).
Produce, verbatim from `Theorems.lean` and following BLUEPRINT Part 2 Stage A (A1–A5) and
SKETCH Step 1 (1a),(1b): `strict_margin_proof` (#1, `Cval * (1 - cval) - 1 = 929/156250000`
— unfold `Cval`,`cval`, `norm_num`); `log_ten_lower_proof` (#2, `(2:ℝ) < Real.log 10` — via
`Real.exp_one_lt_d9` ⇒ `exp 2 < 7.39 < 10` and `Real.lt_log_iff_exp_lt`);
`log_ten_upper_proof` (#3, `Real.log 10 < 12/5` — `10 < exp (12/5)` from the degree-5 Taylor
partial sum `∑_{k≤5}(12/5)^k/k! = 166093/15625 > 10`, then `Real.log_lt_iff`);
`log_two_upper_proof` (#4, `Real.log 2 < 25/36` — SKETCH 1b route: `log 2 = 2 artanh(1/3)`,
keep the `j = 0,1` terms, geometric tail `≤ 2/(5·3^5)·(1/(1-1/9)) = 1/540`, giving
`log 2 ≤ 1123/1620 < 1125/1620 = 25/36`; Mathlib handles: `Real.abs_log_sub_add_sum_range_le`
at `x = ±1/3`, `Real.log_div`, `tsum_geometric_of_lt_one`); `C_lt_ratio_123_65_proof` (#5,
`(10/9) * Cval < 123/65`, i.e. `81001·65 = 5265065 < 5535000 = 123·45000`, `norm_num`).
ALSO produce, in `Constants/LogEnclose.lean` under `namespace EntropyBound.Constants`, the
REUSABLE certified rational log-enclosure API that BLUEPRINT E3 and G4 both need and that the
Plan agent is assigning to exactly one worker (do not duplicate it elsewhere): definitions
`logLo (a : ℚ) (J : ℕ) : ℚ` and `logHi (a : ℚ) (J : ℕ) : ℚ` computed from the artanh series
`log a = 2 ∑_{j≥0} y^(2j+1)/(2j+1)` with `y = (a-1)/(a+1)`, truncated at `J` with an explicit
geometric tail bound, together with the two theorems
`logLo_le : ∀ (a : ℚ) (J : ℕ), 0 < a → ((logLo a J : ℚ) : ℝ) ≤ Real.log (a : ℝ)` and
`le_logHi : ∀ (a : ℚ) (J : ℕ), 0 < a → Real.log (a : ℝ) ≤ ((logHi a J : ℚ) : ℝ)`; reuse the
same tail machinery you built for #4. Respect the BLUEPRINT Cheat-watch (Stage A) box: the
bounds must be on `Real.log` itself, never on a `logApprox : ℚ → ℚ` surrogate standing in for
it; keep the STRICT `<` in #2 (Step 7b needs `-log s ≥ 6 log 10 > 12`); do NOT weaken `25/36`
to something `norm_num` finds easier — Step 6 needs exactly `25/324 > log 2 / 9`. Guardrail
that must compile in your file from #4 alone: `example : (25:ℝ)/324 > Real.log 2 / 9 := by …`.

Agent 2: OWNS `EntropyBound/Proofs/Toolbox/Basic.lean` and every NEW file in
`EntropyBound/Proofs/Toolbox/` EXCEPT `Toolbox/Poly.lean`, which belongs to Agent 4 — do not
create, import or edit `Toolbox/Poly.lean`, and do not prove #17/#18/#19/#20. Suggested
split: `Toolbox/Entropy.lean` and `Toolbox/Series.lean`, both imported from
`Toolbox/Basic.lean`. First build the two support lemmas of BLUEPRINT Stage B's preamble in
`namespace EntropyBound.Toolbox`: `Hnat_eq_binEntropy : Hnat = Real.binEntropy` (an equality
of FUNCTIONS, proved once — `Hnat z = -z * Real.log z - (1-z) * Real.log (1-z)`) and
`summable_inv_mul_succ : Summable (fun m : ℕ => 1 / (((m:ℝ)+1) * ((m:ℝ)+2)))` with
`tsum … = 1` (telescoping); every `tsum` below is dominated by the latter. Then produce,
verbatim from `Theorems.lean`, in priority order: `binEntropy_two_sided_proof` (#7, SKETCH
2b / BLUEPRINT B2 — from `z ≤ -log(1-z) ≤ z/(1-z)` via `Real.add_one_le_exp` /
`Real.log_le_sub_one_of_pos`, giving `-(1-z)log(1-z) ∈ [z(1-z), z]`);
`fser_closed_form_proof` (#8, SKETCH 2c / B3 — `∑ z^k/(k(k+1)) = ∑ z^k/k - ∑ z^k/(k+1)` from
`-log(1-z) = ∑ z^k/k` (`Real.hasSum_log_sub_log_of_abs_lt_one` or the `log(1-x)` series), and
the `fser 1 = 1` conjunct by the telescoping sum — no Abel limit needed);
`enat_series_form_proof` (#9, SKETCH 2d / B4 — unfold `enat z = Hnat z / z`, use #8, treat
`z = 1` separately where both sides are `0`); `enat_sum_of_squares_proof` (#10, SKETCH 2e /
B5 — from #9 the `log` terms cancel since `-2log(st) + log s² + log t² = 0`, leaving the
termwise identity `f(s²)+f(t²)-2f(st) = ∑ (s^k - t^k)²/(k(k+1))`, then `tsum_add`/`tsum_sub`
with summability from `summable_inv_mul_succ`); and LAST, only if the four above are done,
`binEntropy_parabola_lower_proof` (#6, SKETCH 2a / B1 — substitute `z = (1-u)/2`, prove
`log 2 - Hnat ((1-u)/2) = ∑_{k≥1} u^{2k}/(2k(2k-1))`, bound coefficientwise by
`∑ 1/(2k(2k-1)) = log 2`, conclude with `4z(1-z) = 1-u²`). Respect the BLUEPRINT Cheat-watch
(Stage B) box: never replace a `tsum` by a finite partial sum "for tractability"; never prove
a statement only on a subinterval and then quantify over the frozen domain anyway; do not use
`Real.binEntropy`'s API to restate `Hnat` facts with different constants — the bridge must be
the single function equality above; #6 must hold on ALL of `[0,1]`, not just where `nlinarith`
succeeds. Guardrails to include: `example : fser 1 = 1` and `example : Qser 0 = 1`.

Agent 3: OWNS `EntropyBound/Proofs/RankOne/Basic.lean` and every new file in
`EntropyBound/Proofs/RankOne/` (import new files from `RankOne/Basic.lean`). Produce,
verbatim from `Theorems.lean`, following BLUEPRINT Part 2 Stage C (C1, C2, C4, C5, C6) and
SKETCH Step 3 (3a),(3c),(3d): `q_sign_average_proof` (#21 — unfold `qker`,`lam`; pure `ring`,
the cross terms cancel and `lam² = 81/100`; this is the ONLY guard against a λ/λ² swap, so it
must be `ring`-true as stated); `q_mem_Icc_proof` (#22 — each of the four factors lies in
`[0,1]`: `s - λs(1-s) ≥ s - s(1-s) = s² ≥ 0` and `s + λs(1-s) ≤ s(2-s) ≤ 1` since
`1 - s(2-s) = (1-s)² ≥ 0`; then #21 exhibits `qker s t` as a convex combination — `nlinarith`
per factor); `Rpoly_power_basis_proof` (#24 — `simp [Rpoly, cR, bern, Finset.sum_range_succ]`
then `ring_nf`/`norm_num`; this is what validates the 25-entry Bernstein table `cR` against
SKETCH (3c)'s power basis); `Rpoly_determinant_identity_proof` (#25 — rewrite by #24 FIRST so
`ring` sees the power basis rather than `bern`, then `ring`; budget compile time, this is the
largest `ring` call in the project); `Rpoly_lower_bound_proof` (#26 — support lemmas in
`namespace EntropyBound.RankOne`, e.g. `bern_nonneg` and `sum_bern_four_eq_one`
(`∑ k ∈ range 5, bern 4 k x = 1` via `add_pow`/`Finset.sum_range_choose_mul_pow` with
`x + (1-x) = 1`), then `Rpoly s t = ∑ₖ∑_ℓ cR k ℓ B_k(s) B_ℓ(t) ≥ (min cR)·1 = 31387/40000`,
the 25-entry minimum being `norm_num`-checked at `cR 2 3`). DO NOT attempt #23
`diag_normalization` or #27 `rank_one_product_bound` this iteration: they need
`gprofile_sq_eq` (#19) and `binEntropy_parabola_lower` (#6), which are being worked on by
other agents right now and are not ✅. Respect the BLUEPRINT Cheat-watch (Stage C) box: #25
must be proved for ALL real `s,t` with no interval hypothesis added; #26 must deliver the
stated constant `31387/40000`, not merely `0 < Rpoly`; do NOT "prove" #26 by `decide` on a
finite grid of `(s,t)` — that is sampling, not proof; do not drop the `s²t²(s-t)²` factor or
turn `=` into `≥` in #25. Guardrails to include: `example : Rpoly 0 0 = 5119741/1000000` and
`example : Rpoly 1 1 = 1`.

Agent 4: OWNS `EntropyBound/Proofs/ProfileSpeed/Basic.lean`, every new file in
`EntropyBound/Proofs/ProfileSpeed/`, AND the single file
`EntropyBound/Proofs/Toolbox/Poly.lean` (create it and import it FROM
`ProfileSpeed/Basic.lean`, since Agent 2 owns `Toolbox/Basic.lean`; touch no other Toolbox
file). In `Toolbox/Poly.lean` produce, verbatim from `Theorems.lean`, BLUEPRINT B9 / SKETCH
(2i): `Ppoly_pos_proof` (#17 — both factors are `≥ 1` on `[0,1]` because `z²(1-z) ≤ z`;
`nlinarith`); `Npoly_eq_deriv_form_proof` (#18, unrestricted `∀ z` — compute `deriv Ppoly`
via `HasDerivAt` or the `deriv` simp set, then `ring_nf`/`norm_num`; this is where SKETCH
(4a)'s coefficient transcription gets validated, so a mismatch means a real typo, not a proof
bug); `gprofile_sq_eq_proof` (#19 — `Real.sq_sqrt` needs the radicand `≥ 0`, which follows
from the algebraic identity `1 - s²(1+(81/100)(1-s)²) = (1-s)(1 + s - (81/100)s²(1-s))` plus
#17; do NOT redefine `gprof`, `Defs.lean` is frozen). In `Proofs/ProfileSpeed/` produce,
following BLUEPRINT D1–D2 / SKETCH (4b): `Gpoly_bernstein_left_proof` (#28) and
`Gpoly_bernstein_right_proof` (#29) — expand `Gpoly (x/2)` resp. `Gpoly (1/2 + x/2)` as
degree-10 polynomials and match `∑ k ∈ range 11, bGl/bGr k * bern 10 k x` by
`simp [Gpoly, Ppoly, Npoly, bern, bGl, bGr, Finset.sum_range_succ]; ring_nf; norm_num`; if
`ring_nf` times out, go coefficient-by-coefficient with `linear_combination`; and
`Gpoly_pos_proof` (#30) — all 22 Bernstein coefficients are positive (`norm_num` on the
`match`; smallest is `bGl 4 = 2530002779/840000000`), `bern 10 k x ≥ 0` on `[0,1]` and
`∑ k ∈ range 11, bern 10 k x = 1`, with an EXPLICIT case split on `z ≤ 1/2` (`z = x/2`,
`x = 2z`) versus `z ≥ 1/2` (`z = 1/2 + x/2`, `x = 2z-1`). Put all Bernstein helper lemmas in
`namespace EntropyBound.ProfileSpeed` (Agent 3 is proving its own degree-4 versions in
`namespace EntropyBound.RankOne` in parallel — identical bare names would clash). STRETCH,
only after the six above are ✅ and in this order: `gprofile_speed_le_proof` (#31, from
`Gpoly z > 0` ⇒ `25 N(z)² < 64 P(z)` with `Ppoly z > 0`) and `gprofile_hasDerivAt_proof`
(#20, chain rule on `u ↦ 2u √(Ppoly (1-u²))` using #18). Do NOT attempt #32
`gprofile_lipschitz` this iteration (it needs #31 plus the MVT plumbing). Respect the
BLUEPRINT Cheat-watch (Stage D) box: #31/#30 must be `∀ z ∈ [0,1]`, never "at the Bernstein
nodes"; do NOT prove `Gpoly_pos` by sampling points and appealing to continuity — the
Bernstein certificate IS the proof; never replace the constant `16/5` by a larger, easier one
(Step 6's margin `25/324 > log 2/9` has no slack). Guardrails to include:
`example : Gpoly 0 = 5023/100` and `example : Gpoly 1 = 28`.

## Iteration 2
Clear every REVIEW.md "Required follow-up": finish Stage B's four series leaves (the sole blocker
for Stage E), close Stage C and Stage D completely, open the untouched Stage I probability track,
and take the three newly-unblocked Stage G leaves plus the free Stage H identity. Advances
BLUEPRINT Stages B, C, D, G, H, I.

GLOBAL RULES FOR ALL FOUR AGENTS THIS ITERATION (binding, read before coding).
(a) NEVER edit `EntropyBound/Defs.lean`, `EntropyBound/Theorems.lean` (both SHA-pinned in
`scripts/frozen.sha256`), `EntropyBound.lean` (root import file), `EntropyBound/Solution.lean` or
`EntropyBound/Discharge.lean`. Three other agents are running in parallel right now; touching a
file you do not own loses work. You may READ and `import` any file; you may only WRITE the files
your own "Agent k:" line names.
(b) You may create NEW files only inside the directories your line names, and every new file must
be reachable from the module graph via an `import` you add to a `Basic.lean` that YOU own
(`EntropyBound.lean` already imports every `EntropyBound/Proofs/<Stage>/Basic.lean`).
(c) For each frozen theorem `t` you prove: write `theorem t_proof : <statement copied VERBATIM
from EntropyBound/Theorems.lean> := by …` in `namespace EntropyBound` in one of your files; then
in the SAME file add `namespace EntropyBound.Solution` with the verbatim restatement
`theorem t : <same statement> := EntropyBound.t_proof`, and the no-drift gate
`example : @EntropyBound.t = @EntropyBound.Solution.t := rfl`. Do NOT add the `Solution`
restatement for a theorem you did not finish (a `sorry` there is a hard `verify.py` failure).
(d) ALL support/helper lemmas go in your own sub-namespace (`namespace EntropyBound.Toolbox` /
`.RankOne` / `.ProfileSpeed` / `.Constants` / `.Diagonal` / `.Scalar` / `.FiniteEntropy` as your
line says), NEVER bare in `namespace EntropyBound` — parallel agents would otherwise clash on
names like `bern_nonneg`.
(e) Banned everywhere: `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`,
`debug.skipKernelTC`, and `decide` over a numeric grid (`scripts/ALLOWED_AXIOMS.txt` is EMPTY —
USER_NOTES.md permits no assumed certificates). `#print axioms EntropyBound.Solution.<t>` must
print exactly `propext, Classical.choice, Quot.sound`. Real-valued `def`s need
`noncomputable section`. Do NOT import `MeasureTheory`, `ProbabilityTheory` or `PMF` anywhere
(binding modeling decision 📝 2026-08-09T00:41:42Z).
(f) `lake build` must be clean (the only warnings allowed are the `declaration uses 'sorry'` ones
coming from `Theorems.lean`). Toolchain/Mathlib pins must not be bumped:
`leanprover/lean4:v4.31.0`, Mathlib rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
(g) Follow the BLUEPRINT Part −1 §5 worker-onboarding ritual: read `PROGRESS.md` end to end, then
append a `🔧 in progress` entry claiming your files BEFORE coding, then `✅`/`⚠️` entries as you
go, with `Agent: agent-iter2-<k>`, a real `date -u +"%Y-%m-%dT%H:%M:%SZ"` timestamp, the
`#print axioms` output on the `Check:` line, and a mandatory `Next:` line with backticked lemma
names. PROGRESS.md is append-only — never edit or delete an existing entry.
(h) ALREADY ✅ — reuse, never re-prove, never re-assign: #1–#12 and #17–#22, #24–#26, #28–#31.
Concretely `EntropyBound.strict_margin_proof`, `.log_ten_lower_proof`, `.log_ten_upper_proof`,
`.log_two_upper_proof`, `.C_lt_ratio_123_65_proof` (`Proofs/Constants/Basic.lean`);
`.binEntropy_parabola_lower_proof`, `.binEntropy_two_sided_proof`, `.fser_closed_form_proof`,
`.enat_series_form_proof`, `.enat_sum_of_squares_proof`, `.Qser_closed_form_proof`,
`.Qser_lower_bounds_proof` (`Proofs/Toolbox/{Entropy,Series,Parabola,Qseries}.lean`);
`.Ppoly_pos_proof`, `.Npoly_eq_deriv_form_proof`, `.gprofile_sq_eq_proof`
(`Proofs/Toolbox/Poly.lean`); `.q_sign_average_proof`, `.q_mem_Icc_proof`,
`.Rpoly_power_basis_proof`, `.Rpoly_determinant_identity_proof`, `.Rpoly_lower_bound_proof`
(`Proofs/RankOne/{Kernel,Bernstein,Determinant}.lean`); `.Gpoly_bernstein_left_proof`,
`.Gpoly_bernstein_right_proof`, `.Gpoly_pos_proof`, `.gprofile_speed_le_proof`,
`.gprofile_hasDerivAt_proof` (`Proofs/ProfileSpeed/{Basic,Bernstein}.lean`).

Agent 1: OWNS `EntropyBound/Proofs/Toolbox/Basic.lean` and every NEW file you create in
`EntropyBound/Proofs/Toolbox/` (suggested single new file `EntropyBound/Proofs/Toolbox/Aseries.lean`,
imported from `Toolbox/Basic.lean`). You may READ and `import` but must NOT edit
`Toolbox/Entropy.lean`, `Toolbox/Series.lean`, `Toolbox/Parabola.lean`, `Toolbox/Qseries.lean`, and
you must NOT create, edit or import-from `Toolbox/Poly.lean` (Agent 2 owns it). Produce, copied
VERBATIM from `EntropyBound/Theorems.lean`, BLUEPRINT Part 2 Stage B items B7 and B8, SKETCH (2f),
(2g), (2h): `Qser_hasDerivAt_proof` (#13, `Theorems.lean:63`,
`∀ z : ℝ, 0 ≤ z → z < 1 → HasDerivAt Qser (Qder z) z`); `Qder_upper_bounds_proof` (#14,
`Theorems.lean:65`, all three conjuncts `0 ≤ Qder z`, `Qder z ≤ z / (1 - z^2)`, and
`0 < z → Qder z ≤ -Real.log (1 - z^2) / z`); `Aser_closed_form_proof` (#15, `Theorems.lean:70`,
`∀ u ∈ Set.Icc (0:ℝ) 1, Aser u = u * Real.sqrt (Qser (1 - u^2))`); `Aser_hasDerivAt_proof` (#16,
`Theorems.lean:73`). Path to follow. (B7/#13) Termwise differentiation: for the given `z` pick a
rational `r` with `z < r < 1` (e.g. `r := (z+1)/2`) and differentiate on `Set.Ioo (-r) r`, where
both the series and the termwise derivative series are dominated by geometric series; Mathlib
handles: `hasDerivAt_tsum_of_summable_deriv` / `hasFDerivAt_tsum_of_summable_norm_deriv`, or the
uniform-convergence route `hasDerivAt_of_tendstoUniformlyOn` (BLUEPRINT Part 0 names both). The
frozen hypothesis is `0 ≤ z < 1` and must be discharged for EVERY such `z` — instantiating `r`
from `z` is fine, restricting the statement is not. (B7/#14) Coefficient bounds
`2j/((j+1)(2j+1)) ≤ 1` and `≤ 1/j`, both from `(j+1)(2j+1) = 2j² + 3j + 1 ≥ 2j²`; then compare
against `∑_{j≥1} z^(2j-1) = z/(1-z²)` and `∑_{j≥1} z^(2j-1)/j = -log(1-z²)/z` (the latter is
`Real.hasSum_log_sub_log_of_abs_lt_one` / the `-log(1-x)` series at `x = z²`, divided by `z`);
nonnegativity is termwise. (B8/#15) First prove the support identity
`∑' m, (1 - z^(m+1))²/((m+1)(m+2)) = (1-z) * Qser z` for `z ∈ [0,1]` — the left side is
`1 - 2 * fser z + fser (z²)`, which per the ✅ entry of 2026-08-09T01:16:25Z is "one
`Toolbox.hasSum_congr_fun` away from `Toolbox.hasSum_fser`" — then substitute `z = 1 - u²` and use
`Real.sqrt_mul`/`Real.sqrt_sq` with `u ≥ 0`. Check the boundary values `Aser 0 = 0`, `Aser 1 = 1`
as guardrail `example`s (BLUEPRINT Stage B cheat-watch mandates them). (B8/#16) Chain rule on
`A(u) = u * √(Qser (1-u²))` using #13 and `Qser z ≥ 1 > 0` (from ✅ `Qser_lower_bounds_proof`) so
`Real.sqrt` is differentiable there; `HasDerivAt.comp`, `HasDerivAt.sqrt`, `HasDerivAt.mul`, and
`HasDerivAt.congr_of_eventuallyEq` against #15 on a neighbourhood inside `Set.Ioo 0 1`. Note
`(u^2) * Qder (1-u^2)` IS `(1-z) Q'(z)` at `z = 1-u²` — no algebraic rearrangement is needed.
Already-✅ results you may use: `EntropyBound.Qser_closed_form_proof` (#11),
`EntropyBound.Qser_lower_bounds_proof` (#12), `EntropyBound.fser_closed_form_proof` (#8), and from
`namespace EntropyBound.Toolbox`: `summable_inv_mul_succ`, `tsum_inv_mul_succ`,
`summable_fser_term`, `hasSum_congr_fun`, `hasSum_fser`, `fser_eq`, `fser_one`,
`hasSum_pow_add_two`, `hasSum_psi`, `summable_coeff`, `summable_Qser_term`, `hasSum_Qser`,
`Hnat_eq_binEntropy`. Respect the BLUEPRINT Stage B Cheat-watch box: never replace a `tsum` by a
finite partial sum "for tractability"; do not prove #13 only on a subinterval and then quantify
over `0 ≤ z < 1` anyway; do not shrink a frozen domain or add a hypothesis. Do NOT touch #17–#20
(all ✅) and do NOT re-prove #11/#12.

Agent 2: OWNS `EntropyBound/Proofs/RankOne/` (all of `Basic.lean`, `Kernel.lean`, `Bernstein.lean`,
`Determinant.lean` plus a NEW `EntropyBound/Proofs/RankOne/Product.lean`),
`EntropyBound/Proofs/ProfileSpeed/` (`Basic.lean`, `Bernstein.lean` plus any new file),
`EntropyBound/Proofs/Toolbox/Poly.lean`, and `EntropyBound/Proofs/Constants/` (`Basic.lean`,
`LogEnclose.lean`). Import each new file from a `Basic.lean` you own. Produce, copied VERBATIM from
`EntropyBound/Theorems.lean`, in this priority order:
(1) `diag_normalization_proof` (#23, `Theorems.lean:100`,
`∀ s ∈ Set.Icc (0:ℝ) 1, s * gprof s = 2 * Real.sqrt (qker s s * (1 - qker s s))`) — BLUEPRINT
Stage C item C3, SKETCH (3b). Both sides are `≥ 0` (`Real.sqrt_nonneg`, and `s * gprof s ≥ 0`
since `gprof` is `2 * Real.sqrt …`), so it suffices to match squares:
`s² * gprof s ^ 2 = 4 * (qker s s * (1 - qker s s))`, which is `ring` after
`rw [EntropyBound.gprofile_sq_eq_proof]` (#19 ✅) and `simp only [qker, Ppoly]`; finish with
`Real.sqrt_eq_iff`-style reasoning or `Real.sqrt_eq_sqrt_of_sq_eq_sq`. Put it in
`RankOne/Product.lean`.
(2) `rank_one_product_bound_proof` (#27, `Theorems.lean:129`,
`∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, Real.log 2 * (s * t * gprof s * gprof t) ≤ Hnat (qker s t)`)
— BLUEPRINT Stage C item C7, SKETCH (3e), same file. From ✅
`EntropyBound.Rpoly_determinant_identity_proof` (#25) + `EntropyBound.Rpoly_lower_bound_proof`
(#26) get `(q(s,t)(1-q(s,t)))² ≥ q(s,s)(1-q(s,s)) · q(t,t)(1-q(t,t)) ≥ 0` (the slack term is
`s²t²(s-t)² * Rpoly s t ≥ 0`, using `sq_nonneg` and #26); take square roots with
`Real.sqrt_le_sqrt`/`Real.le_sqrt` and `Real.sqrt_mul`, using `q(1-q) ≥ 0` from ✅
`EntropyBound.q_mem_Icc_proof` (#22); then `Hnat (qker s t) ≥ 4 * Real.log 2 * (q(1-q))` by ✅
`EntropyBound.binEntropy_parabola_lower_proof` (#6) applied at `qker s t ∈ [0,1]` (#22), and
`4 * (s * gprof s / 2) * (t * gprof t / 2) = s*t*gprof s*gprof t` by (1) above.
(3) `gprofile_lipschitz_proof` (#32, `Theorems.lean:146`,
`∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, |gprof s - gprof t| ≤ (16/5) * |Real.sqrt (1-s) - Real.sqrt (1-t)|`)
— BLUEPRINT Stage D item D4, SKETCH (4c); put it in `Proofs/ProfileSpeed/` (new file, or
`ProfileSpeed/Basic.lean` which you own). Apply
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` to `φ : u ↦ gprof (1 - u^2)` on
`Set.Icc (0:ℝ) 1`, taking the `HasDerivWithinAt` on the interior from ✅
`EntropyBound.gprofile_hasDerivAt_proof` (#20) via `HasDerivAt.hasDerivWithinAt` and the bound
`|φ'| = |2 * Npoly (1-u²) / Real.sqrt (Ppoly (1-u²))| ≤ 16/5` from ✅
`EntropyBound.gprofile_speed_le_proof` (#31); continuity of `φ` at the endpoints comes from
`Real.continuous_sqrt` composed with a polynomial whose radicand is `≥ 0` on `[0,1]` (reuse
`EntropyBound.ProfileSpeed.gprof_radicand_eq` + `EntropyBound.Ppoly_pos_proof`). Then rewrite
`s = 1 - (Real.sqrt (1-s))^2` by `Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - s)` so that
`gprof s = φ (Real.sqrt (1-s))`, and DERIVE BOTH orderings `s ≤ t` and `t ≤ s` (the cheat-watch
forbids proving one case and calling it symmetric).
(4) SUPPORT, cheap and required by later stages — in
`EntropyBound/Proofs/Constants/LogEnclose.lean`, `namespace EntropyBound.Constants`, next to the
existing `logTail_of_one_le`, add `logTail_of_le_one` : the same explicit evaluation of
`Constants.logTail a J` for rational arguments `0 < a ≤ 1` (where `yOf a = (a-1)/(a+1) ≤ 0`, so
`|yOf a|` must be discharged by `abs_of_nonpos`). Do not change `logLo`, `logHi`, `logLo_le`,
`le_logHi`, `abs_log_sub_sum_le` or any existing statement in that file — only ADD. This is the
only extension `Proofs/Constants/` needs; BLUEPRINT E3 and G4 will both consume it.
Respect the BLUEPRINT Stage C and Stage D Cheat-watch boxes: #27 must keep the `Real.log 2` factor
exactly where the frozen statement puts it and must hold on the full closed `[0,1]²` including the
boundary where `gprof 1 = 0`; do not drop the `s²t²(s-t)²` factor or turn `=` into `≥` in #25;
NEVER enlarge the Lipschitz constant `16/5` in #32 (Step 6's margin `25/324 > log 2/9` has no
slack); do not re-prove or restate #19/#20/#31 — cite them. Guardrails already compiling in your
files (`Rpoly 0 0 = 5119741/1000000`, `Rpoly 1 1 = 1`, `Gpoly 0 = 5023/100`, `Gpoly 1 = 28`,
`(25:ℝ)/324 > Real.log 2 / 9`) must keep compiling.

Agent 3: OWNS `EntropyBound/Proofs/Diagonal/` (`Basic.lean` plus any new files) and
`EntropyBound/Proofs/Scalar/Basic.lean`. Import each new file from `Diagonal/Basic.lean`. Produce,
copied VERBATIM from `EntropyBound/Theorems.lean`, BLUEPRINT Part 2 Stage G items G1–G3 and Stage H
item H1, SKETCH (7a), (7b), (7c), (8a):
(1) `Phi_decomposition_proof` (#45, `Theorems.lean:200`, `∀ s t : ℝ, Phi s t = Dfun s + Dfun t +
(9/10) * (2 * enat (s*t) - enat (s^2) - enat (t^2) - (Real.log 2 / 9) * (gprof s - gprof t)^2)`) in
`Proofs/Scalar/Basic.lean` — it holds for ALL reals with NO hypotheses; `simp only [Phi, Dfun]`
then `ring`. The only content is `(9/10)*(1/9) = 1/10` and
`g(s)² + g(t)² - (g(s)-g(t))² = 2 g(s) g(t)`. Keep it hypothesis-free.
(2) `diagonal_at_one_proof` (#40, `Theorems.lean:187`, `Dfun 1 = 0`) — `enat 1 = Hnat 1 / 1 = 0`
(`Real.log_one`, `Real.log_zero`) and `gprof 1 = 0` because the radicand is
`(1 + 0) * (1 - 1*(1+0)) = 0`; `simp`/`norm_num` after unfolding `Dfun`, `enat`, `Hnat`, `gprof`.
(3) `diagonal_small_proof` (#41, `Theorems.lean:189`, `∀ s : ℝ, 0 < s → s ≤ 1/1000000 → 0 < Dfun s`)
— from ✅ `EntropyBound.binEntropy_two_sided_proof` (#7) get `enat (s²) ≥ -Real.log (s²) = 2*(-log s)`
and `enat s ≤ -Real.log s + 1`, and `(Real.log 2 / 10) * (gprof s)^2 ≥ 0` (a square times a
nonnegative constant — use ✅ `EntropyBound.log_two_upper_proof` only if you need `log 2 > 0`, which
is `Real.log_pos`). So `Dfun s ≥ (9/5 - Cval)*(-log s) - Cval = (8999/50000)*(-log s) - 81001/50000
> 0` because `-log s ≥ 6 * Real.log 10 > 12` by ✅ `EntropyBound.log_ten_lower_proof` (#2) and
`(8999/50000)*12 > 81001/50000`. Check that arithmetic exactly — do not eyeball it.
(4) `diagonal_large_proof` (#42, `Theorems.lean:191`, `∀ s : ℝ, 1 - 1/1000000 ≤ s → s < 1 →
0 < Dfun s`) — put `ε = 1 - s`, `δ = 1 - s² = ε(2-ε)`, `L = Real.log (1/ε) > 12` (from #2). Prove
the support lemma `Hnat_symm : ∀ z, Hnat z = Hnat (1 - z)` in `namespace EntropyBound.Diagonal`
(pure unfolding + `ring_nf`), so `Hnat (s²) = Hnat δ` and `Hnat s = Hnat ε`; then #7 gives
`enat (s²) / enat s ≥ ((2-ε)/(1-ε)) * (L - Real.log (2-ε) + 1 - δ)/(L+1) ≥ 2*(L + 3/10)/(L+1) >
123/65 > (10/9)*Cval`, using `Real.log (2-ε) ≤ Real.log 2 < 25/36` (✅ #4
`EntropyBound.log_two_upper_proof`), `δ < 1/500000`, and ✅ #5
`EntropyBound.C_lt_ratio_123_65_proof`. Conclude `(9/10)*enat (s²) - Cval * enat s > 0` and add
`(Real.log 2 / 10) * (gprof s)^2 ≥ 0`.
STRETCH, only after (1)–(4) are ✅ and logged, and ONLY as support lemmas (do NOT state a
`Solution` restatement for anything unfinished): begin the BLUEPRINT G4 box machinery for
`diagonal_middle` (#43) in a new `EntropyBound/Proofs/Diagonal/Enclose.lean` —
(i) a support lemma rewriting `Dfun s` on `(0,1)` into a `sqrt`-free form using ✅
`EntropyBound.gprofile_sq_eq_proof` (#19), i.e. `Dfun s = (9/10) * enat (s^2) - Cval * enat s +
(Real.log 2 / 10) * (4 * (1-s) * Ppoly s)`; (ii) monotone endpoint enclosures for
`s ↦ enat s` and `s ↦ enat (s^2)` on a rational box `[a,b] ⊆ (0,1)` built from ✅ #7
`binEntropy_two_sided` and the certified rational log enclosures
`EntropyBound.Constants.logLo_le` / `.le_logHi` in `EntropyBound/Proofs/Constants/LogEnclose.lean`
(READ-ONLY for you — Agent 2 owns that file this iteration; for arguments `a < 1` do NOT wait on
Agent 2's `logTail_of_le_one`, instead apply the API at `a⁻¹ > 1` together with `Real.log_inv`);
(iii) the BLUEPRINT-mandated guardrail `example : 0 < Dfun (686/1000)` proved BY THAT BOX
MACHINERY (this is where the true minimum ≈ 6.09e-5 lives — if the machinery cannot resolve it, it
will not resolve the range, so log that fact as `⚠️` rather than tuning the constant).
Respect the BLUEPRINT Stage G Cheat-watch box: never replace `Cval = 81001/50000` by anything
smaller; never enlarge the `10⁻⁶` small/large ranges without re-proving G2/G3 at the new endpoints;
`diagonal_middle`'s hypotheses are `≤`, not `<`. Do NOT attempt #43 `diagonal_middle` or #44
`diagonal_estimate` as frozen theorems this iteration (#44 needs #43). Guardrail to include:
`example : Dfun 1 = 0` (follows from (2)).

Agent 4: OWNS `EntropyBound/Proofs/FiniteEntropy/` entirely (`Basic.lean` plus any new files you
create — suggested `FiniteEntropy/Core.lean` and `FiniteEntropy/Uniform.lean`, both imported from
`FiniteEntropy/Basic.lean`) and `EntropyBound/Proofs/IndepCoupling/Basic.lean`. This is BLUEPRINT
Part 2 Stage I (items I1–I7) and SKETCH Step 9 (9a)–(9d); the whole track is untouched and depends
on NOTHING already proved, so you can start immediately. Work in this priority order, logging a `✅`
per theorem as it lands, and stop wherever you run out of time (an honest `⚠️` with the exact
failing goal is worth more than a rushed one):
(I1, first) support lemmas in `namespace EntropyBound.FiniteEntropy`: `entropyW_nonneg` (each term
`-w log w ≥ 0` for `w ∈ [0,1]`), `law_nonneg`, `law_sum_eq_one`, and the Gibbs bound
`∑ pᵢ log (1/pᵢ) ≤ Real.log N` for a weight vector supported on an `N`-element `Finset` (concavity
of `Real.log`, via `Real.add_one_le_exp` or `ConcaveOn.le_map_sum`; Mathlib also has
`Real.strictConcaveOn_negMulLog` and `Real.continuous_negMulLog`).
(1) `uniform_entropy_eq_log_card_proof` (#51, `Theorems.lean:234`) — `law (unifW G) id = unifW G`,
then `entropyW (unifW G) = ∑_{x ∈ G} (1/N) * Real.log N = Real.log N`.
(2) `entropy_le_log_card_proof` (#50, `Theorems.lean:229`) — Gibbs from I1 applied to `law w Z`
supported in `G`. The frozen hypothesis is exactly `∀ ω, w ω ≠ 0 → Z ω ∈ G`; do NOT add
`G.Nonempty` and do NOT divide by `G.card` in a way that assumes it.
(3) `freq_eq_one_sub_ES_proof` (#53, `Theorems.lean:240`) — `∑ₓ unifW G x * pcond G i x` grouped
fiberwise by `pref i.val` (`Finset.sum_fiberwise`, `Finset.sum_filter`) telescopes to
`Pr(Xᵢ = false) = 1 - Pr(Xᵢ = true)`, and `Pr(Xᵢ = true) = |{x ∈ G : x i = true}| / |G|`. This is
where `pcond`'s junk value `0` on unsupported prefixes must be shown harmless — it is always
multiplied by `unifW G x`, which is `0` off `G`.
(4) `condHrv_le_of_comp_proof` (#49, `Theorems.lean:224`) — "conditioning on more reduces entropy":
`H(Z, W) - H(W) ≤ H(Z, f(W)) - H(f(W))`, reduced to concavity of `Real.negMulLog` plus Jensen on
the finite conditional laws (`ConcaveOn.le_map_sum` / `ConcaveOn.smul_le_sum`). It must hold for an
ARBITRARY `f`, not just injective `f` — the whole point downstream is that `orVec` is
non-injective.
(5) `entropy_chain_rule_proof` (#48, `Theorems.lean:220`) — induct on the coordinate index using the
DEFINITIONAL `Hrv w (Z,W) = Hrv w W + condHrv w Z W` and the bookkeeping lemma
`Hrv w (fun ω => pref (i+1) (X ω)) = Hrv w (fun ω => pref i (X ω)) + condHrv w (fun ω => X ω i)
(fun ω => pref i (X ω))`, which follows from `law`-level injectivity of
`(pref i x, x i) ↦ pref (i+1) x`; the telescope closes because `pref 0 x = fun _ => false` and
`pref n x = x` for `x : Fin n → Bool`. Must hold for `n = 0` too (empty sum, `Hrv w X = 0`).
(6) `prefix_entropy_decomposition_proof` (#52, `Theorems.lean:237`) — combine (5) at `X := id`,
`w := unifW G` with (1), plus the support identity
`condHrv (unifW G) (fun x => x i) (fun x => pref i.val x) = HiFun G i` (the prefix-weighted average
of `Hnat (pcond G i v)`). That last identity is the real work of the stage; if you get only this
far, land it as a named support lemma and log it.
STRETCH, only after (1)–(6): `indep_support_mem_proof` (#54, `Theorems.lean:246`, BLUEPRINT Stage J
item J1) in `EntropyBound/Proofs/IndepCoupling/Basic.lean` — `windW G p ≠ 0` forces
`unifW G p.1 ≠ 0` and `unifW G p.2 ≠ 0`, hence `p.1, p.2 ∈ G`, and `UnionClosedCube` gives
`orVec p.1 p.2 ∈ G`. Do NOT attempt #55 `indep_coupling_bound` (it needs #48 + #49 plus the
`pref`/`orVec` commutation lemma).
Respect the BLUEPRINT Stage I Cheat-watch box: do NOT import `MeasureTheory` or
`ProbabilityTheory` and re-derive these from Mathlib's measure-theoretic entropy — the frozen
statements are about `Hrv`/`condHrv` exactly as `Defs.lean` defines them (📝 modeling decision (3)
of 2026-08-09T00:41:42Z is binding); #49 must hold for arbitrary `f`; #50 must not smuggle in
`G.Nonempty`; #52 must not be proved only for `n ≥ 1`. Guardrails to include:
`example : Hrv (unifW ({fun _ => false} : Finset (Fin 1 → Bool))) id = 0` and
`example : Hrv (unifW (Finset.univ : Finset (Fin 1 → Bool))) id = Real.log 2`.

## Iteration 3
Open the two remaining hard tracks and the two coupling stages: BLUEPRINT Stage E
(`Proofs/EntropySpeed/`, frozen #33–#38, the critical path to Stages F→H→L), Stage G's last leaf
#43 `diagonal_middle` with the NEW derivative-corrected box bound REVIEW iteration 2 requires, and
Stage J item J2 + Stage K (`Proofs/{IndepCoupling,SharedCoupling}/`, frozen #55–#59). Stage F (#39)
and Stage H (#46/#47) stay UNASSIGNED this iteration: #39 needs #38 and #46/#47 need #39 + #44, none
of which is ✅ yet — do not attempt them.

RULES FOR ALL FOUR AGENTS (read before writing code). (a) Onboarding ritual: read your `Agent k:`
line below, then `PROGRESS.md` end to end, then the BLUEPRINT stage section named in your line
INCLUDING its Cheat-watch box, then the cited SKETCH step; append a `🔧 in progress` PROGRESS entry
claiming your files BEFORE editing, and `✅`/`⚠️` entries as you go (real UTC timestamps from
`date -u +"%Y-%m-%dT%H:%M:%SZ"`, `Agent: agent-iter3-<k>`, backticked lemma names on `Next:`).
(b) NEVER edit `EntropyBound/Defs.lean` or `EntropyBound/Theorems.lean` (SHA-pinned), never weaken or
re-type a frozen statement, never add a hypothesis. (c) Copy each frozen statement VERBATIM from
`EntropyBound/Theorems.lean` into a `<name>_proof` in `namespace EntropyBound`, add the
`EntropyBound.Solution.<name>` restatement AND the no-drift gate
`example : @EntropyBound.<name> = @EntropyBound.Solution.<name> := rfl` in the SAME file, and report
`#print axioms EntropyBound.Solution.<name>` = `[propext, Classical.choice, Quot.sound]` in your
`Check:` line. (d) BANNED anywhere: `sorry`, `admit`, `axiom`, `decide`, `native_decide`, `unsafe`,
`implemented_by`, `skipKernelTC`, and any `MeasureTheory`/`ProbabilityTheory`/`PMF` import
(📝 modeling decision (3) of 2026-08-09T00:41:42Z). `scripts/ALLOWED_AXIOMS.txt` is EMPTY: both
interval-arithmetic obligations must be genuinely proved. (e) Touch ONLY the files your line lists;
the other three agents are running right now. (f) Real-valued `def`s need `noncomputable section`.
(g) Leave the build GREEN: the only acceptable warnings project-wide are the 61
`declaration uses 'sorry'` from `Theorems.lean`, and an unused frozen hypothesis must be absorbed by
`have _h := h` or it trips the `unusedVariables` linter. (h) ALREADY ✅ — do NOT re-prove, just cite:
#1–#32 (Stages A–D complete), #40 `diagonal_at_one`, #41 `diagonal_small`, #42 `diagonal_large`,
#45 `Phi_decomposition`, #48–#53 (Stage I complete), #54 `indep_support_mem`.

Agent 1: OWNS `EntropyBound/Proofs/EntropySpeed/Basic.lean` (the existing SETUP placeholder — it is
already imported by the root `EntropyBound.lean`; use it as your hub and add import lines for YOUR
new files only) plus NEW `EntropyBound/Proofs/EntropySpeed/Ends.lean` and NEW
`EntropyBound/Proofs/EntropySpeed/Lip.lean`. Do NOT touch the root `EntropyBound.lean`, do NOT
create or import `EntropySpeed/{Enclose,BoxesLow,BoxesHigh,Middle}.lean` (Agent 2 owns those), do NOT
touch `Proofs/Toolbox/` (read/import only — import `EntropyBound.Proofs.Toolbox.Aseries` and
`.Qseries` DIRECTLY rather than the `Toolbox.Basic` hub). This is BLUEPRINT Stage E items E1, E2, E5,
E6 and SKETCH Step 5 (5a), (5b), (5d). Support lemmas go in `namespace EntropyBound.EntropySpeed`.
Targets in this priority order:
(1) `Ader_lower_small_proof` (#33, `Theorems.lean:152`): `∀ z : ℝ, 0 < z → z ≤ 1/10 →
8/9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)`. Path (SKETCH 5a with the extended range of
📝 modeling decision (9), which is BINDING — the range is `(0, 1/10]`, do not "restore" `1/100`):
from ✅ `EntropyBound.Qser_lower_bounds_proof` (#12) get `1 ≤ Qser z`, hence `1 ≤ Real.sqrt (Qser z)`
and `Qser z / Real.sqrt (Qser z) = Real.sqrt (Qser z)` (`Real.div_sqrt` / `Real.sq_sqrt`); from ✅
`EntropyBound.Qder_upper_bounds_proof` (#14) get `0 ≤ Qder z` and `Qder z ≤ z/(1-z^2) ≤
(1/10)/(99/100) = 10/99`. Then the quotient is `≥ 1 - (1-z)*Qder z ≥ 1 - 10/99 = 89/99 > 88/99 = 8/9`.
(2) `Ader_lower_large_proof` (#34, `Theorems.lean:156`): same expression on `99999/100000 ≤ z < 1`.
Path (SKETCH 5b): `Qser z ≥ 1 + z^2/6 ≥ 1 + (624/625)/6 = 729/625 = (27/25)^2` (#12) gives
`Real.sqrt (Qser z) ≥ 27/25`; you then need only `(1-z) * Qder z / Real.sqrt (Qser z) ≤ 27/25 - 8/9 =
43/225 ≈ 0.191`, which is a LOT of slack, so use this cheap route instead of the sketch's
`ε log(1/ε)` monotonicity: the third conjunct of #14 gives `Qder z ≤ -Real.log (1 - z^2)/z`, and
`Real.log_le_sub_one_of_pos` at `1/Real.sqrt (1-z^2)` gives `-Real.log (1-z^2) ≤ 2/Real.sqrt (1-z^2)`,
so `(1-z) * Qder z ≤ 2(1-z)/(z * Real.sqrt (1-z^2)) ≤ 2 * Real.sqrt (1-z)/z ≤ 2*Real.sqrt (1/100000)
< 1/100` (using `1 - z^2 ≥ 1 - z` and `Real.sqrt_le_sqrt`).
(3) `EntropySpeed.Ader_lower_of_middle : (∀ z : ℝ, 1/10 ≤ z → z ≤ 99999/100000 →
8/9 ≤ (Qser z - (1-z)*Qder z)/Real.sqrt (Qser z)) → ∀ z : ℝ, 0 < z → z < 1 → 8/9 ≤ (…)` — the E4
case split, discharged from (1)+(2) plus the hypothesis. State it EXACTLY in this hypothesis form:
`EntropyBound.Ader_lower_middle` (#35) is still `sorry` and citing it would inject `sorryAx` — Agent 2
is proving it in parallel, and next iteration #36 becomes a one-liner.
(4) `EntropySpeed.Aser_lipschitz_lower_of` and (5) `EntropySpeed.entropy_speed_bound_of`: the frozen
conclusions of #37 (`Theorems.lean:168`) and #38 (`Theorems.lean:172`) VERBATIM, each with the same
`(hA : ∀ z : ℝ, 0 < z → z < 1 → 8/9 ≤ (Qser z - (1-z)*Qder z)/Real.sqrt (Qser z))` as its only extra
hypothesis. For (4) (BLUEPRINT E5 / SKETCH 5d first half): `ContinuousOn Aser (Set.Icc 0 1)` by the
Weierstrass M-test — every term of `Aser`'s inner `tsum` is `≤ 1/((m+1)*(m+2))` on `[0,1]` and ✅
`EntropyBound.Toolbox.summable_inv_mul_succ` is the majorant, so `tendstoUniformlyOn_tsum` +
`TendstoUniformlyOn.continuousOn` + `Real.continuous_sqrt.comp_continuousOn`; then
`exists_hasDerivAt_eq_slope` on `[u,v]` with ✅ `EntropyBound.Aser_hasDerivAt_proof` (#16) on the
interior and `hA`, handling `u = v` and BOTH orderings explicitly (do not say "by symmetry"). For (5)
(BLUEPRINT E6 / SKETCH 5d second half): with `a m = (1 - (1-u^2)^(m+1))/Real.sqrt ((m+1)*(m+2))` and
`b m` likewise in `v`, ✅ `EntropyBound.Toolbox.tsum_one_sub_pow_sq` + ✅
`EntropyBound.Aser_closed_form_proof` (#15) identify `∑' a m ^2 = (Aser u)^2` and `∑' b m ^2 =
(Aser v)^2`; get `∑' (a-b)^2 = ∑' a^2 - 2 ∑' a*b + ∑' b^2 ≥ (Aser u - Aser v)^2` from Cauchy–Schwarz
on FINITE partial sums (`Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_mul_sq_le_sq_mul_sq`)
passed to the limit (`HasSum.tendsto_sum_nat`, `Real.tsum_le_of_sum_range_le`), then `Real.sqrt` is
monotone and `Real.sqrt_sq_eq_abs`. Note `(a m - b m)^2 = ((1-u^2)^(m+1) - (1-v^2)^(m+1))^2/((m+1)*
(m+2))`, exactly the frozen summand. Do NOT replace any `tsum` by a partial sum and do NOT assume
`u ≥ v`. Respect the BLUEPRINT Stage E Cheat-watch box: `8/9` may not be weakened (Step 6 needs
`(8/9)^2 = 64/81`), the three ranges must still cover `(0,1)`, no `decide`/`native_decide`, no grid
evaluation. Guardrails to include: `example : EntropyBound.Aser 0 = 0` and
`example : EntropyBound.Aser 1 = 1` (both already available as `Toolbox.Aser_zero`/`.Aser_one`).

Agent 2: OWNS the NEW files `EntropyBound/Proofs/EntropySpeed/Enclose.lean`,
`EntropyBound/Proofs/EntropySpeed/BoxesLow.lean`, `EntropyBound/Proofs/EntropySpeed/BoxesHigh.lean`,
`EntropyBound/Proofs/EntropySpeed/Middle.lean` (the last one imports the other three), AND the root
import file `EntropyBound.lean`, to which your LAST action must be appending exactly one line,
`import EntropyBound.Proofs.EntropySpeed.Middle`, followed by a whole-project `lake build` — without
that line your files are outside the module graph and `verify.py` will not see them. Do NOT touch
`EntropySpeed/{Basic,Ends,Lip}.lean` (Agent 1 owns them) and do NOT touch `Proofs/Toolbox/` or
`Proofs/Constants/` (read/import only). This is BLUEPRINT Stage E item E3 / OBLIGATION 1 and SKETCH
Step 5 (5c). Support lemmas go in `namespace EntropyBound.EntropySpeed`. TARGET: the frozen
`Ader_lower_middle_proof` (#35, `Theorems.lean:160`): `∀ z : ℝ, 1/10 ≤ z → z ≤ 99999/100000 →
8/9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z)`. Engineering plan (follow it; it is the
BLUEPRINT E3 plan made concrete):
(i) SQUARE-FREE FORM in `Enclose.lean`: prove `EntropySpeed.ader_ge_of : 0 < NQ → 0 < Q →
64 * Q ≤ 81 * NQ^2 → 8/9 ≤ NQ / Real.sqrt Q` once, so no `Real.sqrt` appears in any box lemma
(`Real.sqrt_le_sqrt`, `Real.sq_sqrt`, `Real.le_div_iff₀`).
(ii) MONOTONE ENCLOSURE API in `Enclose.lean`, the key simplification: BOTH `Qser` and `Qder` are
increasing on `[0,1)` because every term is (`Summable.tsum_le_tsum` termwise — GOTCHA logged
2026-08-09T01:50:54Z: the bare `tsum_le_tsum` does not exist in this rev, use
`Summable.tsum_le_tsum h hf hg` with the termwise hypothesis FIRST; summability from ✅
`EntropyBound.Toolbox.summable_Qser_term` and `.summable_Qder_term`). So on a box `[a,b]` the
enclosure is just the endpoint values: `Qser a ≤ Qser z ≤ Qser b` and `0 ≤ Qder z ≤ Qder b`. NO
Taylor remainder is needed for the shape, only for the numbers.
(iii) NUMBERS AT RATIONAL ENDPOINTS. Lower bounds on `Qser a`: a partial sum, since all terms are
nonneg (`Finset.sum_le_tsum` + `Toolbox.summable_Qser_term`). Upper bounds on `Qser b`: for
`b ≤ 1/2` use partial sum + the explicit geometric tail `∑_{j>J} b^(2j)/((j+1)(2j+1)) ≤
b^(2J+2)/(1-b^2)` (coefficients `≤ 1`); for `b ≥ 1/2` use ✅ `EntropyBound.Qser_closed_form_proof`
(#11) with certified rational `Real.log` enclosures. Upper bounds on `Qder b`: take the MINIMUM of the
two bounds of ✅ `EntropyBound.Qder_upper_bounds_proof` (#14) at `z = b`, i.e. `b/(1-b^2)` and
`-Real.log (1-b^2)/b`. For every `Real.log` enclosure REUSE, do not rebuild:
`EntropyBound.Constants.logLo_le (a : ℚ) (J : ℕ) (0 < a) : ((logLo a J : ℚ) : ℝ) ≤ Real.log (a:ℝ)`
and `EntropyBound.Constants.le_logHi` from `EntropyBound/Proofs/Constants/LogEnclose.lean`, evaluated
by `rw [Constants.logLo, Constants.logMid, Constants.logTail_of_one_le …]; norm_num
[Finset.sum_range_succ]` for `a ≥ 1` or `Constants.logTail_of_le_one` for `a ≤ 1` (the `a⁻¹` +
`Real.log_inv` detour is no longer necessary).
(iv) COVER `[1/10, 99999/100000]` by an EXPLICITLY LISTED finite partition of rational breakpoints,
one `∀ z ∈ [aⱼ, aⱼ₊₁], 8/9 ≤ Ader z` lemma per box closed by `nlinarith` from the endpoint
enclosures, then chain them with `interval_cases`-free `rcases le_or_lt` splits. The true margin here
is ≈ `0.032` (minimum near `z ≈ 0.49`), i.e. ~500× more slack than Stage G, so start COARSE: ~64
boxes on `[1/10, 1/2]` in `BoxesLow.lean` and ~64 on `[1/2, 99999/100000]` in `BoxesHigh.lean`, and
refine only the boxes that fail. Log the exact partition in `PROGRESS.md` so a follow-up agent can
refine locally instead of restarting.
If you run out of time, land `Enclose.lean` (items (i)–(iii)) plus as many boxes as compile, log a
`⚠️` naming the exact first failing box and its certified numbers, and do NOT add a `Solution`
restatement for #35. Respect the BLUEPRINT Stage E Cheat-watch box: #35 is a genuine proof
obligation (no axiom is permitted), you must bound `Ader` on each CLOSED box rather than evaluating
at grid points, and you may not shrink the range `[1/10, 99999/100000]` or weaken `8/9`.

Agent 3: OWNS `EntropyBound/Proofs/Diagonal/` ENTIRELY (`Basic.lean` hub, `Endpoints.lean`,
`Enclose.lean` and any new files you add there — suggested `Diagonal/Deriv.lean`,
`Diagonal/BoxesA.lean`, `Diagonal/BoxesB.lean`, `Diagonal/Middle.lean`, all reachable from
`Diagonal/Basic.lean`, which the root already imports). Touch nothing outside that directory. This is
BLUEPRINT Stage G item G4 / OBLIGATION 2 / HARDEST and SKETCH Step 7 (7d). TARGET: frozen
`diagonal_middle` (#43, `Theorems.lean:193`): `∀ s : ℝ, 1/1000000 ≤ s → s ≤ 1 - 1/1000000 →
0 < Dfun s`; then, ONLY if #43 lands, frozen `diagonal_estimate` (#44, `Theorems.lean:196`) as the
four-way case split `s = 1` / `s ≤ 10⁻⁶` / `1 - 10⁻⁶ ≤ s < 1` / else, citing ✅
`EntropyBound.diagonal_at_one_proof`, `.diagonal_small_proof`, `.diagonal_large_proof` and #43.
MANDATORY NEW CONTENT — REVIEW iteration 2 explicitly forbids another lap of the endpoint-monotone
certificate. Agent 3's measurement of 2026-08-09T01:50:54Z is quantitative: the existing
`EntropyBound.Diagonal.Dfun_box_lower` loses ≈ `8·(b-a)` near the minimum, so against the true margin
`6.1·10⁻⁵` at `s ≈ 0.6856` it needs box width `≲ 7.6·10⁻⁶` (at width `10⁻⁵` it already fails:
`[0.68599, 0.68601]` certifies `-1.93·10⁻⁵`), i.e. ~10⁵ boxes. Log-enclosure precision is NOT the
bottleneck. So this iteration's deliverable is a DERIVATIVE-CORRECTED per-box bound:
(1) `Diagonal.hasDerivAt_Dfun : ∀ s, 0 < s → s < 1 → HasDerivAt Dfun (Dder s) s` where `Dder` is an
EXPLICIT elementary expression (rational functions of `s` plus `Real.log s`, `Real.log (1-s)`,
`Real.log 2`), obtained by differentiating the sqrt-free form ✅
`EntropyBound.Diagonal.Dfun_sqrt_free` (`Dfun s = 9/10 * enat (s^2) - Cval * enat s +
Real.log 2/10 * (4 * (1-s) * Ppoly s)`, which already discharges `(gprof s)^2` via ✅ #19) with
`Real.hasDerivAt_log`, `HasDerivAt.div`, `HasDerivAt.mul` and ✅
`EntropyBound.ProfileSpeed.hasDerivAt_Ppoly`.
(2) `Diagonal.Dfun_box_lower_mvt`: on a rational box `[a,b]` with midpoint `m`,
`Dfun s ≥ (a certified lower bound for Dfun m) - K_[a,b] * (b-a)/2` for all `s ∈ [a,b]`, where
`K_[a,b]` is a certified upper bound for `|Dder|` ON THAT BOX (via
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` or `exists_hasDerivAt_eq_slope`). The point is
that `K` is enclosed per box rather than taken globally: near the interior minimum `Dder ≈ 0`, so the
loss becomes second order in `(b-a)` instead of `8(b-a)`.
(3) VALIDATION MILESTONE, do this before any partition: re-prove
`EntropyBound.DiagonalSpotCheck.Dfun_686_pos : 0 < Dfun (686/1000)` through
`Dfun_box_lower_mvt` on a box of width `≥ 10⁻³` (the old machinery needs `6·10⁻⁶`). If that succeeds
the method is ~100× better and the partition is affordable; if it fails, STOP, append a `⚠️` with the
exact certified numbers (box, `K`, midpoint bound, resulting slack), and do not spend the iteration
on boxes.
(4) Then the graded partition of BLUEPRINT G4: coarse on `[10⁻⁶, 1/2]`, width ~`10⁻³` on `[1/2, 9/10]`
(this is where the `6.1·10⁻⁵` minimum lives), and GEOMETRICALLY refining breakpoints on
`[9/10, 1 - 10⁻⁶]` (e.g. `1 - 10^(-k)` with dyadic refinement) since the margin decays to ≈ `2·10⁻⁶`
at the right endpoint — never a uniform grid there. Emit the partition as an explicit `List ℚ`, one
lemma per box, split across `BoxesA.lean`/`BoxesB.lean` so the build stays incremental, and log the
exact partition in `PROGRESS.md`.
REUSE, do not rebuild: `EntropyBound.Diagonal.{Dfun_sqrt_free, enat_antitone, fser_mono, le_enat_of,
enat_le_of, log_inv_le_num, num_le_log_inv, Dfun_box_lower, Hnat_symm, gterm_nonneg}` and the worked
instantiation `EntropyBound.DiagonalSpotCheck.Dfun_686_pos`, plus
`EntropyBound.Constants.{logLo_le, le_logHi, logTail_of_one_le, logTail_of_le_one}` and ✅
`EntropyBound.ProfileSpeed.{Ppoly_eq_powerBasis, deriv_Ppoly, hasDerivAt_Ppoly}`. Respect the
BLUEPRINT Stage G Cheat-watch box: `Cval = 81001/50000` may NEVER be replaced by anything smaller (it
is optimized against this very inequality); the `10⁻⁶` small/large ranges may not be enlarged without
re-proving G2/G3 at the new endpoints; #43's hypotheses are `≤`, not `<`; no `native_decide`, no
grid sampling, no `sorry`. Guardrail already in the file and which must keep compiling:
`example : EntropyBound.Dfun 1 = 0`.

Agent 4: OWNS `EntropyBound/Proofs/IndepCoupling/` and `EntropyBound/Proofs/SharedCoupling/`
ENTIRELY (`Basic.lean` in each — both already imported by the root — plus any new files you create
there, e.g. `IndepCoupling/Bound.lean`, `SharedCoupling/{Dist,Marginal,Bound}.lean`, imported from
the respective `Basic.lean`). Touch nothing outside those two directories; `Proofs/FiniteEntropy/` is
read/import only. This is BLUEPRINT Stage J item J2 and Stage K items K1–K4, SKETCH Steps 10 and
11(a)–(d). Support lemmas go in `namespace EntropyBound.IndepCoupling` / `EntropyBound.SharedCoupling`.
Targets in this priority order — land what you can, and an honest `⚠️` with the exact failing goal is
worth more than a rushed one:
(1) `indep_coupling_bound_proof` (#55, `Theorems.lean:249`). Recipe (already scouted, PROGRESS
2026-08-09T01:47:40Z): first the missing commutation lemma
`IndepCoupling.pref_orVec : pref k (orVec x y) = orVec (pref k x) (pref k y)` (one `funext` + `Bool`
case split) and the distribution facts `windW_nonneg`, `windW_sum_eq_one` (from ✅
`EntropyBound.FiniteEntropy.unifW_nonneg`, `.unifW_sum_eq_one` and `Fintype.sum_prod_type`); then ✅
`EntropyBound.entropy_chain_rule_proof` (#48) at `w := windW G`, `X := fun p => orVec p.1 p.2`;
then ✅ `EntropyBound.condHrv_le_of_comp_proof` (#49) with `W := fun q => (pref i.val q.1,
pref i.val q.2)` and `f` the function sending that pair to `pref i.val (orVec q.1 q.2)` — this is
where `pref_orVec` earns its keep; finally the conditional-law computation showing the resulting
`condHrv` equals `∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y)`, reusing ✅
`EntropyBound.FiniteEntropy.{split_entropy, law_pref_eq, law_pair_false_eq, prefFiber, pcondV,
pcond_eq_pcondV}` and `Finset.sum_fiberwise`. BLUEPRINT Stage J Cheat-watch: the union bit is `false`
IFF BOTH bits are `false`, so the conditional zero-probability is the PRODUCT `pcond G i x *
pcond G i y` — never an inclusion–exclusion variant; do NOT add `UnionClosedCube G` to #55 (it is not
in the frozen statement and is not needed); do not assume `pcond ≠ 0`.
(2) `shared_isDist_proof` (#56, `Theorems.lean:255`). Support lemmas first:
`SharedCoupling.pcond_mem_Icc : pcond G i v ∈ Set.Icc (0:ℝ) 1` (a ratio of cardinalities, with the
junk value `0` when the fibre is empty), then `pmod G i σ v ∈ Set.Icc (0:ℝ) 1` from the ✅ factor
bounds `EntropyBound.RankOne.{sub_factor_nonneg, add_factor_le_one, sub_factor_le_one,
lam_mul_nonneg}` (SKETCH 3a; note `pmod` carries `λ = 9/10`, NOT `81/100` — do not swap), hence
`0 ≤ kern` and `∑ b : Bool, kern G i σ v b = 1`. Sum-to-one is the crux support lemma
`SharedCoupling.chain_sum_one : ∑ x : Fin n → Bool, ∏ i, kern G i (u i) x (x i) = 1` — prove it by
induction on the coordinate index, grouping vectors by `pref k` (`Finset.sum_fiberwise`,
`Finset.prod_range_succ`) since `kern` reads the prefix of the SAME vector it is evaluated on; then
`∑ p, wshW G p = 2^(-n) * ∑ u, (chain sum)*(chain sum) = 1` by `Fintype.sum_prod_type` and
`Finset.card_univ` on `Fin n → Bool`.
(3) `shared_support_mem_proof` (#57, `Theorems.lean:258`): the crux is
`SharedCoupling.pmod_eq_of_endpoints : pcond G i v = 0 ∨ pcond G i v = 1 → pmod G i σ v =
pcond G i v` (so a modified transition never creates mass outside `G`'s support); then by induction
on coordinates `wshW G p ≠ 0 → p.2.1 ∈ G ∧ p.2.2 ∈ G`, and `UnionClosedCube` finishes.
(4) `shared_marginal_uniform_proof` (#58, `Theorems.lean:262`): average the product formula over
`u : Fin n → Bool`; distinct coordinates carry distinct independent signs so the average factorizes
(`Finset.prod_sum` / `Fintype.sum_prod_piFinset`), and
`(1/2) * (kern G i true v b + kern G i false v b) = Pr(X i = b | X_{<i} = v)`; conclude by induction
on prefix length. #58 is NOT decorative — without it the `Egfun G i` of #59 is a different quantity
from the one Step 12 feeds to `scalar_inequality`.
(5) STRETCH `shared_coupling_bound_proof` (#59, `Theorems.lean:265`), BLUEPRINT K4 / SKETCH (11c)–(11d):
`Hrv wshW Z ≥ ∑ᵢ condHrv wshW Zᵢ (fun p => (pref i p.2.1, pref i p.2.2, pref i p.1))` by ✅ #48 + ✅
#49; that conditional entropy equals `∑ᵢ 𝔼 Hnat (qker Sᵢ Tᵢ)` because the fresh sign `Uᵢ` is uniform
and independent of the conditioning and averaging the two modified zero-probabilities over `σ = ±1`
is EXACTLY ✅ `EntropyBound.q_sign_average_proof` (#21); then ✅
`EntropyBound.rank_one_product_bound_proof` (#27) pointwise inside the expectation, and finally
`𝔼[W²] ≥ (𝔼W)²` (`Finset.sum_mul_sq_le_sq_mul_sq`) plus the tower property, using (4) to identify the
result with `(Egfun G i)^2`. BLUEPRINT Stage K Cheat-watch (binding): the conditional-i.i.d.
factorization must be PROVED from `wshW`'s explicit product formula (📝 modeling decision (8) of
2026-08-09T00:41:42Z) — if `X̃, Ỹ` were independent unconditionally the whole `1/10` term would be
unearned; no `Kernel`/`PMF` bind; do not weaken #59 to `≥ 0`; do not add `UnionClosedCube` to
#56/#58/#59 (only #57 has it).

## Iteration 4
Close the last 8 frozen theorems' worth of mathematics. This iteration advances BLUEPRINT
Stage E (E4–E6 restatements: #36/#37/#38), Stage F (F1: #39), Stage H (H2–H4: #46/#47) and
Stage L (L1: #60, L2: the cube→`Finset α` transfer for #61). Agents 2, 3 and 4 work on the
tail of one dependency chain, so each of them must deliver its result as a PROVED
HYPOTHESIS-FORM lemma whose conclusion is the frozen statement VERBATIM (exactly the pattern
Review iteration 3 check (g) validated for `EntropySpeed.Ader_lower_of_middle`), and then
close the frozen theorem outright if and only if its upstream `_proof` name is already
available in a clean build at the end of your run.

GLOBAL RULES (all agents, unchanged from previous iterations):
(a) NEVER edit `EntropyBound/Defs.lean` or `EntropyBound/Theorems.lean` — their SHA-256s are
    pinned in `scripts/frozen.sha256` and any byte change fails Check 1.
(b) NEVER weaken a frozen statement: no added hypothesis, no shrunk domain, no specialized
    `∀`, no `=` downgraded to `≤`/`⊆`, no constant enlarged/shrunk.
(c) BANNED everywhere: `sorry`, `admit`, `axiom`, `native_decide`, `decide`, `unsafe`,
    `implemented_by`, `skipKernelTC`, `ofReduceBool`, and any `MeasureTheory` /
    `ProbabilityTheory` / `PMF` / Mathlib-`Kernel` import (📝 modeling decision (3) of
    PROGRESS 2026-08-09T00:41:42Z). `scripts/ALLOWED_AXIOMS.txt` is EMPTY: every theorem you
    prove must `#print axioms` to exactly `[propext, Classical.choice, Quot.sound]`.
(d) For each frozen theorem you finish, put the sorry-free proof in `namespace EntropyBound`
    as `<name>_proof`, add the VERBATIM restatement `theorem <name> := <name>_proof` in
    `namespace EntropyBound.Solution` next to it, and add the no-drift gate
    `example : @EntropyBound.<name> = @EntropyBound.Solution.<name> := rfl`.
(e) Support lemmas go in your stage's namespace (`EntropyBound.OffDiagonal`,
    `EntropyBound.Scalar`, `EntropyBound.Assembly`). Before adding a name to a namespace that
    another file already uses, grep for it — a duplicate declaration is a hard
    "environment already contains" error at the root import (this bit Agent 2 in iteration 3).
(f) `Defs.lean` uses `noncomputable section` for all real-valued definitions; do the same.
(g) Append a PROGRESS.md entry (claim + result) with the mandatory `Check:`/`Next:` lines;
    never edit an existing entry. Timestamps via `date -u +"%Y-%m-%dT%H:%M:%SZ"`.
(h) DO NOT re-prove anything already ✅ (53 of 61): #1–#35, #40–#45, #48–#59. In particular
    `Ader_lower_middle` (#35) and `diagonal_middle` (#43) are CLOSED — no more box work is
    needed anywhere in this project. The ONLY open frozen names are #36 `Ader_lower_bound`,
    #37 `Aser_lipschitz_lower`, #38 `entropy_speed_bound`, #39 `off_diagonal_estimate`,
    #46 `pointwise_inequality`, #47 `scalar_inequality`, #60 `frankl_cube`,
    #61 `frankl_038272`.
(i) Gotchas recorded by earlier agents, reuse them: `le_or_lt` does not exist in this
    Lean v4.31.0 / Mathlib rev — use `le_or_gt`; `Finset.sum_le_tsum` does not exist — use
    `Summable.sum_le_tsum`; `continuousOn_finset_sum` is deprecated in favour of
    `continuousOn_finsetSum`; `norm_num` does not evaluate `Nat.choose` on numerals.

Agent 1: OWNS the NEW file `EntropyBound/Proofs/EntropySpeed/Final.lean`, the existing hub
`EntropyBound/Proofs/EntropySpeed/Basic.lean` (import lines only — do NOT touch `Ends.lean`,
`Lip.lean`, `Enclose.lean`, `BoxesLow.lean`, `BoxesHigh.lean`, `Middle.lean`), and ALL of
`EntropyBound/Proofs/OffDiagonal/` (the placeholder `Basic.lean` plus a NEW
`OffDiagonal/Estimate.lean` imported from it). Touch nothing else; every other directory is
read/import only.
  TASK 1 (do this FIRST, it is ~15 lines and everything else in the iteration waits on it).
  BLUEPRINT Stage E items E4/E5/E6. In `EntropySpeed/Final.lean` prove the three remaining
  Stage E frozen theorems by composing already-✅ results — Review iteration 3 check (g)
  verified MYSELF that all three go through with zero new mathematics:
    `theorem Ader_lower_bound_proof := EntropyBound.EntropySpeed.Ader_lower_of_middle EntropyBound.Ader_lower_middle_proof`   (#36, `Theorems.lean:164`)
    `theorem Aser_lipschitz_lower_proof := EntropyBound.EntropySpeed.Aser_lipschitz_lower_of Ader_lower_bound_proof`          (#37, `Theorems.lean:168`)
    `theorem entropy_speed_bound_proof := EntropyBound.EntropySpeed.entropy_speed_bound_of Ader_lower_bound_proof`            (#38, `Theorems.lean:172`)
  `Ader_lower_of_middle` is at `Proofs/EntropySpeed/Ends.lean:184`; `Aser_lipschitz_lower_of`
  at `Proofs/EntropySpeed/Lip.lean:139`; `entropy_speed_bound_of` at `Lip.lean:244`; each
  takes exactly one hypothesis, which is literally the frozen statement of #35 resp. #36.
  `EntropyBound.Ader_lower_middle_proof` is ✅ in `Proofs/EntropySpeed/Middle.lean`.
  `Final.lean` must `import EntropyBound.Proofs.EntropySpeed.Middle` and
  `EntropyBound.Proofs.EntropySpeed.Lip`. Add each `Solution` restatement + `rfl` gate per
  rule (d). ALSO add `import EntropyBound.Proofs.EntropySpeed.Final` to `EntropySpeed/Basic.lean`
  — this simultaneously fixes the module-graph fragility Review iteration 3 flagged (today
  only the root `EntropyBound.lean`'s last line reaches `EntropySpeed/Middle.lean`); there is
  no import cycle, `Middle.lean` imports only `Theorems` + `BoxesHigh`.
  TASK 2. BLUEPRINT Stage F item F1 / SKETCH Step 6 (`SKETCH.md:336-351`): frozen
  `off_diagonal_estimate` (#39, `Theorems.lean:180`),
  `∀ s, 0 < s → s ≤ 1 → ∀ t, 0 < t → t ≤ 1 → (Real.log 2 / 9) * (gprof s - gprof t)^2 ≤ 2 * enat (s*t) - enat (s^2) - enat (t^2)`.
  Put it in `OffDiagonal/Estimate.lean`. The chain, all four inputs now ✅:
    set `u := Real.sqrt (1-s)`, `v := Real.sqrt (1-t)`; `1 - u^2 = s` and `1 - v^2 = t` by
    `Real.sq_sqrt` (needs `s ≤ 1`, `t ≤ 1`), and `u, v ∈ Set.Icc 0 1`;
    (1) ✅ `EntropyBound.enat_sum_of_squares_proof` (#10, `Proofs/Toolbox/Series.lean:202`)
        rewrites `2*enat (s*t) - enat (s^2) - enat (t^2)` as the frozen `tsum`;
    (2) ✅ #38 `entropy_speed_bound_proof` (your TASK 1) at these `u, v` gives
        `(8/9)|u-v| ≤ √(that tsum)`; square BOTH sides — both are nonnegative, so use
        `mul_self_le_mul_self` / `pow_le_pow_left` (`by gcongr`) and `Real.sq_sqrt` on the
        nonneg tsum, and DISCHARGE the nonnegativity side conditions explicitly rather than
        pushing them into `nlinarith`;
    (3) ✅ `EntropyBound.gprofile_lipschitz_proof` (#32, `Proofs/ProfileSpeed/Basic.lean`)
        gives `|gprof s - gprof t| ≤ (16/5) * |u - v|`, hence squared
        `(u-v)^2 ≥ (25/256) (gprof s - gprof t)^2`;
    (4) `(64/81)*(25/256) = 25/324` and ✅ `EntropyBound.log_two_upper_proof` (#4,
        `Proofs/Constants/Basic.lean`, `Real.log 2 < 25/36`) gives `Real.log 2 / 9 < 25/324`;
        finish with `nlinarith`/`linarith` against `(gprof s - gprof t)^2 ≥ 0`.
  BLUEPRINT Stage F cheat-watch (binding, `BLUEPRINT.md:1027-1033`): the hypotheses are
  EXACTLY `0 < s ≤ 1`, `0 < t ≤ 1` — do not add `s ≠ t`, `s ≤ t`, or exclude `s = 1` (where
  `gprof 1 = 0`); do NOT replace `Real.log 2 / 9` in the conclusion by `25/324` (a different
  statement, and #45 `Phi_decomposition` is written with `log 2 / 9`); do not enlarge `16/5`
  or `8/9`. `OffDiagonal/Basic.lean` must import `OffDiagonal/Estimate.lean` (it is already
  imported from the root).

Agent 2: OWNS `EntropyBound/Proofs/Scalar/` ENTIRELY — the existing `Scalar/Basic.lean`
(which already holds ✅ `Phi_decomposition_proof` #45; append to it, do not rewrite it) plus
NEW `Scalar/Pointwise.lean` imported from `Basic.lean`. Touch nothing outside that directory.
This is BLUEPRINT Stage H items H2–H4, SKETCH Step 8 (`SKETCH.md:405-432`). Support lemmas in
`namespace EntropyBound.Scalar`.
  Because Agent 1 is proving #39 concurrently, state your Stage H results in HYPOTHESIS FORM
  first, with `hoff` being the frozen statement of #39 VERBATIM, i.e.
  `hoff : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 → (Real.log 2 / 9) * (gprof s - gprof t)^2 ≤ 2 * enat (s*t) - enat (s^2) - enat (t^2)`.
  Deliverables, in order:
  (H2) `Scalar.Phi_nonneg_of (hoff) : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ Phi s t`
       — rewrite by ✅ `EntropyBound.Phi_decomposition_proof` (#45, `Scalar/Basic.lean`), then
       ✅ `EntropyBound.diagonal_estimate_proof` (#44, `Proofs/Diagonal/Middle.lean`, gives
       `0 ≤ Dfun s` on `0 < s ≤ 1`) twice and `hoff` once; `linarith`.
  (H3) `Scalar.pointwise_inequality_of (hoff) : <#46 `Theorems.lean:206` VERBATIM>`
       — multiply H2 by `s*t > 0` and use the support lemma `Scalar.mul_enat_eq_Hnat :
       ∀ z : ℝ, z ≠ 0 → z * enat z = Hnat z` (`enat z = Hnat z / z`, `mul_div_cancel₀`) at
       `z = s`, `z = t` and `z = s*t`. THEN handle the boundary: the frozen statement is on
       the CLOSED `Set.Icc 0 1`, so `s = 0` and `t = 0` are separate cases in which both
       sides are `0` (`Hnat 0 = 0` since `Real.log 0 = 0`; the products vanish). Do not
       restrict to `(0,1]`.
  (H4) `Scalar.scalar_inequality_of (hpt : <#46 VERBATIM>) : <#47 `Theorems.lean:212` VERBATIM>`
       — NOTE this one needs NO input from Agent 1, only #46, so prove it unconditionally in
       `hpt` form. Apply `hpt` at `(S i, S j)`, take `∑ i ∑ j w i * w j * (·)`, divide by 2.
       The three algebraic facts (BLUEPRINT H4, `BLUEPRINT.md:1125-1130`):
       `∑ i ∑ j w i * w j * (S i * S j * gprof (S i) * gprof (S j)) = (∑ i, w i * (S i * gprof (S i)))^2`
       by `Finset.sum_mul_sum`; `∑ i ∑ j w i * w j * (S i * Hnat (S j)) = (∑ i, w i * S i) * (∑ i, w i * Hnat (S i))`
       likewise; and symmetry of the `s * Hnat t + t * Hnat s` term under swapping `i, j`
       (`Finset.sum_comm`). Use `hw1 : ∑ i, w i = 1` where needed.
  FINALLY, once (H2)–(H4) compile: check whether `EntropyBound.off_diagonal_estimate_proof`
  exists in a clean build (Agent 1's `EntropyBound/Proofs/OffDiagonal/Estimate.lean`). If it
  does, add `import EntropyBound.Proofs.OffDiagonal.Basic` and close both frozen theorems —
  `theorem pointwise_inequality_proof := Scalar.pointwise_inequality_of EntropyBound.off_diagonal_estimate_proof`
  and `theorem scalar_inequality_proof := Scalar.scalar_inequality_of pointwise_inequality_proof`
  — each with its `Solution` restatement and `rfl` gate per rule (d). If Agent 1's file is
  absent or red, do NOT add the import; leave the hypothesis forms, and log `⚠️` in
  PROGRESS.md naming exactly what is missing. Never `sorry` #39 to make the composition work.
  BLUEPRINT Stage H cheat-watch (binding, `BLUEPRINT.md:1132-1141`): #47 must quantify over
  an ARBITRARY `{ι : Type} [Fintype ι]` and an arbitrary weight vector — not `ι := Fin 2`,
  not a uniform `w`. Do NOT add `0 < w i` (Step 12 instantiates with `unifW G`, which IS `0`
  off `G`) and do NOT add `∀ i, 0 < S i` (the hypothesis is `S i ∈ Set.Icc 0 1` and the
  `S i = 0` case is genuinely used). Do not replace the double sum by a second variable with
  an independence hypothesis. Guardrail that must compile in your file: an `example`
  instantiating #47 (or `scalar_inequality_of`) at `ι := Fin 1`, `w := fun _ => 1`,
  `S := fun _ => 1/2`.

Agent 3: OWNS the NEW file `EntropyBound/Proofs/Assembly/Transfer.lean` and may append
EXACTLY ONE line, `import EntropyBound.Proofs.Assembly.Transfer`, to the root
`EntropyBound.lean` (nothing else in that file — Agent 4 owns `Assembly/Basic.lean`, do not
touch it, and do not create `Assembly/Cube.lean`). This is BLUEPRINT Stage L item L2
(`BLUEPRINT.md:1302-1313`), SKETCH Step 12's final paragraph. It is INDEPENDENT of every
other agent's work this iteration: nothing here needs #39, #46, #47 or #60 as a proof, only
#60 as a HYPOTHESIS. Support lemmas in `namespace EntropyBound.Assembly`, prefixed
distinctly from Agent 4's (e.g. `Assembly.tr_*`) to avoid a duplicate-declaration clash.
  Deliverable: `Assembly.frankl_038272_of_cube (hcube : <#60 `Theorems.lean:271` VERBATIM,
  i.e. ∀ {n : ℕ} (G : Finset (Fin n → Bool)), UnionClosedCube G → G.Nonempty →
  (∃ x ∈ G, x ≠ fun _ => false) → ∃ i : Fin n, 1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card>)
  : <#61 `Theorems.lean:275` VERBATIM>`.
  Construction (BLUEPRINT L2): let `U := F.sup id : Finset α`, `n := U.card`, and take the
  equiv `ε : Fin n ≃ ↥U` from `U.equivFin` (`.symm` as needed). Map
  `A ↦ (fun i => decide ((ε i : α) ∈ A))` and set `G := F.image (that map)`. Prove as support
  lemmas: (i) the map is INJECTIVE ON `F` — every `A ∈ F` satisfies `A ⊆ U` (from
  `Finset.le_sup`), so two members agreeing on all of `U` are equal (`Finset.ext`); (ii)
  `G.card = F.card` (`Finset.card_image_of_injOn`); (iii) `UnionClosed F → UnionClosedCube G`
  (`orVec` of the two indicator vectors is the indicator of `A ∪ B`, and `A ∪ B ∈ F`); (iv)
  `(G.filter (fun x => x i = true)).card = (F.filter (fun A => (ε i : α) ∈ A)).card` (again
  `card_image_of_injOn`, on the filtered set); (v) `F.Nonempty → G.Nonempty`; (vi)
  `F.Nonempty → F ≠ {∅} → ∃ x ∈ G, x ≠ fun _ => false` (some `A ∈ F` is nonempty; pick
  `a ∈ A`, then `a ∈ U`, so the indicator vector is `true` at `ε.symm ⟨a, _⟩`). Then #61
  follows from `hcube` applied to `G`: obtain `i`, take `x := (ε i : α)`, and rewrite the two
  cardinalities by (ii) and (iv).
  BLUEPRINT Stage L cheat-watch (binding, `BLUEPRINT.md:1315-1327`): `α` stays ARBITRARY with
  only `[DecidableEq α]` — no `[Fintype α]`, no `α := ℕ`, no `F ⊆ U.powerset` hypothesis. The
  hypotheses are exactly `UnionClosed F`, `F.Nonempty`, `F ≠ {∅}`; adding `2 ≤ F.card` or
  `∅ ∈ F` is the cardinal cheat. The conclusion is the ℕ inequality
  `1196 * F.card ≤ 3125 * (F.filter …).card` — do not restate it over ℝ and do not flip the
  constants. Injectivity in (i) MUST be proved, not `sorry`d or dodged — if it failed,
  `G.card < F.card` and the bound would be about a different family. Note `decide` is a
  BANNED TACTIC but `decide : Prop → Bool` as a FUNCTION (`Decidable.decide`) is the ordinary
  way to write the indicator and is fine; if you prefer, use `if a ∈ A then true else false`.
  Guardrail to add at the bottom of your file, once `frankl_038272_of_cube` compiles: an
  `example` that feeds it a `hcube` obtained by `fun G _ hne hnt => …` on the concrete family
  `({{0}, {0,1}} : Finset (Finset ℕ))` is NOT required; instead just check the transfer
  end-to-end shape compiles, e.g.
  `example (h : <#60 statement>) : ∃ x : ℕ, 1196 * ({{0}, {0,1}} : Finset (Finset ℕ)).card ≤ 3125 * (({{0}, {0,1}} : Finset (Finset ℕ)).filter (fun A => x ∈ A)).card := frankl_038272_of_cube h _ (by …) (by …) (by …)`.

Agent 4: OWNS `EntropyBound/Proofs/Assembly/Basic.lean` (the existing placeholder, already
imported from the root) and the NEW file `EntropyBound/Proofs/Assembly/Cube.lean` imported
from it. Do NOT create or touch `Assembly/Transfer.lean` (Agent 3) and do NOT edit the root
`EntropyBound.lean` (Agent 3 appends one line there). This is BLUEPRINT Stage L item L1
(`BLUEPRINT.md:1280-1300`), SKETCH Step 12 (`SKETCH.md:544-576`). Support lemmas in
`namespace EntropyBound.Assembly`, prefixed distinctly from Agent 3's (e.g. `Assembly.cu_*`).
  Deliverable: `Assembly.frankl_cube_of_scalar (hsc : <#47 `Theorems.lean:212` VERBATIM,
  including the implicit `{ι : Type} [Fintype ι]` and all three hypotheses>) : <#60
  `Theorems.lean:271` VERBATIM>`. Everything else it needs is already ✅. Proof plan:
  - Support lemma `Assembly.HiFun_nonneg : 0 ≤ HiFun G i` (each `Hnat` of a `pcond ∈ [0,1]`
    is `≥ 0`; `pcond ∈ Set.Icc 0 1` is ✅ `EntropyBound.SharedCoupling.pcond_nonneg`,
    `.pcond_le_one` in `Proofs/SharedCoupling/Dist.lean`).
  - By contradiction: assume `∀ i, ¬(1196 * G.card ≤ 3125 * (G.filter (fun x => x i = true)).card)`,
    i.e. frequency `< cval` for every `i`. Push to ℝ and apply ✅
    `EntropyBound.freq_eq_one_sub_ES_proof` (#53) to get `1 - cval < ESfun G i`, hence
    `1 - cval ≤ ESfun G i`, for every `i`.
  - Two entropy ceilings: ✅ `EntropyBound.entropy_le_log_card_proof` (#50) with
    ✅ `.indep_support_mem_proof` (#54) and `EntropyBound.IndepCoupling.{windW_nonneg,
    windW_sum_eq_one}` (`Proofs/IndepCoupling/Bound.lean`) gives
    `Hrv (windW G) (fun p => orVec p.1 p.2) ≤ Real.log G.card`; likewise with
    ✅ `.shared_support_mem_proof` (#57) and ✅ `.shared_isDist_proof` (#56) gives
    `Hrv (wshW G) (fun p => orVec p.2.1 p.2.2) ≤ Real.log G.card`.
  - Two entropy floors: ✅ `EntropyBound.indep_coupling_bound_proof` (#55) and ✅
    `.shared_coupling_bound_proof` (#59). Take the `(9/10, 1/10)` mixture:
    `Real.log G.card ≥ (9/10) * (∑ i, ∑ x, ∑ y, unifW G x * unifW G y * Hnat (pcond G i x * pcond G i y)) + (Real.log 2 / 10) * (∑ i, (Egfun G i)^2)`.
  - Per coordinate `i`, apply `hsc` with `ι := Fin n → Bool`, `w := unifW G`,
    `S := pcond G i` (hypotheses: `EntropyBound.FiniteEntropy.unifW_nonneg`,
    `.unifW_sum_eq_one` — the latter needs `G.Nonempty`, which is the frozen `hne` — and
    `pcond G i x ∈ Set.Icc 0 1` from the two `SharedCoupling` lemmas above). Note that with
    these instantiations `∑ x, unifW G x * pcond G i x` IS `ESfun G i`,
    `∑ x, unifW G x * Hnat (pcond G i x)` IS `HiFun G i`, and
    `∑ x, unifW G x * (pcond G i x * gprof (pcond G i x))` IS `Egfun G i` — check the
    `Defs.lean` definitions (D33–D35) and rewrite by `rfl`/`simp only [ESfun, HiFun, Egfun]`
    rather than reproving. Combined with `ESfun G i ≥ 1 - cval` and `HiFun G i ≥ 0`, the
    `i`-th bracket is `≥ Cval * (1 - cval) * HiFun G i`.
  - Sum over `i` and use ✅ `EntropyBound.prefix_entropy_decomposition_proof` (#52,
    `∑ i, HiFun G i = Real.log G.card`) to get
    `Real.log G.card ≥ Cval * (1 - cval) * Real.log G.card`. ✅
    `EntropyBound.strict_margin_proof` (#1) says `Cval * (1 - cval) = 1 + 929/156250000 > 1`,
    and `Real.log G.card ≥ 0` (from `1 ≤ G.card`, `hne`), so `Real.log G.card = 0`, i.e.
    `G.card = 1`.
  - Endgame: `G = {x₀}` with `x₀ ≠ fun _ => false` by `hnt`, so some `i` has `x₀ i = true`;
    then `(G.filter (fun x => x i = true)).card = 1 = G.card` and
    `1196 * 1 ≤ 3125 * 1` — contradicting the assumed strict inequality at that `i`. The
    `n = 0` case needs no separate treatment: `hnt` is then unsatisfiable
    (`Fin 0 → Bool` has a unique element), so notice that BEFORE casing on `n`.
  FINALLY, once `frankl_cube_of_scalar` compiles: check whether
  `EntropyBound.scalar_inequality_proof` exists in a clean build (Agent 2's
  `EntropyBound/Proofs/Scalar/`). If it does, add `import EntropyBound.Proofs.Scalar.Basic`
  and close #60 —
  `theorem frankl_cube_proof := Assembly.frankl_cube_of_scalar EntropyBound.scalar_inequality_proof`
  — with its `Solution` restatement and `rfl` gate per rule (d). If it is absent or red, do
  NOT add the import; leave the hypothesis form and log `⚠️` in PROGRESS.md naming exactly
  what is missing. Never `sorry` #47 to make the composition work.
  BLUEPRINT Stage L cheat-watch (binding): #60's hypotheses are exactly `UnionClosedCube G`,
  `G.Nonempty`, `∃ x ∈ G, x ≠ fun _ => false` — do not add `2 ≤ G.card`, do not add
  `(fun _ => false) ∈ G`, do not add `0 < n`. The conclusion is the ℕ inequality
  `1196 * G.card ≤ 3125 * (G.filter …).card`; keep the constants and their sides exactly as
  frozen. `cval = 1196/3125` and `Cval = 81001/50000` come from the frozen `Defs.lean` — never
  replace either by a rounded value.
