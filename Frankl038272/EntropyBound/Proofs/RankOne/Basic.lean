/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Proofs.RankOne.Kernel
import EntropyBound.Proofs.RankOne.Bernstein
import EntropyBound.Proofs.RankOne.Determinant
import EntropyBound.Proofs.RankOne.Product

/-!
# Stage C — the rank-one product bound `h(q(s,t)) ≥ s t g(s) g(t)` (`SKETCH.md` Step 3)

Aggregator module for the `RankOne` stage.  The proofs live in the sibling files imported
above:

* `RankOne/Kernel.lean` — C1/C2: `q_sign_average` (#21) and `q_mem_Icc` (#22);
* `RankOne/Bernstein.lean` — C4/C6: `Rpoly_power_basis` (#24) and `Rpoly_lower_bound` (#26);
* `RankOne/Determinant.lean` — C5: `Rpoly_determinant_identity` (#25).

Still open in this stage: `diag_normalization` (#23), which needs `gprofile_sq_eq` (#19),
and `rank_one_product_bound` (#27), which needs #19, #23 and `binEntropy_parabola_lower`
(#6).

All frozen restatements belong to `namespace EntropyBound.Solution`; support lemmas live in
`namespace EntropyBound.RankOne`.
-/

namespace EntropyBound

end EntropyBound
