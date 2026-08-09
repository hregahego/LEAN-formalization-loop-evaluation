/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Proofs.EntropySpeed.Ends
import EntropyBound.Proofs.EntropySpeed.Lip
import EntropyBound.Proofs.EntropySpeed.Final

/-!
# Stage E — the entropy speed bound `A'(u) ≥ 8/9` (`SKETCH.md` Step 5)

Hub module for the `EntropySpeed` stage.  The actual content lives in

* `EntropyBound.Proofs.EntropySpeed.Ends` — BLUEPRINT E1, E2 (#33, #34) and the E4 case
  split in hypothesis form;
* `EntropyBound.Proofs.EntropySpeed.Lip` — BLUEPRINT E5, E6 (the frozen conclusions of #37
  and #38, each with the `A' ≥ 8/9` statement as its only extra hypothesis);
* `EntropyBound.Proofs.EntropySpeed.Final` — BLUEPRINT E4, E5, E6 closed (#36, #37, #38),
  composing the hypothesis forms above with `Ader_lower_middle_proof` (#35, `Middle.lean`).

All declarations belong to `namespace EntropyBound` and must never shadow a frozen name.
-/

namespace EntropyBound

end EntropyBound
