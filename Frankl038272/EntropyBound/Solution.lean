/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.Constants.Basic
import EntropyBound.Proofs.Toolbox.Basic
import EntropyBound.Proofs.RankOne.Basic
import EntropyBound.Proofs.ProfileSpeed.Basic
import EntropyBound.Proofs.EntropySpeed.Basic
import EntropyBound.Proofs.OffDiagonal.Basic
import EntropyBound.Proofs.Diagonal.Basic
import EntropyBound.Proofs.Scalar.Basic
import EntropyBound.Proofs.FiniteEntropy.Basic
import EntropyBound.Proofs.IndepCoupling.Basic
import EntropyBound.Proofs.SharedCoupling.Basic
import EntropyBound.Proofs.Assembly.Basic

/-!
# `EntropyBound.Solution` — the frozen theorems, restated and proved

Once a frozen theorem of `EntropyBound/Theorems.lean` has a sorry-free `_proof` declaration
in `Proofs/`, restate it here **verbatim** in `namespace EntropyBound.Solution` and set it
`:= <name>_proof`.  `scripts/verify.py` checks that
`#print axioms EntropyBound.Solution.<name>` is clean for every frozen name, and that each
`EntropyBound.Solution.<name>` has exactly the frozen statement's type.

This module is a stub at the end of the SETUP stage: no frozen theorem is proved yet, and a
restatement may never be `sorry`.
-/

namespace EntropyBound.Solution

end EntropyBound.Solution
