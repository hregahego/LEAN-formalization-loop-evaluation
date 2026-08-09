/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Theorems
import EntropyBound.Solution

/-!
# `EntropyBound.Discharge` — machine-checked no-drift gates

For every frozen theorem `t` of `EntropyBound/Theorems.lean` whose proof exists in
`Proofs/`, this file contains a gate

```
example : @EntropyBound.t = @EntropyBound.t_proof := rfl
```

which type-checks **iff** the proof has exactly the frozen proposition.  `scripts/verify.py`
independently generates the corresponding `EntropyBound.Solution.t` gates, so an empty
`Discharge.lean` cannot hide drift.

This module is a stub at the end of the SETUP stage: nothing is proved yet.
-/
