/-
# Prob27b — the no-drift gate

For each frozen theorem of `Prob27b/Theorems.lean` that has been proved, add

```lean
example : @Prob27b.<name> = @Prob27b.<name>_proof := rfl
```

here.  Such a line type-checks **iff** the proof has *exactly* the frozen
proposition, so it machine-checks that no statement drifted.

SETUP: no frozen theorem is proved yet, so there is nothing to gate.  (Note that
`scripts/verify.py` does not rely on this file: it *generates* the analogous
`@Prob27b.<name> = @Prob27b.Solution.<name>` gates itself.)
-/
import Prob27b.Theorems
import Prob27b.Solution

namespace Prob27b

end Prob27b
