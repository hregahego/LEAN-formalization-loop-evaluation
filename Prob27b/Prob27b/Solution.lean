/-
# Prob27b — the clean answer

Once a frozen theorem of `Prob27b/Theorems.lean` is proved in `Prob27b/Proofs/**`,
restate it **verbatim** here in `namespace Prob27b.Solution` and set it
`:= <name>_proof` (the sorry-free declaration from `Proofs/`).

`scripts/verify.py` checks `#print axioms Prob27b.Solution.<name>` for every
frozen name, and generates the gate `@Prob27b.<name> = @Prob27b.Solution.<name>`
so the restatement cannot drift from the frozen statement.

SETUP: no frozen theorem is proved yet, so this namespace is still empty.
-/
import Prob27b.Theorems
import Prob27b.Proofs.StageA.Basic
import Prob27b.Proofs.StageB.Basic
import Prob27b.Proofs.StageC.Basic
import Prob27b.Proofs.StageD.Basic
import Prob27b.Proofs.StageE.Basic
import Prob27b.Proofs.StageF.Basic

namespace Prob27b.Solution

end Prob27b.Solution
