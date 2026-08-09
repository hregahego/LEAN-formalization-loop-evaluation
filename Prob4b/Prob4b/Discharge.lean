/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b SETUP agent
-/
import Prob4b.Solution

/-!
# No-drift gates

For each of the 20 frozen statements this module carries the machine-checked
gate

```
example : @Prob4b.<name> = @Prob4b.<name>_proof := rfl
```

which type-checks if and only if the proof in `Prob4b/Proofs/**` has *exactly*
the frozen proposition. `verify.py` independently generates the companion gates
`@Prob4b.<name> = @Prob4b.Solution.<name> := rfl`.

Each stage adds its gates here as it closes a frozen theorem. As of iteration 5
ALL TWENTY frozen statements are gated, namely (in frozen order) `B_nontrivial`,
`B_relation`, `B_isNoetherianRing`, `B_maximalIdeal_pow_three`,
`B_colon_two_gen`, `B_triple_inter_eq_bot`, `M_ann_eq`, `M_pair_inter`,
`M_u_ne_zero`, `M_u_mem_triple`, `M_triple_defect`, `C_isNoetherianRing`,
`C_ann_eq`, `C_pair_inter`, `C_triple_defect`, `R_finiteConductor`,
`R_triple_inter_not_fg`, `R_not_quasiCoherent`,
`quasiCoherent_imp_finiteConductor` and the headline
`exists_finiteConductor_not_quasiCoherent`.
-/

namespace Prob4b

/-- No-drift gate for frozen statement 1. -/
example : @Prob4b.B_nontrivial = @Prob4b.B_nontrivial_proof := rfl

/-- No-drift gate for frozen statement 2. -/
example : @Prob4b.B_relation = @Prob4b.B_relation_proof := rfl

/-- No-drift gate for frozen statement 3. -/
example : @Prob4b.B_isNoetherianRing = @Prob4b.B_isNoetherianRing_proof := rfl

/-- No-drift gate for frozen statement 4. -/
example : @Prob4b.B_maximalIdeal_pow_three = @Prob4b.B_maximalIdeal_pow_three_proof := rfl

/-- No-drift gate for frozen statement 5. -/
example : @Prob4b.B_colon_two_gen = @Prob4b.B_colon_two_gen_proof := rfl

/-- No-drift gate for frozen statement 6. -/
example : @Prob4b.B_triple_inter_eq_bot = @Prob4b.B_triple_inter_eq_bot_proof := rfl

/-- No-drift gate for frozen statement 7. -/
example : @Prob4b.M_ann_eq = @Prob4b.M_ann_eq_proof := rfl

/-- No-drift gate for frozen statement 8. -/
example : @Prob4b.M_pair_inter = @Prob4b.M_pair_inter_proof := rfl

/-- No-drift gate for frozen statement 9. -/
example : @Prob4b.M_u_ne_zero = @Prob4b.M_u_ne_zero_proof := rfl

/-- No-drift gate for frozen statement 10. -/
example : @Prob4b.M_u_mem_triple = @Prob4b.M_u_mem_triple_proof := rfl

/-- No-drift gate for frozen statement 11. -/
example : @Prob4b.M_triple_defect = @Prob4b.M_triple_defect_proof := rfl

/-- No-drift gate for frozen statement 12. -/
example : @Prob4b.C_isNoetherianRing = @Prob4b.C_isNoetherianRing_proof := rfl

/-- No-drift gate for frozen statement 13. -/
example : @Prob4b.C_ann_eq = @Prob4b.C_ann_eq_proof := rfl

/-- No-drift gate for frozen statement 14. -/
example : @Prob4b.C_pair_inter = @Prob4b.C_pair_inter_proof := rfl

/-- No-drift gate for frozen statement 15. -/
example : @Prob4b.C_triple_defect = @Prob4b.C_triple_defect_proof := rfl

/-- No-drift gate for frozen statement 16. -/
example : @Prob4b.R_finiteConductor = @Prob4b.R_finiteConductor_proof := rfl

/-- No-drift gate for frozen statement 17. -/
example : @Prob4b.R_triple_inter_not_fg = @Prob4b.R_triple_inter_not_fg_proof := rfl

/-- No-drift gate for frozen statement 18. -/
example : @Prob4b.R_not_quasiCoherent = @Prob4b.R_not_quasiCoherent_proof := rfl

/-- No-drift gate for frozen statement 19. -/
example : @Prob4b.quasiCoherent_imp_finiteConductor =
    @Prob4b.quasiCoherent_imp_finiteConductor_proof := rfl

/-- No-drift gate for frozen statement 20. -/
example : @Prob4b.exists_finiteConductor_not_quasiCoherent =
    @Prob4b.exists_finiteConductor_not_quasiCoherent_proof := rfl

end Prob4b
