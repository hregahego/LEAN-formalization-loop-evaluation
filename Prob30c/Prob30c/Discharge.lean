/-
`Prob30c.Discharge` — the machine-checked no-drift gate.

For each of the 15 frozen theorems this file compiles
`example : @Prob30c.<name> = @Prob30c.Solution.<name> := rfl`,
which type-checks **iff** the `Solution` declaration has *exactly* the frozen
proposition — no added hypothesis, no weakened conclusion, no renamed binder
order.  `scripts/verify.py` (check 5b) regenerates the same gates independently.
-/
import Prob30c.Solution

namespace Prob30c

example : @Prob30c.mem_polyExt_iff = @Prob30c.Solution.mem_polyExt_iff := rfl
example : @Prob30c.isNAbsorbing_succ = @Prob30c.Solution.isNAbsorbing_succ := rfl
example : @Prob30c.Jid_pow_three_eq_bot = @Prob30c.Solution.Jid_pow_three_eq_bot := rfl
example : @Prob30c.Jid_sq_eq_Wid = @Prob30c.Solution.Jid_sq_eq_Wid := rfl
example : @Prob30c.isNoetherianRing_A = @Prob30c.Solution.isNoetherianRing_A := rfl
example : @Prob30c.s_component_cancellation = @Prob30c.Solution.s_component_cancellation := rfl
example : @Prob30c.not_isNAbsorbing_A_q = @Prob30c.Solution.not_isNAbsorbing_A_q := rfl
example : @Prob30c.fPoly_mul_gPoly = @Prob30c.Solution.fPoly_mul_gPoly := rfl
example : @Prob30c.not_isNAbsorbing_polyExt_A_succ_q
    = @Prob30c.Solution.not_isNAbsorbing_polyExt_A_succ_q := rfl
example : @Prob30c.isNAbsorbing_A_succ_q = @Prob30c.Solution.isNAbsorbing_A_succ_q := rfl
example : @Prob30c.isNAbsorbing_polyExt_A_succ_succ_q
    = @Prob30c.Solution.isNAbsorbing_polyExt_A_succ_succ_q := rfl
example : @Prob30c.omegaAbs_A = @Prob30c.Solution.omegaAbs_A := rfl
example : @Prob30c.omegaAbs_polyExt_A = @Prob30c.Solution.omegaAbs_polyExt_A := rfl
example : @Prob30c.gap_family = @Prob30c.Solution.gap_family := rfl
example : @Prob30c.polyAbsorbingConj_false = @Prob30c.Solution.polyAbsorbingConj_false := rfl

end Prob30c
