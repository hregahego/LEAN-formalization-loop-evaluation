/-
# Prob20 — no-drift gate

For every frozen theorem, this module contains

```lean
example : @Prob20.<name> = @Prob20.Solution.<name> := rfl
```

which type-checks **iff** the proved declaration has *exactly* the frozen
proposition.  `scripts/verify.py` additionally generates the same gates itself,
so an omission here is detected.

Iteration 2: gates for the five discharged frozen theorems #1, #2, #4, #5, #6.
Iteration 3: gates for #3, #7, #8, #9, #10, #11, #12, #13 as well.
Iteration 4: gates for #14, #15, #16, #17 — all 17 frozen theorems are now gated.
-/
import Prob20.Solution

namespace Prob20

example : @Prob20.D_isDomain = @Prob20.Solution.D_isDomain := rfl

example : @Prob20.mem_Dom_iff_mem_max_or_sub_one_mem_max
    = @Prob20.Solution.mem_Dom_iff_mem_max_or_sub_one_mem_max := rfl

example : @Prob20.D_isFractionRing = @Prob20.Solution.D_isFractionRing := rfl

example : @Prob20.theta_apply_tprod = @Prob20.Solution.theta_apply_tprod := rfl

example : @Prob20.theta_mem_intMv = @Prob20.Solution.theta_mem_intMv := rfl

example : @Prob20.D_isLocalRing = @Prob20.Solution.D_isLocalRing := rfl

example : @Prob20.p_eval_mem_max = @Prob20.Solution.p_eval_mem_max := rfl

example : @Prob20.smul_p_mem_int = @Prob20.Solution.smul_p_mem_int := rfl

example : @Prob20.g_mem_int = @Prob20.Solution.g_mem_int := rfl

example : @Prob20.bigP_mem_intMv = @Prob20.Solution.bigP_mem_intMv := rfl

example : @Prob20.p_not_mem_max_int = @Prob20.Solution.p_not_mem_max_int := rfl

example : @Prob20.t_mul_p_not_mem_max_int = @Prob20.Solution.t_mul_p_not_mem_max_int := rfl

example : @Prob20.t_add_one_mul_p_not_mem_max_int
    = @Prob20.Solution.t_add_one_mul_p_not_mem_max_int := rfl

example : @Prob20.theta_not_injective = @Prob20.Solution.theta_not_injective := rfl

example : @Prob20.bigP_not_mem_range = @Prob20.Solution.bigP_not_mem_range := rfl

example : @Prob20.theta_not_surjective = @Prob20.Solution.theta_not_surjective := rfl

example : @Prob20.theta_not_injective_not_surjective
    = @Prob20.Solution.theta_not_injective_not_surjective := rfl

end Prob20
