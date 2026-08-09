import Erdos477.Solution

/-!
# Discharge — machine-checked no-drift gates

For every frozen theorem of `Erdos477/Theorems.lean` and its restatement in
`Erdos477/Solution.lean`, this file contains

```
example : @Erdos477.<name> = @Erdos477.Solution.<name> := rfl
```

which type-checks **iff** the proved declaration has *exactly* the frozen
proposition. `scripts/verify.py` (check 5b) regenerates these gates itself, so
they are duplicated here only as a fast local signal.

Sixteen gates — one for every frozen statement, all Stages A through G. None is
missing: every frozen name now has a sorry-free `Erdos477.Solution.*`
counterpart bound to it by `rfl` here.
-/

namespace Erdos477

-- ===== Stage A — elementary layer =====

example : @Erdos477.zero_mem_Bset = @Erdos477.Solution.zero_mem_Bset := rfl

example : @Erdos477.Dset_neg_mem = @Erdos477.Solution.Dset_neg_mem := rfl

example : @Erdos477.pow13_inj = @Erdos477.Solution.pow13_inj := rfl

example : @Erdos477.mem_Bset_of_rat_pow13 = @Erdos477.Solution.mem_Bset_of_rat_pow13 := rfl

example : @Erdos477.sub_pow13_mem_Dset_iff = @Erdos477.Solution.sub_pow13_mem_Dset_iff := rfl

-- ===== Stage B — the cofactor bound =====

example : @Erdos477.Qcof_ge_half_max_pow12 = @Erdos477.Solution.Qcof_ge_half_max_pow12 := rfl

example : @Erdos477.abs_pow13_sub_pow13_ge = @Erdos477.Solution.abs_pow13_sub_pow13_ge := rfl

-- ===== Stage C — function-field exclusion, Route A =====

example : @Erdos477.bm_forms_height_bound = @Erdos477.Solution.bm_forms_height_bound := rfl

example : @Erdos477.no_nonconstant_param_of_not_pow13 =
    @Erdos477.Solution.no_nonconstant_param_of_not_pow13 := rfl

example : @Erdos477.no_rational_param_of_not_mem_Bset =
    @Erdos477.Solution.no_rational_param_of_not_mem_Bset := rfl

example : @Erdos477.no_linear_param = @Erdos477.Solution.no_linear_param := rfl

-- ===== Stage D — the Heath-Brown bridge =====

example : @Erdos477.hb_diagonal_count = @Erdos477.Solution.hb_diagonal_count := rfl

-- ===== Stage E — the bad-shift estimate =====

example : @Erdos477.badShift_bound = @Erdos477.Solution.badShift_bound := rfl

-- ===== Stage F — the greedy tiling criterion =====

example : @Erdos477.greedy_tiling = @Erdos477.Solution.greedy_tiling := rfl

-- ===== Stage G — assembly =====

example : @Erdos477.good_shift_exists = @Erdos477.Solution.good_shift_exists := rfl

example : @Erdos477.erdos_477 = @Erdos477.Solution.erdos_477 := rfl

end Erdos477
