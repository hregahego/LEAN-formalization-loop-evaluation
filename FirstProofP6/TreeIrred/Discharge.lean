import TreeIrred.Solution

/-!
# Discharge — machine-checked no-drift gate

For each frozen theorem of `TreeIrred/Theorems.lean` and its sorry-free
counterpart in `TreeIrred/Proofs/**`, this module records

```
example : @TreeIrred.<name> = @<name>_proof := rfl
```

which type-checks **iff** the proof has exactly the frozen proposition.

A gate may only be added once its `<name>_proof` exists.  All thirteen frozen
names now have one, so all 24 gates (two per name) are live below.
-/

namespace TreeIrred

-- 1 · `form_gram_entries`
example : @TreeIrred.form_gram_entries = @TreeIrred.form_gram_entries_proof := rfl
example : @TreeIrred.form_gram_entries = @TreeIrred.Solution.form_gram_entries := rfl

-- 2 · `norm_one_irreducible`
example : @TreeIrred.norm_one_irreducible = @TreeIrred.norm_one_irreducible_proof := rfl
example : @TreeIrred.norm_one_irreducible = @TreeIrred.Solution.norm_one_irreducible := rfl

-- 3 · `capacity_node_formula`
example : @TreeIrred.capacity_node_formula = @TreeIrred.capacity_node_formula_proof := rfl
example : @TreeIrred.capacity_node_formula = @TreeIrred.Solution.capacity_node_formula := rfl

-- 4 · `capacity_denom_pos`
example : @TreeIrred.capacity_denom_pos = @TreeIrred.capacity_denom_pos_proof := rfl
example : @TreeIrred.capacity_denom_pos = @TreeIrred.Solution.capacity_denom_pos := rfl

-- 5 · `capacity_pos`
example : @TreeIrred.capacity_pos = @TreeIrred.capacity_pos_proof := rfl
example : @TreeIrred.capacity_pos = @TreeIrred.Solution.capacity_pos := rfl

-- 6 · `capacity_lt_one`
example : @TreeIrred.capacity_lt_one = @TreeIrred.capacity_lt_one_proof := rfl
example : @TreeIrred.capacity_lt_one = @TreeIrred.Solution.capacity_lt_one := rfl

-- 7 · `capacity_spec`
example : @TreeIrred.capacity_spec = @TreeIrred.capacity_spec_proof := rfl
example : @TreeIrred.capacity_spec = @TreeIrred.Solution.capacity_spec := rfl

-- 8 · `admissible_posDef`
example : @TreeIrred.admissible_posDef = @TreeIrred.admissible_posDef_proof := rfl
example : @TreeIrred.admissible_posDef = @TreeIrred.Solution.admissible_posDef := rfl

-- 9 · `rooted_estimate`
example : @TreeIrred.rooted_estimate = @TreeIrred.rooted_estimate_proof := rfl
example : @TreeIrred.rooted_estimate = @TreeIrred.Solution.rooted_estimate := rfl

-- 10 · `admissible_root_bound`
example : @TreeIrred.admissible_root_bound = @TreeIrred.admissible_root_bound_proof := rfl
example : @TreeIrred.admissible_root_bound = @TreeIrred.Solution.admissible_root_bound := rfl

-- 11 · `exists_reroot_at`
example : @TreeIrred.exists_reroot_at = @TreeIrred.exists_reroot_at_proof := rfl
example : @TreeIrred.exists_reroot_at = @TreeIrred.Solution.exists_reroot_at := rfl

-- 12 · `pointed_root_irreducible`
example : @TreeIrred.pointed_root_irreducible = @TreeIrred.pointed_root_irreducible_proof := rfl
example : @TreeIrred.pointed_root_irreducible = @TreeIrred.Solution.pointed_root_irreducible := rfl

-- 13 · `tree_has_irreducible_vertex`
example :
    @TreeIrred.tree_has_irreducible_vertex = @TreeIrred.tree_has_irreducible_vertex_proof := rfl
example :
    @TreeIrred.tree_has_irreducible_vertex = @TreeIrred.Solution.tree_has_irreducible_vertex := rfl

end TreeIrred
