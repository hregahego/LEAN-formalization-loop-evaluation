/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.IndepCoupling.Bound

/-!
# Stage J — the independent coupling bound (`SKETCH.md` Step 10)

This file contains BLUEPRINT Stage J item J1, the support statement for the independent
coupling: if the product weight `windW G p` is nonzero then both coordinates of `p` lie in
`G`, so union-closedness puts `orVec p.1 p.2` in `G` as well.

All declarations belong to `namespace EntropyBound`; support lemmas live in
`namespace EntropyBound.IndepCoupling`.
-/

namespace EntropyBound

namespace IndepCoupling

/-- The uniform weight vanishes off `G`. -/
lemma mem_of_unifW_ne_zero {n : ℕ} {G : Finset (Fin n → Bool)} {x : Fin n → Bool}
    (hx : unifW G x ≠ 0) : x ∈ G := by
  by_contra h
  exact hx (by simp [unifW, h])

end IndepCoupling

/-! ### Frozen theorem #54 — the support of the independent coupling -/

theorem indep_support_mem_proof {n : ℕ} (G : Finset (Fin n → Bool)) (hG : UnionClosedCube G) :
    ∀ p, windW G p ≠ 0 → orVec p.1 p.2 ∈ G := by
  intro p hp
  simp only [windW] at hp
  have h1 : unifW G p.1 ≠ 0 := fun h => hp (by rw [h, zero_mul])
  have h2 : unifW G p.2 ≠ 0 := fun h => hp (by rw [h, mul_zero])
  exact hG p.1 (IndepCoupling.mem_of_unifW_ne_zero h1) p.2
    (IndepCoupling.mem_of_unifW_ne_zero h2)

namespace Solution

theorem indep_support_mem {n : ℕ} (G : Finset (Fin n → Bool)) (hG : UnionClosedCube G) :
    ∀ p, windW G p ≠ 0 → orVec p.1 p.2 ∈ G :=
  EntropyBound.indep_support_mem_proof G hG

end Solution

example : @EntropyBound.indep_support_mem = @EntropyBound.Solution.indep_support_mem := rfl

end EntropyBound
