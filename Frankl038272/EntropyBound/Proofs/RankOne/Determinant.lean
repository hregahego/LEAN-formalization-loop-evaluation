/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.RankOne.Bernstein

/-!
# Stage C · C5 — the determinant factorization

`SKETCH.md` Step 3 (3c) / `BLUEPRINT.md` Stage C, item C5.

The `2 × 2` "determinant"
`[q(s,t)(1-q(s,t))]² - q(s,s)(1-q(s,s)) q(t,t)(1-q(t,t))`
factors exactly as `s² t² (s-t)² R(s,t)`.  This is a polynomial identity valid for **all**
real `s, t` — no interval hypothesis is used or needed.  The proof rewrites `Rpoly` into the
power basis with `Rpoly_power_basis` (#24) first, so `ring` never has to see `bern`.
-/

namespace EntropyBound

/-- Frozen theorem #25 (`Rpoly_determinant_identity`). -/
theorem Rpoly_determinant_identity_proof :
    ∀ s t : ℝ, (qker s t * (1 - qker s t)) ^ 2
      - qker s s * (1 - qker s s) * (qker t t * (1 - qker t t))
      = s ^ 2 * t ^ 2 * (s - t) ^ 2 * Rpoly s t := by
  intro s t
  rw [Rpoly_power_basis_proof s t]
  simp only [qker]
  ring

end EntropyBound

namespace EntropyBound.Solution

/-- Frozen theorem #25, restated verbatim. -/
theorem Rpoly_determinant_identity :
    ∀ s t : ℝ, (qker s t * (1 - qker s t)) ^ 2
      - qker s s * (1 - qker s s) * (qker t t * (1 - qker t t))
      = s ^ 2 * t ^ 2 * (s - t) ^ 2 * Rpoly s t :=
  EntropyBound.Rpoly_determinant_identity_proof

end EntropyBound.Solution

example :
    @EntropyBound.Rpoly_determinant_identity
      = @EntropyBound.Solution.Rpoly_determinant_identity := rfl
