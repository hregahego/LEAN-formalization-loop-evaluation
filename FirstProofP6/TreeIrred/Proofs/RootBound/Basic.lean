import TreeIrred.Proofs.Model.Basic
import TreeIrred.Proofs.Capacity.Basic
import TreeIrred.Proofs.PosDef.Basic
import TreeIrred.Proofs.RootedEstimate.Basic

/-!
# Stage F -- Corollary 1 (`admissible_root_bound`)

`SKETCH.md` Corollary 1: for an admissible rooted tree `C` and a lattice vector
`x` that is nonzero on `verts C`, the *strict* bound `x^2 - x_rho > 0` holds.

The informal proof runs through the dual vector `rho^#` and Cauchy's
inequality.  We take the (equivalent, and cheaper) route sanctioned by
`BLUEPRINT.md` Part 2 Stage F: a case split on the sign of `x C.root`, using
`admissible_posDef` when `x C.root <= 0` and `rooted_estimate` at `k = 1`
together with `gamma C < 1` when `1 <= x C.root`.  The frozen statement is
untouched and the strictness is genuine in both cases.
-/

namespace TreeIrred

namespace RootBound

/-- The `1 ≤ x C.root` half of Corollary 1, done entirely in `ℚ`: the rooted
estimate at `k = 1` says `Bq ≥ 3 * r - 2 * g`, and `g < 1`, `1 ≤ r` turn that
into `r < Bq`.  Stated abstractly so the cast bookkeeping stays in one place. -/
theorem lt_of_estimate {Bq r g : ℚ} (hre : 0 ≤ Bq - 3 * r + g * 2) (hg : g < 1)
    (hr : 1 ≤ r) : r < Bq := by
  linarith

end RootBound

/-- Frozen theorem #10 (`TreeIrred/Theorems.lean:53-54`), `SKETCH.md`
Corollary 1: an admissible rooted tree satisfies the *strict* root bound
`0 < B C x x - x C.root` for every `x` that is nonzero somewhere on `verts C`.
Both cases are genuinely proved: `x C.root ≤ 0` uses positive definiteness
(`admissible_posDef_proof`) and `1 ≤ x C.root` uses the rooted estimate at
`k = 1` (`rooted_estimate_proof`) together with `gamma C < 1`
(`capacity_lt_one_proof`). -/
theorem admissible_root_bound_proof (C : RTree) (hC : Admissible C)
    (x : ℕ → ℤ) (hx : NonzeroOn C x) : 0 < B C x x - x C.root := by
  rcases le_or_gt (x C.root) 0 with hroot | hroot
  · -- F1: positive definiteness already gives `0 < B C x x`.
    have hpd : 0 < B C x x := admissible_posDef_proof C hC x hx
    omega
  · -- F2: `1 ≤ x C.root`; run the rooted estimate at `k = 1`.
    have hre := rooted_estimate_proof C hC x 1
    have hg : gamma C < 1 := capacity_lt_one_proof C hC
    have hr : (1 : ℚ) ≤ ((x C.root : ℤ) : ℚ) := by exact_mod_cast hroot
    push_cast at hre
    have hq : ((x C.root : ℤ) : ℚ) < ((B C x x : ℤ) : ℚ) :=
      RootBound.lt_of_estimate (by linarith) hg hr
    have hz : x C.root < B C x x := by exact_mod_cast hq
    omega

/-! ### Guardrails (per TASKS R4: `norm_num`, never `decide`) -/

/-- The concrete path `0 — 1 — 2`, all weights `2`. -/
private def PF : RTree := .node 0 2 [.node 1 2 [.node 2 2 []]]

private theorem PF_admissible : Admissible PF := by
  norm_num [PF, Admissible]

/-- The theorem is non-vacuous: it applies to `PF` at the nonzero vector
`basis 0`. -/
example : 0 < B PF (basis 0) (basis 0) - basis 0 PF.root :=
  admissible_root_bound_proof PF PF_admissible (basis 0)
    ⟨0, by norm_num [PF], by norm_num [basis]⟩

/-- ... and the bound it yields there is the true one: `B = 2`, `x_ρ = 1`. -/
example : B PF (basis 0) (basis 0) - basis 0 PF.root = 1 := by
  norm_num [PF, form, basis, RTree.root]

end TreeIrred
