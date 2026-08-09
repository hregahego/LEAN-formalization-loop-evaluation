/-
# Stage G — the headline (`Prob20/Proofs/Headline/`)

Assembly of the frozen headline theorem #17: for every `n : ℕ` (i.e. every
`n ≥ 2` under the frozen `n + 2` rendering), the canonical map
`θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is **neither injective nor surjective**.

Nothing is re-proved here.  The two halves are the frozen statements #14 and
#16, already proved elsewhere:

* `Prob20.theta_not_injective_proof`  (`Prob20/Proofs/Injectivity/Basic.lean`),
* `Prob20.theta_not_surjective_proof` (`Prob20/Proofs/Surjectivity/Basic.lean`).
-/
import Prob20.Defs
import Prob20.Proofs.Injectivity.Basic
import Prob20.Proofs.Surjectivity.Basic

open scoped TensorProduct

namespace Prob20

/-- **#17 — HEADLINE.** For the explicit domain `D = 𝔽₂ + t(t+1)T` and every `n ≥ 2`,
the canonical map `θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is neither injective nor surjective.

Statement copied verbatim from `Prob20/Theorems.lean:82-84`; the proof is the pair
of the frozen #14 and #16, for the *same* arbitrary `n`. -/
theorem theta_not_injective_not_surjective_proof :
    ∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n + 2)) ∧
      ∃ F ∈ IntDn (n + 2), F ∉ LinearMap.range (theta ↥Dom K (n + 2)) :=
  fun n => ⟨Prob20.theta_not_injective_proof n, Prob20.theta_not_surjective_proof n⟩

end Prob20
