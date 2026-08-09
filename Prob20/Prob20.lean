/-
# Prob20 — root import module

Problem 20 (Cahen–Fontana–Frisch–Glaz): for the explicit domain
`D = 𝔽₂ + t(t+1)·T ⊆ 𝔽₂(t)` and every `n ≥ 2`, the canonical map
`θₙ : Int(D)^{⊗ₙ} → Int(Dⁿ)` is neither injective nor surjective.
-/
import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac
import Prob20.Proofs.Domain.Local
import Prob20.Proofs.Theta.Basic
import Prob20.Proofs.Theta.MemIntMv
import Prob20.Proofs.KeyPolys.Basic
import Prob20.Proofs.Vanishing.Basic
import Prob20.Proofs.Injectivity.Basic
import Prob20.Proofs.Surjectivity.Basic
import Prob20.Proofs.Headline.Basic
import Prob20.Solution
import Prob20.Discharge
