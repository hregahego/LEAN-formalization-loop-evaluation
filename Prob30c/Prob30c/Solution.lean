/-
`Prob30c.Solution` — the 15 frozen theorems restated verbatim under clean names.

Each declaration must end up as `:= <name>_proof`, the sorry-free declaration
produced in `Prob30c/Proofs/**`.  Until a stage delivers that proof the
declaration below simply forwards to the frozen (still `sorry`) statement in
`Prob30c.Theorems`, which is exactly what `scripts/verify.py` check 4 detects:
`#print axioms Prob30c.Solution.<name>` then reports `sorryAx`.

Replacing `Prob30c.<name>` by `<name>_proof` on the right-hand side is the ONLY
edit a worker makes here.
-/
import Prob30c.Theorems
import Prob30c.Proofs.Absorbing.Basic
import Prob30c.Proofs.Model.Basic
import Prob30c.Proofs.Cancellation.Basic
import Prob30c.Proofs.Witnesses.Basic
import Prob30c.Proofs.Bound.Basic
import Prob30c.Proofs.Transfer.Basic
import Prob30c.Proofs.Headline.Basic

namespace Prob30c.Solution

open Polynomial Finset

theorem mem_polyExt_iff {R : Type*} [CommRing R] (I : Ideal R) (p : Polynomial R) :
    p ∈ polyExt I ↔ ∀ n, p.coeff n ∈ I :=
  Prob30c.mem_polyExt_iff_proof I p

theorem isNAbsorbing_succ {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (h : IsNAbsorbing I n) : IsNAbsorbing I (n + 1) :=
  Prob30c.isNAbsorbing_succ_proof I n h

theorem Jid_pow_three_eq_bot (q : ℕ) : (Jid Dbase tD q) ^ 3 = ⊥ :=
  Prob30c.Jid_pow_three_eq_bot_proof q

theorem Jid_sq_eq_Wid (q : ℕ) : (Jid Dbase tD q) ^ 2 = Wid Dbase tD q :=
  Prob30c.Jid_sq_eq_Wid_proof q

theorem isNoetherianRing_A (q : ℕ) : IsNoetherianRing (A q) :=
  Prob30c.isNoetherianRing_A_proof q

theorem s_component_cancellation (q : ℕ) (x y : A q)
    (hx : x ∈ Jid Dbase tD q) (hy : y ∈ Jid Dbase tD q)
    (h : x * y ∈ Ideal.span {sElt q}) :
    x * y ∈ Ideal.span {tElt q * sElt q} :=
  Prob30c.s_component_cancellation_proof q x y hx hy h

theorem not_isNAbsorbing_A_q (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (⊥ : Ideal (A q)) q :=
  Prob30c.not_isNAbsorbing_A_q_proof q hq

theorem fPoly_mul_gPoly (q : ℕ) :
    fPoly q * gPoly q = C (sElt q) * (X + X ^ 2) :=
  Prob30c.fPoly_mul_gPoly_proof q

theorem not_isNAbsorbing_polyExt_A_succ_q (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (polyExt (⊥ : Ideal (A q))) (q + 1) :=
  Prob30c.not_isNAbsorbing_polyExt_A_succ_q_proof q hq

theorem isNAbsorbing_A_succ_q (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (⊥ : Ideal (A q)) (q + 1) :=
  Prob30c.isNAbsorbing_A_succ_q_proof q hq

theorem isNAbsorbing_polyExt_A_succ_succ_q (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (polyExt (⊥ : Ideal (A q))) (q + 2) :=
  Prob30c.isNAbsorbing_polyExt_A_succ_succ_q_proof q hq

theorem omegaAbs_A (q : ℕ) (hq : 2 ≤ q) : omegaAbs (⊥ : Ideal (A q)) = q + 1 :=
  Prob30c.omegaAbs_A_proof q hq

theorem omegaAbs_polyExt_A (q : ℕ) (hq : 2 ≤ q) :
    omegaAbs (polyExt (⊥ : Ideal (A q))) = q + 2 :=
  Prob30c.omegaAbs_polyExt_A_proof q hq

theorem gap_family (n : ℕ) (hn : 3 ≤ n) :
    IsNoetherianRing (A (n - 1)) ∧
      omegaAbs (⊥ : Ideal (A (n - 1))) = n ∧
      omegaAbs (polyExt (⊥ : Ideal (A (n - 1)))) = n + 1 :=
  Prob30c.gap_family_proof n hn

theorem polyAbsorbingConj_false : ¬ PolyAbsorbingConj :=
  Prob30c.polyAbsorbingConj_false_proof

end Prob30c.Solution
