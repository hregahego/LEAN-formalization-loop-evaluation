/-
Stage E -- the generic irredundant-length upper bound (E1-E7).

The whole file works at the *generic* base `(B, τ, q)` with `[IsDomain B]` and
`Prime τ`, and only the very last theorem specialises to `B = Dbase`, `τ = tD`.

The characteristic-2 cancellation of Stage C enters **only** as the explicit
hypothesis `hcanc` of `irredundant_len_le_of_hcanc`: it is FALSE at the base
`B = Polynomial Dbase`, `τ = Polynomial.C tD` (proved: `hcanc_polyDbase_false`),
and Stage F instantiates the `hcanc`-free bound `irredundant_len_le_generic`
at exactly that base.
-/
import Prob30c.Proofs.Absorbing.Basic
import Prob30c.Proofs.Model.Basic
import Prob30c.Proofs.Cancellation.Basic

namespace Prob30c

open Finset

variable {B : Type} [CommRing B] {τ : B} {q : ℕ}

/-! ## E0 — small support lemmas about the `s`-line and about `B ⧸ (τ^q)` -/

/-- Vanishing in `B ⧸ (τ^q)` is divisibility by `τ^q`. -/
theorem quo_mk_eq_zero_iff (b : B) :
    (Ideal.Quotient.mk (Ideal.span {τ ^ q}) b : Quo B τ q) = 0 ↔ τ ^ q ∣ b := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- An element whose only possibly-nonzero coordinate is the `s`-coordinate lies
on the `s`-line `B · s`. -/
theorem eq_algebraMap_mul_sElt {x : Alg B τ q} {b : B} (h0 : x.fst = 0)
    (h1 : Alg.α₁ x = 0) (h2 : Alg.α₂ x = 0) (h3 : Alg.α₃ x = 0)
    (h4 : Alg.γ₁ x = 0) (h5 : Alg.γ₂ x = 0)
    (h6 : Alg.σ x = Ideal.Quotient.mk (Ideal.span {τ ^ q}) b) :
    x = algebraMap B (Alg B τ q) b * Alg.sElt B τ q := by
  refine Alg.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [h0, h1, h2, h3, h4, h5, h6]

/-- Scalars slide into the `s`-line. -/
theorem smul_algebraMap_mul_sElt (c b : B) :
    c • (algebraMap B (Alg B τ q) b * Alg.sElt B τ q)
      = algebraMap B (Alg B τ q) (c * b) * Alg.sElt B τ q := by
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul]

/-- An element of the `s`-line vanishes exactly when `τ^q` divides its
coefficient. -/
theorem algebraMap_mul_sElt_eq_zero_iff_dvd (b : B) :
    algebraMap B (Alg B τ q) b * Alg.sElt B τ q = 0 ↔ τ ^ q ∣ b := by
  rw [Alg.algebraMap_mul_sElt_eq_zero_iff, quo_mk_eq_zero_iff]

/-! ## E1 — the `fst` of a product -/

/-- `Unitization.fst` is a ring hom, so it commutes with finite products. -/
theorem fst_prod {ι : Type*} (S : Finset ι) (a : ι → Alg B τ q) :
    (∏ i ∈ S, a i).fst = ∏ i ∈ S, (a i).fst :=
  map_prod (Unitization.fstHom B (Jmod B τ q)) a S

/-! ## E2 — three factors in `J` kill a product -/

/-- Multiplying an element of `W` by anything only rescales it by the scalar
part of the other factor: `w * x = x.fst • w`. -/
theorem Wid_mul_eq_smul {w x : Alg B τ q} (hw : w ∈ Wid B τ q) :
    w * x = x.fst • w := by
  have hfst : (x - algebraMap B (Alg B τ q) x.fst).fst
      = x.fst - (algebraMap B (Alg B τ q) x.fst).fst :=
    map_sub (Unitization.fstHom B (Jmod B τ q)) _ _
  have hj : x - algebraMap B (Alg B τ q) x.fst ∈ Jid B τ q :=
    Alg.mem_Jid_iff.2 (by rw [hfst, Alg.fst_algebraMap, sub_self])
  have h1 : w * x - w * algebraMap B (Alg B τ q) x.fst = 0 := by
    rw [← mul_sub]; exact Alg.Wid_mul_Jid hw hj
  rw [sub_eq_zero.1 h1, mul_comm, ← Algebra.smul_def]

/-- The same, for a whole finite product of factors. -/
theorem Wid_mul_prod_eq_smul {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (a : ι → Alg B τ q) :
    ∀ {w : Alg B τ q}, w ∈ Wid B τ q →
      w * ∏ i ∈ T, a i = (∏ i ∈ T, (a i).fst) • w := by
  classical
  induction T using Finset.induction with
  | empty => intro w _; simp
  | insert j T hj ih =>
      intro w hw
      have hsmul : (a j).fst • w ∈ Wid B τ q := by
        rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hw
      rw [Finset.prod_insert hj, Finset.prod_insert hj, ← mul_assoc,
        Wid_mul_eq_smul hw, ih hsmul, smul_smul, mul_comm]

/-- **E2.** A product over a finset containing three distinct `J`-indices
vanishes (`J³ = 0`). -/
theorem prod_eq_zero_of_three_J {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {a : ι → Alg B τ q} {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (h23 : i₂ ≠ i₃) (hm1 : i₁ ∈ S) (hm2 : i₂ ∈ S) (hm3 : i₃ ∈ S)
    (hJ1 : a i₁ ∈ Jid B τ q) (hJ2 : a i₂ ∈ Jid B τ q) (hJ3 : a i₃ ∈ Jid B τ q) :
    ∏ i ∈ S, a i = 0 := by
  have hm2' : i₂ ∈ S.erase i₁ := Finset.mem_erase.2 ⟨h12.symm, hm2⟩
  have hm3' : i₃ ∈ (S.erase i₁).erase i₂ :=
    Finset.mem_erase.2 ⟨h23.symm, Finset.mem_erase.2 ⟨h13.symm, hm3⟩⟩
  rw [← Finset.mul_prod_erase S a hm1, ← Finset.mul_prod_erase _ a hm2',
    ← Finset.mul_prod_erase _ a hm3', ← mul_assoc, ← mul_assoc,
    Alg.Wid_mul_Jid (Alg.mul_mem_Wid hJ1 hJ2) hJ3, zero_mul]

/-! ## E3 — the collapse lemmas -/

/-- **E3 (two `J`-factors).** A product over a finset containing two distinct
`J`-indices collapses to a scalar multiple of the product of those two
factors. -/
theorem prod_eq_smul_of_two_J {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {a : ι → Alg B τ q} {i₁ i₂ : ι} (h12 : i₁ ≠ i₂) (hm1 : i₁ ∈ S) (hm2 : i₂ ∈ S)
    (hJ1 : a i₁ ∈ Jid B τ q) (hJ2 : a i₂ ∈ Jid B τ q) :
    ∏ i ∈ S, a i
      = (∏ i ∈ (S.erase i₁).erase i₂, (a i).fst) • (a i₁ * a i₂) := by
  have hm2' : i₂ ∈ S.erase i₁ := Finset.mem_erase.2 ⟨h12.symm, hm2⟩
  rw [← Finset.mul_prod_erase S a hm1, ← Finset.mul_prod_erase _ a hm2',
    ← mul_assoc]
  exact Wid_mul_prod_eq_smul _ a (Alg.mul_mem_Wid hJ1 hJ2)

/-- **E3 (one `J`-factor).** A product over a finset one of whose factors lies
in `W` collapses to a scalar multiple of that factor. -/
theorem prod_eq_smul_of_one_J {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {a : ι → Alg B τ q} {i₁ : ι} (hm1 : i₁ ∈ S) (hW : a i₁ ∈ Wid B τ q) :
    ∏ i ∈ S, a i = (∏ i ∈ S.erase i₁, (a i).fst) • a i₁ := by
  rw [← Finset.mul_prod_erase S a hm1]
  exact Wid_mul_prod_eq_smul _ a hW

/-! ## E4/E5 — the valuation core

Both Case 2 and Case 3 end in the same elementary divisibility argument, which is
isolated here.  `N` is the set of factors *outside* `J`, `d i` their scalar parts,
`b` the coefficient of the surviving `s`-line element, and `τ ^ e` a divisor of
`b` known in advance (`e = 1` in Case 2 under `hcanc`, `e = 0` otherwise).

Only prime divisibility is used — no `multiplicity` / valuation API. -/

theorem card_add_le_of_prime_dvd {B : Type} [CommRing B] [IsDomain B] {τ : B}
    (hτ : Prime τ) {q : ℕ} {ι : Type*} [DecidableEq ι] {N : Finset ι} {d : ι → B}
    {b : B} {e : ℕ} (hzero : τ ^ q ∣ (∏ i ∈ N, d i) * b)
    (hne : ∀ i ∈ N, ¬ τ ^ q ∣ (∏ k ∈ N.erase i, d k) * b)
    (hb : τ ^ e ∣ b) (hN : N.Nonempty) :
    N.card + e ≤ q := by
  have hdvd : ∀ i ∈ N, τ ∣ d i := by
    intro i hi
    by_contra hcon
    refine hne i hi ?_
    have hsplit : (∏ k ∈ N, d k) * b = d i * ((∏ k ∈ N.erase i, d k) * b) := by
      rw [← Finset.mul_prod_erase N d hi, mul_assoc]
    rw [hsplit] at hzero
    exact hτ.pow_dvd_of_dvd_mul_left q hcon hzero
  obtain ⟨i₀, hi₀⟩ := hN
  have hconst : τ ^ (N.erase i₀).card = ∏ _k ∈ N.erase i₀, τ :=
    (Finset.prod_const τ).symm
  have hpow : τ ^ (N.erase i₀).card ∣ ∏ k ∈ N.erase i₀, d k := by
    rw [hconst]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun k hk => hdvd k (Finset.mem_of_mem_erase hk)
  have hfull : τ ^ ((N.erase i₀).card + e) ∣ (∏ k ∈ N.erase i₀, d k) * b := by
    rw [pow_add]; exact mul_dvd_mul hpow hb
  by_contra hcon
  have hc : (N.erase i₀).card = N.card - 1 := Finset.card_erase_of_mem hi₀
  have hpos : 1 ≤ N.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
  have hle : q ≤ (N.erase i₀).card + e := by omega
  exact hne i₀ hi₀ (dvd_trans (pow_dvd_pow τ hle) hfull)

/-! ## E4 — Case 2: exactly two factors lie in `J`

The cancellation enters only through the hypothesis `hcanc`, in the `τ ^ e`-graded
form: `e = 1` when Stage C is available (giving `m ≤ q + 1`), `e = 0` otherwise
(giving `m ≤ q + 2`). -/

theorem case_two_bound {B : Type} [CommRing B] [IsDomain B] {τ : B} (hτ : Prime τ)
    {q m : ℕ} (a : Fin m → Alg B τ q) {i₁ i₂ : Fin m} (h12 : i₁ ≠ i₂)
    (hJ1 : (a i₁).fst = 0) (hJ2 : (a i₂).fst = 0)
    (hother : ∀ i, i ≠ i₁ → i ≠ i₂ → (a i).fst ≠ 0)
    (h0 : ∏ i, a i = 0) (hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0)
    {e : ℕ} (hqe : e ≤ q)
    (hcanc : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : B, a₂ * b₃ + a₃ * b₂ + a₃ * b₃ = 0 →
      a₁ * b₃ + a₃ * b₁ + a₂ * b₂ = 0 → τ ^ e ∣ (a₁ * b₃ + a₃ * b₁)) :
    m + e ≤ q + 2 := by
  classical
  set x := a i₁ with hxdef
  set y := a i₂ with hydef
  set N : Finset (Fin m) := (Finset.univ.erase i₁).erase i₂ with hNdef
  have hJ1' : x ∈ Jid B τ q := Alg.mem_Jid_iff.2 hJ1
  have hJ2' : y ∈ Jid B τ q := Alg.mem_Jid_iff.2 hJ2
  -- the two `J`-factors multiply into `W`
  obtain ⟨hw0, hw1, hw2, hw3⟩ := Alg.mem_Wid_iff.1 (Alg.mul_mem_Wid hJ1' hJ2')
  -- membership in `N` means "different from both `J`-indices"
  have hmemN : ∀ {i : Fin m}, i ∈ N → i ≠ i₁ ∧ i ≠ i₂ := by
    intro i hi
    rw [hNdef, Finset.mem_erase, Finset.mem_erase] at hi
    exact ⟨hi.2.1, hi.1⟩
  have hdne : ∀ i ∈ N, (a i).fst ≠ 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hmemN hi
    exact hother i h1 h2
  have hc : (∏ i ∈ N, (a i).fst) ≠ 0 := Finset.prod_ne_zero_iff.2 hdne
  -- the collapse of the full product
  have hfull : ∏ i, a i = (∏ i ∈ N, (a i).fst) • (x * y) :=
    prod_eq_smul_of_two_J h12 (Finset.mem_univ _) (Finset.mem_univ _) hJ1' hJ2'
  have hcz : (∏ i ∈ N, (a i).fst) • (x * y) = 0 := by rw [← hfull]; exact h0
  -- the two `u`-coordinates vanish, in the domain `B`
  have hg1 : Alg.γ₁ (x * y) = 0 := by
    have h := congrArg Alg.γ₁ hcz
    rw [Alg.γ₁_smul, Alg.γ₁_zero] at h
    exact (mul_eq_zero.1 h).resolve_left hc
  have hg2 : Alg.γ₂ (x * y) = 0 := by
    have h := congrArg Alg.γ₂ hcz
    rw [Alg.γ₂_smul, Alg.γ₂_zero] at h
    exact (mul_eq_zero.1 h).resolve_left hc
  have hu₁ : Alg.α₂ x * Alg.α₃ y + Alg.α₃ x * Alg.α₂ y + Alg.α₃ x * Alg.α₃ y = 0 := by
    rw [Alg.γ₁_mul, hJ1, hJ2] at hg1
    linear_combination hg1
  have hu₂ : Alg.α₁ x * Alg.α₃ y + Alg.α₃ x * Alg.α₁ y + Alg.α₂ x * Alg.α₂ y = 0 := by
    rw [Alg.γ₂_mul, hJ1, hJ2] at hg2
    linear_combination hg2
  -- the surviving `s`-line coefficient, and the cancellation hypothesis
  set b : B := Alg.α₁ x * Alg.α₃ y + Alg.α₃ x * Alg.α₁ y with hbdef
  have hbdvd : τ ^ e ∣ b :=
    hcanc (Alg.α₁ x) (Alg.α₂ x) (Alg.α₃ x) (Alg.α₁ y) (Alg.α₂ y) (Alg.α₃ y) hu₁ hu₂
  have hsig : Alg.σ (x * y) = Ideal.Quotient.mk (Ideal.span {τ ^ q}) b := by
    rw [Alg.σ_mul, hJ1, hJ2, zero_smul, zero_smul, zero_add, zero_add]
  have hxy : x * y = algebraMap B (Alg B τ q) b * Alg.sElt B τ q :=
    eq_algebraMap_mul_sElt hw0 hw1 hw2 hw3 hg1 hg2 hsig
  -- every `erase j` product, for `j` outside `J`, is on the `s`-line
  have hprodj : ∀ j ∈ N, ∏ i ∈ Finset.univ.erase j, a i
      = algebraMap B (Alg B τ q) ((∏ i ∈ N.erase j, (a i).fst) * b)
        * Alg.sElt B τ q := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := hmemN hj
    have hm1 : i₁ ∈ Finset.univ.erase j :=
      Finset.mem_erase.2 ⟨fun h => hj1 h.symm, Finset.mem_univ _⟩
    have hm2 : i₂ ∈ Finset.univ.erase j :=
      Finset.mem_erase.2 ⟨fun h => hj2 h.symm, Finset.mem_univ _⟩
    have herase : ((Finset.univ.erase j).erase i₁).erase i₂ = N.erase j := by
      rw [hNdef, Finset.erase_right_comm (s := (Finset.univ : Finset (Fin m)))
        (a := j) (b := i₁),
        Finset.erase_right_comm (s := (Finset.univ : Finset (Fin m)).erase i₁)
        (a := j) (b := i₂)]
    rw [prod_eq_smul_of_two_J h12 hm1 hm2 hJ1' hJ2', herase, hxy,
      smul_algebraMap_mul_sElt]
  -- the divisibility data fed to the valuation core
  have hzero : τ ^ q ∣ (∏ i ∈ N, (a i).fst) * b := by
    rw [← algebraMap_mul_sElt_eq_zero_iff_dvd, ← smul_algebraMap_mul_sElt, ← hxy,
      ← hfull]
    exact h0
  have hne : ∀ j ∈ N, ¬ τ ^ q ∣ (∏ i ∈ N.erase j, (a i).fst) * b := by
    intro j hj hdvd
    refine hirr j ?_
    rw [hprodj j hj, algebraMap_mul_sElt_eq_zero_iff_dvd]
    exact hdvd
  -- cardinality bookkeeping
  have hm2 : 2 ≤ m := by
    have h1 := i₁.isLt
    have h2 := i₂.isLt
    have hv : i₁.val ≠ i₂.val := fun h => h12 (Fin.ext h)
    omega
  have hcard : N.card = m - 2 := by
    have hmem : i₂ ∈ (Finset.univ : Finset (Fin m)).erase i₁ :=
      Finset.mem_erase.2 ⟨fun h => h12 h.symm, Finset.mem_univ _⟩
    rw [hNdef, Finset.card_erase_of_mem hmem,
      Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ,
      Fintype.card_fin]
    omega
  rcases N.eq_empty_or_nonempty with hN | hN
  · rw [hN, Finset.card_empty] at hcard
    omega
  · have := card_add_le_of_prime_dvd hτ hzero hne hbdvd hN
    omega

/-! ## E5 — Case 3: exactly one factor lies in `J`

Here the cancellation is *not* available and *not* needed: the unique `J`-factor
is forced into the `s`-line by the domain hypothesis alone. -/

theorem case_one_bound {B : Type} [CommRing B] [IsDomain B] {τ : B} (hτ : Prime τ)
    {q m : ℕ} (a : Fin m → Alg B τ q) {i₁ : Fin m} (hJ1 : (a i₁).fst = 0)
    (hother : ∀ i, i ≠ i₁ → (a i).fst ≠ 0) (h0 : ∏ i, a i = 0)
    (hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0) :
    m ≤ q + 1 := by
  classical
  set N : Finset (Fin m) := Finset.univ.erase i₁ with hNdef
  have hdne : ∀ i ∈ N, (a i).fst ≠ 0 := by
    intro i hi
    exact hother i (Finset.mem_erase.1 hi).1
  have hc : (∏ i ∈ N, (a i).fst) ≠ 0 := Finset.prod_ne_zero_iff.2 hdne
  have hsplit : a i₁ * ∏ i ∈ N, a i = 0 := by
    rw [hNdef, Finset.mul_prod_erase _ a (Finset.mem_univ i₁)]
    exact h0
  have hRfst : (∏ i ∈ N, a i).fst = ∏ i ∈ N, (a i).fst := fst_prod N a
  -- the `e`-coordinates of the `J`-factor vanish, so it lies in `W`
  have ha1 : Alg.α₁ (a i₁) = 0 := by
    have h := congrArg Alg.α₁ hsplit
    rw [Alg.α₁_mul, hJ1, Alg.α₁_zero, zero_mul, zero_add, hRfst] at h
    exact (mul_eq_zero.1 h).resolve_left hc
  have ha2 : Alg.α₂ (a i₁) = 0 := by
    have h := congrArg Alg.α₂ hsplit
    rw [Alg.α₂_mul, hJ1, Alg.α₂_zero, zero_mul, zero_add, hRfst] at h
    exact (mul_eq_zero.1 h).resolve_left hc
  have ha3 : Alg.α₃ (a i₁) = 0 := by
    have h := congrArg Alg.α₃ hsplit
    rw [Alg.α₃_mul, hJ1, Alg.α₃_zero, zero_mul, zero_add, hRfst] at h
    exact (mul_eq_zero.1 h).resolve_left hc
  have hW : a i₁ ∈ Wid B τ q := Alg.mem_Wid_iff.2 ⟨hJ1, ha1, ha2, ha3⟩
  -- and so do its `u`-coordinates: it lies on the `s`-line
  have hg1 : Alg.γ₁ (a i₁) = 0 := by
    have h := congrArg Alg.γ₁ hsplit
    rw [Alg.γ₁_mul, hJ1, ha2, ha3, Alg.γ₁_zero, hRfst] at h
    have h' : (∏ i ∈ N, (a i).fst) * Alg.γ₁ (a i₁) = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_left hc
  have hg2 : Alg.γ₂ (a i₁) = 0 := by
    have h := congrArg Alg.γ₂ hsplit
    rw [Alg.γ₂_mul, hJ1, ha1, ha2, ha3, Alg.γ₂_zero, hRfst] at h
    have h' : (∏ i ∈ N, (a i).fst) * Alg.γ₂ (a i₁) = 0 := by linear_combination h
    exact (mul_eq_zero.1 h').resolve_left hc
  obtain ⟨b, hb⟩ :=
    Ideal.Quotient.mk_surjective (I := Ideal.span {τ ^ q}) (Alg.σ (a i₁))
  have hxeq : a i₁ = algebraMap B (Alg B τ q) b * Alg.sElt B τ q :=
    eq_algebraMap_mul_sElt hJ1 ha1 ha2 ha3 hg1 hg2 hb.symm
  have hfull : ∏ i, a i = (∏ i ∈ N, (a i).fst) • a i₁ :=
    prod_eq_smul_of_one_J (Finset.mem_univ _) hW
  have hprodj : ∀ j ∈ N, ∏ i ∈ Finset.univ.erase j, a i
      = algebraMap B (Alg B τ q) ((∏ i ∈ N.erase j, (a i).fst) * b)
        * Alg.sElt B τ q := by
    intro j hj
    have hj1 : j ≠ i₁ := (Finset.mem_erase.1 hj).1
    have hm1 : i₁ ∈ Finset.univ.erase j :=
      Finset.mem_erase.2 ⟨fun h => hj1 h.symm, Finset.mem_univ _⟩
    have herase : (Finset.univ.erase j).erase i₁ = N.erase j := by
      rw [hNdef, Finset.erase_right_comm (s := (Finset.univ : Finset (Fin m)))
        (a := j) (b := i₁)]
    rw [prod_eq_smul_of_one_J hm1 hW, herase, hxeq, smul_algebraMap_mul_sElt]
  have hzero : τ ^ q ∣ (∏ i ∈ N, (a i).fst) * b := by
    rw [← algebraMap_mul_sElt_eq_zero_iff_dvd, ← smul_algebraMap_mul_sElt, ← hxeq,
      ← hfull]
    exact h0
  have hne : ∀ j ∈ N, ¬ τ ^ q ∣ (∏ i ∈ N.erase j, (a i).fst) * b := by
    intro j hj hdvd
    refine hirr j ?_
    rw [hprodj j hj, algebraMap_mul_sElt_eq_zero_iff_dvd]
    exact hdvd
  have hm1 : 1 ≤ m := by
    have := i₁.isLt
    omega
  have hcard : N.card = m - 1 := by
    rw [hNdef, Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ,
      Fintype.card_fin]
  rcases N.eq_empty_or_nonempty with hN | hN
  · rw [hN, Finset.card_empty] at hcard
    omega
  · have hb0 : τ ^ 0 ∣ b := by rw [pow_zero]; exact one_dvd b
    have := card_add_le_of_prime_dvd hτ hzero hne hb0 hN
    omega

/-! ## E2 (continued) — Case 1: at least three factors lie in `J` -/

theorem card_le_three_of_three_J {B : Type} [CommRing B] {τ : B} {q m : ℕ}
    (a : Fin m → Alg B τ q) {i₁ i₂ i₃ : Fin m} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (h23 : i₂ ≠ i₃) (hJ1 : a i₁ ∈ Jid B τ q) (hJ2 : a i₂ ∈ Jid B τ q)
    (hJ3 : a i₃ ∈ Jid B τ q)
    (hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0) :
    m ≤ 3 := by
  classical
  by_contra hcon
  have hsub : ¬ (Finset.univ : Finset (Fin m)) ⊆ {i₁, i₂, i₃} := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hle
    have h23' : ({i₂, i₃} : Finset (Fin m)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h3 : ({i₁, i₂, i₃} : Finset (Fin m)).card ≤ 3 :=
      le_trans (Finset.card_insert_le _ _) (by omega)
    omega
  obtain ⟨j, -, hj⟩ := Finset.not_subset.1 hsub
  have hj1 : j ≠ i₁ := fun h => hj (by rw [h]; simp)
  have hj2 : j ≠ i₂ := fun h => hj (by rw [h]; simp)
  have hj3 : j ≠ i₃ := fun h => hj (by rw [h]; simp)
  refine hirr j (prod_eq_zero_of_three_J h12 h13 h23 ?_ ?_ ?_ hJ1 hJ2 hJ3)
  · exact Finset.mem_erase.2 ⟨fun h => hj1 h.symm, Finset.mem_univ _⟩
  · exact Finset.mem_erase.2 ⟨fun h => hj2 h.symm, Finset.mem_univ _⟩
  · exact Finset.mem_erase.2 ⟨fun h => hj3 h.symm, Finset.mem_univ _⟩

/-! ## E6 — the two length bounds

`irredundant_len_le_aux` runs the four-case analysis once, graded by the exponent
`e` of the cancellation available at the base: `e = 0` always (no cancellation),
`e = 1` when `hcanc` holds. -/

theorem irredundant_len_le_aux {B : Type} [CommRing B] [IsDomain B] {τ : B}
    (hτ : Prime τ) {q e : ℕ} (he : e ≤ 1) (hqe : e + 1 ≤ q) {m : ℕ}
    (a : Fin m → Alg B τ q) (h0 : ∏ i, a i = 0)
    (hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0)
    (hcanc : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : B, a₂ * b₃ + a₃ * b₂ + a₃ * b₃ = 0 →
      a₁ * b₃ + a₃ * b₁ + a₂ * b₂ = 0 → τ ^ e ∣ (a₁ * b₃ + a₃ * b₁)) :
    m + e ≤ q + 2 := by
  classical
  set Jset : Finset (Fin m) :=
    Finset.univ.filter (fun i => (a i).fst = 0) with hJdef
  have hmemJ : ∀ i : Fin m, i ∈ Jset ↔ (a i).fst = 0 := by
    intro i
    rw [hJdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  -- **Case 0** (omitted by the sketch): some factor must lie in `J`.
  have hJne : Jset.Nonempty := by
    rcases Finset.eq_empty_or_nonempty Jset with hemp | hne
    · exfalso
      have hall : ∀ i : Fin m, (a i).fst ≠ 0 := by
        intro i hi
        have hmem : i ∈ Jset := (hmemJ i).2 hi
        rw [hemp] at hmem
        exact absurd hmem (Finset.notMem_empty i)
      have hprod : (∏ i, a i).fst ≠ 0 := by
        rw [fst_prod]
        exact Finset.prod_ne_zero_iff.2 fun i _ => hall i
      rw [h0] at hprod
      exact hprod rfl
    · exact hne
  have hpos : 1 ≤ Jset.card := Finset.card_pos.2 hJne
  rcases Nat.lt_or_ge Jset.card 3 with hlt | hge
  · rcases Nat.lt_or_ge Jset.card 2 with h1 | h2
    · -- **Case 3**: exactly one factor in `J`.
      obtain ⟨i₁, hi₁⟩ := Finset.card_eq_one.1 (by omega : Jset.card = 1)
      have hJ1 : (a i₁).fst = 0 := (hmemJ i₁).1 (by rw [hi₁]; simp)
      have hother : ∀ i, i ≠ i₁ → (a i).fst ≠ 0 := by
        intro i hi hf
        have hmem := (hmemJ i).2 hf
        rw [hi₁, Finset.mem_singleton] at hmem
        exact hi hmem
      have := case_one_bound hτ a hJ1 hother h0 hirr
      omega
    · -- **Case 2**: exactly two factors in `J`.
      obtain ⟨i₁, i₂, h12, hset⟩ := Finset.card_eq_two.1 (by omega : Jset.card = 2)
      have hJ1 : (a i₁).fst = 0 := (hmemJ i₁).1 (by rw [hset]; simp)
      have hJ2 : (a i₂).fst = 0 := (hmemJ i₂).1 (by rw [hset]; simp)
      have hother : ∀ i, i ≠ i₁ → i ≠ i₂ → (a i).fst ≠ 0 := by
        intro i hia hib hf
        have hmem := (hmemJ i).2 hf
        rw [hset, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact hia h
        · exact hib h
      exact case_two_bound hτ a h12 hJ1 hJ2 hother h0 hirr (by omega) hcanc
  · -- **Case 1**: at least three factors in `J`, so `J³ = 0` forces `m ≤ 3`.
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨i₁, i₂, i₃, h12, h13, h23, hT⟩ := Finset.card_eq_three.1 hTcard
    have hmemT : ∀ i ∈ T, a i ∈ Jid B τ q := fun i hi =>
      Alg.mem_Jid_iff.2 ((hmemJ i).1 (hTsub hi))
    have hJ1 : a i₁ ∈ Jid B τ q := hmemT i₁ (by rw [hT]; simp)
    have hJ2 : a i₂ ∈ Jid B τ q := hmemT i₂ (by rw [hT]; simp)
    have hJ3 : a i₃ ∈ Jid B τ q := hmemT i₃ (by rw [hT]; simp)
    have := card_le_three_of_three_J a h12 h13 h23 hJ1 hJ2 hJ3 hirr
    omega

/-- **E6 (generic).** Without any cancellation hypothesis, every irredundant
zero-product in `Alg B τ q` has length at most `q + 2`.  This is the version
Stage F instantiates at `B = Polynomial Dbase`, `τ = Polynomial.C tD` — a base at
which `hcanc` is FALSE (`hcanc_polyDbase_false`). -/
theorem irredundant_len_le_generic {B : Type} [CommRing B] [IsDomain B] {τ : B}
    (hτ : Prime τ) {q : ℕ} (hq : 1 ≤ q) {m : ℕ} (a : Fin m → Alg B τ q)
    (h0 : ∏ i, a i = 0)
    (hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0) :
    m ≤ q + 2 := by
  have h := irredundant_len_le_aux (e := 0) hτ (by omega) (by omega) a h0 hirr
    (fun _ _ _ _ _ _ _ _ => by rw [pow_zero]; exact one_dvd _)
  omega

/-- **E6 (with cancellation).** With the characteristic-2 cancellation available
at the base — supplied as the EXPLICIT hypothesis `hcanc`, never proved
generically — the bound improves to `q + 1`. -/
theorem irredundant_len_le_of_hcanc {B : Type} [CommRing B] [IsDomain B] {τ : B}
    (hτ : Prime τ) {q : ℕ} (hq : 2 ≤ q) {m : ℕ} (a : Fin m → Alg B τ q)
    (h0 : ∏ i, a i = 0)
    (hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0)
    (hcanc : ∀ a₁ a₂ a₃ b₁ b₂ b₃ : B, a₂ * b₃ + a₃ * b₂ + a₃ * b₃ = 0 →
      a₁ * b₃ + a₃ * b₁ + a₂ * b₂ = 0 → τ ∣ (a₁ * b₃ + a₃ * b₁)) :
    m ≤ q + 1 := by
  have h := irredundant_len_le_aux (e := 1) hτ (by omega) (by omega) a h0 hirr
    (fun a₁ a₂ a₃ b₁ b₂ b₃ h1 h2 => by
      rw [pow_one]; exact hcanc a₁ a₂ a₃ b₁ b₂ b₃ h1 h2)
  omega

/-! ## E7 — the frozen `isNAbsorbing_A_succ_q` -/

/-- Frozen statement `isNAbsorbing_A_succ_q`, proved: `0` is `(q+1)`-absorbing in
`A_q`.  Instantiates `irredundant_len_le_of_hcanc` at `B = Dbase`, `τ = tD`, with
`Polynomial.prime_X` for primality and Stage C's `hcanc_Dbase` for the
cancellation. -/
theorem isNAbsorbing_A_succ_q_proof (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (⊥ : Ideal (A q)) (q + 1) := by
  rw [absorbing_iff_no_irredundant]
  rintro ⟨a, ha, hj⟩
  have h0 : ∏ i, a i = 0 := Ideal.mem_bot.1 ha
  have hirr : ∀ j, ∏ i ∈ Finset.univ.erase j, a i ≠ 0 := fun j h =>
    hj j (Ideal.mem_bot.2 h)
  have hlen := irredundant_len_le_of_hcanc (B := Dbase) (τ := tD)
    Polynomial.prime_X hq a h0 hirr hcanc_Dbase
  omega

end Prob30c
