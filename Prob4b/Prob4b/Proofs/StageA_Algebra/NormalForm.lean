/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b worker agent-iter1-1
-/
import Prob4b.Defs

/-!
# Stage A, steps A3 / A4 — the normal form of `B`

`Balg = F₂[a,b,c,d] / ((a,b,c,d)³, ad + bc)` is a noncomputable quotient, so no
finite check reduces on it directly. This file makes `Balg` *computable about* by
building an explicit `ZMod 2`-linear normal form

* `nf : Balg →ₗ[ZMod 2] (Idx → ZMod 2)`,
* its section `sec : (Idx → ZMod 2) →ₗ[ZMod 2] Balg`,

proving that they are **two-sided** inverses (`nf_sec` and `sec_nf`), packaging the
pair as `basisB : Basis Idx (ZMod 2) Balg`, and recording the evaluation lemmas
`nf_one`, `nf_xa`, …, `nf_xd_mul_xd` with which Stages B and C compute.

The index type is `Idx := Unit ⊕ Fin 4 ⊕ Fin 9`, listing the monomial basis

`1; a, b, c, d; a², ab, ac, ad, b², bd, c², cd, d²`

(`bc` is deliberately absent: the defining relation makes `bc = ad`).

Frozen theorem 1 (`Prob4b.B_nontrivial`) is delivered here as
`B_nontrivial_proof`, obtained from the explicit functional `nf` and not by
`decide`.
-/

open MvPolynomial

namespace Prob4b

noncomputable section

/-! ## The index type and its monomial exponents -/

/-- The 14-element index type of the monomial basis
`1; a, b, c, d; a², ab, ac, ad, b², bd, c², cd, d²` of `B`. -/
abbrev Idx : Type := Unit ⊕ Fin 4 ⊕ Fin 9

/-- The exponent vector of the degree-2 monomial `X i * X j`. -/
def pexp (i j : Fin 4) : Fin 4 →₀ ℕ := Finsupp.single i 1 + Finsupp.single j 1

/-- The variable pairs of the nine degree-2 basis monomials
`a², ab, ac, ad, b², bd, c², cd, d²` (note: `bc` is not among them). -/
def deg2 : Fin 9 → Fin 4 × Fin 4 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 3), (2, 2), (2, 3), (3, 3)]

/-- The exponent vector of the basis monomial indexed by `i : Idx`. -/
def monoExp : Idx → (Fin 4 →₀ ℕ)
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl k) => Finsupp.single k 1
  | Sum.inr (Sum.inr j) => pexp (deg2 j).1 (deg2 j).2

/-- The index of the basis monomial `ad`. -/
def adIdx : Idx := Sum.inr (Sum.inr 3)

/-- The exponent vector of the monomial `bc`, which is *not* a basis monomial. -/
def bcExp : Fin 4 →₀ ℕ := pexp 1 2

@[simp] theorem monoExp_inl (u : Unit) : monoExp (Sum.inl u) = 0 := rfl

@[simp] theorem monoExp_lin (k : Fin 4) :
    monoExp (Sum.inr (Sum.inl k)) = Finsupp.single k 1 := rfl

@[simp] theorem monoExp_quad (j : Fin 9) :
    monoExp (Sum.inr (Sum.inr j)) = pexp (deg2 j).1 (deg2 j).2 := rfl

/-- Evaluation of a degree-2 exponent vector at a variable. -/
theorem pexp_apply (i j k : Fin 4) :
    (pexp i j) k = (if i = k then 1 else 0) + (if j = k then 1 else 0) := by
  simp [pexp, Finsupp.single_apply]

/-- `pexp` is symmetric. -/
theorem pexp_comm (i j : Fin 4) : pexp i j = pexp j i := by simp [pexp, add_comm]

/-- Two degree-2 exponent vectors agree exactly when their variable pairs agree
up to order. -/
theorem pexp_eq_iff {i j k l : Fin 4} :
    pexp i j = pexp k l ↔ (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have h' : ∀ m : Fin 4, (if i = m then 1 else 0) + (if j = m then 1 else 0)
        = ((if k = m then 1 else 0) + (if l = m then 1 else 0) : ℕ) := by
      intro m
      have := congrArg (fun f => f m) h
      simpa [pexp_apply] using this
    clear h
    revert h'
    revert i j k l
    decide
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp [pexp, add_comm]

/-! ## Total degree of an exponent vector -/

/-- The total degree of an exponent vector. -/
def edeg (m : Fin 4 →₀ ℕ) : ℕ := ∑ k : Fin 4, m k

theorem edeg_add (m m' : Fin 4 →₀ ℕ) : edeg (m + m') = edeg m + edeg m' := by
  simp [edeg, Finset.sum_add_distrib]

@[simp] theorem edeg_zero : edeg 0 = 0 := by simp [edeg]

@[simp] theorem edeg_single (i : Fin 4) : edeg (Finsupp.single i 1) = 1 := by
  simp [edeg, Finsupp.single_apply]

@[simp] theorem edeg_pexp (i j : Fin 4) : edeg (pexp i j) = 2 := by
  simp [pexp, edeg_add]

theorem edeg_eq_zero_iff (m : Fin 4 →₀ ℕ) : edeg m = 0 ↔ m = 0 := by
  constructor
  · intro h
    ext k
    have := (Finset.sum_eq_zero_iff (s := (Finset.univ : Finset (Fin 4))) (f := fun k => m k)).1 h
    simpa using this k (Finset.mem_univ k)
  · rintro rfl; simp

/-- Every basis monomial has degree at most 2. -/
theorem edeg_monoExp (i : Idx) : edeg (monoExp i) ≤ 2 := by
  rcases i with u | k | j <;> simp

@[simp] theorem edeg_bcExp : edeg bcExp = 2 := by simp [bcExp]

/-- Peel one variable off a nonconstant exponent vector. -/
theorem exists_peel (m : Fin 4 →₀ ℕ) (hm : 0 < edeg m) :
    ∃ (i : Fin 4) (m' : Fin 4 →₀ ℕ), m = Finsupp.single i 1 + m' ∧ edeg m' + 1 = edeg m := by
  have hne : m ≠ 0 := fun h => by simp [h] at hm
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, m i ≠ 0 := by
    by_contra hc
    simp only [ne_eq, not_exists, not_not] at hc
    exact hne (by ext k; simp [hc k])
  have hle : Finsupp.single i 1 ≤ m := by
    intro k
    by_cases hk : i = k
    · subst hk
      simpa using Nat.one_le_iff_ne_zero.2 hi
    · simp [hk]
  refine ⟨i, m - Finsupp.single i 1, ?_, ?_⟩
  · rw [add_comm, tsub_add_cancel_of_le hle]
  · have h2 : edeg (m - Finsupp.single i 1) + edeg (Finsupp.single i 1) = edeg m := by
      rw [← edeg_add, tsub_add_cancel_of_le hle]
    rw [edeg_single] at h2
    omega

/-! ## The basis monomials are pairwise distinct -/

theorem deg2_injective : ∀ j j' : Fin 9,
    ((deg2 j).1 = (deg2 j').1 ∧ (deg2 j).2 = (deg2 j').2) ∨
      ((deg2 j).1 = (deg2 j').2 ∧ (deg2 j).2 = (deg2 j').1) → j = j' := by decide

theorem deg2_ne_bc : ∀ j : Fin 9,
    ¬(((deg2 j).1 = 1 ∧ (deg2 j).2 = 2) ∨ ((deg2 j).1 = 2 ∧ (deg2 j).2 = 1)) := by decide

/-- Distinct indices carry distinct monomials. -/
theorem monoExp_eq_iff (i j : Idx) : monoExp i = monoExp j ↔ i = j := by
  constructor
  · intro h
    have hd : edeg (monoExp i) = edeg (monoExp j) := congrArg edeg h
    rcases i with u | k | m <;> rcases j with u' | k' | m'
    all_goals try simp only [monoExp_inl, monoExp_lin, monoExp_quad, edeg_zero, edeg_single,
      edeg_pexp] at h hd
    all_goals first
      | omega
      | rfl
      | exact congrArg (fun t => Sum.inr (Sum.inl t))
          (Finsupp.single_left_injective (b := (1 : ℕ)) one_ne_zero h)
      | exact congrArg (fun t => Sum.inr (Sum.inr t)) (deg2_injective _ _ (pexp_eq_iff.1 h))
  · rintro rfl; rfl

/-- `bc` is not a basis monomial. -/
theorem monoExp_ne_bcExp (i : Idx) : monoExp i ≠ bcExp := by
  intro h
  have hd : edeg (monoExp i) = edeg bcExp := congrArg edeg h
  rcases i with u | k | m
  · simp at hd
  · simp at hd
  · rw [monoExp_quad, bcExp] at h
    exact deg2_ne_bc m (pexp_eq_iff.1 h)

/-- Every exponent vector of degree at most 2 is either a basis monomial or `bc`. -/
theorem pexp_classify (i j : Fin 4) : (∃ k : Idx, pexp i j = monoExp k) ∨ pexp i j = bcExp := by
  have hcov : ∀ i j : Fin 4,
      (∃ k : Fin 9, deg2 k = (i, j) ∨ deg2 k = (j, i)) ∨ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) := by
    decide
  rcases hcov i j with ⟨k, hk | hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨Sum.inr (Sum.inr k), by rw [monoExp_quad, hk]⟩
  · exact Or.inl ⟨Sum.inr (Sum.inr k), by rw [monoExp_quad, hk]; exact pexp_comm i j⟩
  · exact Or.inr rfl
  · exact Or.inr (pexp_comm 2 1)

/-- Every exponent vector of degree at most 2 is either a basis monomial or `bc`. -/
theorem exp_classify (m : Fin 4 →₀ ℕ) (h : edeg m ≤ 2) :
    (∃ i : Idx, m = monoExp i) ∨ m = bcExp := by
  rcases Nat.lt_or_ge (edeg m) 1 with h0 | h1
  · have : m = 0 := (edeg_eq_zero_iff m).1 (by omega)
    exact Or.inl ⟨Sum.inl (), by simp [this]⟩
  obtain ⟨i, m', rfl, hm'⟩ := exists_peel m (by omega)
  rcases Nat.lt_or_ge (edeg m') 1 with h0' | h1'
  · have : m' = 0 := (edeg_eq_zero_iff m').1 (by omega)
    exact Or.inl ⟨Sum.inr (Sum.inl i), by simp [this]⟩
  obtain ⟨j, m'', rfl, hm''⟩ := exists_peel m' (by omega)
  have : m'' = 0 := (edeg_eq_zero_iff m'').1 (by omega)
  subst this
  have hp : Finsupp.single i 1 + (Finsupp.single j 1 + 0) = pexp i j := by
    simp [pexp]
  rw [hp]
  exact pexp_classify i j

/-! ## The normal form on polynomials -/

/-- The normal form on `F₂[a,b,c,d]`: read off the coefficients of the 14 basis
monomials, adding the coefficient of `bc` to that of `ad`. -/
def nfPol : Pol →ₗ[ZMod 2] (Idx → ZMod 2) where
  toFun p i := coeff (monoExp i) p + (if i = adIdx then coeff bcExp p else 0)
  map_add' p q := by
    funext i
    simp only [Pi.add_apply, coeff_add]
    split <;> ring
  map_smul' c p := by
    funext i
    simp only [coeff_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
    split <;> ring

theorem nfPol_apply (p : Pol) (i : Idx) :
    nfPol p i = coeff (monoExp i) p + (if i = adIdx then coeff bcExp p else 0) := rfl

/-- The normal form of a basis monomial is its own basis vector. -/
theorem nfPol_monomial_monoExp (i : Idx) (c : ZMod 2) :
    nfPol (monomial (monoExp i) c) = Pi.single i c := by
  funext j
  rw [nfPol_apply, coeff_monomial, coeff_monomial, Pi.single_apply]
  rw [if_neg (monoExp_ne_bcExp i)]
  by_cases hij : j = i
  · subst hij
    simp
  · rw [if_neg (fun hc => hij ((monoExp_eq_iff j i).1 hc.symm)), if_neg hij]
    simp

/-- The normal form of `bc` is the basis vector of `ad`. -/
theorem nfPol_monomial_bcExp (c : ZMod 2) :
    nfPol (monomial bcExp c) = Pi.single adIdx c := by
  funext j
  rw [nfPol_apply, coeff_monomial, coeff_monomial, Pi.single_apply]
  rw [if_neg (fun hc => monoExp_ne_bcExp j hc.symm), if_pos rfl]
  by_cases hj : j = adIdx
  · simp [hj]
  · simp [hj]

/-! ## `nfPol` kills the relation ideal -/

/-- The ideal of polynomials all of whose monomials have total degree at least `k`. -/
def degGe (k : ℕ) : Ideal Pol where
  carrier := {p | ∀ m, edeg m < k → coeff m p = 0}
  zero_mem' := by intro m _; simp
  add_mem' := by
    intro a b ha hb m hm
    simp only [coeff_add, ha m hm, hb m hm, add_zero]
  smul_mem' := by
    intro c p hp m hm
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero ?_
    rintro ⟨x, y⟩ hx
    have hxy : x + y = m := Finset.mem_antidiagonal.1 hx
    have hy : edeg y ≤ edeg m := by rw [← hxy, edeg_add]; omega
    rw [hp y (by omega), mul_zero]

theorem mem_degGe {k : ℕ} {p : Pol} : p ∈ degGe k ↔ ∀ m, edeg m < k → coeff m p = 0 := Iff.rfl

theorem degGe_mul (j k : ℕ) : degGe j * degGe k ≤ degGe (j + k) := by
  rw [Ideal.mul_le]
  intro r hr s hs
  rw [mem_degGe]
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨x, y⟩ hx
  have hxy : x + y = m := Finset.mem_antidiagonal.1 hx
  have hsum : edeg x + edeg y = edeg m := by rw [← hxy, edeg_add]
  rcases lt_or_ge (edeg x) j with h | h
  · rw [mem_degGe.1 hr x h, zero_mul]
  · rw [mem_degGe.1 hs y (by omega), mul_zero]

theorem mPol_le_degGe_one : mPol ≤ degGe 1 := by
  rw [mPol, Ideal.span_le]
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have key : ∀ i : Fin 4, (X i : Pol) ∈ degGe 1 := by
    intro i m hm
    rw [coeff_X, if_neg]
    intro h
    have h1 : edeg (Finsupp.single i 1) = 1 := by simp
    rw [h] at h1
    omega
  rcases hp with rfl | rfl | rfl | rfl
  exacts [key 0, key 1, key 2, key 3]

theorem mPol_pow_three_le : mPol ^ 3 ≤ degGe 3 := by
  have h2 : mPol * mPol ≤ degGe 2 :=
    le_trans (Ideal.mul_mono mPol_le_degGe_one mPol_le_degGe_one) (degGe_mul 1 1)
  have h3 : mPol * mPol * mPol ≤ degGe 3 :=
    le_trans (Ideal.mul_mono h2 mPol_le_degGe_one) (degGe_mul 2 1)
  have hp : mPol ^ 3 = mPol * mPol * mPol := by ring
  rw [hp]
  exact h3

/-- `nfPol` vanishes on polynomials with no monomial of degree below 3. -/
theorem nfPol_eq_zero_of_mem_degGe_three {p : Pol} (hp : p ∈ degGe 3) : nfPol p = 0 := by
  funext i
  rw [nfPol_apply, mem_degGe.1 hp _ (by have := edeg_monoExp i; omega),
    mem_degGe.1 hp _ (by simp)]
  simp

/-- Every monomial of degree at least `n` lies in `m^n`. -/
theorem monomial_mem_mPol_pow (n : ℕ) : ∀ m : Fin 4 →₀ ℕ, n ≤ edeg m →
    (monomial m (1 : ZMod 2)) ∈ mPol ^ n := by
  induction n with
  | zero => intro m _; simp
  | succ n ih =>
    intro m hm
    obtain ⟨i, m', hm', hdeg⟩ := exists_peel m (by omega)
    have h1 : (X i : Pol) ∈ mPol := by
      apply Ideal.subset_span
      fin_cases i <;> simp
    have h2 : (monomial m' (1 : ZMod 2)) ∈ mPol ^ n := ih m' (by omega)
    have h3 : (monomial m (1 : ZMod 2)) = X i * monomial m' 1 := by
      rw [hm', X, monomial_mul, one_mul]
    rw [h3, pow_succ']
    exact Ideal.mul_mem_mul h1 h2

/-- The relation `ad + bc` as a polynomial. -/
def relElt : Pol := X 0 * X 3 + X 1 * X 2

theorem X_mul_X (i j : Fin 4) : (X i * X j : Pol) = monomial (pexp i j) 1 := by
  rw [X, X, monomial_mul, one_mul]
  rfl

theorem monoExp_adIdx : monoExp adIdx = pexp 0 3 := rfl

/-- The normal form kills the defining relation: `ad` and `bc` have the same
normal form, so their sum vanishes in characteristic 2. -/
theorem nfPol_relElt : nfPol relElt = 0 := by
  have h1 : (X 0 * X 3 : Pol) = monomial (monoExp adIdx) 1 := by
    rw [X_mul_X, monoExp_adIdx]
  have h2 : (X 1 * X 2 : Pol) = monomial bcExp 1 := by rw [X_mul_X]; rfl
  rw [relElt, h1, h2, map_add, nfPol_monomial_monoExp, nfPol_monomial_bcExp]
  funext i
  simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply]
  split <;> decide

theorem relElt_mem_degGe_two : relElt ∈ degGe 2 := by
  intro m hm
  have h1 : (X 0 * X 3 : Pol) = monomial (pexp 0 3) 1 := X_mul_X 0 3
  have h2 : (X 1 * X 2 : Pol) = monomial (pexp 1 2) 1 := X_mul_X 1 2
  have hne1 : ¬ (pexp 0 3 = m) := by
    intro hc
    rw [← hc] at hm
    simp at hm
  have hne2 : ¬ (pexp 1 2 = m) := by
    intro hc
    rw [← hc] at hm
    simp at hm
  rw [relElt, coeff_add, h1, h2, coeff_monomial, coeff_monomial, if_neg hne1, if_neg hne2,
    add_zero]

/-- `nfPol` kills every multiple of the relation. -/
theorem nfPol_mul_relElt (q : Pol) : nfPol (q * relElt) = 0 := by
  set c : ZMod 2 := coeff 0 q with hc
  have hsplit : q = C c + (q - C c) := by ring
  have hq0 : q - C c ∈ degGe 1 := by
    intro m hm
    have hm0 : m = 0 := (edeg_eq_zero_iff m).1 (by omega)
    subst hm0
    rw [coeff_sub, coeff_C, if_pos rfl, hc, sub_self]
  have hmul : (q - C c) * relElt ∈ degGe 3 :=
    (degGe_mul 1 2) (Ideal.mul_mem_mul hq0 relElt_mem_degGe_two)
  have hCc : C c * relElt = c • relElt := by
    rw [C_mul']
  calc nfPol (q * relElt) = nfPol (C c * relElt) + nfPol ((q - C c) * relElt) := by
        rw [← map_add]
        congr 1
        ring
    _ = 0 := by
        rw [hCc, map_smul, nfPol_relElt, nfPol_eq_zero_of_mem_degGe_three hmul]
        simp

/-- `nfPol` vanishes on the whole relation ideal. -/
theorem nfPol_eq_zero_of_mem_relIdeal (p : Pol) (hp : p ∈ relIdeal) : nfPol p = 0 := by
  rw [relIdeal, Submodule.mem_sup] at hp
  obtain ⟨y, hy, z, hz, rfl⟩ := hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_add, nfPol_eq_zero_of_mem_degGe_three (mPol_pow_three_le hy)]
  have : (q * (X 0 * X 3 + X 1 * X 2) : Pol) = q * relElt := rfl
  rw [this, nfPol_mul_relElt]
  simp

/-- The relation ideal is contained in the kernel of `nfPol` (stated as an
inclusion of sets, since `relIdeal` is a `Pol`-submodule while the kernel is a
`ZMod 2`-submodule). -/
theorem nfPol_relIdeal_le_ker : (relIdeal : Set Pol) ⊆ (LinearMap.ker nfPol : Set Pol) :=
  fun p hp => nfPol_eq_zero_of_mem_relIdeal p hp

/-! ## The normal form on `B` -/

/-- The normal form `nf : B →ₗ[F₂] (Idx → F₂)`, obtained by descending `nfPol`
through the quotient by `relIdeal`. -/
def nf : Balg →ₗ[ZMod 2] (Idx → ZMod 2) where
  toFun x := Quotient.liftOn' x nfPol (by
    intro a b hab
    have hm : a - b ∈ relIdeal := by simpa [Submodule.quotientRel_def] using hab
    have h0 := nfPol_eq_zero_of_mem_relIdeal _ hm
    simp only [map_sub, sub_eq_zero] at h0
    exact h0)
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn' with
    | h a =>
      induction y using Quotient.inductionOn' with
      | h b => exact map_add nfPol a b
  map_smul' := by
    intro c x
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp only [RingHom.id_apply, zero_smul]
      change nfPol (0 : Pol) = 0
      exact map_zero nfPol
    · simp

@[simp] theorem nf_mk (p : Pol) : nf (Ideal.Quotient.mk relIdeal p) = nfPol p := rfl

/-- The class in `B` of the basis monomial indexed by `i`. -/
def monB (i : Idx) : Balg := Ideal.Quotient.mk relIdeal (monomial (monoExp i) 1)

@[simp] theorem nf_monB (i : Idx) : nf (monB i) = Pi.single i 1 := by
  rw [monB, nf_mk, nfPol_monomial_monoExp]

/-- The section `sec : (Idx → F₂) →ₗ[F₂] B` sending a basis vector to the class
of the corresponding monomial. -/
def sec : (Idx → ZMod 2) →ₗ[ZMod 2] Balg where
  toFun v := ∑ i : Idx, v i • monB i
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

theorem sec_apply (v : Idx → ZMod 2) : sec v = ∑ i : Idx, v i • monB i := rfl

@[simp] theorem sec_single (i : Idx) (c : ZMod 2) : sec (Pi.single i c) = c • monB i := by
  rw [sec_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The two-sided inverse and the basis -/

theorem nf_sec_apply (v : Idx → ZMod 2) : nf (sec v) = v := by
  rw [sec_apply, map_sum]
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [map_smul, nf_monB]
    simp
  · intro i _ hi
    rw [map_smul, nf_monB]
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `nf ∘ sec = id`: the 14 basis vectors are hit. -/
theorem nf_sec : nf ∘ₗ sec = LinearMap.id :=
  LinearMap.ext fun v => nf_sec_apply v

theorem sec_nf_apply (x : Balg) : sec (nf x) = x := by
  induction x using Quotient.inductionOn' with
  | h p =>
    change sec (nf (Ideal.Quotient.mk relIdeal p)) = Ideal.Quotient.mk relIdeal p
    induction p using MvPolynomial.induction_on' with
    | monomial m c =>
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · simp
      rcases Nat.lt_or_ge (edeg m) 3 with hdeg | hdeg
      · rcases exp_classify m (by omega) with ⟨i, rfl⟩ | rfl
        · rw [nf_mk, nfPol_monomial_monoExp, sec_single, one_smul, monB]
        · rw [nf_mk, nfPol_monomial_bcExp, sec_single, one_smul, monB, monoExp_adIdx]
          rw [Ideal.Quotient.eq]
          have hb : monomial (pexp 0 3) (1 : ZMod 2) - monomial bcExp 1 = relElt := by
            rw [relElt, X_mul_X, X_mul_X]
            have : (pexp 1 2 : Fin 4 →₀ ℕ) = bcExp := rfl
            rw [this]
            ring_nf
            rw [sub_eq_add_neg]
            congr 1
            rw [← neg_one_smul (ZMod 2) (monomial bcExp (1 : ZMod 2))]
            simp
          rw [hb, relIdeal]
          exact Submodule.mem_sup_right (Ideal.subset_span rfl)
      · have hzero : (monomial m (1 : ZMod 2)) ∈ relIdeal :=
          Submodule.mem_sup_left (monomial_mem_mPol_pow 3 m hdeg)
        rw [nf_mk, nfPol_eq_zero_of_mem_degGe_three
          (mPol_pow_three_le (monomial_mem_mPol_pow 3 m hdeg))]
        rw [map_zero, (Ideal.Quotient.eq_zero_iff_mem).2 hzero]
    | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq]

/-- `sec ∘ nf = id`: the 14 monomial classes span `B`. -/
theorem sec_nf : sec ∘ₗ nf = LinearMap.id :=
  LinearMap.ext fun x => sec_nf_apply x

/-- `B` is a 14-dimensional `F₂`-vector space with the monomial basis. -/
def basisB : Module.Basis Idx (ZMod 2) Balg :=
  Module.Basis.ofEquivFun (LinearEquiv.ofLinear nf sec nf_sec sec_nf)

/-! ## Evaluation lemmas -/

@[simp] theorem nf_one : nf (1 : Balg) = Pi.single (Sum.inl ()) 1 := by
  have h1 : (1 : Balg) = Ideal.Quotient.mk relIdeal (monomial (monoExp (Sum.inl ())) 1) := by
    rw [monoExp_inl]
    simp
  rw [h1, nf_mk, nfPol_monomial_monoExp]

theorem nf_x (i : Fin 4) :
    nf (Ideal.Quotient.mk relIdeal (X i)) = Pi.single (Sum.inr (Sum.inl i)) 1 := by
  have h : (X i : Pol) = monomial (monoExp (Sum.inr (Sum.inl i))) 1 := by
    rw [monoExp_lin, X]
  rw [h, nf_mk, nfPol_monomial_monoExp]

@[simp] theorem nf_xa : nf xa = Pi.single (Sum.inr (Sum.inl 0)) 1 := nf_x 0

@[simp] theorem nf_xb : nf xb = Pi.single (Sum.inr (Sum.inl 1)) 1 := nf_x 1

@[simp] theorem nf_xc : nf xc = Pi.single (Sum.inr (Sum.inl 2)) 1 := nf_x 2

@[simp] theorem nf_xd : nf xd = Pi.single (Sum.inr (Sum.inl 3)) 1 := nf_x 3

/-- The product of two generators is the class of the corresponding degree-2
monomial. -/
theorem mk_X_mul_mk_X (i j : Fin 4) :
    (Ideal.Quotient.mk relIdeal (X i)) * (Ideal.Quotient.mk relIdeal (X j))
      = Ideal.Quotient.mk relIdeal (monomial (pexp i j) 1) := by
  rw [← map_mul, X_mul_X]

/-- Normal form of a product of two generators, in terms of its exponent. -/
theorem nf_mul_gen (i j : Fin 4) :
    nf ((Ideal.Quotient.mk relIdeal (X i)) * (Ideal.Quotient.mk relIdeal (X j)))
      = nfPol (monomial (pexp i j) 1) := by
  rw [mk_X_mul_mk_X, nf_mk]

@[simp] theorem nf_xa_mul_xa : nf (xa * xa) = Pi.single (Sum.inr (Sum.inr 0)) 1 := by
  rw [show xa = Ideal.Quotient.mk relIdeal (X 0) from rfl, nf_mul_gen,
    show pexp 0 0 = monoExp (Sum.inr (Sum.inr 0)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xa_mul_xb : nf (xa * xb) = Pi.single (Sum.inr (Sum.inr 1)) 1 := by
  rw [show xa = Ideal.Quotient.mk relIdeal (X 0) from rfl,
    show xb = Ideal.Quotient.mk relIdeal (X 1) from rfl, nf_mul_gen,
    show pexp 0 1 = monoExp (Sum.inr (Sum.inr 1)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xa_mul_xc : nf (xa * xc) = Pi.single (Sum.inr (Sum.inr 2)) 1 := by
  rw [show xa = Ideal.Quotient.mk relIdeal (X 0) from rfl,
    show xc = Ideal.Quotient.mk relIdeal (X 2) from rfl, nf_mul_gen,
    show pexp 0 2 = monoExp (Sum.inr (Sum.inr 2)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xa_mul_xd : nf (xa * xd) = Pi.single adIdx 1 := by
  rw [show xa = Ideal.Quotient.mk relIdeal (X 0) from rfl,
    show xd = Ideal.Quotient.mk relIdeal (X 3) from rfl, nf_mul_gen,
    show pexp 0 3 = monoExp adIdx from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xb_mul_xb : nf (xb * xb) = Pi.single (Sum.inr (Sum.inr 4)) 1 := by
  rw [show xb = Ideal.Quotient.mk relIdeal (X 1) from rfl, nf_mul_gen,
    show pexp 1 1 = monoExp (Sum.inr (Sum.inr 4)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xb_mul_xc : nf (xb * xc) = Pi.single adIdx 1 := by
  rw [show xb = Ideal.Quotient.mk relIdeal (X 1) from rfl,
    show xc = Ideal.Quotient.mk relIdeal (X 2) from rfl, nf_mul_gen,
    show pexp 1 2 = bcExp from rfl, nfPol_monomial_bcExp]

@[simp] theorem nf_xb_mul_xd : nf (xb * xd) = Pi.single (Sum.inr (Sum.inr 5)) 1 := by
  rw [show xb = Ideal.Quotient.mk relIdeal (X 1) from rfl,
    show xd = Ideal.Quotient.mk relIdeal (X 3) from rfl, nf_mul_gen,
    show pexp 1 3 = monoExp (Sum.inr (Sum.inr 5)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xc_mul_xc : nf (xc * xc) = Pi.single (Sum.inr (Sum.inr 6)) 1 := by
  rw [show xc = Ideal.Quotient.mk relIdeal (X 2) from rfl, nf_mul_gen,
    show pexp 2 2 = monoExp (Sum.inr (Sum.inr 6)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xc_mul_xd : nf (xc * xd) = Pi.single (Sum.inr (Sum.inr 7)) 1 := by
  rw [show xc = Ideal.Quotient.mk relIdeal (X 2) from rfl,
    show xd = Ideal.Quotient.mk relIdeal (X 3) from rfl, nf_mul_gen,
    show pexp 2 3 = monoExp (Sum.inr (Sum.inr 7)) from rfl, nfPol_monomial_monoExp]

@[simp] theorem nf_xd_mul_xd : nf (xd * xd) = Pi.single (Sum.inr (Sum.inr 8)) 1 := by
  rw [show xd = Ideal.Quotient.mk relIdeal (X 3) from rfl, nf_mul_gen,
    show pexp 3 3 = monoExp (Sum.inr (Sum.inr 8)) from rfl, nfPol_monomial_monoExp]

/-! ## Frozen theorem 1 -/

/-- Frozen theorem 1: `B` did not collapse. Proved from the explicit functional
`nf`, not by `decide`. -/
theorem B_nontrivial_proof : Nontrivial Balg := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have h1 : nf (1 : Balg) = nf 0 := congrArg nf h
  rw [nf_one, map_zero] at h1
  have h2 := congrFun h1 (Sum.inl ())
  rw [Pi.single_eq_same] at h2
  exact one_ne_zero h2

/-! ## Guardrails -/

/-- Guardrail: the index type really has 14 elements. -/
example : Fintype.card Idx = 14 := by decide

/-- Guardrail: the defining relation is live in the normal form. -/
example : nf (xa * xd) = nf (xb * xc) := by rw [nf_xa_mul_xd, nf_xb_mul_xc]

/-- Guardrail: the degree-2 part did not collapse. -/
example : xa * xb ≠ 0 := by
  intro h
  have h1 : nf (xa * xb) = nf 0 := congrArg nf h
  rw [nf_xa_mul_xb, map_zero] at h1
  have h2 := congrFun h1 (Sum.inr (Sum.inr 1))
  rw [Pi.single_eq_same] at h2
  exact one_ne_zero h2

end

end Prob4b
