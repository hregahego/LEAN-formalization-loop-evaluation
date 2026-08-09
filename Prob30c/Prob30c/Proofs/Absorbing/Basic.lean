/-
Stage A -- the absorbing-number API: `IsNAbsorbing`, `omegaAbs`, `polyExt`,
   and the faithfulness of the `I[X]` model (A1-A7 of BLUEPRINT Part 2).

Everything here is base-ring independent: `R` is an arbitrary `CommRing` and `I`
an arbitrary ideal.  Nothing in this file mentions the counterexample ring.
-/
import Prob30c.Defs

namespace Prob30c

open Finset

/-! ## A1 — the "drop one factor" form of `IsNAbsorbing` -/

/-- `I` is `n`-absorbing iff for every family of `n+1` elements with product in `I`
    one of the `n`-element sub-products obtained by *dropping a single factor*
    already lies in `I`.  This is the working form used by every later stage. -/
theorem absorbing_iff_exists_drop {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    IsNAbsorbing I n ↔ ∀ a : Fin (n + 1) → R, (∏ i, a i) ∈ I →
      ∃ j, (∏ i ∈ Finset.univ.erase j, a i) ∈ I := by
  constructor
  · intro h a ha
    obtain ⟨S, hcard, hS⟩ := h a ha
    have hne : (Sᶜ : Finset (Fin (n + 1))).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, hcard]
      simp
    obtain ⟨j, hj⟩ := hne
    rw [Finset.mem_compl] at hj
    refine ⟨j, ?_⟩
    have hsub : S ⊆ Finset.univ.erase j := by
      intro x hx
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ x⟩
      rintro rfl
      exact hj hx
    have hle : (Finset.univ.erase j).card ≤ S.card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), hcard]
      simp
    rwa [← Finset.eq_of_subset_of_card_le hsub hle]
  · intro h a ha
    obtain ⟨j, hj⟩ := h a ha
    refine ⟨Finset.univ.erase j, ?_, hj⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp

/-! ## A2 — the "no irredundant product" form -/

/-- The `push_neg` form of A1: `I` is `n`-absorbing iff there is no *irredundant*
    product of `n+1` factors lying in `I`. -/
theorem absorbing_iff_no_irredundant {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    IsNAbsorbing I n ↔ ¬ ∃ a : Fin (n + 1) → R, (∏ i, a i) ∈ I ∧
      ∀ j, (∏ i ∈ Finset.univ.erase j, a i) ∉ I := by
  rw [absorbing_iff_exists_drop]
  constructor
  · rintro h ⟨a, ha, hj⟩
    obtain ⟨j, hjmem⟩ := h a ha
    exact hj j hjmem
  · intro h a ha
    by_contra hcon
    exact h ⟨a, ha, fun j hj => hcon ⟨j, hj⟩⟩

/-! ## A3 — monotonicity of `n`-absorbing (FROZEN `isNAbsorbing_succ`) -/

/-- Frozen statement `isNAbsorbing_succ`, proved: an `n`-absorbing ideal is
    `(n+1)`-absorbing.  Given `a : Fin (n+2) → R` with product in `I`, apply the
    hypothesis to the family of length `n+1` obtained by *merging the first two
    slots* into `a 0 * a 1`, then pull the resulting `n`-element subset back. -/
theorem isNAbsorbing_succ_proof {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (h : IsNAbsorbing I n) : IsNAbsorbing I (n + 1) := by
  intro a ha
  set b : Fin (n + 1) → R := Fin.cons (a 0 * a 1) (fun i : Fin n => a i.succ.succ) with hb
  have hb0 : b 0 = a 0 * a 1 := by rw [hb]; simp
  have hbne : ∀ i : Fin (n + 1), i ≠ 0 → b i = a i.succ := by
    intro i hi
    induction i using Fin.cases with
    | zero => exact absurd rfl hi
    | succ k => rw [hb]; simp
  have hprod : (∏ i, b i) = ∏ i, a i := by
    rw [Fin.prod_univ_succ (f := b), Fin.prod_univ_succ (f := a),
      Fin.prod_univ_succ (f := fun i : Fin (n + 1) => a i.succ), hb0,
      Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hbne i.succ (Fin.succ_ne_zero i)),
      Fin.succ_zero_eq_one, mul_assoc]
  obtain ⟨S, hcard, hS⟩ := h b (by rw [hprod]; exact ha)
  by_cases h0 : (0 : Fin (n + 1)) ∈ S
  · -- the merged slot is used: keep both `a 0` and `a 1`
    have h1 : (1 : Fin (n + 2)) ∉ (S.erase 0).image Fin.succ := by
      intro hmem
      obtain ⟨k, hk, hk1⟩ := Finset.mem_image.1 hmem
      rw [← Fin.succ_zero_eq_one] at hk1
      exact (Finset.mem_erase.1 hk).1 (Fin.succ_injective _ hk1)
    have h0' : (0 : Fin (n + 2)) ∉ insert (1 : Fin (n + 2)) ((S.erase 0).image Fin.succ) := by
      intro hmem
      rcases Finset.mem_insert.1 hmem with hx | hx
      · exact (Fin.succ_ne_zero (0 : Fin (n + 1))) (by rw [Fin.succ_zero_eq_one]; exact hx.symm)
      · obtain ⟨k, _, hk1⟩ := Finset.mem_image.1 hx
        exact Fin.succ_ne_zero k hk1
    have hpos : 0 < n := by
      have := Finset.card_pos.2 ⟨0, h0⟩
      omega
    refine ⟨insert 0 (insert 1 ((S.erase 0).image Fin.succ)), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem h0', Finset.card_insert_of_notMem h1,
        Finset.card_image_of_injective _ (Fin.succ_injective _),
        Finset.card_erase_of_mem h0, hcard]
      omega
    · rw [Finset.prod_insert h0', Finset.prod_insert h1,
        Finset.prod_image fun x _ y _ hxy => Fin.succ_injective _ hxy]
      have hrw : ∀ i ∈ S.erase 0, a i.succ = b i := by
        intro i hi
        exact (hbne i (Finset.mem_erase.1 hi).1).symm
      rw [Finset.prod_congr rfl hrw, ← mul_assoc, ← hb0,
        Finset.mul_prod_erase _ _ h0]
      exact hS
  · -- the merged slot is unused: `∏_{i ∈ S} b i` already misses both `a 0`, `a 1`
    have h0' : (0 : Fin (n + 2)) ∉ S.image Fin.succ := by
      intro hmem
      obtain ⟨k, _, hk1⟩ := Finset.mem_image.1 hmem
      exact Fin.succ_ne_zero k hk1
    refine ⟨insert 0 (S.image Fin.succ), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem h0',
        Finset.card_image_of_injective _ (Fin.succ_injective _), hcard]
    · rw [Finset.prod_insert h0',
        Finset.prod_image fun x _ y _ hxy => Fin.succ_injective _ hxy]
      have hrw : ∀ i ∈ S, a i.succ = b i := by
        intro i hi
        refine (hbne i ?_).symm
        rintro rfl
        exact h0 hi
      rw [Finset.prod_congr rfl hrw]
      exact Ideal.mul_mem_left _ _ hS

/-! ## A3′ — monotonicity along `≤` -/

/-- Iterating A3: an `m`-absorbing ideal is `n`-absorbing for every `n ≥ m`. -/
theorem isNAbsorbing_of_le {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (h : IsNAbsorbing I m) : IsNAbsorbing I n := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.1 hmn
    rwa [this] at h
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact isNAbsorbing_succ_proof I k (ih (Nat.lt_succ_iff.1 hlt))
    · have : m = k + 1 := le_antisymm hmn hge
      rwa [this] at h

/-! ## A4 — faithfulness of the `I[X]` model (FROZEN `mem_polyExt_iff`) -/

/-- Frozen statement `mem_polyExt_iff`, proved: `polyExt I = I[X]` really is the set
    of polynomials all of whose coefficients lie in `I`. -/
theorem mem_polyExt_iff_proof {R : Type*} [CommRing R] (I : Ideal R) (p : Polynomial R) :
    p ∈ polyExt I ↔ ∀ n, p.coeff n ∈ I :=
  Ideal.mem_map_C_iff

/-! ## A5 — the zero ideal extends to the zero ideal -/

/-- `0[X] = 0`. -/
theorem polyExt_bot {R : Type*} [CommRing R] : polyExt (⊥ : Ideal R) = ⊥ :=
  Ideal.map_bot

/-- Membership in `0[X]` is just vanishing. -/
theorem mem_polyExt_bot_iff {R : Type*} [CommRing R] (p : Polynomial R) :
    p ∈ polyExt (⊥ : Ideal R) ↔ p = 0 := by
  rw [polyExt_bot, Ideal.mem_bot]

/-! ## A6 — pinning down `ω` by a matching upper and lower bound -/

/-- If `I` is `(n+1)`-absorbing but *not* `n`-absorbing then `ω_R(I) = n+1`.
    Both bounds are genuinely used: `≤` is `Nat.sInf_le` applied to the witness
    `n+1`, and `≥` uses that the infimum is attained together with A3′. -/
theorem omegaAbs_eq_succ_of {R : Type*} [CommRing R] {I : Ideal R} {n : ℕ}
    (hup : IsNAbsorbing I (n + 1)) (hlow : ¬ IsNAbsorbing I n) : omegaAbs I = n + 1 := by
  have hmem : (n + 1) ∈ {k : ℕ | 0 < k ∧ IsNAbsorbing I k} := ⟨Nat.succ_pos n, hup⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  replace hlt : omegaAbs I < n + 1 := not_le.1 hlt
  have hattained : omegaAbs I ∈ {k : ℕ | 0 < k ∧ IsNAbsorbing I k} :=
    Nat.sInf_mem (Set.nonempty_of_mem hmem)
  exact hlow (isNAbsorbing_of_le I (Nat.lt_succ_iff.1 hlt) hattained.2)

/-! ## A7 — transport along a ring isomorphism -/

/-- `n`-absorbingness of the zero ideal is invariant under ring isomorphism. -/
theorem isNAbsorbing_congr_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {n : ℕ} (h : IsNAbsorbing (⊥ : Ideal R) n) : IsNAbsorbing (⊥ : Ideal S) n := by
  intro a ha
  rw [Ideal.mem_bot] at ha
  have ha' : (∏ i, e.symm (a i)) ∈ (⊥ : Ideal R) := by
    rw [Ideal.mem_bot, ← map_prod, ha, map_zero]
  obtain ⟨T, hcard, hT⟩ := h (fun i => e.symm (a i)) ha'
  rw [Ideal.mem_bot] at hT
  refine ⟨T, hcard, ?_⟩
  rw [Ideal.mem_bot]
  calc ∏ i ∈ T, a i = e (∏ i ∈ T, e.symm (a i)) := by
        rw [map_prod]
        exact Finset.prod_congr rfl fun i _ => (e.apply_symm_apply (a i)).symm
    _ = e 0 := by rw [hT]
    _ = 0 := map_zero e

end Prob30c
