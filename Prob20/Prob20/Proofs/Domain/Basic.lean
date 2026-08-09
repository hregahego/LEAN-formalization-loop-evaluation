/-
# Stage A — the elementary arithmetic of `S`, `T`, `π`, `𝔪ʲ` and `D`

This module implements BLUEPRINT Part 2 Stage A items **A1, A2, A3, A5**:

* **A1** unfolding lemmas for `T` and `S`, and the two basic membership facts
  `algebraMap A K a ∈ T`, `(algebraMap A K s)⁻¹ ∈ T` for `s ∈ S`;
* **A2** the workhorse `mem_maxPow_iff`, characterising membership in `𝔪ʲ = πʲT`
  by the divisibility `πʲ ∣ a` in `𝔽₂[t]`, plus the bookkeeping corollaries
  `mul_mem_maxPow`, `maxPow_succ_le`, `maxPow_mul_maxPow`;
* **A3** the two primes `𝔫₀ = tT` and `𝔫₁ = (t+1)T` (as predicates `mem_n0`,
  `mem_n1` on elements of `K`), the CRT identity `𝔪 = 𝔫₀ ⊓ 𝔫₁`, their primality,
  and the two facts Stage D consumes about `D`-elements lying in `𝔫ᵢ`;
* **A5** the residue computation `x ∈ T → x*x + x ∈ 𝔪`.

Everything is a divisibility statement in `A = 𝔽₂[t]`; `T` is never assumed to be
a PID / Dedekind / Noetherian ring.

Support lemmas that are not named by the blueprint are prefixed `dom_`.
-/
import Prob20.Defs

namespace Prob20

/-! ### A1 — unfolding `T` and `S` -/

/-- `algebraMap A K` is injective (`K = Frac A`). -/
theorem dom_algebraMap_injective : Function.Injective (algebraMap A K) :=
  RatFunc.algebraMap_injective (ZMod 2)

/-- An element of `S` is nonzero in `K`. -/
theorem dom_ne_zero_of_mem_S {s : A} (hs : s ∈ S) : algebraMap A K s ≠ 0 := by
  intro h
  have hs0 : s = 0 := dom_algebraMap_injective (by simpa using h)
  exact hs.1 (by simp [hs0])

/-- **A1.** Membership in `T = S⁻¹A ⊆ K`, spelled out. -/
theorem mem_T_iff (x : K) :
    x ∈ T ↔ ∃ a : A, ∃ s ∈ S, algebraMap A K s * x = algebraMap A K a :=
  Iff.rfl

/-- `t + 1 = t - 1` in `𝔽₂[t]`. -/
theorem dom_X_add_one_eq : (Polynomial.X + 1 : A) = Polynomial.X - Polynomial.C 1 := by
  rw [Polynomial.C_1, sub_eq_add_neg, CharTwo.neg_eq]

/-- Divisibility by `t` is evaluation at `0`. -/
theorem dom_X_dvd_iff (a : A) : Polynomial.X ∣ a ↔ a.eval 0 = 0 := by
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]

/-- Divisibility by `t + 1` is evaluation at `1`. -/
theorem dom_X_add_one_dvd_iff (a : A) : (Polynomial.X + 1 : A) ∣ a ↔ a.eval 1 = 0 := by
  rw [dom_X_add_one_eq, Polynomial.dvd_iff_isRoot]
  rfl

/-- **A1.** `S = A ∖ ((t) ∪ (t+1))`. -/
theorem mem_S_iff_not_dvd (a : A) :
    a ∈ S ↔ ¬ (Polynomial.X ∣ a) ∧ ¬ ((Polynomial.X + 1) ∣ a) := by
  rw [dom_X_dvd_iff, dom_X_add_one_dvd_iff]
  exact Iff.rfl

/-- **A1.** Every element of `A` lies in `T`. -/
theorem algebraMap_mem_T (a : A) : algebraMap A K a ∈ T := ⟨a, 1, S.one_mem, by simp⟩

/-- **A1.** Every element of `S` is invertible in `T`. -/
theorem inv_algebraMap_mem_T (s : A) (hs : s ∈ S) : (algebraMap A K s)⁻¹ ∈ T :=
  ⟨1, s, hs, by rw [map_one, mul_inv_cancel₀ (dom_ne_zero_of_mem_S hs)]⟩

/-- Every element of `T` is a fraction `a / s` with `s ∈ S`. -/
theorem dom_eq_div_of_mem_T {x : K} (hx : x ∈ T) :
    ∃ a s : A, s ∈ S ∧ x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  obtain ⟨a, s, hs, h⟩ := hx
  have hsne := dom_ne_zero_of_mem_S hs
  exact ⟨a, s, hs, by field_simp; linear_combination h⟩

/-! ### A2 — `mem_maxPow_iff`, the workhorse -/

/-- `t + 1` is irreducible in `𝔽₂[t]`. -/
theorem dom_irreducible_X_add_one : Irreducible (Polynomial.X + 1 : A) := by
  rw [dom_X_add_one_eq]
  exact Polynomial.irreducible_X_sub_C 1

/-- `t` is coprime to every element of `S`. -/
theorem dom_coprime_X {s : A} (hs : s ∈ S) : IsCoprime (Polynomial.X : A) s :=
  Polynomial.irreducible_X.coprime_iff_not_dvd.2 ((mem_S_iff_not_dvd s).1 hs).1

/-- `t + 1` is coprime to every element of `S`. -/
theorem dom_coprime_X_add_one {s : A} (hs : s ∈ S) : IsCoprime (Polynomial.X + 1 : A) s :=
  dom_irreducible_X_add_one.coprime_iff_not_dvd.2 ((mem_S_iff_not_dvd s).1 hs).2

/-- `π = t(t+1)` is coprime to every element of `S`. -/
theorem dom_coprime_piA {s : A} (hs : s ∈ S) : IsCoprime piA s :=
  (dom_coprime_X hs).mul_left (dom_coprime_X_add_one hs)

/-- `t` and `t + 1` are coprime. -/
theorem dom_coprime_X_X_add_one : IsCoprime (Polynomial.X : A) (Polynomial.X + 1) :=
  ⟨-1, 1, by ring⟩

/-- `t ∣ π`. -/
theorem dom_X_dvd_piA : (Polynomial.X : A) ∣ piA := ⟨Polynomial.X + 1, rfl⟩

/-- `t + 1 ∣ π`. -/
theorem dom_X_add_one_dvd_piA : (Polynomial.X + 1 : A) ∣ piA := ⟨Polynomial.X, mul_comm _ _⟩

/-- **A2, the workhorse.** For `a : A` and `s ∈ S`, the fraction `a/s` lies in `𝔪ʲ = πʲT`
exactly when `πʲ` divides the numerator `a`. -/
theorem mem_maxPow_iff (a s : A) (hs : s ∈ S) (j : ℕ) :
    algebraMap A K a * (algebraMap A K s)⁻¹ ∈ maxPow j ↔ piA ^ j ∣ a := by
  have hsne := dom_ne_zero_of_mem_S hs
  constructor
  · rintro ⟨y, ⟨b, s', hs', hb⟩, hxy⟩
    have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 := mul_inv_cancel₀ hsne
    simp only [piK] at hxy
    have key : a * s' = piA ^ j * b * s := by
      apply dom_algebraMap_injective
      simp only [map_mul, map_pow]
      linear_combination (algebraMap A K s * algebraMap A K s') * hxy +
        ((algebraMap A K piA) ^ j * algebraMap A K s) * hb -
        (algebraMap A K a * algebraMap A K s') * h1
    exact ((dom_coprime_piA hs').pow_left).dvd_of_dvd_mul_right ⟨b * s, by rw [key]; ring⟩
  · rintro ⟨b, rfl⟩
    refine ⟨algebraMap A K b * (algebraMap A K s)⁻¹,
      T.mul_mem (algebraMap_mem_T b) (inv_algebraMap_mem_T s hs), ?_⟩
    simp only [piK, map_mul, map_pow, mul_assoc]

/-- **A2.** `πʲ·y ∈ 𝔪ʲ` for every `y ∈ T`. -/
theorem mul_mem_maxPow (j : ℕ) (y : K) (hy : y ∈ T) : piK ^ j * y ∈ maxPow j :=
  ⟨y, hy, rfl⟩

/-- `π ∈ T`. -/
theorem dom_piK_mem_T : piK ∈ T := algebraMap_mem_T piA

/-- **A2.** The filtration is decreasing. -/
theorem maxPow_succ_le (j : ℕ) : maxPow (j + 1) ≤ maxPow j := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨piK * y, T.mul_mem dom_piK_mem_T hy, by ring⟩

/-- **A2.** `𝔪ⁱ · 𝔪ʲ ⊆ 𝔪ⁱ⁺ʲ`. -/
theorem maxPow_mul_maxPow {i j : ℕ} {x y : K} (hx : x ∈ maxPow i) (hy : y ∈ maxPow j) :
    x * y ∈ maxPow (i + j) := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, T.mul_mem hu hv, by rw [pow_add]; ring⟩

/-- Every element of `𝔪ʲ` lies in `T`. -/
theorem dom_mem_T_of_mem_maxPow {j : ℕ} {x : K} (hx : x ∈ maxPow j) : x ∈ T := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact T.mul_mem (T.pow_mem dom_piK_mem_T j) hy

/-! ### A3 — the two primes `𝔫₀ = tT` and `𝔫₁ = (t+1)T` -/

/-- `x ∈ 𝔫₀ = tT`, spelled out as "`x = a/s` with `t ∣ a` and `s ∈ S`". -/
def mem_n0 (x : K) : Prop :=
  ∃ a s : A, s ∈ S ∧ Polynomial.X ∣ a ∧ algebraMap A K s * x = algebraMap A K a

/-- `x ∈ 𝔫₁ = (t+1)T`, spelled out as "`x = a/s` with `t + 1 ∣ a` and `s ∈ S`". -/
def mem_n1 (x : K) : Prop :=
  ∃ a s : A, s ∈ S ∧ (Polynomial.X + 1) ∣ a ∧ algebraMap A K s * x = algebraMap A K a

/-- An element of `𝔫₀` lies in `T`. -/
theorem dom_mem_T_of_mem_n0 {x : K} (hx : mem_n0 x) : x ∈ T := by
  obtain ⟨a, s, hs, _, h⟩ := hx
  exact ⟨a, s, hs, h⟩

/-- An element of `𝔫₁` lies in `T`. -/
theorem dom_mem_T_of_mem_n1 {x : K} (hx : mem_n1 x) : x ∈ T := by
  obtain ⟨a, s, hs, _, h⟩ := hx
  exact ⟨a, s, hs, h⟩

/-- `a/s ∈ 𝔫₀` iff `t ∣ a`. -/
theorem dom_mem_n0_iff (a s : A) (hs : s ∈ S) :
    mem_n0 (algebraMap A K a * (algebraMap A K s)⁻¹) ↔ Polynomial.X ∣ a := by
  have hsne := dom_ne_zero_of_mem_S hs
  have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 := mul_inv_cancel₀ hsne
  constructor
  · rintro ⟨b, r, hr, ⟨b', rfl⟩, hbr⟩
    have key : a * r = Polynomial.X * b' * s := by
      apply dom_algebraMap_injective
      simp only [map_mul] at hbr ⊢
      linear_combination (algebraMap A K s) * hbr -
        (algebraMap A K a * algebraMap A K r) * h1
    exact (dom_coprime_X hr).dvd_of_dvd_mul_right ⟨b' * s, by rw [key]; ring⟩
  · intro ha
    exact ⟨a, s, hs, ha, by linear_combination (algebraMap A K a) * h1⟩

/-- `a/s ∈ 𝔫₁` iff `t + 1 ∣ a`. -/
theorem dom_mem_n1_iff (a s : A) (hs : s ∈ S) :
    mem_n1 (algebraMap A K a * (algebraMap A K s)⁻¹) ↔ (Polynomial.X + 1 : A) ∣ a := by
  have hsne := dom_ne_zero_of_mem_S hs
  have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 := mul_inv_cancel₀ hsne
  constructor
  · rintro ⟨b, r, hr, ⟨b', rfl⟩, hbr⟩
    have key : a * r = (Polynomial.X + 1) * b' * s := by
      apply dom_algebraMap_injective
      simp only [map_mul] at hbr ⊢
      linear_combination (algebraMap A K s) * hbr -
        (algebraMap A K a * algebraMap A K r) * h1
    exact (dom_coprime_X_add_one hr).dvd_of_dvd_mul_right ⟨b' * s, by rw [key]; ring⟩
  · intro ha
    exact ⟨a, s, hs, ha, by linear_combination (algebraMap A K a) * h1⟩

/-- **A3.** `𝔪 = 𝔫₀ ⊓ 𝔫₁` — this is the CRT identity `t ∣ a ∧ (t+1) ∣ a ↔ t(t+1) ∣ a`. -/
theorem mem_maxSet_iff (x : K) : x ∈ maxSet ↔ (mem_n0 x ∧ mem_n1 x) := by
  constructor
  · intro hx
    obtain ⟨a, s, hs, rfl⟩ := dom_eq_div_of_mem_T (dom_mem_T_of_mem_maxPow hx)
    rw [mem_maxPow_iff a s hs 1, pow_one] at hx
    exact ⟨(dom_mem_n0_iff a s hs).2 (dom_X_dvd_piA.trans hx),
      (dom_mem_n1_iff a s hs).2 (dom_X_add_one_dvd_piA.trans hx)⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨a, s, hs, rfl⟩ := dom_eq_div_of_mem_T (dom_mem_T_of_mem_n0 h0)
    rw [mem_maxPow_iff a s hs 1, pow_one]
    exact dom_coprime_X_X_add_one.mul_dvd ((dom_mem_n0_iff a s hs).1 h0)
      ((dom_mem_n1_iff a s hs).1 h1)

/-- **A3.** `𝔫₀` is prime. -/
theorem n0_prime (x y : K) (hx : x ∈ T) (hy : y ∈ T) (hxy : mem_n0 (x * y)) :
    mem_n0 x ∨ mem_n0 y := by
  obtain ⟨a, s, hs, rfl⟩ := dom_eq_div_of_mem_T hx
  obtain ⟨b, r, hr, rfl⟩ := dom_eq_div_of_mem_T hy
  have hprod : algebraMap A K a * (algebraMap A K s)⁻¹ * (algebraMap A K b * (algebraMap A K r)⁻¹)
      = algebraMap A K (a * b) * (algebraMap A K (s * r))⁻¹ := by
    simp only [map_mul, mul_inv]
    ring
  rw [hprod, dom_mem_n0_iff _ _ (S.mul_mem hs hr)] at hxy
  rcases Polynomial.prime_X.2.2 a b hxy with h | h
  · exact Or.inl ((dom_mem_n0_iff a s hs).2 h)
  · exact Or.inr ((dom_mem_n0_iff b r hr).2 h)

/-- **A3.** `𝔫₁` is prime. -/
theorem n1_prime (x y : K) (hx : x ∈ T) (hy : y ∈ T) (hxy : mem_n1 (x * y)) :
    mem_n1 x ∨ mem_n1 y := by
  obtain ⟨a, s, hs, rfl⟩ := dom_eq_div_of_mem_T hx
  obtain ⟨b, r, hr, rfl⟩ := dom_eq_div_of_mem_T hy
  have hprod : algebraMap A K a * (algebraMap A K s)⁻¹ * (algebraMap A K b * (algebraMap A K r)⁻¹)
      = algebraMap A K (a * b) * (algebraMap A K (s * r))⁻¹ := by
    simp only [map_mul, mul_inv]
    ring
  rw [hprod, dom_mem_n1_iff _ _ (S.mul_mem hs hr)] at hxy
  rcases dom_irreducible_X_add_one.prime.2.2 a b hxy with h | h
  · exact Or.inl ((dom_mem_n1_iff a s hs).2 h)
  · exact Or.inr ((dom_mem_n1_iff b r hr).2 h)

/-! ### A4 (the two facts Stage D.3 consumes) -/

/-- A `D`-element lying in `𝔫₀` already lies in `𝔪`: its constant term cannot be `1`. -/
theorem mem_max_of_mem_Dom_of_mem_n0 (x : K) (hx : x ∈ Dom) (h0 : mem_n0 x) : x ∈ maxSet := by
  obtain ⟨c, y, hy, hxc⟩ := hx
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · exact ⟨y, hy, by rw [hxc]; simp⟩
  · exfalso
    obtain ⟨a, s, hs, hrep⟩ := dom_eq_div_of_mem_T (dom_mem_T_of_mem_n0 h0)
    have hsne := dom_ne_zero_of_mem_S hs
    have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 := mul_inv_cancel₀ hsne
    have hsub : algebraMap A K (a - s) * (algebraMap A K s)⁻¹ ∈ maxPow 1 := by
      refine ⟨y, hy, ?_⟩
      rw [map_sub]
      have : x = algebraMap A K a * (algebraMap A K s)⁻¹ := hrep
      rw [hxc] at this
      simp only [map_one] at this
      linear_combination -this - h1
    rw [mem_maxPow_iff (a - s) s hs 1, pow_one] at hsub
    have hXa : Polynomial.X ∣ a := (dom_mem_n0_iff a s hs).1 (hrep ▸ h0)
    have hXs : Polynomial.X ∣ s := by
      have := dom_X_dvd_piA.trans hsub
      simpa using dvd_sub hXa this
    exact ((mem_S_iff_not_dvd s).1 hs).1 hXs

/-- A `D`-element lying in `𝔫₁` already lies in `𝔪`: its constant term cannot be `1`. -/
theorem mem_max_of_mem_Dom_of_mem_n1 (x : K) (hx : x ∈ Dom) (h1' : mem_n1 x) : x ∈ maxSet := by
  obtain ⟨c, y, hy, hxc⟩ := hx
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · exact ⟨y, hy, by rw [hxc]; simp⟩
  · exfalso
    obtain ⟨a, s, hs, hrep⟩ := dom_eq_div_of_mem_T (dom_mem_T_of_mem_n1 h1')
    have hsne := dom_ne_zero_of_mem_S hs
    have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 := mul_inv_cancel₀ hsne
    have hsub : algebraMap A K (a - s) * (algebraMap A K s)⁻¹ ∈ maxPow 1 := by
      refine ⟨y, hy, ?_⟩
      rw [map_sub]
      have : x = algebraMap A K a * (algebraMap A K s)⁻¹ := hrep
      rw [hxc] at this
      simp only [map_one] at this
      linear_combination -this - h1
    rw [mem_maxPow_iff (a - s) s hs 1, pow_one] at hsub
    have hXa : (Polynomial.X + 1 : A) ∣ a := (dom_mem_n1_iff a s hs).1 (hrep ▸ h1')
    have hXs : (Polynomial.X + 1 : A) ∣ s := by
      have := dom_X_add_one_dvd_piA.trans hsub
      simpa using dvd_sub hXa this
    exact ((mem_S_iff_not_dvd s).1 hs).2 hXs

/-! ### A5 — residue arithmetic: both residue fields of `T` are `𝔽₂` -/

/-- **A5.** For every `x ∈ T`, `x² + x ∈ 𝔪`.  Both residue fields of `T` are `𝔽₂`, so
`x² + x` vanishes at `t = 0` and at `t = 1`. -/
theorem mul_self_add_self_mem_max (x : K) (hx : x ∈ T) : x * x + x ∈ maxSet := by
  obtain ⟨a, s, hs, rfl⟩ := dom_eq_div_of_mem_T hx
  have hsne := dom_ne_zero_of_mem_S hs
  have hrep : algebraMap A K a * (algebraMap A K s)⁻¹ * (algebraMap A K a * (algebraMap A K s)⁻¹)
      + algebraMap A K a * (algebraMap A K s)⁻¹
      = algebraMap A K (a * a + a * s) * (algebraMap A K (s * s))⁻¹ := by
    simp only [map_mul, map_add, mul_inv]
    field_simp
  rw [hrep, mem_maxPow_iff _ _ (S.mul_mem hs hs) 1, pow_one]
  have key : ∀ u v : ZMod 2, v ≠ 0 → u * u + u * v = 0 := by decide
  refine dom_coprime_X_X_add_one.mul_dvd ?_ ?_
  · rw [dom_X_dvd_iff]
    simpa using key (a.eval 0) (s.eval 0) hs.1
  · rw [dom_X_add_one_dvd_iff]
    simpa using key (a.eval 1) (s.eval 1) hs.2

/-! ### Guardrails (BLUEPRINT Stage A cheat-watch) -/

example : piK ∈ maxSet := ⟨1, T.one_mem, by simp⟩

example : (1 : K) ∉ maxSet := by
  intro h
  have h2 : algebraMap A K 1 * (algebraMap A K 1)⁻¹ ∈ maxPow 1 := by simpa using h
  rw [mem_maxPow_iff 1 1 S.one_mem 1, pow_one] at h2
  have h3 : (Polynomial.X : A) ∣ 1 := dom_X_dvd_piA.trans h2
  rw [dom_X_dvd_iff] at h3
  simp only [Polynomial.eval_one] at h3
  exact one_ne_zero h3

example : tK ∈ T := algebraMap_mem_T Polynomial.X

example : piK * tK ∈ Dom := ⟨0, tK, algebraMap_mem_T Polynomial.X, by simp⟩

end Prob20
