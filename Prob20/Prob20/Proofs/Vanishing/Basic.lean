/-
# Stage D (★ MILESTONE) — `Prob20/Proofs/Vanishing/`

The test points `u1 N = t(t+1)ᴺ` and `u0 N = tᴺ(t+1)`, the key vanishing lemma
`eval_sub_eval_zero_mem_max_u1` / `_u0`, the "eventually in `𝔪²`" submodules
`Ev1` / `Ev0`, and the frozen non-memberships #11, #12, #13.

The `∃ N₀, ∀ N ≥ N₀` in D.2/D.3 is load-bearing: `f.eval u - f.eval 0 ∈ 𝔪` is
proved only for the specific test points with `N` large, never for a general
`u ∈ 𝔪`.
-/
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac
import Prob20.Proofs.Theta.Basic

namespace Prob20

/-! ### D.1 — the test points -/

/-- `u1 N = t(t+1)ᴺ`, the test family separating `p` and `(t+1)p`. -/
noncomputable def u1 (N : ℕ) : K := tK * (tK + 1) ^ N

/-- `u0 N = tᴺ(t+1)`, the swapped test family, needed for `t·p`. -/
noncomputable def u0 (N : ℕ) : K := tK ^ N * (tK + 1)

/-- `t(t+1)ᴺ ∈ A`. -/
noncomputable def van_uA1 (N : ℕ) : A := Polynomial.X * (Polynomial.X + 1) ^ N

/-- `tᴺ(t+1) ∈ A`. -/
noncomputable def van_uA0 (N : ℕ) : A := Polynomial.X ^ N * (Polynomial.X + 1)

theorem van_tK_add_one : tK + 1 = algebraMap A K (Polynomial.X + 1) := by
  simp [tK]

theorem van_u1_eq (N : ℕ) : u1 N = algebraMap A K (van_uA1 N) := by
  simp [u1, van_uA1, tK]

theorem van_u0_eq (N : ℕ) : u0 N = algebraMap A K (van_uA0 N) := by
  simp [u0, van_uA0, tK]

/-- Membership in `𝔪ʲ` for an element of `A`, read off from divisibility. -/
theorem van_mem_maxPow_algebraMap (a : A) (j : ℕ) :
    algebraMap A K a ∈ maxPow j ↔ piA ^ j ∣ a := by
  have h := mem_maxPow_iff a 1 S.one_mem j
  simpa using h

theorem u1_mem_maxSet (N : ℕ) (hN : 1 ≤ N) : u1 N ∈ maxSet := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [van_u1_eq, van_mem_maxPow_algebraMap, pow_one]
  exact ⟨(Polynomial.X + 1) ^ M, by simp [van_uA1, piA]; ring⟩

theorem u0_mem_maxSet (N : ℕ) (hN : 1 ≤ N) : u0 N ∈ maxSet := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [van_u0_eq, van_mem_maxPow_algebraMap, pow_one]
  exact ⟨Polynomial.X ^ M, by simp [van_uA0, piA]; ring⟩

theorem u1_mem_Dom (N : ℕ) (hN : 1 ≤ N) : u1 N ∈ Dom :=
  max_le_Dom _ (u1_mem_maxSet N hN)

theorem u0_mem_Dom (N : ℕ) (hN : 1 ≤ N) : u0 N ∈ Dom :=
  max_le_Dom _ (u0_mem_maxSet N hN)

/-! ### D.2 — the "small at `t+1`" (resp. `t`) estimate -/

/-- Clearing denominators: every `f : K[X]` has a single `s ≠ 0` in `A` and an
`H : A[X]` with `s · f(y) = H(y)` for every `y : A`. -/
theorem van_common_denom (f : Polynomial K) :
    ∃ (s : A) (H : Polynomial A), s ≠ 0 ∧
      ∀ y : A, algebraMap A K s * f.eval (algebraMap A K y) = algebraMap A K (H.eval y) := by
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) f
  refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors A) f,
    nonZeroDivisors.ne_zero hb, fun y => ?_⟩
  have hev : ((IsLocalization.integerNormalization (nonZeroDivisors A) f).map
      (algebraMap A K)).eval (algebraMap A K y)
      = algebraMap A K ((IsLocalization.integerNormalization (nonZeroDivisors A) f).eval y) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [← hev, hmap]
  simp [Algebra.smul_def]

theorem van_X_dvd_of_eval_zero {h : Polynomial K} (h0 : h.eval 0 = 0) :
    ∃ h₁ : Polynomial K, h = Polynomial.X * h₁ := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff] at h0
  exact h0


theorem van_algebraMap_ne_zero {a : A} (ha : a ≠ 0) : algebraMap A K a ≠ 0 :=
  fun hz => ha (dom_algebraMap_injective (by rw [hz, map_zero]))

/-- **D.2.** For any `h` with `h(0) = 0`, the values `h(u1 N)` are "small at `t+1`"
for all large `N`: with a fixed denominator `d` prime to `t+1`, the numerator is
divisible by `t+1`.  Nothing here uses `h ∈ Int(D)`. -/
theorem van_ord1_of_large (h : Polynomial K) (h0 : h.eval 0 = 0) :
    ∃ d : A, ¬ ((Polynomial.X + 1 : A) ∣ d) ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ a : A, (Polynomial.X + 1 : A) ∣ a ∧
        algebraMap A K d * h.eval (u1 N) = algebraMap A K a := by
  obtain ⟨h₁, rfl⟩ := van_X_dvd_of_eval_zero h0
  obtain ⟨s, H, hs, hH⟩ := van_common_denom h₁
  obtain ⟨e, d, hd, rfl⟩ := WfDvdMonoid.max_power_factor hs dom_irreducible_X_add_one
  refine ⟨d, hd, e + 1, fun N hN => ?_⟩
  obtain ⟨c, hc⟩ : (Polynomial.X + 1 : A) ^ (e + 1) ∣ van_uA1 N * H.eval (van_uA1 N) :=
    Dvd.dvd.mul_right (dvd_trans (pow_dvd_pow _ hN) ⟨Polynomial.X, by rw [van_uA1]; ring⟩) _
  refine ⟨(Polynomial.X + 1) * c, ⟨c, rfl⟩, mul_left_cancel₀
    (van_algebraMap_ne_zero (pow_ne_zero e frac_X_add_one_ne_zero)) ?_⟩
  have hHy := hH (van_uA1 N)
  have hc' : algebraMap A K (van_uA1 N) * algebraMap A K (H.eval (van_uA1 N))
      = (algebraMap A K (Polynomial.X + 1 : A)) ^ (e + 1) * algebraMap A K c := by
    rw [← map_mul, hc, map_mul, map_pow]
  rw [van_u1_eq]
  simp only [map_mul, map_pow, Polynomial.eval_mul, Polynomial.eval_X] at hHy ⊢
  linear_combination (algebraMap A K (van_uA1 N)) * hHy + hc'

/-- Twin of `van_ord1_of_large` for the family `u0` and the prime `t`. -/
theorem van_ord0_of_large (h : Polynomial K) (h0 : h.eval 0 = 0) :
    ∃ d : A, ¬ ((Polynomial.X : A) ∣ d) ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ a : A, (Polynomial.X : A) ∣ a ∧
        algebraMap A K d * h.eval (u0 N) = algebraMap A K a := by
  obtain ⟨h₁, rfl⟩ := van_X_dvd_of_eval_zero h0
  obtain ⟨s, H, hs, hH⟩ := van_common_denom h₁
  obtain ⟨e, d, hd, rfl⟩ := WfDvdMonoid.max_power_factor hs Polynomial.irreducible_X
  refine ⟨d, hd, e + 1, fun N hN => ?_⟩
  obtain ⟨c, hc⟩ : (Polynomial.X : A) ^ (e + 1) ∣ van_uA0 N * H.eval (van_uA0 N) :=
    Dvd.dvd.mul_right (dvd_trans (pow_dvd_pow _ hN) ⟨Polynomial.X + 1, by rw [van_uA0]⟩) _
  have hXne : (Polynomial.X : A) ≠ 0 := Polynomial.X_ne_zero
  refine ⟨Polynomial.X * c, ⟨c, rfl⟩, mul_left_cancel₀
    (van_algebraMap_ne_zero (pow_ne_zero e hXne)) ?_⟩
  have hHy := hH (van_uA0 N)
  have hc' : algebraMap A K (van_uA0 N) * algebraMap A K (H.eval (van_uA0 N))
      = (algebraMap A K (Polynomial.X : A)) ^ (e + 1) * algebraMap A K c := by
    rw [← map_mul, hc, map_mul, map_pow]
  rw [van_u0_eq]
  simp only [map_mul, map_pow, Polynomial.eval_mul, Polynomial.eval_X] at hHy ⊢
  linear_combination (algebraMap A K (van_uA0 N)) * hHy + hc'

/-- Bridge: an element of `T` whose numerator is divisible by `t + 1` (after clearing a
denominator prime to `t + 1`) lies in `𝔫₁`. -/
theorem van_mem_n1_of_mem_T (x : K) (hx : x ∈ T)
    (h : ∃ d a : A, ¬ ((Polynomial.X + 1 : A) ∣ d) ∧ (Polynomial.X + 1 : A) ∣ a ∧
      algebraMap A K d * x = algebraMap A K a) : mem_n1 x := by
  obtain ⟨d, a, hd, ha, hda⟩ := h
  obtain ⟨b, s, hs, rfl⟩ := dom_eq_div_of_mem_T hx
  have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 :=
    mul_inv_cancel₀ (dom_ne_zero_of_mem_S hs)
  have key : d * b = a * s := by
    apply dom_algebraMap_injective
    simp only [map_mul]
    linear_combination (algebraMap A K s) * hda -
      (algebraMap A K d * algebraMap A K b) * h1
  have hdvd : (Polynomial.X + 1 : A) ∣ d * b := key ▸ ha.mul_right s
  refine (dom_mem_n1_iff b s hs).2 ?_
  rcases (dom_irreducible_X_add_one.prime.dvd_mul.1 hdvd) with h' | h'
  · exact absurd h' hd
  · exact h'

/-- Bridge: an element of `T` whose numerator is divisible by `t` (after clearing a
denominator prime to `t`) lies in `𝔫₀`. -/
theorem van_mem_n0_of_mem_T (x : K) (hx : x ∈ T)
    (h : ∃ d a : A, ¬ ((Polynomial.X : A) ∣ d) ∧ (Polynomial.X : A) ∣ a ∧
      algebraMap A K d * x = algebraMap A K a) : mem_n0 x := by
  obtain ⟨d, a, hd, ha, hda⟩ := h
  obtain ⟨b, s, hs, rfl⟩ := dom_eq_div_of_mem_T hx
  have h1 : algebraMap A K s * (algebraMap A K s)⁻¹ = 1 :=
    mul_inv_cancel₀ (dom_ne_zero_of_mem_S hs)
  have key : d * b = a * s := by
    apply dom_algebraMap_injective
    simp only [map_mul]
    linear_combination (algebraMap A K s) * hda -
      (algebraMap A K d * algebraMap A K b) * h1
  have hdvd : (Polynomial.X : A) ∣ d * b := key ▸ ha.mul_right s
  refine (dom_mem_n0_iff b s hs).2 ?_
  rcases (Polynomial.prime_X.dvd_mul.1 hdvd) with h' | h'
  · exact absurd h' hd
  · exact h'

/-! ### D.3 ★ — the key vanishing lemma -/

/-- **D.3 ★ (the key lemma).**  For `f ∈ Int(D)`, the increment `f(u1 N) - f(0)` lies in
`𝔪` for all large `N`.  The `∃ N₀` is load-bearing: the statement is NOT known for a
general element of `𝔪` in place of `u1 N`. -/
theorem eval_sub_eval_zero_mem_max_u1 (f : Polynomial K) (hf : f ∈ IntD) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, f.eval (u1 N) - f.eval 0 ∈ maxSet := by
  have hhInt : f - Polynomial.C (f.eval 0) ∈ IntD :=
    Subalgebra.sub_mem _ hf (C_mem_IntD _ (eval_zero_mem_Dom f hf))
  have hh0 : (f - Polynomial.C (f.eval 0)).eval 0 = 0 := by simp
  obtain ⟨d, hd, N₀, hN₀⟩ := van_ord1_of_large _ hh0
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hev : (f - Polynomial.C (f.eval 0)).eval (u1 N) = f.eval (u1 N) - f.eval 0 := by simp
  have hdom : (f - Polynomial.C (f.eval 0)).eval (u1 N) ∈ Dom :=
    (mem_IntD_iff _).1 hhInt _ (u1_mem_Dom N hN1)
  obtain ⟨a, ha, hda⟩ := hN₀ N (le_trans (le_max_right _ _) hN)
  have hn1 : mem_n1 ((f - Polynomial.C (f.eval 0)).eval (u1 N)) :=
    van_mem_n1_of_mem_T _ (Dom_le_T hdom) ⟨d, a, hd, ha, hda⟩
  rw [← hev]
  exact mem_max_of_mem_Dom_of_mem_n1 _ hdom hn1

/-- **D.3 ★** — the `u0` twin of the key vanishing lemma. -/
theorem eval_sub_eval_zero_mem_max_u0 (f : Polynomial K) (hf : f ∈ IntD) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, f.eval (u0 N) - f.eval 0 ∈ maxSet := by
  have hhInt : f - Polynomial.C (f.eval 0) ∈ IntD :=
    Subalgebra.sub_mem _ hf (C_mem_IntD _ (eval_zero_mem_Dom f hf))
  have hh0 : (f - Polynomial.C (f.eval 0)).eval 0 = 0 := by simp
  obtain ⟨d, hd, N₀, hN₀⟩ := van_ord0_of_large _ hh0
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hev : (f - Polynomial.C (f.eval 0)).eval (u0 N) = f.eval (u0 N) - f.eval 0 := by simp
  have hdom : (f - Polynomial.C (f.eval 0)).eval (u0 N) ∈ Dom :=
    (mem_IntD_iff _).1 hhInt _ (u0_mem_Dom N hN1)
  obtain ⟨a, ha, hda⟩ := hN₀ N (le_trans (le_max_right _ _) hN)
  have hn0 : mem_n0 ((f - Polynomial.C (f.eval 0)).eval (u0 N)) :=
    van_mem_n0_of_mem_T _ (Dom_le_T hdom) ⟨d, a, hd, ha, hda⟩
  rw [← hev]
  exact mem_max_of_mem_Dom_of_mem_n0 _ hdom hn0

/-! ### D.4 — the "eventually in `𝔪²`" submodules -/

theorem van_smul_eval (c : ↥Dom) (G : Polynomial K) (x : K) :
    (c • G).eval x = (c : K) * G.eval x := by
  rw [Algebra.smul_def]
  simp [Polynomial.algebraMap_apply, int_algebraMap_dom_apply]

theorem van_smul_mem_maxPow2 (c : ↥Dom) {z : K} (hz : z ∈ maxPow 2) :
    (c : K) * z ∈ maxPow 2 :=
  (maxPow 2).smul_mem (⟨(c : K), Dom_le_T c.2⟩ : ↥T) hz

/-- **D.4.** `G` is eventually congruent to `G(0)` modulo `𝔪²` along the family `u1`.
Note `𝔪²`, not `𝔪`: with `𝔪` the whole argument collapses. -/
noncomputable def Ev1 : Submodule ↥Dom (Polynomial K) where
  carrier :=
    {G : Polynomial K | ∃ N₀ : ℕ, ∀ N ≥ N₀, G.eval (u1 N) - G.eval 0 ∈ maxPow 2}
  zero_mem' := ⟨0, fun N _ => by simp⟩
  add_mem' := by
    rintro F G ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hsplit : (F + G).eval (u1 N) - (F + G).eval 0
        = (F.eval (u1 N) - F.eval 0) + (G.eval (u1 N) - G.eval 0) := by
      simp only [Polynomial.eval_add]; ring
    rw [hsplit]
    exact (maxPow 2).add_mem (h₁ N (le_trans (le_max_left _ _) hN))
      (h₂ N (le_trans (le_max_right _ _) hN))
  smul_mem' := by
    rintro c G ⟨N₀, h₀⟩
    refine ⟨N₀, fun N hN => ?_⟩
    have hsplit : (c • G).eval (u1 N) - (c • G).eval 0
        = (c : K) * (G.eval (u1 N) - G.eval 0) := by
      rw [van_smul_eval, van_smul_eval]; ring
    rw [hsplit]
    exact van_smul_mem_maxPow2 c (h₀ N hN)

/-- **D.4.** The `u0` twin of `Ev1`. -/
noncomputable def Ev0 : Submodule ↥Dom (Polynomial K) where
  carrier :=
    {G : Polynomial K | ∃ N₀ : ℕ, ∀ N ≥ N₀, G.eval (u0 N) - G.eval 0 ∈ maxPow 2}
  zero_mem' := ⟨0, fun N _ => by simp⟩
  add_mem' := by
    rintro F G ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hsplit : (F + G).eval (u0 N) - (F + G).eval 0
        = (F.eval (u0 N) - F.eval 0) + (G.eval (u0 N) - G.eval 0) := by
      simp only [Polynomial.eval_add]; ring
    rw [hsplit]
    exact (maxPow 2).add_mem (h₁ N (le_trans (le_max_left _ _) hN))
      (h₂ N (le_trans (le_max_right _ _) hN))
  smul_mem' := by
    rintro c G ⟨N₀, h₀⟩
    refine ⟨N₀, fun N hN => ?_⟩
    have hsplit : (c • G).eval (u0 N) - (c • G).eval 0
        = (c : K) * (G.eval (u0 N) - G.eval 0) := by
      rw [van_smul_eval, van_smul_eval]; ring
    rw [hsplit]
    exact van_smul_mem_maxPow2 c (h₀ N hN)

/-! ### D.5 — `𝔪·Int(D)` sits inside both `Ev` submodules -/

/-- **D.5.** Every element of `𝔪·Int(D)` is eventually in `𝔪²` along `u1`. -/
theorem maxSmulInt_le_Ev1 : maxSmulInt ≤ Ev1 := by
  refine Submodule.span_le.2 ?_
  rintro G ⟨c, hc, f, hf, rfl⟩
  obtain ⟨N₀, hN₀⟩ := eval_sub_eval_zero_mem_max_u1 f hf
  refine ⟨N₀, fun N hN => ?_⟩
  have hsplit : (Polynomial.C c * f).eval (u1 N) - (Polynomial.C c * f).eval 0
      = c * (f.eval (u1 N) - f.eval 0) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C]; ring
  rw [hsplit]
  exact maxPow_mul_maxPow hc (hN₀ N hN)

/-- **D.5.** The `u0` twin. -/
theorem maxSmulInt_le_Ev0 : maxSmulInt ≤ Ev0 := by
  refine Submodule.span_le.2 ?_
  rintro G ⟨c, hc, f, hf, rfl⟩
  obtain ⟨N₀, hN₀⟩ := eval_sub_eval_zero_mem_max_u0 f hf
  refine ⟨N₀, fun N hN => ?_⟩
  have hsplit : (Polynomial.C c * f).eval (u0 N) - (Polynomial.C c * f).eval 0
      = c * (f.eval (u0 N) - f.eval 0) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_C]; ring
  rw [hsplit]
  exact maxPow_mul_maxPow hc (hN₀ N hN)

/-! ### D.6 — the three frozen non-memberships (#11, #12, #13)

The three proofs are deliberately NOT unified: `p` and `(t+1)p` are separated by the
family `u1 N = t(t+1)ᴺ`, while `t·p` genuinely needs the swapped family
`u0 N = tᴺ(t+1)`.  See the `📝` PROGRESS entry recording this asymmetry. -/

/-- If `w(0) ≠ 0` then `π² ∤ t·w`: the `t`-adic order of `t·w` is exactly one. -/
theorem van_not_dvd_piA_sq_X (w : A) (hw : w.eval 0 ≠ 0) :
    ¬ (piA ^ 2 ∣ Polynomial.X * w) := by
  rintro ⟨k, hk⟩
  have hX : (Polynomial.X : A) ≠ 0 := Polynomial.X_ne_zero
  have h2 : Polynomial.X * w
      = Polynomial.X * (Polynomial.X * (Polynomial.X + 1) ^ 2 * k) := by
    rw [hk, piA]; ring
  have h3 : w = Polynomial.X * ((Polynomial.X + 1) ^ 2 * k) := by
    rw [mul_left_cancel₀ hX h2]; ring
  exact hw (by rw [h3]; simp)

/-- If `w(1) ≠ 0` then `π² ∤ (t+1)·w`: the `(t+1)`-adic order of `(t+1)·w` is exactly one. -/
theorem van_not_dvd_piA_sq_X_add_one (w : A) (hw : w.eval 1 ≠ 0) :
    ¬ (piA ^ 2 ∣ (Polynomial.X + 1) * w) := by
  rintro ⟨k, hk⟩
  have h2 : (Polynomial.X + 1) * w
      = (Polynomial.X + 1) * ((Polynomial.X + 1) * Polynomial.X ^ 2 * k) := by
    rw [hk, piA]; ring
  have h3 : w = (Polynomial.X + 1) * (Polynomial.X ^ 2 * k) := by
    rw [mul_left_cancel₀ frac_X_add_one_ne_zero h2]; ring
  exact hw (by rw [h3]; simp [frac_two_eq_zero])

/-- The cofactor of `t` in the numerator of `p(u1 N)`. -/
noncomputable def van_w1 (N : ℕ) : A := (Polynomial.X + 1) ^ N * (van_uA1 N + 1)

/-- The cofactor of `t+1` in the numerator of `t·p(u0 N)` (up to one factor of `t`). -/
noncomputable def van_w0 (N : ℕ) : A := Polynomial.X ^ N * (van_uA0 N + 1)

theorem van_w1_eval_zero (N : ℕ) : (van_w1 N).eval 0 = 1 := by
  simp [van_w1, van_uA1]

theorem van_w0_eval_one (N : ℕ) : (van_w0 N).eval 1 = 1 := by
  simp [van_w0, van_uA0, frac_two_eq_zero]

theorem van_p_eval (x : K) : p.eval x = x * x + x := by
  simp only [p, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]; ring

theorem van_C_mul_p_eval (c x : K) : (Polynomial.C c * p).eval x = c * (x * x + x) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, van_p_eval]

theorem van_p_eval_zero : p.eval (0 : K) = 0 := by simp [van_p_eval]

theorem van_C_mul_p_eval_zero (c : K) : (Polynomial.C c * p).eval 0 = 0 := by
  rw [van_C_mul_p_eval]; ring

theorem van_p_eval_u1 (N : ℕ) :
    p.eval (u1 N) = algebraMap A K (Polynomial.X * van_w1 N) := by
  rw [van_p_eval, van_u1_eq, ← map_mul, ← map_add]
  congr 1
  simp only [van_w1, van_uA1]; ring

theorem van_t_add_one_mul_p_eval_u1 (N : ℕ) :
    (Polynomial.C (tK + 1) * p).eval (u1 N)
      = algebraMap A K (Polynomial.X * ((Polynomial.X + 1) * van_w1 N)) := by
  rw [van_C_mul_p_eval, van_tK_add_one, van_u1_eq, ← map_mul, ← map_add, ← map_mul]
  congr 1
  simp only [van_w1, van_uA1]; ring

theorem van_t_mul_p_eval_u0 (N : ℕ) :
    (Polynomial.C tK * p).eval (u0 N)
      = algebraMap A K ((Polynomial.X + 1) * (Polynomial.X * van_w0 N)) := by
  simp only [tK]
  rw [van_C_mul_p_eval, van_u0_eq, ← map_mul, ← map_add, ← map_mul]
  congr 1
  simp only [van_w0, van_uA0]; ring

/-- **#11.** `p ∉ 𝔪·Int(D)`. -/
theorem p_not_mem_max_int_proof : p ∉ maxSmulInt := by
  intro hp
  obtain ⟨N₀, hN₀⟩ := maxSmulInt_le_Ev1 hp
  have h := hN₀ N₀ le_rfl
  rw [van_p_eval_zero, sub_zero, van_p_eval_u1, van_mem_maxPow_algebraMap] at h
  refine van_not_dvd_piA_sq_X (van_w1 N₀) ?_ h
  rw [van_w1_eval_zero]; decide

/-- **#13.** `(t+1)·p ∉ 𝔪·Int(D)` — same test family `u1` as for `p`. -/
theorem t_add_one_mul_p_not_mem_max_int_proof :
    Polynomial.C (tK + 1) * p ∉ maxSmulInt := by
  intro hp
  obtain ⟨N₀, hN₀⟩ := maxSmulInt_le_Ev1 hp
  have h := hN₀ N₀ le_rfl
  rw [van_C_mul_p_eval_zero, sub_zero, van_t_add_one_mul_p_eval_u1,
    van_mem_maxPow_algebraMap] at h
  refine van_not_dvd_piA_sq_X ((Polynomial.X + 1) * van_w1 N₀) ?_ h
  simp only [Polynomial.eval_mul, van_w1_eval_zero, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, zero_add, mul_one]
  decide

/-- **#12.** `t·p ∉ 𝔪·Int(D)` — this one needs the SWAPPED family `u0`. -/
theorem t_mul_p_not_mem_max_int_proof : Polynomial.C tK * p ∉ maxSmulInt := by
  intro hp
  obtain ⟨N₀, hN₀⟩ := maxSmulInt_le_Ev0 hp
  have h := hN₀ N₀ le_rfl
  rw [van_C_mul_p_eval_zero, sub_zero, van_t_mul_p_eval_u0,
    van_mem_maxPow_algebraMap] at h
  refine van_not_dvd_piA_sq_X_add_one (Polynomial.X * van_w0 N₀) ?_ h
  simp only [Polynomial.eval_mul, van_w0_eval_one, Polynomial.eval_X, mul_one]
  decide

/-! ### Guardrails — the witness lives exactly between `𝔪` and `𝔪²` -/

example : p.eval (u1 1) ∈ maxSet := by
  rw [van_p_eval_u1, van_mem_maxPow_algebraMap, pow_one]
  exact ⟨Polynomial.X * (Polynomial.X + 1) + 1, by simp only [van_w1, van_uA1, piA]; ring⟩

example : p.eval (u1 1) ∉ maxPow 2 := by
  rw [van_p_eval_u1, van_mem_maxPow_algebraMap]
  refine van_not_dvd_piA_sq_X (van_w1 1) ?_
  rw [van_w1_eval_zero]; decide

end Prob20
