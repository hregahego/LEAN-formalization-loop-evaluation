import Erdos477.Defs
import Erdos477.Proofs.Elementary.Basic
import Erdos477.Proofs.Greedy.Basic
import Erdos477.Proofs.BadShift.Basic

/-!
# Stage G — assembly (Prop 5.2 and the headline theorem, SKETCH §8)

This file carries BLUEPRINT §"Stage G" steps G1 and G2 in **conditional** form:
the only ingredient that is not yet available is the frozen `badShift_bound`
(Stage E step E4, which waits on Stage C4 `no_linear_param`), so it is taken here
as an explicit hypothesis of exactly its own shape.

* `good_shift_exists_of_bound` — G1, the pigeonhole of SKETCH §8.1. Assuming the
  bad-shift estimate `|S_c(T)| ≤ K_c · T^{5/6}` for every `c ∉ B`, the set `B` of
  thirteenth powers satisfies the greedy criterion. Its conclusion is exactly the
  frozen `good_shift_exists` (`Erdos477/Theorems.lean:110-111`).
* `erdos_477_of_good_shift` — G2, SKETCH §8.2. Its hypothesis is exactly the
  frozen `good_shift_exists` and its conclusion is exactly the frozen `erdos_477`
  (`Erdos477/Theorems.lean:114-115`), so this discharges the whole of G2 already.

Neither declaration is named `<frozen name>_proof`: both take an extra hypothesis
on purpose and must never be mistaken for the frozen theorems.

Support declarations go in `namespace Erdos477` and must never shadow a frozen
name from `Erdos477/Defs.lean` or `Erdos477/Theorems.lean`.
-/

namespace Erdos477

/-! ## G1 — the greedy criterion for `Bset`, conditional on the bad-shift bound -/

/-- **BLUEPRINT Stage G, step G1 / SKETCH §8.1 (paper's Proposition 5.2), in
conditional form.**

Given the bad-shift estimate `hbb` (which is exactly the frozen `badShift_bound`,
still `sorry` at the time of writing and therefore taken as a hypothesis here),
the set `Bset` of thirteenth powers satisfies hypothesis `(H)` of the greedy
tiling criterion: every finite `C ⊆ ℤ \ Bset` admits a `b ∈ Bset` with
`c - b ∉ Dset` for all `c ∈ C`.

The proof is the strict pigeonhole: with `K := ∑_{c ∈ C} K_c` and any integer
`T > K^6` we get
`|⋃_{c ∈ C} S_c(T)| ≤ K·T^{5/6} < T^{1/6}·T^{5/6} = T < 2T+1 = |[-T, T] ∩ ℤ|`,
so some `t₀` with `|t₀| ≤ T` is bad for no `c ∈ C`; take `b := t₀ ^ 13`. -/
theorem good_shift_exists_of_bound
    (hbb : ∀ c : ℤ, c ∉ Bset → ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6))
    (C : Finset ℤ) (hC : ∀ c ∈ C, c ∉ Bset) :
    ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset := by
  -- The empty case is real and easy: `b := 0`.
  rcases Finset.eq_empty_or_nonempty C with rfl | -
  · exact ⟨0, zero_mem_Bset_proof, by simp⟩
  -- Pick one constant `K c` per `c ∈ C` (junk value off `C`).
  have hKex : ∀ c : ℤ, ∃ K : ℝ, c ∈ C → ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6) := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨K, -, hK⟩ := hbb c (hC c hc)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose K hK using hKex
  set Ksum : ℝ := ∑ c ∈ C, K c with hKsum
  -- `T := (⌈Ksum⌉₊ + 1) ^ 6`, chosen AFTER `K` and never appearing in a statement.
  set m : ℕ := ⌈Ksum⌉₊ + 1 with hm
  set T : ℤ := ((m ^ 6 : ℕ) : ℤ) with hTdef
  have hmpos : 0 < m := Nat.succ_pos _
  have hT1 : (1 : ℤ) ≤ T := by
    have h : 1 ≤ m ^ 6 := Nat.one_le_pow _ _ hmpos
    rw [hTdef]
    exact_mod_cast h
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hT1
  -- `Ksum < T ^ (1/6)`, i.e. `Ksum < m`.
  have hTm : (T : ℝ) ^ ((1 : ℝ) / 6) = (m : ℝ) := by
    have hTeq : (T : ℝ) = (m : ℝ) ^ (6 : ℕ) := by rw [hTdef]; push_cast; ring
    rw [hTeq, ← Real.rpow_natCast (m : ℝ) 6, ← Real.rpow_mul (by positivity)]
    norm_num
  have hKlt : Ksum < (T : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [hTm, hm]
    have := Nat.le_ceil Ksum
    push_cast
    linarith
  -- The counting chain.
  have hXpos : (0 : ℝ) < (T : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hTpos _
  have hcard : ((C.biUnion fun c => badShifts c T).card : ℝ) < (T : ℝ) := by
    have h1 : ((C.biUnion fun c => badShifts c T).card : ℝ)
        ≤ ∑ c ∈ C, ((badShifts c T).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := C) (t := fun c => badShifts c T)
    have h2 : ∑ c ∈ C, ((badShifts c T).card : ℝ)
        ≤ ∑ c ∈ C, K c * (T : ℝ) ^ ((5 : ℝ) / 6) :=
      Finset.sum_le_sum fun c hc => hK c hc T hT1
    have h3 : ∑ c ∈ C, K c * (T : ℝ) ^ ((5 : ℝ) / 6) = Ksum * (T : ℝ) ^ ((5 : ℝ) / 6) := by
      rw [hKsum, ← Finset.sum_mul]
    have h4 : Ksum * (T : ℝ) ^ ((5 : ℝ) / 6)
        < (T : ℝ) ^ ((1 : ℝ) / 6) * (T : ℝ) ^ ((5 : ℝ) / 6) :=
      mul_lt_mul_of_pos_right hKlt hXpos
    have h5 : (T : ℝ) ^ ((1 : ℝ) / 6) * (T : ℝ) ^ ((5 : ℝ) / 6) = (T : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num
    linarith
  have hcardZ : (((C.biUnion fun c => badShifts c T).card : ℤ)) < T := by
    exact_mod_cast hcard
  -- Strict pigeonhole against the `2T + 1` candidates in `[-T, T]`.
  have hnotsub : ¬ (Finset.Icc (-T) T ⊆ C.biUnion fun c => badShifts c T) := by
    intro hsub
    have hcc := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcc
    have h2T : (((T + 1 - -T).toNat : ℕ) : ℤ) = 2 * T + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have hle : (2 * T + 1 : ℤ) ≤ (((C.biUnion fun c => badShifts c T).card : ℤ)) := by
      rw [← h2T]; exact_mod_cast hcc
    omega
  obtain ⟨t₀, ht₀Icc, ht₀⟩ := Finset.not_subset.mp hnotsub
  refine ⟨t₀ ^ 13, ⟨t₀, rfl⟩, fun c hc => ?_⟩
  rw [sub_pow13_mem_Dset_iff_proof]
  intro hmem
  exact ht₀ (Finset.mem_biUnion.mpr
    ⟨c, hc, (mem_badShifts_iff c T t₀).mpr ⟨Finset.mem_Icc.mp ht₀Icc, hmem⟩⟩)

/-! ## G2 — the headline theorem, conditional on the greedy criterion -/

/-- **BLUEPRINT Stage G, step G2 / SKETCH §8.2 (Theorem 1.1), in conditional form.**

The hypothesis `hgs` is *exactly* the frozen `good_shift_exists`
(`Erdos477/Theorems.lean:110-111`) and the conclusion is *exactly* the frozen
`erdos_477` (`Erdos477/Theorems.lean:114-115`).

Route: transport `hgs` along `Dset_eq_sub_Bset` into the set literal that
`greedy_tiling`'s hypothesis inlines, apply `greedy_tiling_proof` at `B := Bset`
to obtain the tiling complement `A` with its unique `(a, b)`-representation, and
upgrade `(a, b)` to `(a, m)` using `b = m ^ 13` for existence and `pow13_inj` for
uniqueness (SKETCH §9.5(4)). -/
theorem erdos_477_of_good_shift
    (hgs : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) → ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset) :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n := by
  -- `greedy_tiling` inlines the set literal `{d | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y}`.
  have H : ∀ C : Finset ℤ, (∀ c ∈ C, c ∉ Bset) →
      ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y} := by
    intro C hC
    obtain ⟨b, hb, hb2⟩ := hgs C hC
    refine ⟨b, hb, fun c hc => ?_⟩
    rw [← Dset_eq_sub_Bset]
    exact hb2 c hc
  obtain ⟨A, hA⟩ := greedy_tiling_proof Bset H
  refine ⟨A, fun n => ?_⟩
  obtain ⟨ab, ⟨hab1, hab2, hab3⟩, habu⟩ := hA n
  obtain ⟨m, hm⟩ := hab2
  refine ⟨(ab.1, m), ⟨hab1, ?_⟩, ?_⟩
  · show ab.1 + m ^ 13 = n
    rw [← hm]
    exact hab3
  · rintro ⟨a, m'⟩ ⟨ha1, ha2⟩
    have he : ((a, m' ^ 13) : ℤ × ℤ) = ab := habu (a, m' ^ 13) ⟨ha1, ⟨m', rfl⟩, ha2⟩
    have hfst : a = ab.1 := congrArg Prod.fst he
    have hsnd : m' ^ 13 = ab.2 := congrArg Prod.snd he
    have : m' = m := pow13_inj_proof (by simpa [hm] using hsnd)
    exact Prod.ext hfst this

/-! ## Guardrail `example`s (BLUEPRINT Stage G cheat-watch box) -/

/-- The `C = ∅` case of the greedy criterion is real and easy: `b := 0`. -/
example : ∃ b ∈ Bset, ∀ c ∈ (∅ : Finset ℤ), c - b ∉ Dset :=
  ⟨0, zero_mem_Bset_proof, by simp⟩

/-- ... and `good_shift_exists_of_bound` at `C := ∅` indeed produces it. -/
example (hbb : ∀ c : ℤ, c ∉ Bset → ∃ K : ℝ, 1 ≤ K ∧ ∀ T : ℤ, 1 ≤ T →
      ((badShifts c T).card : ℝ) ≤ K * (T : ℝ) ^ ((5 : ℝ) / 6)) :
    ∃ b ∈ Bset, ∀ c ∈ (∅ : Finset ℤ), c - b ∉ Dset :=
  good_shift_exists_of_bound hbb ∅ (by simp)

/-! ## G1 and G2 — the two frozen assembly theorems

Stage E step E4 has landed (`Erdos477.badShift_bound_proof`,
`Erdos477/Proofs/BadShift/Basic.lean`), so the `hbb` hypothesis of
`good_shift_exists_of_bound` above is available unconditionally and the last two
frozen statements are one-liners.  The witness `A` of `erdos_477_proof` comes
only from `Erdos477.greedy_tiling_proof`, through `erdos_477_of_good_shift`. -/

/-- **P5.1 = paper's Proposition 5.2** (BLUEPRINT Stage G, step G1; SKETCH §8.1):
`Bset` satisfies the greedy criterion.

Type-identical to the frozen `Erdos477.good_shift_exists`. -/
theorem good_shift_exists_proof (C : Finset ℤ) (hC : ∀ c ∈ C, c ∉ Bset) :
    ∃ b ∈ Bset, ∀ c ∈ C, c - b ∉ Dset :=
  good_shift_exists_of_bound (fun c hc => badShift_bound_proof c hc) C hC

/-- **HEADLINE — Theorem 1.1 / Erdős Problem 477** (BLUEPRINT Stage G, step G2;
SKETCH §8.2): the thirteenth powers have a tiling complement in `ℤ`.

Type-identical to the frozen `Erdos477.erdos_477`. -/
theorem erdos_477_proof :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.1 + p.2 ^ 13 = n :=
  erdos_477_of_good_shift
    (fun C hC => good_shift_exists_of_bound (fun c hc => badShift_bound_proof c hc) C hC)

end Erdos477
