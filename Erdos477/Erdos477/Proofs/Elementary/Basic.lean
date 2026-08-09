import Erdos477.Defs

/-!
# Stage A — the elementary layer (L0.1–L0.6, SKETCH §2)

The six trivial-but-ubiquitous facts of `SKETCH.md` §2, together with the four
support lemmas the later stages are promised (`BLUEPRINT.md` Stage A, steps
A1–A6):

* `zero_mem_Bset_proof` (L0.1), `zero_mem_Dset` — Stage F needs `0 ∈ D` for the
  `a_j ∉ A_{j−1}` step (SKETCH §9.5(9));
* `Dset_neg_mem_proof` (L0.2), by swapping `u` and `v` — no sign manipulation;
* `pow13_inj_proof` (L0.3) on **all** of `ℤ`, plus `pow13_eq_neg` and the
  rational version `pow13_inj_rat` that Stage C needs;
* `mem_Bset_of_rat_pow13_proof` (L0.4) for **every** `q : ℚ`, by the elementary
  denominator route `Rat.den_pow` + `Nat.pow_eq_one`;
* `sub_pow13_mem_Dset_iff_proof` (L0.6);
* `Dset_eq_sub_Bset` (A6), a set **equality**, which Stage G uses to instantiate
  `greedy_tiling` at `B := Bset`.

The five `*_proof` declarations have types character-identical to the frozen
statements of `Erdos477/Theorems.lean:23-35`.
-/

namespace Erdos477

/-! ### Odd exponent -/

/-- `13` is odd — the single input the whole injectivity discussion needs. -/
theorem odd_thirteen : Odd 13 := ⟨6, by norm_num⟩

/-- `m ↦ m¹³` is strictly monotone on any linearly ordered ring, in particular on
`ℤ` and on `ℚ`; this is where the odd exponent (and the negative branch) lives. -/
theorem strictMono_pow13 {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] : StrictMono fun a : R => a ^ 13 :=
  odd_thirteen.strictMono_pow

/-! ### L0.1 -/

/-- L0.1. -/
theorem zero_mem_Bset_proof : (0 : ℤ) ∈ Bset := ⟨0, by norm_num⟩

/-- L0.1, second half — support lemma for Stage F (SKETCH §9.5(9)). -/
theorem zero_mem_Dset : (0 : ℤ) ∈ Dset := ⟨0, 0, by ring⟩

/-! ### L0.2 -/

/-- L0.2 — `D` is symmetric. -/
theorem Dset_neg_mem_proof (d : ℤ) (hd : d ∈ Dset) : -d ∈ Dset := by
  obtain ⟨u, v, rfl⟩ := hd
  exact ⟨v, u, by ring⟩

/-! ### L0.3 -/

/-- L0.3 — `m ↦ m¹³` is injective on `ℤ`. -/
theorem pow13_inj_proof : Function.Injective (fun m : ℤ => m ^ 13) :=
  strictMono_pow13.injective

/-- L0.3, consequence — support lemma. -/
theorem pow13_eq_neg : ∀ x y : ℤ, x ^ 13 = -y ^ 13 → x = -y := by
  intro x y h
  refine pow13_inj_proof ?_
  simpa [odd_thirteen.neg_pow] using h

/-- L0.3 over `ℚ` — support lemma; Stage C needs it for "no nontrivial 13th root
of unity in `ℚ`". -/
theorem pow13_inj_rat : Function.Injective (fun q : ℚ => q ^ 13) :=
  strictMono_pow13.injective

/-! ### L0.4 -/

/-- L0.4 — an integer with a rational 13th root is a 13th power. -/
theorem mem_Bset_of_rat_pow13_proof (c : ℤ) (q : ℚ) (h : q ^ 13 = (c : ℚ)) : c ∈ Bset := by
  have hden : q.den ^ 13 = 1 := by
    have hd := congrArg Rat.den h
    rwa [Rat.den_pow, Rat.den_intCast] at hd
  have hd1 : q.den = 1 := (Nat.pow_eq_one.mp hden).resolve_right (by norm_num)
  have hq : ((q.num : ℚ)) = q := (Rat.den_eq_one_iff q).mp hd1
  refine ⟨q.num, ?_⟩
  have hcast : ((q.num ^ 13 : ℤ) : ℚ) = (c : ℚ) := by push_cast [hq]; exact h
  exact_mod_cast hcast.symm

/-! ### L0.6 -/

/-- L0.6 — membership reformulation for bad shifts. -/
theorem sub_pow13_mem_Dset_iff_proof (c t : ℤ) : c - t ^ 13 ∈ Dset ↔ t ^ 13 - c ∈ Dset := by
  constructor
  · intro h
    simpa using Dset_neg_mem_proof _ h
  · intro h
    simpa using Dset_neg_mem_proof _ h

/-! ### A6 — the bridge to `greedy_tiling` -/

/-- Support lemma: `D` really is the difference set `B − B`, as a set **equality**.
Stage G instantiates `greedy_tiling` at `B := Bset` through this. -/
theorem Dset_eq_sub_Bset : Dset = {d : ℤ | ∃ x ∈ Bset, ∃ y ∈ Bset, d = x - y} := by
  ext d
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨u ^ 13, ⟨u, rfl⟩, v ^ 13, ⟨v, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, rfl⟩, y, ⟨v, rfl⟩, rfl⟩
    exact ⟨u, v, rfl⟩

/-! ### Guardrails (BLUEPRINT, Stage A "Cheat watch") -/

example : (0 : ℤ) ∈ Dset := zero_mem_Dset

example : (-1 : ℤ) ∈ Bset := ⟨-1, by norm_num⟩

example : ((-1 : ℤ)) ^ 13 = -1 := by norm_num

/-- `2` is not a thirteenth power, proved by a size argument: strict monotonicity
of `m ↦ m¹³` traps `m` between `1` and `2`, where `1 < 2 < 2¹³`. -/
example : (2 : ℤ) ∉ Bset := by
  rintro ⟨m, hm⟩
  rcases le_or_gt m 1 with hle | hlt
  · have h1 : m ^ 13 ≤ (1 : ℤ) ^ 13 := strictMono_pow13.monotone hle
    rw [one_pow] at h1
    linarith
  · have h2 : (2 : ℤ) ≤ m := hlt
    have h1 : (2 : ℤ) ^ 13 ≤ m ^ 13 := strictMono_pow13.monotone h2
    norm_num at h1
    linarith

end Erdos477
