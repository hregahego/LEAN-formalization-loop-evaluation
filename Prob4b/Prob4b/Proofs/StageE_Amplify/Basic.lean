/-
Copyright (c) 2026 Prob4b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob4b formalization agents
-/
import Prob4b.Proofs.StageA_Algebra.NormalForm
import Prob4b.Proofs.StageC_Module.Basic
import Prob4b.Proofs.StageD_Idealization.Basic

/-!
# Stage E — `R = Δ(B) + C^(ℕ)` is finite conductor

This file delivers **step E0** of Stage E: the basic infrastructure for the amplified
ring `Ramp = Rsub`, the subring of `ℕ → Cring` consisting of the sequences that agree
with a fixed diagonal element `iota x` outside a finite set of coordinates.

The main constructions are:

* `mem_Rsub_iff` — the carrier of `Rsub` unfolded exactly once;
* `tail_unique` and `tailValue` — the tail value of an element of `Ramp` (an element of
  `Balg`, seen inside `Cring` through `iota`), well defined because two cofinite subsets
  of `ℕ` always meet;
* `exc` — the finite exceptional set of coordinates where an element differs from its
  tail value;
* `coordAt` and `offSet` — the two families of elements of `Ramp` out of which the finite
  generating sets of steps E1/E2 are built;
* `mem_ideal_span_finset` — a finite span in `Ramp` written as an explicit finite sum.

Steps **E1** (`re_ann_fg_of_C`), **E2** (`re_pair_inter_fg_of_C`) and **E3**
(`re_finiteConductor_of_C`) follow at the end of the file. They are stated with the frozen
theorems 13 and 14 (`C_ann_eq`, `C_pair_inter`) as explicit hypotheses `hC13`, `hC14`, and
are then instantiated at the Stage C/D results `di_ann_eq_of_M M_ann_eq_proof` and
`di_pair_inter_of_M M_pair_inter_proof` to give frozen theorem 16 as
`R_finiteConductor_proof`.

Note that `Ramp` is *not* Noetherian — Stage F refutes exactly that — so no lemma here may
assert or use such a thing; all finiteness below comes from `B_isNoetherianRing_proof` and
`C_isNoetherianRing_proof` together with a finite exceptional set.
-/

namespace Prob4b

noncomputable section

/-! ### Coordinates of elements of `Ramp` -/

/-- Membership in `Rsub` unfolded once: a sequence lies in `R` exactly when it is equal to
some diagonal element `iota x` outside a finite set of coordinates. This is the only place
where the carrier of `Rsub` is unfolded. -/
theorem mem_Rsub_iff (f : ℕ → Cring) :
    f ∈ Rsub ↔ ∃ x : Balg, {n | f n ≠ iota x}.Finite := Iff.rfl

/-- The first coordinate of `iota x` is `x`. -/
@[simp] theorem iota_fst (x : Balg) : (iota x).fst = x := rfl

/-- The second coordinate of `iota x` vanishes. -/
@[simp] theorem iota_snd (x : Balg) : (iota x).snd = 0 := rfl

/-- `iota` turns a product of images into the image of a product. -/
theorem iota_mul_iota (x y : Balg) : iota x * iota y = iota (x * y) := (map_mul iota x y).symm

/-- `iota` sends `0` to `0`. -/
@[simp] theorem iota_zero : iota (0 : Balg) = 0 := map_zero iota

/-- `iota : Balg →+* Cring` is injective. -/
theorem iota_injective : Function.Injective iota := fun x y h => by
  simpa using congrArg TrivSqZeroExt.fst h

/-- Coordinates of a sum in `Ramp`. -/
@[simp] theorem coe_add_apply (f g : Ramp) (n : ℕ) :
    ((f + g : Ramp) : ℕ → Cring) n = (f : ℕ → Cring) n + (g : ℕ → Cring) n := rfl

/-- Coordinates of a product in `Ramp`. -/
@[simp] theorem coe_mul_apply (f g : Ramp) (n : ℕ) :
    ((f * g : Ramp) : ℕ → Cring) n = (f : ℕ → Cring) n * (g : ℕ → Cring) n := rfl

/-- Coordinates of a negation in `Ramp`. -/
@[simp] theorem coe_neg_apply (f : Ramp) (n : ℕ) :
    ((-f : Ramp) : ℕ → Cring) n = -(f : ℕ → Cring) n := rfl

/-- Coordinates of `0 : Ramp`. -/
@[simp] theorem coe_zero_apply (n : ℕ) : ((0 : Ramp) : ℕ → Cring) n = 0 := rfl

/-- Coordinates of `1 : Ramp`. -/
@[simp] theorem coe_one_apply (n : ℕ) : ((1 : Ramp) : ℕ → Cring) n = 1 := rfl

/-- Coordinates of a diagonal element. -/
@[simp] theorem diag_apply (x : Balg) (n : ℕ) :
    ((diag x : Ramp) : ℕ → Cring) n = iota x := rfl

/-- Two elements of `Ramp` with the same coordinates are equal. -/
theorem Ramp_ext {f g : Ramp} (h : ∀ n, (f : ℕ → Cring) n = (g : ℕ → Cring) n) : f = g :=
  Subtype.ext (funext h)

/-! ### The tail value -/

/-- The tail value of an element of `Ramp` is unique: two cofinite sets of coordinates
meet, so the two candidate diagonal values agree there, and `iota` is injective. -/
theorem tail_unique (f : Ramp) (x y : Balg)
    (hx : {n | (f : ℕ → Cring) n ≠ iota x}.Finite)
    (hy : {n | (f : ℕ → Cring) n ≠ iota y}.Finite) : x = y := by
  obtain ⟨n, hn⟩ := ((hx.union hy).infinite_compl).nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  exact iota_injective (hn.1.symm.trans hn.2)

/-- The tail value of `f : Ramp`: the unique `x : Balg` with `f n = iota x` for all but
finitely many `n`. -/
def tailValue (f : Ramp) : Balg := Classical.choose ((mem_Rsub_iff _).mp f.2)

/-- `f` agrees with `iota (tailValue f)` outside a finite set of coordinates. -/
theorem tailValue_spec (f : Ramp) :
    {n | (f : ℕ → Cring) n ≠ iota (tailValue f)}.Finite :=
  Classical.choose_spec ((mem_Rsub_iff _).mp f.2)

/-- Characterisation of the tail value: any cofinitely attained diagonal value is it. -/
theorem tailValue_eq_of (f : Ramp) (x : Balg)
    (h : {n | (f : ℕ → Cring) n ≠ iota x}.Finite) : tailValue f = x :=
  tail_unique f _ _ (tailValue_spec f) h

/-- Practical form of `tailValue_eq_of`: it is enough to exhibit a finite set of
coordinates off which `f` is the constant `iota x`. -/
theorem tailValue_eq_of_apply (f : Ramp) (x : Balg) (S : Set ℕ) (hS : S.Finite)
    (h : ∀ n ∉ S, (f : ℕ → Cring) n = iota x) : tailValue f = x :=
  tailValue_eq_of f x (hS.subset fun n hn => by
    by_contra hnS
    exact hn (h n hnS))

/-! ### The exceptional set -/

/-- The exceptional set of `f : Ramp`: the coordinates where `f` differs from its tail
value. -/
def exc (f : Ramp) : Set ℕ := {n | (f : ℕ → Cring) n ≠ iota (tailValue f)}

/-- Membership in the exceptional set, unfolded. -/
theorem mem_exc_iff (f : Ramp) (n : ℕ) :
    n ∈ exc f ↔ (f : ℕ → Cring) n ≠ iota (tailValue f) := Iff.rfl

/-- The exceptional set is finite. -/
theorem exc_finite (f : Ramp) : (exc f).Finite := tailValue_spec f

/-- Outside its exceptional set, `f` is the constant `iota (tailValue f)`. -/
theorem apply_eq_of_not_mem_exc (f : Ramp) (n : ℕ) (h : n ∉ exc f) :
    (f : ℕ → Cring) n = iota (tailValue f) := not_not.mp h

/-! ### `tailValue` is a ring homomorphism split by `diag` -/

/-- The tail value of a diagonal element is the element itself. -/
@[simp] theorem tailValue_diag (x : Balg) : tailValue (diag x) = x :=
  tailValue_eq_of_apply _ _ ∅ Set.finite_empty fun n _ => diag_apply x n

/-- The tail value of `0` is `0`. -/
@[simp] theorem tailValue_zero : tailValue 0 = 0 := by
  simpa using tailValue_diag (0 : Balg)

/-- The tail value of `1` is `1`. -/
@[simp] theorem tailValue_one : tailValue 1 = 1 := by
  simpa using tailValue_diag (1 : Balg)

/-- The tail value is additive. -/
@[simp] theorem tailValue_add (f g : Ramp) :
    tailValue (f + g) = tailValue f + tailValue g :=
  tailValue_eq_of_apply _ _ (exc f ∪ exc g) ((exc_finite f).union (exc_finite g)) (by
    intro n hn
    simp only [Set.mem_union, not_or] at hn
    rw [coe_add_apply, apply_eq_of_not_mem_exc f n hn.1, apply_eq_of_not_mem_exc g n hn.2,
      map_add])

/-- The tail value is multiplicative. -/
@[simp] theorem tailValue_mul (f g : Ramp) :
    tailValue (f * g) = tailValue f * tailValue g :=
  tailValue_eq_of_apply _ _ (exc f ∪ exc g) ((exc_finite f).union (exc_finite g)) (by
    intro n hn
    simp only [Set.mem_union, not_or] at hn
    rw [coe_mul_apply, apply_eq_of_not_mem_exc f n hn.1, apply_eq_of_not_mem_exc g n hn.2,
      map_mul])

/-! ### The coordinate elements `coordAt` -/

/-- `coordAt n c` is the element of `Ramp` equal to `c` in coordinate `n` and to `0`
elsewhere; its tail value is `0`. -/
def coordAt (n : ℕ) (c : Cring) : Ramp :=
  ⟨fun k => if k = n then c else 0, ⟨0, (Set.finite_singleton n).subset (by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    by_contra hne
    simp only [Set.mem_singleton_iff] at hne
    simp [hne] at hk)⟩⟩

/-- `coordAt n c` takes the value `c` in coordinate `n`. -/
@[simp] theorem coordAt_apply_self (n : ℕ) (c : Cring) :
    ((coordAt n c : Ramp) : ℕ → Cring) n = c := by
  simp [coordAt]

/-- `coordAt n c` vanishes away from coordinate `n`. -/
@[simp] theorem coordAt_apply_ne (n k : ℕ) (c : Cring) (h : k ≠ n) :
    ((coordAt n c : Ramp) : ℕ → Cring) k = 0 := by
  simp [coordAt, h]

/-- The tail value of `coordAt n c` is `0`. -/
@[simp] theorem tailValue_coordAt (n : ℕ) (c : Cring) : tailValue (coordAt n c) = 0 :=
  tailValue_eq_of_apply _ _ {n} (Set.finite_singleton n) (by
    intro k hk
    rw [coordAt_apply_ne n k c (by simpa using hk), map_zero])

/-- Multiplying `coordAt n c` by an arbitrary element only sees its `n`-th coordinate. -/
theorem coordAt_mul (n : ℕ) (c : Cring) (f : Ramp) :
    coordAt n c * f = coordAt n (c * (f : ℕ → Cring) n) := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk]

/-- `coordAt n` is additive. -/
theorem coordAt_add (n : ℕ) (c c' : Cring) :
    coordAt n (c + c') = coordAt n c + coordAt n c' := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk]

/-! ### The tail elements `offSet` -/

/-- `offSet S hS x` is the element of `Ramp` equal to `iota x` off the finite set `S` and
to `0` on `S`. -/
def offSet (S : Set ℕ) (hS : S.Finite) (x : Balg) : Ramp :=
  ⟨(Set.indicator Sᶜ fun _ => iota x), ⟨x, hS.subset (by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra hnS
    exact hn (Set.indicator_of_mem (by simpa using hnS) _))⟩⟩

/-- The coordinates of `offSet S hS x`, as an indicator function. -/
theorem offSet_coe (S : Set ℕ) (hS : S.Finite) (x : Balg) :
    ((offSet S hS x : Ramp) : ℕ → Cring) = Set.indicator Sᶜ fun _ => iota x := rfl

/-- `offSet S hS x` vanishes on `S`. -/
@[simp] theorem offSet_apply_mem (S : Set ℕ) (hS : S.Finite) (x : Balg) {n : ℕ}
    (h : n ∈ S) : ((offSet S hS x : Ramp) : ℕ → Cring) n = 0 := by
  rw [offSet_coe]
  exact Set.indicator_of_notMem (by simpa using h) _

/-- `offSet S hS x` is `iota x` off `S`. -/
@[simp] theorem offSet_apply_not_mem (S : Set ℕ) (hS : S.Finite) (x : Balg) {n : ℕ}
    (h : n ∉ S) : ((offSet S hS x : Ramp) : ℕ → Cring) n = iota x := by
  rw [offSet_coe]
  exact Set.indicator_of_mem (by simpa using h) _

/-- The tail value of `offSet S hS x` is `x`. -/
@[simp] theorem tailValue_offSet (S : Set ℕ) (hS : S.Finite) (x : Balg) :
    tailValue (offSet S hS x) = x :=
  tailValue_eq_of_apply _ _ S hS fun _ hn => offSet_apply_not_mem S hS x hn

/-! ### Finite spans in `Ramp` -/

/-- An element of the ideal generated by a finite subset of `Ramp` is exactly a finite
`Ramp`-combination of that subset. Consumed by Stage F, step F4. -/
theorem mem_ideal_span_finset (s : Finset Ramp) (h : Ramp) :
    h ∈ Ideal.span (↑s : Set Ramp) ↔ ∃ g : Ramp → Ramp, h = ∑ i ∈ s, g i * i := by
  constructor
  · intro hh
    obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp hh
    exact ⟨g, by simpa [smul_eq_mul] using hg.symm⟩
  · rintro ⟨g, rfl⟩
    exact sum_mem fun i hi =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr hi))

/-! ### Guardrails -/

/-- Guardrail (Stage E cheat-watch (f)): the diagonal copy of `B` did not collapse. -/
example : (diag xa : Ramp) ≠ 0 := by
  intro h
  have h0 : iota xa = iota (0 : Balg) := by
    have h1 := congrArg (fun f : Ramp => (f : ℕ → Cring) 0) h
    simpa using h1
  have hxa : xa = 0 := iota_injective h0
  have h2 : nf xa = nf (0 : Balg) := congrArg nf hxa
  rw [nf_xa, map_zero] at h2
  have h3 := congrFun h2 (Sum.inr (Sum.inl 0))
  rw [Pi.single_eq_same] at h3
  exact one_ne_zero h3

/-- Guardrail (Stage E cheat-watch (f)): the defect element sits nontrivially in `R`. -/
example : uAt 0 ≠ (0 : Ramp) := by
  intro h
  have h0 : (TrivSqZeroExt.inr uElt : Cring) = 0 := by
    have h1 := congrArg (fun f : Ramp => (f : ℕ → Cring) 0) h
    simpa [uAt] using h1
  have h2 : uElt = 0 := by
    have h3 := congrArg TrivSqZeroExt.snd h0
    simpa using h3
  exact M_u_ne_zero_proof h2

/-! ### Extra arithmetic of `coordAt` and `offSet`, used by steps E1 and E2 -/

/-- Coordinates of a difference in `Ramp`. -/
@[simp] theorem coe_sub_apply (f g : Ramp) (n : ℕ) :
    ((f - g : Ramp) : ℕ → Cring) n = (f : ℕ → Cring) n - (g : ℕ → Cring) n := rfl

/-- `coordAt n` sends `0` to `0`. -/
@[simp] theorem coordAt_zero (n : ℕ) : coordAt n (0 : Cring) = 0 := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk]

/-- Two coordinate elements at the same place multiply coordinatewise. -/
theorem coordAt_mul_coordAt (n : ℕ) (c c' : Cring) :
    coordAt n c * coordAt n c' = coordAt n (c * c') := by
  rw [coordAt_mul, coordAt_apply_self]

/-- `offSet S hS` sends `0` to `0`. -/
@[simp] theorem offSet_zero (S : Set ℕ) (hS : S.Finite) : offSet S hS (0 : Balg) = 0 := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k ∈ S
  · rw [offSet_apply_mem S hS 0 hk, coe_zero_apply]
  · rw [offSet_apply_not_mem S hS 0 hk, coe_zero_apply, map_zero]

/-- `offSet S hS` is additive. -/
theorem offSet_add (S : Set ℕ) (hS : S.Finite) (x y : Balg) :
    offSet S hS (x + y) = offSet S hS x + offSet S hS y := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k ∈ S
  · rw [coe_add_apply, offSet_apply_mem S hS (x + y) hk, offSet_apply_mem S hS x hk,
      offSet_apply_mem S hS y hk, add_zero]
  · rw [coe_add_apply, offSet_apply_not_mem S hS (x + y) hk, offSet_apply_not_mem S hS x hk,
      offSet_apply_not_mem S hS y hk, map_add]

/-- Multiplying `offSet S hS x` by a diagonal element scales the tail value. -/
theorem diag_mul_offSet (S : Set ℕ) (hS : S.Finite) (r x : Balg) :
    diag r * offSet S hS x = offSet S hS (r * x) := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k ∈ S
  · rw [coe_mul_apply, offSet_apply_mem S hS x hk, offSet_apply_mem S hS (r * x) hk, mul_zero]
  · rw [coe_mul_apply, diag_apply, offSet_apply_not_mem S hS x hk,
      offSet_apply_not_mem S hS (r * x) hk, ← map_mul]

/-- Off `S`, a coordinate element carrying `iota x` is a multiple of the `offSet`
generator built from `x`. -/
theorem coordAt_one_mul_offSet (S : Set ℕ) (hS : S.Finite) (x : Balg) {n : ℕ} (hn : n ∉ S) :
    coordAt n 1 * offSet S hS x = coordAt n (iota x) := by
  rw [coordAt_mul, offSet_apply_not_mem S hS x hn, one_mul]

/-- Multiplying `offSet S hS c` by an element of `Ramp` whose exceptional set is contained
in `S` multiplies the tail values. -/
theorem offSet_mul_of_exc_subset (S : Set ℕ) (hS : S.Finite) (f : Ramp) (hsub : exc f ⊆ S)
    (c : Balg) : offSet S hS c * f = offSet S hS (c * tailValue f) := by
  refine Ramp_ext fun k => ?_
  by_cases hk : k ∈ S
  · rw [coe_mul_apply, offSet_apply_mem S hS c hk,
      offSet_apply_mem S hS (c * tailValue f) hk, zero_mul]
  · rw [coe_mul_apply, offSet_apply_not_mem S hS c hk,
      offSet_apply_not_mem S hS (c * tailValue f) hk,
      apply_eq_of_not_mem_exc f k fun h => hk (hsub h), ← map_mul]

/-- Coordinates of a finite sum in `Ramp`. -/
theorem coe_sum_apply (T : Finset ℕ) (F : ℕ → Ramp) (k : ℕ) :
    ((∑ n ∈ T, F n : Ramp) : ℕ → Cring) k = ∑ n ∈ T, ((F n : ℕ → Cring) k) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coe_add_apply, ih]

/-- An element of `Ramp` supported inside a finite set `T` is the sum of its coordinate
elements over `T`. -/
theorem re_eq_sum_coordAt (h : Ramp) (T : Finset ℕ)
    (hT : ∀ n, n ∉ T → (h : ℕ → Cring) n = 0) :
    h = ∑ n ∈ T, coordAt n ((h : ℕ → Cring) n) := by
  classical
  refine Ramp_ext fun k => ?_
  rw [coe_sum_apply]
  by_cases hk : k ∈ T
  · rw [Finset.sum_eq_single k]
    · rw [coordAt_apply_self]
    · intro n _ hne
      exact coordAt_apply_ne n k _ (Ne.symm hne)
    · intro hcon
      exact absurd hk hcon
  · rw [Finset.sum_eq_zero, hT k hk]
    intro n hn
    exact coordAt_apply_ne n k _ (by rintro rfl; exact hk hn)

/-! ### Membership in the ideal generated by the E1/E2 generating sets -/

/-- If every generator of an ideal `t` of `Cring` gives a coordinate element of `K`, then so
does every element of `Ideal.span t`. -/
theorem re_coordAt_mem_of_span {K : Ideal Ramp} (n : ℕ) (t : Set Cring)
    (hgen : ∀ c ∈ t, coordAt n c ∈ K) {c : Cring} (hc : c ∈ Ideal.span t) :
    coordAt n c ∈ K := by
  induction hc using Submodule.span_induction with
  | mem c hc => exact hgen c hc
  | zero => rw [coordAt_zero]; exact K.zero_mem
  | add a b _ _ ha hb => rw [coordAt_add]; exact add_mem ha hb
  | smul r a _ ha =>
      rw [smul_eq_mul, ← coordAt_mul_coordAt]
      exact Ideal.mul_mem_left _ _ ha

/-- If every generator of an ideal `t` of `Balg` gives an `offSet` element of `K`, then so
does every element of `Ideal.span t`. -/
theorem re_offSet_mem_of_span {K : Ideal Ramp} (S : Set ℕ) (hS : S.Finite) (t : Set Balg)
    (hgen : ∀ z ∈ t, offSet S hS z ∈ K) {z : Balg} (hz : z ∈ Ideal.span t) :
    offSet S hS z ∈ K := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hgen z hz
  | zero => rw [offSet_zero]; exact K.zero_mem
  | add a b _ _ ha hb => rw [offSet_add]; exact add_mem ha hb
  | smul r a _ ha =>
      rw [smul_eq_mul, ← diag_mul_offSet]
      exact Ideal.mul_mem_left _ _ ha

/-- Off `S`, a coordinate element carrying a member of the extension along `iota` of an
ideal generated by `t` lies in any ideal containing the `offSet` generators built from `t`. -/
theorem re_coordAt_mem_of_map {K : Ideal Ramp} (S : Set ℕ) (hS : S.Finite) {n : ℕ}
    (hn : n ∉ S) (t : Set Balg) (hgen : ∀ z ∈ t, offSet S hS z ∈ K) {c : Cring}
    (hc : c ∈ Ideal.map iota (Ideal.span t)) : coordAt n c ∈ K := by
  rw [Ideal.map_span] at hc
  refine re_coordAt_mem_of_span n _ ?_ hc
  rintro _ ⟨z, hz, rfl⟩
  rw [← coordAt_one_mul_offSet S hS z hn]
  exact Ideal.mul_mem_left _ _ (hgen z hz)


/-! ### The finite generating sets of steps E1 and E2 -/

/-- The candidate finite generating set of steps E1/E2: the `offSet` elements built from a
finite family `w` of elements of `Balg`, together with the coordinate elements built at
each exceptional coordinate `n ∈ S` from a finite family `cs n` of elements of `Cring`. -/
def reGens (S : Set ℕ) (hS : S.Finite) (w : Finset Balg) (cs : ℕ → Finset Cring) :
    Set Ramp :=
  (fun z => offSet S hS z) '' (↑w : Set Balg) ∪
    ⋃ n ∈ S, (fun c => coordAt n c) '' (↑(cs n) : Set Cring)

/-- `reGens` is a finite set: a finite union of finitely many finite images. -/
theorem reGens_finite (S : Set ℕ) (hS : S.Finite) (w : Finset Balg) (cs : ℕ → Finset Cring) :
    (reGens S hS w cs).Finite :=
  (w.finite_toSet.image _).union (hS.biUnion fun n _ => (cs n).finite_toSet.image _)

/-- The `offSet` generators lie in the span of `reGens`. -/
theorem offSet_mem_span_reGens (S : Set ℕ) (hS : S.Finite) (w : Finset Balg)
    (cs : ℕ → Finset Cring) {z : Balg} (hz : z ∈ (↑w : Set Balg)) :
    offSet S hS z ∈ Ideal.span (reGens S hS w cs) :=
  Ideal.subset_span (Or.inl ⟨z, hz, rfl⟩)

/-- The coordinate generators lie in the span of `reGens`. -/
theorem coordAt_mem_span_reGens (S : Set ℕ) (hS : S.Finite) (w : Finset Balg)
    (cs : ℕ → Finset Cring) {n : ℕ} (hn : n ∈ S) {c : Cring}
    (hc : c ∈ (↑(cs n) : Set Cring)) :
    coordAt n c ∈ Ideal.span (reGens S hS w cs) :=
  Ideal.subset_span (Or.inr (Set.mem_biUnion hn ⟨c, hc, rfl⟩))

/-- Annihilation in `Ramp`, read coordinatewise. -/
theorem mem_ann_Ramp_iff (f g : Ramp) :
    g ∈ ann f ↔ ∀ n, (g : ℕ → Cring) n * (f : ℕ → Cring) n = 0 := by
  rw [mem_ann f g]
  constructor
  · intro h n
    have h' := congrArg (fun u : Ramp => (u : ℕ → Cring) n) h
    simpa using h'
  · intro h
    refine Ramp_ext fun n => ?_
    rw [coe_mul_apply, coe_zero_apply]
    exact h n

/-! ### E1 — annihilators in `Ramp` are finitely generated -/

set_option maxHeartbeats 4000000 in
-- instance search for `CommRing Ramp` / `CommRing Cring` (both built on the quotients
-- `Balg` and `Mmod`) dominates elaboration here; the default budget is not enough.
/-- The easy half of step E1: every listed generator kills `f`. -/
theorem re_ann_gens_le (f : Ramp) (hS : (exc f).Finite) (w : Finset Balg)
    (cs : ℕ → Finset Cring) (hw : ∀ z ∈ (↑w : Set Balg), z * tailValue f = 0)
    (hcs : ∀ n ∈ exc f, ∀ c ∈ (↑(cs n) : Set Cring), c * (f : ℕ → Cring) n = 0) :
    Ideal.span (reGens (exc f) hS w cs) ≤ ann f := by
  rw [Ideal.span_le]
  rintro h (⟨z, hz, rfl⟩ | hh)
  · rw [SetLike.mem_coe, mem_ann_Ramp_iff]
    intro k
    by_cases hk : k ∈ exc f
    · rw [offSet_apply_mem _ hS z hk, zero_mul]
    · rw [offSet_apply_not_mem _ hS z hk, apply_eq_of_not_mem_exc f k hk, iota_mul_iota,
        hw z hz, iota_zero]
  · simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hh
    obtain ⟨n, hn, c, hc, rfl⟩ := hh
    rw [SetLike.mem_coe, mem_ann f (coordAt n c), coordAt_mul, hcs n hn c hc, coordAt_zero]

set_option maxHeartbeats 4000000 in
-- instance search for `CommRing Ramp` / `CommRing Cring` (both built on the quotients
-- `Balg` and `Mmod`) dominates elaboration here; the default budget is not enough.
/-- The content of step E1: an element killing `f` lies in the span of the listed
generators. Off the exceptional set this is where the hypothesis `hC13` (frozen theorem
13, `C_ann_eq`) enters. -/
theorem re_ann_le_gens (hC13 : ∀ x : Balg, ann (iota x) = (ann x).map iota) (f : Ramp)
    (hS : (exc f).Finite) (w : Finset Balg) (cs : ℕ → Finset Cring)
    (hw : Ideal.span (↑w : Set Balg) = ann (tailValue f))
    (hcs : ∀ n, Ideal.span (↑(cs n) : Set Cring) = ann ((f : ℕ → Cring) n)) :
    ann f ≤ Ideal.span (reGens (exc f) hS w cs) := by
  classical
  intro gg hgg
  have hgfn : ∀ n, (gg : ℕ → Cring) n * (f : ℕ → Cring) n = 0 :=
    (mem_ann_Ramp_iff f gg).mp hgg
  obtain ⟨n₀, hn₀⟩ := (hS.union (exc_finite gg)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hn₀
  have hzann : tailValue gg ∈ ann (tailValue f) := by
    rw [mem_ann (tailValue f) (tailValue gg)]
    apply iota_injective
    rw [iota_zero, ← iota_mul_iota, ← apply_eq_of_not_mem_exc gg n₀ hn₀.2,
      ← apply_eq_of_not_mem_exc f n₀ hn₀.1]
    exact hgfn n₀
  have hzmul : tailValue gg * tailValue f = 0 :=
    (mem_ann (tailValue f) (tailValue gg)).mp hzann
  have hoffz : offSet (exc f) hS (tailValue gg) ∈ Ideal.span (reGens (exc f) hS w cs) :=
    re_offSet_mem_of_span (exc f) hS _
      (fun z hz => offSet_mem_span_reGens (exc f) hS w cs hz) (by rw [hw]; exact hzann)
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = hS.toFinset ∪ (exc_finite gg).toFinset :=
    ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : Ramp, g' = gg - offSet (exc f) hS (tailValue gg) := ⟨_, rfl⟩
  have hzero : ∀ n, n ∉ T → (g' : ℕ → Cring) n = 0 := by
    intro n hn
    rw [hT] at hn
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hn
    rw [hg', coe_sub_apply, offSet_apply_not_mem _ hS _ hn.1,
      apply_eq_of_not_mem_exc gg n hn.2, sub_self]
  have hann' : ∀ n, (g' : ℕ → Cring) n * (f : ℕ → Cring) n = 0 := by
    intro n
    rw [hg', coe_sub_apply, sub_mul, hgfn n]
    by_cases hk : n ∈ exc f
    · rw [offSet_apply_mem _ hS _ hk, zero_mul, sub_self]
    · rw [offSet_apply_not_mem _ hS _ hk, apply_eq_of_not_mem_exc f n hk, iota_mul_iota,
        hzmul, iota_zero, sub_self]
  have hmem : ∀ n ∈ T,
      coordAt n ((g' : ℕ → Cring) n) ∈ Ideal.span (reGens (exc f) hS w cs) := by
    intro n _
    by_cases hk : n ∈ exc f
    · refine re_coordAt_mem_of_span n _
        (fun c hc => coordAt_mem_span_reGens (exc f) hS w cs hk hc) ?_
      rw [hcs n, mem_ann ((f : ℕ → Cring) n) ((g' : ℕ → Cring) n)]
      exact hann' n
    · refine re_coordAt_mem_of_map (exc f) hS hk _
        (fun z hz => offSet_mem_span_reGens (exc f) hS w cs hz) ?_
      have hmm : (g' : ℕ → Cring) n ∈ ann ((f : ℕ → Cring) n) :=
        (mem_ann ((f : ℕ → Cring) n) ((g' : ℕ → Cring) n)).mpr (hann' n)
      rw [apply_eq_of_not_mem_exc f n hk, hC13 (tailValue f), ← hw] at hmm
      exact hmm
  have hg'mem : g' ∈ Ideal.span (reGens (exc f) hS w cs) := by
    rw [re_eq_sum_coordAt g' T hzero]
    exact sum_mem hmem
  have hsplit : gg = g' + offSet (exc f) hS (tailValue gg) := by rw [hg']; ring
  rw [hsplit]
  exact add_mem hg'mem hoffz

set_option maxHeartbeats 4000000 in
-- instance search for `CommRing Ramp` / `CommRing Cring` (both built on the quotients
-- `Balg` and `Mmod`) dominates elaboration here; the default budget is not enough.
/-- **Step E1.** Every annihilator ideal of `Ramp` is finitely generated. The frozen
theorem 13 (`C_ann_eq`) is carried as the explicit hypothesis `hC13`. The finiteness comes
from `B_isNoetherianRing_proof` and `C_isNoetherianRing_proof` together with the finite
exceptional set `exc f`; `Ramp` itself is never assumed Noetherian. -/
theorem re_ann_fg_of_C (hC13 : ∀ x : Balg, ann (iota x) = (ann x).map iota) :
    ∀ f : Ramp, (ann f).FG := by
  classical
  intro f
  have hnB : ∀ I : Ideal Balg, I.FG :=
    (isNoetherianRing_iff_ideal_fg Balg).mp B_isNoetherianRing_proof
  have hnC : ∀ I : Ideal Cring, I.FG :=
    (isNoetherianRing_iff_ideal_fg Cring).mp C_isNoetherianRing_proof
  have hS : (exc f).Finite := exc_finite f
  obtain ⟨w, hw⟩ := hnB (ann (tailValue f))
  have hw' : Ideal.span (↑w : Set Balg) = ann (tailValue f) := hw
  choose cs hcs using fun n : ℕ => hnC (ann ((f : ℕ → Cring) n))
  have hcs' : ∀ n : ℕ, Ideal.span (↑(cs n) : Set Cring) = ann ((f : ℕ → Cring) n) := hcs
  refine Submodule.fg_def.mpr ⟨reGens (exc f) hS w cs, reGens_finite _ hS w cs, ?_⟩
  refine le_antisymm (re_ann_gens_le f hS w cs ?_ ?_) (re_ann_le_gens hC13 f hS w cs hw' hcs')
  · intro z hz
    exact (mem_ann (tailValue f) z).mp (by rw [← hw']; exact Ideal.subset_span hz)
  · intro n _ c hc
    exact (mem_ann ((f : ℕ → Cring) n) c).mp (by rw [← hcs' n]; exact Ideal.subset_span hc)

/-! ### E2 — pairwise intersections of principal ideals in `Ramp` -/

set_option maxHeartbeats 4000000 in
-- instance search for `CommRing Ramp` / `CommRing Cring` (both built on the quotients
-- `Balg` and `Mmod`) dominates elaboration here; the default budget is not enough.
/-- The easy half of step E2: every listed generator lies in `f·R ⊓ g·R`. -/
theorem re_pair_gens_le (f g : Ramp) (hS : (exc f ∪ exc g).Finite) (w : Finset Balg)
    (cs : ℕ → Finset Cring)
    (hw : ∀ z ∈ (↑w : Set Balg),
      z ∈ (Ideal.span {tailValue f} ⊓ Ideal.span {tailValue g} : Ideal Balg))
    (hcs : ∀ n ∈ exc f ∪ exc g, ∀ c ∈ (↑(cs n) : Set Cring),
      c ∈ (Ideal.span {(f : ℕ → Cring) n} ⊓
        Ideal.span {(g : ℕ → Cring) n} : Ideal Cring)) :
    Ideal.span (reGens (exc f ∪ exc g) hS w cs) ≤
      (Ideal.span {f} ⊓ Ideal.span {g} : Ideal Ramp) := by
  rw [Ideal.span_le]
  rintro h (⟨z, hz, rfl⟩ | hh)
  · obtain ⟨hzf, hzg⟩ := Submodule.mem_inf.mp (hw z hz)
    obtain ⟨cf, hcf⟩ := Ideal.mem_span_singleton'.mp hzf
    obtain ⟨cg, hcg⟩ := Ideal.mem_span_singleton'.mp hzg
    refine SetLike.mem_coe.mpr (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
    · refine Ideal.mem_span_singleton'.mpr ⟨offSet _ hS cf, ?_⟩
      rw [offSet_mul_of_exc_subset _ hS f Set.subset_union_left cf, hcf]
    · refine Ideal.mem_span_singleton'.mpr ⟨offSet _ hS cg, ?_⟩
      rw [offSet_mul_of_exc_subset _ hS g Set.subset_union_right cg, hcg]
  · simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hh
    obtain ⟨n, hn, c, hc, rfl⟩ := hh
    obtain ⟨hcf, hcg⟩ := Submodule.mem_inf.mp (hcs n hn c hc)
    obtain ⟨df, hdf⟩ := Ideal.mem_span_singleton'.mp hcf
    obtain ⟨dg, hdg⟩ := Ideal.mem_span_singleton'.mp hcg
    refine SetLike.mem_coe.mpr (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
    · exact Ideal.mem_span_singleton'.mpr ⟨coordAt n df, by rw [coordAt_mul, hdf]⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨coordAt n dg, by rw [coordAt_mul, hdg]⟩

set_option maxHeartbeats 4000000 in
-- instance search for `CommRing Ramp` / `CommRing Cring` (both built on the quotients
-- `Balg` and `Mmod`) dominates elaboration here; the default budget is not enough.
/-- The content of step E2: an element of `f·R ⊓ g·R` lies in the span of the listed
generators. Off the exceptional set this is where the hypothesis `hC14` (frozen theorem
14, `C_pair_inter`) enters, at the arbitrary tail values `tailValue f`, `tailValue g`. -/
theorem re_pair_le_gens (hC14 : ∀ x y : Balg, Ideal.span {iota x} ⊓ Ideal.span {iota y} =
      (Ideal.span {x} ⊓ Ideal.span {y}).map iota)
    (f g : Ramp) (hS : (exc f ∪ exc g).Finite) (w : Finset Balg) (cs : ℕ → Finset Cring)
    (hw : Ideal.span (↑w : Set Balg) =
      (Ideal.span {tailValue f} ⊓ Ideal.span {tailValue g} : Ideal Balg))
    (hcs : ∀ n, Ideal.span (↑(cs n) : Set Cring) =
      (Ideal.span {(f : ℕ → Cring) n} ⊓ Ideal.span {(g : ℕ → Cring) n} : Ideal Cring)) :
    (Ideal.span {f} ⊓ Ideal.span {g} : Ideal Ramp) ≤
      Ideal.span (reGens (exc f ∪ exc g) hS w cs) := by
  classical
  intro h hmemh
  obtain ⟨hhf, hhg⟩ := Submodule.mem_inf.mp hmemh
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hhf
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hhg
  have hsn : ∀ n, (h : ℕ → Cring) n = (s : ℕ → Cring) n * (f : ℕ → Cring) n := by
    intro n
    rw [← hs, coe_mul_apply]
  have htn : ∀ n, (h : ℕ → Cring) n = (t : ℕ → Cring) n * (g : ℕ → Cring) n := by
    intro n
    rw [← ht, coe_mul_apply]
  obtain ⟨n₀, hn₀⟩ := (hS.union (exc_finite h)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hn₀
  have hziota : iota (tailValue h) ∈
      (Ideal.span {iota (tailValue f)} ⊓ Ideal.span {iota (tailValue g)} : Ideal Cring) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · refine Ideal.mem_span_singleton'.mpr ⟨(s : ℕ → Cring) n₀, ?_⟩
      rw [← apply_eq_of_not_mem_exc f n₀ hn₀.1.1, ← hsn n₀,
        apply_eq_of_not_mem_exc h n₀ hn₀.2]
    · refine Ideal.mem_span_singleton'.mpr ⟨(t : ℕ → Cring) n₀, ?_⟩
      rw [← apply_eq_of_not_mem_exc g n₀ hn₀.1.2, ← htn n₀,
        apply_eq_of_not_mem_exc h n₀ hn₀.2]
  have hz : tailValue h ∈ Ideal.span (↑w : Set Balg) := by
    rw [hw, ← iota_mem_map_iff, ← hC14]
    exact hziota
  have hoffz : offSet (exc f ∪ exc g) hS (tailValue h) ∈
      Ideal.span (reGens (exc f ∪ exc g) hS w cs) :=
    re_offSet_mem_of_span _ hS _ (fun z hz' => offSet_mem_span_reGens _ hS w cs hz') hz
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = hS.toFinset ∪ (exc_finite h).toFinset :=
    ⟨_, rfl⟩
  obtain ⟨h', hh'⟩ : ∃ h' : Ramp,
      h' = h - offSet (exc f ∪ exc g) hS (tailValue h) := ⟨_, rfl⟩
  have hzero : ∀ n, n ∉ T → (h' : ℕ → Cring) n = 0 := by
    intro n hn
    rw [hT] at hn
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hn
    rw [hh', coe_sub_apply, offSet_apply_not_mem _ hS _ hn.1,
      apply_eq_of_not_mem_exc h n hn.2, sub_self]
  have hcoordmem : ∀ n, (h' : ℕ → Cring) n ∈ (Ideal.span {(f : ℕ → Cring) n} ⊓
      Ideal.span {(g : ℕ → Cring) n} : Ideal Cring) := by
    intro n
    have hoff : (offSet (exc f ∪ exc g) hS (tailValue h) : ℕ → Cring) n ∈
        (Ideal.span {(f : ℕ → Cring) n} ⊓
          Ideal.span {(g : ℕ → Cring) n} : Ideal Cring) := by
      by_cases hk : n ∈ exc f ∪ exc g
      · rw [offSet_apply_mem _ hS _ hk]
        exact Submodule.zero_mem _
      · rw [offSet_apply_not_mem _ hS _ hk]
        simp only [Set.mem_union, not_or] at hk
        rw [apply_eq_of_not_mem_exc f n hk.1, apply_eq_of_not_mem_exc g n hk.2]
        exact hziota
    rw [hh', coe_sub_apply]
    refine sub_mem ?_ hoff
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨(s : ℕ → Cring) n, (hsn n).symm⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨(t : ℕ → Cring) n, (htn n).symm⟩
  have hmem : ∀ n ∈ T, coordAt n ((h' : ℕ → Cring) n) ∈
      Ideal.span (reGens (exc f ∪ exc g) hS w cs) := by
    intro n _
    by_cases hk : n ∈ exc f ∪ exc g
    · refine re_coordAt_mem_of_span n _
        (fun c hc => coordAt_mem_span_reGens _ hS w cs hk hc) ?_
      rw [hcs n]
      exact hcoordmem n
    · refine re_coordAt_mem_of_map _ hS hk _
        (fun z hz' => offSet_mem_span_reGens _ hS w cs hz') ?_
      have hmm := hcoordmem n
      simp only [Set.mem_union, not_or] at hk
      rw [apply_eq_of_not_mem_exc f n hk.1, apply_eq_of_not_mem_exc g n hk.2, hC14,
        ← hw] at hmm
      exact hmm
  have hh'mem : h' ∈ Ideal.span (reGens (exc f ∪ exc g) hS w cs) := by
    rw [re_eq_sum_coordAt h' T hzero]
    exact sum_mem hmem
  have hsplit : h = h' + offSet (exc f ∪ exc g) hS (tailValue h) := by rw [hh']; ring
  rw [hsplit]
  exact add_mem hh'mem hoffz

set_option maxHeartbeats 4000000 in
-- instance search for `CommRing Ramp` / `CommRing Cring` (both built on the quotients
-- `Balg` and `Mmod`) dominates elaboration here; the default budget is not enough.
/-- **Step E2.** Every intersection of two principal ideals of `Ramp` is finitely
generated. The frozen theorem 14 (`C_pair_inter`) is carried as the explicit hypothesis
`hC14`, and is used at the arbitrary tail values, never only at `xa`, `xb`. -/
theorem re_pair_inter_fg_of_C (hC14 : ∀ x y : Balg,
    Ideal.span {iota x} ⊓ Ideal.span {iota y} =
      (Ideal.span {x} ⊓ Ideal.span {y}).map iota) :
    ∀ f g : Ramp, (Ideal.span {f} ⊓ Ideal.span {g} : Ideal Ramp).FG := by
  classical
  intro f g
  have hnB : ∀ I : Ideal Balg, I.FG :=
    (isNoetherianRing_iff_ideal_fg Balg).mp B_isNoetherianRing_proof
  have hnC : ∀ I : Ideal Cring, I.FG :=
    (isNoetherianRing_iff_ideal_fg Cring).mp C_isNoetherianRing_proof
  have hS : (exc f ∪ exc g).Finite := (exc_finite f).union (exc_finite g)
  obtain ⟨w, hw⟩ := hnB (Ideal.span {tailValue f} ⊓ Ideal.span {tailValue g})
  have hw' : Ideal.span (↑w : Set Balg) =
      (Ideal.span {tailValue f} ⊓ Ideal.span {tailValue g} : Ideal Balg) := hw
  choose cs hcs using fun n : ℕ =>
    hnC (Ideal.span {(f : ℕ → Cring) n} ⊓ Ideal.span {(g : ℕ → Cring) n})
  have hcs' : ∀ n : ℕ, Ideal.span (↑(cs n) : Set Cring) =
      (Ideal.span {(f : ℕ → Cring) n} ⊓
        Ideal.span {(g : ℕ → Cring) n} : Ideal Cring) := hcs
  refine Submodule.fg_def.mpr ⟨reGens (exc f ∪ exc g) hS w cs, reGens_finite _ hS w cs, ?_⟩
  refine le_antisymm (re_pair_gens_le f g hS w cs ?_ ?_)
    (re_pair_le_gens hC14 f g hS w cs hw' hcs')
  · intro z hz
    rw [← hw']
    exact Ideal.subset_span hz
  · intro n _ c hc
    rw [← hcs' n]
    exact Ideal.subset_span hc

/-! ### E3 — `Ramp` is a finite-conductor ring -/

/-- **Step E3.** `Ramp` is a finite-conductor ring, given the frozen theorems 13 and 14 as
the hypotheses `hC13` and `hC14`. The statement is otherwise byte-identical to frozen
theorem 16 (`R_finiteConductor`), with `Ramp`'s canonical `CommRing` instance. -/
theorem re_finiteConductor_of_C (hC13 : ∀ x : Balg, ann (iota x) = (ann x).map iota)
    (hC14 : ∀ x y : Balg, Ideal.span {iota x} ⊓ Ideal.span {iota y} =
      (Ideal.span {x} ⊓ Ideal.span {y}).map iota) : FiniteConductor Ramp :=
  ⟨re_ann_fg_of_C hC13, re_pair_inter_fg_of_C hC14⟩

/-! ### Frozen theorem 16, unconditionally -/

/-- **Frozen theorem 16.** `R` is a finite-conductor ring. This is the one-line
instantiation of `re_finiteConductor_of_C` at the Stage C/D results that landed in
parallel: `di_ann_eq_of_M M_ann_eq_proof` is frozen theorem 13 (`C_ann_eq`) and
`di_pair_inter_of_M M_pair_inter_proof` is frozen theorem 14 (`C_pair_inter`). -/
theorem R_finiteConductor_proof : FiniteConductor Ramp :=
  re_finiteConductor_of_C (di_ann_eq_of_M M_ann_eq_proof)
    (di_pair_inter_of_M M_pair_inter_proof)

end

end Prob4b
