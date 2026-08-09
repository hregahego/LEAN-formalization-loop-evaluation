/-
# Stage E — failure of injectivity (`Prob20/Proofs/Injectivity/`)

**E1 — the residue homomorphism.**  Since `D = 𝔽₂ + 𝔪` (frozen #2) and `1 ∉ 𝔪`,
every `d ∈ D` is congruent modulo `𝔪` to exactly one of `0`, `1`, so

```
ρ : D →+* 𝔽₂,   ρ d = 0 if (d : K) ∈ 𝔪,  ρ d = 1 otherwise
```

is a well-defined ring homomorphism (it is `D ↠ D/𝔪 ≅ 𝔽₂`).  The ring-hom laws
are all proved through the single characterising property
`rho_sub_mem_max : (d : K) - ρ d ∈ 𝔪`, which is also exactly what Stage E3 needs
in order to know `Λ (d • f) = ρ d * Λ f`.

**E2–E6.**  `V := K[X]/𝔪·Int(D)` is an `𝔽₂`-vector space in which the classes of
`p` and `t·p` are linearly independent — this is *exactly* frozen #11, #12, #13.
Splitting the resulting injection `𝔽₂² ↪ V` produces two coordinate functionals
`Λ, Μ : Int(D) →ₗ[D] 𝔽₂` (semilinear along `ρ`, i.e. honestly `D`-linear once
`𝔽₂` carries the `D`-action `d · c = ρ d · c`), and `ν f := ρ (f(0))` is a third.
The multilinear map `Ψ f = Λ (f 0) · Μ (f 1) · ∏_{i ≥ 2} ν (f i)` lifts to
`Φ` on the tensor power and separates
`τ = (p ⊗ tp ⊗ 1 ⊗ ⋯) - (tp ⊗ p ⊗ 1 ⊗ ⋯)` from `0`, while `θ τ = 0`.
-/
import Prob20.Defs
import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.Domain.Frac
import Prob20.Proofs.Theta.Basic
import Prob20.Proofs.KeyPolys.Basic
import Prob20.Proofs.Vanishing.Basic

open scoped TensorProduct

namespace Prob20

/-! ## Helpers -/

/-- `1 ∉ 𝔪`: the maximal ideal is proper.  (Same script as the anonymous guardrail
`example` of `Prob20/Proofs/Domain/Basic.lean`, reproved here under a name.) -/
theorem inj_one_not_mem_max : (1 : K) ∉ maxSet := by
  intro h
  have h2 : algebraMap A K 1 * (algebraMap A K 1)⁻¹ ∈ maxPow 1 := by simpa using h
  rw [mem_maxPow_iff 1 1 S.one_mem 1, pow_one] at h2
  have h3 : (Polynomial.X : A) ∣ 1 := dom_X_dvd_piA.trans h2
  rw [dom_X_dvd_iff] at h3
  simp only [Polynomial.eval_one] at h3
  exact one_ne_zero h3

/-- The image of `𝔽₂` in `K` lies in `T` (take denominator `1`). -/
theorem inj_zmod_mem_T (c : ZMod 2) : algebraMap (ZMod 2) K c ∈ T :=
  ⟨Polynomial.C c, 1, S.one_mem, by simp⟩

/-- `𝔪` is a `T`-submodule, so it absorbs multiplication by elements of `T`. -/
theorem inj_mul_mem_max {x y : K} (hx : x ∈ maxSet) (hy : y ∈ T) : y * x ∈ maxSet :=
  maxSet.smul_mem (⟨y, hy⟩ : ↥T) hx

/-- A constant of `𝔽₂` lies in `𝔪` only if it is `0` (else `1 ∈ 𝔪`). -/
theorem inj_zmod_eq_zero_of_mem_max {c : ZMod 2} (hc : algebraMap (ZMod 2) K c ∈ maxSet) :
    c = 0 := by
  rcases frac_zmod_two_cases c with rfl | rfl
  · rfl
  · rw [map_one] at hc
    exact absurd hc inj_one_not_mem_max

/-! ## E1 — the residue map `ρ : D → 𝔽₂` -/

open Classical in
/-- The underlying function of `ρ`: `0` on `𝔪`, `1` off it. -/
noncomputable def inj_rhoFun (d : ↥Dom) : ZMod 2 :=
  if (d : K) ∈ maxSet then 0 else 1

/-- The characterising property: `d ≡ ρ d` modulo `𝔪`.  This is where frozen #2
(`D = 𝔽₂ + 𝔪`) enters. -/
theorem inj_rhoFun_sub_mem_max (d : ↥Dom) :
    (d : K) - algebraMap (ZMod 2) K (inj_rhoFun d) ∈ maxSet := by
  unfold inj_rhoFun
  by_cases h : (d : K) ∈ maxSet
  · rw [if_pos h, map_zero, sub_zero]
    exact h
  · rw [if_neg h, map_one]
    rcases (mem_Dom_iff_mem_max_or_sub_one_mem_max_proof (d : K)).1 d.2 with h0 | h1
    · exact absurd h0 h
    · exact h1

/-- …and it determines `ρ d` uniquely, because `𝔪` contains no nonzero constant. -/
theorem inj_eq_of_sub_mem_max {d : ↥Dom} {c : ZMod 2}
    (h : (d : K) - algebraMap (ZMod 2) K c ∈ maxSet) : inj_rhoFun d = c := by
  have h1 := inj_rhoFun_sub_mem_max d
  have h3 := maxSet.sub_mem h1 h
  have h4 : (d : K) - algebraMap (ZMod 2) K (inj_rhoFun d)
      - ((d : K) - algebraMap (ZMod 2) K c)
      = algebraMap (ZMod 2) K (c - inj_rhoFun d) := by
    rw [map_sub]; ring
  rw [h4] at h3
  have h5 := inj_zmod_eq_zero_of_mem_max h3
  exact (sub_eq_zero.mp h5).symm

theorem inj_rhoFun_zero : inj_rhoFun 0 = 0 :=
  inj_eq_of_sub_mem_max (by simp)

theorem inj_rhoFun_one : inj_rhoFun 1 = 1 :=
  inj_eq_of_sub_mem_max (by simp)

theorem inj_rhoFun_add (d e : ↥Dom) :
    inj_rhoFun (d + e) = inj_rhoFun d + inj_rhoFun e := by
  refine inj_eq_of_sub_mem_max ?_
  have h := maxSet.add_mem (inj_rhoFun_sub_mem_max d) (inj_rhoFun_sub_mem_max e)
  have key : (d : K) - algebraMap (ZMod 2) K (inj_rhoFun d)
      + ((e : K) - algebraMap (ZMod 2) K (inj_rhoFun e))
      = ((d + e : ↥Dom) : K) - algebraMap (ZMod 2) K (inj_rhoFun d + inj_rhoFun e) := by
    push_cast [map_add]
    ring
  rwa [key] at h

theorem inj_rhoFun_mul (d e : ↥Dom) :
    inj_rhoFun (d * e) = inj_rhoFun d * inj_rhoFun e := by
  refine inj_eq_of_sub_mem_max ?_
  have hd := inj_mul_mem_max (inj_rhoFun_sub_mem_max d) (Dom_le_T e.2)
  have he := inj_mul_mem_max (inj_rhoFun_sub_mem_max e) (inj_zmod_mem_T (inj_rhoFun d))
  have h := maxSet.add_mem hd he
  have key : (e : K) * ((d : K) - algebraMap (ZMod 2) K (inj_rhoFun d))
      + algebraMap (ZMod 2) K (inj_rhoFun d)
        * ((e : K) - algebraMap (ZMod 2) K (inj_rhoFun e))
      = ((d * e : ↥Dom) : K) - algebraMap (ZMod 2) K (inj_rhoFun d * inj_rhoFun e) := by
    push_cast [map_mul]
    ring
  rwa [key] at h

/-- **Stage E1.** The residue homomorphism `ρ : D →+* 𝔽₂`, i.e. `D ↠ D/𝔪 ≅ 𝔽₂`. -/
noncomputable def rho : ↥Dom →+* ZMod 2 where
  toFun := inj_rhoFun
  map_one' := inj_rhoFun_one
  map_mul' := inj_rhoFun_mul
  map_zero' := inj_rhoFun_zero
  map_add' := inj_rhoFun_add

theorem rho_apply (d : ↥Dom) : rho d = inj_rhoFun d := rfl

/-- `ρ d = 0` exactly on `𝔪`. -/
theorem rho_eq_zero_iff : ∀ d : ↥Dom, rho d = 0 ↔ (d : K) ∈ maxSet := by
  intro d
  constructor
  · intro h
    have h1 := inj_rhoFun_sub_mem_max d
    rw [rho_apply] at h
    rwa [h, map_zero, sub_zero] at h1
  · intro h
    rw [rho_apply]
    exact inj_eq_of_sub_mem_max (by simpa using h)

/-- `d - ρ d ∈ 𝔪`: exactly the form Stage E3 consumes for `Λ (d • f) = ρ d * Λ f`. -/
theorem rho_sub_mem_max : ∀ d : ↥Dom, (d : K) - algebraMap (ZMod 2) K (rho d) ∈ maxSet :=
  inj_rhoFun_sub_mem_max

/-! ### Guardrails -/

example : rho 0 = 0 := map_zero rho

example : rho 1 = 1 := map_one rho

example : rho ⟨piK, max_le_Dom piK ⟨1, T.one_mem, by simp⟩⟩ = 0 :=
  (rho_eq_zero_iff _).2 ⟨1, T.one_mem, by simp⟩

/-! ## The `↥Dom`-module structure on `𝔽₂`

`𝔽₂ = D/𝔪` is a `D`-algebra along `ρ`.  This instance is **`local` to this file**
(a global one would risk a diamond with `Algebra ↥Dom K`); it is what lets the
functionals below be honest `↥Dom`-linear maps and lets `PiTensorProduct.lift`
accept them. -/

noncomputable local instance instAlgDomZMod : Algebra ↥Dom (ZMod 2) := rho.toAlgebra

theorem inj_smul_zmod (d : ↥Dom) (c : ZMod 2) : d • c = rho d * c := rfl

/-! ## E2 — `p̄` and `(t·p)‾` are `𝔽₂`-independent in `K[X]/𝔪·Int(D)` -/

/-- `𝔪·Int(D)` seen as an `𝔽₂`-submodule of the ambient `K[X]`.  (An `𝔽₂`-scalar is
`0` or `1`, so the `↥Dom`-submodule `maxSmulInt` is already closed under it.) -/
noncomputable def inj_N : Submodule (ZMod 2) (Polynomial K) where
  carrier := {G : Polynomial K | G ∈ maxSmulInt}
  zero_mem' := Submodule.zero_mem maxSmulInt
  add_mem' ha hb := Submodule.add_mem maxSmulInt ha hb
  smul_mem' c G hG := by
    rcases frac_zmod_two_cases c with rfl | rfl
    · rw [zero_smul]
      exact Submodule.zero_mem maxSmulInt
    · rw [one_smul]
      exact hG

theorem inj_mem_N_iff (G : Polynomial K) : G ∈ inj_N ↔ G ∈ maxSmulInt := Iff.rfl

/-- The defining generators `c·f` (`c ∈ 𝔪`, `f ∈ Int(D)`) of `𝔪·Int(D)`. -/
theorem inj_gen_mem (c : K) (hc : c ∈ maxSet) (f : ↥IntD) :
    Polynomial.C c * (f : Polynomial K) ∈ maxSmulInt :=
  Submodule.subset_span ⟨c, hc, (f : Polynomial K), f.2, rfl⟩

theorem inj_mkQ_eq_zero_iff (G : Polynomial K) : inj_N.mkQ G = 0 ↔ G ∈ maxSmulInt := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact inj_mem_N_iff G

/-- The `𝔽₂`-linear map `(c₀, c₁) ↦ c₀·p̄ + c₁·(t·p)‾` into `K[X]/𝔪·Int(D)`. -/
noncomputable def inj_kappa : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Polynomial K ⧸ inj_N) where
  toFun c := c 0 • inj_N.mkQ p + c 1 • inj_N.mkQ (Polynomial.C tK * p)
  map_add' c d := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

theorem inj_kappa_apply (c : Fin 2 → ZMod 2) :
    inj_kappa c = c 0 • inj_N.mkQ p + c 1 • inj_N.mkQ (Polynomial.C tK * p) := rfl

theorem inj_p_add_tp : p + Polynomial.C tK * p = Polynomial.C (tK + 1) * p := by
  rw [map_add, map_one]; ring

/-- **E2.**  `p̄` and `(t·p)‾` are linearly independent over `𝔽₂` in `K[X]/𝔪·Int(D)`.
The three nonzero `𝔽₂`-combinations are `p`, `t·p` and `(t+1)·p`, so this is exactly
frozen #11, #12, #13. -/
theorem inj_kappa_ker : LinearMap.ker inj_kappa = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro c hc
  rw [inj_kappa_apply, ← map_smul, ← map_smul, ← map_add, inj_mkQ_eq_zero_iff] at hc
  have h0 := frac_zmod_two_cases (c 0)
  have h1 := frac_zmod_two_cases (c 1)
  have hval : ∀ i : Fin 2, c i = (0 : Fin 2 → ZMod 2) i := by
    intro i
    fin_cases i
    · rcases h0 with h | h
      · simpa using h
      rcases h1 with h' | h'
      · rw [h, h', one_smul, zero_smul, add_zero] at hc
        exact absurd hc p_not_mem_max_int_proof
      · rw [h, h', one_smul, one_smul, inj_p_add_tp] at hc
        exact absurd hc t_add_one_mul_p_not_mem_max_int_proof
    · rcases h1 with h | h
      · simpa using h
      rcases h0 with h' | h'
      · rw [h, h', one_smul, zero_smul, zero_add] at hc
        exact absurd hc t_mul_p_not_mem_max_int_proof
      · rw [h, h', one_smul, one_smul, inj_p_add_tp] at hc
        exact absurd hc t_add_one_mul_p_not_mem_max_int_proof
  exact funext hval

/-! ## E3 — the functionals `Λ`, `Μ`, `ν` -/

theorem inj_exists_sigma :
    ∃ σ : (Polynomial K ⧸ inj_N) →ₗ[ZMod 2] (Fin 2 → ZMod 2), σ ∘ₗ inj_kappa = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective inj_kappa inj_kappa_ker

/-- A left inverse of `inj_kappa`; its two components are the coordinate functionals. -/
noncomputable def inj_sigma : (Polynomial K ⧸ inj_N) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  inj_exists_sigma.choose

theorem inj_sigma_spec : inj_sigma ∘ₗ inj_kappa = LinearMap.id :=
  inj_exists_sigma.choose_spec

theorem inj_sigma_kappa (c : Fin 2 → ZMod 2) : inj_sigma (inj_kappa c) = c :=
  LinearMap.congr_fun inj_sigma_spec c

theorem inj_sigma_p : inj_sigma (inj_N.mkQ p) = ![1, 0] := by
  have h := inj_sigma_kappa ![1, 0]
  rwa [inj_kappa_apply, show (![1, 0] : Fin 2 → ZMod 2) 0 = 1 from rfl,
    show (![1, 0] : Fin 2 → ZMod 2) 1 = 0 from rfl, one_smul, zero_smul, add_zero] at h

theorem inj_sigma_tp : inj_sigma (inj_N.mkQ (Polynomial.C tK * p)) = ![0, 1] := by
  have h := inj_sigma_kappa ![0, 1]
  rwa [inj_kappa_apply, show (![0, 1] : Fin 2 → ZMod 2) 0 = 0 from rfl,
    show (![0, 1] : Fin 2 → ZMod 2) 1 = 1 from rfl, one_smul, zero_smul, zero_add] at h

/-- The `↥Dom`-action on `Int(D)` is multiplication by the constant `(d : K)`. -/
theorem inj_coe_smul (d : ↥Dom) (f : ↥IntD) :
    ((d • f : ↥IntD) : Polynomial K) = Polynomial.C (d : K) * (f : Polynomial K) := by
  rw [SetLike.val_smul, Algebra.smul_def, Polynomial.algebraMap_apply]
  rfl

/-- On classes of elements of `Int(D)`, the `↥Dom`-action on `K[X]/𝔪·Int(D)` factors
through `ρ` — because `d - ρ d ∈ 𝔪` (`rho_sub_mem_max`), so `(d - ρ d)·f` is a
generator of `𝔪·Int(D)`. -/
theorem inj_mkQ_smul (d : ↥Dom) (f : ↥IntD) :
    inj_N.mkQ ((d • f : ↥IntD) : Polynomial K)
      = rho d • inj_N.mkQ ((f : ↥IntD) : Polynomial K) := by
  have hgen : Polynomial.C ((d : K) - algebraMap (ZMod 2) K (rho d)) * (f : Polynomial K)
      ∈ maxSmulInt := inj_gen_mem _ (rho_sub_mem_max d) f
  rcases frac_zmod_two_cases (rho d) with h | h
  · rw [h, map_zero, sub_zero] at hgen
    rw [h, zero_smul, inj_coe_smul, inj_mkQ_eq_zero_iff]
    exact hgen
  · rw [h, map_one] at hgen
    rw [h, one_smul, inj_coe_smul, ← sub_eq_zero, ← map_sub, inj_mkQ_eq_zero_iff]
    have heq : Polynomial.C (d : K) * (f : Polynomial K) - (f : Polynomial K)
        = Polynomial.C ((d : K) - 1) * (f : Polynomial K) := by
      rw [map_sub, map_one]; ring
    rwa [heq]

/-- **E3.**  The two coordinate functionals `Λ = inj_Lin 0` and `Μ = inj_Lin 1`
on `Int(D)`, `↥Dom`-linear for the `ρ`-action on `𝔽₂`. -/
noncomputable def inj_Lin (k : Fin 2) : ↥IntD →ₗ[↥Dom] ZMod 2 where
  toFun f := inj_sigma (inj_N.mkQ ((f : ↥IntD) : Polynomial K)) k
  map_add' f g := by
    have h : ((f + g : ↥IntD) : Polynomial K) = (f : Polynomial K) + (g : Polynomial K) := rfl
    rw [h, map_add, map_add]
    rfl
  map_smul' d f := by
    rw [inj_mkQ_smul, map_smul, RingHom.id_apply, inj_smul_zmod]
    rfl

theorem inj_Lin_apply (k : Fin 2) (f : ↥IntD) :
    inj_Lin k f = inj_sigma (inj_N.mkQ ((f : ↥IntD) : Polynomial K)) k := rfl

theorem inj_Lin_p (k : Fin 2) : inj_Lin k ⟨p, p_mem_int⟩ = ![1, 0] k := by
  rw [inj_Lin_apply]
  exact congrFun inj_sigma_p k

theorem inj_Lin_tp (k : Fin 2) :
    inj_Lin k ⟨Polynomial.C tK * p, t_mul_p_mem_int⟩ = ![0, 1] k := by
  rw [inj_Lin_apply]
  exact congrFun inj_sigma_tp k

/-- Evaluation at `0`, as a map `Int(D) → D` (well defined by `eval_zero_mem_Dom`). -/
noncomputable def inj_ev0 (f : ↥IntD) : ↥Dom :=
  ⟨(f : Polynomial K).eval 0, eval_zero_mem_Dom _ f.2⟩

theorem inj_ev0_add (f g : ↥IntD) : inj_ev0 (f + g) = inj_ev0 f + inj_ev0 g :=
  Subtype.ext (by simp [inj_ev0])

theorem inj_ev0_one : inj_ev0 1 = 1 :=
  Subtype.ext (by simp [inj_ev0])

theorem inj_ev0_smul (d : ↥Dom) (f : ↥IntD) : inj_ev0 (d • f) = d * inj_ev0 f := by
  refine Subtype.ext ?_
  simp only [inj_ev0, inj_coe_smul, Polynomial.eval_mul, Polynomial.eval_C, Subring.coe_mul]

/-- **E3.**  The third functional `ν f = ρ (f(0))`. -/
noncomputable def inj_nu : ↥IntD →ₗ[↥Dom] ZMod 2 where
  toFun f := rho (inj_ev0 f)
  map_add' f g := by rw [inj_ev0_add, map_add]
  map_smul' d f := by
    rw [RingHom.id_apply, inj_smul_zmod, inj_ev0_smul, map_mul]

theorem inj_nu_one : inj_nu 1 = 1 := by
  change rho (inj_ev0 1) = 1
  rw [inj_ev0_one, map_one]

/-! ## E4 — the separating functional on the tensor power -/

/-- The family of functionals: `Λ` in slot `0`, `Μ` in slot `1`, `ν` everywhere else. -/
noncomputable def inj_phi (n : ℕ) : Fin (n + 2) → (↥IntD →ₗ[↥Dom] ZMod 2) :=
  Fin.cons (inj_Lin 0) (Fin.cons (inj_Lin 1) fun _ => inj_nu)

/-- **E4.**  The `↥Dom`-multilinear map `f ↦ Λ (f 0) · Μ (f 1) · ∏_{i ≥ 2} ν (f i)`.
Multilinearity is free: it is `mkPiAlgebra` composed with linear maps. -/
noncomputable def inj_Psi (n : ℕ) :
    MultilinearMap ↥Dom (fun _ : Fin (n + 2) => ↥IntD) (ZMod 2) :=
  (MultilinearMap.mkPiAlgebra ↥Dom (Fin (n + 2)) (ZMod 2)).compLinearMap (inj_phi n)

/-- **E4.**  The induced functional `Φ` on the tensor power. -/
noncomputable def inj_Phi (n : ℕ) :
    (⨂[↥Dom] (_ : Fin (n + 2)), ↥IntD) →ₗ[↥Dom] ZMod 2 :=
  PiTensorProduct.lift (inj_Psi n)

theorem inj_Phi_tprod (n : ℕ) (f : Fin (n + 2) → ↥IntD) :
    inj_Phi n (PiTensorProduct.tprod ↥Dom f) = ∏ i, inj_phi n i (f i) := by
  simp [inj_Phi, inj_Psi, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]

/-! ## E5 — the tensor `τ` -/

/-- `a = (p, t·p, 1, …, 1)`. -/
noncomputable def inj_a (n : ℕ) : Fin (n + 2) → ↥IntD :=
  Fin.cons ⟨p, p_mem_int⟩ (Fin.cons ⟨Polynomial.C tK * p, t_mul_p_mem_int⟩ fun _ => 1)

/-- `b = (t·p, p, 1, …, 1)`, i.e. `a` with the first two slots swapped. -/
noncomputable def inj_b (n : ℕ) : Fin (n + 2) → ↥IntD :=
  Fin.cons ⟨Polynomial.C tK * p, t_mul_p_mem_int⟩ (Fin.cons ⟨p, p_mem_int⟩ fun _ => 1)

theorem inj_Phi_a (n : ℕ) : inj_Phi n (PiTensorProduct.tprod ↥Dom (inj_a n)) = 1 := by
  rw [inj_Phi_tprod, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [inj_phi, inj_a, inj_Lin_p, inj_Lin_tp, inj_nu_one]

theorem inj_Phi_b (n : ℕ) : inj_Phi n (PiTensorProduct.tprod ↥Dom (inj_b n)) = 0 := by
  rw [inj_Phi_tprod, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [inj_phi, inj_b, inj_Lin_p, inj_Lin_tp, inj_nu_one]

/-- **E5.**  `θ` does not separate the two pure tensors: pulling the constant `t`
out of `Polynomial.aeval` gives the same product both times. -/
theorem inj_theta_ab (n : ℕ) :
    theta ↥Dom K (n + 2) (PiTensorProduct.tprod ↥Dom (inj_a n))
      = theta ↥Dom K (n + 2) (PiTensorProduct.tprod ↥Dom (inj_b n)) := by
  rw [theta_apply_tprod_proof, theta_apply_tprod_proof, Fin.prod_univ_succ, Fin.prod_univ_succ,
    Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [inj_a, inj_b, Fin.cons_zero, Fin.cons_succ, map_mul, Polynomial.aeval_C,
    OneMemClass.coe_one, map_one, Finset.prod_const_one, mul_one]
  ring

/-! ### Guardrails for E5 (they catch a mis-ordered `Λ`/`Μ`) -/

example (n : ℕ) : inj_Phi n (PiTensorProduct.tprod ↥Dom (inj_a n)) = 1 := inj_Phi_a n

example (n : ℕ) : inj_Phi n (PiTensorProduct.tprod ↥Dom (inj_b n)) = 0 := inj_Phi_b n

/-! ## E6 — frozen #14 -/

/-- **Frozen #14.**  `θₙ` is not injective for any `n ≥ 2`: the tensor
`τ = tprod a - tprod b` is nonzero (the functional `Φ` of E4 takes the value `1` on it)
but `θ τ = 0`. -/
theorem theta_not_injective_proof : ∀ n : ℕ, ¬ Function.Injective (theta ↥Dom K (n + 2)) := by
  intro n hinj
  have hth : theta ↥Dom K (n + 2)
      (PiTensorProduct.tprod ↥Dom (inj_a n) - PiTensorProduct.tprod ↥Dom (inj_b n)) = 0 := by
    rw [map_sub, inj_theta_ab, sub_self]
  have hzero : PiTensorProduct.tprod ↥Dom (inj_a n)
      - PiTensorProduct.tprod ↥Dom (inj_b n) = 0 := hinj (by rw [hth, map_zero])
  have hPhi : inj_Phi n
      (PiTensorProduct.tprod ↥Dom (inj_a n) - PiTensorProduct.tprod ↥Dom (inj_b n)) = 1 := by
    rw [map_sub, inj_Phi_a, inj_Phi_b, sub_zero]
  rw [hzero, map_zero] at hPhi
  exact zero_ne_one hPhi

end Prob20
