/-
Stage B -- the ring `A_q`, its coordinates and multiplication table,
   `J^2 = W`, `J^3 = 0`, Noetherianity (B1-B8).

B1 (the three `Jmod` algebra instances) is already discharged in `Defs.lean`.
Everything below is proved at the *generic* base `(B, τ, q)` wherever possible so
that Stage F can reuse it at `B = Polynomial Dbase`, `τ = C tD`; only the three
frozen statements are specialised to `B = Dbase`, `τ = tD`.
-/
import Prob30c.Defs

namespace Prob30c

namespace Alg

variable {B : Type} [CommRing B] {τ : B} {q : ℕ}

/-! ## B2 — the seven coordinates of `Alg B τ q` -/

/-- The `e₁`-coordinate. -/
def α₁ (x : Alg B τ q) : B := x.snd.1
/-- The `e₂`-coordinate. -/
def α₂ (x : Alg B τ q) : B := x.snd.2.1
/-- The `e₃`-coordinate. -/
def α₃ (x : Alg B τ q) : B := x.snd.2.2.1
/-- The `u₁`-coordinate. -/
def γ₁ (x : Alg B τ q) : B := x.snd.2.2.2.1
/-- The `u₂`-coordinate. -/
def γ₂ (x : Alg B τ q) : B := x.snd.2.2.2.2.1
/-- The `s`-coordinate, living in `B ⧸ (τ^q)`. -/
def σ (x : Alg B τ q) : Quo B τ q := x.snd.2.2.2.2.2

/-- Two elements of `Alg B τ q` agree iff their seven coordinates agree. -/
theorem ext_iff' {x y : Alg B τ q} :
    x = y ↔ x.fst = y.fst ∧ α₁ x = α₁ y ∧ α₂ x = α₂ y ∧ α₃ x = α₃ y ∧
      γ₁ x = γ₁ y ∧ γ₂ x = γ₂ y ∧ σ x = σ y := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact Unitization.ext h0 (Jmod.ext' h1 h2 h3 h4 h5 h6)

/-- The seven-coordinate extensionality principle. -/
theorem ext' {x y : Alg B τ q} (h0 : x.fst = y.fst) (h1 : α₁ x = α₁ y)
    (h2 : α₂ x = α₂ y) (h3 : α₃ x = α₃ y) (h4 : γ₁ x = γ₁ y) (h5 : γ₂ x = γ₂ y)
    (h6 : σ x = σ y) : x = y :=
  ext_iff'.2 ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-! ### Coordinates of `0`, `1`, `+`, `-`, `•`, `algebraMap` -/

@[simp] theorem α₁_zero : α₁ (0 : Alg B τ q) = 0 := rfl
@[simp] theorem α₂_zero : α₂ (0 : Alg B τ q) = 0 := rfl
@[simp] theorem α₃_zero : α₃ (0 : Alg B τ q) = 0 := rfl
@[simp] theorem γ₁_zero : γ₁ (0 : Alg B τ q) = 0 := rfl
@[simp] theorem γ₂_zero : γ₂ (0 : Alg B τ q) = 0 := rfl
@[simp] theorem σ_zero : σ (0 : Alg B τ q) = 0 := rfl

@[simp] theorem α₁_one : α₁ (1 : Alg B τ q) = 0 := rfl
@[simp] theorem α₂_one : α₂ (1 : Alg B τ q) = 0 := rfl
@[simp] theorem α₃_one : α₃ (1 : Alg B τ q) = 0 := rfl
@[simp] theorem γ₁_one : γ₁ (1 : Alg B τ q) = 0 := rfl
@[simp] theorem γ₂_one : γ₂ (1 : Alg B τ q) = 0 := rfl
@[simp] theorem σ_one : σ (1 : Alg B τ q) = 0 := rfl

@[simp] theorem α₁_add (x y : Alg B τ q) : α₁ (x + y) = α₁ x + α₁ y := rfl
@[simp] theorem α₂_add (x y : Alg B τ q) : α₂ (x + y) = α₂ x + α₂ y := rfl
@[simp] theorem α₃_add (x y : Alg B τ q) : α₃ (x + y) = α₃ x + α₃ y := rfl
@[simp] theorem γ₁_add (x y : Alg B τ q) : γ₁ (x + y) = γ₁ x + γ₁ y := rfl
@[simp] theorem γ₂_add (x y : Alg B τ q) : γ₂ (x + y) = γ₂ x + γ₂ y := rfl
@[simp] theorem σ_add (x y : Alg B τ q) : σ (x + y) = σ x + σ y := rfl

@[simp] theorem α₁_neg (x : Alg B τ q) : α₁ (-x) = -α₁ x := rfl
@[simp] theorem α₂_neg (x : Alg B τ q) : α₂ (-x) = -α₂ x := rfl
@[simp] theorem α₃_neg (x : Alg B τ q) : α₃ (-x) = -α₃ x := rfl
@[simp] theorem γ₁_neg (x : Alg B τ q) : γ₁ (-x) = -γ₁ x := rfl
@[simp] theorem γ₂_neg (x : Alg B τ q) : γ₂ (-x) = -γ₂ x := rfl
@[simp] theorem σ_neg (x : Alg B τ q) : σ (-x) = -σ x := rfl

@[simp] theorem α₁_smul (b : B) (x : Alg B τ q) : α₁ (b • x) = b * α₁ x := rfl
@[simp] theorem α₂_smul (b : B) (x : Alg B τ q) : α₂ (b • x) = b * α₂ x := rfl
@[simp] theorem α₃_smul (b : B) (x : Alg B τ q) : α₃ (b • x) = b * α₃ x := rfl
@[simp] theorem γ₁_smul (b : B) (x : Alg B τ q) : γ₁ (b • x) = b * γ₁ x := rfl
@[simp] theorem γ₂_smul (b : B) (x : Alg B τ q) : γ₂ (b • x) = b * γ₂ x := rfl
@[simp] theorem σ_smul (b : B) (x : Alg B τ q) : σ (b • x) = b • σ x := rfl

@[simp] theorem fst_algebraMap (b : B) :
    (algebraMap B (Alg B τ q) b).fst = b := rfl
@[simp] theorem α₁_algebraMap (b : B) : α₁ (algebraMap B (Alg B τ q) b) = 0 := rfl
@[simp] theorem α₂_algebraMap (b : B) : α₂ (algebraMap B (Alg B τ q) b) = 0 := rfl
@[simp] theorem α₃_algebraMap (b : B) : α₃ (algebraMap B (Alg B τ q) b) = 0 := rfl
@[simp] theorem γ₁_algebraMap (b : B) : γ₁ (algebraMap B (Alg B τ q) b) = 0 := rfl
@[simp] theorem γ₂_algebraMap (b : B) : γ₂ (algebraMap B (Alg B τ q) b) = 0 := rfl
@[simp] theorem σ_algebraMap (b : B) : σ (algebraMap B (Alg B τ q) b) = 0 := rfl

/-! ### Coordinates of the generators -/

@[simp] theorem fst_e₁ : (e₁ B τ q).fst = 0 := rfl
@[simp] theorem α₁_e₁ : α₁ (e₁ B τ q) = 1 := rfl
@[simp] theorem α₂_e₁ : α₂ (e₁ B τ q) = 0 := rfl
@[simp] theorem α₃_e₁ : α₃ (e₁ B τ q) = 0 := rfl
@[simp] theorem γ₁_e₁ : γ₁ (e₁ B τ q) = 0 := rfl
@[simp] theorem γ₂_e₁ : γ₂ (e₁ B τ q) = 0 := rfl
@[simp] theorem σ_e₁ : σ (e₁ B τ q) = 0 := rfl

@[simp] theorem fst_e₂ : (e₂ B τ q).fst = 0 := rfl
@[simp] theorem α₁_e₂ : α₁ (e₂ B τ q) = 0 := rfl
@[simp] theorem α₂_e₂ : α₂ (e₂ B τ q) = 1 := rfl
@[simp] theorem α₃_e₂ : α₃ (e₂ B τ q) = 0 := rfl
@[simp] theorem γ₁_e₂ : γ₁ (e₂ B τ q) = 0 := rfl
@[simp] theorem γ₂_e₂ : γ₂ (e₂ B τ q) = 0 := rfl
@[simp] theorem σ_e₂ : σ (e₂ B τ q) = 0 := rfl

@[simp] theorem fst_e₃ : (e₃ B τ q).fst = 0 := rfl
@[simp] theorem α₁_e₃ : α₁ (e₃ B τ q) = 0 := rfl
@[simp] theorem α₂_e₃ : α₂ (e₃ B τ q) = 0 := rfl
@[simp] theorem α₃_e₃ : α₃ (e₃ B τ q) = 1 := rfl
@[simp] theorem γ₁_e₃ : γ₁ (e₃ B τ q) = 0 := rfl
@[simp] theorem γ₂_e₃ : γ₂ (e₃ B τ q) = 0 := rfl
@[simp] theorem σ_e₃ : σ (e₃ B τ q) = 0 := rfl

@[simp] theorem fst_u₁ : (u₁ B τ q).fst = 0 := rfl
@[simp] theorem α₁_u₁ : α₁ (u₁ B τ q) = 0 := rfl
@[simp] theorem α₂_u₁ : α₂ (u₁ B τ q) = 0 := rfl
@[simp] theorem α₃_u₁ : α₃ (u₁ B τ q) = 0 := rfl
@[simp] theorem γ₁_u₁ : γ₁ (u₁ B τ q) = 1 := rfl
@[simp] theorem γ₂_u₁ : γ₂ (u₁ B τ q) = 0 := rfl
@[simp] theorem σ_u₁ : σ (u₁ B τ q) = 0 := rfl

@[simp] theorem fst_u₂ : (u₂ B τ q).fst = 0 := rfl
@[simp] theorem α₁_u₂ : α₁ (u₂ B τ q) = 0 := rfl
@[simp] theorem α₂_u₂ : α₂ (u₂ B τ q) = 0 := rfl
@[simp] theorem α₃_u₂ : α₃ (u₂ B τ q) = 0 := rfl
@[simp] theorem γ₁_u₂ : γ₁ (u₂ B τ q) = 0 := rfl
@[simp] theorem γ₂_u₂ : γ₂ (u₂ B τ q) = 1 := rfl
@[simp] theorem σ_u₂ : σ (u₂ B τ q) = 0 := rfl

@[simp] theorem fst_sElt : (sElt B τ q).fst = 0 := rfl
@[simp] theorem α₁_sElt : α₁ (sElt B τ q) = 0 := rfl
@[simp] theorem α₂_sElt : α₂ (sElt B τ q) = 0 := rfl
@[simp] theorem α₃_sElt : α₃ (sElt B τ q) = 0 := rfl
@[simp] theorem γ₁_sElt : γ₁ (sElt B τ q) = 0 := rfl
@[simp] theorem γ₂_sElt : γ₂ (sElt B τ q) = 0 := rfl
@[simp] theorem σ_sElt :
    σ (sElt B τ q) = Ideal.Quotient.mk (Ideal.span {τ ^ q}) 1 := rfl

theorem tElt_def : tElt B τ q = algebraMap B (Alg B τ q) τ := rfl

@[simp] theorem fst_tElt : (tElt B τ q).fst = τ := rfl
@[simp] theorem α₁_tElt : α₁ (tElt B τ q) = 0 := rfl
@[simp] theorem α₂_tElt : α₂ (tElt B τ q) = 0 := rfl
@[simp] theorem α₃_tElt : α₃ (tElt B τ q) = 0 := rfl
@[simp] theorem γ₁_tElt : γ₁ (tElt B τ q) = 0 := rfl
@[simp] theorem γ₂_tElt : γ₂ (tElt B τ q) = 0 := rfl
@[simp] theorem σ_tElt : σ (tElt B τ q) = 0 := rfl

/-! ## B4 — the single general product formula

Every downstream computation in `Alg B τ q` is an instance of these seven
identities; they are read off once from `Unitization`'s multiplication
`(x * y).snd = x.fst • y.snd + y.fst • x.snd + x.snd * y.snd` together with the
frozen table `Jmod.mul_def`. -/

@[simp] theorem α₁_mul (x y : Alg B τ q) :
    α₁ (x * y) = x.fst * α₁ y + y.fst * α₁ x := add_zero _

@[simp] theorem α₂_mul (x y : Alg B τ q) :
    α₂ (x * y) = x.fst * α₂ y + y.fst * α₂ x := add_zero _

@[simp] theorem α₃_mul (x y : Alg B τ q) :
    α₃ (x * y) = x.fst * α₃ y + y.fst * α₃ x := add_zero _

@[simp] theorem γ₁_mul (x y : Alg B τ q) :
    γ₁ (x * y) = x.fst * γ₁ y + y.fst * γ₁ x
      + (α₂ x * α₃ y + α₃ x * α₂ y + α₃ x * α₃ y) := rfl

@[simp] theorem γ₂_mul (x y : Alg B τ q) :
    γ₂ (x * y) = x.fst * γ₂ y + y.fst * γ₂ x
      + (α₁ x * α₃ y + α₃ x * α₁ y + α₂ x * α₂ y) := rfl

@[simp] theorem σ_mul (x y : Alg B τ q) :
    σ (x * y) = x.fst • σ y + y.fst • σ x
      + Ideal.Quotient.mk (Ideal.span {τ ^ q}) (α₁ x * α₃ y + α₃ x * α₁ y) := rfl

/-! ## B3 — the multiplication table -/

/-- Anything with vanishing `fst` and vanishing `e`-coordinates (i.e. anything in
`W`) annihilates everything with vanishing `fst` (i.e. everything in `J`). -/
theorem mul_eq_zero_of_coords {x y : Alg B τ q} (hf : x.fst = 0) (h₁ : α₁ x = 0)
    (h₂ : α₂ x = 0) (h₃ : α₃ x = 0) (hy : y.fst = 0) : x * y = 0 := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hf, h₁, h₂, h₃, hy]

theorem e₁_mul_e₁ : e₁ B τ q * e₁ B τ q = 0 := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

theorem e₁_mul_e₂ : e₁ B τ q * e₂ B τ q = 0 := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

theorem e₂_mul_e₁ : e₂ B τ q * e₁ B τ q = 0 := by
  rw [mul_comm]; exact e₁_mul_e₂

theorem e₁_mul_e₃ : e₁ B τ q * e₃ B τ q = u₂ B τ q + sElt B τ q := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

theorem e₃_mul_e₁ : e₃ B τ q * e₁ B τ q = u₂ B τ q + sElt B τ q := by
  rw [mul_comm]; exact e₁_mul_e₃

theorem e₂_mul_e₂ : e₂ B τ q * e₂ B τ q = u₂ B τ q := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

theorem e₂_mul_e₃ : e₂ B τ q * e₃ B τ q = u₁ B τ q := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

theorem e₃_mul_e₂ : e₃ B τ q * e₂ B τ q = u₁ B τ q := by
  rw [mul_comm]; exact e₂_mul_e₃

theorem e₃_mul_e₃ : e₃ B τ q * e₃ B τ q = u₁ B τ q := by
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

/-! ### `u₁`, `u₂`, `s` annihilate `J` -/

theorem u₁_mul_e₁ : u₁ B τ q * e₁ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₁_mul_e₂ : u₁ B τ q * e₂ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₁_mul_e₃ : u₁ B τ q * e₃ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₁_mul_u₁ : u₁ B τ q * u₁ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₁_mul_u₂ : u₁ B τ q * u₂ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₁_mul_sElt : u₁ B τ q * sElt B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl

theorem u₂_mul_e₁ : u₂ B τ q * e₁ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₂_mul_e₂ : u₂ B τ q * e₂ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₂_mul_e₃ : u₂ B τ q * e₃ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₂_mul_u₁ : u₂ B τ q * u₁ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₂_mul_u₂ : u₂ B τ q * u₂ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem u₂_mul_sElt : u₂ B τ q * sElt B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl

theorem sElt_mul_e₁ : sElt B τ q * e₁ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem sElt_mul_e₂ : sElt B τ q * e₂ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem sElt_mul_e₃ : sElt B τ q * e₃ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem sElt_mul_u₁ : sElt B τ q * u₁ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem sElt_mul_u₂ : sElt B τ q * u₂ B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl
theorem sElt_mul_sElt : sElt B τ q * sElt B τ q = 0 := mul_eq_zero_of_coords rfl rfl rfl rfl rfl

/-! ### The char-2 identity behind `W ≤ J²` -/

theorem e₁_mul_e₃_add_e₂_mul_e₂ (h2 : (2 : B) = 0) :
    e₁ B τ q * e₃ B τ q + e₂ B τ q * e₂ B τ q = sElt B τ q := by
  rw [e₁_mul_e₃, e₂_mul_e₂]
  refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp
  linear_combination h2

/-! ### `algebraMap b * sElt` — the `s`-line -/

/-- `B` acts on `1 : B ⧸ (τ^q)` by reduction. -/
@[simp] theorem smul_one_quo (b : B) :
    b • (1 : Quo B τ q) = Ideal.Quotient.mk (Ideal.span {τ ^ q}) b := by
  have h : (1 : Quo B τ q) = Ideal.Quotient.mk (Ideal.span {τ ^ q}) 1 := rfl
  rw [h, Jmod.quo_smul_mk, mul_one]

@[simp] theorem fst_algebraMap_mul_sElt (b : B) :
    (algebraMap B (Alg B τ q) b * sElt B τ q).fst = 0 := by simp

theorem σ_algebraMap_mul_sElt (b : B) :
    σ (algebraMap B (Alg B τ q) b * sElt B τ q)
      = Ideal.Quotient.mk (Ideal.span {τ ^ q}) b := by
  simp

theorem algebraMap_mul_sElt_eq_zero_iff (b : B) :
    algebraMap B (Alg B τ q) b * sElt B τ q = 0
      ↔ Ideal.Quotient.mk (Ideal.span {τ ^ q}) b = 0 := by
  constructor
  · intro h
    rw [← σ_algebraMap_mul_sElt (τ := τ) (q := q) b, h, σ_zero]
  · intro h
    refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [h]

theorem tElt_pow (n : ℕ) : tElt B τ q ^ n = algebraMap B (Alg B τ q) (τ ^ n) := by
  rw [tElt_def, ← map_pow]

theorem tElt_pow_mul_sElt_eq_zero_iff (n : ℕ) :
    tElt B τ q ^ n * sElt B τ q = 0
      ↔ Ideal.Quotient.mk (Ideal.span {τ ^ q}) (τ ^ n) = 0 := by
  rw [tElt_pow, algebraMap_mul_sElt_eq_zero_iff]

/-! ### B3 (guardrails) — the model is non-degenerate -/

theorem one_ne_zero_Alg [Nontrivial B] : (1 : Alg B τ q) ≠ 0 := fun h =>
  one_ne_zero (α := B) (congrArg (fun x : Alg B τ q => x.fst) h)

theorem u₁_ne_zero [Nontrivial B] : u₁ B τ q ≠ 0 := fun h =>
  one_ne_zero (α := B) (congrArg γ₁ h)

theorem u₂_ne_zero [Nontrivial B] : u₂ B τ q ≠ 0 := fun h =>
  one_ne_zero (α := B) (congrArg γ₂ h)

theorem sElt_ne_zero
    (h : (Ideal.Quotient.mk (Ideal.span {τ ^ q}) 1 : Quo B τ q) ≠ 0) :
    sElt B τ q ≠ 0 := fun hs => by
  refine h ?_
  rw [← σ_sElt (B := B) (τ := τ) (q := q), hs, σ_zero]

/-! ## B5 — the ideals `J` and `W` on coordinates -/

theorem mem_Jid_iff {x : Alg B τ q} : x ∈ Jid B τ q ↔ x.fst = 0 := by
  rw [Jid, RingHom.mem_ker]
  rfl

theorem e₁_mem_Jid : e₁ B τ q ∈ Jid B τ q := mem_Jid_iff.2 rfl
theorem e₂_mem_Jid : e₂ B τ q ∈ Jid B τ q := mem_Jid_iff.2 rfl
theorem e₃_mem_Jid : e₃ B τ q ∈ Jid B τ q := mem_Jid_iff.2 rfl

theorem mem_Wid_iff {w : Alg B τ q} :
    w ∈ Wid B τ q ↔ w.fst = 0 ∧ α₁ w = 0 ∧ α₂ w = 0 ∧ α₃ w = 0 := by
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
    | zero => exact ⟨rfl, rfl, rfl, rfl⟩
    | add x y _ _ ihx ihy =>
        exact ⟨by simp [ihx.1, ihy.1], by simp [ihx.2.1, ihy.2.1],
          by simp [ihx.2.2.1, ihy.2.2.1], by simp [ihx.2.2.2, ihy.2.2.2]⟩
    | smul a x _ ih =>
        rw [smul_eq_mul]
        exact ⟨by simp [ih.1], by simp [ih.1, ih.2.1], by simp [ih.1, ih.2.2.1],
          by simp [ih.1, ih.2.2.2]⟩
  · rintro ⟨h0, h1, h2, h3⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {τ ^ q}) (σ w)
    have hw : w = algebraMap B (Alg B τ q) (γ₁ w) * u₁ B τ q
        + algebraMap B (Alg B τ q) (γ₂ w) * u₂ B τ q
        + algebraMap B (Alg B τ q) c * sElt B τ q := by
      refine ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [h0, h1, h2, h3, ← hc]
    rw [hw]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem u₁_mem_Wid : u₁ B τ q ∈ Wid B τ q := Ideal.subset_span (by simp)
theorem u₂_mem_Wid : u₂ B τ q ∈ Wid B τ q := Ideal.subset_span (by simp)
theorem sElt_mem_Wid : sElt B τ q ∈ Wid B τ q := Ideal.subset_span (by simp)

theorem Wid_le_Jid : Wid B τ q ≤ Jid B τ q := fun _ hw => mem_Jid_iff.2 (mem_Wid_iff.1 hw).1

/-- The product of two elements of `J` lies in `W`. -/
theorem mul_mem_Wid {x y : Alg B τ q} (hx : x ∈ Jid B τ q) (hy : y ∈ Jid B τ q) :
    x * y ∈ Wid B τ q := by
  rw [mem_Jid_iff] at hx hy
  exact mem_Wid_iff.2 ⟨by simp [hx, hy], by simp [hx, hy], by simp [hx, hy], by simp [hx, hy]⟩

/-- `W` annihilates `J`. -/
theorem Wid_mul_Jid {w z : Alg B τ q} (hw : w ∈ Wid B τ q) (hz : z ∈ Jid B τ q) :
    w * z = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := mem_Wid_iff.1 hw
  exact mul_eq_zero_of_coords h0 h1 h2 h3 (mem_Jid_iff.1 hz)

/-! ## B7 — `J² = W` -/

theorem Jid_sq_le_Wid : (Jid B τ q) ^ 2 ≤ Wid B τ q := by
  rw [pow_two]
  exact Ideal.mul_le.2 fun x hx y hy => mul_mem_Wid hx hy

theorem Wid_le_Jid_sq (h2 : (2 : B) = 0) : Wid B τ q ≤ (Jid B τ q) ^ 2 := by
  rw [Wid, Ideal.span_le, pow_two]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact e₃_mul_e₃ (B := B) (τ := τ) (q := q) ▸ Ideal.mul_mem_mul e₃_mem_Jid e₃_mem_Jid
  · exact e₂_mul_e₂ (B := B) (τ := τ) (q := q) ▸ Ideal.mul_mem_mul e₂_mem_Jid e₂_mem_Jid
  · exact e₁_mul_e₃_add_e₂_mul_e₂ (τ := τ) (q := q) h2 ▸
      Ideal.add_mem _ (Ideal.mul_mem_mul e₁_mem_Jid e₃_mem_Jid)
        (Ideal.mul_mem_mul e₂_mem_Jid e₂_mem_Jid)

/-- `J² = W` at the generic base, provided the base has characteristic 2. -/
theorem Jid_sq_eq_Wid_gen (h2 : (2 : B) = 0) : (Jid B τ q) ^ 2 = Wid B τ q :=
  le_antisymm Jid_sq_le_Wid (Wid_le_Jid_sq h2)

/-! ## B6 — `J³ = 0` -/

/-- `J³ = 0` at the generic base (no characteristic assumption needed). -/
theorem Jid_pow_three_eq_bot_gen : (Jid B τ q) ^ 3 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
  refine Ideal.mul_le.2 fun r hr s hs => ?_
  exact Ideal.mem_bot.2 (Wid_mul_Jid (Jid_sq_le_Wid hr) hs)

end Alg

/-! ## B3 (guardrails) at the counterexample base — `A q` does not collapse

Without these, `sElt q` could be `0` (or `Quo` could be the zero ring) and every
later theorem would be vacuously true. -/

open Polynomial in
/-- A polynomial of degree `< q` is nonzero mod `t^q`. -/
theorem mk_ne_zero_of_natDegree_lt {q : ℕ} {p : Dbase} (hp : p ≠ 0)
    (hlt : p.natDegree < q) :
    (Ideal.Quotient.mk (Ideal.span {tD ^ q}) p : Quo Dbase tD q) ≠ 0 := by
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  have hdeg := Polynomial.natDegree_le_of_dvd h hp
  rw [Polynomial.natDegree_X_pow] at hdeg
  omega

/-- Guardrail: `A q` is not the zero ring. -/
theorem one_ne_zero_A (q : ℕ) : (1 : A q) ≠ 0 := Alg.one_ne_zero_Alg

/-- Guardrail: `u₁ ≠ 0`. -/
theorem u₁_ne_zero (q : ℕ) : u₁ q ≠ 0 := Alg.u₁_ne_zero

/-- Guardrail: `u₂ ≠ 0`. -/
theorem u₂_ne_zero (q : ℕ) : u₂ q ≠ 0 := Alg.u₂_ne_zero

/-- Guardrail: `s ≠ 0`, i.e. `D/t^qD ≠ 0`. -/
theorem sElt_ne_zero {q : ℕ} (hq : 1 ≤ q) : sElt q ≠ 0 :=
  Alg.sElt_ne_zero (mk_ne_zero_of_natDegree_lt one_ne_zero (by
    rw [Polynomial.natDegree_one]; omega))

/-- Guardrail: `t^q · s = 0` — the `s`-line really is `t^q`-torsion. -/
theorem tElt_pow_mul_sElt (q : ℕ) : tElt q ^ q * sElt q = 0 :=
  (Alg.tElt_pow_mul_sElt_eq_zero_iff q).2
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 dvd_rfl))

/-- Guardrail: `t^(q-1) · s ≠ 0` — the `s`-line is *exactly* `t^q`-torsion, so the
irredundant product of Step 3 really has length `q + 1`. -/
theorem tElt_pow_pred_mul_sElt_ne_zero {q : ℕ} (hq : 1 ≤ q) :
    tElt q ^ (q - 1) * sElt q ≠ 0 := fun h => by
  refine mk_ne_zero_of_natDegree_lt (q := q) (p := tD ^ (q - 1))
    (pow_ne_zero _ Polynomial.X_ne_zero) ?_
    ((Alg.tElt_pow_mul_sElt_eq_zero_iff (B := Dbase) (τ := tD) (q := q) (q - 1)).1 h)
  rw [Polynomial.natDegree_X_pow]
  omega

/-! ## B8 — Noetherianity -/

/-- `Alg B τ q` is a finite `B`-module, hence Noetherian as a `B`-module. -/
theorem isNoetherian_Alg (B : Type) [CommRing B] [IsNoetherianRing B] (τ : B) (q : ℕ) :
    IsNoetherian B (Alg B τ q) := by
  haveI : IsNoetherian B B := isNoetherianRing_iff.1 inferInstance
  haveI : IsNoetherian B (Jmod B τ q) :=
    inferInstanceAs (IsNoetherian B (B × B × B × B × B × Quo B τ q))
  exact isNoetherian_of_linearEquiv (Unitization.linearEquiv B B (Jmod B τ q)).symm

theorem isNoetherianRing_Alg (B : Type) [CommRing B] [IsNoetherianRing B] (τ : B) (q : ℕ) :
    IsNoetherianRing (Alg B τ q) :=
  isNoetherianRing_iff.2 (isNoetherian_of_tower B (isNoetherian_Alg B τ q))

/-- **B8 (frozen statement).** `A_q` is Noetherian. -/
theorem isNoetherianRing_A_proof (q : ℕ) : IsNoetherianRing (A q) :=
  isNoetherianRing_Alg Dbase tD q

/-! ## B6/B7 at the counterexample base `B = Dbase`, `τ = tD` -/

/-- **B7 (frozen statement).** `J² = W = Du₁ + Du₂ + (D/t^q)s`. -/
theorem Jid_sq_eq_Wid_proof (q : ℕ) : (Jid Dbase tD q) ^ 2 = Wid Dbase tD q :=
  Alg.Jid_sq_eq_Wid_gen CharTwo.two_eq_zero

/-- **B6 (frozen statement).** `J³ = 0`. -/
theorem Jid_pow_three_eq_bot_proof (q : ℕ) : (Jid Dbase tD q) ^ 3 = ⊥ :=
  Alg.Jid_pow_three_eq_bot_gen

end Prob30c
