module

public import AnyDim.Basic

/-!
# Symmetric functions with rational coefficients

Source: Debus--Schabert, Sections 1 and 2.

The undecidability result concerns symmetric functions `f ∈ Λ_ℚ = ℚ[p_1, p_2, …]`
(`Λℚ := MvPolynomial ℕ+ ℚ`, defined in `AnyDim.Basic`).  This file provides the evaluation of
rational symmetric functions at real tuples and the degree notions over `ℚ`:

* `evalTruncℚ h x` is the real number `h^{(n)}(x)` for `h ∈ Λ_ℚ` and `x : Fin n → ℝ`
  (`evalHom x : Λℚ →ₐ[ℚ] ℝ` sends `p_k` to `∑_i x_i^k`).
* `AnyDimPSDℚ h`, `AnyDimPDℚ h`: `h` is any-dimensional psd / positive definite.
* `WHomogeneousℚ h D`, `WDegLEℚ h D`: homogeneity and degree bounds for the grading
  `deg p_k = k`; `IsEvenℚ h`: `h ∈ ℚ[p_2, p_4, p_6, …]`.

The bridge to the notions for real symmetric functions of `AnyDim.Basic` (via the inclusion
`toΛ : Λℚ →+* Λ`) is `evalTruncℚ_eq_evalTrunc`, `anyDimPSDℚ_iff`, `anyDimPDℚ_iff`,
`wHomogeneousℚ_iff`, `vars_toΛ`.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace AnyDim.Undecidability

/-- The power sum `p_k ∈ Λ_ℚ`. -/
def p (k : PNat) : Λℚ := MvPolynomial.X k

/-- The evaluation `h ↦ h^{(n)}(x)` as an algebra homomorphism `Λℚ →ₐ[ℚ] ℝ`:
`p_k` is sent to `∑_i x_i^k`. -/
def evalHom {n : ℕ} (x : Fin n → ℝ) : Λℚ →ₐ[ℚ] ℝ :=
  MvPolynomial.aeval (fun k : PNat => tuplePower x (k : ℕ))

/-- The value `h^{(n)}(x)` of the truncation of `h ∈ Λ_ℚ` at the real tuple `x`. -/
def evalTruncℚ {n : ℕ} (h : Λℚ) (x : Fin n → ℝ) : ℝ :=
  evalHom x h

/-- `h ∈ Λ_ℚ` is any-dimensional psd: `h^{(n)}(x) ≥ 0` for every `n` and every real tuple `x`. -/
def AnyDimPSDℚ (h : Λℚ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), 0 ≤ evalTruncℚ h x

/-- `h ∈ Λ_ℚ` is any-dimensional positive definite: `h^{(n)}(x) > 0` at every nonzero finite
real tuple. -/
def AnyDimPDℚ (h : Λℚ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 → 0 < evalTruncℚ h x

/-- `h` is homogeneous of degree `D` in the original coordinates
(NOT `h.totalDegree`, which counts every `p_k` with degree one). -/
def WHomogeneousℚ (h : Λℚ) (D : ℕ) : Prop :=
  MvPolynomial.IsWeightedHomogeneous wt h D

/-- Degree at most `D` in the original coordinates. -/
def WDegLEℚ (h : Λℚ) (D : ℕ) : Prop :=
  MvPolynomial.weightedTotalDegree wt h ≤ D

/-- `h ∈ ℚ[p_2, p_4, p_6, …]`: only even power sums occur in `h`. -/
def IsEvenℚ (h : Λℚ) : Prop :=
  ∀ k ∈ h.vars, Even (k : ℕ)

/-! ### Elementary facts -/

theorem tuplePower_eq_sum {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    tuplePower x k = ∑ i : Fin n, x i ^ k := rfl

/-- Power sums are invariant under permutations of the coordinates (symmetry of `h^{(n)}`). -/
theorem tuplePower_comp_perm {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    tuplePower (x ∘ σ) k = tuplePower x k := by
  unfold tuplePower
  exact Equiv.sum_comp σ (fun i => x i ^ k)

/-- `h^{(n)}` is a symmetric polynomial function. -/
theorem evalTruncℚ_comp_perm {n : ℕ} (h : Λℚ) (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    evalTruncℚ h (x ∘ σ) = evalTruncℚ h x := by
  unfold evalTruncℚ evalHom
  simp only [tuplePower_comp_perm]

theorem evalTruncℚ_p {n : ℕ} (x : Fin n → ℝ) (k : PNat) :
    evalTruncℚ (p k) x = tuplePower x (k : ℕ) := by
  simp [evalTruncℚ, evalHom, p]

theorem evalTruncℚ_C {n : ℕ} (x : Fin n → ℝ) (c : ℚ) :
    evalTruncℚ (MvPolynomial.C c) x = (c : ℝ) := by
  simp [evalTruncℚ, evalHom]

/-! ### `h ↦ evalTruncℚ h x` is a ring homomorphism -/

section Hom

variable {n : ℕ} (x : Fin n → ℝ)

theorem evalTruncℚ_add (h₁ h₂ : Λℚ) :
    evalTruncℚ (h₁ + h₂) x = evalTruncℚ h₁ x + evalTruncℚ h₂ x :=
  (evalHom x).map_add h₁ h₂

theorem evalTruncℚ_sub (h₁ h₂ : Λℚ) :
    evalTruncℚ (h₁ - h₂) x = evalTruncℚ h₁ x - evalTruncℚ h₂ x :=
  (evalHom x).map_sub h₁ h₂

theorem evalTruncℚ_mul (h₁ h₂ : Λℚ) :
    evalTruncℚ (h₁ * h₂) x = evalTruncℚ h₁ x * evalTruncℚ h₂ x :=
  (evalHom x).map_mul h₁ h₂

theorem evalTruncℚ_pow (h : Λℚ) (e : ℕ) : evalTruncℚ (h ^ e) x = evalTruncℚ h x ^ e :=
  (evalHom x).map_pow h e

theorem evalTruncℚ_sum {ι : Type*} (s : Finset ι) (f : ι → Λℚ) :
    evalTruncℚ (∑ i ∈ s, f i) x = ∑ i ∈ s, evalTruncℚ (f i) x :=
  map_sum (evalHom x) f s

theorem evalTruncℚ_one : evalTruncℚ (1 : Λℚ) x = 1 :=
  (evalHom x).map_one

theorem evalTruncℚ_zero : evalTruncℚ (0 : Λℚ) x = 0 :=
  (evalHom x).map_zero

theorem evalTruncℚ_ofNat (m : ℕ) [m.AtLeastTwo] :
    evalTruncℚ (OfNat.ofNat m : Λℚ) x = OfNat.ofNat m :=
  map_ofNat (evalHom x) m

/-- Evaluating an integer polynomial substituted by elements of `Λℚ`. -/
theorem evalTruncℚ_aeval {σ : Type*} (P : MvPolynomial σ ℤ) (g : σ → Λℚ) :
    evalTruncℚ (MvPolynomial.aeval g P) x =
      MvPolynomial.aeval (fun i => evalTruncℚ (g i) x) P :=
  MvPolynomial.comp_aeval_apply g ((evalHom x).restrictScalars ℤ) P

end Hom

/-- A homogeneous function of positive degree vanishes at the zero tuple. -/
theorem evalTruncℚ_zero_of_wHomogeneous {n : ℕ} {h : Λℚ} {D : ℕ} (hh : WHomogeneousℚ h D)
    (hD : 0 < D) : evalTruncℚ h (0 : Fin n → ℝ) = 0 := by
  have hf : (fun k : PNat => tuplePower (0 : Fin n → ℝ) (k : ℕ)) = fun _ => 0 := by
    funext k
    exact tuplePower_zero_left k.pos
  unfold evalTruncℚ evalHom
  rw [hf, MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq,
    hh.coeff_eq_zero 0 (by simp [hD.ne]), map_zero]

/-- An even function is invariant under `x ↦ -x`. -/
theorem evalTruncℚ_neg_of_isEven {n : ℕ} {h : Λℚ} (hh : IsEvenℚ h) (x : Fin n → ℝ) :
    evalTruncℚ h (-x) = evalTruncℚ h x := by
  unfold evalTruncℚ evalHom
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.aeval_eq_eval₂Hom]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun k hk _ => ?_) rfl
  unfold tuplePower
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply, (hh k hk).neg_pow]

theorem tuplePower_nonneg_of_even {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (hk : Even k) :
    0 ≤ tuplePower x k :=
  Finset.sum_nonneg fun i _ => hk.pow_nonneg (x i)

/-- A nonzero tuple has a nonzero coordinate. -/
theorem exists_ne_zero_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact ⟨i, hi⟩

/-- `p_k(x) > 0` for a nonzero tuple and even `k ≥ 2`. -/
theorem tuplePower_pos_of_even {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) {k : ℕ} (hk : Even k)
    (hk0 : k ≠ 0) : 0 < tuplePower x k := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hx
  refine Finset.sum_pos' (fun j _ => hk.pow_nonneg (x j)) ⟨i, Finset.mem_univ i, ?_⟩
  exact (hk.pow_pos_iff hk0).mpr hi

/-- `p_2(x) > 0` for a nonzero tuple. -/
theorem tuplePower_two_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < tuplePower x 2 :=
  tuplePower_pos_of_even hx even_two two_ne_zero

/-- `p_4(x) > 0` for a nonzero tuple. -/
theorem tuplePower_four_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < tuplePower x 4 :=
  tuplePower_pos_of_even hx ⟨2, rfl⟩ (by norm_num)

/-- A nonnegative, nonzero tuple has positive sum `p_1(z) > 0`. -/
theorem tuplePower_one_pos_of_nonneg {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) (hz0 : z ≠ 0) :
    0 < tuplePower z 1 := by
  obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hz0
  refine Finset.sum_pos' (fun j _ => by simpa using hz j) ⟨i, Finset.mem_univ i, ?_⟩
  simpa using lt_of_le_of_ne (hz i) (Ne.symm hi)

/-! ### Bridge to real symmetric functions -/

theorem toΛ_p (k : PNat) : toΛ (p k) = AnyDim.p k := by
  simp [toΛ, p, AnyDim.p]

/-- The value of `h ∈ Λ_ℚ` at a real tuple is the value of its image in `Λ`. -/
theorem evalTruncℚ_eq_evalTrunc {n : ℕ} (h : Λℚ) (x : Fin n → ℝ) :
    evalTruncℚ h x = evalTrunc (toΛ h) x := by
  rw [evalTrunc_eq_aeval, evalTruncℚ, evalHom, toΛ, MvPolynomial.aeval_map_algebraMap]

theorem anyDimPSDℚ_iff (h : Λℚ) : AnyDimPSDℚ h ↔ AnyDimPSD (toΛ h) := by
  simp only [AnyDimPSDℚ, AnyDimPSD, evalTruncℚ_eq_evalTrunc]

theorem anyDimPDℚ_iff (h : Λℚ) : AnyDimPDℚ h ↔ AnyDimPD (toΛ h) := by
  simp only [AnyDimPDℚ, AnyDimPD, evalTruncℚ_eq_evalTrunc]

theorem toΛ_injective : Function.Injective toΛ :=
  MvPolynomial.map_injective _ (algebraMap ℚ ℝ).injective

theorem support_toΛ (h : Λℚ) : (toΛ h).support = h.support :=
  MvPolynomial.support_map_of_injective h (algebraMap ℚ ℝ).injective

theorem vars_toΛ (h : Λℚ) : (toΛ h).vars = h.vars :=
  MvPolynomial.vars_map_of_injective h (algebraMap ℚ ℝ).injective

/-- Homogeneity of `h ∈ Λ_ℚ` agrees with homogeneity of its image in `Λ`. -/
theorem wHomogeneousℚ_iff (h : Λℚ) (D : ℕ) : WHomogeneousℚ h D ↔ WHomogeneous (toΛ h) D := by
  unfold WHomogeneousℚ WHomogeneous
  rw [support_toΛ]
  constructor
  · intro hh e he
    rw [monomialWeight_eq_weight]
    exact hh (MvPolynomial.mem_support_iff.1 he)
  · intro hh e he
    rw [← monomialWeight_eq_weight]
    exact hh e (MvPolynomial.mem_support_iff.2 he)

end AnyDim.Undecidability

end
