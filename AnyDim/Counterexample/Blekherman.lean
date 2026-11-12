module

public import AnyDim.Basic

/-!
# Theorem 3.2 (Blekherman) and Corollary 3.3

Source: Debus--Schabert, Section 3, Theorem 3.2 and Corollary 3.3.

* `theorem_3_2` is Blekherman's theorem on symmetric sums of squares on the hypercube
  `{0,1}^n`, see [Lee--Prakash--de Wolf--Yuen, *On the sum-of-squares degree of symmetric
  quadratic functions*, Theorem 2.3] (reference [19] of the paper), where it is attributed to
  Blekherman's unpublished manuscript *Symmetric sums of squares on the hypercube*.

  **This theorem is stated without proof: its proof is `sorry`.**  It is the only `sorry` of the
  project.  The paper also uses it as a black box.

* `corollary_3_3` is Corollary 3.3, deduced from `theorem_3_2` exactly as in the paper.  It
  therefore depends on the `sorry` (as `#print axioms corollary_3_3` shows).

An elementary, fully proved replacement for Corollary 3.3 under the stronger hypothesis
`2 deg Q + 4 ≤ n` is `AnyDim.Elementary.corollary_3_3_elementary`; it suffices for
Theorem 3.1 (2).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open Polynomial

/-- **Theorem 3.2** (Blekherman; [19, Theorem 2.3]).  Let `Q : {0,1}^n → ℝ_{≥0}` be a symmetric
nonnegative Boolean function and let `q ∈ ℝ[T]` be the unique polynomial of degree at most `n`
with `Q(x_1, …, x_n) = q(x_1 + ⋯ + x_n)` on `{0,1}^n`.  If `Q` coincides on `{0,1}^n` with a sum
of squares `∑_j g_j²` of `n`-variate polynomials of degree `d ≤ n/2`, then

  `q(T) = ∑_{k=0}^{d} σ_{d-k}(T) ∏_{i=0}^{k-1} (T - i)(n - T - i)`

with sums of squares `σ_k ∈ ℝ[T]` of degree `deg σ_k ≤ 2k`.

In the statement below, `Q` is the function `x ↦ ∑_j g_j(x)²`; the hypothesis `hQ` says that it
is of the form `q(∑ x_i)` on the cube (so it is symmetric and nonnegative), and `q` is determined
by `hq : deg q ≤ n` and `hQ`.

**Not proved here** (`sorry`): the proof uses the representation theory of the symmetric group
and is not part of the paper either. -/
theorem theorem_3_2 {n d : ℕ} (hd : 2 * d ≤ n) {r : ℕ} (g : Fin r → MvPolynomial (Fin n) ℝ)
    (hg : ∀ j, (g j).totalDegree ≤ d) (q : Polynomial ℝ) (hq : q.natDegree ≤ n)
    (hQ : ∀ x : Fin n → ℝ, (∀ i, x i = 0 ∨ x i = 1) →
      ∑ j, (MvPolynomial.eval x (g j)) ^ 2 = q.eval (∑ i, x i)) :
    ∃ σ : ℕ → Polynomial ℝ, (∀ k, IsSOS (σ k) ∧ (σ k).natDegree ≤ 2 * k) ∧
      q = ∑ k ∈ Finset.range (d + 1), σ (d - k) *
        ∏ i ∈ Finset.range k, ((X - C (i : ℝ)) * (C (n : ℝ) - X - C (i : ℝ))) := by
  sorry

/-! ### Auxiliary facts for Corollary 3.3 -/

/-- A univariate sum of squares is nonnegative on `ℝ`. -/
theorem isSOS_polynomial_eval_nonneg {s : Polynomial ℝ} (hs : IsSOS s) (t : ℝ) :
    0 ≤ s.eval t := by
  obtain ⟨r, u, rfl⟩ := hs
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_nonneg fun j _ => by rw [Polynomial.eval_pow]; exact sq_nonneg _

/-- Substituting polynomials of degree at most `1` does not raise the total degree. -/
theorem totalDegree_aeval_le_of_le_one {σ τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (a : MvPolynomial σ ℝ) :
    (MvPolynomial.aeval f a).totalDegree ≤ a.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le fun e he => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans
    (le_trans ?_ (MvPolynomial.le_totalDegree he))
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc e i * (f i).totalDegree ≤ e i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = e i := mul_one _

/-- The affine substitution `X_i ↦ 2 X_i - 1`, which maps `{0,1}^n` onto `{-1,1}^n`. -/
def cubeShift (n : ℕ) : Poly n →ₐ[ℝ] Poly n :=
  MvPolynomial.aeval fun i : Fin n => (2 * MvPolynomial.X i - 1 : Poly n)

theorem eval_cubeShift {n : ℕ} (x : Fin n → ℝ) (a : Poly n) :
    MvPolynomial.eval x (cubeShift n a) = MvPolynomial.eval (fun i => 2 * x i - 1) a := by
  have h : (MvPolynomial.aeval x).comp (cubeShift n) =
      MvPolynomial.aeval (fun i => 2 * x i - 1) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [cubeShift]
  exact congrArg (fun φ : Poly n →ₐ[ℝ] ℝ => φ a) h

theorem totalDegree_cubeShift_le {n : ℕ} (a : Poly n) :
    (cubeShift n a).totalDegree ≤ a.totalDegree := by
  refine totalDegree_aeval_le_of_le_one _ (fun i => ?_) a
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [← map_ofNat (MvPolynomial.C : ℝ →+* Poly n) 2, MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_one]
    exact Nat.zero_le _

/-- **Corollary 3.3.**  Let `Q ∈ ℝ[X_1, …, X_n]` be a sum of squares with `deg Q ≤ n`, and let
`q ∈ ℝ[T]` satisfy `deg q ≤ n` and `Q(x) = q(∑ x_i)` for all `x ∈ {-1,1}^n`.  Then
`q(1/2) ≥ 0`.

The proof applies Theorem 3.2 to `Q(2x_1 - 1, …, 2x_n - 1)` and `q̃ = q(2T - n)` with
`d = ⌊n/2⌋` and evaluates at `T = n/2 + 1/4`; it depends on the unproved `theorem_3_2`. -/
theorem corollary_3_3 {n : ℕ} {Q : Poly n} (hQ : IsSOS Q) (hdeg : Q.totalDegree ≤ n)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ n)
    (h : ∀ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) → evalAt Q x = q.eval (∑ i, x i)) :
    0 ≤ q.eval (1 / 2) := by
  set d := n / 2 with hd
  have h2d : 2 * d ≤ n := by omega
  -- `Q = ∑ g_j²` with `deg g_j ≤ ⌊n/2⌋`
  obtain ⟨r, g, hQg, hg⟩ := sos_degree_bound' (d := d) hQ (by omega)
  -- the shifted data `Q̃ = Q(2x - 1)` and `q̃ = q(2T - n)`
  set qt : Polynomial ℝ := q.comp (2 * X - C (n : ℝ)) with hqt
  have hlin : (2 * X - C (n : ℝ) : Polynomial ℝ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [← Polynomial.C_ofNat]
      exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    · rw [Polynomial.natDegree_C]
      exact Nat.zero_le _
  have hqtdeg : qt.natDegree ≤ n := by
    refine Polynomial.natDegree_comp_le.trans (le_trans ?_ hq)
    calc q.natDegree * (2 * X - C (n : ℝ) : Polynomial ℝ).natDegree ≤ q.natDegree * 1 :=
          Nat.mul_le_mul_left _ hlin
      _ = q.natDegree := mul_one _
  have hcube : ∀ x : Fin n → ℝ, (∀ i, x i = 0 ∨ x i = 1) →
      ∑ j, (MvPolynomial.eval x (cubeShift n (g j))) ^ 2 = qt.eval (∑ i, x i) := by
    intro x hx
    have hx' : ∀ i, 2 * x i - 1 = 1 ∨ 2 * x i - 1 = -1 := by
      intro i
      rcases hx i with h0 | h1
      · right; rw [h0]; norm_num
      · left; rw [h1]; norm_num
    have hQx := h (fun i => 2 * x i - 1) hx'
    simp only [eval_cubeShift]
    rw [hqt, Polynomial.eval_comp]
    have hsum : ∑ i, (2 * x i - 1) = (2 * X - C (n : ℝ) : Polynomial ℝ).eval (∑ i, x i) := by
      simp [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [← hsum, ← hQx, evalAt, hQg]
    simp only [map_sum, map_pow]
  obtain ⟨σ, hσ, hrep⟩ := theorem_3_2 h2d (fun j => cubeShift n (g j))
    (fun j => (totalDegree_cubeShift_le (g j)).trans (hg j)) qt hqtdeg hcube
  -- evaluate at `T = n/2 + 1/4`
  have hval : q.eval (1 / 2) = qt.eval ((n : ℝ) / 2 + 1 / 4) := by
    rw [hqt, Polynomial.eval_comp]
    congr 1
    simp
    ring
  rw [hval, hrep, Polynomial.eval_finsetSum]
  refine Finset.sum_nonneg fun k hk => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  refine mul_nonneg (isSOS_polynomial_eval_nonneg (hσ (d - k)).1 _)
    (Finset.prod_nonneg fun i hi => ?_)
  have hik : i < k := Finset.mem_range.mp hi
  have hkd : k < d + 1 := Finset.mem_range.mp hk
  have hi1 : ((i : ℝ) + 1) ≤ (d : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ d)
  have hdn : 2 * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2d
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact mul_nonneg (by linarith) (by linarith)

end AnyDim

end
