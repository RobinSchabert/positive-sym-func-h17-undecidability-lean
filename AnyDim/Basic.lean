module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
# Symmetric functions and their truncations

Source: S. Debus and R. Schabert, *Hilbert's 17th problem for symmetric functions:
undecidability and a counterexample*, Section 1 (Notation).

* `Λ := MvPolynomial ℕ+ ℝ` is the ring of symmetric functions `ℝ[p_1, p_2, …]`.  The variable
  `X k` is the ABSTRACT power sum `p_k`, not a coordinate.  `ℕ+` starts at `1`, so there is no
  stray generator `p_0`.  `Λℚ := MvPolynomial ℕ+ ℚ` is the ring `Λ_ℚ` of symmetric functions with
  rational coefficients, and `toΛ : Λℚ →+* Λ` is the inclusion.
* `trunc n : Λ →ₐ[ℝ] Poly n` is the truncation `f ↦ f^{(n)}`: it sends `p_k` to
  `X_1^k + ⋯ + X_n^k`.  `evalTrunc f x` is the real number `f^{(n)}(x)`.
* `IsSOS` is "finite sum of squares" in any commutative ring.
* `AnyDimPSD f`, `AnyDimPD f`, `AnyDimSOS f` are the properties *any-dimensional psd*,
  *any-dimensional positive definite* and *any-dimensional sos* (the cones `SP` and `SΣ`).
  As in the paper, `n` ranges over `ℕ = {1, 2, …}`; for `AnyDimPSD` and `AnyDimPD` the case
  `n = 0` is vacuous or follows from `n = 1`, so the definitions quantify over all `n`
  (`anyDimPSD_iff`, `anyDimPD_iff`).
* `monomialWeight`, `WDegLE`, `WHomogeneous`, `wDegree` describe the grading `deg p_k = k`, i.e.
  the degree in the original coordinates (NOT `MvPolynomial.totalDegree` in `Λ`).

The Mathlib imports of the whole project are collected in this file.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

/-- The ring of symmetric functions `Λ = ℝ[p_1, p_2, …]`. -/
abbrev Λ := MvPolynomial PNat Real

/-- The ring `Λ_ℚ = ℚ[p_1, p_2, …]` of symmetric functions with rational coefficients. -/
abbrev Λℚ := MvPolynomial PNat ℚ

/-- The inclusion `Λ_ℚ ⊆ Λ`. -/
def toΛ : Λℚ →+* Λ := MvPolynomial.map (algebraMap ℚ ℝ)

/-- Real polynomials in `n` variables. -/
abbrev Poly (n : Nat) := MvPolynomial (Fin n) Real

/-- The power sum `p_k ∈ Λ`. -/
def p (k : PNat) : Λ := MvPolynomial.X k

/-- The power sum `X_1^k + ⋯ + X_n^k` in `n` variables. -/
def powerSum (n k : Nat) : Poly n :=
  Finset.univ.sum (fun i : Fin n => (MvPolynomial.X i) ^ k)

/-- The power sum `x_1^k + ⋯ + x_n^k` of a real tuple. -/
def tuplePower {n : Nat} (x : Fin n → Real) (k : Nat) : Real :=
  Finset.univ.sum (fun i : Fin n => x i ^ k)

/-- The truncation `f ↦ f^{(n)}` to `n` variables, an algebra homomorphism. -/
def trunc (n : Nat) : AlgHom Real Λ (Poly n) :=
  MvPolynomial.aeval (fun k : PNat => powerSum n (k : Nat))

/-- Evaluation of a polynomial at a real tuple. -/
def evalAt {n : Nat} (q : Poly n) (x : Fin n → Real) : Real :=
  MvPolynomial.eval x q

/-- The value `f^{(n)}(x)` of the truncation of `f` at the real tuple `x`. -/
def evalTrunc {n : Nat} (f : Λ) (x : Fin n → Real) : Real :=
  evalAt (trunc n f) x

/-- Finite sum of squares. No uniform number of squares is imposed. -/
def IsSOS {R : Type*} [CommRing R] (h : R) : Prop :=
  ∃ (r : Nat) (q : Fin r → R), h = Finset.univ.sum (fun j => q j ^ 2)

/-- `f` is *any-dimensional sos* (`f ∈ SΣ`): every truncation `f^{(n)}`, `n ≥ 1`, is a sum of
squares of polynomials. -/
def AnyDimSOS (f : Λ) : Prop :=
  ∀ n : Nat, 0 < n → IsSOS (trunc n f)

/-- `f` is *any-dimensional psd* (`f ∈ SP`): `f^{(n)} ≥ 0` on `ℝ^n` for every `n`. -/
def AnyDimPSD (f : Λ) : Prop :=
  ∀ (n : Nat) (x : Fin n → Real), 0 ≤ evalTrunc f x

/-- `f` is *any-dimensional positive definite*: `f^{(n)}(x) > 0` for every nonzero real tuple. -/
def AnyDimPD (f : Λ) : Prop :=
  ∀ (n : Nat) (x : Fin n → Real), x ≠ 0 → 0 < evalTrunc f x

/-- The degree of a monomial `p_{r_1} ⋯ p_{r_s}` in the original coordinates, `r_1 + ⋯ + r_s`
(NOT its total degree in `Λ`). -/
def monomialWeight (e : PNat →₀ Nat) : Nat :=
  e.sum (fun k a => (k : Nat) * a)

/-- `f` has degree at most `D` (in the original coordinates). -/
def WDegLE (h : Λ) (D : Nat) : Prop :=
  ∀ e ∈ h.support, monomialWeight e ≤ D

/-- `f` is homogeneous of degree `D`: a linear combination of products `p_{r_1} ⋯ p_{r_s}` with
`r_1 + ⋯ + r_s = D`. -/
def WHomogeneous (h : Λ) (D : Nat) : Prop :=
  ∀ e ∈ h.support, monomialWeight e = D

/-- The degree of `f` in the original coordinates. -/
def wDegree (h : Λ) : Nat := h.support.sup monomialWeight

/-- `f ∈ ℝ[p_1, …, p_s]`. -/
def UsesFirst (s : Nat) (h : Λ) : Prop :=
  ∀ k ∈ h.vars, (k : Nat) ≤ s

/-- The largest index of a power sum occurring in `f`. -/
def variableBound (h : Λ) : Nat := h.vars.sup (fun k : PNat => (k : Nat))

theorem wdeg_mono {h : Λ} {D E : Nat} (hh : WDegLE h D) (hDE : D ≤ E) :
    WDegLE h E := by
  intro e he
  exact le_trans (hh e he) hDE

theorem usesFirst_mono {h : Λ} {s m : Nat} (hh : UsesFirst s h) (hsm : s ≤ m) :
    UsesFirst m h := by
  intro k hk
  exact le_trans (hh k hk) hsm

theorem wdeg_self (h : Λ) : WDegLE h (wDegree h) :=
  fun _ he => Finset.le_sup he

theorem usesFirst_self (h : Λ) : UsesFirst (variableBound h) h :=
  fun _ hk => Finset.le_sup (f := fun k : PNat => (k : Nat)) hk

theorem WHomogeneous.wDegLE {h : Λ} {D : Nat} (hh : WHomogeneous h D) : WDegLE h D :=
  fun e he => (hh e he).le

theorem isSOS_map {R S : Type*} [CommRing R] [CommRing S]
    (phi : RingHom R S) {h : R} (hh : IsSOS h) : IsSOS (phi h) := by
  rcases hh with ⟨r, q, hq⟩
  refine ⟨r, (fun i => phi (q i)), ?_⟩
  rw [hq]
  simp only [map_sum, map_pow]

theorem isSOS_eval_nonneg {n : Nat} {h : Poly n} (hh : IsSOS h)
    (x : Fin n → Real) : 0 ≤ evalAt h x := by
  rcases hh with ⟨r, q, hq⟩
  unfold evalAt
  rw [hq]
  simp only [map_sum, map_pow]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (MvPolynomial.eval x (q i)))

theorem eval_powerSum {n : Nat} (x : Fin n → Real) (k : Nat) :
    evalAt (powerSum n k) x = tuplePower x k := by
  simp [evalAt, powerSum, tuplePower]

theorem trunc_p (n : Nat) (k : PNat) : trunc n (p k) = powerSum n k :=
  MvPolynomial.aeval_X _ k

theorem evalTrunc_p {n : Nat} (x : Fin n → Real) (k : PNat) :
    evalTrunc (p k) x = tuplePower x (k : Nat) := by
  rw [evalTrunc, trunc_p, eval_powerSum]

/-- `f ↦ f^{(n)}(x)` as an algebra homomorphism `Λ →ₐ[ℝ] ℝ`. -/
def evalTruncHom {n : Nat} (x : Fin n → Real) : Λ →ₐ[Real] Real :=
  (MvPolynomial.aeval x).comp (trunc n)

theorem evalTruncHom_apply {n : Nat} (x : Fin n → Real) (f : Λ) :
    evalTruncHom x f = evalTrunc f x :=
  rfl

/-- `f^{(n)}(x)` is obtained by substituting `p_k ↦ x_1^k + ⋯ + x_n^k`. -/
theorem evalTrunc_eq_aeval {n : Nat} (f : Λ) (x : Fin n → Real) :
    evalTrunc f x = MvPolynomial.aeval (fun k : PNat => tuplePower x (k : Nat)) f := by
  rw [← evalTruncHom_apply]
  have h : evalTruncHom x = MvPolynomial.aeval (fun k : PNat => tuplePower x (k : Nat)) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [evalTruncHom_apply, MvPolynomial.aeval_X]
    exact evalTrunc_p x k
  rw [h]

theorem tuplePower_zero_left {n : Nat} {k : Nat} (hk : 0 < k) :
    tuplePower (0 : Fin n → Real) k = 0 := by
  simp [tuplePower, zero_pow hk.ne']

/-- The value of `f^{(0)}` (the constant term of `f`) is the value of `f^{(1)}` at `0`. -/
theorem evalTrunc_fin_zero (f : Λ) (x : Fin 0 → Real) :
    evalTrunc f x = evalTrunc f (0 : Fin 1 → Real) := by
  have hg : (fun k : PNat => tuplePower x (k : Nat)) =
      fun k : PNat => tuplePower (0 : Fin 1 → Real) (k : Nat) := by
    funext k
    rw [tuplePower_zero_left k.pos]
    simp [tuplePower]
  rw [evalTrunc_eq_aeval, evalTrunc_eq_aeval, hg]

/-- `f` is any-dimensional psd iff `f^{(n)} ≥ 0` on `ℝ^n` for every `n ∈ ℕ = {1, 2, …}`
(the paper's convention): the case `n = 0` follows from `n = 1`. -/
theorem anyDimPSD_iff (f : Λ) :
    AnyDimPSD f ↔ ∀ n : Nat, 0 < n → ∀ x : Fin n → Real, 0 ≤ evalTrunc f x := by
  refine ⟨fun h n _ x => h n x, fun h n x => ?_⟩
  cases n with
  | zero =>
    rw [evalTrunc_fin_zero]
    exact h 1 Nat.one_pos 0
  | succ n => exact h (n + 1) n.succ_pos x

/-- `f` is any-dimensional positive definite iff `f^{(n)}(x) > 0` for every `n ∈ ℕ = {1, 2, …}`
and every nonzero `x ∈ ℝ^n` (for `n = 0` there is no nonzero tuple). -/
theorem anyDimPD_iff (f : Λ) :
    AnyDimPD f ↔ ∀ n : Nat, 0 < n → ∀ x : Fin n → Real, x ≠ 0 → 0 < evalTrunc f x := by
  refine ⟨fun h n _ x hx => h n x hx, fun h n x hx => ?_⟩
  cases n with
  | zero => exact absurd (Subsingleton.elim x 0) hx
  | succ n => exact h (n + 1) n.succ_pos x hx

section SumOfSquares

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Removing the top homogeneous component strictly lowers the total degree. -/
theorem totalDegree_sub_homogeneousComponent_lt {φ : MvPolynomial σ R} {e : ℕ}
    (he : φ.totalDegree ≤ e) (he0 : 0 < e) :
    (φ - homogeneousComponent e φ).totalDegree < e := by
  rw [totalDegree, Finset.sup_lt_iff he0]
  intro d hd
  rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hd
  split_ifs at hd with hde
  · simp at hd
  · have hle : d.degree ≤ φ.totalDegree := le_totalDegree (by simpa using hd)
    exact lt_of_le_of_ne (hle.trans he) hde

/-- The top homogeneous component of a square is the square of the top component. -/
theorem homogeneousComponent_two_mul_sq {φ : MvPolynomial σ R} {e : ℕ}
    (he : φ.totalDegree ≤ e) (he0 : 0 < e) :
    homogeneousComponent (2 * e) (φ ^ 2) = homogeneousComponent e φ ^ 2 := by
  set t := homogeneousComponent e φ
  set r := φ - t with hr
  have ht : t.IsHomogeneous e := homogeneousComponent_isHomogeneous e φ
  have hrdeg : r.totalDegree < e := totalDegree_sub_homogeneousComponent_lt he he0
  have htr : (t * r).totalDegree < 2 * e :=
    (totalDegree_mul t r).trans_lt (by have := ht.totalDegree_le; omega)
  have hrr : (r * r).totalDegree < 2 * e :=
    (totalDegree_mul r r).trans_lt (by omega)
  have hsplit : φ ^ 2 = t ^ 2 + (t * r + t * r + r * r) := by
    rw [show φ = t + r by rw [hr]; ring]; ring
  have hrest : (t * r + t * r + r * r).totalDegree < 2 * e :=
    (totalDegree_add _ _).trans_lt <| max_lt
      ((totalDegree_add _ _).trans_lt (max_lt htr htr)) hrr
  rw [hsplit, map_add, homogeneousComponent_eq_zero _ _ hrest, add_zero,
    homogeneousComponent_of_mem (ht.pow 2), ite_eq_left (mul_comm _ _)]

/-- Over `ℝ` there is no cancellation of top-degree terms in a sum of squares: if
`∑ i, q i ^ 2` has total degree at most `2 * d + 1`, then every `q i` has degree at most `d`. -/
theorem totalDegree_le_of_sum_sq' {σ ι : Type*} [Fintype ι] {q : ι → MvPolynomial σ ℝ} {d : ℕ}
    (hdeg : (∑ i, q i ^ 2).totalDegree ≤ 2 * d + 1) (i : ι) : (q i).totalDegree ≤ d := by
  by_contra! hi
  set e := Finset.univ.sup fun j => (q j).totalDegree
  have hqe : ∀ j, (q j).totalDegree ≤ e := fun j =>
    Finset.le_sup (f := fun j => (q j).totalDegree) (Finset.mem_univ j)
  have hde : d < e := hi.trans_le (hqe i)
  have he0 : 0 < e := (Nat.zero_le d).trans_lt hde
  have hsum : ∑ j, homogeneousComponent e (q j) ^ 2 = 0 := by
    rw [← homogeneousComponent_eq_zero (2 * e) (∑ j, q j ^ 2) (by omega),
      map_sum]
    exact Finset.sum_congr rfl fun j _ => (homogeneousComponent_two_mul_sq (hqe j) he0).symm
  have htop : ∀ j, homogeneousComponent e (q j) = 0 := by
    intro j
    refine (homogeneousComponent_isHomogeneous e (q j)).eq_zero_of_forall_eval_eq_zero
      fun x => ?_
    have hx := congrArg (eval x) hsum
    simp only [map_sum, map_pow, map_zero] at hx
    exact pow_eq_zero_iff two_ne_zero |>.1 <|
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _).1 hx j (Finset.mem_univ j)
  have hlt : e < e := by
    refine (Finset.sup_lt_iff he0).2 fun j _ => ?_
    simpa [htop j] using totalDegree_sub_homogeneousComponent_lt (hqe j) he0
  exact lt_irrefl e hlt

/-- If `∑ i, q i ^ 2` has total degree at most `2 * d`, then every `q i` has degree at most `d`. -/
theorem totalDegree_le_of_sum_sq {σ ι : Type*} [Fintype ι] {q : ι → MvPolynomial σ ℝ} {d : ℕ}
    (hdeg : (∑ i, q i ^ 2).totalDegree ≤ 2 * d) (i : ι) : (q i).totalDegree ≤ d :=
  totalDegree_le_of_sum_sq' (hdeg.trans (Nat.le_succ _)) i

end SumOfSquares

theorem sos_degree_bound {n d : Nat} {h : Poly n}
    (hsos : IsSOS h) (hdeg : h.totalDegree ≤ 2 * d) :
    ∃ (r : Nat) (q : Fin r → Poly n),
      h = Finset.univ.sum (fun i => q i ^ 2) ∧
      ∀ i, (q i).totalDegree ≤ d := by
  obtain ⟨r, q, rfl⟩ := hsos
  exact ⟨r, q, rfl, totalDegree_le_of_sum_sq hdeg⟩

/-- A sum of squares of degree at most `2d + 1` is a sum of squares of polynomials of degree at
most `d` (the degree of a real sum of squares is even). -/
theorem sos_degree_bound' {n d : Nat} {h : Poly n}
    (hsos : IsSOS h) (hdeg : h.totalDegree ≤ 2 * d + 1) :
    ∃ (r : Nat) (q : Fin r → Poly n),
      h = Finset.univ.sum (fun i => q i ^ 2) ∧
      ∀ i, (q i).totalDegree ≤ d := by
  obtain ⟨r, q, rfl⟩ := hsos
  exact ⟨r, q, rfl, totalDegree_le_of_sum_sq' hdeg⟩

section Weighted

open MvPolynomial
variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

/-- Weighted homogeneous polynomials of the same weight are closed under subtraction. -/
theorem IsWeightedHomogeneous.sub' {φ ψ : MvPolynomial σ R} {n : ℕ}
    (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ - ψ) n := by
  rw [← mem_weightedHomogeneousSubmodule] at hφ hψ ⊢
  exact sub_mem hφ hψ

/-- Numerals are weighted homogeneous of weight `0`. -/
theorem isWeightedHomogeneous_ofNat (k : ℕ) [k.AtLeastTwo] :
    IsWeightedHomogeneous w (OfNat.ofNat k : MvPolynomial σ R) 0 :=
  map_ofNat (C : R →+* MvPolynomial σ R) k ▸ isWeightedHomogeneous_C w _

end Weighted

/-- The weight function `p_k ↦ k` as a Mathlib weight. -/
def wt : PNat → ℕ := fun k => (k : ℕ)

/-- `monomialWeight` is the Mathlib weight for the weight function `k ↦ k`. -/
theorem monomialWeight_eq_weight (e : PNat →₀ ℕ) :
    monomialWeight e = Finsupp.weight wt e := by
  simp only [monomialWeight, wt, Finsupp.weight_apply, smul_eq_mul, mul_comm]

theorem wHomogeneous_iff {h : Λ} {D : ℕ} :
    WHomogeneous h D ↔ MvPolynomial.IsWeightedHomogeneous wt h D := by
  constructor
  · intro hh e he
    rw [← monomialWeight_eq_weight]
    exact hh e (MvPolynomial.mem_support_iff.2 he)
  · intro hh e he
    rw [monomialWeight_eq_weight]
    exact hh (MvPolynomial.mem_support_iff.1 he)

end AnyDim
end
