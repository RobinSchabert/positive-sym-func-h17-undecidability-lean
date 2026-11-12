module

public import AnyDim.Undecidability.Encoding

/-!
# Section 2.4: Normalization and homogenization

Source: Debus--Schabert, Remark 2.4 and Section 2.4.

* `powerSumPoly f ∈ Λℚ` is the symmetric function `∑_i f(X_i)` for a univariate `f` with
  `f(0) = 0` (Remark 2.4); with it, `Spoly k j = S_j`, `Upoly = U = p_1`, `Epoly k = E` and
  `QP k P d = Q_P ∈ ℚ[p_1, …, p_{2m+1}]` (`QP_mem_supported`), the symmetric function (6); its
  value at a tuple `z` is `𝒬_P(z)` (`evalTruncℚ_QP`).
* Degrees: `deg S_j ≤ m`, `deg U = 1`, `deg E ≤ 2m + 1`, and (7), (8):
  `deg Q_P ≤ L := 2md + 2` (`QP_wdeg`).
* For a nonzero real tuple `x` put `y_i = (p_2(x)/p_4(x)) x_i²` (`normalize x`), see (10).  Then
  `p_r(y) = (p_2(x)/p_4(x))^r p_{2r}(x)` and `p_1(y) = p_2(y) = p_2(x)²/p_4(x)`.
* The homogenization (11) `H = p_4^L G(p_2²/p_4, p_2² p_4/p_4², …, p_2^{2m+1} p_{4m+2}/p_4^{2m+1})`
  is `homogenize L Q = ∑_{w ≤ L} p_4^{L-w} · subst (Q_w)` where `Q_w` is the part of `Q` of
  degree `w` and `subst : p_r ↦ p_2^r p_{2r}`; on basis elements this is the paper's
  `p_{r_1} ⋯ p_{r_s} ↦ p_4^{L-e} p_2^e ∏ p_{2 r_i}`, `e = ∑ r_i` (`homogenize_monomial`).
* `toFrac_homogenize`: in the quotient field of `Λ_ℚ`, `homogenize L Q` is literally the right
  hand side of (11), `p_4^L · Q(p_2^r p_{2r} / p_4^r)`.
* `homogenize L Q` is homogeneous of degree `4L` and even; if `Q ∈ ℚ[p_1, …, p_s]`, `s ≥ 2`, then
  `homogenize L Q ∈ ℚ[p_2, p_4, …, p_{2s}]` (`homogenize_mem_supported`); for `x ≠ 0` and
  `deg Q ≤ L`, `H^{(n)}(x) = p_4(x)^L · Q(y)` (`evalTruncℚ_homogenize`).

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace AnyDim.Undecidability

/-! ### Symmetric functions from univariate polynomials -/

/-- For `f ∈ ℚ[T]`, the element `∑_{r ≥ 1} coeff_r(f) · p_r ∈ Λℚ`.  If `f(0) = 0` this is the
abstract symmetric function `∑_i f(z_i)`; the constant term is dropped since `p_0` does
not exist in `Λℚ` (it would depend on the number of variables). -/
def powerSumPoly (f : Polynomial ℚ) : Λℚ :=
  ∑ r ∈ Finset.range f.natDegree, MvPolynomial.C (f.coeff (r + 1)) * p (Nat.succPNat r)

/-- `powerSumPoly f` evaluates to `∑_i f(z_i)` when `f(0) = 0`. -/
theorem evalTruncℚ_powerSumPoly (f : Polynomial ℚ) (hf : f.coeff 0 = 0) {n : ℕ}
    (z : Fin n → ℝ) : evalTruncℚ (powerSumPoly f) z = ∑ i, Polynomial.aeval (z i) f := by
  unfold powerSumPoly
  rw [evalTruncℚ_sum]
  simp only [evalTruncℚ_mul, evalTruncℚ_C, evalTruncℚ_p, Nat.succPNat_coe, tuplePower,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ', hf]
  simp [Rat.smul_def]

/-! ### Λℚ small API for weighted degree bounds -/

theorem wDegLE_iff {h : Λℚ} {D : ℕ} :
    WDegLEℚ h D ↔ ∀ d ∈ h.support, Finsupp.weight wt d ≤ D := by
  unfold WDegLEℚ MvPolynomial.weightedTotalDegree
  exact Finset.sup_le_iff

theorem WDegLEℚ.mono {h : Λℚ} {D E : ℕ} (hh : WDegLEℚ h D) (hDE : D ≤ E) : WDegLEℚ h E :=
  le_trans hh hDE

theorem wDegLE_C (c : ℚ) : WDegLEℚ (MvPolynomial.C c : Λℚ) 0 := by
  rw [wDegLE_iff]
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hd
  split_ifs at hd with h0
  · rw [← h0]; simp
  · exact absurd rfl hd

theorem wDegLE_one : WDegLEℚ (1 : Λℚ) 0 := by
  rw [← map_one MvPolynomial.C]; exact wDegLE_C 1

theorem wDegLE_ofNat (m : ℕ) [m.AtLeastTwo] : WDegLEℚ (OfNat.ofNat m : Λℚ) 0 := by
  rw [← map_ofNat (MvPolynomial.C : ℚ →+* Λℚ) m]; exact wDegLE_C _

theorem wDegLE_intCast (c : ℤ) : WDegLEℚ ((c : Λℚ)) 0 := by
  rw [← map_intCast (MvPolynomial.C : ℚ →+* Λℚ) c]; exact wDegLE_C _

theorem wDegLE_p (r : PNat) : WDegLEℚ (p r) (r : ℕ) := by
  rw [wDegLE_iff]
  intro d hd
  rw [p, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at hd
  split_ifs at hd with h0
  · rw [← h0, Finsupp.weight_single, smul_eq_mul, one_mul]
    rfl
  · exact absurd rfl hd

theorem WDegLEℚ.add {h₁ h₂ : Λℚ} {D : ℕ} (h1 : WDegLEℚ h₁ D) (h2 : WDegLEℚ h₂ D) :
    WDegLEℚ (h₁ + h₂) D := by
  rw [wDegLE_iff] at *
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact h1 d h
  · exact h2 d h

theorem WDegLEℚ.sub {h₁ h₂ : Λℚ} {D : ℕ} (h1 : WDegLEℚ h₁ D) (h2 : WDegLEℚ h₂ D) :
    WDegLEℚ (h₁ - h₂) D := by
  rw [wDegLE_iff] at *
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_sub PNat h₁ h₂ hd) with h | h
  · exact h1 d h
  · exact h2 d h

theorem WDegLEℚ.mul {h₁ h₂ : Λℚ} {D₁ D₂ : ℕ} (h1 : WDegLEℚ h₁ D₁) (h2 : WDegLEℚ h₂ D₂) :
    WDegLEℚ (h₁ * h₂) (D₁ + D₂) := by
  rw [wDegLE_iff] at *
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hd)
  rw [map_add]
  exact add_le_add (h1 a ha) (h2 b hb)

theorem WDegLEℚ.pow {h : Λℚ} {D : ℕ} (hh : WDegLEℚ h D) (e : ℕ) : WDegLEℚ (h ^ e) (e * D) := by
  induction e with
  | zero => simpa using wDegLE_one
  | succ e ih =>
    rw [pow_succ, add_mul, one_mul]
    exact ih.mul hh

theorem WDegLEℚ.sum {ι : Type*} (s : Finset ι) (f : ι → Λℚ) {D : ℕ}
    (hf : ∀ i ∈ s, WDegLEℚ (f i) D) : WDegLEℚ (∑ i ∈ s, f i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (wDegLE_C 0).mono (Nat.zero_le D)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem WDegLEℚ.prod {ι : Type*} (s : Finset ι) (f : ι → Λℚ) (D : ι → ℕ)
    (hf : ∀ i ∈ s, WDegLEℚ (f i) (D i)) : WDegLEℚ (∏ i ∈ s, f i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wDegLE_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Substituting elements of weighted degree `≤ m` into an integer polynomial of total degree
`≤ d` gives weighted degree `≤ m d`. -/
theorem WDegLEℚ.aeval {k : ℕ} (P : MvPolynomial (Fin k) ℤ) {d : ℕ} (hPd : P.totalDegree ≤ d)
    (g : Fin k → Λℚ) {m : ℕ} (hg : ∀ i, WDegLEℚ (g i) m) :
    WDegLEℚ (MvPolynomial.aeval g P) (m * d) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  refine WDegLEℚ.sum _ _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial, eq_intCast]
  have hdeg : (α.sum fun _ e => e) ≤ d := (MvPolynomial.le_totalDegree hα).trans hPd
  have hprod : WDegLEℚ (α.prod fun i e => g i ^ e) (m * α.sum fun _ e => e) := by
    unfold Finsupp.prod Finsupp.sum
    rw [Finset.mul_sum]
    exact WDegLEℚ.prod _ _ _ fun i _ => by rw [mul_comm]; exact (hg i).pow _
  have := (wDegLE_intCast (P.coeff α)).mul hprod
  rw [zero_add] at this
  exact this.mono (Nat.mul_le_mul_left m hdeg)

/-- `powerSumPoly f` has weighted degree at most `deg f`. -/
theorem powerSumPoly_wdeg (f : Polynomial ℚ) : WDegLEℚ (powerSumPoly f) f.natDegree := by
  unfold powerSumPoly
  refine WDegLEℚ.sum _ _ fun r hr => ?_
  have h := (wDegLE_C (f.coeff (r + 1))).mul (wDegLE_p (Nat.succPNat r))
  rw [zero_add, Nat.succPNat_coe] at h
  exact h.mono (Finset.mem_range.mp hr)

variable (k : ℕ)

/-- `S_j = ∑_i ℓ_j(z_i)` as an element of `Λℚ`. -/
def Spoly (j : Fin k) : Λℚ := powerSumPoly (ell k j)

/-- `U = ∑_i z_i = p_1` as an element of `Λℚ`. -/
def Upoly : Λℚ := p 1

/-- `E = ∑_i z_i Q(z_i)²` as an element of `Λℚ`. -/
def Epoly : Λℚ := powerSumPoly (Polynomial.X * Qpoly k ^ 2)

/-- `V = 1 + ∑_j S_j² + 16 U²` as an element of `Λℚ`. -/
def Vpoly : Λℚ := 1 + ∑ j : Fin k, Spoly k j ^ 2 + 16 * Upoly ^ 2

/-- The symmetric function `Q_P ∈ ℚ[p_1, …, p_{2m+1}]` of (6); its value at `z` is `𝒬_P(z)`. -/
def QP (P : MvPolynomial (Fin k) ℤ) (d : ℕ) : Λℚ :=
  (MvPolynomial.aeval (Spoly k) P) ^ 2
    + MvPolynomial.C (Kconst P : ℚ) * Upoly * Epoly k * Vpoly k ^ (d - 1)
    - MvPolynomial.C (1 / 4 : ℚ)

/-- `L = 2 m d + 2`, the degree bound (8) for `Q_P`. -/
def Lconst (d : ℕ) : ℕ := 2 * mconst k * d + 2

theorem Lconst_pos (d : ℕ) : 0 < Lconst k d := by
  unfold Lconst; omega

variable {k}

theorem evalTruncℚ_Spoly {n : ℕ} (z : Fin n → ℝ) (j : Fin k) :
    evalTruncℚ (Spoly k j) z = Ssum z j :=
  evalTruncℚ_powerSumPoly (ell k j) (ell_coeff_zero k j) z

theorem evalTruncℚ_Upoly {n : ℕ} (z : Fin n → ℝ) : evalTruncℚ Upoly z = Usum z := by
  rw [Upoly, evalTruncℚ_p, Usum_eq_tuplePower]
  rfl

theorem evalTruncℚ_Epoly {n : ℕ} (z : Fin n → ℝ) : evalTruncℚ (Epoly k) z = Esum k z := by
  rw [Epoly, evalTruncℚ_powerSumPoly _ (by simp)]
  unfold Esum
  simp only [map_mul, map_pow, Polynomial.aeval_X]

theorem evalTruncℚ_Vpoly {n : ℕ} (z : Fin n → ℝ) : evalTruncℚ (Vpoly k) z = Vval k z := by
  unfold Vpoly Vval
  rw [evalTruncℚ_add, evalTruncℚ_add, evalTruncℚ_one, evalTruncℚ_sum, evalTruncℚ_mul,
    evalTruncℚ_ofNat, evalTruncℚ_pow, evalTruncℚ_Upoly]
  simp only [evalTruncℚ_pow, evalTruncℚ_Spoly]

/-- Remark 2.4: `𝒬_P(z)` is the value of the symmetric function `Q_P` at `z`; so `𝒬_P` is given
by one symmetric function, independently of the number of variables. -/
theorem evalTruncℚ_QP (P : MvPolynomial (Fin k) ℤ) (d : ℕ) {n : ℕ} (z : Fin n → ℝ) :
    evalTruncℚ (QP k P d) z = Qcal P d z := by
  unfold QP Qcal
  rw [evalTruncℚ_sub, evalTruncℚ_add, evalTruncℚ_pow, evalTruncℚ_aeval, evalTruncℚ_mul,
    evalTruncℚ_mul, evalTruncℚ_mul, evalTruncℚ_pow, evalTruncℚ_C, evalTruncℚ_C,
    evalTruncℚ_Upoly, evalTruncℚ_Epoly, evalTruncℚ_Vpoly]
  simp only [evalTruncℚ_Spoly]
  push_cast
  ring

/-! ### Weighted degrees -/

theorem Spoly_wdeg (j : Fin k) : WDegLEℚ (Spoly k j) (mconst k) := by
  rw [← ell_natDegree k j]
  exact powerSumPoly_wdeg (ell k j)

theorem Upoly_wdeg : WDegLEℚ (Upoly : Λℚ) 1 := wDegLE_p 1

theorem Epoly_wdeg : WDegLEℚ (Epoly k) (2 * mconst k + 1) := by
  unfold Epoly
  refine (powerSumPoly_wdeg _).mono ?_
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero _ (Qpoly_monic k).ne_zero),
    Polynomial.natDegree_X, Polynomial.natDegree_pow, Qpoly_natDegree]
  omega

theorem Vpoly_wdeg : WDegLEℚ (Vpoly k) (2 * mconst k) := by
  unfold Vpoly
  have h1 : WDegLEℚ (1 : Λℚ) (2 * mconst k) := wDegLE_one.mono (Nat.zero_le _)
  have h2 : WDegLEℚ (∑ j : Fin k, Spoly k j ^ 2) (2 * mconst k) :=
    WDegLEℚ.sum _ _ fun j _ => (Spoly_wdeg j).pow 2
  have h3 : WDegLEℚ (16 * Upoly ^ 2 : Λℚ) (2 * mconst k) := by
    have := (wDegLE_ofNat 16).mul ((Upoly_wdeg).pow 2)
    rw [zero_add, mul_one] at this
    exact this.mono (by unfold mconst; omega)
  exact (h1.add h2).add h3

/-- (7), (8): `deg Q_P ≤ L = 2 m d + 2`. -/
theorem QP_wdeg (P : MvPolynomial (Fin k) ℤ) {d : ℕ} (hd : 1 ≤ d) (hPd : P.totalDegree ≤ d) :
    WDegLEℚ (QP k P d) (Lconst k d) := by
  unfold QP Lconst
  have hS : WDegLEℚ ((MvPolynomial.aeval (Spoly k) P) ^ 2) (2 * (mconst k * d)) :=
    (WDegLEℚ.aeval P hPd (Spoly k) fun j => Spoly_wdeg j).pow 2
  have hT : WDegLEℚ (MvPolynomial.C (Kconst P : ℚ) * Upoly * Epoly k * Vpoly k ^ (d - 1))
      (0 + 1 + (2 * mconst k + 1) + (d - 1) * (2 * mconst k)) :=
    (((wDegLE_C _).mul Upoly_wdeg).mul Epoly_wdeg).mul ((Vpoly_wdeg).pow (d - 1))
  have hc : WDegLEℚ (MvPolynomial.C (1 / 4 : ℚ) : Λℚ) 0 := wDegLE_C _
  refine ((hS.mono ?_).add (hT.mono ?_)).sub (hc.mono (Nat.zero_le _))
  · nlinarith
  · have : (d - 1) * (2 * mconst k) + 2 * mconst k = 2 * mconst k * d := by
      rcases Nat.exists_eq_add_of_le hd with ⟨e, rfl⟩
      simp only [Nat.add_sub_cancel_left]
      ring
    omega

/-! ### The normalization (10) -/

/-- (10): `y_i = (p_2(x) / p_4(x)) x_i²`. -/
def normalize {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (tuplePower x 2 / tuplePower x 4) * x i ^ 2

theorem normalize_nonneg {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : 0 ≤ normalize x i := by
  unfold normalize
  have h2 := tuplePower_nonneg_of_even x even_two
  have h4 := tuplePower_nonneg_of_even x (⟨2, rfl⟩ : Even 4)
  positivity

/-- `p_r(y) = (p_2(x)/p_4(x))^r p_{2r}(x)` for `y` as in (10). -/
theorem tuplePower_normalize {n : ℕ} (x : Fin n → ℝ) (r : ℕ) :
    tuplePower (normalize x) r = (tuplePower x 2 / tuplePower x 4) ^ r * tuplePower x (2 * r) := by
  simp only [tuplePower, normalize, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul]

/-- `p_1(y) = p_2(x)²/p_4(x)` for `y` as in (10). -/
theorem tuplePower_normalize_one {n : ℕ} (x : Fin n → ℝ) :
    tuplePower (normalize x) 1 = tuplePower x 2 ^ 2 / tuplePower x 4 := by
  rw [tuplePower_normalize, pow_one, mul_one]
  ring

/-- `p_2(y) = p_2(x)²/p_4(x) = p_1(y)` for `y` as in (10) and `x ≠ 0`. -/
theorem tuplePower_normalize_two {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    tuplePower (normalize x) 2 = tuplePower x 2 ^ 2 / tuplePower x 4 := by
  have hb : tuplePower x 4 ≠ 0 := (tuplePower_four_pos hx).ne'
  rw [tuplePower_normalize, show (2 * 2 : ℕ) = 4 from rfl, div_pow, pow_two (tuplePower x 4),
    div_mul_eq_mul_div, mul_div_mul_right _ _ hb]

/-! ### The homogenization (11) -/

/-- The substitution `p_r ↦ p_2^r p_{2r}`, an algebra endomorphism of `Λℚ`. -/
def subst : Λℚ →ₐ[ℚ] Λℚ :=
  MvPolynomial.aeval fun r : PNat => p 2 ^ (r : ℕ) * p (2 * r)

/-- The homogenization (11):
`homogenize L Q = p_4^L · Q(p_2 p_2 / p_4, p_2² p_4 / p_4², …)`, written without denominators as
`∑_{w ≤ L} p_4^{L - w} · subst (Q_w)`, where `Q_w` is the part of `Q` of weighted degree `w`. -/
def homogenize (L : ℕ) (Q : Λℚ) : Λℚ :=
  ∑ w ∈ Finset.range (L + 1),
    p 4 ^ (L - w) * subst (MvPolynomial.weightedHomogeneousComponent wt w Q)

theorem evalTruncℚ_prod {n : ℕ} (x : Fin n → ℝ) {ι : Type*} (s : Finset ι) (f : ι → Λℚ) :
    evalTruncℚ (∏ i ∈ s, f i) x = ∏ i ∈ s, evalTruncℚ (f i) x :=
  map_prod (evalHom x) f s

theorem two_mul_pnat_coe (i : PNat) : ((2 * i : PNat) : ℕ) = 2 * (i : ℕ) := by
  rw [PNat.mul_coe]; rfl

/-- `subst` on a monomial. -/
theorem subst_monomial (d : PNat →₀ ℕ) (r : ℚ) :
    subst (MvPolynomial.monomial d r) =
      MvPolynomial.C r * ∏ i ∈ d.support, (p 2 ^ (i : ℕ) * p (2 * i)) ^ d i := by
  unfold subst
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rfl

theorem two_mul_pnat_injective : Function.Injective (fun r : PNat => 2 * r) := by
  intro a b h
  exact mul_left_cancel h

/-- (11) on a basis element `p^α = p_{r_1} ⋯ p_{r_s}` of degree `e = w(α) ≤ L` (proof of
Proposition 2.6): `p^α ↦ p_4^{L - e} p_2^e ∏_r p_{2r}^{α_r}`. -/
theorem homogenize_monomial (L : ℕ) (α : PNat →₀ ℕ) (c : ℚ) (hα : Finsupp.weight wt α ≤ L) :
    homogenize L (MvPolynomial.monomial α c) =
      MvPolynomial.C c * p 4 ^ (L - Finsupp.weight wt α) * p 2 ^ (Finsupp.weight wt α) *
        MvPolynomial.rename (fun r : PNat => 2 * r) (MvPolynomial.monomial α 1) := by
  classical
  unfold homogenize
  have hmem : MvPolynomial.monomial α c ∈
      MvPolynomial.weightedHomogeneousSubmodule ℚ wt (Finsupp.weight wt α) :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule ℚ _ _ _).mpr
      (MvPolynomial.isWeightedHomogeneous_monomial wt α c rfl)
  rw [Finset.sum_eq_single (Finsupp.weight wt α)]
  · rw [MvPolynomial.weightedHomogeneousComponent_of_mem hmem, ite_eq_left_of_eq_true _ _ (eq_self _),
      subst_monomial,
      MvPolynomial.rename_monomial, MvPolynomial.monomial_eq, map_one, one_mul,
      Finsupp.prod_mapDomain_index_inj two_mul_pnat_injective]
    have hsplit : ∏ i ∈ α.support, (p 2 ^ (i : ℕ) * p (2 * i)) ^ α i =
        p 2 ^ (Finsupp.weight wt α) * α.prod fun r e => p (2 * r) ^ e := by
      rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]; rfl
    rw [hsplit]
    simp only [p]
    ring
  · intro w _ hw
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem hmem, ite_eq_right_of_eq_false _ _ (eq_false hw),
      map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hα)) h

/-- `subst` multiplies weights by `4`. -/
theorem subst_wHomogeneous {φ : Λℚ} {w : ℕ} (hφ : WHomogeneousℚ φ w) :
    WHomogeneousℚ (subst φ) (4 * w) := by
  unfold WHomogeneousℚ at *
  induction hφ using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_zero ℚ wt (4 * w)
  | add p q _ _ hp hq => rw [map_add]; exact hp.add hq
  | monomial d r hr =>
    rw [subst_monomial]
    have hfac : ∀ i ∈ d.support,
        MvPolynomial.IsWeightedHomogeneous wt ((p 2 ^ (i : ℕ) * p (2 * i)) ^ d i)
          (d i • ((i : ℕ) • wt 2 + wt (2 * i))) := fun i _ =>
      ((MvPolynomial.isWeightedHomogeneous_X ℚ wt 2).pow _ |>.mul
        (MvPolynomial.isWeightedHomogeneous_X ℚ wt (2 * i))).pow _
    have := (MvPolynomial.IsWeightedHomogeneous.prod _ _ _ hfac).C_mul r
    convert this using 1
    rw [← hr, Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul, wt, two_mul_pnat_coe, PNat.val_ofNat]
    ring

theorem even_of_mem_vars_subst_X (i : PNat) :
    ∀ k ∈ (p 2 ^ (i : ℕ) * p (2 * i) : Λℚ).vars, Even (k : ℕ) := by
  intro k hk
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk) with h | h
  · have := MvPolynomial.vars_pow _ _ h
    rw [p, MvPolynomial.vars_X, Finset.mem_singleton] at this
    subst this
    exact ⟨1, rfl⟩
  · rw [p, MvPolynomial.vars_X, Finset.mem_singleton] at h
    subst h
    rw [two_mul_pnat_coe]
    exact ⟨(i : ℕ), by ring⟩

/-- `subst` only produces even generators. -/
theorem subst_isEven (φ : Λℚ) : IsEvenℚ (subst φ) := by
  unfold IsEvenℚ
  induction φ using MvPolynomial.induction_on with
  | C a =>
    intro k hk
    rw [subst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.vars_C] at hk
    exact absurd hk (Finset.notMem_empty _)
  | add p q hp hq =>
    intro k hk
    rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ (map_add subst p q ▸ hk)) with h | h
    · exact hp k h
    · exact hq k h
  | mul_X q i hq =>
    intro k hk
    rw [map_mul, subst, MvPolynomial.aeval_X] at hk
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk) with h | h
    · exact hq k h
    · exact even_of_mem_vars_subst_X i k h

/-- `homogenize L Q` is homogeneous of degree `4 L`. -/
theorem homogenize_wHomogeneous (L : ℕ) (Q : Λℚ) : WHomogeneousℚ (homogenize L Q) (4 * L) := by
  unfold homogenize WHomogeneousℚ
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun w hw => ?_
  have hw' : w ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
  have h1 : MvPolynomial.IsWeightedHomogeneous wt (p 4 ^ (L - w)) ((L - w) • wt 4) :=
    (MvPolynomial.isWeightedHomogeneous_X ℚ wt 4).pow _
  have h2 := subst_wHomogeneous
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous w Q)
  convert h1.mul h2 using 1
  simp only [smul_eq_mul, wt, PNat.val_ofNat]
  omega

/-- `homogenize L Q ∈ ℚ[p_2, p_4, …]`. -/
theorem homogenize_isEven (L : ℕ) (Q : Λℚ) : IsEvenℚ (homogenize L Q) := by
  intro k hk
  unfold homogenize at hk
  obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hk)
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hw) with h | h
  · have := MvPolynomial.vars_pow _ _ h
    rw [p, MvPolynomial.vars_X, Finset.mem_singleton] at this
    subst this
    exact ⟨2, rfl⟩
  · exact subst_isEven _ k h

/-- Λℚ monomial evaluated at a tuple. -/
theorem evalTruncℚ_monomial (d : PNat →₀ ℕ) (r : ℚ) {n : ℕ} (y : Fin n → ℝ) :
    evalTruncℚ (MvPolynomial.monomial d r) y =
      (r : ℝ) * ∏ i ∈ d.support, tuplePower y (i : ℕ) ^ d i := by
  unfold evalTruncℚ evalHom
  rw [MvPolynomial.aeval_monomial, eq_ratCast]
  rfl

/-- For a monomial: `subst(p^α)(x) = p_4(x)^{w(α)} p^α(y)` with `y` as in (10). -/
theorem evalTruncℚ_subst_monomial (d : PNat →₀ ℕ) (r : ℚ) {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    evalTruncℚ (subst (MvPolynomial.monomial d r)) x =
      tuplePower x 4 ^ (Finsupp.weight wt d) *
        evalTruncℚ (MvPolynomial.monomial d r) (normalize x) := by
  have hb : tuplePower x 4 ≠ 0 := (tuplePower_four_pos hx).ne'
  rw [subst_monomial, evalTruncℚ_mul, evalTruncℚ_C, evalTruncℚ_prod, evalTruncℚ_monomial]
  simp only [evalTruncℚ_pow, evalTruncℚ_mul, evalTruncℚ_p, PNat.val_ofNat, two_mul_pnat_coe,
    tuplePower_normalize]
  have hfac : ∀ i ∈ d.support,
      (tuplePower x 2 ^ (i : ℕ) * tuplePower x (2 * (i : ℕ))) ^ d i =
        tuplePower x 4 ^ ((i : ℕ) * d i) *
          ((tuplePower x 2 / tuplePower x 4) ^ (i : ℕ) * tuplePower x (2 * (i : ℕ))) ^ d i := by
    intro i _
    rw [pow_mul, ← mul_pow, ← mul_assoc, ← mul_pow, mul_div_cancel₀ _ hb]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hw : Finsupp.weight wt d = ∑ i ∈ d.support, (i : ℕ) * d i := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]; rfl
  rw [hw]
  ring

/-- `subst(φ)(x) = p_4(x)^w φ(y)` for `φ` homogeneous of degree `w` and `y` as in (10). -/
theorem evalTruncℚ_subst {φ : Λℚ} {w : ℕ} (hφ : WHomogeneousℚ φ w) {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    evalTruncℚ (subst φ) x = tuplePower x 4 ^ w * evalTruncℚ φ (normalize x) := by
  induction hφ using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp [evalTruncℚ_zero]
  | add p q _ _ hp hq =>
    rw [map_add, evalTruncℚ_add, evalTruncℚ_add, hp, hq, mul_add]
  | monomial d r hr =>
    rw [evalTruncℚ_subst_monomial d r hx, hr]

/-- `Q = ∑_{w ≤ L} Q_w` when `wdeg Q ≤ L`. -/
theorem sum_weightedHomogeneousComponent_eq {L : ℕ} {Q : Λℚ} (hQ : WDegLEℚ Q L) :
    ∑ w ∈ Finset.range (L + 1), MvPolynomial.weightedHomogeneousComponent wt w Q = Q := by
  conv_rhs => rw [← MvPolynomial.sum_weightedHomogeneousComponent wt Q]
  rw [finsum_eq_sum_of_support_subset]
  intro w hw
  rw [Function.mem_support] at hw
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hw (MvPolynomial.weightedHomogeneousComponent_eq_zero w Q (lt_of_le_of_lt hQ (by omega)))

/-- **The evaluation identity in the proof of Proposition 2.6:** for `deg Q ≤ L` and `x ≠ 0`,
`(homogenize L Q)^{(n)}(x) = p_4(x)^L · Q(y)` with `y = normalize x` as in (10). -/
theorem evalTruncℚ_homogenize {L : ℕ} {Q : Λℚ} (hQ : WDegLEℚ Q L) {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    evalTruncℚ (homogenize L Q) x = tuplePower x 4 ^ L * evalTruncℚ Q (normalize x) := by
  unfold homogenize
  rw [evalTruncℚ_sum]
  simp only [evalTruncℚ_mul, evalTruncℚ_pow, evalTruncℚ_p, PNat.val_ofNat]
  have hterm : ∀ w ∈ Finset.range (L + 1),
      tuplePower x 4 ^ (L - w) *
          evalTruncℚ (subst (MvPolynomial.weightedHomogeneousComponent wt w Q)) x =
        tuplePower x 4 ^ L *
          evalTruncℚ (MvPolynomial.weightedHomogeneousComponent wt w Q) (normalize x) := by
    intro w hw
    rw [evalTruncℚ_subst (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous w Q) hx,
      ← mul_assoc, ← pow_add]
    congr 2
    have : w ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
    omega
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  conv_rhs => rw [← sum_weightedHomogeneousComponent_eq hQ]
  rw [evalTruncℚ_sum]

/-! ### Which power sums occur -/

theorem p_mem_supported {s : Set PNat} {r : PNat} (hr : r ∈ s) :
    p r ∈ MvPolynomial.supported ℚ s :=
  MvPolynomial.X_mem_supported.mpr hr

theorem C_mem_supported (s : Set PNat) (c : ℚ) :
    (MvPolynomial.C c : Λℚ) ∈ MvPolynomial.supported ℚ s :=
  (MvPolynomial.supported ℚ s).algebraMap_mem c

/-- `aeval g φ` lies in a subalgebra as soon as `g r` does for every `p_r` occurring in `φ`. -/
theorem aeval_mem_of_vars (S : Subalgebra ℚ Λℚ) (g : PNat → Λℚ) (φ : Λℚ)
    (hg : ∀ r ∈ φ.vars, g r ∈ S) : MvPolynomial.aeval g φ ∈ S := by
  have hsum : MvPolynomial.aeval g φ =
      ∑ d ∈ φ.support, MvPolynomial.aeval g (MvPolynomial.monomial d (φ.coeff d)) := by
    conv_lhs => rw [MvPolynomial.as_sum φ]
    rw [map_sum]
  rw [hsum]
  refine sum_mem fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  refine S.mul_mem (S.algebraMap_mem _) (prod_mem fun i hi => S.pow_mem (hg i ?_) _)
  exact (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩

/-- Substituting elements of a subalgebra into an integer polynomial stays in the subalgebra. -/
theorem aeval_int_mem {k : ℕ} (S : Subalgebra ℚ Λℚ) (g : Fin k → Λℚ) (hg : ∀ i, g i ∈ S)
    (P : MvPolynomial (Fin k) ℤ) : MvPolynomial.aeval g P ∈ S := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, eq_intCast]; exact intCast_mem S a
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | mul_X q i hq => rw [map_mul, MvPolynomial.aeval_X]; exact S.mul_mem hq (hg i)

theorem vars_weightedHomogeneousComponent_subset (w : ℕ) (Q : Λℚ) :
    (MvPolynomial.weightedHomogeneousComponent wt w Q).vars ⊆ Q.vars := by
  intro i hi
  rw [MvPolynomial.mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  refine ⟨d, ?_, hid⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_weightedHomogeneousComponent] at hd
  rw [MvPolynomial.mem_support_iff]
  intro h0
  apply hd
  rw [h0, ite_self]

/-- `∑_i f(X_i) ∈ ℚ[p_1, …, p_{deg f}]` (Remark 2.4). -/
theorem powerSumPoly_mem_supported (f : Polynomial ℚ) :
    powerSumPoly f ∈ MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ f.natDegree} := by
  unfold powerSumPoly
  refine sum_mem fun r hr => ?_
  refine Subalgebra.mul_mem _ (C_mem_supported _ _) (p_mem_supported ?_)
  have := Finset.mem_range.mp hr
  show ((Nat.succPNat r : PNat) : ℕ) ≤ f.natDegree
  rw [Nat.succPNat_coe]
  omega

theorem supported_le_mono {s t : ℕ} (hst : s ≤ t) :
    MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ s} ≤
      MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ t} :=
  MvPolynomial.supported_mono fun _ hr => le_trans hr hst

/-- Remark 2.4 and (6): `Q_P ∈ ℚ[p_1, …, p_{2m+1}]`. -/
theorem QP_mem_supported (P : MvPolynomial (Fin k) ℤ) (d : ℕ) :
    QP k P d ∈ MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ 2 * mconst k + 1} := by
  set A := MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ 2 * mconst k + 1} with hA
  have hS : ∀ j : Fin k, Spoly k j ∈ A := fun j => by
    have h := powerSumPoly_mem_supported (ell k j)
    rw [ell_natDegree] at h
    exact supported_le_mono (by omega) h
  have hU : (Upoly : Λℚ) ∈ A := p_mem_supported (by
    show ((1 : PNat) : ℕ) ≤ 2 * mconst k + 1
    rw [PNat.one_coe]; omega)
  have hE : Epoly k ∈ A := by
    have h := powerSumPoly_mem_supported (Polynomial.X * Qpoly k ^ 2)
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero _ (Qpoly_monic k).ne_zero),
      Polynomial.natDegree_X, Polynomial.natDegree_pow, Qpoly_natDegree] at h
    exact supported_le_mono (by omega) h
  have hV : Vpoly k ∈ A := by
    unfold Vpoly
    refine A.add_mem (A.add_mem A.one_mem (sum_mem fun j _ => A.pow_mem (hS j) 2)) ?_
    exact A.mul_mem (by simp) (A.pow_mem hU 2)
  unfold QP
  exact A.sub_mem
    (A.add_mem (A.pow_mem (aeval_int_mem A _ hS P) 2)
      (A.mul_mem (A.mul_mem (A.mul_mem (C_mem_supported _ _) hU) hE) (A.pow_mem hV _)))
    (C_mem_supported _ _)

/-- `subst` maps `ℚ[p_1, …, p_s]` into `ℚ[p_2, p_4, …, p_{2s}]`. -/
theorem subst_mem_supported {s : ℕ} {φ : Λℚ}
    (hφ : φ ∈ MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ s}) :
    subst φ ∈ MvPolynomial.supported ℚ {r : PNat | Even (r : ℕ) ∧ (r : ℕ) ≤ 2 * s} := by
  refine aeval_mem_of_vars _ _ φ fun r hr => ?_
  have hrs : (r : ℕ) ≤ s := MvPolynomial.mem_supported.mp hφ (Finset.mem_coe.mpr hr)
  have hr1 : 1 ≤ (r : ℕ) := r.pos
  refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (p_mem_supported ?_) _) (p_mem_supported ?_)
  · refine ⟨⟨1, rfl⟩, ?_⟩
    rw [PNat.val_ofNat]
    omega
  · refine ⟨⟨(r : ℕ), ?_⟩, ?_⟩
    · rw [two_mul_pnat_coe]; ring
    · rw [two_mul_pnat_coe]; omega

/-- If `Q ∈ ℚ[p_1, …, p_s]` with `s ≥ 2`, then `homogenize L Q ∈ ℚ[p_2, p_4, …, p_{2s}]`. -/
theorem homogenize_mem_supported {s : ℕ} (hs : 2 ≤ s) (L : ℕ) {Q : Λℚ}
    (hQ : Q ∈ MvPolynomial.supported ℚ {r : PNat | (r : ℕ) ≤ s}) :
    homogenize L Q ∈
      MvPolynomial.supported ℚ {r : PNat | Even (r : ℕ) ∧ (r : ℕ) ≤ 2 * s} := by
  unfold homogenize
  refine sum_mem fun w _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (p_mem_supported ?_) _) ?_
  · refine ⟨⟨2, rfl⟩, ?_⟩
    rw [PNat.val_ofNat]
    omega
  · refine subst_mem_supported (MvPolynomial.mem_supported.mpr ?_)
    exact (Finset.coe_subset.mpr (vars_weightedHomogeneousComponent_subset w Q)).trans
      (MvPolynomial.mem_supported.mp hQ)

/-! ### The formula (11) in the quotient field -/

/-- The inclusion of `Λ_ℚ` into its quotient field. -/
abbrev toFrac : Λℚ →+* FractionRing Λℚ := algebraMap Λℚ (FractionRing Λℚ)

/-- The substitution `p_r ↦ p_2^r p_{2r} / p_4^r` of (11), with values in the quotient field of
`Λ_ℚ`. -/
def fracSubst : Λℚ →ₐ[ℚ] FractionRing Λℚ :=
  MvPolynomial.aeval fun r : PNat => toFrac (p 2 ^ (r : ℕ) * p (2 * r)) / toFrac (p 4) ^ (r : ℕ)

theorem toFrac_p_ne_zero (r : PNat) : toFrac (p r) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective Λℚ (FractionRing Λℚ))]
  exact MvPolynomial.X_ne_zero r

/-- For a monomial: `subst(p^α) = p_4^{w(α)} · p^α(p_2^r p_{2r} / p_4^r)` in the quotient
field. -/
theorem toFrac_subst_monomial (d : PNat →₀ ℕ) (r : ℚ) :
    toFrac (subst (MvPolynomial.monomial d r)) =
      toFrac (p 4) ^ (Finsupp.weight wt d) * fracSubst (MvPolynomial.monomial d r) := by
  have hb : toFrac (p 4) ≠ 0 := toFrac_p_ne_zero 4
  rw [subst_monomial, map_mul, map_prod, fracSubst, MvPolynomial.aeval_monomial]
  have hC : toFrac (MvPolynomial.C r) = algebraMap ℚ (FractionRing Λℚ) r := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [hC]
  have hw : Finsupp.weight wt d = ∑ i ∈ d.support, (i : ℕ) * d i := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]; rfl
  have hfac : ∀ i ∈ d.support,
      toFrac ((p 2 ^ (i : ℕ) * p (2 * i)) ^ d i) =
        toFrac (p 4) ^ ((i : ℕ) * d i) *
          (toFrac (p 2 ^ (i : ℕ) * p (2 * i)) / toFrac (p 4) ^ (i : ℕ)) ^ d i := by
    intro i _
    rw [map_pow, div_pow, ← pow_mul, mul_div_cancel₀ _ (pow_ne_zero _ hb)]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hw,
    Finsupp.prod]
  ring

/-- `subst(φ) = p_4^w · φ(p_2^r p_{2r} / p_4^r)` for `φ` homogeneous of degree `w`. -/
theorem toFrac_subst {φ : Λℚ} {w : ℕ} (hφ : WHomogeneousℚ φ w) :
    toFrac (subst φ) = toFrac (p 4) ^ w * fracSubst φ := by
  induction hφ using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, mul_add]
  | monomial d r hr => rw [toFrac_subst_monomial d r, hr]

/-- **The formula (11):** in the quotient field of `Λ_ℚ`, for `deg Q ≤ L`,

  `homogenize L Q = p_4^L · Q(p_2²/p_4, p_2² p_4/p_4², p_2³ p_6/p_4³, …)`,

i.e. `homogenize L Q` is obtained from `Q` by substituting each `p_r` by `p_2^r p_{2r} / p_4^r`
and multiplying by `p_4^L`. -/
theorem toFrac_homogenize {L : ℕ} {Q : Λℚ} (hQ : WDegLEℚ Q L) :
    toFrac (homogenize L Q) = toFrac (p 4) ^ L * fracSubst Q := by
  unfold homogenize
  rw [map_sum]
  have hterm : ∀ w ∈ Finset.range (L + 1),
      toFrac (p 4 ^ (L - w) * subst (MvPolynomial.weightedHomogeneousComponent wt w Q)) =
        toFrac (p 4) ^ L * fracSubst (MvPolynomial.weightedHomogeneousComponent wt w Q) := by
    intro w hw
    have hwL : w ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
    rw [map_mul, map_pow,
      toFrac_subst (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous w Q),
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hwL]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
    sum_weightedHomogeneousComponent_eq hQ]

end AnyDim.Undecidability

end
