module

public import AnyDim.Basic

/-!
# The octic `F` and Theorem 3.1 (1)

Source: Debus--Schabert, Section 3, Theorem 3.1 and its proof of part (1).

The homogeneous symmetric function of degree `8`

  `F = 4 p_1² (p_3 - 4 p_1³)² + 9 p_2 (p_6 - 8 p_1² p_4 + 16 p_1⁴ p_2) - 16 p_1⁸`

is any-dimensional positive definite.  Following the paper:

* `sigma t = 0` for `|t| ≤ 2/3` and `sigma t = sgn t` otherwise; inequality (12) is
  `abs_cube_sub_sigma_le : |t³ - σ(t)| ≤ 3 t² |t² - 1|`.
* For a tuple `x`, `kInt x = ∑_i σ(x_i) ∈ ℤ` and
  `Dval x = p_2(x) (p_6(x) - 2 p_4(x) + p_2(x)) = p_2(x) ∑_i x_i² (x_i² - 1)² ≥ 0`;
  inequality (13) in squared form is `sq_p3_sub_kInt_le : (p_3(x) - k)² ≤ 9 D`.
* `eighth_le` : `(p_3(x) - 1/2)² + 9 D ≥ 1/8` for every tuple `x` (the integer `k` has distance
  at least `1/2` from `1/2`).
* If `p_1(x) = 1/2`, then `F(x) = (p_3(x) - 1/2)² + 9 D - 1/16 ≥ 1/16` (`Fexpr_half`); by
  homogeneity `F ≥ 16 p_1⁸` everywhere (`sixteen_mul_le_evalTrunc_F`), and `F = 9 p_2 p_6` if
  `p_1 = 0` (`evalTrunc_F_of_p1_eq_zero`).
* `theorem_3_1_1 : AnyDimPD F`.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

/-- The expression defining `F` in terms of `p_1, p_2, p_3, p_4, p_6`. -/
def Fexpr {R : Type*} [CommRing R] (p1 p2 p3 p4 p6 : R) : R :=
  4 * p1 ^ 2 * (p3 - 4 * p1 ^ 3) ^ 2 + 9 * p2 * (p6 - 8 * p1 ^ 2 * p4 + 16 * p1 ^ 4 * p2)
    - 16 * p1 ^ 8

/-- The octic of Theorem 3.1:
`F = 4 p_1² (p_3 - 4 p_1³)² + 9 p_2 (p_6 - 8 p_1² p_4 + 16 p_1⁴ p_2) - 16 p_1⁸`. -/
def F : Λ := Fexpr (p 1) (p 2) (p 3) (p 4) (p 6)

/-- `F^{(n)}(x)` in terms of the power sums of `x`. -/
theorem evalTrunc_F {n : ℕ} (x : Fin n → ℝ) :
    evalTrunc F x = Fexpr (tuplePower x 1) (tuplePower x 2) (tuplePower x 3) (tuplePower x 4)
      (tuplePower x 6) := by
  have h : ∀ k : PNat, evalTruncHom x (p k) = tuplePower x (k : ℕ) := fun k => evalTrunc_p x k
  rw [← evalTruncHom_apply]
  simp only [F, Fexpr, map_add, map_sub, map_mul, map_pow, map_ofNat, h]
  rfl

/-! ### Homogeneity -/

section Weighted

open MvPolynomial
variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

/-- `Fexpr` is weighted homogeneous of weight `8` if `p_k` has weight `k`. -/
theorem isWeightedHomogeneous_Fexpr {p1 p2 p3 p4 p6 : MvPolynomial σ R}
    (h1 : IsWeightedHomogeneous w p1 1) (h2 : IsWeightedHomogeneous w p2 2)
    (h3 : IsWeightedHomogeneous w p3 3) (h4 : IsWeightedHomogeneous w p4 4)
    (h6 : IsWeightedHomogeneous w p6 6) :
    IsWeightedHomogeneous w (Fexpr p1 p2 p3 p4 p6) 8 := by
  have c4 := isWeightedHomogeneous_ofNat (σ := σ) (R := R) (w := w) 4
  have c8 := isWeightedHomogeneous_ofNat (σ := σ) (R := R) (w := w) 8
  have c9 := isWeightedHomogeneous_ofNat (σ := σ) (R := R) (w := w) 9
  have c16 := isWeightedHomogeneous_ofNat (σ := σ) (R := R) (w := w) 16
  have hA : IsWeightedHomogeneous w (p3 - 4 * p1 ^ 3) 3 := by
    refine IsWeightedHomogeneous.sub' h3 ?_
    convert c4.mul (h1.pow 3) using 1
  have hB : IsWeightedHomogeneous w (p6 - 8 * p1 ^ 2 * p4 + 16 * p1 ^ 4 * p2) 6 := by
    refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.sub' h6 ?_) ?_
    · convert (c8.mul (h1.pow 2)).mul h4 using 1
    · convert (c16.mul (h1.pow 4)).mul h2 using 1
  unfold Fexpr
  refine IsWeightedHomogeneous.sub' (IsWeightedHomogeneous.add ?_ ?_) ?_
  · convert (c4.mul (h1.pow 2)).mul (hA.pow 2) using 1
  · convert (c9.mul h2).mul hB using 1
  · convert c16.mul (h1.pow 8) using 1

end Weighted

/-- `F` is homogeneous of degree `8`. -/
theorem F_wHomogeneous : WHomogeneous F 8 := by
  rw [wHomogeneous_iff]
  exact isWeightedHomogeneous_Fexpr (MvPolynomial.isWeightedHomogeneous_X ℝ wt 1)
    (MvPolynomial.isWeightedHomogeneous_X ℝ wt 2) (MvPolynomial.isWeightedHomogeneous_X ℝ wt 3)
    (MvPolynomial.isWeightedHomogeneous_X ℝ wt 4) (MvPolynomial.isWeightedHomogeneous_X ℝ wt 6)

/-- `F` has degree `8`. -/
theorem F_wDegLE : WDegLE F 8 := F_wHomogeneous.wDegLE

/-! ### The scalar inequality (12) -/

/-- The rounding function of the proof of Theorem 3.1 (1): `σ(t) = 0` if `|t| ≤ 2/3`, and
`σ(t) = sgn t` otherwise. -/
def sigma (t : ℝ) : ℤ :=
  if |t| ≤ 2 / 3 then 0 else if 0 < t then 1 else -1

/-- (12) for `t > 2/3`. -/
theorem abs_cube_sub_one_le {t : ℝ} (ht : 2 / 3 < t) : |t ^ 3 - 1| ≤ 3 * t ^ 2 * |t ^ 2 - 1| := by
  have h1 : t ^ 3 - 1 = (t - 1) * (t ^ 2 + t + 1) := by ring
  have h2 : t ^ 2 - 1 = (t - 1) * (t + 1) := by ring
  have hpos1 : 0 < t ^ 2 + t + 1 := by nlinarith
  have hpos2 : 0 < t + 1 := by linarith
  rw [h1, h2, abs_mul, abs_mul, abs_of_pos hpos1, abs_of_pos hpos2]
  have hkey : t ^ 2 + t + 1 ≤ 3 * t ^ 2 * (t + 1) := by
    have hs : 0 ≤ t - 2 / 3 := by linarith
    nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs]
  calc |t - 1| * (t ^ 2 + t + 1) ≤ |t - 1| * (3 * t ^ 2 * (t + 1)) :=
        mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
    _ = 3 * t ^ 2 * (|t - 1| * (t + 1)) := by ring

/-- **Inequality (12):** `|t³ - σ(t)| ≤ 3 t² |t² - 1|` for all real `t`. -/
theorem abs_cube_sub_sigma_le (t : ℝ) : |t ^ 3 - (sigma t : ℝ)| ≤ 3 * t ^ 2 * |t ^ 2 - 1| := by
  unfold sigma
  split_ifs with h1 h2
  · -- `|t| ≤ 2/3`
    have ht2 : t ^ 2 ≤ 4 / 9 := by
      have := abs_le.mp h1
      nlinarith
    have habs : |t ^ 2 - 1| = 1 - t ^ 2 := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [Int.cast_zero, sub_zero, habs, abs_pow]
    have h0 : 0 ≤ |t| := abs_nonneg t
    have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
    calc |t| ^ 3 = |t| * t ^ 2 := by rw [← hsq]; ring
      _ ≤ 2 / 3 * t ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
      _ ≤ 3 * t ^ 2 * (1 - t ^ 2) := by nlinarith [sq_nonneg t]
  · -- `t > 2/3`
    have ht : 2 / 3 < t := by
      rw [not_le, abs_of_pos h2] at h1
      exact h1
    rw [Int.cast_one]
    exact abs_cube_sub_one_le ht
  · -- `t < -2/3`
    have ht : 2 / 3 < -t := by
      have h0 : t ≤ 0 := not_lt.mp h2
      rw [not_le, abs_of_nonpos h0] at h1
      exact h1
    have h := abs_cube_sub_one_le ht
    have e1 : t ^ 3 - ((-1 : ℤ) : ℝ) = -((-t) ^ 3 - 1) := by push_cast; ring
    rw [e1, abs_neg]
    calc |(-t) ^ 3 - 1| ≤ 3 * (-t) ^ 2 * |(-t) ^ 2 - 1| := h
      _ = 3 * t ^ 2 * |t ^ 2 - 1| := by rw [neg_sq]

/-! ### Inequality (13) -/

/-- The integer `k = ∑_i σ(x_i)`. -/
def kInt {n : ℕ} (x : Fin n → ℝ) : ℤ := ∑ i, sigma (x i)

/-- `D = p_2(x) (p_6(x) - 2 p_4(x) + p_2(x))`. -/
def Dval {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  tuplePower x 2 * (tuplePower x 6 - 2 * tuplePower x 4 + tuplePower x 2)

/-- `p_6(x) - 2 p_4(x) + p_2(x) = ∑_i x_i² (x_i² - 1)²`. -/
theorem defect_eq_sum {n : ℕ} (x : Fin n → ℝ) :
    tuplePower x 6 - 2 * tuplePower x 4 + tuplePower x 2 = ∑ i, x i ^ 2 * (x i ^ 2 - 1) ^ 2 := by
  simp only [tuplePower, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `D = p_2(x) ∑_i x_i² (x_i² - 1)²`. -/
theorem Dval_eq {n : ℕ} (x : Fin n → ℝ) :
    Dval x = (∑ i, x i ^ 2) * ∑ i, x i ^ 2 * (x i ^ 2 - 1) ^ 2 := by
  rw [Dval, defect_eq_sum]
  rfl

/-- `D ≥ 0`. -/
theorem Dval_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ Dval x := by
  rw [Dval_eq]
  exact mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **Inequality (13)**, in squared form: `(p_3(x) - k)² ≤ 9 D`, i.e. `|p_3(x) - k| ≤ 3 √D`. -/
theorem sq_p3_sub_kInt_le {n : ℕ} (x : Fin n → ℝ) :
    (tuplePower x 3 - (kInt x : ℝ)) ^ 2 ≤ 9 * Dval x := by
  -- triangle inequality and (12)
  have h1 : |tuplePower x 3 - (kInt x : ℝ)| ≤ 3 * ∑ i, |x i| * (|x i| * |x i ^ 2 - 1|) := by
    have hsum : tuplePower x 3 - (kInt x : ℝ) = ∑ i, (x i ^ 3 - (sigma (x i) : ℝ)) := by
      rw [tuplePower, kInt, Int.cast_sum, Finset.sum_sub_distrib]
    rw [hsum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (abs_cube_sub_sigma_le (x i)).trans (le_of_eq ?_)
    rw [← sq_abs (x i)]
    ring
  -- Cauchy--Schwarz
  have h2 : (∑ i, |x i| * (|x i| * |x i ^ 2 - 1|)) ^ 2 ≤ Dval x := by
    rw [Dval_eq]
    refine (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |x i|)
      (fun i => |x i| * |x i ^ 2 - 1|)).trans (le_of_eq ?_)
    congr 1
    · exact Finset.sum_congr rfl fun i _ => sq_abs (x i)
    · exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, sq_abs, sq_abs]
  have h3 : 0 ≤ ∑ i, |x i| * (|x i| * |x i ^ 2 - 1|) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc (tuplePower x 3 - (kInt x : ℝ)) ^ 2 = |tuplePower x 3 - (kInt x : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (3 * ∑ i, |x i| * (|x i| * |x i ^ 2 - 1|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = 9 * (∑ i, |x i| * (|x i| * |x i ^ 2 - 1|)) ^ 2 := by ring
    _ ≤ 9 * Dval x := by linarith

/-- An integer has distance at least `1/2` from `1/2`. -/
theorem quarter_le_sq_int_sub_half (k : ℤ) : (1 / 4 : ℝ) ≤ ((k : ℝ) - 1 / 2) ^ 2 := by
  rcases le_or_gt k 0 with h | h
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast h
    nlinarith

/-- The key estimate of the proof of Theorem 3.1 (1): for every finite real tuple `x`,
`(p_3(x) - 1/2)² + 9 D ≥ 1/8`. -/
theorem eighth_le {n : ℕ} (x : Fin n → ℝ) :
    (1 / 8 : ℝ) ≤ (tuplePower x 3 - 1 / 2) ^ 2 + 9 * Dval x := by
  have h1 := sq_p3_sub_kInt_le x
  have h2 := quarter_le_sq_int_sub_half (kInt x)
  -- `(a + b)² ≤ 2 (a² + b²)` with `a = k - p_3`, `b = p_3 - 1/2`
  nlinarith [sq_nonneg ((kInt x : ℝ) - tuplePower x 3 - (tuplePower x 3 - 1 / 2))]

/-! ### Normalization `p_1 = 1/2` and Theorem 3.1 (1) -/

/-- For `p_1 = 1/2`: `F = (p_3 - 1/2)² + 9 p_2 (p_6 - 2 p_4 + p_2) - 1/16`. -/
theorem Fexpr_half (p2 p3 p4 p6 : ℝ) :
    Fexpr (1 / 2) p2 p3 p4 p6 = (p3 - 1 / 2) ^ 2 + 9 * (p2 * (p6 - 2 * p4 + p2)) - 1 / 16 := by
  unfold Fexpr
  ring

/-- `F` is homogeneous of degree `8`, at the level of values. -/
theorem Fexpr_rescale (p1 p2 p3 p4 p6 : ℝ) {c : ℝ} (hc : c ≠ 0) :
    Fexpr p1 p2 p3 p4 p6 =
      c ^ 8 * Fexpr (p1 / c) (p2 / c ^ 2) (p3 / c ^ 3) (p4 / c ^ 4) (p6 / c ^ 6) := by
  unfold Fexpr
  field_simp

theorem tuplePower_div {n : ℕ} (x : Fin n → ℝ) (c : ℝ) (k : ℕ) :
    tuplePower (fun i => x i / c) k = tuplePower x k / c ^ k := by
  simp only [tuplePower, div_pow, Finset.sum_div]

/-- If `p_1(x) = 0`, then `F(x) = 9 p_2(x) p_6(x)`. -/
theorem evalTrunc_F_of_p1_eq_zero {n : ℕ} {x : Fin n → ℝ} (h : tuplePower x 1 = 0) :
    evalTrunc F x = 9 * tuplePower x 2 * tuplePower x 6 := by
  rw [evalTrunc_F, h]
  unfold Fexpr
  ring

/-- `F ≥ 16 p_1⁸` (the remark following the proof of Theorem 3.1 (1)). -/
theorem sixteen_mul_le_evalTrunc_F {n : ℕ} (x : Fin n → ℝ) :
    16 * tuplePower x 1 ^ 8 ≤ evalTrunc F x := by
  by_cases h : tuplePower x 1 = 0
  · rw [evalTrunc_F_of_p1_eq_zero h, h]
    have h2 : 0 ≤ tuplePower x 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h6 : 0 ≤ tuplePower x 6 :=
      Finset.sum_nonneg fun i _ => (show Even 6 from ⟨3, rfl⟩).pow_nonneg _
    have : 0 ≤ 9 * tuplePower x 2 * tuplePower x 6 := by positivity
    simpa using this
  · -- rescale to `p_1 = 1/2`
    set c : ℝ := 2 * tuplePower x 1 with hc
    have hc0 : c ≠ 0 := mul_ne_zero two_ne_zero h
    set y : Fin n → ℝ := fun i => x i / c with hy
    have hy1 : tuplePower x 1 / c = 1 / 2 := by
      rw [hc]; field_simp
    have hval : evalTrunc F x = c ^ 8 * ((tuplePower y 3 - 1 / 2) ^ 2 + 9 * Dval y - 1 / 16) := by
      rw [evalTrunc_F,
        Fexpr_rescale (tuplePower x 1) (tuplePower x 2) (tuplePower x 3) (tuplePower x 4)
          (tuplePower x 6) hc0, hy1, Fexpr_half]
      simp only [Dval, hy, tuplePower_div]
    have hc8 : 0 ≤ c ^ 8 := (show Even 8 from ⟨4, rfl⟩).pow_nonneg c
    have hkey := eighth_le y
    have hpow : 16 * tuplePower x 1 ^ 8 = c ^ 8 * (1 / 16) := by
      rw [hc]; ring
    rw [hval, hpow]
    exact mul_le_mul_of_nonneg_left (by linarith) hc8

/-- **Theorem 3.1 (1).**  `F` is any-dimensional positive definite: `F^{(n)}(x) > 0` for every
`n` and every nonzero `x ∈ ℝ^n`. -/
theorem theorem_3_1_1 : AnyDimPD F := by
  intro n x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  by_cases h : tuplePower x 1 = 0
  · rw [evalTrunc_F_of_p1_eq_zero h]
    have h2 : 0 < tuplePower x 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, by positivity⟩
    have h6 : 0 < tuplePower x 6 :=
      Finset.sum_pos' (fun j _ => (show Even 6 from ⟨3, rfl⟩).pow_nonneg _)
        ⟨i, Finset.mem_univ i, by positivity⟩
    positivity
  · have hpos : 0 < tuplePower x 1 ^ 8 := by positivity
    have := sixteen_mul_le_evalTrunc_F x
    linarith

/-- `F` is in particular any-dimensional psd. -/
theorem F_anyDimPSD : AnyDimPSD F := by
  intro n x
  have h8 : 0 ≤ tuplePower x 1 ^ 8 := (show Even 8 from ⟨4, rfl⟩).pow_nonneg _
  have := sixteen_mul_le_evalTrunc_F x
  linarith

end AnyDim

end
