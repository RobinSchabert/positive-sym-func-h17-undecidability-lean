module

public import AnyDim.Counterexample.Proposition39
public import AnyDim.Counterexample.Elementary.CubeBound

/-!
# Theorem 3.1 and Corollary 3.6

Source: Debus--Schabert, Section 3.

The homogeneous symmetric function of degree `8`

  `F = 4 p_1² (p_3 - 4 p_1³)² + 9 p_2 (p_6 - 8 p_1² p_4 + 16 p_1⁴ p_2) - 16 p_1⁸`

satisfies (`theorem_3_1`):

1. `F` is any-dimensional positive definite (`theorem_3_1_1`, in `Octic.lean`);
2. there is no nonzero formal power series `Q ∈ ℝ[[X_1, X_2, …]]` of bounded degree such that
   `Q^{(n)}` and `Q^{(n)} F^{(n)}` are sums of squares for every `n ∈ ℕ` (`theorem_3_1_2`).

In particular there is no `0 ≠ Q ∈ SΣ` with `Q F ∈ SΣ` (`no_anyDimSOS_multiplier`), `F` is not a
sum of squares in the quotient field of `Λ` (`F_not_sos_in_fractionRing`, `corollary_3_6_a`), and
there is no any-dimensional Krivine--Stengle Positivstellensatz (`corollary_3_6_b`).

## Dependence on Theorem 3.2

`theorem_3_1_2` is proved with the **elementary** degree bound
`Elementary.corollary_3_4_elementary` (`n < 3 deg Q + 20`), so `theorem_3_1`, `corollary_3_6_a`
and `corollary_3_6_b` do **not** depend on the unproved Theorem 3.2:
`#print axioms theorem_3_1` shows only the standard axioms.

`theorem_3_1_2_via_corollary_3_4` is the proof exactly as written in the paper, using
Corollary 3.4 (`n < 2 deg Q + 8`); it depends on the `sorry` in `theorem_3_2`.

Also formalized here: the computations in Remark 3.5 (`remark_3_5`) and Remark 3.7
(`remark_3_7`, `remark_3_7_sphere`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open MvPolynomial

/-! ### Theorem 3.1 (2) -/

/-- **Theorem 3.1 (2).**  There is no nonzero formal power series `Q ∈ ℝ[[X_1, X_2, …]]` of
bounded degree (every truncation `Q^{(n)}` is a polynomial `a` of degree `≤ D`) such that
`Q^{(n)}` and `Q^{(n)} F^{(n)}` are sums of squares for every `n ∈ ℕ`.

Proof: `Q^{(n)} ≠ 0` for all sufficiently large `n`, and then the (elementary) degree bound for
sos multipliers of `F^{(n)}` gives `n < 3 D + 20`, a contradiction for large `n`.  This proof
does not depend on Theorem 3.2. -/
theorem theorem_3_1_2 :
    ¬ ∃ (Q : FSeries) (D : ℕ), Q ≠ 0 ∧ ∀ n, 0 < n →
      ∃ a : Poly n, IsTrunc Q n a ∧ a.totalDegree ≤ D ∧ IsSOS a ∧ IsSOS (a * trunc n F) := by
  rintro ⟨Q, D, hQ0, h⟩
  obtain ⟨n₀, hn₀⟩ := exists_forall_restrict_ne_zero hQ0
  obtain ⟨a, ha, hdeg, h1, h2⟩ := h (max n₀ (3 * D + 20)) (by omega)
  have ha0 : a ≠ 0 := ha.ne_zero (hn₀ _ (le_max_left _ _))
  have hbound := Elementary.corollary_3_4_elementary ha0 h1 h2
  omega

/-- Theorem 3.1 (2), proved exactly as in the paper from Corollary 3.4:
`D ≥ deg Q^{(n)} > (n - 8)/2` for all sufficiently large `n`, a contradiction.

This version depends on the unproved Theorem 3.2 (through Corollaries 3.3 and 3.4); the
statement is identical to `theorem_3_1_2`. -/
theorem theorem_3_1_2_via_corollary_3_4 :
    ¬ ∃ (Q : FSeries) (D : ℕ), Q ≠ 0 ∧ ∀ n, 0 < n →
      ∃ a : Poly n, IsTrunc Q n a ∧ a.totalDegree ≤ D ∧ IsSOS a ∧ IsSOS (a * trunc n F) := by
  rintro ⟨Q, D, hQ0, h⟩
  obtain ⟨n₀, hn₀⟩ := exists_forall_restrict_ne_zero hQ0
  obtain ⟨a, ha, hdeg, h1, h2⟩ := h (max n₀ (2 * D + 8)) (by omega)
  have ha0 : a ≠ 0 := ha.ne_zero (hn₀ _ (le_max_left _ _))
  have hbound := corollary_3_4 ha0 h1 h2
  omega

/-- Theorem 3.1 (2) in terms of the degree of the power series: no nonzero `Q` with all monomials
of degree `≤ D` has truncations `Q^{(n)}` such that `Q^{(n)}` and `Q^{(n)} F^{(n)}` are sums of
squares for all `n`. -/
theorem theorem_3_1_2' :
    ¬ ∃ (Q : FSeries) (D : ℕ), Q ≠ 0 ∧ FDegLE Q D ∧ ∀ n, 0 < n →
      ∀ a : Poly n, IsTrunc Q n a → IsSOS a ∧ IsSOS (a * trunc n F) := by
  rintro ⟨Q, D, hQ0, hD, h⟩
  refine theorem_3_1_2 ⟨Q, D, hQ0, fun n hn => ?_⟩
  obtain ⟨a, ha, hdeg⟩ := (fDegLE_iff Q D).mp hD n
  exact ⟨a, ha, hdeg, (h n hn a ha).1, (h n hn a ha).2⟩

/-- **Theorem 3.1.**  The symmetric function
`F = 4 p_1² (p_3 - 4 p_1³)² + 9 p_2 (p_6 - 8 p_1² p_4 + 16 p_1⁴ p_2) - 16 p_1⁸` is homogeneous of
degree `8` and satisfies:

1. `F` is any-dimensional positive definite, i.e. `F^{(n)}(x) > 0` for every nonzero `x ∈ ℝ^n`;
2. there is no nonzero formal power series `Q ∈ ℝ[[X_1, X_2, …]]` of bounded degree such that
   `Q^{(n)}` and `Q^{(n)} F^{(n)}` are sums of squares for every `n ∈ ℕ`. -/
theorem theorem_3_1 :
    WHomogeneous F 8 ∧ AnyDimPD F ∧
    ¬ ∃ (Q : FSeries) (D : ℕ), Q ≠ 0 ∧ ∀ n, 0 < n →
      ∃ a : Poly n, IsTrunc Q n a ∧ a.totalDegree ≤ D ∧ IsSOS a ∧ IsSOS (a * trunc n F) :=
  ⟨F_wHomogeneous, theorem_3_1_1, theorem_3_1_2⟩

/-- "In particular, there is no symmetric function `0 ≠ Q ∈ SΣ` such that `Q F ∈ SΣ`." -/
theorem no_anyDimSOS_multiplier : ¬ ∃ H : Λ, H ≠ 0 ∧ AnyDimSOS H ∧ AnyDimSOS (H * F) := by
  rintro ⟨H, hH0, hH1, hH2⟩
  refine theorem_3_1_2 ⟨toSeries H, wDegree H, toSeries_ne_zero hH0, fun n hn =>
    ⟨trunc n H, isTrunc_toSeries n H, totalDegree_trunc_le (wdeg_self H), hH1 n hn, ?_⟩⟩
  rw [← map_mul]
  exact hH2 n hn

/-- The degrees of sos multipliers of the truncations `F^{(n)}` grow at least linearly in `n`
(elementary bound; Corollary 3.4 gives the better bound `deg Q > (n - 8)/2`). -/
theorem multiplier_degree_linear {n : ℕ} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) : ((n : ℝ) - 20) / 3 < (Q.totalDegree : ℝ) := by
  have h := Elementary.corollary_3_4_elementary hQ0 hQ hQF
  have h' : (n : ℝ) < 3 * (Q.totalDegree : ℝ) + 20 := by exact_mod_cast h
  linarith

/-! ### Corollary 3.6 -/

/-- `F` is not a sum of squares in the quotient field of `Λ`. -/
theorem F_not_sos_in_fractionRing : ¬ IsSOS (algebraMap Λ (FractionRing Λ) F) := by
  rintro ⟨r, q, hq⟩
  -- a common denominator `b` of the `q_i`
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors Λ) Finset.univ q
  have hb' : ∀ i, ∃ c : Λ, algebraMap Λ (FractionRing Λ) c = (b : Λ) • q i :=
    fun i => hb i (Finset.mem_univ i)
  choose c hc using hb'
  have hb0 : (b : Λ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  -- `b² F = ∑ c_i²` in `Λ`
  have hkey : (b : Λ) ^ 2 * F = ∑ i, c i ^ 2 := by
    apply IsFractionRing.injective Λ (FractionRing Λ)
    rw [map_mul, map_pow, hq, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, hc i, Algebra.smul_def, mul_pow]
  refine no_anyDimSOS_multiplier ⟨(b : Λ) ^ 2, pow_ne_zero 2 hb0, fun n _ => ?_, fun n _ => ?_⟩
  · rw [map_pow]
    exact isSOS_sq _
  · rw [hkey, map_sum]
    simp only [map_pow]
    exact ⟨r, fun i => trunc n (c i), rfl⟩

/-- **Corollary 3.6, first statement.**  There exist symmetric functions that are
any-dimensional positive definite which are not sums of squares in the quotient field of `Λ`. -/
theorem corollary_3_6_a :
    ∃ f : Λ, AnyDimPD f ∧ ¬ IsSOS (algebraMap Λ (FractionRing Λ) f) :=
  ⟨F, theorem_3_1_1, F_not_sos_in_fractionRing⟩

/-- `F` admits no certificate of Krivine--Stengle type: there are no `q, g ∈ SΣ` and `k ∈ ℕ_0`
with `q F = F^{2k} + g`. -/
theorem F_no_krivine_stengle :
    ¬ ∃ (q g : Λ) (k : ℕ), AnyDimSOS q ∧ AnyDimSOS g ∧ q * F = F ^ (2 * k) + g := by
  rintro ⟨q, g, k, hq, hg, heq⟩
  refine no_anyDimSOS_multiplier ⟨q, ?_, hq, fun n hn => ?_⟩
  · -- `q ≠ 0` since `F^{2k} + g` is positive at `x = (1)`
    rintro rfl
    have hx : (fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    have hF := theorem_3_1_1 1 (fun _ => 1) hx
    have hgx := isSOS_eval_nonneg (hg 1 Nat.one_pos) (fun _ => 1)
    have h0 := congrArg (fun f => evalTruncHom (fun _ : Fin 1 => (1 : ℝ)) f) heq
    simp only [zero_mul, map_zero, map_add, map_pow, evalTruncHom_apply] at h0
    have hpow : 0 < evalTrunc F (fun _ : Fin 1 => (1 : ℝ)) ^ (2 * k) := pow_pos hF _
    have hgx' : 0 ≤ evalTrunc g (fun _ : Fin 1 => (1 : ℝ)) := hgx
    linarith
  · rw [heq, map_add, map_pow, pow_mul']
    exact (isSOS_sq _).add (hg n hn)

/-- **Corollary 3.6, second statement.**  No any-dimensional Krivine--Stengle Positivstellensatz
exists: it is not true that for every `f ∈ SP` there are `q, g ∈ SΣ` and `k ∈ ℕ_0` with
`q f = f^{2k} + g`. -/
theorem corollary_3_6_b :
    ¬ ∀ f : Λ, AnyDimPSD f →
      ∃ (q g : Λ) (k : ℕ), AnyDimSOS q ∧ AnyDimSOS g ∧ q * f = f ^ (2 * k) + g :=
  fun h => F_no_krivine_stengle (h F F_anyDimPSD)

/-! ### Remark 3.5 -/

/-- The homomorphism `φ : Λ → ℝ[T] ⊆ ℝ(T)` of Remark 3.5: `p_k ↦ T` for even `k` and
`p_k ↦ 1/2` for odd `k`. -/
def phi : Λ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval fun k : PNat =>
    if (k : ℕ) % 2 = 0 then Polynomial.X else Polynomial.C (1 / 2 : ℝ)

/-- **Remark 3.5:** `φ(F) = -1/16`. -/
theorem remark_3_5 : phi F = Polynomial.C (-(1 / 16 : ℝ)) := by
  have h1 : phi (p 1) = Polynomial.C (1 / 2 : ℝ) := by simp [phi, p]
  have h2 : phi (p 2) = Polynomial.X := by simp [phi, p]
  have h3 : phi (p 3) = Polynomial.C (1 / 2 : ℝ) := by simp [phi, p]
  have h4 : phi (p 4) = Polynomial.X := by simp [phi, p]
  have h6 : phi (p 6) = Polynomial.X := by simp [phi, p]
  apply Polynomial.funext
  intro t
  simp only [F, Fexpr, map_add, map_sub, map_mul, map_pow, map_ofNat, h1, h2, h3, h4, h6,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

/-! ### Remark 3.7 -/

/-- The point `x = (-1, …, -1, 1, …, 1) ∈ ℝ^{2n}` with `n` many `-1`'s and `1`'s. -/
def balancedPoint (n : ℕ) : Fin (n + n) → ℝ :=
  Fin.append (fun _ => -1) (fun _ => 1)

theorem tuplePower_balancedPoint (n k : ℕ) :
    tuplePower (balancedPoint n) k = n * (-1) ^ k + n := by
  unfold tuplePower balancedPoint
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one]

/-- **Remark 3.7:** `F^{(2n)}(x) = 36 n²` at `x = (-1, …, -1, 1, …, 1)`. -/
theorem remark_3_7 (n : ℕ) : evalTrunc F (balancedPoint n) = 36 * (n : ℝ) ^ 2 := by
  rw [evalTrunc_F]
  simp only [tuplePower_balancedPoint]
  unfold Fexpr
  norm_num
  ring

/-- **Remark 3.7:** the point `x / √(2n)` lies on the unit sphere (`p_2 = 1`), and `F` takes the
value `9 / (4 n²)` there.  So the minima of `F^{(n)}` on the unit sphere are not bounded away
from zero uniformly in `n`. -/
theorem remark_3_7_sphere {n : ℕ} (hn : 0 < n) :
    tuplePower (fun i => balancedPoint n i / Real.sqrt (2 * n)) 2 = 1 ∧
      evalTrunc F (fun i => balancedPoint n i / Real.sqrt (2 * n)) = 9 / (4 * (n : ℝ) ^ 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (2 * n) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * n) ≠ 0 := by
    intro h
    rw [h] at hs
    nlinarith
  constructor
  · rw [tuplePower_div, tuplePower_balancedPoint, hs]
    field_simp
    norm_num
  · have hval : evalTrunc F (fun i => balancedPoint n i / Real.sqrt (2 * n)) =
        evalTrunc F (balancedPoint n) / Real.sqrt (2 * n) ^ 8 := by
      rw [evalTrunc_F, evalTrunc_F]
      simp only [tuplePower_div]
      rw [Fexpr_rescale (tuplePower (balancedPoint n) 1) (tuplePower (balancedPoint n) 2)
        (tuplePower (balancedPoint n) 3) (tuplePower (balancedPoint n) 4)
        (tuplePower (balancedPoint n) 6) hs0]
      field_simp
    have h8 : Real.sqrt (2 * n) ^ 8 = (2 * (n : ℝ)) ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hs]
    rw [hval, remark_3_7, h8]
    field_simp
    ring

end AnyDim
end
