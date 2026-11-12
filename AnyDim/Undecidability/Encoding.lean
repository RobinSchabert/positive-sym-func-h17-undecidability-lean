module

public import AnyDim.Undecidability.Rounding

/-!
# Section 2.3: Encoding of integer polynomials (Lemma 2.5)

Source: Debus--Schabert, Section 2.3.

Let `P ∈ ℤ[Y_1, …, Y_k]` (here `P : MvPolynomial (Fin k) ℤ`, with `Y_{j+1} ↔ X j`) and let
`d ≥ 1` be a degree bound for `P`.  With `b_j = ∑_α |c_α| α_j` and `K = 1 + k C² ∑_j b_j²`
the paper defines (6)

  `𝒬_P(z) = P(S)² + K U E (1 + ∑_j S_j² + 16 U²)^{d-1} - 1/4`

for finite tuples `z` with `z_i ≥ 0`, where `S, U, E` come from Lemma 2.3.

* `HasNatZero P`: `P` has a zero in `ℕ_0^k`.
* `bcoef P j = b_j`, `Kconst P = K`, `Vval k z = V = 1 + ‖S‖² + 16 U²`, `Qcal P d z = 𝒬_P(z)`.
* Lemma 2.5: `lemma_2_5_a` (no zero ⟹ `𝒬_P(z) ≥ 1/4`) and `lemma_2_5_b`
  (a zero `N` ⟹ an explicit tuple `z ∈ A^n` with `p_2(z) = p_1(z)` and `𝒬_P(z) = -1/4`).
* The auxiliary claim (9) is `lemma_2_5_claim`; the witness tuple of the converse is
  `witness N` (`N_j` copies of `a_j`, `B` copies of `1/2`, one copy of `1`).

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace AnyDim.Undecidability

variable {k : ℕ}

/-- `P` has a zero in `ℕ_0^k`. -/
def HasNatZero (P : MvPolynomial (Fin k) ℤ) : Prop :=
  ∃ N : Fin k → ℕ, MvPolynomial.eval (fun j => (N j : ℤ)) P = 0

/-- `b_j = ∑_α |c_α| α_j` for `P = ∑_α c_α Y^α`. -/
def bcoef (P : MvPolynomial (Fin k) ℤ) (j : Fin k) : ℕ :=
  ∑ α ∈ P.support, (P.coeff α).natAbs * α j

/-- `K = 1 + k C² ∑_j b_j²`, a positive integer. -/
def Kconst (P : MvPolynomial (Fin k) ℤ) : ℕ :=
  1 + k * Cconst k ^ 2 * ∑ j, bcoef P j ^ 2

theorem Kconst_pos (P : MvPolynomial (Fin k) ℤ) : 0 < Kconst P := by
  unfold Kconst; omega

variable (k)

/-- `V = 1 + ‖S‖₂² + 16 U²` (proof of Lemma 2.5). -/
def Vval {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  1 + ∑ j : Fin k, Ssum z j ^ 2 + 16 * Usum z ^ 2

variable {k}

theorem one_le_Vval {n : ℕ} (z : Fin n → ℝ) : 1 ≤ Vval k z := by
  unfold Vval
  have h1 : 0 ≤ ∑ j : Fin k, Ssum z j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ 16 * Usum z ^ 2 := by positivity
  linarith

theorem Vval_nonneg {n : ℕ} (z : Fin n → ℝ) : 0 ≤ Vval k z :=
  zero_le_one.trans (one_le_Vval z)

/-- `𝒬_P(z)` of (6): `P(S)² + K U E V^{d-1} - 1/4`. -/
def Qcal (P : MvPolynomial (Fin k) ℤ) (d : ℕ) {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (MvPolynomial.aeval (Ssum z) P) ^ 2
    + (Kconst P : ℝ) * Usum z * Esum k z * Vval k z ^ (d - 1) - 1 / 4

/-! ### Evaluating an integer polynomial at natural numbers -/

/-- Evaluating `P` at natural numbers in `ℝ` is the cast of the integer value `P(N)`. -/
theorem aeval_natCast_eq (P : MvPolynomial (Fin k) ℤ) (N : Fin k → ℕ) :
    MvPolynomial.aeval (fun j => (N j : ℝ)) P =
      ((MvPolynomial.eval (fun j => (N j : ℤ)) P : ℤ) : ℝ) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-! ### The auxiliary claim (9) -/

/-- Monomial bound: `(ξ^β)² ≤ V^{|β|}` when every `ξ_i² ≤ V`. -/
theorem sq_monomial_le {ξ : Fin k → ℝ} {V : ℝ} (hξ : ∀ i, ξ i ^ 2 ≤ V)
    (β : Fin k →₀ ℕ) :
    (β.prod fun i e => ξ i ^ e) ^ 2 ≤ V ^ (β.sum fun _ e => e) := by
  rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) (hξ i) _

/-- Gradient bound: `|∂_j P(ξ)|² ≤ b_j² V^{d-1}` on the ball `1 + ‖ξ‖² ≤ V`. -/
theorem gradient_bound (P : MvPolynomial (Fin k) ℤ) {d : ℕ} (hd : 1 ≤ d)
    (hPd : P.totalDegree ≤ d) {ξ : Fin k → ℝ} {V : ℝ} (hV : 1 + ∑ j, ξ j ^ 2 ≤ V) (j : Fin k) :
    |MvPolynomial.aeval ξ (MvPolynomial.pderiv j P)| ^ 2 ≤ (bcoef P j : ℝ) ^ 2 * V ^ (d - 1) := by
  have hsq : 0 ≤ ∑ j, ξ j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hξ : ∀ i, ξ i ^ 2 ≤ V := fun i => by
    have := Finset.single_le_sum (fun i _ => sq_nonneg (ξ i)) (Finset.mem_univ i)
    linarith
  set W := V ^ (d - 1) with hW
  have hW0 : 0 ≤ W := pow_nonneg hV0 _
  -- the derivative as a sum over the support of `P`
  have hder : MvPolynomial.aeval ξ (MvPolynomial.pderiv j P) =
      ∑ α ∈ P.support, ((P.coeff α : ℝ) * (α j : ℝ)) *
        ((α - Finsupp.single j 1).prod fun i e => ξ i ^ e) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.aeval_monomial]
    simp
  -- every monomial of the derivative is bounded by `√W`
  have hmono : ∀ α ∈ P.support,
      |((α - Finsupp.single j 1).prod fun i e => ξ i ^ e)| * (α j : ℝ) ≤ Real.sqrt W * (α j : ℝ) := by
    intro α hα
    rcases Nat.eq_zero_or_pos (α j) with h0 | hpos
    · simp [h0]
    · refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      rw [Real.le_sqrt (abs_nonneg _) hW0, sq_abs]
      refine (sq_monomial_le hξ _).trans ?_
      refine pow_le_pow_right₀ hV1 ?_
      -- degree of `α - e_j` is `|α| - 1 ≤ d - 1`
      have hdeg := MvPolynomial.le_totalDegree hα
      have hsub : ((α - Finsupp.single j 1).sum fun _ e => e) + 1 = α.sum fun _ e => e := by
        have : α = (α - Finsupp.single j 1) + Finsupp.single j 1 := by
          rw [tsub_add_cancel_of_le]
          intro i
          simp only [Finsupp.single_apply]
          split_ifs with hij
          · subst hij; exact hpos
          · exact Nat.zero_le _
        conv_rhs => rw [this]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      omega
  have hb : (bcoef P j : ℝ) = ∑ α ∈ P.support, |(P.coeff α : ℝ)| * (α j : ℝ) := by
    unfold bcoef
    push_cast
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hle : |MvPolynomial.aeval ξ (MvPolynomial.pderiv j P)| ≤ (bcoef P j : ℝ) * Real.sqrt W := by
    rw [hder, hb, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α hα => ?_)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    calc |(P.coeff α : ℝ)| * (α j : ℝ) * |(α - Finsupp.single j 1).prod fun i e => ξ i ^ e|
        = |(P.coeff α : ℝ)| * (|(α - Finsupp.single j 1).prod fun i e => ξ i ^ e| * (α j : ℝ)) := by
          ring
      _ ≤ |(P.coeff α : ℝ)| * (Real.sqrt W * (α j : ℝ)) :=
          mul_le_mul_of_nonneg_left (hmono α hα) (abs_nonneg _)
      _ = |(P.coeff α : ℝ)| * (α j : ℝ) * Real.sqrt W := by ring
  calc |MvPolynomial.aeval ξ (MvPolynomial.pderiv j P)| ^ 2
      ≤ ((bcoef P j : ℝ) * Real.sqrt W) ^ 2 := by gcongr
    _ = (bcoef P j : ℝ) ^ 2 * W := by rw [mul_pow, Real.sq_sqrt hW0]

/-- The segment between `S` and `N` stays inside the ball `1 + ‖ξ‖² ≤ V`. -/
theorem segment_bound {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    1 + ∑ j : Fin k, ((1 - t) * Ssum z j + t * Ncount z j) ^ 2 ≤ Vval k z := by
  have hN := lemma_2_3_norm (k := k) hz
  have hconv : ∀ j : Fin k, ((1 - t) * Ssum z j + t * Ncount z j) ^ 2 ≤
      Ssum z j ^ 2 + (Ncount z j : ℝ) ^ 2 := by
    intro j
    have h1 : ((1 - t) * Ssum z j + t * Ncount z j) ^ 2 ≤
        (1 - t) * Ssum z j ^ 2 + t * (Ncount z j : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Ssum z j - Ncount z j), mul_nonneg ht0 (sub_nonneg.mpr ht1)]
    have h2 : (1 - t) * Ssum z j ^ 2 ≤ Ssum z j ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by linarith)
    have h3 : t * (Ncount z j : ℝ) ^ 2 ≤ (Ncount z j : ℝ) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) ht1
    linarith
  unfold Vval
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hconv j
  rw [Finset.sum_add_distrib] at this
  linarith

/-- The line `t ↦ (1 - t) S + t N` substituted into `P`, as a univariate real polynomial. -/
def linePoly (P : MvPolynomial (Fin k) ℤ) (S N : Fin k → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (S i) + Polynomial.C (N i - S i) * Polynomial.X) P

/-- `linePoly` evaluated at `t` is `P((1 - t) S + t N)`. -/
theorem aeval_linePoly (P : MvPolynomial (Fin k) ℤ) (S N : Fin k → ℝ) (t : ℝ) :
    Polynomial.aeval t (linePoly P S N) =
      MvPolynomial.aeval (fun i => (1 - t) * S i + t * N i) P := by
  unfold linePoly
  have h := MvPolynomial.comp_aeval_apply
    (fun i => Polynomial.C (S i) + Polynomial.C (N i - S i) * Polynomial.X)
    ((Polynomial.aeval t).restrictScalars ℤ) P
  simp only [AlgHom.coe_restrictScalars'] at h
  rw [h]
  refine congrArg (fun g => MvPolynomial.aeval g P) ?_
  funext i
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self_apply]
  ring

/-- Chain rule along the line: `φ'(t) = ∑_j ∂_j P((1 - t) S + t N) (N_j - S_j)`. -/
theorem derivative_linePoly (P : MvPolynomial (Fin k) ℤ) (S N : Fin k → ℝ) (t : ℝ) :
    Polynomial.aeval t (Polynomial.derivative (linePoly P S N)) =
      ∑ j, MvPolynomial.aeval (fun i => (1 - t) * S i + t * N i) (MvPolynomial.pderiv j P) *
        (N j - S j) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp [linePoly]
  | add p q hp hq =>
    simp only [linePoly, map_add] at hp hq ⊢
    rw [hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  | mul_X p i hp =>
    have hA : linePoly (p * MvPolynomial.X i) S N =
        linePoly p S N * (Polynomial.C (S i) + Polynomial.C (N i - S i) * Polynomial.X) := by
      simp [linePoly]
    have hL : Polynomial.derivative (Polynomial.C (S i) + Polynomial.C (N i - S i) * Polynomial.X) =
        Polynomial.C (N i - S i) := by
      simp
    have hsum : ∑ j, MvPolynomial.aeval (fun i => (1 - t) * S i + t * N i)
        (MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin k) ℤ)) * (N j - S j) =
          N i - S i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hji)]
        simp
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hA, Polynomial.derivative_mul, hL, map_add, map_mul, map_mul, hp, aeval_linePoly]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum]
    simp only [MvPolynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self_apply]
    ring

/-- Lagrange's mean value theorem along the segment plus Cauchy–Schwarz. -/
theorem mvt_sq_bound (P : MvPolynomial (Fin k) ℤ) (S N : Fin k → ℝ) (b : Fin k → ℝ) {W : ℝ}
    (_hW : 0 ≤ W)
    (hgrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ j : Fin k,
      |MvPolynomial.aeval (fun i => (1 - t) * S i + t * N i) (MvPolynomial.pderiv j P)| ^ 2
        ≤ b j ^ 2 * W) :
    |MvPolynomial.aeval S P - MvPolynomial.aeval N P| ^ 2 ≤
      (∑ j, b j ^ 2) * W * ∑ j, (S j - N j) ^ 2 := by
  have hf0 : Polynomial.aeval (0 : ℝ) (linePoly P S N) = MvPolynomial.aeval S P := by
    rw [aeval_linePoly]
    refine congrArg (fun g => MvPolynomial.aeval g P) ?_
    funext i
    ring
  have hf1 : Polynomial.aeval (1 : ℝ) (linePoly P S N) = MvPolynomial.aeval N P := by
    rw [aeval_linePoly]
    refine congrArg (fun g => MvPolynomial.aeval g P) ?_
    funext i
    ring
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun t => Polynomial.aeval t (linePoly P S N))
    (fun t => Polynomial.aeval t (Polynomial.derivative (linePoly P S N))) zero_lt_one
    (linePoly P S N).continuous_aeval.continuousOn
    (fun t _ => (linePoly P S N).hasDerivAt_aeval t)
  rw [sub_zero, div_one, hf1, hf0, derivative_linePoly] at hc'
  have hsub : MvPolynomial.aeval S P - MvPolynomial.aeval N P =
      -∑ j, MvPolynomial.aeval (fun i => (1 - c) * S i + c * N i) (MvPolynomial.pderiv j P) *
        (N j - S j) := by
    rw [hc']; ring
  rw [hsub, abs_neg, sq_abs]
  have hc0 : 0 ≤ c := hc.1.le
  have hc1 : c ≤ 1 := hc.2.le
  have hswap : ∑ j, (N j - S j) ^ 2 = ∑ j, (S j - N j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  calc (∑ j, MvPolynomial.aeval (fun i => (1 - c) * S i + c * N i) (MvPolynomial.pderiv j P) *
          (N j - S j)) ^ 2
      ≤ (∑ j, (MvPolynomial.aeval (fun i => (1 - c) * S i + c * N i)
            (MvPolynomial.pderiv j P)) ^ 2) * ∑ j, (N j - S j) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j, (MvPolynomial.aeval (fun i => (1 - c) * S i + c * N i)
            (MvPolynomial.pderiv j P)) ^ 2) * ∑ j, (S j - N j) ^ 2 := by rw [hswap]
    _ ≤ (∑ j, b j ^ 2 * W) * ∑ j, (S j - N j) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum fun j _ => by rw [← sq_abs]; exact hgrad c hc0 hc1 j)
          (Finset.sum_nonneg fun j _ => sq_nonneg _)
    _ = (∑ j, b j ^ 2) * W * ∑ j, (S j - N j) ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

/-- The constant `K` dominates `k C² ∑_j b_j²`. -/
theorem kCsq_sum_bcoef_le_Kconst (P : MvPolynomial (Fin k) ℤ) :
    (k : ℝ) * (Cconst k : ℝ) ^ 2 * ∑ j, (bcoef P j : ℝ) ^ 2 ≤ (Kconst P : ℝ) := by
  unfold Kconst
  push_cast
  linarith

/-- **Inequality (9):** `|P(S) - P(N)|² ≤ K U E V^{d-1}`. -/
theorem lemma_2_5_claim (P : MvPolynomial (Fin k) ℤ) {d : ℕ} (hd : 1 ≤ d) (hPd : P.totalDegree ≤ d)
    {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) :
    |MvPolynomial.aeval (Ssum z) P - MvPolynomial.aeval (fun j => (Ncount z j : ℝ)) P| ^ 2 ≤
      (Kconst P : ℝ) * Usum z * Esum k z * Vval k z ^ (d - 1) := by
  have hW : 0 ≤ Vval k z ^ (d - 1) := pow_nonneg (Vval_nonneg z) _
  have hgrad : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ j : Fin k,
      |MvPolynomial.aeval (fun i => (1 - t) * Ssum z i + t * (Ncount z i : ℝ))
          (MvPolynomial.pderiv j P)| ^ 2 ≤ (bcoef P j : ℝ) ^ 2 * Vval k z ^ (d - 1) :=
    fun t ht0 ht1 j => gradient_bound P hd hPd (segment_bound hz ht0 ht1) j
  have h1 := mvt_sq_bound P (Ssum z) (fun j => (Ncount z j : ℝ)) (fun j => (bcoef P j : ℝ))
    hW hgrad
  have h2 := lemma_2_3_dist (k := k) hz
  have hK := kCsq_sum_bcoef_le_Kconst P
  have hb : 0 ≤ ∑ j, (bcoef P j : ℝ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hU : 0 ≤ Usum z := Usum_nonneg hz
  have hE : 0 ≤ Esum k z := Esum_nonneg hz
  calc |MvPolynomial.aeval (Ssum z) P - MvPolynomial.aeval (fun j => (Ncount z j : ℝ)) P| ^ 2
      ≤ (∑ j, (bcoef P j : ℝ) ^ 2) * Vval k z ^ (d - 1) *
          ∑ j, (Ssum z j - Ncount z j) ^ 2 := h1
    _ ≤ (∑ j, (bcoef P j : ℝ) ^ 2) * Vval k z ^ (d - 1) *
          ((k : ℝ) * (Cconst k : ℝ) ^ 2 * Usum z * Esum k z) := by gcongr
    _ = ((k : ℝ) * (Cconst k : ℝ) ^ 2 * ∑ j, (bcoef P j : ℝ) ^ 2) *
          (Usum z * Esum k z * Vval k z ^ (d - 1)) := by ring
    _ ≤ (Kconst P : ℝ) * (Usum z * Esum k z * Vval k z ^ (d - 1)) := by gcongr
    _ = (Kconst P : ℝ) * Usum z * Esum k z * Vval k z ^ (d - 1) := by ring

/-! ### Lemma 2.5 (a): no zero ⟹ `𝒬_P ≥ 1/4` -/

/-- **Lemma 2.5 (a).**  If `P` has no zero in `ℕ_0^k`, then `𝒬_P(z) ≥ 1/4` for every
finite tuple `z` with `z_i ≥ 0`. -/
theorem lemma_2_5_a (P : MvPolynomial (Fin k) ℤ) {d : ℕ} (hd : 1 ≤ d)
    (hPd : P.totalDegree ≤ d) (hP : ¬ HasNatZero P) {n : ℕ} {z : Fin n → ℝ}
    (hz : ∀ i, 0 ≤ z i) : 1 / 4 ≤ Qcal P d z := by
  set S : ℝ := MvPolynomial.aeval (Ssum z) P with hSdef
  set Nr : ℝ := MvPolynomial.aeval (fun j => (Ncount z j : ℝ)) P with hNdef
  -- `P(N)` is a nonzero integer, hence `|P(N)| ≥ 1`
  have hN : (1 : ℝ) ≤ |Nr| := by
    have hne : MvPolynomial.eval (fun j => (Ncount z j : ℤ)) P ≠ 0 :=
      fun h => hP ⟨Ncount z, h⟩
    have hcast : Nr = ((MvPolynomial.eval (fun j => (Ncount z j : ℤ)) P : ℤ) : ℝ) :=
      aeval_natCast_eq P (Ncount z)
    rw [hcast]
    exact_mod_cast Int.one_le_abs hne
  have h52 : |S - Nr| ^ 2 ≤ (Kconst P : ℝ) * Usum z * Esum k z * Vval k z ^ (d - 1) :=
    lemma_2_5_claim P hd hPd hz
  -- `1 ≤ |P(N)|² ≤ 2 P(S)² + 2 |P(S) - P(N)|²`
  have hsq : (1 : ℝ) ≤ 2 * S ^ 2 + 2 * |S - Nr| ^ 2 := by
    have h1 : |Nr| ^ 2 ≤ 2 * S ^ 2 + 2 * |S - Nr| ^ 2 := by
      rw [sq_abs, sq_abs]
      nlinarith [sq_nonneg (S + (S - Nr))]
    have h0 : (1 : ℝ) ≤ |Nr| ^ 2 := by
      calc (1 : ℝ) = 1 ^ 2 := by ring
        _ ≤ |Nr| ^ 2 := by gcongr
    exact h0.trans h1
  unfold Qcal
  rw [← hSdef]
  linarith

/-! ### Lemma 2.5 (b): a zero ⟹ an explicit tuple with `𝒬_P = -1/4` -/

/-- `B = 4 ∑_j a_j (a_j - 1) N_j`, the number of copies of the label `1/2`
(`a_j = j + 2` for `j : Fin k`). -/
def Bcount (N : Fin k → ℕ) : ℕ :=
  4 * ∑ j : Fin k, ((j : ℕ) + 2) * ((j : ℕ) + 1) * N j

variable (k)

/-- The witness tuple of Lemma 2.5 (b) as a list: `N_j` copies of `a_j` for each `j`, then `B`
copies of `1/2`, then one copy of `1`. -/
def witnessList (N : Fin k → ℕ) : List ℝ :=
  ((List.finRange k).flatMap fun j => List.replicate (N j) ((label k j : ℚ) : ℝ))
    ++ List.replicate (Bcount N) (1 / 2 : ℝ) ++ [1]

/-- The witness tuple of Lemma 2.5 (b) as a finite tuple. -/
def witness (N : Fin k → ℕ) : Fin (witnessList k N).length → ℝ :=
  (witnessList k N).get

variable {k}

/-- A sum over the entries of a list indexed by `Fin l.length`. -/
theorem sum_get_eq_sum_map {L : List ℝ} (f : ℝ → ℝ) :
    ∑ i : Fin L.length, f (L.get i) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  rw [show (fun i => f (L.get i)) = f ∘ L.get from rfl, ← List.map_ofFn, List.ofFn_get]

/-- Sums over the witness tuple: `N_j` copies of `a_j`, `B` copies of `1/2`, one `1`. -/
theorem sum_witness (N : Fin k → ℕ) (f : ℝ → ℝ) :
    ∑ i, f (witness k N i) =
      ∑ j, (N j : ℝ) * f ((label k j : ℚ) : ℝ) + (Bcount N : ℝ) * f (1 / 2) + f 1 := by
  unfold witness
  rw [sum_get_eq_sum_map]
  unfold witnessList
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, List.map_replicate,
    List.sum_replicate, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  simp only [Function.comp_def, List.map_replicate, List.sum_replicate, nsmul_eq_mul,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← Fin.sum_univ_def]

/-- Every entry of the witness tuple is a label. -/
theorem witness_mem_labels0 (N : Fin k → ℕ) (i : Fin (witnessList k N).length) :
    witness k N i ∈ labels0 k := by
  have hmem : witness k N i ∈ witnessList k N := List.get_mem _ _
  unfold witnessList at hmem
  simp only [List.mem_append, List.mem_flatMap, List.mem_replicate, List.mem_singleton] at hmem
  rcases hmem with (⟨j, _, _, h⟩ | ⟨_, h⟩) | h <;> rw [h]
  · exact label_mem_labels0 k j
  · have := coe_mem_labels0 k ((mem_labels_iff k).mpr (Or.inl rfl))
    rwa [show ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) by push_cast; ring] at this
  · have := coe_mem_labels0 k ((mem_labels_iff k).mpr (Or.inr (Or.inl rfl)))
    rwa [Rat.cast_one] at this

theorem witness_nonneg (N : Fin k → ℕ) (i : Fin (witnessList k N).length) :
    0 ≤ witness k N i :=
  labels0_nonneg k (witness_mem_labels0 N i)

/-- The witness tuple is nonzero (its entries sum to at least `1`). -/
theorem witness_ne_zero (N : Fin k → ℕ) : witness k N ≠ 0 := by
  intro h0
  have hsum := sum_witness N id
  simp only [id, h0, Pi.zero_apply, Finset.sum_const_zero] at hsum
  have h1 : 0 ≤ ∑ j, (N j : ℝ) * ((label k j : ℚ) : ℝ) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (label_pos k j).le)
  have h2 : (0 : ℝ) ≤ (Bcount N : ℝ) * (1 / 2) := by positivity
  linarith

/-- Evaluating a rational polynomial at a rational point, viewed in `ℝ`. -/
theorem aeval_ratCast (Q : Polynomial ℚ) (a : ℚ) :
    Polynomial.aeval (a : ℝ) Q = ((Q.eval a : ℚ) : ℝ) := by
  rw [show (a : ℝ) = algebraMap ℚ ℝ a from (eq_ratCast _ _).symm,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

/-- `E = 0` for the witness: `Q` vanishes at every label. -/
theorem Esum_witness (N : Fin k → ℕ) : Esum k (witness k N) = 0 := by
  unfold Esum
  rw [sum_witness N (fun a => a * (Polynomial.aeval a (Qpoly k)) ^ 2)]
  have hQ : ∀ a ∈ labels k, Polynomial.aeval ((a : ℚ) : ℝ) (Qpoly k) = 0 := fun a ha => by
    rw [aeval_ratCast, Qpoly_eval_label k ha, Rat.cast_zero]
  have h12 : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by push_cast; ring
  have h1 : ((1 : ℚ) : ℝ) = (1 : ℝ) := by push_cast; ring
  rw [← h12, ← h1, hQ _ ((mem_labels_iff k).mpr (Or.inl rfl)),
    hQ _ ((mem_labels_iff k).mpr (Or.inr (Or.inl rfl)))]
  simp [hQ _ (label_mem_labels k _)]

/-- `S_j = N_j` for the witness: `ℓ_j` is `1` at `a_j` and `0` at the other labels. -/
theorem Ssum_witness (N : Fin k → ℕ) (j : Fin k) :
    Ssum (witness k N) j = (N j : ℝ) := by
  unfold Ssum
  rw [sum_witness N (fun a => Polynomial.aeval a (ell k j))]
  have hl : ∀ a ∈ labels k, Polynomial.aeval ((a : ℚ) : ℝ) (ell k j) =
      if a = label k j then 1 else 0 := fun a ha => by
    rw [aeval_ratCast, ell_eval_label k j ha]
    split_ifs <;> simp
  have h12 : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by push_cast; ring
  have h1 : ((1 : ℚ) : ℝ) = (1 : ℝ) := by push_cast; ring
  have hne12 : (1 / 2 : ℚ) ≠ label k j := by
    have := two_le_label k j; intro h; rw [← h] at this; norm_num at this
  have hne1 : (1 : ℚ) ≠ label k j := by
    have := two_le_label k j; intro h; rw [← h] at this; norm_num at this
  rw [← h12, ← h1, hl _ ((mem_labels_iff k).mpr (Or.inl rfl)),
    hl _ ((mem_labels_iff k).mpr (Or.inr (Or.inl rfl))), ite_eq_right_iff.mpr (fun h => absurd h hne12), ite_eq_right_iff.mpr (fun h => absurd h hne1)]
  simp only [mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i _ => by rw [hl _ (label_mem_labels k i)]]
  simp only [label_injective k |>.eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `N_j` counts the copies of `a_j` in the witness (not needed for Proposition 2.6). -/
theorem Ncount_witness (N : Fin k → ℕ) (j : Fin k) :
    Ncount (witness k N) j = N j := by
  have h := Ncount_eq_sum_roundInd (witness k N) j
  rw [sum_witness N (roundInd k j)] at h
  have hlab : ∀ i : Fin k, roundInd k j ((label k i : ℚ) : ℝ) = if i = j then 1 else 0 := by
    intro i
    unfold roundInd
    rw [nearest_of_mem k (label_mem_labels0 k i)]
    simp [Rat.cast_inj, label_injective k |>.eq_iff]
  have hhalf : roundInd k j (1 / 2) = 0 := by
    unfold roundInd
    have hmem : ((1 / 2 : ℚ) : ℝ) ∈ labels0 k :=
      coe_mem_labels0 k ((mem_labels_iff k).mpr (Or.inl rfl))
    have h12 : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by push_cast; ring
    rw [h12] at hmem
    rw [nearest_of_mem k hmem]
    split_ifs with hc
    · exfalso
      have h' : ((1 / 2 : ℚ) : ℝ) = ((label k j : ℚ) : ℝ) := by rw [h12, hc]
      have := Rat.cast_injective h'
      have := two_le_label k j
      linarith
    · rfl
  have hone : roundInd k j 1 = 0 := by
    unfold roundInd
    have hmem : ((1 : ℚ) : ℝ) ∈ labels0 k :=
      coe_mem_labels0 k ((mem_labels_iff k).mpr (Or.inr (Or.inl rfl)))
    rw [Rat.cast_one] at hmem
    rw [nearest_of_mem k hmem]
    split_ifs with hc
    · exfalso
      have h' : ((1 : ℚ) : ℝ) = ((label k j : ℚ) : ℝ) := by rw [Rat.cast_one, hc]
      have := Rat.cast_injective h'
      have := two_le_label k j
      linarith
    · rfl
  rw [hhalf, hone] at h
  simp only [hlab, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    add_zero] at h
  exact_mod_cast h

/-- The normalization `p_2(z) = p_1(z)` for the witness: the `B` copies of `1/2` balance
`∑_j a_j (a_j - 1) N_j`. -/
theorem tuplePower_witness (N : Fin k → ℕ) :
    tuplePower (witness k N) 2 = tuplePower (witness k N) 1 := by
  unfold tuplePower
  rw [sum_witness N (fun a => a ^ 2), sum_witness N (fun a => a ^ 1)]
  have hB : (Bcount N : ℝ) = 4 * ∑ j : Fin k, (((j : ℕ) : ℝ) + 2) * (((j : ℕ) : ℝ) + 1) * N j := by
    unfold Bcount
    push_cast
    rfl
  have hlab : ∀ j : Fin k, ((label k j : ℚ) : ℝ) = ((j : ℕ) : ℝ) + 2 := fun j => by
    unfold label; push_cast; ring
  simp only [hlab, hB, pow_one]
  have hkey : ∑ x : Fin k, (N x : ℝ) * (((x : ℕ) : ℝ) + 2) ^ 2 =
      ∑ x : Fin k, (N x : ℝ) * (((x : ℕ) : ℝ) + 2) +
        ∑ j : Fin k, (((j : ℕ) : ℝ) + 2) * (((j : ℕ) : ℝ) + 1) * N j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hkey]
  ring

/-- Every entry of the witness tuple lies in the label set `A = {1/2, 1, 2, …, k + 1}`
(the value `0` does not occur). -/
theorem witness_mem_labels (N : Fin k → ℕ) (i : Fin (witnessList k N).length) :
    ∃ a ∈ labels k, witness k N i = ((a : ℚ) : ℝ) := by
  have hmem : witness k N i ∈ witnessList k N := List.get_mem _ _
  unfold witnessList at hmem
  simp only [List.mem_append, List.mem_flatMap, List.mem_replicate, List.mem_singleton] at hmem
  rcases hmem with (⟨j, _, _, h⟩ | ⟨_, h⟩) | h
  · exact ⟨label k j, label_mem_labels k j, h⟩
  · exact ⟨1 / 2, (mem_labels_iff k).mpr (Or.inl rfl), by rw [h]; push_cast; ring⟩
  · exact ⟨1, (mem_labels_iff k).mpr (Or.inr (Or.inl rfl)), by rw [h, Rat.cast_one]⟩

/-- **Lemma 2.5 (b).**  If `P(N) = 0` for some `N ∈ ℕ_0^k`, then there are `n` and a tuple
`z ∈ A^n` (all coordinates are labels; in particular `z ≥ 0` and `z ≠ 0`) with
`p_2(z) = p_1(z)` and `𝒬_P(z) = -1/4`. -/
theorem lemma_2_5_b (P : MvPolynomial (Fin k) ℤ) (d : ℕ) (hP : HasNatZero P) :
    ∃ (n : ℕ) (z : Fin n → ℝ), (∀ i, ∃ a ∈ labels k, z i = ((a : ℚ) : ℝ)) ∧
      (∀ i, 0 ≤ z i) ∧ z ≠ 0 ∧
      tuplePower z 2 = tuplePower z 1 ∧ Qcal P d z = -1 / 4 := by
  obtain ⟨N, hN⟩ := hP
  refine ⟨_, witness k N, witness_mem_labels N, witness_nonneg N, witness_ne_zero N,
    tuplePower_witness N, ?_⟩
  have hS : Ssum (witness k N) = fun j => (N j : ℝ) := funext (Ssum_witness N)
  unfold Qcal
  rw [hS, Esum_witness, aeval_natCast_eq, hN]
  norm_num

end AnyDim.Undecidability

end
