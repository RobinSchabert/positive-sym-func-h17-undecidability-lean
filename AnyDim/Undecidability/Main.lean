module

public import AnyDim.Undecidability.Homogenization

/-!
# Proposition 2.6 and Theorem 2.2: the reduction `P ↦ H_P`

Source: Debus--Schabert, Section 2.4.

For `P ∈ ℤ[Y_1, …, Y_k]` put `m = k + 2`, `d = max(1, deg P)`, `L = 2md + 2` and let

  `H_P = p_4^L G_P(p_2²/p_4, p_2² p_4/p_4², …, p_2^{2m+1} p_{4m+2}/p_4^{2m+1})`   (11)

(`HP P := homogenize L Q_P`, a denominator-free definition; `HP_eq_fraction` shows that it agrees
with (11) in the quotient field of `Λ_ℚ`).

* **Proposition 2.6** (`proposition_2_6`): `H_P ∈ ℚ[p_2, p_4, …, p_{4m+2}]` is homogeneous of
  degree `4L = 8(k+2)d + 8`, and
  (a) if `P` has no zero in `ℕ_0^k`, then `H_P^{(n)}(x) ≥ (1/4) p_4(x)^L > 0` for all `x ≠ 0`;
  (b) if `P` has a zero in `ℕ_0^k`, then `H_P^{(n)}(x) = -(1/4) p_4(x)^L < 0` for some `x ≠ 0`.
  Hence `H_P` is any-dimensional psd iff `P` has no zero in `ℕ_0^k` (`HP_anyDimPSD_iff`).
* **Theorem 2.2** (`theorem_2_2`): `H_P^{(n)} ≥ 0` on `ℚ^n` for all `n` iff `P` has no zero in
  `ℕ_0^k`.  Nonnegativity on `ℚ^n` and on `ℝ^n` agree by continuity (`nonnegOnRat_iff`), and it
  does not matter whether `n` ranges over `ℕ_0` or `ℕ = {1, 2, …}` (`nonnegOnRat_iff_pos`).
  For `k = 9` the instances `H_P` lie in `ℚ[p_2, p_4, …, p_46]` (`theorem_2_2_nine`).

What is *not* formalized is the notion of (un)decidability itself: the map `P ↦ H_P` is given by
explicit finite rational arithmetic (`Cconst`, `Kconst`, `dBound`, `Lconst`, `QP`, `homogenize`
are explicit), so `theorem_2_2` is a many-one reduction from the solvability of Diophantine
equations in `ℕ_0^k` to the decision problem of Theorem 2.2.  Undecidability then follows from
the theorem of Davis, Putnam, Robinson and Matiyasevich (and from Jones' theorem for `k = 9`),
see Remark 2.1; these two results are used as black boxes and are not part of this
formalization.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace AnyDim.Undecidability

variable {k : ℕ}

/-- The degree bound `d = max(1, deg P)`. -/
def dBound (P : MvPolynomial (Fin k) ℤ) : ℕ := max 1 P.totalDegree

theorem one_le_dBound (P : MvPolynomial (Fin k) ℤ) : 1 ≤ dBound P := le_max_left _ _

theorem totalDegree_le_dBound (P : MvPolynomial (Fin k) ℤ) : P.totalDegree ≤ dBound P :=
  le_max_right _ _

/-- The symmetric function `H_P` of (11). -/
def HP (P : MvPolynomial (Fin k) ℤ) : Λℚ :=
  homogenize (Lconst k (dBound P)) (QP k P (dBound P))

/-- **Definition (11):** in the quotient field of `Λ_ℚ`,

  `H_P = p_4^L · G_P(p_2²/p_4, p_2² p_4/p_4², …, p_2^{2m+1} p_{4m+2}/p_4^{2m+1})`,

where `Q_P = G_P(p_1, …, p_{2m+1})`; i.e. `H_P` is obtained from `Q_P` by substituting each `p_r`
by `p_2^r p_{2r}/p_4^r` and multiplying by `p_4^L`. -/
theorem HP_eq_fraction (P : MvPolynomial (Fin k) ℤ) :
    toFrac (HP P) = toFrac (p 4) ^ Lconst k (dBound P) * fracSubst (QP k P (dBound P)) :=
  toFrac_homogenize (QP_wdeg P (one_le_dBound P) (totalDegree_le_dBound P))

/-- `H_P` is homogeneous of degree `4L`. -/
theorem HP_wHomogeneous (P : MvPolynomial (Fin k) ℤ) :
    WHomogeneousℚ (HP P) (4 * Lconst k (dBound P)) :=
  homogenize_wHomogeneous _ _

/-- `4L = 8(k+2)d + 8`. -/
theorem four_mul_Lconst (k d : ℕ) : 4 * Lconst k d = 8 * (k + 2) * d + 8 := by
  unfold Lconst mconst
  ring

/-- `H_P ∈ ℚ[p_2, p_4, p_6, …]`: it uses only even power sums. -/
theorem HP_isEven (P : MvPolynomial (Fin k) ℤ) : IsEvenℚ (HP P) :=
  homogenize_isEven _ _

/-- `H_P ∈ ℚ[p_2, p_4, …, p_{4m+2}]` with `m = k + 2`. -/
theorem HP_mem_supported (P : MvPolynomial (Fin k) ℤ) :
    HP P ∈ MvPolynomial.supported ℚ {r : PNat | Even (r : ℕ) ∧ (r : ℕ) ≤ 4 * mconst k + 2} := by
  have h := homogenize_mem_supported (s := 2 * mconst k + 1) (by unfold mconst; omega)
    (Lconst k (dBound P)) (QP_mem_supported P (dBound P))
  rw [show 2 * (2 * mconst k + 1) = 4 * mconst k + 2 by ring] at h
  exact h

/-- `H_P^{(n)}(0) = 0` by homogeneity. -/
theorem evalTruncℚ_HP_zero (P : MvPolynomial (Fin k) ℤ) (n : ℕ) :
    evalTruncℚ (HP P) (0 : Fin n → ℝ) = 0 :=
  evalTruncℚ_zero_of_wHomogeneous (HP_wHomogeneous P)
    (by have := Lconst_pos k (dBound P); omega)

/-- For `x ≠ 0`: `H_P^{(n)}(x) = p_4(x)^L · 𝒬_P(y)` with `y = normalize x` as in (10). -/
theorem evalTruncℚ_HP (P : MvPolynomial (Fin k) ℤ) {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    evalTruncℚ (HP P) x =
      tuplePower x 4 ^ Lconst k (dBound P) * Qcal P (dBound P) (normalize x) := by
  unfold HP
  rw [evalTruncℚ_homogenize (QP_wdeg P (one_le_dBound P) (totalDegree_le_dBound P)) hx,
    evalTruncℚ_QP]

/-- **Proposition 2.6 (a):** if `P` has no zero in `ℕ_0^k`, then
`H_P^{(n)}(x) ≥ (1/4) p_4(x)^L` at every nonzero finite real tuple `x`. -/
theorem proposition_2_6_a (P : MvPolynomial (Fin k) ℤ) (hP : ¬ HasNatZero P)
    {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    1 / 4 * tuplePower x 4 ^ Lconst k (dBound P) ≤ evalTruncℚ (HP P) x ∧
      0 < 1 / 4 * tuplePower x 4 ^ Lconst k (dBound P) := by
  rw [evalTruncℚ_HP P hx]
  have hb : 0 < tuplePower x 4 ^ Lconst k (dBound P) := pow_pos (tuplePower_four_pos hx) _
  have hQ : 1 / 4 ≤ Qcal P (dBound P) (normalize x) :=
    lemma_2_5_a P (one_le_dBound P) (totalDegree_le_dBound P) hP (normalize_nonneg x)
  refine ⟨?_, by positivity⟩
  calc 1 / 4 * tuplePower x 4 ^ Lconst k (dBound P)
      = tuplePower x 4 ^ Lconst k (dBound P) * (1 / 4) := by ring
    _ ≤ tuplePower x 4 ^ Lconst k (dBound P) * Qcal P (dBound P) (normalize x) := by
        gcongr

/-- Proposition 2.6 (a): if `P` has no zero in `ℕ_0^k`, then `H_P` is any-dimensional positive
definite. -/
theorem HP_pos_of_not_hasNatZero (P : MvPolynomial (Fin k) ℤ) (hP : ¬ HasNatZero P) :
    AnyDimPDℚ (HP P) := by
  intro n x hx
  obtain ⟨h1, h2⟩ := proposition_2_6_a P hP hx
  linarith

/-- The tuple `x_i = √z_i` used in the proof of Proposition 2.6 (b). -/
theorem exists_sqrt_tuple {n : ℕ} (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∃ x : Fin n → ℝ, ∀ i, x i ^ 2 = z i :=
  ⟨fun i => Real.sqrt (z i), fun i => Real.sq_sqrt (hz i)⟩

/-- **Proposition 2.6 (b):** if `P` has a zero in `ℕ_0^k`, then there are `n` and a nonzero
`x ∈ ℝ^n` with `H_P^{(n)}(x) = -(1/4) p_4(x)^L < 0`. -/
theorem proposition_2_6_b (P : MvPolynomial (Fin k) ℤ) (hP : HasNatZero P) :
    ∃ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 ∧
      evalTruncℚ (HP P) x = -(1 / 4) * tuplePower x 4 ^ Lconst k (dBound P) ∧
      -(1 / 4) * tuplePower x 4 ^ Lconst k (dBound P) < 0 := by
  obtain ⟨n, z, -, hz, hz0, hz12, hQ⟩ := lemma_2_5_b P (dBound P) hP
  obtain ⟨x, hx⟩ := exists_sqrt_tuple z hz
  -- `p_2(x) = p_1(z)` and `p_4(x) = p_2(z)`
  have hx2 : tuplePower x 2 = tuplePower z 1 := by
    unfold tuplePower
    exact Finset.sum_congr rfl fun i _ => by rw [hx i, pow_one]
  have hx4 : tuplePower x 4 = tuplePower z 2 := by
    unfold tuplePower
    exact Finset.sum_congr rfl fun i _ => by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx i]
  have hz1 : 0 < tuplePower z 1 := tuplePower_one_pos_of_nonneg hz hz0
  have hx0 : x ≠ 0 := by
    intro h0
    apply hz0
    funext i
    have := hx i
    rw [h0] at this
    simpa using this.symm
  -- the normalization (10) recovers `z`
  have hnorm : normalize x = z := by
    funext i
    unfold normalize
    rw [hx2, hx4, hz12, div_self hz1.ne', one_mul, hx i]
  have hb : 0 < tuplePower x 4 ^ Lconst k (dBound P) := pow_pos (tuplePower_four_pos hx0) _
  refine ⟨n, x, hx0, ?_, by linarith⟩
  rw [evalTruncℚ_HP P hx0, hnorm, hQ]
  ring

/-- Proposition 2.6 (b): if `P` has a zero in `ℕ_0^k`, then `H_P^{(n)}(x) < 0` at some nonzero
finite real tuple. -/
theorem HP_neg_of_hasNatZero (P : MvPolynomial (Fin k) ℤ) (hP : HasNatZero P) :
    ∃ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 ∧ evalTruncℚ (HP P) x < 0 := by
  obtain ⟨n, x, hx, h1, h2⟩ := proposition_2_6_b P hP
  exact ⟨n, x, hx, h1 ▸ h2⟩

/-- **Proposition 2.6, final statement:** `H_P` is any-dimensional psd if and only if `P` has no
zero in `ℕ_0^k`. -/
theorem HP_anyDimPSD_iff (P : MvPolynomial (Fin k) ℤ) : AnyDimPSDℚ (HP P) ↔ ¬ HasNatZero P := by
  constructor
  · intro hpsd hzero
    obtain ⟨n, x, -, hneg⟩ := HP_neg_of_hasNatZero P hzero
    exact absurd (hpsd n x) (not_le.mpr hneg)
  · intro hP n x
    by_cases hx : x = 0
    · rw [hx, evalTruncℚ_HP_zero]
    · exact (HP_pos_of_not_hasNatZero P hP n x hx).le

/-- **Proposition 2.6.**  For `P ∈ ℤ[Y_1, …, Y_k]`, with `m = k + 2`, `d = max(1, deg P)` and
`L = 2md + 2`: the symmetric function `H_P` lies in `ℚ[p_2, p_4, …, p_{4m+2}]`, is homogeneous of
degree `4L = 8(k+2)d + 8`, and satisfies (a) and (b); hence it is any-dimensional psd iff `P` has
no zero in `ℕ_0^k`. -/
theorem proposition_2_6 (P : MvPolynomial (Fin k) ℤ) :
    HP P ∈ MvPolynomial.supported ℚ {r : PNat | Even (r : ℕ) ∧ (r : ℕ) ≤ 4 * (k + 2) + 2} ∧
    WHomogeneousℚ (HP P) (8 * (k + 2) * dBound P + 8) ∧
    (¬ HasNatZero P → ∀ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 →
      1 / 4 * tuplePower x 4 ^ Lconst k (dBound P) ≤ evalTruncℚ (HP P) x ∧
        0 < 1 / 4 * tuplePower x 4 ^ Lconst k (dBound P)) ∧
    (HasNatZero P → ∃ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 ∧
      evalTruncℚ (HP P) x = -(1 / 4) * tuplePower x 4 ^ Lconst k (dBound P) ∧
        -(1 / 4) * tuplePower x 4 ^ Lconst k (dBound P) < 0) ∧
    (AnyDimPSDℚ (HP P) ↔ ¬ HasNatZero P) := by
  refine ⟨HP_mem_supported P, ?_, fun hP n x hx => proposition_2_6_a P hP hx,
    proposition_2_6_b P, HP_anyDimPSD_iff P⟩
  rw [← four_mul_Lconst]
  exact HP_wHomogeneous P

/-! ### Nonnegativity on rational points and Theorem 2.2 -/

/-- The value `f^{(n)}(x) ∈ ℚ` of the truncation of `f ∈ Λ_ℚ` at a rational tuple `x ∈ ℚ^n`. -/
def evalTruncRat {n : ℕ} (f : Λℚ) (x : Fin n → ℚ) : ℚ :=
  MvPolynomial.aeval (fun r : PNat => ∑ i, x i ^ (r : ℕ)) f

/-- The question of Theorem 2.2: is the truncation of `f` to `n` variables nonnegative on `ℚ^n`
for all `n`? -/
def NonnegOnRat (f : Λℚ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℚ), 0 ≤ evalTruncRat f x

/-- The rational value `f^{(n)}(x)` agrees with the real one. -/
theorem evalTruncRat_cast {n : ℕ} (f : Λℚ) (x : Fin n → ℚ) :
    ((evalTruncRat f x : ℚ) : ℝ) = evalTruncℚ f (fun i => (x i : ℝ)) := by
  unfold evalTruncRat evalTruncℚ evalHom
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, Rat.cast_add, hp, hq]
  | mul_X q i hq =>
    rw [map_mul, map_mul, Rat.cast_mul, hq, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp [tuplePower]

/-- `x ↦ f^{(n)}(x)` is continuous (it is a polynomial function). -/
theorem continuous_evalTruncℚ (f : Λℚ) (n : ℕ) :
    Continuous fun x : Fin n → ℝ => evalTruncℚ f x := by
  simp only [evalTruncℚ_eq_evalTrunc, evalTrunc, evalAt]
  exact MvPolynomial.continuous_eval _

/-- Nonnegativity of all truncations on `ℚ^n` is the same as nonnegativity on `ℝ^n`, by
continuity: `f` satisfies the question of Theorem 2.2 iff `f` is any-dimensional psd. -/
theorem nonnegOnRat_iff (f : Λℚ) : NonnegOnRat f ↔ AnyDimPSDℚ f := by
  constructor
  · intro h n
    have hdense : DenseRange (fun x : Fin n → ℚ => fun i => ((x i : ℚ) : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    have hclosed : IsClosed {x : Fin n → ℝ | 0 ≤ evalTruncℚ f x} :=
      isClosed_le continuous_const (continuous_evalTruncℚ f n)
    intro x
    refine hdense.induction_on (p := fun x => 0 ≤ evalTruncℚ f x) x hclosed fun y => ?_
    have := h n y
    rw [← evalTruncRat_cast]
    exact_mod_cast this
  · intro h n x
    have := h n (fun i => (x i : ℝ))
    rw [← evalTruncRat_cast] at this
    exact_mod_cast this

/-- The question of Theorem 2.2 with `n` ranging over `ℕ = {1, 2, …}` as in the paper: the case
`n = 0` (the constant term of `f`) follows from `n = 1`. -/
theorem nonnegOnRat_iff_pos (f : Λℚ) :
    NonnegOnRat f ↔ ∀ n : ℕ, 0 < n → ∀ x : Fin n → ℚ, 0 ≤ evalTruncRat f x := by
  refine ⟨fun h n _ x => h n x, fun h n x => ?_⟩
  cases n with
  | zero =>
    have hg : (fun r : PNat => ∑ i, x i ^ (r : ℕ)) =
        fun r : PNat => ∑ i, (0 : Fin 1 → ℚ) i ^ (r : ℕ) := by
      funext r
      simp [zero_pow r.ne_zero]
    have h1 := h 1 Nat.one_pos 0
    unfold evalTruncRat at h1 ⊢
    rw [hg]
    exact h1
  | succ n => exact h (n + 1) n.succ_pos x

/-- **Theorem 2.2 (the reduction).**  For every `P ∈ ℤ[Y_1, …, Y_k]` the rational symmetric
function `H_P` — homogeneous, even, and effectively computable from `P` — satisfies:

  the truncation of `H_P` to `n` variables is nonnegative on `ℚ^n` for all `n`
  ⟺ `P` has no zero in `ℕ_0^k`.

Together with the undecidability of the solvability of Diophantine equations in `ℕ_0^k`
(Remark 2.1, not formalized) this is the undecidability statement of Theorem 2.2. -/
theorem theorem_2_2 (P : MvPolynomial (Fin k) ℤ) : NonnegOnRat (HP P) ↔ ¬ HasNatZero P := by
  rw [nonnegOnRat_iff, HP_anyDimPSD_iff]

/-- Theorem 2.2 in terms of real symmetric functions: `H_P ∈ Λ_ℚ ⊆ Λ` is any-dimensional psd
iff `P` has no zero in `ℕ_0^k`. -/
theorem theorem_2_2_real (P : MvPolynomial (Fin k) ℤ) :
    AnyDimPSD (toΛ (HP P)) ↔ ¬ HasNatZero P := by
  rw [← anyDimPSDℚ_iff, HP_anyDimPSD_iff]

/-- **Theorem 2.2, second part.**  For Diophantine equations in nine unknowns (`k = 9`, so
`m = 11` and `4m + 2 = 46`) the instances `H_P` are homogeneous even symmetric functions in
`ℚ[p_2, p_4, …, p_46]`.  Together with Jones' theorem (Remark 2.1, not formalized) the decision
problem of Theorem 2.2 remains undecidable for such instances. -/
theorem theorem_2_2_nine (P : MvPolynomial (Fin 9) ℤ) :
    HP P ∈ MvPolynomial.supported ℚ {r : PNat | Even (r : ℕ) ∧ (r : ℕ) ≤ 46} ∧
    WHomogeneousℚ (HP P) (88 * dBound P + 8) ∧
    (NonnegOnRat (HP P) ↔ ¬ HasNatZero P) := by
  refine ⟨HP_mem_supported P, ?_, theorem_2_2 P⟩
  have h := HP_wHomogeneous P
  rw [four_mul_Lconst] at h
  exact h

/-- Reformulation: deciding the question of Theorem 2.2 for the instances `H_P` would decide the
existence of zeros in `ℕ_0^k` of integer polynomials. -/
theorem hasNatZero_iff_not_nonnegOnRat (P : MvPolynomial (Fin k) ℤ) :
    HasNatZero P ↔ ¬ NonnegOnRat (HP P) := by
  rw [theorem_2_2, not_not]

end AnyDim.Undecidability

end
