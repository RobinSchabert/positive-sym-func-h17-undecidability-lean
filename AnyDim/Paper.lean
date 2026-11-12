module

public import AnyDim.Undecidability.Main
public import AnyDim.Counterexample.Main

/-!
# The paper, statement by statement

This file follows

> S. Debus, R. Schabert, *Hilbert's 17th problem for symmetric functions: undecidability and a
> counterexample*, preprint, 2026

in the order of the paper.  **It is the place to start reading.**  Every numbered result of
Sections 2 and 3 that is formalized is restated here as a `theorem` whose docstring begins with
its label in the paper and records every deviation from the paper's wording.  The proofs in this
file are references to the development in `AnyDim/Undecidability/` and
`AnyDim/Counterexample/`; nothing new is proved here.

The file ends with the list of what is *not* formalized and with an axiom audit, which is checked
at compile time by `#guard_msgs`.

## One unproved statement

Blekherman's theorem (Theorem 3.2 of the paper, quoted there from the literature) is stated but
**not proved** (`sorry`).  Corollary 3.3 and Corollary 3.4 depend on it.  Theorem 3.1,
Corollary 3.6 and Proposition 3.9 do **not** depend on it, see `theorem_3_1` below.

## Notation

| paper | Lean |
|---|---|
| `Λ = ℝ[p₁, p₂, …]`, `Λ_ℚ` | `Λ`, `Λℚ` (`MvPolynomial ℕ+ ℝ`, `MvPolynomial ℕ+ ℚ`); `p r` is `p_r` |
| `ℝ[X₁, …, Xₙ]` | `Poly n` (`MvPolynomial (Fin n) ℝ`) |
| truncation `f^{(n)}` | `trunc n f : Poly n` |
| `f^{(n)}(x)` for `x ∈ ℝⁿ` | `evalTrunc f x` (`evalTruncℚ f x` for `f ∈ Λ_ℚ`) |
| `p_r(x) = x₁ʳ + ⋯ + xₙʳ` | `tuplePower x r` |
| sum of squares | `IsSOS` |
| any-dimensional psd / sos (`SP`, `SΣ`) | `AnyDimPSD`, `AnyDimSOS` |
| homogeneous of degree `d`; `deg f ≤ d` | `WHomogeneous f d`; `WDegLE f d` (`…ℚ` over `ℚ`) |
| `ℚ[p_r : r ∈ S]` | `MvPolynomial.supported ℚ S` |
| `ℝ[[X₁, X₂, …]]`, `g^{(n)}` | `FSeries`; `IsTrunc g n a` says that the polynomial `a` is `g^{(n)}` |
| `P` has a zero in `ℕ₀ᵏ` | `HasNatZero P` |

The variables `X₁, …, Xₙ` of the paper are indexed by `Fin n` (starting at `0`), and the paper's
`a_j = j + 1`, `1 ≤ j ≤ k`, is `label k j = j + 2` for `j : Fin k`.  The power sums are indexed
by `ℕ+`, so there is no `p₀`.  "Degree" of a symmetric function always refers to the grading
`deg p_r = r`.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace AnyDim.Paper

/-! ## Section 1: notation -/

/-- **Notation.**  The truncation `f ↦ f^{(n)}` is the homomorphism of `ℝ`-algebras
`Λ → ℝ[X₁, …, Xₙ]` with `p_r^{(n)} = X₁ʳ + ⋯ + Xₙʳ`. -/
theorem truncation_powerSum (n : ℕ) (r : ℕ+) :
    trunc n (p r) = ∑ i : Fin n, (MvPolynomial.X i : Poly n) ^ (r : ℕ) :=
  trunc_p n r

/-- **Definition (any-dimensional psd).**  `f ∈ SP` iff `f^{(n)} ≥ 0` on `ℝⁿ` for every
`n ∈ ℕ = {1, 2, …}`. -/
theorem definition_anyDimPSD (f : Λ) :
    AnyDimPSD f ↔ ∀ n : ℕ, 0 < n → ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (trunc n f) :=
  anyDimPSD_iff f

/-- **Definition (any-dimensional sos).**  `f ∈ SΣ` iff `f^{(n)}` is a sum of squares of
polynomials for every `n ∈ ℕ = {1, 2, …}`. -/
theorem definition_anyDimSOS (f : Λ) :
    AnyDimSOS f ↔
      ∀ n : ℕ, 0 < n → ∃ (r : ℕ) (q : Fin r → Poly n), trunc n f = ∑ j, q j ^ 2 :=
  Iff.rfl

/-- **Definition (bounded degree).**  A formal power series `g ∈ ℝ[[X₁, X₂, …]]` has
`deg g = sup_n deg g^{(n)} ≤ D` iff every truncation `g^{(n)}` is a polynomial of degree `≤ D`,
iff every monomial of `g` has degree `≤ D`. -/
theorem definition_boundedDegree (g : FSeries) (D : ℕ) :
    (∀ n, ∃ a : Poly n, IsTrunc g n a ∧ a.totalDegree ≤ D) ↔
      ∀ e : ℕ →₀ ℕ, MvPowerSeries.coeff e g ≠ 0 → e.degree ≤ D :=
  (fDegLE_iff g D).symm

/-- **Notation.**  Every symmetric function `f ∈ Λ` is a formal power series of bounded degree,
and the two notions of truncation agree. -/
theorem symmetric_function_as_series (f : Λ) (n : ℕ) :
    IsTrunc (toSeries f) n (trunc n f) ∧ (trunc n f).totalDegree ≤ wDegree f :=
  ⟨isTrunc_toSeries n f, totalDegree_trunc_le (wdeg_self f)⟩

/-! ## Section 2: undecidability -/

section Undecidability

open AnyDim.Undecidability

variable {k : ℕ}

/-- **Section 2.2, setup.**  The set `A = {1/2, 1, 2, …, k + 1}` has `m = k + 2` elements, and
the Lagrange polynomials `ℓ_j` satisfy `deg ℓ_j = m`, `ℓ_j(0) = 0`, `ℓ_j(a) = δ_{a, a_j}` for
`a ∈ A`, `R'(a_j) ≠ 0` and `(T - a_j) ℓ_j(T) = R(T) / R'(a_j)`. -/
theorem lagrange_polynomials (j : Fin k) :
    (labels k).card = k + 2 ∧ (ell k j).natDegree = k + 2 ∧ (ell k j).eval 0 = 0 ∧
    (∀ a ∈ labels k, (ell k j).eval a = if a = label k j then 1 else 0) ∧
    (Polynomial.derivative (Rpoly k)).eval (label k j) ≠ 0 ∧
    (Polynomial.X - Polynomial.C (label k j)) * ell k j =
      Polynomial.C (1 / (Polynomial.derivative (Rpoly k)).eval (label k j)) * Rpoly k :=
  ⟨card_labels k, ell_natDegree k j, ell_eval_zero k j, fun _ ha => ell_eval_label k j ha,
    derivative_Rpoly_eval_label_ne_zero k j, sub_mul_ell_eq k j⟩

/-- **Lemma 2.3.**  There is an effectively computable positive integer `C = Cconst k`,
depending only on `k`, with (1): `|ℓ_j(t) - ρ_j(t)| ≤ C t |Q(t)|` for all `t ≥ 0`.  Moreover,
for `x ∈ ℝⁿ_{≥0}` and `S_j, N_j, U, E` as in (2), one has (3):
`‖S - N‖² ≤ k C² U E` and `‖N‖² ≤ 16 U²`.

`Cconst k` is the explicit integer given by the right-hand side of (4) with ceilings; `N_j` is
`Ncount x j : ℕ`. -/
theorem lemma_2_3 (k : ℕ) :
    0 < Cconst k ∧
    (∀ (j : Fin k) (t : ℝ), 0 ≤ t →
      |Polynomial.aeval t (ell k j) - roundInd k j t| ≤
        (Cconst k : ℝ) * t * |Polynomial.aeval t (Qpoly k)|) ∧
    ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 ≤ x i) →
      ∑ j : Fin k, (Ssum x j - (Ncount x j : ℝ)) ^ 2 ≤
          (k : ℝ) * (Cconst k : ℝ) ^ 2 * Usum x * Esum k x ∧
        ∑ j : Fin k, (Ncount x j : ℝ) ^ 2 ≤ 16 * Usum x ^ 2 :=
  ⟨Cconst_pos k, fun j _ ht => abs_ell_sub_roundInd_le k j ht,
    fun _ _ hx => ⟨lemma_2_3_dist hx, lemma_2_3_norm hx⟩⟩

/-- **Remark 2.4 and (7).**  `S_j`, `U`, `E` are the values of symmetric functions
`Spoly k j`, `Upoly`, `Epoly k ∈ Λ_ℚ`, independently of `n`, and
`deg S_j ≤ m`, `deg U = 1`, `deg E ≤ 2m + 1` (so they lie in `ℚ[p₁, …, p_{2m+1}]`). -/
theorem remark_2_4 (j : Fin k) :
    (∀ (n : ℕ) (x : Fin n → ℝ),
      evalTruncℚ (Spoly k j) x = Ssum x j ∧ evalTruncℚ Upoly x = Usum x ∧
        evalTruncℚ (Epoly k) x = Esum k x) ∧
    WDegLEℚ (Spoly k j) (k + 2) ∧ WDegLEℚ (Upoly : Λℚ) 1 ∧
      WDegLEℚ (Epoly k) (2 * (k + 2) + 1) :=
  ⟨fun _ x => ⟨evalTruncℚ_Spoly x j, evalTruncℚ_Upoly x, evalTruncℚ_Epoly x⟩,
    Spoly_wdeg j, Upoly_wdeg, Epoly_wdeg⟩

/-- **Definition (6) and (8).**  With `d = max{1, deg P}` (`dBound P`) and `K_P = Kconst P`, the
symmetric function `Q_P = QP k P d` lies in `ℚ[p₁, …, p_{2m+1}]`, has `deg Q_P ≤ L = 2md + 2`,
and its value at `x` is `P(S)² + K_P U E (1 + ∑_j S_j² + 16 U²)^{d-1} - 1/4`. -/
theorem definition_QP (P : MvPolynomial (Fin k) ℤ) :
    dBound P = max 1 P.totalDegree ∧
    Kconst P = 1 + k * Cconst k ^ 2 * ∑ j, (∑ α ∈ P.support, (P.coeff α).natAbs * α j) ^ 2 ∧
    QP k P (dBound P) ∈ MvPolynomial.supported ℚ {r : ℕ+ | (r : ℕ) ≤ 2 * (k + 2) + 1} ∧
    WDegLEℚ (QP k P (dBound P)) (2 * (k + 2) * dBound P + 2) ∧
    ∀ (n : ℕ) (x : Fin n → ℝ), evalTruncℚ (QP k P (dBound P)) x =
      (MvPolynomial.aeval (Ssum x) P) ^ 2 +
        (Kconst P : ℝ) * Usum x * Esum k x *
          (1 + ∑ j : Fin k, Ssum x j ^ 2 + 16 * Usum x ^ 2) ^ (dBound P - 1) - 1 / 4 :=
  ⟨rfl, rfl, QP_mem_supported P (dBound P),
    QP_wdeg P (one_le_dBound P) (totalDegree_le_dBound P),
    fun _ x => evalTruncℚ_QP P (dBound P) x⟩

/-- **Lemma 2.5.**  (a) If `P` has no zero in `ℕ₀ᵏ`, then `Q_P(x) ≥ 1/4` for every
`x ∈ ⋃ₙ ℝⁿ_{≥0}`.  (b) If `P(N) = 0` for some `N ∈ ℕ₀ᵏ`, then there are `n ∈ ℕ` and `z ∈ Aⁿ`
with `p₁(z) = p₂(z)` and `Q_P(z) = -1/4`. -/
theorem lemma_2_5 (P : MvPolynomial (Fin k) ℤ) :
    (¬ HasNatZero P → ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 ≤ x i) →
      1 / 4 ≤ evalTruncℚ (QP k P (dBound P)) x) ∧
    (HasNatZero P → ∃ (n : ℕ) (z : Fin n → ℝ), 0 < n ∧
      (∀ i, ∃ a ∈ labels k, z i = ((a : ℚ) : ℝ)) ∧
      tuplePower z 1 = tuplePower z 2 ∧ evalTruncℚ (QP k P (dBound P)) z = -1 / 4) := by
  refine ⟨fun hP n x hx => ?_, fun hP => ?_⟩
  · rw [evalTruncℚ_QP]
    exact lemma_2_5_a P (one_le_dBound P) (totalDegree_le_dBound P) hP hx
  · obtain ⟨n, z, hA, -, hz0, h12, hQ⟩ := lemma_2_5_b P (dBound P) hP
    refine ⟨n, z, Nat.pos_of_ne_zero fun h0 => hz0 ?_, hA, h12.symm, ?_⟩
    · subst h0
      exact Subsingleton.elim _ _
    · rw [evalTruncℚ_QP]
      exact hQ

/-- **The normalization (10).**  For `0 ≠ x ∈ ℝⁿ` put `y_i = (p₂(x)/p₄(x)) x_i²`
(`normalize x`).  Then `p₂(x), p₄(x) > 0`, `y ∈ ℝⁿ_{≥0}`,
`p_r(y) = (p₂(x)/p₄(x))ʳ p_{2r}(x)` and `p₁(y) = p₂(y)`. -/
theorem normalization_10 {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < tuplePower x 2 ∧ 0 < tuplePower x 4 ∧
    (∀ i, normalize x i = tuplePower x 2 / tuplePower x 4 * x i ^ 2) ∧
    (∀ i, 0 ≤ normalize x i) ∧
    (∀ r : ℕ, tuplePower (normalize x) r =
      (tuplePower x 2 / tuplePower x 4) ^ r * tuplePower x (2 * r)) ∧
    tuplePower (normalize x) 1 = tuplePower (normalize x) 2 :=
  ⟨tuplePower_two_pos hx, tuplePower_four_pos hx, fun _ => rfl, normalize_nonneg x,
    tuplePower_normalize x, by rw [tuplePower_normalize_one, tuplePower_normalize_two hx]⟩

/-- **Definition (11).**  In the quotient field of `Λ_ℚ`, the symmetric function `H_P = HP P`
is obtained from `Q_P` by substituting each `p_r` by `p₂ʳ p_{2r} / p₄ʳ` and multiplying by
`p₄ᴸ`, `L = 2md + 2`.

In Lean `HP P` is defined without denominators (`homogenize`); this theorem shows that the
definition agrees with (11). -/
theorem definition_11 (P : MvPolynomial (Fin k) ℤ) :
    (∀ r : ℕ+, fracSubst (Undecidability.p r) =
      toFrac (Undecidability.p 2 ^ (r : ℕ) * Undecidability.p (2 * r)) /
        toFrac (Undecidability.p 4) ^ (r : ℕ)) ∧
    toFrac (HP P) =
      toFrac (Undecidability.p 4) ^ (2 * (k + 2) * dBound P + 2) *
        fracSubst (QP k P (dBound P)) :=
  ⟨fun r => MvPolynomial.aeval_X _ r, HP_eq_fraction P⟩

/-- **Proposition 2.6.**  For `P ∈ ℤ[Y₁, …, Y_k]`, with `m = k + 2`, `d = max{1, deg P}` and
`L = 2md + 2`: `H_P ∈ ℚ[p₂, p₄, …, p_{4m+2}]` is a homogeneous even symmetric function of degree
`4L = 8(k+2)d + 8`, and

(a) if `P` has no zero in `ℕ₀ᵏ`, then `H_P^{(n)}(x) ≥ (1/4) p₄(x)ᴸ > 0` for all `0 ≠ x ∈ ℝⁿ`;

(b) if `P` has a zero in `ℕ₀ᵏ`, then `H_P^{(n)}(x) = -(1/4) p₄(x)ᴸ < 0` for some `0 ≠ x ∈ ℝⁿ`.

Thus `H_P` is any-dimensional psd iff `P` has no zero in `ℕ₀ᵏ`.

That `H_P` is "computable by finite rational arithmetic from `P`" is not a formal statement
here; it is visible from the definition of `HP`. -/
theorem proposition_2_6 (P : MvPolynomial (Fin k) ℤ) :
    HP P ∈ MvPolynomial.supported ℚ {r : ℕ+ | Even (r : ℕ) ∧ (r : ℕ) ≤ 4 * (k + 2) + 2} ∧
    WHomogeneousℚ (HP P) (8 * (k + 2) * dBound P + 8) ∧
    (¬ HasNatZero P → ∀ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 →
      1 / 4 * tuplePower x 4 ^ (2 * (k + 2) * dBound P + 2) ≤ evalTruncℚ (HP P) x ∧
        0 < 1 / 4 * tuplePower x 4 ^ (2 * (k + 2) * dBound P + 2)) ∧
    (HasNatZero P → ∃ (n : ℕ) (x : Fin n → ℝ), x ≠ 0 ∧
      evalTruncℚ (HP P) x = -(1 / 4) * tuplePower x 4 ^ (2 * (k + 2) * dBound P + 2) ∧
        -(1 / 4) * tuplePower x 4 ^ (2 * (k + 2) * dBound P + 2) < 0) ∧
    (AnyDimPSDℚ (HP P) ↔ ¬ HasNatZero P) :=
  Undecidability.proposition_2_6 P

/-- **Theorem 2.2, the reduction.**  For every `P ∈ ℤ[Y₁, …, Y_k]`, the truncation of the
rational symmetric function `H_P` to `n` variables is nonnegative on `ℚⁿ` for all `n ∈ ℕ` if and
only if `P` has no zero in `ℕ₀ᵏ`.

Here `f^{(n)}(x) ∈ ℚ` for `x ∈ ℚⁿ` is obtained by substituting `p_r ↦ x₁ʳ + ⋯ + xₙʳ`.

The paper's Theorem 2.2 states that the decision problem "is `f^{(n)} ≥ 0` on `ℚⁿ` for all `n`?"
is undecidable.  What is formalized is this many-one reduction from the solvability of
Diophantine equations in `ℕ₀ᵏ`; the notion of decidability and the theorem of Davis, Putnam,
Robinson and Matiyasevich (Remark 2.1) are not formalized. -/
theorem theorem_2_2 (P : MvPolynomial (Fin k) ℤ) :
    (∀ n : ℕ, 0 < n → ∀ x : Fin n → ℚ,
      0 ≤ MvPolynomial.aeval (fun r : ℕ+ => ∑ i, x i ^ (r : ℕ)) (HP P)) ↔ ¬ HasNatZero P :=
  (nonnegOnRat_iff_pos (HP P)).symm.trans (Undecidability.theorem_2_2 P)

/-- **Theorem 2.2, the question over `ℝ`.**  "Since each truncation `f^{(n)}` is a polynomial and
thus continuous, the question in Theorem 2.2 is equivalent to asking whether `f` is
any-dimensional psd." -/
theorem theorem_2_2_real (f : Λℚ) :
    ((∀ n : ℕ, 0 < n → ∀ x : Fin n → ℚ,
      0 ≤ MvPolynomial.aeval (fun r : ℕ+ => ∑ i, x i ^ (r : ℕ)) f) ↔ AnyDimPSD (toΛ f)) :=
  (nonnegOnRat_iff_pos f).symm.trans ((nonnegOnRat_iff f).trans (anyDimPSDℚ_iff f))

/-- **Theorem 2.2, second part.**  For nine unknowns (`k = 9`, `m = 11`, `4m + 2 = 46`) the
instances `H_P` are homogeneous even symmetric functions in `ℚ[p₂, p₄, …, p₄₆]`.

Jones' theorem (undecidability for nine unknowns, Remark 2.1) is not formalized. -/
theorem theorem_2_2_nine (P : MvPolynomial (Fin 9) ℤ) :
    HP P ∈ MvPolynomial.supported ℚ {r : ℕ+ | Even (r : ℕ) ∧ (r : ℕ) ≤ 46} ∧
    WHomogeneousℚ (HP P) (88 * dBound P + 8) ∧
    ((∀ n : ℕ, 0 < n → ∀ x : Fin n → ℚ,
      0 ≤ MvPolynomial.aeval (fun r : ℕ+ => ∑ i, x i ^ (r : ℕ)) (HP P)) ↔ ¬ HasNatZero P) :=
  ⟨(Undecidability.theorem_2_2_nine P).1, (Undecidability.theorem_2_2_nine P).2.1,
    theorem_2_2 P⟩

end Undecidability

/-! ## Section 3: a counterexample to Hilbert's 17th problem for symmetric functions -/

section Counterexample

/-- **The octic `F`.** -/
theorem definition_F :
    F = 4 * p 1 ^ 2 * (p 3 - 4 * p 1 ^ 3) ^ 2 +
      9 * p 2 * (p 6 - 8 * p 1 ^ 2 * p 4 + 16 * p 1 ^ 4 * p 2) - 16 * p 1 ^ 8 :=
  rfl

/-- **Theorem 3.1.**  The homogeneous symmetric function
`F = 4p₁²(p₃ - 4p₁³)² + 9p₂(p₆ - 8p₁²p₄ + 16p₁⁴p₂) - 16p₁⁸` of degree `8` satisfies:

(1) `F` is any-dimensional positive definite, i.e. `F^{(n)}(x) > 0` for every
`x ∈ ⋃ₙ (ℝⁿ ∖ {0})`;

(2) there is no nonzero formal power series `Q ∈ ℝ[[X₁, X₂, …]]` of bounded degree such that
`Q^{(n)}` and `Q^{(n)} F^{(n)}` are sums of squares for every `n ∈ ℕ`.

**This theorem does not depend on Theorem 3.2.**  Part (2) is proved with the elementary degree
bound `corollary_3_4_elementary` below instead of Corollary 3.4. -/
theorem theorem_3_1 :
    WHomogeneous F 8 ∧
    (∀ n : ℕ, 0 < n → ∀ x : Fin n → ℝ, x ≠ 0 → 0 < MvPolynomial.eval x (trunc n F)) ∧
    ¬ ∃ (Q : FSeries) (D : ℕ), Q ≠ 0 ∧ ∀ n : ℕ, 0 < n →
      ∃ a : Poly n, IsTrunc Q n a ∧ a.totalDegree ≤ D ∧ IsSOS a ∧ IsSOS (a * trunc n F) :=
  ⟨F_wHomogeneous, (anyDimPD_iff F).mp theorem_3_1_1, theorem_3_1_2⟩

/-- **Theorem 3.1, "in particular".**  There is no symmetric function `0 ≠ Q ∈ SΣ` such that
`Q F ∈ SΣ`. -/
theorem theorem_3_1_in_particular : ¬ ∃ Q : Λ, Q ≠ 0 ∧ AnyDimSOS Q ∧ AnyDimSOS (Q * F) :=
  no_anyDimSOS_multiplier

/-- **Inequality (12).**  For `σ(t) = 0` if `|t| ≤ 2/3` and `σ(t) = sgn t` otherwise:
`|t³ - σ(t)| ≤ 3 t² |t² - 1|` for all `t ∈ ℝ`. -/
theorem inequality_12 (t : ℝ) :
    sigma t = (if |t| ≤ 2 / 3 then 0 else if 0 < t then 1 else -1) ∧
    |t ^ 3 - (sigma t : ℝ)| ≤ 3 * t ^ 2 * |t ^ 2 - 1| :=
  ⟨rfl, abs_cube_sub_sigma_le t⟩

/-- **Inequality (13).**  With `k = ∑ᵢ σ(xᵢ) ∈ ℤ` and
`D = p₂(x)(p₆(x) - 2p₄(x) + p₂(x)) = p₂(x) ∑ᵢ xᵢ²(xᵢ² - 1)² ≥ 0`:
`|p₃(x) - k| ≤ 3√D`, stated in the squared form `(p₃(x) - k)² ≤ 9D`. -/
theorem inequality_13 {n : ℕ} (x : Fin n → ℝ) :
    Dval x = tuplePower x 2 * (tuplePower x 6 - 2 * tuplePower x 4 + tuplePower x 2) ∧
    Dval x = (∑ i, x i ^ 2) * ∑ i, x i ^ 2 * (x i ^ 2 - 1) ^ 2 ∧
    0 ≤ Dval x ∧
    (tuplePower x 3 - ((∑ i, sigma (x i) : ℤ) : ℝ)) ^ 2 ≤ 9 * Dval x :=
  ⟨rfl, Dval_eq x, Dval_nonneg x, sq_p3_sub_kInt_le x⟩

/-- **Remark after the proof of Theorem 3.1 (1).**  `F ≥ 16 p₁⁸`, and `F = 9 p₂ p₆` if
`p₁ = 0`. -/
theorem theorem_3_1_1_addendum {n : ℕ} (x : Fin n → ℝ) :
    16 * tuplePower x 1 ^ 8 ≤ evalTrunc F x ∧
    (tuplePower x 1 = 0 → evalTrunc F x = 9 * tuplePower x 2 * tuplePower x 6) :=
  ⟨sixteen_mul_le_evalTrunc_F x, fun h => evalTrunc_F_of_p1_eq_zero h⟩

/-- **Theorem 3.2** (Blekherman; [19, Theorem 2.3] in the paper).  Let `Q : {0,1}ⁿ → ℝ_{≥0}` be
a symmetric nonnegative Boolean function and let `q ∈ ℝ[T]` be the unique polynomial of degree at
most `n` with `Q(x) = q(x₁ + ⋯ + xₙ)` on `{0,1}ⁿ`.  If `Q` coincides on `{0,1}ⁿ` with a sum of
squares of `n`-variate polynomials of degree `d ≤ n/2`, then
`q(T) = ∑_{k=0}^{d} σ_{d-k}(T) ∏_{i=0}^{k-1} (T - i)(n - T - i)` with sums of squares `σ_k ∈ ℝ[T]`
of degree `deg σ_k ≤ 2k`.

**NOT PROVED.**  This statement is taken from the literature, as in the paper; its proof in
`AnyDim.theorem_3_2` is `sorry`.

Formulation: `Q` is the function `x ↦ ∑ⱼ gⱼ(x)²` with `deg gⱼ ≤ d`; the hypothesis `hQ` says that
it has the form `q(∑ xᵢ)` on the cube (so it is symmetric and nonnegative), and `q` is determined
by `hq` and `hQ`. -/
theorem theorem_3_2 {n d : ℕ} (hd : 2 * d ≤ n) {r : ℕ} (g : Fin r → Poly n)
    (hg : ∀ j, (g j).totalDegree ≤ d) (q : Polynomial ℝ) (hq : q.natDegree ≤ n)
    (hQ : ∀ x : Fin n → ℝ, (∀ i, x i = 0 ∨ x i = 1) →
      ∑ j, (MvPolynomial.eval x (g j)) ^ 2 = q.eval (∑ i, x i)) :
    ∃ σ : ℕ → Polynomial ℝ, (∀ k, IsSOS (σ k) ∧ (σ k).natDegree ≤ 2 * k) ∧
      q = ∑ k ∈ Finset.range (d + 1), σ (d - k) *
        ∏ i ∈ Finset.range k,
          ((Polynomial.X - Polynomial.C (i : ℝ)) *
            (Polynomial.C (n : ℝ) - Polynomial.X - Polynomial.C (i : ℝ))) :=
  AnyDim.theorem_3_2 hd g hg q hq hQ

/-- **Corollary 3.3.**  Let `Q ∈ ℝ[X₁, …, Xₙ]` be a sum of squares with `deg Q ≤ n`, and let
`q ∈ ℝ[T]` satisfy `deg q ≤ n` and `Q(x) = q(∑ xᵢ)` for all `x ∈ {-1, 1}ⁿ`.  Then `q(1/2) ≥ 0`.

Depends on the unproved Theorem 3.2. -/
theorem corollary_3_3 {n : ℕ} {Q : Poly n} (hQ : IsSOS Q) (hdeg : Q.totalDegree ≤ n)
    (q : Polynomial ℝ) (hq : q.natDegree ≤ n)
    (h : ∀ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      MvPolynomial.eval x Q = q.eval (∑ i, x i)) :
    0 ≤ q.eval (1 / 2) :=
  AnyDim.corollary_3_3 hQ hdeg q hq h

/-- **Corollary 3.4.**  Let `0 ≠ Q ∈ ℝ[X₁, …, Xₙ]` be a sos multiplier of `F^{(n)}`, i.e. `Q` and
`Q F^{(n)}` are sums of squares.  Then `deg Q > (n - 8)/2`.

Depends on the unproved Theorem 3.2. -/
theorem corollary_3_4 {n : ℕ} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) : ((n : ℝ) - 8) / 2 < (Q.totalDegree : ℝ) :=
  corollary_3_4' hQ0 hQ hQF

/-- **Remark 3.5.**  For the homomorphism `φ : Λ → ℝ[T] ⊆ ℝ(T)` with `p_r ↦ T` for even `r` and
`p_r ↦ 1/2` for odd `r`: `φ(F) = -1/16`.

Only this computation is formalized, not the discussion of orderings and the real spectrum. -/
theorem remark_3_5 :
    (∀ r : ℕ+, phi (p r) = if (r : ℕ) % 2 = 0 then Polynomial.X else Polynomial.C (1 / 2)) ∧
    phi F = Polynomial.C (-(1 / 16 : ℝ)) :=
  ⟨fun r => MvPolynomial.aeval_X _ r, AnyDim.remark_3_5⟩

/-- **Corollary 3.6.**  There exist symmetric functions that are any-dimensional positive
definite which are not sums of squares in the quotient field of `Λ` (namely `F`).  Moreover, no
any-dimensional Krivine--Stengle Positivstellensatz exists: it is not true that for every
`f ∈ SP` there are `q, g ∈ SΣ` and `k ∈ ℕ₀` with `q f = f^{2k} + g`.

The second statement is proved without assuming `q ≠ 0`, which makes it stronger. -/
theorem corollary_3_6 :
    (AnyDimPD F ∧ ¬ IsSOS (algebraMap Λ (FractionRing Λ) F)) ∧
    ¬ ∀ f : Λ, AnyDimPSD f →
      ∃ (q g : Λ) (k : ℕ), AnyDimSOS q ∧ AnyDimSOS g ∧ q * f = f ^ (2 * k) + g :=
  ⟨⟨theorem_3_1_1, F_not_sos_in_fractionRing⟩, corollary_3_6_b⟩

/-- **Remark 3.7.**  At `x = (-1, …, -1, 1, …, 1) ∈ ℝ²ⁿ` with `n` many `-1`'s and `1`'s we have
`F^{(2n)}(x) = 36n²`; the point `x/√(2n)` lies on the unit sphere and `F` takes the value
`9/(4n²)` there.  So the minima of `F^{(n)}` on the unit sphere are not bounded away from zero
uniformly in `n`. -/
theorem remark_3_7 {n : ℕ} (hn : 0 < n) :
    balancedPoint n = Fin.append (fun _ : Fin n => (-1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) ∧
    evalTrunc F (balancedPoint n) = 36 * (n : ℝ) ^ 2 ∧
    tuplePower (fun i => balancedPoint n i / Real.sqrt (2 * n)) 2 = 1 ∧
    evalTrunc F (fun i => balancedPoint n i / Real.sqrt (2 * n)) = 9 / (4 * (n : ℝ) ^ 2) :=
  ⟨rfl, AnyDim.remark_3_7 n, (remark_3_7_sphere hn).1, (remark_3_7_sphere hn).2⟩

/-- **Proposition 3.9.**  Let `f ∈ SP`.  Suppose that there exist `d ∈ ℕ` and
`0 ≠ q ∈ ℝ[[X₁, X₂, …]]` with `deg q^{(n)} ≤ 2d` such that both polynomials `q^{(n)}` and
`q^{(n)} f^{(n)}` are sums of squares for every `n ∈ ℕ`.  Then there exists `h ∈ SΣ ∖ {0}` with
`h f ∈ SΣ`.

The hypothesis `f ∈ SP` is not used in the proof. -/
theorem proposition_3_9 (f : Λ) (hf : AnyDimPSD f) (d : ℕ) (q : FSeries) (hq : q ≠ 0)
    (h : ∀ n : ℕ, 0 < n → ∃ a : Poly n, IsTrunc q n a ∧ a.totalDegree ≤ 2 * d ∧ IsSOS a ∧
      IsSOS (a * trunc n f)) :
    ∃ H : Λ, H ≠ 0 ∧ AnyDimSOS H ∧ AnyDimSOS (H * f) :=
  AnyDim.proposition_3_9 f hf d q hq h

end Counterexample

/-! ## Not in the paper: an elementary replacement for Corollaries 3.3 and 3.4

These two statements make Theorem 3.1 independent of Theorem 3.2.  They are proved in
`AnyDim/Counterexample/Elementary/` with an explicit pseudo-expectation on the hypercube. -/

section Elementary

/-- **Corollary 3.3, elementary version** (not in the paper).  The conclusion of Corollary 3.3
under the stronger hypothesis `deg Q, deg q ≤ 2d` with `1 ≤ d` and `4d ≤ n`. -/
theorem corollary_3_3_elementary {n d : ℕ} (hd : 1 ≤ d) (hnd : 4 * d ≤ n) {Q : Poly n}
    (hQ : IsSOS Q) (hdeg : Q.totalDegree ≤ 2 * d) (q : Polynomial ℝ) (hq : q.natDegree ≤ 2 * d)
    (h : ∀ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      MvPolynomial.eval x Q = q.eval (∑ i, x i)) :
    0 ≤ q.eval (1 / 2) :=
  Elementary.corollary_3_3_elementary hd hnd hQ hdeg q hq h

/-- **Corollary 3.4, elementary version** (not in the paper).  A nonzero sos multiplier `Q` of
`F^{(n)}` satisfies `deg Q > (n - 20)/3`. -/
theorem corollary_3_4_elementary {n : ℕ} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) : ((n : ℝ) - 20) / 3 < (Q.totalDegree : ℝ) :=
  multiplier_degree_linear hQ0 hQ hQF

end Elementary

/-! ## Not formalized

* **Decidability.**  The notions "decision problem" and "undecidable", the theorem of Davis,
  Putnam, Robinson and Matiyasevich and the theorem of Jones (Remark 2.1) are not formalized.
  Theorem 2.2 is formalized as the reduction `P ↦ H_P` (`theorem_2_2`, `theorem_2_2_nine`); that
  this map is computable is visible from its definition but is not a formal statement.
* **The proof of Theorem 3.2** (Blekherman).
* The consequences of Theorem 2.2 for the Vandermonde cell `Π₂₃` and for Positivstellensätze
  mentioned after Theorem 2.2.
* In Remark 3.5, the discussion of the real spectrum; in Remark 3.7, the comparison with
  [9, Theorem 5.4]; Remark 3.8.
* **Section 4** (dimension-free trace inequalities and entanglement criteria: Theorem 4.2 and
  Proposition 4.4).
-/

/-! ## Axiom audit

Each `#guard_msgs` below makes the build fail if the listed axioms change.  All results depend
only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`, except Theorem 3.2 and
its two corollaries, which also depend on `sorryAx`. -/

/-- info: 'AnyDim.Paper.lemma_2_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lemma_2_3

/-- info: 'AnyDim.Paper.remark_2_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms remark_2_4

/-- info: 'AnyDim.Paper.definition_QP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms definition_QP

/-- info: 'AnyDim.Paper.lemma_2_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lemma_2_5

/-- info: 'AnyDim.Paper.definition_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms definition_11

/--
info: 'AnyDim.Paper.proposition_2_6' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms proposition_2_6

/-- info: 'AnyDim.Paper.theorem_2_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms theorem_2_2

/--
info: 'AnyDim.Paper.theorem_2_2_real' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms theorem_2_2_real

/--
info: 'AnyDim.Paper.theorem_2_2_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms theorem_2_2_nine

/-- info: 'AnyDim.Paper.theorem_3_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms theorem_3_1

/--
info: 'AnyDim.Paper.theorem_3_1_in_particular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms theorem_3_1_in_particular

/-- info: 'AnyDim.Paper.inequality_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inequality_12

/-- info: 'AnyDim.Paper.inequality_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inequality_13

/-- info: 'AnyDim.Paper.remark_3_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms remark_3_5

/-- info: 'AnyDim.Paper.corollary_3_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms corollary_3_6

/-- info: 'AnyDim.Paper.remark_3_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms remark_3_7

/--
info: 'AnyDim.Paper.proposition_3_9' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms proposition_3_9

/--
info: 'AnyDim.Paper.corollary_3_3_elementary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms corollary_3_3_elementary

/--
info: 'AnyDim.Paper.corollary_3_4_elementary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms corollary_3_4_elementary

/-! The following three results depend on the unproved Theorem 3.2 (`sorryAx`). -/

/--
info: 'AnyDim.Paper.theorem_3_2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms theorem_3_2

/--
info: 'AnyDim.Paper.corollary_3_3' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms corollary_3_3

/--
info: 'AnyDim.Paper.corollary_3_4' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms corollary_3_4

end AnyDim.Paper

end
