module

public import AnyDim.Counterexample.Elementary.SignedMoments
public import AnyDim.Counterexample.MultiplierDegree

/-!
# An elementary replacement for Corollary 3.3 and Corollary 3.4

This file makes Theorem 3.1 (2) independent of the unproved Theorem 3.2 (Blekherman).

* `dMk_eq_of_eval_eq`: two polynomials which agree on `{-1,1}^n` have the same class modulo
  `(X_i² - 1)` (the vanishing ideal of the sign cube).
* `corollary_3_3_elementary`: the statement of Corollary 3.3 under the stronger hypothesis
  `deg Q, deg q ≤ 2d`, `1 ≤ d`, `4d ≤ n` (instead of `deg Q, deg q ≤ n`).  The proof applies the
  pseudo-expectation `L` of `SignedMoments` to `Q ≡ q(∑ X_i)`:
  `0 ≤ L(Q) = L(q(∑ X_i)) = q(1/2)`.
* `cubeNonneg_elementary`: `CubeNonneg N D` for `2D + 4 ≤ N`.
* `corollary_3_4_elementary`: a nonzero sos multiplier `Q` of `F^{(n)}` satisfies
  `n < 3 deg Q + 20`, i.e. `deg Q > (n - 20)/3`.  This is weaker than Corollary 3.4
  (`deg Q > (n - 8)/2`) but still grows linearly in `n`, which is all that is needed for
  Theorem 3.1 (2).

All proofs in this file are complete (no `sorry`), and none of them uses `theorem_3_2`.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim.Elementary

/-- The algebra map `BoolCube n → SignCube n` sending `X_i` to `(X_i + 1) / 2`. -/
def boolToSigned (n : Nat) : AlgHom Real (BoolCube n) (SignCube n) :=
  Ideal.Quotient.liftₐ (boolIdeal n)
    (MvPolynomial.aeval fun i : Fin n => algebraMap Real (SignCube n) (1 / 2) * (yGen n i + 1)) (by
      have hle : boolIdeal n ≤ RingHom.ker (MvPolynomial.aeval
          fun i : Fin n => algebraMap Real (SignCube n) (1 / 2) * (yGen n i + 1)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨i, rfl⟩
        have hy := yGen_sq n i
        have ht : 2 * algebraMap Real (SignCube n) (1 / 2) = 1 := by
          rw [← map_ofNat (algebraMap Real (SignCube n)) 2, ← map_mul]
          norm_num
        simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, MvPolynomial.aeval_X]
        linear_combination algebraMap Real (SignCube n) (1 / 2) ^ 2 * hy +
          (yGen n i + 1) * algebraMap Real (SignCube n) (1 / 2) * ht
      exact fun a ha => hle ha)

/-- `boolToSigned` is a left inverse of `signedToBool`. -/
theorem boolToSigned_comp_signedToBool (n : Nat) :
    (boolToSigned n).comp (signedToBool n) = AlgHom.id Real (SignCube n) := by
  refine Ideal.Quotient.algHom_ext Real (MvPolynomial.algHom_ext fun i => ?_)
  have h1 : (signedToBool n) (Ideal.Quotient.mkₐ Real (signedIdeal n) (MvPolynomial.X i)) =
      2 * bGen n i - 1 := signedToBool_yGen n i
  have h2 : boolToSigned n (bGen n i) = algebraMap Real (SignCube n) (1 / 2) * (yGen n i + 1) :=
    MvPolynomial.aeval_X _ i
  have ht : 2 * algebraMap Real (SignCube n) (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap Real (SignCube n)) 2, ← map_mul]
    norm_num
  simp only [AlgHom.comp_apply, h1, map_sub, map_mul, map_ofNat, h2, map_one, AlgHom.id_apply]
  change _ = yGen n i
  linear_combination (yGen n i + 1) * ht

theorem boolToSigned_signedToBool (n : Nat) (a : SignCube n) :
    boolToSigned n (signedToBool n a) = a := by
  have h := AlgHom.congr_fun (boolToSigned_comp_signedToBool n) a
  rwa [AlgHom.comp_apply, AlgHom.id_apply] at h

/-- The point of `{-1,1}^n` which is `1` on `V` and `-1` outside `V`. -/
def signPoint (n : Nat) (V : Finset (Fin n)) : Fin n → Real :=
  fun i => 2 * booleanPoint n V i - 1

theorem signPoint_mem (n : Nat) (V : Finset (Fin n)) (i : Fin n) :
    signPoint n V i = 1 ∨ signPoint n V i = -1 := by
  unfold signPoint booleanPoint
  split_ifs
  · left; norm_num
  · right; norm_num

/-- Evaluating the class of a polynomial at a Boolean point, after the change of coordinates,
is evaluating the polynomial at the corresponding sign point. -/
theorem booleanEval_signedToBool_dMk (n : Nat) (V : Finset (Fin n)) (Q : Poly n) :
    booleanEval n V (signedToBool n (dMk n Q)) = MvPolynomial.eval (signPoint n V) Q := by
  have h : ((booleanEval n V).comp (signedToBool n)).comp (dMk n) =
      MvPolynomial.aeval (signPoint n V) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 : signedToBool n (dMk n (MvPolynomial.X i)) = 2 * bGen n i - 1 :=
      signedToBool_yGen n i
    have h2 : booleanEval n V (bGen n i) = booleanPoint n V i := by
      simp [bGen, bMk, booleanEval]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, map_sub, map_mul, map_ofNat, map_one, h2,
      MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun φ : Poly n →ₐ[Real] Real => φ Q) h

/-- Two polynomials which agree on `{-1,1}^n` are congruent modulo `(X_i² - 1)`. -/
theorem dMk_eq_of_eval_eq {n : Nat} {P Q : Poly n}
    (h : ∀ x : Fin n → Real, (∀ i, x i = 1 ∨ x i = -1) →
      MvPolynomial.eval x P = MvPolynomial.eval x Q) : dMk n P = dMk n Q := by
  have hB : signedToBool n (dMk n P) = signedToBool n (dMk n Q) := by
    apply eq_of_booleanEval_eq
    intro V
    rw [booleanEval_signedToBool_dMk, booleanEval_signedToBool_dMk]
    exact h _ (signPoint_mem n V)
  have := congrArg (boolToSigned n) hB
  rwa [boolToSigned_signedToBool, boolToSigned_signedToBool] at this

/-- `q(∑ X_i)` as an element of the sign cube algebra. -/
theorem aeval_ySum_eq_dMk (n : Nat) (q : Polynomial Real) :
    Polynomial.aeval (ySum n) q =
      dMk n (Polynomial.aeval (∑ i, (MvPolynomial.X i : Poly n)) q) := by
  have hy : ySum n = dMk n (∑ i, (MvPolynomial.X i : Poly n)) := by
    rw [map_sum]
    rfl
  rw [hy, Polynomial.aeval_algHom_apply]

theorem eval_aeval_sum {n : Nat} (x : Fin n → Real) (q : Polynomial Real) :
    MvPolynomial.eval x (Polynomial.aeval (∑ i, (MvPolynomial.X i : Poly n)) q) =
      q.eval (∑ i, x i) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval x : Poly n →ₐ[Real] Real)
    (∑ i, (MvPolynomial.X i : Poly n)) q
  have hx : (MvPolynomial.aeval x : Poly n →ₐ[Real] Real) (∑ i, (MvPolynomial.X i : Poly n)) =
      ∑ i, x i := by
    simp
  rw [hx] at h
  exact h.symm

/-- **Corollary 3.3, elementary version.**  Let `1 ≤ d`, `4d ≤ n`, let `Q ∈ ℝ[X_1, …, X_n]` be a
sum of squares with `deg Q ≤ 2d`, and let `q ∈ ℝ[T]` satisfy `deg q ≤ 2d` and
`Q(x) = q(∑ x_i)` for all `x ∈ {-1,1}^n`.  Then `q(1/2) ≥ 0`.

Compared with Corollary 3.3 the degree hypothesis is `deg Q ≤ n/2` instead of `deg Q ≤ n`; in
return the proof is complete and does not use Theorem 3.2. -/
theorem corollary_3_3_elementary {n d : Nat} (hd : 1 ≤ d) (hnd : 4 * d ≤ n) {Q : Poly n}
    (hQ : IsSOS Q) (hdeg : Q.totalDegree ≤ 2 * d) (q : Polynomial Real)
    (hq : q.natDegree ≤ 2 * d)
    (h : ∀ x : Fin n → Real, (∀ i, x i = 1 ∨ x i = -1) → evalAt Q x = q.eval (∑ i, x i)) :
    0 ≤ q.eval (1 / 2) := by
  obtain ⟨L⟩ := signedPseudo_exists hd hnd
  have hpos := signed_nonneg_of_sos L Q hdeg hQ
  have heq : dMk n Q = Polynomial.aeval (ySum n) q := by
    rw [aeval_ySum_eq_dMk]
    exact dMk_eq_of_eval_eq fun x hx => by rw [eval_aeval_sum]; exact h x hx
  have hsub : (⟨dMk n Q, dMk_mem Q hdeg⟩ : DFilter n (2 * d)) =
      ⟨Polynomial.aeval (ySum n) q, ySum_poly_mem q hq⟩ := Subtype.ext heq
  rw [hsub, signed_polynomial_eval L q hq] at hpos
  exact hpos

/-- `CubeNonneg N D` holds for `2D + 4 ≤ N`, without Theorem 3.2. -/
theorem cubeNonneg_elementary {N D : Nat} (h : 2 * D + 4 ≤ N) : CubeNonneg N D := by
  intro Q q hQ hdeg hq hcube
  exact corollary_3_3_elementary (d := D / 2 + 1) (by omega) (by omega) hQ (by omega) q
    (by omega) hcube

/-- **Corollary 3.4, elementary version.**  A nonzero sos multiplier `Q` of `F^{(n)}` satisfies
`n < 3 deg Q + 20`, i.e. `deg Q > (n - 20)/3`.  The proof is the one of Corollary 3.4, with the
elementary version of Corollary 3.3; it does not depend on Theorem 3.2. -/
theorem corollary_3_4_elementary {n : Nat} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) : n < 3 * Q.totalDegree + 20 := by
  by_contra hcon
  push Not at hcon
  exact no_multiplier_of_cubeNonneg hQ0 hQ hQF le_rfl (N := n - Q.totalDegree) (by omega)
    (cubeNonneg_elementary (by omega))

end AnyDim.Elementary
end
