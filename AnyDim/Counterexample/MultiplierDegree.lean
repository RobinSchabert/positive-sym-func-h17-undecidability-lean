module

public import AnyDim.Counterexample.Symmetric
public import AnyDim.Counterexample.Blekherman

/-!
# Corollary 3.4: sos multipliers of `F^{(n)}` have degree `> (n - 8)/2`

Source: Debus--Schabert, Corollary 3.4 and its proof.

The proof of Corollary 3.4 uses Corollary 3.3 only through the following property of a pair
`(N, D)`, which we call `CubeNonneg N D`:

  if `Q ∈ ℝ[X_1, …, X_N]` is a sum of squares of degree `≤ D` and `q ∈ ℝ[T]` has degree `≤ D`
  and `Q(x) = q(∑ x_i)` for all `x ∈ {-1,1}^N`, then `q(1/2) ≥ 0`.

* `cubeNonneg_of_le`: Corollary 3.3 gives `CubeNonneg N D` for `D ≤ N` (depends on the unproved
  Theorem 3.2).
* `no_multiplier_of_cubeNonneg`: the argument of the paper.  Let `0 ≠ Q` be a sos multiplier of
  `F^{(n)}` with `deg Q ≤ d`, and `n = N + d`.  After symmetrizing, `Q = Q̃(p_1, …, p_d)`.  For
  `z ∈ ℝ^d`, `Q(x, z) = q(∑ x_i, z)` and `(Q F^{(n)})(x, z) = (q f)(∑ x_i, z)` on `{-1,1}^N`, so
  `CubeNonneg N (d + 8)` yields (14): `q(1/2, z) ≥ 0` and `q(1/2, z) f(1/2, z) ≥ 0`.  As
  `f(1/2, 0) = -1/16 < 0`, the polynomial `q(1/2, z)` vanishes near `0`, hence identically,
  contradicting the algebraic independence of the `c_k(1/2) + p_k^{(d)}`.
* `corollary_3_4`: `n < 2 deg Q + 8`, i.e. `deg Q > (n - 8)/2` (depends on Theorem 3.2).

A weaker bound that does not depend on Theorem 3.2 is
`AnyDim.Elementary.corollary_3_4_elementary : n < 3 deg Q + 20`.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open MvPolynomial

/-- The conclusion of Corollary 3.3 for `N` variables and degree bound `D`: every sum of squares
`Q` of degree `≤ D` which agrees on `{-1,1}^N` with `q(∑ x_i)`, `deg q ≤ D`, has
`q(1/2) ≥ 0`. -/
def CubeNonneg (N D : ℕ) : Prop :=
  ∀ (Q : Poly N) (q : Polynomial ℝ), IsSOS Q → Q.totalDegree ≤ D → q.natDegree ≤ D →
    (∀ x : Fin N → ℝ, (∀ i, x i = 1 ∨ x i = -1) → evalAt Q x = q.eval (∑ i, x i)) →
    0 ≤ q.eval (1 / 2)

/-- Corollary 3.3 gives `CubeNonneg N D` whenever `D ≤ N`.  (Depends on Theorem 3.2.) -/
theorem cubeNonneg_of_le {N D : ℕ} (h : D ≤ N) : CubeNonneg N D :=
  fun _ q hQ hdeg hq hcube => corollary_3_3 hQ (hdeg.trans h) q (hq.trans h) hcube

/-- The core of the proof of Corollary 3.4, for a symmetric multiplier `B^{(N+m)}` given by a
symmetric function `B ∈ ℝ[p_1, …, p_m]` of degree `≤ m`. -/
theorem multiplier_core {N m : ℕ} {B : Λ} (hB0 : B ≠ 0) (hBdeg : WDegLE B m)
    (hB : IsSOS (trunc (N + m) B)) (hBF : IsSOS (trunc (N + m) (B * F)))
    (hcube : CubeNonneg N (m + 8)) : False := by
  have hBFdeg : WDegLE (B * F) (m + 8) := hBdeg.mul F_wDegLE
  -- (14): `q(1/2, z) ≥ 0` …
  have hG : ∀ z : Fin m → ℝ, 0 ≤ evalAt (psi N m B) z := by
    intro z
    rw [← univariateTail_eval_half]
    refine hcube (withTail N z B) (univariateTail N z B) ?_ ?_ ?_
      (fun x hx => evalAt_withTail_cube N z B hx)
    · rw [withTail_apply]
      exact tailEval_isSOS hB z
    · exact (withTail_degree z hBdeg).trans (Nat.le_add_right _ _)
    · exact (univariateTail_degree z hBdeg).trans (Nat.le_add_right _ _)
  -- … and `q(1/2, z) f(1/2, z) ≥ 0`
  have hGF : ∀ z : Fin m → ℝ, 0 ≤ evalAt (psi N m B * psi N m F) z := by
    intro z
    rw [← map_mul, ← univariateTail_eval_half]
    refine hcube (withTail N z (B * F)) (univariateTail N z (B * F)) ?_ ?_ ?_
      (fun x hx => evalAt_withTail_cube N z (B * F) hx)
    · rw [withTail_apply]
      exact tailEval_isSOS hBF z
    · exact withTail_degree z hBFdeg
    · exact univariateTail_degree z hBFdeg
  -- `f(1/2, 0) = -1/16 < 0`
  have hJ0 : evalAt (psi N m F) (fun _ => 0) < 0 := by
    rw [psi_F_at_zero]
    norm_num
  -- hence `q(1/2, z)` is the zero polynomial, contradicting algebraic independence
  have hzero : psi N m B = 0 := polynomial_zero_of_nonneg_product _ _ hG hGF hJ0
  exact psi_ne_zero N B (usesFirst_of_wDegLE hBdeg) hB0 hzero

/-- The proof of Corollary 3.4, relative to the conclusion of Corollary 3.3: a nonzero sos
multiplier `Q` of `F^{(n)}` with `deg Q ≤ d` cannot exist if `n = N + d` and
`CubeNonneg N (d + 8)` holds. -/
theorem no_multiplier_of_cubeNonneg {n : ℕ} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) {d N : ℕ} (hd : Q.totalDegree ≤ d) (hn : n = N + d)
    (hcube : CubeNonneg N (d + 8)) : False := by
  -- Reynolds operator and the fundamental theorem of symmetric polynomials
  obtain ⟨B, hBdeg, hB⟩ := exists_trunc_eq_of_totalDegree_le (symmetrize_isSymmetric Q)
    ((totalDegree_symmetrize_le Q).trans hd)
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [map_zero] at hB
    exact symmetrize_ne_zero hQ hQ0 hB.symm
  have h1 : IsSOS (trunc n B) := by
    rw [hB]
    exact symmetrize_isSOS hQ
  have h2 : IsSOS (trunc n (B * F)) := by
    rw [map_mul, hB, ← symmetrize_mul_trunc]
    exact symmetrize_isSOS hQF
  subst hn
  exact multiplier_core hB0 hBdeg h1 h2 hcube

/-- **Corollary 3.4.**  Let `0 ≠ Q ∈ ℝ[X_1, …, X_n]` be a sos multiplier of `F^{(n)}` (i.e. `Q`
and `Q F^{(n)}` are sums of squares).  Then `deg Q > (n - 8)/2`, i.e. `n < 2 deg Q + 8`.

This is the paper's statement and proof; it depends on the unproved Theorem 3.2 via
Corollary 3.3. -/
theorem corollary_3_4 {n : ℕ} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) : n < 2 * Q.totalDegree + 8 := by
  by_contra hcon
  push Not at hcon
  exact no_multiplier_of_cubeNonneg hQ0 hQ hQF le_rfl (N := n - Q.totalDegree) (by omega)
    (cubeNonneg_of_le (by omega))

/-- Corollary 3.4 in the form `deg Q > (n - 8)/2`. -/
theorem corollary_3_4' {n : ℕ} {Q : Poly n} (hQ0 : Q ≠ 0) (hQ : IsSOS Q)
    (hQF : IsSOS (Q * trunc n F)) : ((n : ℝ) - 8) / 2 < (Q.totalDegree : ℝ) := by
  have h := corollary_3_4 hQ0 hQ hQF
  have h' : (n : ℝ) < 2 * (Q.totalDegree : ℝ) + 8 := by exact_mod_cast h
  linarith

end AnyDim
end
