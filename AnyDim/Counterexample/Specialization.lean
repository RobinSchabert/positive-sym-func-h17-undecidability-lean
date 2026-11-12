module

public import AnyDim.Counterexample.Octic

/-!
# The specializations in the proof of Corollary 3.4

Source: Debus--Schabert, proof of Corollary 3.4.

Fix `N` ("cube variables" `x ∈ {-1,1}^N`) and `m` ("free variables" `z ∈ ℝ^m`).  For
`x ∈ {-1,1}^N` and `z ∈ ℝ^m` the power sums of the concatenated tuple are

  `p_k(x, z) = c_k(∑ x_i) + p_k(z)`,   `c_k(T) = N` (`k` even),  `c_k(T) = T` (`k` odd).

* `tailEval N z : Poly (N + m) →ₐ Poly N` substitutes `z` for the last `m` variables, and
  `withTail N z h = h^{(N+m)}(X_1, …, X_N, z)` (`withTail_eq_comp`).
* `univariateTail N z h ∈ ℝ[T]` is the paper's `q(T, z) = h(c_1(T) + p_1(z), c_2(T) + p_2(z), …)`.
  On the cube, `h^{(N+m)}(x, z) = q(∑ x_i, z)` (`evalAt_withTail_cube`).
* `psi N m h ∈ ℝ[Z_1, …, Z_m]` is `q(1/2, Z) = h(c_1(1/2) + p_1(Z), c_2(1/2) + p_2(Z), …)`
  (`univariateTail_eval_half`); `background N k = c_k(1/2)`.
* `psi_F_at_zero`: `f(1/2, 0) = -1/16`.
* Degree bounds: `withTail_degree`, `univariateTail_degree`.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

/-- `c_k(1/2)`: equal to `N` for even `k` and to `1/2` for odd `k`. -/
def background (N : Nat) (k : PNat) : Real :=
  if (k : Nat) % 2 = 0 then (N : Real) else 1 / 2

/-- The algebra homomorphism `h ↦ q(1/2, Z) = h(c_k(1/2) + p_k(Z))`, `Λ → ℝ[Z_1, …, Z_m]`. -/
def psi (N m : Nat) : AlgHom Real Λ (Poly m) :=
  MvPolynomial.aeval (fun k : PNat =>
    MvPolynomial.C (background N k) + powerSum m (k : Nat))

/-- Specialize the last `m` coordinates to `z`, retaining `N` polynomial variables. -/
def tailEval (N : Nat) {m : Nat} (z : Fin m → Real) :
    AlgHom Real (Poly (N + m)) (Poly N) :=
  MvPolynomial.aeval
    (Fin.addCases (fun i : Fin N => (MvPolynomial.X i : Poly N))
      (fun j : Fin m => (MvPolynomial.C (z j) : Poly N)))

/-- `h ↦ h^{(N+m)}(X_1, …, X_N, z)`. -/
def withTail (N : Nat) {m : Nat} (z : Fin m → Real) : AlgHom Real Λ (Poly N) :=
  MvPolynomial.aeval (fun k : PNat =>
    powerSum N (k : Nat) + MvPolynomial.C (tuplePower z (k : Nat)))

/-- If every generator image has total degree at most its index, then an evaluation
homomorphism `Λ → MvPolynomial σ ℝ` sends symmetric functions of degree at most `Dg` to
polynomials of total degree at most `Dg`. -/
theorem totalDegree_aeval_le_of_wDegLE {σ : Type*} (g : PNat → MvPolynomial σ Real)
    (hg : ∀ k, (g k).totalDegree ≤ (k : Nat)) {h : Λ} {Dg : Nat} (hh : WDegLE h Dg) :
    (MvPolynomial.aeval g h).totalDegree ≤ Dg := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine MvPolynomial.totalDegree_finsetSum_le fun e he => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans (le_trans ?_ (hh e he))
  rw [monomialWeight, Finsupp.sum]
  refine Finset.sum_le_sum fun k _ => (MvPolynomial.totalDegree_pow _ _).trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (hg k)

/-- If every generator image has degree at most its index, then an evaluation homomorphism
`Λ → ℝ[T]` sends symmetric functions of degree at most `Dg` to polynomials of degree at most
`Dg`. -/
theorem natDegree_aeval_le_of_wDegLE (g : PNat → Polynomial Real)
    (hg : ∀ k, (g k).natDegree ≤ (k : Nat)) {h : Λ} {Dg : Nat} (hh : WDegLE h Dg) :
    (MvPolynomial.aeval g h).natDegree ≤ Dg := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he => ?_
  rw [Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans (le_trans ?_ (hh e he))
  rw [monomialWeight, Finsupp.sum]
  refine Finset.sum_le_sum fun k _ => Polynomial.natDegree_pow_le.trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (hg k)

theorem totalDegree_powerSum_le (n k : Nat) : (powerSum n k).totalDegree ≤ k := by
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  exact (MvPolynomial.totalDegree_pow _ _).trans (by
    rw [MvPolynomial.totalDegree_X, mul_one])

/-- The truncation `h^{(n)}` has degree at most `deg h`. -/
theorem totalDegree_trunc_le {n : Nat} {h : Λ} {Dg : Nat} (hh : WDegLE h Dg) :
    (trunc n h).totalDegree ≤ Dg :=
  totalDegree_aeval_le_of_wDegLE _ (fun k => totalDegree_powerSum_le n k) hh

theorem tailEval_powerSum (N : Nat) {m : Nat} (z : Fin m → Real) (k : Nat) :
    tailEval N z (powerSum (N + m) k) =
      powerSum N k + MvPolynomial.C (tuplePower z k) := by
  simp only [tailEval, powerSum, tuplePower, Fin.sum_univ_add, map_add, map_sum, map_pow,
    MvPolynomial.aeval_X, Fin.addCases_left, Fin.addCases_right]

/-- `withTail N z h` is the truncation `h^{(N+m)}` with the last `m` variables specialized to
`z`. -/
theorem withTail_eq_comp (N : Nat) {m : Nat} (z : Fin m → Real) :
    withTail N z = (tailEval N z).comp (trunc (N + m)) := by
  refine MvPolynomial.algHom_ext fun k => ?_
  rw [AlgHom.comp_apply, withTail, trunc, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    tailEval_powerSum]

theorem withTail_apply (N : Nat) {m : Nat} (z : Fin m → Real) (h : Λ) :
    withTail N z h = tailEval N z (trunc (N + m) h) := by
  rw [withTail_eq_comp, AlgHom.comp_apply]

/-- Specializing variables of a sum of squares gives a sum of squares. -/
theorem tailEval_isSOS {N m : Nat} {a : Poly (N + m)} (ha : IsSOS a) (z : Fin m → Real) :
    IsSOS (tailEval N z a) :=
  isSOS_map (tailEval N z).toRingHom ha

theorem withTail_degree {N m Dg : Nat} (z : Fin m → Real) {h : Λ}
    (hh : WDegLE h Dg) : (withTail N z h).totalDegree ≤ Dg := by
  refine totalDegree_aeval_le_of_wDegLE _ (fun k => ?_) hh
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (totalDegree_powerSum_le N k) ?_)
  rw [MvPolynomial.totalDegree_C]
  exact Nat.zero_le _

/-- The univariate polynomial `q(T, z) = h(c_1(T) + p_1(z), c_2(T) + p_2(z), …)` of the proof of
Corollary 3.4, where `c_k(T) = N` for even `k` and `c_k(T) = T` for odd `k`. -/
def univariateTail (N : Nat) {m : Nat} (z : Fin m → Real) :
    AlgHom Real Λ (Polynomial Real) :=
  MvPolynomial.aeval (fun k : PNat =>
    Polynomial.C (tuplePower z (k : Nat)) +
      if (k : Nat) % 2 = 0 then Polynomial.C (N : Real) else Polynomial.X)

/-- On the sign cube: `p_k(x) = N` for even `k` and `p_k(x) = ∑ x_i` for odd `k`. -/
theorem tuplePower_cube {N : Nat} {x : Fin N → Real} (hx : ∀ i, x i = 1 ∨ x i = -1) (k : Nat) :
    tuplePower x k = if k % 2 = 0 then (N : Real) else ∑ i, x i := by
  unfold tuplePower
  split_ifs with hk
  · obtain ⟨j, rfl⟩ : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk
    have h1 : ∀ i, x i ^ (2 * j) = 1 := by
      intro i
      rcases hx i with h | h <;> rw [h] <;> simp
    simp [h1]
  · have hk1 : k = 2 * (k / 2) + 1 := by omega
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk1]
    rcases hx i with h | h <;> rw [h] <;> simp [pow_succ]

/-- For `x ∈ {-1,1}^N` and `z ∈ ℝ^m`: `h^{(N+m)}(x, z) = q(∑ x_i, z)`. -/
theorem evalAt_withTail_cube (N : Nat) {m : Nat} (z : Fin m → Real) (h : Λ) {x : Fin N → Real}
    (hx : ∀ i, x i = 1 ∨ x i = -1) :
    evalAt (withTail N z h) x = Polynomial.eval (∑ i, x i) (univariateTail N z h) := by
  have hom : (MvPolynomial.aeval x).comp (withTail N z) =
      (Polynomial.aeval (∑ i, x i)).comp (univariateTail N z) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, withTail, univariateTail, MvPolynomial.aeval_X,
      MvPolynomial.aeval_X, map_add, map_add, MvPolynomial.algHom_C, Polynomial.aeval_C]
    have hp : MvPolynomial.aeval x (powerSum N (k : Nat)) = tuplePower x k := by
      simp only [powerSum, tuplePower, map_sum, map_pow, MvPolynomial.aeval_X]
    rw [hp, tuplePower_cube hx]
    split_ifs
    · rw [Polynomial.aeval_C, add_comm]; rfl
    · rw [Polynomial.aeval_X, add_comm]
  exact congrArg (fun φ : Λ →ₐ[Real] Real => φ h) hom

theorem univariateTail_degree {N m Dg : Nat} (z : Fin m → Real) {h : Λ}
    (hh : WDegLE h Dg) : (univariateTail N z h).natDegree ≤ Dg := by
  refine natDegree_aeval_le_of_wDegLE _ (fun k => ?_) hh
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]
    exact Nat.zero_le _
  · have hk : 1 ≤ (k : Nat) := k.pos
    split_ifs
    · rw [Polynomial.natDegree_C]
      exact Nat.zero_le _
    · exact Polynomial.natDegree_X_le.trans hk

/-- `q(1/2, z) = (psi N m h)(z)`. -/
theorem univariateTail_eval_half (N : Nat) {m : Nat} (z : Fin m → Real) (h : Λ) :
    Polynomial.eval (1 / 2 : Real) (univariateTail N z h) = evalAt (psi N m h) z := by
  have hom : (Polynomial.aeval (1 / 2 : Real)).comp (univariateTail N z) =
      (MvPolynomial.aeval z).comp (psi N m) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, univariateTail, psi, MvPolynomial.aeval_X,
      MvPolynomial.aeval_X, map_add, map_add, Polynomial.aeval_C, MvPolynomial.algHom_C]
    have hp : MvPolynomial.aeval z (powerSum m (k : Nat)) = tuplePower z k := by
      simp only [powerSum, tuplePower, map_sum, map_pow, MvPolynomial.aeval_X]
    rw [hp, background]
    split_ifs <;> simp [add_comm]
  have key : Polynomial.aeval (1 / 2 : Real) (univariateTail N z h) =
      MvPolynomial.aeval z (psi N m h) := by
    simpa only [AlgHom.comp_apply] using congrArg (fun φ : Λ →ₐ[Real] Real => φ h) hom
  exact key

theorem evalAt_psi_p (N : Nat) {m : Nat} (z : Fin m → Real) (k : PNat) :
    evalAt (psi N m (p k)) z = background N k + tuplePower z (k : Nat) := by
  rw [psi, p, MvPolynomial.aeval_X, evalAt, map_add, MvPolynomial.eval_C]
  exact congrArg _ (eval_powerSum z (k : Nat))

/-- `f(1/2, 0) = -1/16`: at `z = 0` the arguments are `c_k(1/2) = N` for `k ∈ {2, 4, 6}` and
`1/2` for `k ∈ {1, 3}`, so
`4 (1/2)² (1/2 - 4 (1/2)³)² + 9 N (N - 8 (1/2)² N + 16 (1/2)⁴ N) - 16 (1/2)⁸ = -1/16`. -/
theorem psi_F_at_zero (N m : Nat) :
    evalAt (psi N m F) (fun _ => 0) = -(1 / 16 : Real) := by
  have key : ∀ k : PNat, MvPolynomial.eval (fun _ : Fin m => (0 : Real)) (psi N m (p k)) =
      background N k := by
    intro k
    have hk : tuplePower (fun _ : Fin m => (0 : Real)) (k : Nat) = 0 := by
      simp [tuplePower, zero_pow k.ne_zero]
    have hpk := evalAt_psi_p N (fun _ : Fin m => (0 : Real)) k
    rw [hk, add_zero] at hpk
    exact hpk
  have b1 : background N 1 = 1 / 2 := by simp [background]
  have b2 : background N 2 = N := by simp [background]
  have b3 : background N 3 = 1 / 2 := by simp [background]
  have b4 : background N 4 = N := by simp [background]
  have b6 : background N 6 = N := by simp [background]
  simp only [evalAt, F, Fexpr, map_add, map_sub, map_mul, map_pow, map_ofNat, key, b1, b2, b3,
    b4, b6]
  ring

end AnyDim
end
