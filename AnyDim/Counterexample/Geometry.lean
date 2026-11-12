module

public import AnyDim.Counterexample.Specialization

/-!
# Algebraic independence of the power sums and the open-set argument

Source: Debus--Schabert, end of the proof of Corollary 3.4.

* `powerSubst_injective`: the power sums `p_1^{(s)}, …, p_s^{(s)}` in `s` variables are
  algebraically independent (via the Jacobian, a Vandermonde determinant, and the inverse
  function theorem for the polynomial map `z ↦ (p_1(z), …, p_s(z))`).
* `psi_ne_zero`: so are their translates `c_k(1/2) + p_k^{(s)}`: if `0 ≠ h ∈ ℝ[p_1, …, p_s]`,
  then `psi N s h ≠ 0`.
* `trunc_ne_zero_of_usesFirst`: if `0 ≠ h ∈ ℝ[p_1, …, p_s]`, then `h^{(s)} ≠ 0`.
* `polynomial_zero_of_nonneg_product`: if `G ≥ 0` and `G · J ≥ 0` on `ℝ^m` and `J(0) < 0`, then
  `G = 0` (`J < 0` on an open neighbourhood of `0`, where `G` must vanish).

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

def lineRestriction {s : Nat} (q : Poly s) (a b : Fin s → Real) : Polynomial Real :=
  MvPolynomial.aeval (fun i : Fin s =>
    Polynomial.C (a i) + Polynomial.X * Polynomial.C (b i - a i)) q

theorem lineRestriction_eval {s : Nat} (q : Poly s) (a b : Fin s → Real) (t : Real) :
    Polynomial.eval t (lineRestriction q a b) =
      evalAt q (fun i => a i + t * (b i - a i)) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [lineRestriction, evalAt]
  | add q r hq hr => simp_all [lineRestriction, evalAt]
  | mul_X q i hq => simp_all [lineRestriction, evalAt]

theorem lineRestriction_eval_one {s : Nat} (q : Poly s) (a b : Fin s → Real) :
    Polynomial.eval 1 (lineRestriction q a b) = evalAt q b := by
  rw [lineRestriction_eval]
  congr 1
  funext i
  ring

theorem polynomial_zero_of_interval (P : Polynomial Real) (lo hi : Real)
    (hlo : lo < hi) (hzero : ∀ t ∈ Set.Ioo lo hi, Polynomial.eval t P = 0) :
    P = 0 :=
  Polynomial.eq_zero_of_infinite_isRoot P <|
    (Set.Ioo_infinite hlo).mono fun t ht => hzero t ht

theorem lineRestriction_zero_of_open {s : Nat} (q : Poly s)
    (U : Set (Fin s → Real)) (hU : IsOpen U) (a b : Fin s → Real)
    (ha : a ∈ U) (hq : ∀ z ∈ U, evalAt q z = 0) :
    lineRestriction q a b = 0 := by
  set l : Real → (Fin s → Real) := fun t i => a i + t * (b i - a i) with hl
  have hcont : Continuous l := by fun_prop
  have h0 : l 0 ∈ U := by simpa [hl] using ha
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.preimage hcont) 0 h0
  refine polynomial_zero_of_interval _ (-ε) ε (by linarith) fun t ht => ?_
  rw [lineRestriction_eval]
  refine hq _ (hball ?_)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  exact ht

theorem polynomial_zero_on_open {s : Nat} (q : Poly s)
    (U : Set (Fin s → Real)) (hU : IsOpen U) (hne : U.Nonempty)
    (hq : ∀ z ∈ U, evalAt q z = 0) : q = 0 := by
  obtain ⟨a, ha⟩ := hne
  apply MvPolynomial.funext
  intro b
  have hline := lineRestriction_zero_of_open q U hU a b ha hq
  have heval := congrArg (Polynomial.eval (1 : Real)) hline
  have hb : evalAt q b = 0 := by
    simpa only [lineRestriction_eval_one, Polynomial.eval_zero] using heval
  simpa [evalAt] using hb

def powerMap (s : Nat) (z : Fin s → Real) : Fin s → Real :=
  fun i => tuplePower z (i.val + 1)

def powerSubst (s : Nat) : AlgHom Real (Poly s) (Poly s) :=
  MvPolynomial.aeval (fun i : Fin s => powerSum s (i.val + 1))

theorem powerSubst_eval (s : Nat) (q : Poly s) (z : Fin s → Real) :
    evalAt (powerSubst s q) z = evalAt q (powerMap s z) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [powerSubst, evalAt]
  | add q r hq hr => simp_all [powerSubst, evalAt]
  | mul_X q i hq => simp_all [powerSubst, evalAt, powerMap, ← eval_powerSum]

def jacobianMatrix (s : Nat) (z : Fin s → Real) : Matrix (Fin s) (Fin s) Real :=
  fun i j => ((i.val + 1 : Nat) : Real) * z j ^ i.val

def matrixCLM {s : Nat} (M : Matrix (Fin s) (Fin s) Real) :
    ContinuousLinearMap (RingHom.id Real) (Fin s → Real) (Fin s → Real) :=
  ContinuousLinearMap.pi (fun i =>
    Finset.univ.sum (fun j : Fin s => M i j • ContinuousLinearMap.proj j))

def vandermondeProduct {s : Nat} (z : Fin s → Real) : Real :=
  Finset.univ.prod (fun i : Fin s =>
    Finset.univ.prod (fun j : Fin s => if i < j then z j - z i else 1))

theorem jacobian_determinant (s : Nat) (z : Fin s → Real) :
    Matrix.det (jacobianMatrix s z) = (s.factorial : Real) * vandermondeProduct z := by
  have hM : jacobianMatrix s z =
      Matrix.diagonal (fun i : Fin s => ((i.val + 1 : Nat) : Real)) *
        (Matrix.vandermonde z).transpose := by
    ext i j
    simp [jacobianMatrix, Matrix.diagonal_mul, Matrix.vandermonde]
  have hfact : (∏ i : Fin s, ((i.val + 1 : Nat) : Real)) = (s.factorial : Real) := by
    rw [Fin.prod_univ_eq_prod_range (fun i => ((i + 1 : Nat) : Real)) s, ← Nat.cast_prod,
      Finset.prod_range_add_one_eq_factorial]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose, Matrix.det_vandermonde,
    hfact, vandermondeProduct]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

theorem vandermondeProduct_ne_zero {s : Nat} (z : Fin s → Real)
    (hz : Function.Injective z) : vandermondeProduct z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  split_ifs with h
  · exact sub_ne_zero.mpr fun hji => (ne_of_lt h) (hz hji).symm
  · exact one_ne_zero

theorem jacobian_det_ne_zero (s : Nat) (z : Fin s → Real)
    (hz : Function.Injective z) : Matrix.det (jacobianMatrix s z) ≠ 0 := by
  rw [jacobian_determinant]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
    (vandermondeProduct_ne_zero z hz)

theorem exists_distinct_tuple (s : Nat) :
    ∃ z : Fin s → Real, Function.Injective z :=
  ⟨fun i => (i.val : Real), fun _ _ h => Fin.ext (Nat.cast_injective h)⟩

theorem matrixCLM_apply {s : Nat} (M : Matrix (Fin s) (Fin s) Real)
    (v : Fin s → Real) (i : Fin s) :
    matrixCLM M v i = Finset.univ.sum (fun j => M i j * v j) := by
  simp [matrixCLM]

theorem powerMap_coordinate_strict_derivative (s : Nat) (z : Fin s → Real)
    (i : Fin s) :
    HasStrictFDerivAt (fun x : Fin s → Real => tuplePower x (i.val + 1))
      (Finset.univ.sum (fun j : Fin s =>
        (((i.val + 1 : Nat) : Real) * z j ^ i.val) •
          (ContinuousLinearMap.proj j : (Fin s → Real) →L[Real] Real))) z := by
  unfold tuplePower
  refine HasStrictFDerivAt.fun_sum fun j _ => ?_
  convert (hasStrictFDerivAt_apply (𝕜 := Real) (F' := fun _ => Real) j z).pow (i.val + 1) using 2
  simp

theorem powerMap_strict_derivative (s : Nat) (z : Fin s → Real) :
    HasStrictFDerivAt (powerMap s) (matrixCLM (jacobianMatrix s z)) z := by
  unfold powerMap matrixCLM
  exact hasStrictFDerivAt_pi.mpr fun i => powerMap_coordinate_strict_derivative s z i

theorem matrixCLM_equiv {s : Nat} (M : Matrix (Fin s) (Fin s) Real)
    (hM : Matrix.det M ≠ 0) :
    ∃ e : ContinuousLinearEquiv (RingHom.id Real) (Fin s → Real) (Fin s → Real),
      e.toContinuousLinearMap = matrixCLM M := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (Fin s → Real) ≃ₗ[Real] (Fin s → Real) :=
    Matrix.toLin'OfInv (M := M⁻¹) (M' := M) (Matrix.nonsing_inv_mul M hu)
      (Matrix.mul_nonsing_inv M hu)
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  ext v i
  simp [e, matrixCLM_apply, Matrix.toLin'OfInv, Matrix.mulVec, dotProduct]

theorem open_image_of_strict_derivative {s : Nat}
    (f : (Fin s → Real) → (Fin s → Real)) (x : Fin s → Real)
    (e : ContinuousLinearEquiv (RingHom.id Real) (Fin s → Real) (Fin s → Real))
    (hf : HasStrictFDerivAt f e.toContinuousLinearMap x) :
    ∃ U : Set (Fin s → Real),
      IsOpen U ∧ f x ∈ U ∧ U ≤ Set.range f := by
  let H := hf.toOpenPartialHomeomorph f
  refine ⟨H.target, H.open_target, hf.image_mem_toOpenPartialHomeomorph_target, fun y hy => ?_⟩
  refine ⟨H.symm y, ?_⟩
  rw [← hf.toOpenPartialHomeomorph_coe]
  exact H.right_inv hy

theorem powerMap_open_image (s : Nat) :
    ∃ U : Set (Fin s → Real),
      IsOpen U ∧ U.Nonempty ∧ U ≤ Set.range (powerMap s) := by
  obtain ⟨z, hz⟩ := exists_distinct_tuple s
  obtain ⟨e, he⟩ := matrixCLM_equiv (jacobianMatrix s z) (jacobian_det_ne_zero s z hz)
  have hder : HasStrictFDerivAt (powerMap s) e.toContinuousLinearMap z := by
    rw [he]
    exact powerMap_strict_derivative s z
  obtain ⟨U, hU, hzU, hUr⟩ := open_image_of_strict_derivative (powerMap s) z e hder
  exact ⟨U, hU, ⟨powerMap s z, hzU⟩, hUr⟩

theorem powerSubst_kernel (s : Nat) (q : Poly s) (hq : powerSubst s q = 0) : q = 0 := by
  obtain ⟨U, hU, hne, hUr⟩ := powerMap_open_image s
  apply polynomial_zero_on_open q U hU hne
  intro u hu
  obtain ⟨z, rfl⟩ := hUr hu
  rw [← powerSubst_eval, hq]
  simp [evalAt]

theorem powerSubst_injective (s : Nat) : Function.Injective (powerSubst s) := by
  intro q r hqr
  apply sub_eq_zero.mp
  apply powerSubst_kernel s
  simp only [map_sub]
  exact sub_eq_zero.mpr hqr

def translate (s : Nat) (c : Fin s → Real) : AlgHom Real (Poly s) (Poly s) :=
  MvPolynomial.aeval (fun i : Fin s => MvPolynomial.X i + MvPolynomial.C (c i))

theorem translate_inverse_apply (s : Nat) (c : Fin s → Real) (q : Poly s) :
    translate s (fun i => -c i) (translate s c q) = q := by
  have h : (translate s fun i => -c i).comp (translate s c) = AlgHom.id Real (Poly s) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [translate, AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_C,
      AlgHom.id_apply, MvPolynomial.algebraMap_eq, map_neg]
    ring
  exact congrArg (· q) h

theorem translate_injective (s : Nat) (c : Fin s → Real) :
    Function.Injective (translate s c) := by
  intro q r hqr
  have h := congrArg (translate s (fun i => -c i)) hqr
  simpa only [translate_inverse_apply] using h

def generatorIndex {s : Nat} (i : Fin s) : PNat := ⟨i.val + 1, Nat.succ_pos i.val⟩

def embedFirst (s : Nat) : AlgHom Real (Poly s) Λ :=
  MvPolynomial.aeval (fun i : Fin s => p (generatorIndex i))

def shiftedPowerSubst (n s : Nat) : AlgHom Real (Poly s) (Poly s) :=
  (powerSubst s).comp (translate s (fun i => background n (generatorIndex i)))

theorem shiftedPowerSubst_injective (n s : Nat) :
    Function.Injective (shiftedPowerSubst n s) := by
  exact (powerSubst_injective s).comp
    (translate_injective s (fun i => background n (generatorIndex i)))

theorem finite_representation {s : Nat} (h : Λ) (hh : UsesFirst s h) :
    ∃ q : Poly s, embedFirst s q = h := by
  have hinj : Function.Injective (generatorIndex (s := s)) := by
    intro i j hij
    have := congrArg PNat.val hij
    simp only [generatorIndex, PNat.mk_coe] at this
    exact Fin.ext (by omega)
  have hvars : (h.vars : Set PNat) ⊆ Set.range (generatorIndex (s := s)) := by
    intro k hk
    have hks := hh k hk
    refine ⟨⟨k.val - 1, by have := k.pos; omega⟩, PNat.eq ?_⟩
    simp only [generatorIndex, PNat.mk_coe]
    have := k.pos
    omega
  have hemb : embedFirst s = MvPolynomial.rename (R := Real) (generatorIndex (s := s)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [embedFirst, p, MvPolynomial.aeval_X, MvPolynomial.rename_X]
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range h _ hinj hvars
  exact ⟨q, by rw [hemb]; exact hq⟩

theorem trunc_embedFirst (s : ℕ) (q : Poly s) :
    trunc s (embedFirst s q) = powerSubst s q := by
  have h : (trunc s).comp (embedFirst s) = powerSubst s := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, embedFirst, MvPolynomial.aeval_X, p, trunc, MvPolynomial.aeval_X,
      powerSubst, MvPolynomial.aeval_X]
    rfl
  exact congrArg (· q) h

/-- A nonzero element of `ℝ[p_1, …, p_s]` has nonzero truncation to `s` variables. -/
theorem trunc_ne_zero_of_usesFirst {s : ℕ} {h : Λ} (hh : UsesFirst s h) (hne : h ≠ 0) :
    trunc s h ≠ 0 := by
  obtain ⟨q, rfl⟩ := finite_representation h hh
  rw [trunc_embedFirst]
  intro h0
  exact hne (by rw [powerSubst_kernel s q h0, map_zero])

theorem psi_on_embedFirst (n s : Nat) (q : Poly s) :
    psi n s (embedFirst s q) = shiftedPowerSubst n s q := by
  have h : (psi n s).comp (embedFirst s) = shiftedPowerSubst n s := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, embedFirst, shiftedPowerSubst, powerSubst, translate, psi, p,
      MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    exact add_comm _ _
  exact congrArg (· q) h

/-- The translates `c_k(1/2) + p_k^{(s)}`, `1 ≤ k ≤ s`, are algebraically independent: a nonzero
`h ∈ ℝ[p_1, …, p_s]` has `psi N s h ≠ 0`. -/
theorem psi_ne_zero {s : Nat} (n : Nat) (h : Λ)
    (hh : UsesFirst s h) (hne : h ≠ 0) : psi n s h ≠ 0 := by
  intro hz
  obtain ⟨q, hq⟩ := finite_representation h hh
  have hq0 : shiftedPowerSubst n s q = 0 := by
    rw [← psi_on_embedFirst, hq]
    exact hz
  have hqzero : q = 0 := by
    apply shiftedPowerSubst_injective n s
    simpa only [map_zero] using hq0
  apply hne
  rw [← hq, hqzero, map_zero]

/-- General m>=s version, obtained without another Jacobian calculation. -/
theorem psi_ne_zero_of_le {s m : Nat} (n : Nat) (h : Λ)
    (hsm : s ≤ m) (hh : UsesFirst s h) (hne : h ≠ 0) : psi n m h ≠ 0 := by
  exact psi_ne_zero n h (usesFirst_mono hh hsm) hne

theorem real_nonneg_mul_negative_eq_zero (a b : Real)
    (ha : 0 ≤ a) (hab : 0 ≤ a * b) (hb : b < 0) : a = 0 := by
  by_contra hne
  have ha' : 0 < a := by
    by_contra h
    exact hne (le_antisymm (le_of_not_gt h) ha)
  have hneg := mul_neg_of_pos_of_neg ha' hb
  linarith

theorem evalAt_continuous {m : Nat} (q : Poly m) :
    Continuous (fun z : Fin m → Real => evalAt q z) :=
  MvPolynomial.continuous_eval q

theorem negative_locus_open {m : Nat} (q : Poly m) :
    IsOpen {z : Fin m → Real | evalAt q z < 0} :=
  isOpen_lt (evalAt_continuous q) continuous_const

/-- The multiplier cannot merely vanish at the bad point: it vanishes on an open set. -/
theorem polynomial_zero_of_nonneg_product {m : Nat} (G J : Poly m)
    (hG : ∀ z : Fin m → Real, 0 ≤ evalAt G z)
    (hGJ : ∀ z : Fin m → Real, 0 ≤ evalAt (G * J) z)
    (hJ0 : evalAt J (fun _ => 0) < 0) : G = 0 := by
  apply polynomial_zero_on_open G {z | evalAt J z < 0}
    (negative_locus_open J) ⟨(fun _ => 0), hJ0⟩
  intro z hz
  have hp : 0 ≤ evalAt G z * evalAt J z := by
    simpa [evalAt, map_mul] using hGJ z
  exact real_nonneg_mul_negative_eq_zero _ _ (hG z) hp hz

end AnyDim
end
