module

public import AnyDim.Counterexample.Geometry

/-!
# Symmetrization and the fundamental theorem of symmetric polynomials

Source: Debus--Schabert, proofs of Corollary 3.4 and Proposition 3.9 ("By applying the
Reynolds-operator, we can assume that `Q` is symmetric.  By the fundamental theorem of symmetric
polynomials, we can write `Q = Q̃(p_1, …, p_d)`").

* Closure properties of sums of squares (`isSOS_zero`, `isSOS_sq`, `IsSOS.add`, `isSOS_sum`,
  `IsSOS.smul_nonneg`).
* `symmetrize a = ∑_σ σ·a` (the Reynolds operator up to the factor `n!`): it is symmetric, maps
  sums of squares to sums of squares, does not raise the degree, is nonzero on nonzero sums of
  squares, and `symmetrize (a · f^{(n)}) = symmetrize a · f^{(n)}`.
* `exists_trunc_eq_of_totalDegree_le`: a symmetric polynomial of degree `≤ d` in `n` variables is
  the truncation `B^{(n)}` of a symmetric function `B ∈ Λ` of degree `≤ d` (so `B` is a
  polynomial in `p_1, …, p_d`).  This uses Mathlib's fundamental theorem for elementary
  symmetric polynomials and Newton's identities (`newtonE`, `trunc_newtonE`).
* Zero padding: `truncateVars m n` sets `X_{m+1}, …, X_n` to zero, and
  `(f^{(n)})(X_1, …, X_m, 0, …, 0) = f^{(m)}` (`truncateVars_trunc`); hence truncations of sums
  of squares are sums of squares (`isSOS_trunc_of_le`).

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open MvPolynomial Filter Topology

/-! ### Elementary closure properties of `IsSOS` -/

theorem isSOS_zero {R : Type*} [CommRing R] : IsSOS (0 : R) :=
  ⟨0, Fin.elim0, by simp⟩

theorem isSOS_sq {R : Type*} [CommRing R] (q : R) : IsSOS (q ^ 2) :=
  ⟨1, fun _ => q, by simp⟩

theorem IsSOS.add {R : Type*} [CommRing R] {a b : R} (ha : IsSOS a) (hb : IsSOS b) :
    IsSOS (a + b) := by
  obtain ⟨r, q, rfl⟩ := ha
  obtain ⟨s, q', rfl⟩ := hb
  refine ⟨r + s, Fin.append q q', ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem isSOS_sum {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, IsSOS (f i)) : IsSOS (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSOS_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem IsSOS.smul_nonneg {R : Type*} [CommRing R] [Algebra ℝ R] {a : R} (ha : IsSOS a) {r : ℝ}
    (hr : 0 ≤ r) : IsSOS (r • a) := by
  obtain ⟨n, q, rfl⟩ := ha
  refine ⟨n, fun j => Real.sqrt r • q j, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_pow, Real.sq_sqrt hr]

/-- Over `ℝ`, a vanishing sum of squares of polynomials has vanishing summands. -/
theorem sum_sq_eq_zero {m : ℕ} {ι : Type*} [Fintype ι] {q : ι → Poly m}
    (h : ∑ i, q i ^ 2 = 0) (i : ι) : q i = 0 := by
  apply MvPolynomial.funext
  intro x
  have hx := congrArg (eval x) h
  simp only [map_sum, map_pow, map_zero] at hx
  rw [map_zero]
  exact pow_eq_zero_iff two_ne_zero |>.1 <|
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _).1 hx i (Finset.mem_univ i)

/-! ### Symmetrization -/

section Symmetrization

variable {n : ℕ}

/-- The (unnormalized) symmetrization `∑_σ σ·a` of a polynomial in `n` variables. -/
def symmetrize (a : Poly n) : Poly n := ∑ σ : Equiv.Perm (Fin n), rename σ a

theorem symmetrize_isSymmetric (a : Poly n) : (symmetrize a).IsSymmetric := by
  intro τ
  unfold symmetrize
  rw [map_sum]
  simp only [rename_rename]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun _ => by
    simp only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul]

theorem symmetrize_isSOS {a : Poly n} (ha : IsSOS a) : IsSOS (symmetrize a) :=
  isSOS_sum _ _ fun σ _ => isSOS_map (rename σ).toRingHom ha

theorem totalDegree_symmetrize_le (a : Poly n) : (symmetrize a).totalDegree ≤ a.totalDegree :=
  (totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => totalDegree_rename_le σ a)

theorem symmetrize_isHomogeneous {a : Poly n} {d : ℕ} (ha : a.IsHomogeneous d) :
    (symmetrize a).IsHomogeneous d :=
  IsHomogeneous.sum _ _ _ fun _ _ => ha.rename_isHomogeneous

theorem eval_symmetrize (a : Poly n) (x : Fin n → ℝ) :
    eval x (symmetrize a) = ∑ σ : Equiv.Perm (Fin n), eval (x ∘ σ) a := by
  unfold symmetrize
  rw [map_sum]
  simp only [eval_rename]

/-- The symmetrization of a nonzero SOS is nonzero (it is pointwise at least the SOS itself). -/
theorem symmetrize_ne_zero {a : Poly n} (ha : IsSOS a) (hne : a ≠ 0) : symmetrize a ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x : Fin n → ℝ, eval x a ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (MvPolynomial.funext fun x => by rw [h x, map_zero])
  have hpos : 0 < eval x a := lt_of_le_of_ne (isSOS_eval_nonneg ha x) (Ne.symm hx)
  intro h0
  have h1 := eval_symmetrize a x
  rw [h0, map_zero] at h1
  have h2 : eval x a ≤ ∑ σ : Equiv.Perm (Fin n), eval (x ∘ σ) a := by
    have := Finset.single_le_sum (f := fun σ : Equiv.Perm (Fin n) => eval (x ∘ σ) a)
      (fun σ _ => isSOS_eval_nonneg ha (x ∘ σ)) (Finset.mem_univ (1 : Equiv.Perm (Fin n)))
    simpa using this
  linarith

theorem trunc_isSymmetric (h : Λ) : (trunc n h).IsSymmetric := by
  intro σ
  have hcomp : (rename (R := ℝ) σ).comp (trunc n) = trunc n := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, trunc, MvPolynomial.aeval_X, powerSum, map_sum, map_pow,
      rename_X]
    exact Equiv.sum_comp σ fun i => (X i : Poly n) ^ (k : ℕ)
  exact congrArg (· h) hcomp

theorem symmetrize_mul_trunc (a : Poly n) (h : Λ) :
    symmetrize (a * trunc n h) = symmetrize a * trunc n h := by
  unfold symmetrize
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by rw [map_mul, trunc_isSymmetric h σ]

end Symmetrization

/-! ### Symmetric polynomials as polynomials in the power sums -/

section PowerSums

/-- The universal polynomials expressing the elementary symmetric polynomials through the power
sums (Newton's identities): `k·e_k = ∑_{j<k} (-1)^{k+1+j} e_j p_{k-j}`. -/
def newtonE : ℕ → Λ
  | 0 => 1
  | k + 1 => ((k + 1 : ℕ) : ℝ)⁻¹ • ((-1) ^ (k + 2) *
      ∑ j : Fin (k + 1), (-1) ^ (j : ℕ) * newtonE j *
        p (Nat.toPNat (k + 1 - j) (by have := j.isLt; omega)))
decreasing_by exact j.isLt

theorem newtonE_succ (k : ℕ) : newtonE (k + 1) = ((k + 1 : ℕ) : ℝ)⁻¹ • ((-1) ^ (k + 2) *
      ∑ j : Fin (k + 1), (-1) ^ (j : ℕ) * newtonE j *
        p (Nat.toPNat (k + 1 - j) (by have := j.isLt; omega))) := by
  rw [newtonE]

theorem powerSum_eq_psum (n k : ℕ) : powerSum n k = psum (Fin n) ℝ k := rfl

/-- Mathlib's Newton sum over the antidiagonal, as a sum over `Fin (k+1)`. -/
theorem newton_sum_eq (n k : ℕ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal (k + 1) with a.1 < k + 1,
        (-1) ^ a.1 * esymm (Fin n) ℝ a.1 * psum (Fin n) ℝ a.2 =
      ∑ j : Fin (k + 1),
        (-1) ^ (j : ℕ) * esymm (Fin n) ℝ j * psum (Fin n) ℝ (k + 1 - j) := by
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun a : ℕ × ℕ =>
      if a.1 < k + 1 then (-1) ^ a.1 * esymm (Fin n) ℝ a.1 * psum (Fin n) ℝ a.2 else 0),
    Finset.sum_range_succ, ite_eq_right (lt_irrefl _), add_zero,
    Fin.sum_univ_eq_sum_range
      (fun j => (-1) ^ j * esymm (Fin n) ℝ j * psum (Fin n) ℝ (k + 1 - j))]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_left (Finset.mem_range.1 hj)]

theorem trunc_newtonE (n k : ℕ) : trunc n (newtonE k) = esymm (Fin n) ℝ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  cases k with
  | zero => simp [newtonE, esymm_zero]
  | succ k =>
    rw [newtonE_succ, map_smul, map_mul, map_pow, map_neg, map_one, map_sum]
    have hterm : ∀ j : Fin (k + 1),
        trunc n ((-1) ^ (j : ℕ) * newtonE j *
            p (Nat.toPNat (k + 1 - j) (by have := j.isLt; omega))) =
          (-1) ^ (j : ℕ) * esymm (Fin n) ℝ j * psum (Fin n) ℝ (k + 1 - j) := by
      intro j
      rw [map_mul, map_mul, map_pow, map_neg, map_one, ih j j.isLt, trunc_p]
      rfl
    simp only [hterm]
    rw [← newton_sum_eq, ← mul_esymm_eq_sum (Fin n) ℝ (k + 1)]
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [← map_natCast (algebraMap ℝ (Poly n)), Algebra.smul_def, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hk, map_one, one_mul]

/-- Fundamental theorem of symmetric polynomials in the power-sum form: every symmetric polynomial
in `n` variables is the truncation of an element of `Λ`. -/
theorem exists_trunc_eq_of_isSymmetric {n : ℕ} {b : Poly n} (hb : b.IsSymmetric) :
    ∃ B : Λ, trunc n B = b := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℝ (le_refl n) ⟨b, hb⟩
  refine ⟨aeval (fun i : Fin n => newtonE (i + 1)) Q, ?_⟩
  have h1 : aeval (fun i : Fin n => esymm (Fin n) ℝ (i + 1)) Q = b := by
    have := congrArg Subtype.val hQ
    rwa [esymmAlgHom_apply] at this
  rw [← h1, comp_aeval_apply]
  have hfun : (fun i : Fin n => trunc n (newtonE ((i : ℕ) + 1))) =
      fun i : Fin n => esymm (Fin n) ℝ ((i : ℕ) + 1) :=
    funext fun i => trunc_newtonE n ((i : ℕ) + 1)
  rw [hfun]

theorem powerSum_isHomogeneous (n k : ℕ) : (powerSum n k).IsHomogeneous k :=
  IsHomogeneous.sum _ _ _ fun i _ => by simpa using isHomogeneous_X_pow (R := ℝ) i k

/-- `trunc n` sends a monomial of weight `w` to a homogeneous polynomial of degree `w`. -/
theorem trunc_monomial_isHomogeneous (n : ℕ) (e : PNat →₀ ℕ) (r : ℝ) :
    (trunc n (monomial e r)).IsHomogeneous (monomialWeight e) := by
  rw [trunc, aeval_monomial, monomialWeight, Finsupp.sum, Finsupp.prod]
  have := IsHomogeneous.prod e.support (fun k : PNat => powerSum n (k : ℕ) ^ e k)
    (fun k : PNat => (k : ℕ) * e k) fun k _ => (powerSum_isHomogeneous n k).pow (e k)
  have hC : ((algebraMap ℝ (Poly n)) r).IsHomogeneous 0 := isHomogeneous_C _ r
  simpa using hC.mul this

/-- `trunc n` is compatible with the weighted and ordinary homogeneous decompositions. -/
theorem trunc_weightedHomogeneousComponent (n w : ℕ) (B : Λ) :
    trunc n (weightedHomogeneousComponent wt w B) =
      homogeneousComponent w (trunc n B) := by
  induction B using MvPolynomial.induction_on' with
  | monomial e r =>
    have hh := trunc_monomial_isHomogeneous n e r
    rw [homogeneousComponent_of_mem hh,
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial wt e r rfl)]
    rw [← monomialWeight_eq_weight]
    split_ifs <;> simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

theorem trunc_isHomogeneous {n : ℕ} {h : Λ} {e : ℕ} (hh : WHomogeneous h e) :
    (trunc n h).IsHomogeneous e := by
  have hw : IsWeightedHomogeneous wt h e := fun d hd => by
    rw [← monomialWeight_eq_weight]
    exact hh d (mem_support_iff.2 hd)
  rw [← hw.weightedHomogeneousComponent_same, trunc_weightedHomogeneousComponent]
  exact homogeneousComponent_isHomogeneous _ _

theorem wHomogeneous_weightedHomogeneousComponent (w : ℕ) (B : Λ) :
    WHomogeneous (weightedHomogeneousComponent wt w B) w := fun e he => by
  rw [monomialWeight_eq_weight]
  exact weightedHomogeneousComponent_isWeightedHomogeneous w B (mem_support_iff.1 he)

/-- Homogeneous symmetric polynomials of degree `d` are truncations of homogeneous
elements of `Λ` of weight `d`. -/
theorem exists_trunc_eq_of_isHomogeneous {n : ℕ} {b : Poly n} (hb : b.IsSymmetric) {d : ℕ}
    (hd : b.IsHomogeneous d) : ∃ B : Λ, WHomogeneous B d ∧ trunc n B = b := by
  obtain ⟨B₀, hB₀⟩ := exists_trunc_eq_of_isSymmetric hb
  refine ⟨weightedHomogeneousComponent wt d B₀,
    wHomogeneous_weightedHomogeneousComponent d B₀, ?_⟩
  rw [trunc_weightedHomogeneousComponent, hB₀, homogeneousComponent_eq_self hd]

/-- Symmetric polynomials of degree `≤ d` are truncations of elements of `Λ` of
degree `≤ d`. -/
theorem exists_trunc_eq_of_totalDegree_le {n : ℕ} {b : Poly n} (hb : b.IsSymmetric) {d : ℕ}
    (hd : b.totalDegree ≤ d) : ∃ B : Λ, WDegLE B d ∧ trunc n B = b := by
  obtain ⟨B₀, hB₀⟩ := exists_trunc_eq_of_isSymmetric hb
  refine ⟨∑ w ∈ Finset.range (d + 1), weightedHomogeneousComponent wt w B₀, ?_, ?_⟩
  · intro e he
    rw [mem_support_iff, coeff_sum] at he
    obtain ⟨w, hw, hew⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    rw [wHomogeneous_weightedHomogeneousComponent w B₀ e (mem_support_iff.2 hew)]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hw)
  · rw [map_sum]
    simp only [trunc_weightedHomogeneousComponent, hB₀]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hd))
      (fun w _ hw => homogeneousComponent_eq_zero w b (by
        rw [Finset.mem_range, not_lt] at hw
        omega))]
    exact sum_homogeneousComponent b

end PowerSums

/-! ### Zero padding -/

section ZeroPadding

/-- Setting the variables `X_m, …, X_{n-1}` to zero. -/
def truncateVars (m n : ℕ) : Poly n →ₐ[ℝ] Poly m :=
  aeval fun i : Fin n => if h : i.val < m then X ⟨i.val, h⟩ else 0

theorem truncateVars_powerSum {m n : ℕ} (hmn : m ≤ n) {k : ℕ} (hk : 0 < k) :
    truncateVars m n (powerSum n k) = powerSum m k := by
  unfold truncateVars powerSum
  rw [map_sum]
  simp only [map_pow, aeval_X]
  let g : ℕ → Poly m := fun i => if h : i < m then X ⟨i, h⟩ ^ k else 0
  have h1 : ∀ i : Fin n,
      (if h : i.val < m then (X ⟨i.val, h⟩ : Poly m) else 0) ^ k = g i.val := by
    intro i
    by_cases h : i.val < m
    · simp [g, h]
    · simp [g, h, zero_pow hk.ne']
  have h2 : ∀ j : Fin m, (X j : Poly m) ^ k = g j.val := fun j => by simp [g, j.isLt]
  simp_rw [h1, h2]
  rw [Fin.sum_univ_eq_sum_range g n, Fin.sum_univ_eq_sum_range g m]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.2 hmn)
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  simp [g, not_lt.2 hi]

theorem truncateVars_trunc {m n : ℕ} (hmn : m ≤ n) (h : Λ) :
    truncateVars m n (trunc n h) = trunc m h := by
  have hcomp : (truncateVars m n).comp (trunc n) = trunc m := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, trunc, aeval_X]
    exact truncateVars_powerSum hmn k.pos
  exact congrArg (· h) hcomp

theorem isSOS_trunc_of_le {m n : ℕ} (hmn : m ≤ n) {h : Λ} (hs : IsSOS (trunc n h)) :
    IsSOS (trunc m h) := by
  rw [← truncateVars_trunc hmn]
  exact isSOS_map (truncateVars m n).toRingHom hs

end ZeroPadding

/-! ### The conventions "for every `n`" and "for every `n ≥ 1`" agree -/

theorem isSOS_trunc_zero {h : Λ} (hh : IsSOS (trunc 1 h)) : IsSOS (trunc 0 h) :=
  isSOS_trunc_of_le (Nat.zero_le 1) hh

/-- `f ∈ SΣ` iff every truncation `f^{(n)}`, `n ≥ 0`, is a sum of squares. -/
theorem anyDimSOS_iff_forall (h : Λ) : AnyDimSOS h ↔ ∀ n, IsSOS (trunc n h) := by
  refine ⟨fun hs n => ?_, fun hs n _ => hs n⟩
  cases n with
  | zero => exact isSOS_trunc_zero (hs 1 Nat.one_pos)
  | succ n => exact hs (n + 1) n.succ_pos

/-- A degree bound for `f` uses only the power sums `p_1, …, p_d`. -/
theorem usesFirst_of_wDegLE {h : Λ} {d : ℕ} (hh : WDegLE h d) : UsesFirst d h := by
  intro k hk
  obtain ⟨e, he, hke⟩ := (MvPolynomial.mem_vars_iff_mem_support k).mp hk
  refine le_trans ?_ (hh e he)
  rw [monomialWeight, Finsupp.sum]
  have hek : 1 ≤ e k := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hke)
  calc (k : ℕ) ≤ (k : ℕ) * e k := Nat.le_mul_of_pos_right _ hek
    _ ≤ ∑ a ∈ e.support, (a : ℕ) * e a :=
      Finset.single_le_sum (f := fun a : PNat => (a : ℕ) * e a) (fun _ _ => Nat.zero_le _) hke

/-- Degree bounds are compatible with products. -/
theorem WDegLE.mul {g h : Λ} {D E : ℕ} (hg : WDegLE g D) (hh : WDegLE h E) :
    WDegLE (g * h) (D + E) := by
  classical
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
  have hadd : monomialWeight (a + b) = monomialWeight a + monomialWeight b := by
    simp only [monomialWeight_eq_weight, map_add]
  rw [hadd]
  exact add_le_add (hg a ha) (hh b hb)

end AnyDim
end
