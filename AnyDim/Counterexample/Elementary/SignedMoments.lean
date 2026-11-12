module

public import AnyDim.Counterexample.Elementary.BooleanMoments

/-!
# A pseudo-expectation on the sign cube (elementary route)

Transport of `BooleanMoments` along `X_i ↦ 2 X_i - 1`: for `d ≥ 1` and `n ≥ 4d` there is a
linear functional `L` on the functions of degree `≤ 2d` on `{-1,1}^n` (`SignedPseudo n d`,
`signedPseudo_exists`) with `L(1) = 1`, `L(q²) ≥ 0` for `deg q ≤ d`, and
`L((∑ X_i - 1/2) · a) = 0` for `deg a ≤ 2d - 1`.  Consequently `L(P(∑ X_i)) = P(1/2)` for every
univariate `P` of degree `≤ 2d` (`signed_polynomial_eval`) and `L(h) ≥ 0` for every sum of
squares `h` of degree `≤ 2d` (`signed_nonneg_of_sos`).

The equation `∑ X_i = 1/2` is never imposed as an identity on the cube; only the low-degree
annihilation property is used.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim.Elementary

def preSignedToBool (n : Nat) : AlgHom Real (Poly n) (BoolCube n) :=
  MvPolynomial.aeval (fun i : Fin n => 2 * bGen n i - 1)

theorem preSignedToBool_kills (n : Nat) :
    ∀ a ∈ signedIdeal n, preSignedToBool n a = 0 := by
  have hle : signedIdeal n ≤ RingHom.ker (preSignedToBool n) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hsq := bGen_sq n i
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, map_one, preSignedToBool,
      MvPolynomial.aeval_X]
    linear_combination 4 * hsq
  exact fun a ha => hle ha

def signedToBool (n : Nat) : AlgHom Real (SignCube n) (BoolCube n) :=
  Ideal.Quotient.liftₐ (signedIdeal n) (preSignedToBool n) (preSignedToBool_kills n)

theorem signedToBool_yGen (n : Nat) (i : Fin n) :
    signedToBool n (yGen n i) = 2 * bGen n i - 1 := by
  show preSignedToBool n (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ i

theorem signedToBool_yMono_mem (n : Nat) (S : Finset (Fin n)) :
    signedToBool n (yMono n S) ∈ BFilter n S.card := by
  induction S using Finset.induction_on with
  | empty => simpa [yMono] using bOne_mem n 0
  | insert i S hi ih =>
    rw [yMono, Finset.prod_insert hi, map_mul, signedToBool_yGen, Finset.card_insert_of_notMem hi,
      add_comm]
    refine bMul_mem ?_ ih
    rw [two_mul]
    exact sub_mem (add_mem (bGen_mem n i) (bGen_mem n i)) (bOne_mem n 1)

theorem signedToBool_filtered {n k : Nat} (q : SignCube n) (hq : q ∈ DFilter n k) :
    signedToBool n q ∈ BFilter n k := by
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    exact bFilter_mono hS (signedToBool_yMono_mem n S)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- Only the filtered LINEAR restriction; the filtered spaces are not rings. -/
def filteredSignedToBool (n k : Nat) : LinearMap (RingHom.id Real) (DFilter n k) (BFilter n k) where
  toFun q := ⟨signedToBool n q.val, signedToBool_filtered q.val q.property⟩
  map_add' := by
    intro q r
    apply Subtype.ext
    change signedToBool n (q.val + r.val) = signedToBool n q.val + signedToBool n r.val
    exact map_add (signedToBool n) q.val r.val
  map_smul' := by
    intro c q
    apply Subtype.ext
    change signedToBool n (c • q.val) = c • signedToBool n q.val
    exact map_smul (signedToBool n) c q.val

theorem signedToBool_slice (n : Nat) :
    signedToBool n (ySlice n) = 2 * bSlice n (fractionalCardinality n) := by
  have h2 : (2 : BoolCube n) * algebraMap Real (BoolCube n) (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap Real (BoolCube n)) 2, ← map_mul]
    norm_num
  have hr : fractionalCardinality n = (n : Real) * (1 / 2) + 1 / 2 * (1 / 2) := by
    rw [fractionalCardinality]; ring
  simp only [ySlice, ySum, bSlice, bSum, hr, map_sub, map_sum, signedToBool_yGen, AlgHom.commutes,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, map_add, map_mul, map_natCast]
  linear_combination ((n : BoolCube n) + algebraMap Real (BoolCube n) (1 / 2)) * h2

def transportedFunctional {n d : Nat} (M : BooleanMoments n d) :
    LinearMap (RingHom.id Real) (DFilter n (2 * d)) Real :=
  M.L.comp (filteredSignedToBool n (2 * d))

structure SignedPseudo (n d : Nat) where
  L : LinearMap (RingHom.id Real) (DFilter n (2 * d)) Real
  on_one : L ⟨1, yOne_mem n (2 * d)⟩ = 1
  on_square : ∀ (q : SignCube n) (hq : q ∈ DFilter n d),
    0 ≤ L ⟨q ^ 2, ySquare_mem hq⟩
  on_slice : ∀ (k : Nat) (hk : k + 1 ≤ 2 * d)
    (a : SignCube n) (ha : a ∈ DFilter n k),
    L ⟨ySlice n * a, ySlice_mem hk ha⟩ = 0

theorem transported_one {n d : Nat} (M : BooleanMoments n d) :
    transportedFunctional M ⟨1, yOne_mem n (2 * d)⟩ = 1 := by
  rw [← booleanMoments_one M]
  exact linearMap_mk_congr M.L (map_one _) _ _

theorem transported_square {n d : Nat} (M : BooleanMoments n d)
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (q : SignCube n) (hq : q ∈ DFilter n d) :
    0 ≤ transportedFunctional M ⟨q ^ 2, ySquare_mem hq⟩ := by
  refine (boolean_square_nonneg M hd hnd _ (signedToBool_filtered q hq)).trans_eq ?_
  exact linearMap_mk_congr M.L (map_pow _ _ _).symm _ _

theorem transported_slice {n d : Nat} (M : BooleanMoments n d)
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (k : Nat) (hk : k + 1 ≤ 2 * d)
    (a : SignCube n) (ha : a ∈ DFilter n k) :
    transportedFunctional M ⟨ySlice n * a, ySlice_mem hk ha⟩ = 0 := by
  have ha' := signedToBool_filtered a ha
  have hmem := bSlice_mem (fractionalCardinality n) hk ha'
  have heq : signedToBool n (ySlice n * a) =
      bSlice n (fractionalCardinality n) * signedToBool n a +
        bSlice n (fractionalCardinality n) * signedToBool n a := by
    rw [map_mul, signedToBool_slice, mul_assoc, two_mul]
  change M.L ⟨signedToBool n (ySlice n * a), _⟩ = 0
  rw [linearMap_mk_congr M.L heq _ (add_mem hmem hmem), linearMap_mk_add M.L hmem hmem,
    boolean_slice_zero M hd hnd hk _ ha', add_zero]

/-- For `d ≥ 1` and `n ≥ 4d` the pseudo-expectation on the sign cube exists (assembled from the
Boolean cube; no additional axiom). -/
theorem signedPseudo_exists {n d : Nat} (hd : 1 ≤ d) (hnd : 4 * d ≤ n) :
    Nonempty (SignedPseudo n d) := by
  obtain ⟨M⟩ := booleanMoments_exists n d
  refine ⟨{
    L := transportedFunctional M
    on_one := transported_one M
    on_square := ?_
    on_slice := ?_
  }⟩
  · intro q hq
    exact transported_square M hd hnd q hq
  · intro k hk a ha
    exact transported_slice M hd hnd k hk a ha

section AlgebraFunctional

variable {A : Type*} [Ring A] [Algebra Real A] {p : Submodule Real A}

/-- A real submodule of a real algebra is closed under left multiplication by scalars
`algebraMap c`. -/
theorem algebraMap_mul_mem (c : Real) {x : A} (hx : x ∈ p) : algebraMap Real A c * x ∈ p :=
  (Algebra.smul_def c x) ▸ p.smul_mem c hx

/-- A functional on a real submodule of a real algebra pulls out scalars written as
left multiplication by `algebraMap c`. -/
theorem linearMap_mk_algebraMap_mul (L : p →ₗ[Real] Real) (c : Real) {x : A} (hx : x ∈ p)
    (h : algebraMap Real A c * x ∈ p) :
    L ⟨algebraMap Real A c * x, h⟩ = c * L ⟨x, hx⟩ :=
  (linearMap_mk_congr L (Algebra.smul_def c x).symm h (p.smul_mem c hx)).trans
    (linearMap_mk_smul L c hx _)

end AlgebraFunctional

theorem signed_power_eval {n d : Nat} (L : SignedPseudo n d)
    (j : Nat) (hj : j ≤ 2 * d) :
    L.L ⟨ySum n ^ j, ySum_pow_mem hj⟩ = (1 / 2 : Real) ^ j := by
  induction j with
  | zero =>
    rw [linearMap_mk_congr L.L (pow_zero _) _ (yOne_mem n _), L.on_one, pow_zero]
  | succ j ih =>
    have hj' : j ≤ 2 * d := by omega
    have hsl := ySlice_mem hj (ySum_pow_mem_self n j)
    have hsm : algebraMap Real (SignCube n) (1 / 2) * ySum n ^ j ∈ DFilter n (2 * d) :=
      algebraMap_mul_mem _ (ySum_pow_mem hj')
    have heq : ySum n ^ (j + 1) =
        ySlice n * ySum n ^ j + algebraMap Real (SignCube n) (1 / 2) * ySum n ^ j := by
      rw [ySlice]; ring
    rw [linearMap_mk_congr L.L heq _ (add_mem hsl hsm), linearMap_mk_add L.L hsl hsm,
      L.on_slice j hj _ (ySum_pow_mem_self n j),
      linearMap_mk_algebraMap_mul L.L _ (ySum_pow_mem hj') hsm, ih hj', pow_succ]
    ring

theorem signed_polynomial_eval {n d : Nat} (L : SignedPseudo n d)
    (P : Polynomial Real) (hP : P.natDegree ≤ 2 * d) :
    L.L ⟨Polynomial.aeval (ySum n) P, ySum_poly_mem P hP⟩ =
      Polynomial.eval (1 / 2 : Real) P := by
  have hlt := Nat.lt_succ_of_le hP
  have hf : ∀ j, P.coeff j • ySum n ^ j ∈ DFilter n (2 * d) := by
    intro j
    by_cases hj : j ≤ 2 * d
    · exact Submodule.smul_mem _ _ (ySum_pow_mem hj)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
      exact zero_mem _
  rw [linearMap_mk_congr L.L (Polynomial.aeval_eq_sum_range' hlt (ySum n)) _
      (Submodule.sum_mem _ fun j _ => hf j),
    linearMap_mk_sum L.L _ _ hf, Polynomial.eval_eq_sum_range' hlt]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ 2 * d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [linearMap_mk_smul L.L _ (ySum_pow_mem hj'), signed_power_eval L j hj']

theorem signed_apply_sos {n d : Nat} (L : SignedPseudo n d)
    (h : Poly n) (hdeg : h.totalDegree ≤ 2 * d)
    (r : Nat) (q : Fin r → Poly n)
    (heq : h = Finset.univ.sum (fun i => q i ^ 2))
    (hq : ∀ i, (q i).totalDegree ≤ d) :
    L.L ⟨dMk n h, dMk_mem h hdeg⟩ =
      Finset.univ.sum (fun i =>
        L.L ⟨(dMk n (q i)) ^ 2, ySquare_mem (dMk_mem (q i) (hq i))⟩) := by
  have hmem : ∀ i, dMk n (q i) ^ 2 ∈ DFilter n (2 * d) :=
    fun i => ySquare_mem (dMk_mem (q i) (hq i))
  have heq' : dMk n h = ∑ i, dMk n (q i) ^ 2 := by
    rw [heq, map_sum (dMk n)]
    simp only [map_pow]
  rw [linearMap_mk_congr L.L heq' _ (Submodule.sum_mem _ fun i _ => hmem i),
    linearMap_mk_sum L.L _ _ hmem]

theorem signed_nonneg_of_sos {n d : Nat} (L : SignedPseudo n d)
    (h : Poly n) (hdeg : h.totalDegree ≤ 2 * d) (hsos : IsSOS h) :
    0 ≤ L.L ⟨dMk n h, dMk_mem h hdeg⟩ := by
  obtain ⟨r, q, heq, hq⟩ := sos_degree_bound hsos hdeg
  rw [signed_apply_sos L h hdeg r q heq hq]
  exact Finset.sum_nonneg (fun i _ => L.on_square _ (dMk_mem (q i) (hq i)))

end AnyDim.Elementary
end
