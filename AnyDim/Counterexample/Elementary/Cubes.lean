module

public import AnyDim.Basic

/-!
# The two cube algebras (elementary route)

This file and the two following ones (`BooleanMoments`, `SignedMoments`) give an elementary,
self-contained proof of a weaker form of Corollary 3.3 of the paper, which does **not** use
Blekherman's theorem (Theorem 3.2).  It is used to make Theorem 3.1 independent of the `sorry`
in the statement of Theorem 3.2; see `AnyDim.Counterexample.Elementary.CubeBound`.

* `BoolCube n = ℝ[X_1, …, X_n] / (X_i² - X_i)` is the algebra of functions on `{0,1}^n`,
  `SignCube n = ℝ[X_1, …, X_n] / (X_i² - 1)` the algebra of functions on `{-1,1}^n`.
* `BFilter n k`, `DFilter n k` are the images of the polynomials of degree `≤ k`
  (spanned by the squarefree monomials in at most `k` variables).
* `bSum n`, `ySum n` are the classes of `X_1 + ⋯ + X_n`.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim.Elementary

def boolIdeal (n : Nat) : Ideal (Poly n) :=
  Ideal.span (Set.range (fun i : Fin n =>
    (MvPolynomial.X i : Poly n) ^ 2 - MvPolynomial.X i))

def signedIdeal (n : Nat) : Ideal (Poly n) :=
  Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : Poly n) ^ 2 - 1))

abbrev BoolCube (n : Nat) := Poly n ⧸ boolIdeal n
abbrev SignCube (n : Nat) := Poly n ⧸ signedIdeal n

def bMk (n : Nat) : AlgHom Real (Poly n) (BoolCube n) :=
  Ideal.Quotient.mkₐ Real (boolIdeal n)

def dMk (n : Nat) : AlgHom Real (Poly n) (SignCube n) :=
  Ideal.Quotient.mkₐ Real (signedIdeal n)

def bGen (n : Nat) (i : Fin n) : BoolCube n := bMk n (MvPolynomial.X i)
def yGen (n : Nat) (i : Fin n) : SignCube n := dMk n (MvPolynomial.X i)

def bMono (n : Nat) (S : Finset (Fin n)) : BoolCube n := S.prod (bGen n)
def yMono (n : Nat) (S : Finset (Fin n)) : SignCube n := S.prod (yGen n)

def BFilter (n k : Nat) : Submodule Real (BoolCube n) :=
  Submodule.span Real {a | ∃ S : Finset (Fin n), S.card ≤ k ∧ a = bMono n S}

def DFilter (n k : Nat) : Submodule Real (SignCube n) :=
  Submodule.span Real {a | ∃ S : Finset (Fin n), S.card ≤ k ∧ a = yMono n S}

def bSum (n : Nat) : BoolCube n := Finset.univ.sum (bGen n)
def ySum (n : Nat) : SignCube n := Finset.univ.sum (yGen n)

def fractionalCardinality (n : Nat) : Real := (n : Real) / 2 + 1 / 4

def bSlice (n : Nat) (r : Real) : BoolCube n := bSum n - algebraMap Real (BoolCube n) r

def ySlice (n : Nat) : SignCube n := ySum n - algebraMap Real (SignCube n) (1 / 2 : Real)

/-- If every product of a generator of `s` with a generator of `t` lies in `span R u`, then
so does every product of an element of `span R s` with an element of `span R t`. -/
theorem mul_mem_span_of_forall_mem {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {s t u : Set A} {a b : A} (ha : a ∈ Submodule.span R s) (hb : b ∈ Submodule.span R t)
    (h : ∀ x ∈ s, ∀ y ∈ t, x * y ∈ Submodule.span R u) : a * b ∈ Submodule.span R u := by
  have hab := Submodule.mul_mem_mul ha hb
  rw [Submodule.span_mul_span] at hab
  refine Submodule.span_le.mpr ?_ hab
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy

theorem bGen_sq (n : Nat) (i : Fin n) : bGen n i ^ 2 = bGen n i := by
  have hmem : (MvPolynomial.X i : Poly n) ^ 2 - MvPolynomial.X i ∈ boolIdeal n :=
    Ideal.subset_span ⟨i, rfl⟩
  have hz : bMk n ((MvPolynomial.X i : Poly n) ^ 2 - MvPolynomial.X i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rwa [map_sub, map_pow, sub_eq_zero] at hz

theorem yGen_sq (n : Nat) (i : Fin n) : yGen n i ^ 2 = 1 := by
  have hmem : (MvPolynomial.X i : Poly n) ^ 2 - 1 ∈ signedIdeal n :=
    Ideal.subset_span ⟨i, rfl⟩
  have hz : dMk n ((MvPolynomial.X i : Poly n) ^ 2 - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rwa [map_sub, map_pow, map_one, sub_eq_zero] at hz

theorem bGen_mul_bMono (n : Nat) (i : Fin n) (S : Finset (Fin n)) :
    bGen n i * bMono n S = bMono n (insert i S) := by
  unfold bMono
  by_cases hi : i ∈ S
  · rw [Finset.insert_eq_of_mem hi, ← Finset.insert_erase hi,
      Finset.prod_insert (Finset.notMem_erase i S), ← mul_assoc, ← pow_two, bGen_sq]
  · rw [Finset.prod_insert hi]

theorem yGen_mul_yMono (n : Nat) (i : Fin n) (S : Finset (Fin n)) :
    yGen n i * yMono n S =
      if i ∈ S then yMono n (S.erase i) else yMono n (insert i S) := by
  unfold yMono
  split_ifs with hi
  · conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.prod_insert (Finset.notMem_erase i S), ← mul_assoc, ← pow_two, yGen_sq,
      one_mul]
  · rw [Finset.prod_insert hi]

theorem bMono_mul (n : Nat) (S T : Finset (Fin n)) :
    bMono n S * bMono n T = bMono n (S ∪ T) := by
  induction S using Finset.induction_on with
  | empty => simp [bMono]
  | insert i S hiS ih =>
    have h : bMono n (insert i S) = bGen n i * bMono n S := Finset.prod_insert hiS
    rw [h, mul_assoc, ih, bGen_mul_bMono, Finset.insert_union]

theorem yMono_mul (n : Nat) (S T : Finset (Fin n)) :
    yMono n S * yMono n T = yMono n ((S \ T) ∪ (T \ S)) := by
  induction S using Finset.induction_on with
  | empty => simp [yMono]
  | insert i S hiS ih =>
    have h : yMono n (insert i S) = yGen n i * yMono n S := Finset.prod_insert hiS
    rw [h, mul_assoc, ih, yGen_mul_yMono]
    by_cases hiT : i ∈ T
    · rw [ite_eq_left (by simp [hiT, hiS])]
      congr 1
      ext j
      by_cases hj : j = i <;> simp [hj, hiT, hiS]
    · rw [ite_eq_right (by simp [hiT, hiS])]
      congr 1
      ext j
      by_cases hj : j = i <;> simp [hj, hiT, hiS]

theorem bMono_mem (n k : Nat) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    bMono n S ∈ BFilter n k := by
  exact Submodule.subset_span ⟨S, hS, rfl⟩

theorem yMono_mem (n k : Nat) (S : Finset (Fin n)) (hS : S.card ≤ k) :
    yMono n S ∈ DFilter n k := by
  exact Submodule.subset_span ⟨S, hS, rfl⟩

theorem bOne_mem (n k : Nat) : (1 : BoolCube n) ∈ BFilter n k := by
  simpa [bMono] using bMono_mem n k ∅ (Nat.zero_le k)

theorem yOne_mem (n k : Nat) : (1 : SignCube n) ∈ DFilter n k := by
  simpa [yMono] using yMono_mem n k ∅ (Nat.zero_le k)

theorem bFilter_mono {n k l : Nat} (hkl : k ≤ l) :
    BFilter n k ≤ BFilter n l :=
  Submodule.span_mono fun _ ⟨S, hS, ha⟩ => ⟨S, hS.trans hkl, ha⟩

theorem yFilter_mono {n k l : Nat} (hkl : k ≤ l) :
    DFilter n k ≤ DFilter n l :=
  Submodule.span_mono fun _ ⟨S, hS, ha⟩ => ⟨S, hS.trans hkl, ha⟩

theorem bGen_mem (n : Nat) (i : Fin n) : bGen n i ∈ BFilter n 1 := by
  simpa [bMono] using bMono_mem n 1 {i} (by simp)

theorem yGen_mem (n : Nat) (i : Fin n) : yGen n i ∈ DFilter n 1 := by
  simpa [yMono] using yMono_mem n 1 {i} (by simp)

theorem bSum_mem (n : Nat) : bSum n ∈ BFilter n 1 :=
  Submodule.sum_mem _ fun i _ => bGen_mem n i

theorem ySum_mem (n : Nat) : ySum n ∈ DFilter n 1 :=
  Submodule.sum_mem _ fun i _ => yGen_mem n i

theorem bMul_mem {n k l : Nat} {a b : BoolCube n}
    (ha : a ∈ BFilter n k) (hb : b ∈ BFilter n l) :
    a * b ∈ BFilter n (k + l) := by
  refine mul_mem_span_of_forall_mem ha hb ?_
  rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩
  rw [bMono_mul]
  exact bMono_mem n _ _ ((Finset.card_union_le S T).trans (add_le_add hS hT))

theorem yMul_mem {n k l : Nat} {a b : SignCube n}
    (ha : a ∈ DFilter n k) (hb : b ∈ DFilter n l) :
    a * b ∈ DFilter n (k + l) := by
  refine mul_mem_span_of_forall_mem ha hb ?_
  rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩
  rw [yMono_mul]
  exact yMono_mem n _ _ <| (Finset.card_union_le _ _).trans <| add_le_add
    ((Finset.card_le_card Finset.sdiff_subset).trans hS)
    ((Finset.card_le_card Finset.sdiff_subset).trans hT)

theorem bSquare_mem {n k : Nat} {a : BoolCube n} (ha : a ∈ BFilter n k) :
    a ^ 2 ∈ BFilter n (2 * k) := by
  simpa [pow_two, two_mul] using bMul_mem ha ha

theorem ySquare_mem {n k : Nat} {a : SignCube n} (ha : a ∈ DFilter n k) :
    a ^ 2 ∈ DFilter n (2 * k) := by
  simpa [pow_two, two_mul] using yMul_mem ha ha

theorem bSlice_mem_one (n : Nat) (r : Real) : bSlice n r ∈ BFilter n 1 := by
  rw [bSlice, Algebra.algebraMap_eq_smul_one]
  exact sub_mem (bSum_mem n) (Submodule.smul_mem _ r (bOne_mem n 1))

theorem ySlice_mem_one (n : Nat) : ySlice n ∈ DFilter n 1 := by
  rw [ySlice, Algebra.algebraMap_eq_smul_one]
  exact sub_mem (ySum_mem n) (Submodule.smul_mem _ _ (yOne_mem n 1))

theorem bSlice_mem {n k Dg : Nat} (r : Real) (hk : k + 1 ≤ Dg)
    {a : BoolCube n} (ha : a ∈ BFilter n k) :
    bSlice n r * a ∈ BFilter n Dg :=
  bFilter_mono (by omega) (bMul_mem (bSlice_mem_one n r) ha)

theorem ySlice_mem {n k Dg : Nat} (hk : k + 1 ≤ Dg)
    {a : SignCube n} (ha : a ∈ DFilter n k) :
    ySlice n * a ∈ DFilter n Dg :=
  yFilter_mono (by omega) (yMul_mem (ySlice_mem_one n) ha)

theorem yGen_pow_even (n : Nat) (i : Fin n) (k : Nat) :
    yGen n i ^ (2 * k) = 1 := by
  rw [pow_mul, yGen_sq, one_pow]

theorem yGen_pow_odd (n : Nat) (i : Fin n) (k : Nat) :
    yGen n i ^ (2 * k + 1) = yGen n i := by
  rw [pow_succ, yGen_pow_even, one_mul]

/-- Powers of an element of filtration degree `k` have filtration degree `k * m`. -/
theorem yPow_mem {n k : Nat} {a : SignCube n} (ha : a ∈ DFilter n k) (m : Nat) :
    a ^ m ∈ DFilter n (k * m) := by
  induction m with
  | zero => simpa using yOne_mem n 0
  | succ m ih => rw [pow_succ, Nat.mul_succ]; exact yMul_mem ih ha

/-- Finite products in the signed quotient add filtration degrees. -/
theorem yProd_mem {n : Nat} {ι : Type*} (s : Finset ι) (f : ι → SignCube n) (m : ι → Nat)
    (h : ∀ i ∈ s, f i ∈ DFilter n (m i)) : ∏ i ∈ s, f i ∈ DFilter n (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using yOne_mem n 0
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact yMul_mem (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The image of a monomial with exponent vector `e` has filtration degree `e.degree`. -/
theorem dMk_monomial_mem (n : Nat) (e : Fin n →₀ ℕ) (c : ℝ) :
    dMk n (MvPolynomial.monomial e c) ∈ DFilter n e.degree := by
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.algHom_C, Finsupp.prod, map_prod,
    ← Algebra.smul_def, Finsupp.degree_apply]
  refine Submodule.smul_mem _ c (yProd_mem _ _ _ fun i _ => ?_)
  rw [map_pow]
  simpa only [yGen, Nat.one_mul] using yPow_mem (yGen_mem n i) (e i)

theorem dMk_mem {n k : Nat} (q : Poly n) (hq : q.totalDegree ≤ k) :
    dMk n q ∈ DFilter n k := by
  rw [q.as_sum, map_sum]
  exact Submodule.sum_mem _ fun e he =>
    yFilter_mono ((MvPolynomial.le_totalDegree he).trans hq) (dMk_monomial_mem n e _)

theorem ySum_pow_mem_self (n j : Nat) : ySum n ^ j ∈ DFilter n j := by
  simpa using yPow_mem (ySum_mem n) j

theorem ySum_pow_mem {n K j : Nat} (hj : j ≤ K) :
    ySum n ^ j ∈ DFilter n K :=
  yFilter_mono hj (ySum_pow_mem_self n j)

theorem ySum_poly_mem {n K : Nat} (P : Polynomial Real) (hP : P.natDegree ≤ K) :
    Polynomial.aeval (ySum n) P ∈ DFilter n K := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP)]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (ySum_pow_mem (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

end AnyDim.Elementary
end
