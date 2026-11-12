module

public import AnyDim.Counterexample.Elementary.Cubes

/-!
# A pseudo-expectation on the Boolean cube (elementary route)

For `n ≥ 4d` there is a linear functional `L` on the functions of degree `≤ 2d` on `{0,1}^n`
(`BooleanMoments n d`) which behaves like "evaluation at a point of Hamming weight
`n/2 + 1/4`": `L(1) = 1`, `L` vanishes on multiples of `∑ X_i - (n/2 + 1/4)` and
`L(q²) ≥ 0` for `deg q ≤ d` (`boolean_square_nonneg`).  The positivity is proved by an explicit
Gram matrix decomposition into incidence matrices with nonnegative coefficients
(`gramForm_decomposition`, `gramCoefficient_nonneg`).

This is a Grigoriev-type lower bound; it replaces Blekherman's theorem (Theorem 3.2 of the
paper) in the elementary route, at the cost of the stronger assumption `n ≥ 4d` instead of
`n ≥ 2d`.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim.Elementary

def falling (r : Real) (k : Nat) : Real :=
  (Finset.range k).prod (fun j => r - (j : Real))

def realChoose (r : Real) (k : Nat) : Real := falling r k / (k.factorial : Real)

def boolMoment (n k : Nat) : Real :=
  falling (fractionalCardinality n) k / falling (n : Real) k

theorem falling_succ (r : Real) (k : Nat) :
    falling r (k + 1) = falling r k * (r - (k : Real)) :=
  Finset.prod_range_succ _ _

theorem falling_pos (r : Real) (k : Nat) (hk : (k : Real) ≤ r) :
    0 < falling r k :=
  Finset.prod_pos fun j hj => by
    have : (j : Real) < k := by exact_mod_cast Finset.mem_range.mp hj
    linarith

theorem boolMoment_succ {n s : Nat} (hs : s < n) :
    boolMoment n (s + 1) = boolMoment n s *
      (fractionalCardinality n - (s : Real)) / ((n : Real) - (s : Real)) := by
  have hsn : (s : Real) < n := by exact_mod_cast hs
  have h₁ : falling (n : Real) s ≠ 0 := (falling_pos _ _ hsn.le).ne'
  have h₂ : (n : Real) - s ≠ 0 := (sub_pos.mpr hsn).ne'
  simp only [boolMoment, falling_succ]
  field_simp

/-- Boolean evaluation at the indicator of a finite set. -/
def booleanPoint (n : Nat) (V : Finset (Fin n)) : Fin n → Real :=
  fun i => if i ∈ V then 1 else 0

theorem booleanPoint_kills (n : Nat) (V : Finset (Fin n)) :
    ∀ a ∈ boolIdeal n, MvPolynomial.aeval (booleanPoint n V) a = 0 := by
  intro a ha
  refine (Ideal.span_le (I := RingHom.ker (MvPolynomial.aeval (booleanPoint n V)))).mpr ?_ ha
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  by_cases hi : i ∈ V <;> simp [booleanPoint, hi]

def booleanEval (n : Nat) (V : Finset (Fin n)) : AlgHom Real (BoolCube n) Real :=
  Ideal.Quotient.liftₐ (boolIdeal n) (MvPolynomial.aeval (booleanPoint n V))
    (booleanPoint_kills n V)

theorem booleanEval_bMono (n : Nat) (V S : Finset (Fin n)) :
    booleanEval n V (bMono n S) = if S ⊆ V then 1 else 0 := by
  simp [bMono, bGen, bMk, booleanEval, booleanPoint, Finset.prod_boole, Finset.subset_iff]

/-- A coefficient extractor defined by Boolean inclusion-exclusion. -/
def booleanCoefficient (n : Nat) (S : Finset (Fin n)) : BoolCube n →ₗ[Real] Real :=
  S.powerset.sum (fun V => ((-1 : Real) ^ (S.card - V.card)) •
    (booleanEval n V).toLinearMap)

/-- `(-1) ^ (a - b) = (-1) ^ a * (-1) ^ b` for natural `b ≤ a`. -/
theorem neg_one_pow_sub_of_le {R : Type*} [Ring R] {a b : ℕ} (h : b ≤ a) :
    (-1 : R) ^ (a - b) = (-1) ^ a * (-1) ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add]
  rcases neg_one_pow_eq_or R b with h | h <;> simp [h]

open Finset in
/-- Inclusion-exclusion over the interval `[T, S]` of the subset lattice:
`∑_{T ⊆ V ⊆ S} (-1) ^ (|S| - |V|) = [S = T]`. -/
theorem sum_powerset_superset_neg_one_pow {α : Type*} [DecidableEq α] (S T : Finset α) :
    ∑ V ∈ S.powerset, (if T ⊆ V then (-1 : ℝ) ^ (S.card - V.card) else 0) =
      if S = T then 1 else 0 := by
  by_cases hTS : T ⊆ S
  · rw [← Finset.sum_filter]
    have himage : S.powerset.filter (T ⊆ ·) = (S \ T).powerset.image (· ∪ T) := by
      ext V
      simp only [mem_filter, mem_powerset, mem_image]
      constructor
      · rintro ⟨hVS, hTV⟩
        exact ⟨V \ T, sdiff_subset_sdiff hVS Subset.rfl, sdiff_union_of_subset hTV⟩
      · rintro ⟨W, hW, rfl⟩
        exact ⟨union_subset (hW.trans sdiff_subset) hTS, subset_union_right⟩
    have hinj : Set.InjOn (· ∪ T) ((S \ T).powerset : Set (Finset α)) := by
      intro W₁ h₁ W₂ h₂ h
      simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at h₁ h₂
      rw [← union_sdiff_cancel_right (disjoint_of_subset_left h₁ sdiff_disjoint),
        ← union_sdiff_cancel_right (disjoint_of_subset_left h₂ sdiff_disjoint)]
      exact congrArg (· \ T) h
    rw [himage, sum_image hinj]
    have hterm : ∀ W ∈ (S \ T).powerset,
        (-1 : ℝ) ^ (S.card - (W ∪ T).card) = (-1) ^ (S \ T).card * (-1) ^ W.card := by
      intro W hW
      rw [mem_powerset] at hW
      rw [card_union_of_disjoint (disjoint_of_subset_left hW sdiff_disjoint),
        ← card_sdiff_add_card_eq_card hTS, Nat.add_sub_add_right,
        neg_one_pow_sub_of_le (card_le_card hW)]
    have hsum : ∑ W ∈ (S \ T).powerset, (-1 : ℝ) ^ W.card = if S \ T = ∅ then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := S \ T))
      push_cast at this
      rw [this]
    rw [sum_congr rfl hterm, ← mul_sum, hsum]
    by_cases hST : S ⊆ T
    · simp [subset_antisymm hST hTS]
    · rw [ite_eq_right (by rwa [sdiff_eq_empty_iff_subset]), ite_eq_right (fun h => hST h.le), mul_zero]
  · rw [ite_eq_right (fun h => hTS h.ge)]
    refine sum_eq_zero fun V hV => ite_eq_right fun hTV => hTS (hTV.trans (mem_powerset.mp hV))

theorem booleanCoefficient_bMono (n : Nat) (S T : Finset (Fin n)) :
    booleanCoefficient n S (bMono n T) = if S = T then 1 else 0 := by
  simp only [booleanCoefficient, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, booleanEval_bMono, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact sum_powerset_superset_neg_one_pow S T

def booleanMomentMap (n : Nat) : BoolCube n →ₗ[Real] Real :=
  Finset.univ.sum (fun S : Finset (Fin n) =>
    boolMoment n S.card • booleanCoefficient n S)

structure BooleanMoments (n d : Nat) where
  L : LinearMap (RingHom.id Real) (BFilter n (2 * d)) Real
  on_monomial : ∀ (S : Finset (Fin n)) (hS : S.card ≤ 2 * d),
    L ⟨bMono n S, bMono_mem n (2 * d) S hS⟩ = boolMoment n S.card

theorem booleanMoments_exists (n d : Nat) : Nonempty (BooleanMoments n d) :=
  ⟨{ L := (booleanMomentMap n).comp (BFilter n (2 * d)).subtype
     on_monomial := fun S _ => by
       simp [booleanMomentMap, booleanCoefficient_bMono] }⟩

theorem booleanMoments_one {n d : Nat} (M : BooleanMoments n d) :
    M.L ⟨1, bOne_mem n (2 * d)⟩ = 1 := by
  simpa [bMono, boolMoment, falling] using M.on_monomial ∅ (Nat.zero_le _)

theorem boolMoment_recurrence {n s : Nat} (hs : s < n) :
    (s : Real) * boolMoment n s + ((n - s : Nat) : Real) * boolMoment n (s + 1) =
      fractionalCardinality n * boolMoment n s := by
  have h : (n : Real) - s ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hs.ne')
  rw [boolMoment_succ hs, Nat.cast_sub hs.le]
  field_simp
  ring

theorem bSum_mul_monomial (n : Nat) (S : Finset (Fin n)) :
    bSum n * bMono n S =
      (S.card : Real) • bMono n S +
      (Finset.univ \ S).sum (fun i => bMono n (insert i S)) := by
  rw [bSum, Finset.sum_mul, ← Finset.sum_sdiff (Finset.subset_univ S), add_comm]
  congr 1
  · rw [Finset.sum_congr rfl fun i hi => by rw [bGen_mul_bMono, Finset.insert_eq_of_mem hi],
      Finset.sum_const, Nat.cast_smul_eq_nsmul]
  · exact Finset.sum_congr rfl fun i _ => bGen_mul_bMono n i S

section SubmoduleFunctional

variable {M : Type*} [AddCommGroup M] [Module Real M] {p : Submodule Real M}
  (L : p →ₗ[Real] Real)

/-- A functional on a submodule only depends on the underlying element. -/
theorem linearMap_mk_congr {x y : M} (hxy : x = y) (hx : x ∈ p) (hy : y ∈ p) :
    L ⟨x, hx⟩ = L ⟨y, hy⟩ := by
  subst hxy; rfl

/-- Additivity of a functional on a submodule, stated on underlying elements. -/
theorem linearMap_mk_add {x y : M} (hx : x ∈ p) (hy : y ∈ p) (h : x + y ∈ p) :
    L ⟨x + y, h⟩ = L ⟨x, hx⟩ + L ⟨y, hy⟩ := by
  rw [← map_add]; rfl

/-- Subtractivity of a functional on a submodule, stated on underlying elements. -/
theorem linearMap_mk_sub {x y : M} (hx : x ∈ p) (hy : y ∈ p) (h : x - y ∈ p) :
    L ⟨x - y, h⟩ = L ⟨x, hx⟩ - L ⟨y, hy⟩ := by
  rw [← map_sub]; rfl

/-- Homogeneity of a functional on a submodule, stated on underlying elements. -/
theorem linearMap_mk_smul (a : Real) {x : M} (hx : x ∈ p) (h : a • x ∈ p) :
    L ⟨a • x, h⟩ = a * L ⟨x, hx⟩ := by
  rw [← smul_eq_mul, ← map_smul]; rfl

/-- A functional on a submodule commutes with finite sums of underlying elements. -/
theorem linearMap_mk_sum {ι : Type*} (s : Finset ι) (f : ι → M) (hf : ∀ i, f i ∈ p)
    (h : ∑ i ∈ s, f i ∈ p) :
    L ⟨∑ i ∈ s, f i, h⟩ = ∑ i ∈ s, L ⟨f i, hf i⟩ := by
  rw [← map_sum]
  congr 1
  ext
  simp

end SubmoduleFunctional

/-- `boolean_slice_zero` for a single squarefree monomial. -/
theorem boolean_slice_zero_bMono {n d : Nat} (M : BooleanMoments n d)
    (hnd : 2 * d ≤ n) (S : Finset (Fin n)) (hS : S.card + 1 ≤ 2 * d) :
    M.L ⟨bSlice n (fractionalCardinality n) * bMono n S,
      bSlice_mem (fractionalCardinality n) hS (bMono_mem n S.card S le_rfl)⟩ = 0 := by
  have hmem : ∀ i, bMono n (insert i S) ∈ BFilter n (2 * d) := fun i =>
    bMono_mem n _ _ ((Finset.card_insert_le i S).trans hS)
  have hS' : bMono n S ∈ BFilter n (2 * d) := bMono_mem n _ _ (by omega)
  have key : bSlice n (fractionalCardinality n) * bMono n S =
      ((S.card : Real) - fractionalCardinality n) • bMono n S +
        (Finset.univ \ S).sum (fun i => bMono n (insert i S)) := by
    rw [bSlice, sub_mul, bSum_mul_monomial, ← Algebra.smul_def, sub_smul]
    abel
  rw [linearMap_mk_congr M.L key _ (add_mem (Submodule.smul_mem _ _ hS') (Submodule.sum_mem _
      fun i _ => hmem i)), linearMap_mk_add M.L (Submodule.smul_mem _ _ hS')
      (Submodule.sum_mem _ fun i _ => hmem i), linearMap_mk_smul M.L _ hS',
    linearMap_mk_sum M.L _ _ hmem, M.on_monomial S (by omega),
    Finset.sum_congr rfl fun i _ =>
      M.on_monomial (insert i S) ((Finset.card_insert_le i S).trans hS)]
  have hcard : ∀ i ∈ Finset.univ \ S, (insert i S).card = S.card + 1 := fun i hi =>
    Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hi).2
  rw [Finset.sum_congr rfl fun i hi => by rw [hcard i hi], Finset.sum_const,
    ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]
  have := boolMoment_recurrence (n := n) (s := S.card) (by omega)
  linarith

/-- The functional `M.L` vanishes on multiples of the slice `bSlice n r` of low degree.
The hypothesis `_hd` is not needed for this proof; it is kept to match the stated interface. -/
theorem boolean_slice_zero {n d k : Nat} (M : BooleanMoments n d)
    (_hd : 1 ≤ d) (hnd : 4 * d ≤ n) (hk : k + 1 ≤ 2 * d)
    (a : BoolCube n) (ha : a ∈ BFilter n k) :
    M.L ⟨bSlice n (fractionalCardinality n) * a,
      bSlice_mem (fractionalCardinality n) hk ha⟩ = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    exact boolean_slice_zero_bMono M (by omega) S (by omega)
  | zero =>
    rw [linearMap_mk_congr M.L (mul_zero _) _ (zero_mem _)]
    exact map_zero M.L
  | add x y hx hy ihx ihy =>
    rw [linearMap_mk_congr M.L (mul_add _ x y) _
      (add_mem (bSlice_mem _ hk hx) (bSlice_mem _ hk hy)),
      linearMap_mk_add M.L (bSlice_mem _ hk hx) (bSlice_mem _ hk hy), ihx, ihy, add_zero]
  | smul a x hx ihx =>
    rw [linearMap_mk_congr M.L (mul_smul_comm a _ x) _
      (Submodule.smul_mem _ a (bSlice_mem _ hk hx)),
      linearMap_mk_smul M.L a (bSlice_mem _ hk hx), ihx, mul_zero]

abbrev Level (n d : Nat) := {S : Finset (Fin n) // S.card = d}

def levelCombination {n d : Nat} (c : Level n d → Real) : BoolCube n :=
  Finset.univ.sum (fun S : Level n d => c S • bMono n S.val)

theorem levelCombination_mem {n d : Nat} (c : Level n d → Real) :
    levelCombination c ∈ BFilter n d :=
  Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (bMono_mem n d S.val S.property.le)

/-- The element binom(w,k), defined in an arbitrary real algebra. -/
def binomElement {R : Type*} [CommRing R] [Algebra Real R] (w : R) (k : Nat) : R :=
  (1 / (k.factorial : Real)) •
    (Finset.range k).prod (fun j => w - algebraMap Real R (j : Real))

def homogenizedMonomial (n d : Nat) (S : Finset (Fin n)) : BoolCube n :=
  (1 / realChoose (fractionalCardinality n - (S.card : Real)) (d - S.card)) •
    Finset.univ.sum (fun T : Level n d => if S ≤ T.val then bMono n T.val else 0)

/-- Every filtration level is contained in level `n`, since a subset of `Fin n` has at most
`n` elements. -/
theorem bFilter_le_top_level (n k : Nat) : BFilter n k ≤ BFilter n n :=
  Submodule.span_mono fun _ ⟨S, _, h⟩ =>
    ⟨S, (Finset.card_le_univ S).trans (Fintype.card_fin n).le, h⟩

/-- The squarefree monomials span `BoolCube n`. -/
theorem mem_bFilter_top (n : Nat) (x : BoolCube n) : x ∈ BFilter n n := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change bMk n p ∈ BFilter n n
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (bOne_mem n n)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    exact bFilter_le_top_level n (n + 1) (bMul_mem hp (bGen_mem n i))

/-- Expansion of an element of `BoolCube n` in the squarefree monomials, with coefficients given by
`booleanCoefficient`. -/
theorem eq_sum_booleanCoefficient_smul (n : Nat) (x : BoolCube n) :
    x = Finset.univ.sum (fun S => booleanCoefficient n S x • bMono n S) := by
  induction mem_bFilter_top n x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, -, rfl⟩ := hx
    simp [booleanCoefficient_bMono]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul a x _ hx =>
    simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← hx]

/-- Elements of `BoolCube n` are determined by their values at all Boolean points. -/
theorem eq_of_booleanEval_eq {n : Nat} {x y : BoolCube n}
    (h : ∀ V, booleanEval n V x = booleanEval n V y) : x = y := by
  rw [eq_sum_booleanCoefficient_smul n x, eq_sum_booleanCoefficient_smul n y]
  simp [booleanCoefficient, h]

/-- Boolean evaluation of `bSum n` counts the points of `V`. -/
theorem booleanEval_bSum (n : Nat) (V : Finset (Fin n)) :
    booleanEval n V (bSum n) = V.card := by
  simp [bSum, bGen, bMk, booleanEval, booleanPoint]

/-- Real algebra homomorphisms commute with `binomElement`. -/
theorem map_binomElement {R S : Type*} [CommRing R] [Algebra Real R] [CommRing S]
    [Algebra Real S] (f : R →ₐ[Real] S) (w : R) (k : Nat) :
    f (binomElement w k) = binomElement (f w) k := by
  simp [binomElement, map_prod]

/-- In `ℝ`, `binomElement` is `realChoose`. -/
theorem binomElement_real (x : Real) (k : Nat) : binomElement x k = realChoose x k := by
  simp [binomElement, realChoose, falling, div_eq_inv_mul]

/-- At a natural number, `falling` is the descending factorial. -/
theorem falling_natCast (m k : Nat) : falling (m : Real) k = m.descFactorial k := by
  induction k with
  | zero => simp [falling]
  | succ k ih =>
    rw [falling_succ, ih, Nat.descFactorial_succ]
    by_cases hkm : k ≤ m
    · push_cast [Nat.cast_sub hkm]
      ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp

/-- At a natural number, `realChoose` is the binomial coefficient. -/
theorem realChoose_natCast (m k : Nat) : realChoose (m : Real) k = m.choose k := by
  rw [realChoose, falling_natCast, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- The number of `d`-subsets `T` with `S ⊆ T ⊆ V`. -/
theorem card_filter_powersetCard_between {α : Type*} [Fintype α] [DecidableEq α]
    {S V : Finset α} {d : Nat} (hSV : S ⊆ V) (hS : S.card ≤ d) :
    ((Finset.powersetCard d Finset.univ).filter (fun T => S ⊆ T ∧ T ⊆ V)).card =
      (V.card - S.card).choose (d - S.card) := by
  have himage : (Finset.powersetCard d Finset.univ).filter (fun T => S ⊆ T ∧ T ⊆ V) =
      (Finset.powersetCard (d - S.card) (V \ S)).image (· ∪ S) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hT, hST, hTV⟩
      refine ⟨T \ S, ⟨Finset.sdiff_subset_sdiff hTV Finset.Subset.rfl, ?_⟩,
        Finset.sdiff_union_of_subset hST⟩
      rw [Finset.card_sdiff_of_subset hST, hT]
    · rintro ⟨W, ⟨hWV, hW⟩, rfl⟩
      have hdisj : Disjoint W S := Finset.disjoint_of_subset_left hWV Finset.sdiff_disjoint
      refine ⟨by rw [Finset.card_union_of_disjoint hdisj, hW]; omega,
        Finset.subset_union_right, Finset.union_subset (hWV.trans Finset.sdiff_subset) hSV⟩
  have hinj : Set.InjOn (· ∪ S) (Finset.powersetCard (d - S.card) (V \ S) : Set (Finset α)) := by
    intro W₁ h₁ W₂ h₂ h
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at h₁ h₂
    rw [← Finset.union_sdiff_cancel_right
        (Finset.disjoint_of_subset_left h₁.1 Finset.sdiff_disjoint),
      ← Finset.union_sdiff_cancel_right
        (Finset.disjoint_of_subset_left h₂.1 Finset.sdiff_disjoint)]
    exact congrArg (· \ S) h
  rw [himage, Finset.card_image_of_injOn hinj, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hSV]

theorem lifting_count_identity {n d : Nat} (S : Finset (Fin n)) (hS : S.card ≤ d) :
    Finset.univ.sum (fun T : Level n d => if S ≤ T.val then bMono n T.val else 0) =
      bMono n S * binomElement
        (bSum n - algebraMap Real (BoolCube n) (S.card : Real)) (d - S.card) := by
  refine eq_of_booleanEval_eq fun V => ?_
  rw [map_sum, map_mul, booleanEval_bMono, map_binomElement, map_sub, booleanEval_bSum,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, binomElement_real]
  simp only [apply_ite (booleanEval n V), map_zero, booleanEval_bMono]
  by_cases hSV : S ⊆ V
  · rw [ite_eq_left hSV, one_mul, ← Nat.cast_sub (Finset.card_le_card hSV), realChoose_natCast,
      ← card_filter_powersetCard_between hSV hS, Finset.card_filter, Nat.cast_sum,
      Finset.sum_subtype (Finset.powersetCard d Finset.univ) (p := fun T => T.card = d)
        (by simp [Finset.mem_powersetCard])]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h₁ : S ⊆ T.val <;> by_cases h₂ : T.val ⊆ V <;> simp [h₁, h₂]
  · rw [ite_eq_right hSV, zero_mul]
    refine Finset.sum_eq_zero fun T _ => ?_
    by_cases h₁ : S ⊆ T.val
    · rw [ite_eq_left h₁, ite_eq_right fun h₂ => hSV (h₁.trans h₂)]
    · rw [ite_eq_right h₁]

/-- Powers of an element of filtration degree `k` have filtration degree `k * m`. -/
theorem bPow_mem {n k : Nat} {a : BoolCube n} (ha : a ∈ BFilter n k) (m : Nat) :
    a ^ m ∈ BFilter n (k * m) := by
  induction m with
  | zero => simpa using bOne_mem n 0
  | succ m ih => rw [pow_succ, Nat.mul_succ]; exact bMul_mem ih ha

/-- A real polynomial of degree at most `K` evaluated at `bSum n` has filtration degree `K`. -/
theorem bSum_poly_mem {n K : Nat} (P : Polynomial Real) (hP : P.natDegree ≤ K) :
    Polynomial.aeval (bSum n) P ∈ BFilter n K := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP)]
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
  exact bFilter_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    (by simpa using bPow_mem (bSum_mem n) j)

open Polynomial in
/-- The polynomial `X ↦ binom(X - s, k)` as an element of `ℝ[X]`. -/
def shiftedBinomPoly (s : Real) (k : Nat) : Polynomial Real :=
  C (1 / (k.factorial : Real)) * (Finset.range k).prod (fun j => X - C (s + j))

open Polynomial in
/-- Evaluating `shiftedBinomPoly s k` at `w` gives `binom(w - s, k)`. -/
theorem aeval_shiftedBinomPoly {R : Type*} [CommRing R] [Algebra Real R] (w : R) (s : Real)
    (k : Nat) :
    aeval w (shiftedBinomPoly s k) = binomElement (w - algebraMap Real R s) k := by
  simp [shiftedBinomPoly, binomElement, map_prod, Algebra.smul_def, sub_sub]

open Polynomial in
/-- Evaluating `shiftedBinomPoly s k` at a real `r` gives `realChoose (r - s) k`. -/
theorem eval_shiftedBinomPoly (r s : Real) (k : Nat) :
    (shiftedBinomPoly s k).eval r = realChoose (r - s) k := by
  simp [shiftedBinomPoly, realChoose, falling, eval_prod, sub_sub, div_eq_inv_mul]

open Polynomial in
/-- `shiftedBinomPoly s k` has degree at most `k`. -/
theorem natDegree_shiftedBinomPoly_le (s : Real) (k : Nat) :
    (shiftedBinomPoly s k).natDegree ≤ k := by
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun j _ => natDegree_X_sub_C_le (R := Real) _).trans ?_
  simp

open Polynomial in
/-- If `P` has degree at most `k`, then `P - P(r) = (X - r) Q` with `deg Q ≤ k - 1`. -/
theorem exists_sub_eval_eq_mul (P : Polynomial Real) (r : Real) {k : Nat}
    (hP : P.natDegree ≤ k) :
    ∃ Q : Polynomial Real, Q.natDegree ≤ k - 1 ∧ P - C (P.eval r) = (X - C r) * Q := by
  refine ⟨(P - C (P.eval r)) /ₘ (X - C r), ?_, ?_⟩
  · rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, natDegree_sub_C]
    omega
  · exact (mul_divByMonic_eq_iff_isRoot.mpr (by simp)).symm

/-- `realChoose r k` is positive when `k ≤ r`. -/
theorem realChoose_pos {r : Real} {k : Nat} (hk : (k : Real) ≤ r) : 0 < realChoose r k :=
  div_pos (falling_pos r k hk) (by exact_mod_cast k.factorial_pos)

theorem homogenizedMonomial_difference {n d : Nat}
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    ∃ R : BoolCube n, R ∈ BFilter n (d - 1) ∧
      homogenizedMonomial n d S - bMono n S =
        bSlice n (fractionalCardinality n) * R := by
  set r := fractionalCardinality n
  set s := S.card
  set k := d - s with hk
  set c := realChoose (r - s) k with hcdef
  have hc : c ≠ 0 := by
    refine (realChoose_pos ?_).ne'
    have : (4 * d : Real) ≤ n := by exact_mod_cast hnd
    rw [hk, Nat.cast_sub hS]
    simp only [r, fractionalCardinality]
    linarith
  have hhom : homogenizedMonomial n d S =
      c⁻¹ • (bMono n S * Polynomial.aeval (bSum n) (shiftedBinomPoly s k)) := by
    rw [homogenizedMonomial, lifting_count_identity S hS, aeval_shiftedBinomPoly, one_div]
  obtain ⟨Q, hQdeg, hQ⟩ := exists_sub_eval_eq_mul (shiftedBinomPoly s k) r
    (natDegree_shiftedBinomPoly_le s k)
  rw [eval_shiftedBinomPoly, ← hcdef, sub_eq_iff_eq_add] at hQ
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · refine ⟨0, zero_mem _, ?_⟩
    rw [hhom, hk0, mul_zero, sub_eq_zero]
    simp [c, hk0, shiftedBinomPoly, realChoose, falling]
  · refine ⟨c⁻¹ • (bMono n S * Polynomial.aeval (bSum n) Q), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ ?_
      have := bMul_mem (bMono_mem n s S le_rfl) (bSum_poly_mem (n := n) Q hQdeg)
      rwa [show s + (k - 1) = d - 1 by omega] at this
    · rw [hhom, hQ, map_add, map_mul, Polynomial.aeval_C, map_sub, Polynomial.aeval_X,
        Polynomial.aeval_C, bSlice]
      have key : bMono n S * ((bSum n - algebraMap Real (BoolCube n) r) * Polynomial.aeval (bSum n) Q +
            algebraMap Real (BoolCube n) c) =
          (bSum n - algebraMap Real (BoolCube n) r) * (bMono n S * Polynomial.aeval (bSum n) Q) +
            algebraMap Real (BoolCube n) c * bMono n S := by
        ring
      rw [key, ← Algebra.smul_def, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul,
        mul_smul_comm, add_sub_cancel_right]

/-- `levelCombination` is linear in the coefficients: zero. -/
theorem levelCombination_zero (n d : Nat) : levelCombination (0 : Level n d → Real) = 0 := by
  simp [levelCombination]

/-- `levelCombination` is linear in the coefficients: addition. -/
theorem levelCombination_add {n d : Nat} (c₁ c₂ : Level n d → Real) :
    levelCombination (c₁ + c₂) = levelCombination c₁ + levelCombination c₂ := by
  simp [levelCombination, add_smul, Finset.sum_add_distrib]

/-- `levelCombination` is linear in the coefficients: scalars. -/
theorem levelCombination_smul {n d : Nat} (a : Real) (c : Level n d → Real) :
    levelCombination (a • c) = a • levelCombination c := by
  simp [levelCombination, mul_smul, Finset.smul_sum]

/-- `homogenizedMonomial n d S` is a combination of level-`d` monomials. -/
theorem homogenizedMonomial_eq_levelCombination (n d : Nat) (S : Finset (Fin n)) :
    homogenizedMonomial n d S = levelCombination (fun T : Level n d =>
      (1 / realChoose (fractionalCardinality n - (S.card : Real)) (d - S.card)) *
        if S ≤ T.val then 1 else 0) := by
  rw [homogenizedMonomial, levelCombination, Finset.smul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

theorem homogenize_element {n d : Nat} (hd : 1 ≤ d) (hnd : 4 * d ≤ n)
    (q : BoolCube n) (hq : q ∈ BFilter n d) :
    ∃ (c : Level n d → Real) (R : BoolCube n),
      R ∈ BFilter n (d - 1) ∧
      q - levelCombination c = bSlice n (fractionalCardinality n) * R := by
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    obtain ⟨R, hR, hEq⟩ := homogenizedMonomial_difference hd hnd S hS
    refine ⟨fun T => (1 / realChoose (fractionalCardinality n - (S.card : Real)) (d - S.card)) *
      if S ≤ T.val then 1 else 0, (-1 : Real) • R, Submodule.smul_mem _ _ hR, ?_⟩
    rw [← homogenizedMonomial_eq_levelCombination, mul_smul_comm, ← hEq, neg_one_smul, neg_sub]
  | zero => exact ⟨0, 0, zero_mem _, by simp [levelCombination_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, R₁, hR₁, h₁⟩ := hx
    obtain ⟨c₂, R₂, hR₂, h₂⟩ := hy
    refine ⟨c₁ + c₂, R₁ + R₂, add_mem hR₁ hR₂, ?_⟩
    rw [levelCombination_add, mul_add, ← h₁, ← h₂]
    abel
  | smul a x _ hx =>
    obtain ⟨c, R, hR, h⟩ := hx
    refine ⟨a • c, a • R, Submodule.smul_mem _ a hR, ?_⟩
    rw [levelCombination_smul, ← smul_sub, h, mul_smul_comm]

theorem homogenize_square {n d : Nat} (M : BooleanMoments n d)
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n)
    (q : BoolCube n) (hq : q ∈ BFilter n d) :
    ∃ c : Level n d → Real,
      M.L ⟨q ^ 2, bSquare_mem hq⟩ =
      M.L ⟨levelCombination c ^ 2, bSquare_mem (levelCombination_mem c)⟩ := by
  obtain ⟨c, R, hR, hEq⟩ := homogenize_element hd hnd q hq
  refine ⟨c, ?_⟩
  have hH := levelCombination_mem c
  have hRqH : R * (q + levelCombination c) ∈ BFilter n (d - 1 + d) := bMul_mem hR (add_mem hq hH)
  have hk : d - 1 + d + 1 ≤ 2 * d := by omega
  have key : q ^ 2 - levelCombination c ^ 2 =
      bSlice n (fractionalCardinality n) * (R * (q + levelCombination c)) := by
    rw [← mul_assoc, ← hEq]
    ring
  rw [← sub_eq_zero, ← linearMap_mk_sub M.L _ _ (sub_mem (bSquare_mem hq) (bSquare_mem hH)),
    linearMap_mk_congr M.L key _ (bSlice_mem _ hk hRqH)]
  exact boolean_slice_zero M hd hnd hk _ hRqH

def gramEntry (n d : Nat) (S T : Level n d) : Real :=
  boolMoment n (2 * d - (S.val ∩ T.val).card)

def incidenceEntry (n d j : Nat) (S T : Level n d) : Real :=
  (Nat.choose (S.val ∩ T.val).card j : Real)

def gramCoefficient (n d j : Nat) : Real :=
  falling ((n : Real) - fractionalCardinality n) j *
    falling (fractionalCardinality n) (2 * d - j) / falling (n : Real) (2 * d)

def gramForm {n d : Nat} (c : Level n d → Real) : Real :=
  Finset.univ.sum (fun S : Level n d =>
    Finset.univ.sum (fun T : Level n d => c S * c T * gramEntry n d S T))

def incidenceForm {n d : Nat} (j : Nat) (c : Level n d → Real) : Real :=
  Finset.univ.sum (fun S : Level n d =>
    Finset.univ.sum (fun T : Level n d => c S * c T * incidenceEntry n d j S T))

/-- Expansion of the square of a level combination into squarefree monomials. -/
theorem levelCombination_sq {n d : Nat} (c : Level n d → Real) :
    levelCombination c ^ 2 = Finset.univ.sum (fun S : Level n d =>
      Finset.univ.sum (fun T : Level n d => (c S * c T) • bMono n (S.val ∪ T.val))) := by
  simp only [levelCombination, sq, Finset.sum_mul_sum, smul_mul_smul_comm, bMono_mul]

theorem moment_level_square {n d : Nat} (M : BooleanMoments n d)
    (c : Level n d → Real) :
    M.L ⟨levelCombination c ^ 2, bSquare_mem (levelCombination_mem c)⟩ =
      gramForm c := by
  have hcard : ∀ S T : Level n d, (S.val ∪ T.val).card ≤ 2 * d := fun S T =>
    (Finset.card_union_le _ _).trans (by rw [S.property, T.property, two_mul])
  have hmem : ∀ S T : Level n d, (c S * c T) • bMono n (S.val ∪ T.val) ∈ BFilter n (2 * d) :=
    fun S T => Submodule.smul_mem _ _ (bMono_mem n _ _ (hcard S T))
  rw [linearMap_mk_congr M.L (levelCombination_sq c) _
      (Submodule.sum_mem _ fun S _ => Submodule.sum_mem _ fun T _ => hmem S T),
    linearMap_mk_sum M.L _ _ fun S => Submodule.sum_mem _ fun T _ => hmem S T]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [linearMap_mk_sum M.L _ _ (hmem S)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [linearMap_mk_smul M.L _ (bMono_mem n _ _ (hcard S T)), M.on_monomial _ (hcard S T), gramEntry]
  have := Finset.card_union_add_card_inter S.val T.val
  rw [S.property, T.property] at this
  rw [show (S.val ∪ T.val).card = 2 * d - (S.val ∩ T.val).card by omega]

def forwardDifference : Nat → (Nat → Real) → Nat → Real
  | 0, h => h
  | j + 1, h => fun l => forwardDifference j h (l + 1) - forwardDifference j h l

/-- `forwardDifference j` is the `j`-th iterate of Mathlib's forward difference `fwdDiff 1`. -/
theorem forwardDifference_eq_iterate_fwdDiff (j : Nat) (h : Nat → Real) :
    forwardDifference j h = (fwdDiff 1)^[j] h := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

theorem finite_newton_expansion (h : Nat → Real) (l : Nat) :
    h l = (Finset.range (l + 1)).sum
      (fun j => (Nat.choose l j : Real) * forwardDifference j h 0) := by
  simpa [forwardDifference_eq_iterate_fwdDiff, nsmul_eq_mul] using
    shift_eq_sum_fwdDiff_iter 1 h l 0

theorem falling_difference_formula {n d l j : Nat}
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (hlj : l + j ≤ d) :
    forwardDifference j (fun a => boolMoment n (2 * d - a)) l =
      falling ((n : Real) - fractionalCardinality n) j *
        falling (fractionalCardinality n) (2 * d - l - j) /
        falling (n : Real) (2 * d - l) := by
  induction j generalizing l with
  | zero => simp [forwardDifference, falling, boolMoment]
  | succ j ih =>
    rw [forwardDifference]
    dsimp only
    rw [ih (l := l + 1) (by omega), ih (l := l) (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, 2 * d - l - (j + 1) = m := ⟨_, rfl⟩
    rw [hm, show 2 * d - (l + 1) - j = m by omega, show 2 * d - l - j = m + 1 by omega,
      show 2 * d - (l + 1) = m + j by omega, show 2 * d - l = m + j + 1 by omega,
      falling_succ, falling_succ, falling_succ _ j]
    have hmj : ((m + j : Nat) : Real) < n := by exact_mod_cast (show m + j < n by omega)
    have h₁ : falling (n : Real) (m + j) ≠ 0 := (falling_pos _ _ hmj.le).ne'
    have h₂ : (n : Real) - ((m + j : Nat) : Real) ≠ 0 := (sub_pos.mpr hmj).ne'
    field_simp
    push_cast
    ring

theorem gram_entry_decomposition {n d : Nat}
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (S T : Level n d) :
    gramEntry n d S T = (Finset.range (d + 1)).sum
      (fun j => gramCoefficient n d j * incidenceEntry n d j S T) := by
  have hl : (S.val ∩ T.val).card ≤ d :=
    (Finset.card_le_card Finset.inter_subset_left).trans S.property.le
  refine (finite_newton_expansion (fun a => boolMoment n (2 * d - a)) _).trans ?_
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) (fun j _ hj => ?_) |>.trans
    (Finset.sum_congr rfl fun j hj => ?_)
  · rw [Finset.mem_range, not_lt] at hj
    simp [Nat.choose_eq_zero_of_lt (show (S.val ∩ T.val).card < j by omega)]
  · rw [falling_difference_formula hd hnd (by simp at hj; omega)]
    simp [gramCoefficient, incidenceEntry, mul_comm]

theorem gramCoefficient_nonneg {n d j : Nat}
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (hj : j ≤ d) :
    0 ≤ gramCoefficient n d j := by
  have hn : (4 * d : Real) ≤ n := by exact_mod_cast hnd
  have hd' : (1 : Real) ≤ d := by exact_mod_cast hd
  have hj' : (j : Real) ≤ d := by exact_mod_cast hj
  have hj₀ : (0 : Real) ≤ j := Nat.cast_nonneg j
  unfold gramCoefficient fractionalCardinality
  refine le_of_lt (div_pos (mul_pos (falling_pos _ _ ?_) (falling_pos _ _ ?_)) (falling_pos _ _ ?_))
  · linarith
  · rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  · push_cast
    linarith

theorem incidence_count (n j : Nat) (S T : Finset (Fin n)) :
    Finset.univ.sum (fun U : Level n j =>
      if U.val ⊆ S ∩ T then (1 : Real) else 0) =
        (Nat.choose (S ∩ T).card j : Real) := by
  rw [← Finset.sum_subtype (Finset.powersetCard j Finset.univ) (by simp [Finset.mem_powersetCard])
    (fun U => if U ⊆ S ∩ T then (1 : Real) else 0), Finset.sum_boole,
    ← Finset.card_powersetCard j (S ∩ T)]
  congr 2
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨Finset.subset_univ _, h.2⟩, h.1⟩⟩

theorem incidence_sum_squares {n d : Nat} (j : Nat) (c : Level n d → Real) :
    incidenceForm j c =
      Finset.univ.sum (fun U : Level n j =>
        (Finset.univ.sum (fun S : Level n d => if U.val ≤ S.val then c S else 0)) ^ 2) := by
  simp_rw [sq, Finset.sum_mul_sum]
  simp only [incidenceForm, incidenceEntry, ← incidence_count n j, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; enter [2, S]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ =>
    Finset.sum_congr rfl fun U _ => ?_
  simp only [Finset.subset_inter_iff]
  split_ifs <;> simp_all

theorem incidenceForm_nonneg {n d : Nat} (j : Nat) (c : Level n d → Real) :
    0 ≤ incidenceForm j c := by
  rw [incidence_sum_squares]
  exact Finset.sum_nonneg (fun U _ => sq_nonneg _)

theorem gramForm_decomposition {n d : Nat}
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (c : Level n d → Real) :
    gramForm c = (Finset.range (d + 1)).sum
      (fun j => gramCoefficient n d j * incidenceForm j c) := by
  simp only [gramForm, incidenceForm, gram_entry_decomposition hd hnd, Finset.mul_sum]
  conv_lhs => enter [2, S]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ =>
    Finset.sum_congr rfl fun T _ => by ring

theorem gramForm_nonneg {n d : Nat}
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n) (c : Level n d → Real) :
    0 ≤ gramForm c := by
  rw [gramForm_decomposition hd hnd]
  apply Finset.sum_nonneg
  intro j hj
  have hjd : j ≤ d := by
    have := Finset.mem_range.mp hj
    omega
  exact mul_nonneg (gramCoefficient_nonneg hd hnd hjd) (incidenceForm_nonneg j c)

/-- The positivity of the pseudo-expectation on the Boolean cube: `L(q²) ≥ 0` for `deg q ≤ d`
when `n ≥ 4d`. -/
theorem boolean_square_nonneg {n d : Nat} (M : BooleanMoments n d)
    (hd : 1 ≤ d) (hnd : 4 * d ≤ n)
    (q : BoolCube n) (hq : q ∈ BFilter n d) :
    0 ≤ M.L ⟨q ^ 2, bSquare_mem hq⟩ := by
  obtain ⟨c, hc⟩ := homogenize_square M hd hnd q hq
  rw [hc, moment_level_square]
  exact gramForm_nonneg hd hnd c

end AnyDim.Elementary
end
