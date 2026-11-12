module

public import AnyDim.Counterexample.Symmetric

/-!
# Formal power series in countably many variables

Source: Debus--Schabert, Section 1 (formal power series of bounded degree) and Section 3.

* `FSeries := MvPowerSeries ℕ ℝ` is the ring `ℝ[[X_1, X_2, …]]` (the variables are indexed by
  `ℕ = {0, 1, 2, …}` in Lean), and `FSeriesN n := MvPowerSeries (Fin n) ℝ`.
* `restrict n : FSeries →ₐ[ℝ] FSeriesN n` is the truncation `g ↦ g^{(n)}`: the variables
  `X_i`, `i > n`, are set to `0`.
* `IsTrunc g n a`: the polynomial `a ∈ ℝ[X_1, …, X_n]` *is* the truncation `g^{(n)}`.  A formal
  power series has bounded degree (`deg g = sup_n deg g^{(n)} < ∞`) iff there is `D` such that
  every `g^{(n)}` is a polynomial of degree `≤ D`; `FDegLE g D` says that all monomials of `g`
  have degree `≤ D`, and `fDegLE_iff` shows that the two formulations agree.
* `toSeries : Λ →ₐ[ℝ] FSeries` sends `p_k` to `∑_i X_i^k`; it is injective
  (`toSeries_ne_zero`), compatible with truncation (`restrict_toSeries`, `isTrunc_toSeries`),
  and every symmetric function is a formal power series of bounded degree
  (`fDegLE_toSeries`).
* `exists_forall_restrict_ne_zero`: if `g ≠ 0`, then `g^{(n)} ≠ 0` for all sufficiently large
  `n`.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open MvPolynomial Filter Topology

/-! ### Formal power series in countably many variables -/

/-- Formal power series `ℝ⟦X_0, X_1, X_2, …⟧` in countably many variables. -/
abbrev FSeries := MvPowerSeries ℕ ℝ

/-- Formal power series in the first `n` variables. -/
abbrev FSeriesN (n : ℕ) := MvPowerSeries (Fin n) ℝ

/-- The restriction `g ↦ g^{(n)}`: the variables `X_i`, `i ≥ n`, are set to `0`. -/
def restrict (n : ℕ) : FSeries →ₐ[ℝ] FSeriesN n :=
  MvPowerSeries.killCompl Fin.valEmbedding

theorem coeff_restrict (n : ℕ) (g : FSeries) (e : Fin n →₀ ℕ) :
    MvPowerSeries.coeff e (restrict n g) =
      MvPowerSeries.coeff (Finsupp.embDomain Fin.valEmbedding e) g :=
  MvPowerSeries.coeff_killCompl g e

open Classical in
/-- The formal power series `∑_i X_i^k`, the image of the power sum `p_k`. -/
def pseries (k : PNat) : FSeries :=
  fun e => if ∃ i : ℕ, e = Finsupp.single i (k : ℕ) then 1 else 0

/-- The embedding `Λ → ℝ⟦X_0, X_1, …⟧`, `p_k ↦ ∑_i X_i^k`. -/
def toSeries : Λ →ₐ[ℝ] FSeries :=
  MvPolynomial.aeval pseries

/-- Exponent vectors of the form `embDomain val e` that are a single power of one variable. -/
theorem embDomain_eq_single_iff {n : ℕ} (e : Fin n →₀ ℕ) {i k : ℕ} (hk : k ≠ 0) :
    Finsupp.embDomain Fin.valEmbedding e = Finsupp.single i k ↔
      ∃ j : Fin n, (j : ℕ) = i ∧ e = Finsupp.single j k := by
  constructor
  · intro h
    have hi : i ∈ (Finsupp.embDomain Fin.valEmbedding e).support := by
      rw [h, Finsupp.mem_support_iff, Finsupp.single_eq_same]
      exact hk
    rw [Finsupp.support_embDomain, Finset.mem_map] at hi
    obtain ⟨j, -, hj⟩ := hi
    refine ⟨j, hj, ?_⟩
    apply Finsupp.embDomain_injective Fin.valEmbedding
    rw [h, Finsupp.embDomain_single, hj]
  · rintro ⟨j, rfl, rfl⟩
    rw [Finsupp.embDomain_single]
    rfl

theorem restrict_pseries (n : ℕ) (k : PNat) :
    restrict n (pseries k) = ((powerSum n (k : ℕ) : Poly n) : FSeriesN n) := by
  classical
  ext e
  rw [coeff_restrict, MvPolynomial.coeff_coe, powerSum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_X_pow]
  rw [MvPowerSeries.coeff_apply]
  have hk : (k : ℕ) ≠ 0 := k.ne_zero
  by_cases h : ∃ j : Fin n, Finsupp.single j (k : ℕ) = e
  · obtain ⟨j, hj⟩ := h
    have hl : (∃ i : ℕ, Finsupp.embDomain Fin.valEmbedding e = Finsupp.single i (k : ℕ)) :=
      ⟨j, (embDomain_eq_single_iff e hk).2 ⟨j, rfl, hj.symm⟩⟩
    rw [Finset.sum_eq_single j]
    · simp only [pseries, hl, hj, ite_true]
    · intro i _ hij
      rw [ite_eq_right]
      intro hi
      exact hij (Finsupp.single_left_injective hk (hi.trans hj.symm))
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  · have hl :
        ¬ (∃ i : ℕ, Finsupp.embDomain Fin.valEmbedding e = Finsupp.single i (k : ℕ)) := by
      rintro ⟨i, hi⟩
      obtain ⟨j, -, hj⟩ := (embDomain_eq_single_iff e hk).1 hi
      exact h ⟨j, hj.symm⟩
    simp only [pseries, hl, ite_false]
    symm
    exact Finset.sum_eq_zero fun j _ => by
      rw [ite_eq_right]
      intro hj
      exact h ⟨j, hj⟩

/-- `(toSeries h)^{(n)} = h^{(n)}`: the restriction of the formal series of `h` is its
truncation `h^{(n)}`. -/
theorem restrict_toSeries (n : ℕ) (h : Λ) :
    restrict n (toSeries h) = ((trunc n h : Poly n) : FSeriesN n) := by
  have hcomp : (restrict n).comp toSeries =
      (MvPolynomial.coeToMvPowerSeries.algHom ℝ).comp (trunc n) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, toSeries, trunc, MvPolynomial.aeval_X,
      MvPolynomial.coeToMvPowerSeries.algHom_apply, restrict_pseries, Algebra.algebraMap_self,
      MvPowerSeries.map_id, RingHom.id_apply]
  have := congrArg (· h) hcomp
  simpa using this

/-- `(g f)^{(n)} = g^{(n)} f^{(n)}` for a formal power series `g` and a symmetric function `f`. -/
theorem restrict_mul_toSeries (n : ℕ) (g : FSeries) (f : Λ) :
    restrict n (g * toSeries f) = restrict n g * ((trunc n f : Poly n) : FSeriesN n) := by
  rw [map_mul, restrict_toSeries]

theorem toSeries_ne_zero {h : Λ} (hh : h ≠ 0) : toSeries h ≠ 0 := by
  intro h0
  apply trunc_ne_zero_of_usesFirst (usesFirst_self h) hh
  have h1 := restrict_toSeries (variableBound h) h
  rw [h0, map_zero] at h1
  exact MvPolynomial.coe_eq_zero_iff.1 h1.symm

/-- Λ restriction `g^{(n)}` of `g` that contains a given monomial of `g`. -/
theorem exists_restrict_coeff_ne_zero {g : FSeries} {α : ℕ →₀ ℕ}
    (hα : MvPowerSeries.coeff α g ≠ 0) {n : ℕ} (hn : ∀ i ∈ α.support, i < n) :
    ∃ α' : Fin n →₀ ℕ, Finsupp.embDomain Fin.valEmbedding α' = α ∧
      MvPowerSeries.coeff α' (restrict n g) ≠ 0 := by
  have hsupp : (α.support : Set ℕ) ⊆ Set.range (Fin.val : Fin n → ℕ) := fun i hi =>
    ⟨⟨i, hn i hi⟩, rfl⟩
  refine ⟨Finsupp.comapDomain Fin.val α Fin.val_injective.injOn, ?_, ?_⟩
  · rw [Finsupp.embDomain_eq_mapDomain, Fin.valEmbedding_apply]
    exact Finsupp.mapDomain_comapDomain _ Fin.val_injective α hsupp
  · rw [coeff_restrict, Finsupp.embDomain_eq_mapDomain, Fin.valEmbedding_apply,
      Finsupp.mapDomain_comapDomain _ Fin.val_injective α hsupp]
    exact hα


/-- The polynomial `a` in `n` variables is the truncation `g^{(n)}` of the formal power series
`g`. -/
def IsTrunc (g : FSeries) (n : ℕ) (a : Poly n) : Prop :=
  (a : FSeriesN n) = restrict n g

/-- The truncation `f^{(n)}` of a symmetric function is the truncation of its formal power
series. -/
theorem isTrunc_toSeries (n : ℕ) (h : Λ) : IsTrunc (toSeries h) n (trunc n h) :=
  (restrict_toSeries n h).symm

/-- `(g f)^{(n)} = g^{(n)} f^{(n)}` for a formal power series `g` and a symmetric function `f`. -/
theorem IsTrunc.mul_toSeries {g : FSeries} {n : ℕ} {a : Poly n} (ha : IsTrunc g n a) (f : Λ) :
    IsTrunc (g * toSeries f) n (a * trunc n f) := by
  unfold IsTrunc at ha ⊢
  rw [restrict_mul_toSeries, ← ha, MvPolynomial.coe_mul]

/-- If `g ≠ 0`, then `g^{(n)} ≠ 0` for all sufficiently large `n`: one of the monomials of `g`
with nonzero coefficient involves only finitely many variables. -/
theorem exists_forall_restrict_ne_zero {g : FSeries} (hg : g ≠ 0) :
    ∃ n₀, ∀ n ≥ n₀, restrict n g ≠ 0 := by
  obtain ⟨α, hα⟩ : ∃ α, MvPowerSeries.coeff α g ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (MvPowerSeries.ext fun e => by rw [h e, map_zero])
  refine ⟨α.support.sup id + 1, fun n hn h0 => ?_⟩
  obtain ⟨α', -, hα'⟩ := exists_restrict_coeff_ne_zero hα (n := n) (fun i hi => by
    have : i ≤ α.support.sup id := Finset.le_sup (f := id) hi
    omega)
  rw [h0, map_zero] at hα'
  exact hα' rfl

/-- If `a = g^{(n)}` for a nonzero truncation, then `a ≠ 0`. -/
theorem IsTrunc.ne_zero {g : FSeries} {n : ℕ} {a : Poly n} (ha : IsTrunc g n a)
    (hg : restrict n g ≠ 0) : a ≠ 0 := by
  rintro rfl
  exact hg (by rw [← ha]; rfl)

/-- `FDegLE g D`: every monomial of the formal power series `g` has degree at most `D`. -/
def FDegLE (g : FSeries) (D : ℕ) : Prop :=
  ∀ e, MvPowerSeries.coeff e g ≠ 0 → e.degree ≤ D

/-- A formal power series has degree `≤ D` iff every truncation `g^{(n)}` is a polynomial of
degree `≤ D` (the paper's `deg g = sup_n deg g^{(n)} ≤ D`). -/
theorem fDegLE_iff (g : FSeries) (D : ℕ) :
    FDegLE g D ↔ ∀ n, ∃ a : Poly n, IsTrunc g n a ∧ a.totalDegree ≤ D := by
  classical
  constructor
  · intro hg n
    -- the polynomial with the coefficients of `g^{(n)}`
    have hfin : {e : Fin n →₀ ℕ | e.degree ≤ D}.Finite := Finsupp.finite_of_degree_le D
    refine ⟨∑ e ∈ hfin.toFinset, monomial e (MvPowerSeries.coeff e (restrict n g)), ?_, ?_⟩
    · unfold IsTrunc
      ext e
      rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      by_cases he : e.degree ≤ D
      · rw [Finset.sum_eq_single e]
        · rw [ite_eq_left rfl]
        · intro b _ hb
          rw [ite_eq_right]
          intro h
          exact absurd h hb
        · intro h
          exact absurd (hfin.mem_toFinset.mpr he) h
      · have h0 : MvPowerSeries.coeff e (restrict n g) = 0 := by
          by_contra hne
          rw [coeff_restrict] at hne
          have := hg _ hne
          rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] at this
          exact he this
        rw [h0]
        refine Finset.sum_eq_zero fun b hb => ?_
        rw [ite_eq_right]
        intro h
        rw [h] at hb
        exact absurd (hfin.mem_toFinset.mp hb) he
    · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun e he => ?_)
      exact (MvPolynomial.totalDegree_monomial_le _ _).trans (hfin.mem_toFinset.mp he)
  · intro h e he
    -- `e` involves only finitely many variables
    set n := e.support.sup id + 1 with hn
    obtain ⟨e', hee', he'⟩ := exists_restrict_coeff_ne_zero he (n := n) (fun i hi => by
      have : i ≤ e.support.sup id := Finset.le_sup (f := id) hi
      omega)
    obtain ⟨a, ha, hdeg⟩ := h n
    rw [← ha, MvPolynomial.coeff_coe] at he'
    have hle : e'.degree ≤ a.totalDegree :=
      MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr he')
    rw [← hee', Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
    exact hle.trans hdeg

/-- Every symmetric function is a formal power series of bounded degree. -/
theorem fDegLE_toSeries {h : Λ} {D : ℕ} (hh : WDegLE h D) : FDegLE (toSeries h) D :=
  (fDegLE_iff _ _).mpr fun n => ⟨trunc n h, isTrunc_toSeries n h, totalDegree_trunc_le hh⟩

end AnyDim
end
