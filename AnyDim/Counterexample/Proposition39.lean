module

public import AnyDim.Counterexample.ClosedCone

/-!
# Proposition 3.9: from multipliers of bounded degree to multipliers in `SΣ`

Source: Debus--Schabert, Proposition 3.9.

Let `f ∈ SP`, and suppose there are `d` and a formal power series `0 ≠ q ∈ ℝ[[X_1, X_2, …]]` with
`deg q^{(n)} ≤ 2d` such that `q^{(n)}` and `q^{(n)} f^{(n)}` are sums of squares for every `n`.
Then there is `h ∈ SΣ ∖ {0}` with `h f ∈ SΣ` (`proposition_3_9`).

As in the paper: symmetrize `q^{(n)}`, write the symmetrizations in the power sum basis
(`exists_trunc_eq_of_totalDegree_le`), normalize the coefficient vectors to the unit sphere of the
finite-dimensional space of symmetric functions of degree `≤ 2d` (`Coord`, `coord`, `ofCoordₗ`),
pass to a convergent subsequence, and use that truncations of sums of squares are sums of
squares (`isSOS_trunc_of_le`) and that the cone of sums of squares of bounded degree is closed
(`isSOS_of_tendsto`).

The more general `exists_multiplier_of_bounded_degree` only needs nonzero sos multipliers of
bounded degree for arbitrarily large `n` (they need not be truncations of one power series);
`multiplier_degree_tendsto` is the contrapositive: if `f` has no multiplier in `SΣ`, the minimal
degree of a sos multiplier of `f^{(n)}` tends to infinity.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open MvPolynomial Filter Topology

/-! ### Coordinates on the symmetric functions of degree `≤ d` -/

section Coordinates

variable {d : ℕ}

theorem generatorIndex_injective (d : ℕ) : Function.Injective (generatorIndex (s := d)) := by
  intro i j hij
  have := congrArg PNat.val hij
  simp only [generatorIndex, PNat.mk_coe] at this
  exact Fin.ext (by omega)

theorem le_monomialWeight (e : PNat →₀ ℕ) (k : PNat) :
    (k : ℕ) * e k ≤ monomialWeight e := by
  unfold monomialWeight
  by_cases hk : k ∈ e.support
  · exact Finset.single_le_sum (f := fun k : PNat => (k : ℕ) * e k) (fun _ _ => Nat.zero_le _) hk
  · rw [Finsupp.notMem_support_iff.1 hk, mul_zero]
    exact Nat.zero_le _

theorem degree_le_monomialWeight (e : PNat →₀ ℕ) : e.degree ≤ monomialWeight e := by
  rw [Finsupp.degree_apply, monomialWeight, Finsupp.sum]
  exact Finset.sum_le_sum fun k _ => Nat.le_mul_of_pos_left (e k) k.pos

/-- There are only finitely many monomials of bounded weight. -/
theorem finite_monomialWeight_le (d : ℕ) :
    {e : PNat →₀ ℕ | monomialWeight e ≤ d}.Finite := by
  have hfin : ({e : Fin d →₀ ℕ | e.degree ≤ d}.image
      (Finsupp.mapDomain (generatorIndex (s := d)))).Finite :=
    (Finsupp.finite_of_degree_le d).image _
  refine hfin.subset ?_
  intro e he
  have hsupp : (e.support : Set PNat) ⊆ Set.range (generatorIndex (s := d)) := by
    intro k hk
    have hk' : k ∈ e.support := hk
    have hpos : 0 < e k := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hk')
    have hkd : (k : ℕ) ≤ d :=
      (Nat.le_mul_of_pos_right (k : ℕ) hpos).trans ((le_monomialWeight e k).trans he)
    refine ⟨⟨k.val - 1, by have := k.pos; omega⟩, PNat.eq ?_⟩
    simp only [generatorIndex, PNat.mk_coe]
    have := k.pos
    omega
  refine ⟨Finsupp.comapDomain _ e (generatorIndex_injective d).injOn, ?_, ?_⟩
  · show Finsupp.degree _ ≤ d
    have := Finsupp.degree_mapDomain (generatorIndex (s := d))
      (Finsupp.comapDomain _ e (generatorIndex_injective d).injOn)
    rw [Finsupp.mapDomain_comapDomain _ (generatorIndex_injective d) e hsupp] at this
    rw [← this]
    exact (degree_le_monomialWeight e).trans he
  · exact Finsupp.mapDomain_comapDomain _ (generatorIndex_injective d) e hsupp

/-- The finite set of exponent vectors of weight `≤ d`. -/
def monoSet (d : ℕ) : Finset (PNat →₀ ℕ) := (finite_monomialWeight_le d).toFinset

theorem mem_monoSet {e : PNat →₀ ℕ} : e ∈ monoSet d ↔ monomialWeight e ≤ d := by
  simp [monoSet]

/-- Coordinates on the finite-dimensional space `A_{≤ d}`. -/
abbrev Coord (d : ℕ) := (monoSet d) → ℝ

/-- The coordinate vector of `B ∈ Λ` (restricted to the monomials of weight `≤ d`). -/
def coord (d : ℕ) (B : Λ) : Coord d := fun v => B.coeff v.1

/-- The element of `A_{≤ d}` with coordinate vector `c`. -/
def ofCoordₗ (d : ℕ) : Coord d →ₗ[ℝ] Λ :=
  ∑ v : monoSet d, (monomial v.1).comp (LinearMap.proj v)

theorem ofCoordₗ_apply (c : Coord d) :
    ofCoordₗ d c = ∑ v : monoSet d, monomial v.1 (c v) := by
  simp only [ofCoordₗ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem coeff_ofCoordₗ_of_mem (c : Coord d) {e : PNat →₀ ℕ} (he : e ∈ monoSet d) :
    (ofCoordₗ d c).coeff e = c ⟨e, he⟩ := by
  rw [ofCoordₗ_apply, coeff_sum, Finset.sum_eq_single ⟨e, he⟩]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro v _ hv
    rw [coeff_monomial, ite_eq_right]
    intro h
    exact hv (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_ofCoordₗ_of_not_mem (c : Coord d) {e : PNat →₀ ℕ} (he : e ∉ monoSet d) :
    (ofCoordₗ d c).coeff e = 0 := by
  rw [ofCoordₗ_apply, coeff_sum]
  exact Finset.sum_eq_zero fun v _ => by
    rw [coeff_monomial, ite_eq_right]
    intro h
    exact he (h ▸ v.2)

theorem ofCoordₗ_coord {B : Λ} (hB : WDegLE B d) : ofCoordₗ d (coord d B) = B := by
  ext e
  by_cases he : e ∈ monoSet d
  · rw [coeff_ofCoordₗ_of_mem _ he]
    rfl
  · rw [coeff_ofCoordₗ_of_not_mem _ he]
    by_contra h
    exact he (mem_monoSet.2 (hB e (mem_support_iff.2 (Ne.symm h))))

theorem coord_ofCoordₗ (c : Coord d) : coord d (ofCoordₗ d c) = c := by
  funext v
  exact coeff_ofCoordₗ_of_mem c v.2

theorem wDegLE_ofCoordₗ (c : Coord d) : WDegLE (ofCoordₗ d c) d := by
  intro e he
  by_contra h
  exact mem_support_iff.1 he (coeff_ofCoordₗ_of_not_mem c (mt mem_monoSet.1 h))

theorem coord_eq_zero_iff {B : Λ} (hB : WDegLE B d) : coord d B = 0 ↔ B = 0 := by
  constructor
  · intro h
    rw [← ofCoordₗ_coord hB, h, map_zero]
  · rintro rfl
    funext v
    simp [coord]

/-- Every linear functional of the form `c ↦ (L (ofCoordₗ d c)).coeff e` is continuous. -/
theorem continuous_coeff_comp_ofCoordₗ {m : ℕ} (L : Λ →ₗ[ℝ] Poly m)
    (e : Fin m →₀ ℕ) :
    Continuous fun c : Coord d => (L (ofCoordₗ d c)).coeff e :=
  ((lcoeff ℝ e).comp (L.comp (ofCoordₗ d))).continuous_of_finiteDimensional

end Coordinates

/-! ### The compactness argument of Proposition 3.9 -/

theorem exists_multiplier_core (f : Λ) (d : ℕ) (P : (PNat →₀ ℕ) → Prop)
    (hP : ∀ e, P e → monomialWeight e ≤ d) (B : ℕ → Λ)
    (hBP : ∀ n, ∀ e ∈ (B n).support, P e)
    (hB : ∀ N, ∃ n ≥ N, B n ≠ 0 ∧ IsSOS (trunc n (B n)) ∧
      IsSOS (trunc n (B n * f))) :
    ∃ H : Λ, H ≠ 0 ∧ (∀ e ∈ H.support, P e) ∧ AnyDimSOS H ∧ AnyDimSOS (H * f) := by
  choose nn hnn hBne hB1 hB2 using hB
  have hdeg : ∀ n, WDegLE (B n) d := fun n e he => hP e (hBP n e he)
  -- normalized coordinate vectors of the `B (nn N)`
  let v : ℕ → Coord d := fun N => coord d (B (nn N))
  have hv : ∀ N, v N ≠ 0 := fun N h => hBne N ((coord_eq_zero_iff (hdeg _)).1 h)
  let u : ℕ → Coord d := fun N => ‖v N‖⁻¹ • v N
  have hu : ∀ N, u N ∈ Metric.sphere (0 : Coord d) 1 := by
    intro N
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hv N))]
  have hofu : ∀ N, ofCoordₗ d (u N) = ‖v N‖⁻¹ • B (nn N) := by
    intro N
    simp only [u, v, map_smul, ofCoordₗ_coord (hdeg _)]
  -- a convergent subsequence
  obtain ⟨c₀, hc₀, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Coord d) 1).tendsto_subseq hu
  have hle : ∀ m k, m ≤ nn (φ (k + m)) := fun m k =>
    le_trans (le_trans (Nat.le_add_left m k) (hφ.id_le (k + m))) (hnn (φ (k + m)))
  have hlim' : ∀ m, Tendsto (fun k => u (φ (k + m))) atTop (𝓝 c₀) := fun m =>
    hlim.comp (tendsto_add_atTop_nat m)
  refine ⟨ofCoordₗ d c₀, ?_, ?_, ?_, ?_⟩
  · -- `H ≠ 0` since `‖c₀‖ = 1`
    intro h
    have hc : c₀ = 0 := by
      rw [← coord_ofCoordₗ c₀, h]
      funext w
      simp [coord]
    rw [hc, Metric.mem_sphere, dist_zero_right, norm_zero] at hc₀
    exact zero_ne_one hc₀
  · -- the support of `H` satisfies `P`
    intro e he
    by_contra hPe
    have he' : e ∈ monoSet d := by
      by_contra hm
      exact mem_support_iff.1 he (coeff_ofCoordₗ_of_not_mem c₀ hm)
    have hzero : ∀ N, u N ⟨e, he'⟩ = 0 := by
      intro N
      simp only [u, v, Pi.smul_apply, coord, smul_eq_mul]
      rw [notMem_support_iff.1 (fun hs => hPe (hBP _ e hs)), mul_zero]
    have h1 : Tendsto (fun k => u (φ k) ⟨e, he'⟩) atTop (𝓝 (c₀ ⟨e, he'⟩)) :=
      (tendsto_pi_nhds.1 hlim) ⟨e, he'⟩
    have h2 : Tendsto (fun k => u (φ k) ⟨e, he'⟩) atTop (𝓝 0) := by
      simp only [hzero]
      exact tendsto_const_nhds
    exact mem_support_iff.1 he
      (by rw [coeff_ofCoordₗ_of_mem c₀ he']; exact tendsto_nhds_unique h1 h2)
  · -- `H ∈ SΣ` by closedness of the sos cone
    intro m _
    apply isSOS_of_tendsto (D := d) (fun k => trunc m (ofCoordₗ d (u (φ (k + m)))))
    · intro k
      rw [hofu, map_smul]
      exact (isSOS_trunc_of_le (hle m k) (hB1 _)).smul_nonneg (inv_nonneg.2 (norm_nonneg _))
    · intro k
      exact (totalDegree_trunc_le (wDegLE_ofCoordₗ _)).trans (by omega)
    · intro e
      have := ((continuous_coeff_comp_ofCoordₗ (trunc m).toLinearMap e).tendsto c₀).comp
        (hlim' m)
      simpa [Function.comp_def] using this
  · -- `H f ∈ SΣ` by closedness of the sos cone
    intro m _
    apply isSOS_of_tendsto (D := d + wDegree f) (fun k => trunc m (ofCoordₗ d (u (φ (k + m))) * f))
    · intro k
      rw [hofu, smul_mul_assoc, map_smul]
      exact (isSOS_trunc_of_le (hle m k) (hB2 _)).smul_nonneg (inv_nonneg.2 (norm_nonneg _))
    · intro k
      rw [map_mul]
      refine (totalDegree_mul _ _).trans ?_
      have h1 := totalDegree_trunc_le (n := m) (wDegLE_ofCoordₗ (u (φ (k + m))))
      have h2 := totalDegree_trunc_le (n := m) (wdeg_self f)
      omega
    · intro e
      have := ((continuous_coeff_comp_ofCoordₗ
        ((trunc m).toLinearMap ∘ₗ LinearMap.mulRight ℝ f) e).tendsto c₀).comp (hlim' m)
      simpa [Function.comp_def] using this

/-- The symmetrization and compactness argument of Proposition 3.9: if for arbitrarily large `n`
there is a nonzero sum of squares `a_n` of degree `≤ d` in `n` variables with `a_n f^{(n)}` a sum
of squares, then there is a nonzero `H ∈ SΣ` of degree `≤ d` with `H f ∈ SΣ`. -/
theorem exists_multiplier_of_bounded_degree (f : Λ) (d : ℕ)
    (h : ∀ N, ∃ n ≥ N, ∃ a : Poly n, a ≠ 0 ∧ a.totalDegree ≤ d ∧ IsSOS a ∧
      IsSOS (a * trunc n f)) :
    ∃ H : Λ, H ≠ 0 ∧ WDegLE H d ∧ AnyDimSOS H ∧ AnyDimSOS (H * f) := by
  classical
  -- the symmetrized multipliers, written in the power sums
  let good : ℕ → Prop := fun n =>
    ∃ a : Poly n, a ≠ 0 ∧ a.totalDegree ≤ d ∧ IsSOS a ∧ IsSOS (a * trunc n f)
  let B : ℕ → Λ := fun n => if hn : good n then
    Classical.choose (exists_trunc_eq_of_totalDegree_le
      (symmetrize_isSymmetric (Classical.choose hn))
      ((totalDegree_symmetrize_le _).trans (Classical.choose_spec hn).2.1)) else 0
  have hBspec : ∀ n (hn : good n), WDegLE (B n) d ∧
      trunc n (B n) = symmetrize (Classical.choose hn) := by
    intro n hn
    simp only [B, dite_eq_left hn]
    exact Classical.choose_spec (exists_trunc_eq_of_totalDegree_le
      (symmetrize_isSymmetric (Classical.choose hn))
      ((totalDegree_symmetrize_le _).trans (Classical.choose_spec hn).2.1))
  have hBdeg : ∀ n, WDegLE (B n) d := by
    intro n
    by_cases hn : good n
    · exact (hBspec n hn).1
    · simp only [B, dite_eq_right hn]
      intro e he
      simp at he
  obtain ⟨H, hH0, hHP, hH1, hH2⟩ := exists_multiplier_core f d (fun e => monomialWeight e ≤ d)
    (fun _ he => he) B hBdeg (by
      intro N
      obtain ⟨n, hn, hgood⟩ := h N
      refine ⟨n, hn, ?_, ?_, ?_⟩
      · intro h0
        have := (hBspec n hgood).2
        rw [h0, map_zero] at this
        exact symmetrize_ne_zero (Classical.choose_spec hgood).2.2.1
          (Classical.choose_spec hgood).1 this.symm
      · rw [(hBspec n hgood).2]
        exact symmetrize_isSOS (Classical.choose_spec hgood).2.2.1
      · rw [map_mul, (hBspec n hgood).2, ← symmetrize_mul_trunc]
        exact symmetrize_isSOS (Classical.choose_spec hgood).2.2.2)
  exact ⟨H, hH0, hHP, hH1, hH2⟩

/-- If `f` has no nonzero multiplier in `SΣ`, then the minimal degree of a nonzero sos multiplier
of `f^{(n)}` tends to infinity with `n`. -/
theorem multiplier_degree_tendsto (f : Λ)
    (hno : ¬ ∃ H : Λ, H ≠ 0 ∧ AnyDimSOS H ∧ AnyDimSOS (H * f)) (d : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ a : Poly n, a ≠ 0 → IsSOS a → IsSOS (a * trunc n f) →
      d < a.totalDegree := by
  by_contra hcon
  push Not at hcon
  obtain ⟨H, hH0, -, hH1, hH2⟩ := exists_multiplier_of_bounded_degree f d fun N => by
    obtain ⟨n, hn, a, ha0, ha1, ha2, hdeg⟩ := hcon N
    exact ⟨n, hn, a, ha0, hdeg, ha1, ha2⟩
  exact hno ⟨H, hH0, hH1, hH2⟩

/-- **Proposition 3.9**, with the additional information `deg h ≤ 2d`. -/
theorem proposition_3_9' (f : Λ) (d : ℕ) (q : FSeries) (hq : q ≠ 0)
    (h : ∀ n, 0 < n → ∃ a : Poly n, IsTrunc q n a ∧ a.totalDegree ≤ 2 * d ∧ IsSOS a ∧
      IsSOS (a * trunc n f)) :
    ∃ H : Λ, H ≠ 0 ∧ WDegLE H (2 * d) ∧ AnyDimSOS H ∧ AnyDimSOS (H * f) := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_restrict_ne_zero hq
  refine exists_multiplier_of_bounded_degree f (2 * d) fun N => ?_
  refine ⟨max N (max n₀ 1), le_max_left _ _, ?_⟩
  have hn1 : 0 < max N (max n₀ 1) := by omega
  obtain ⟨a, ha, hdeg, h1, h2⟩ := h _ hn1
  exact ⟨a, ha.ne_zero (hn₀ _ (by omega)), hdeg, h1, h2⟩

/-- **Proposition 3.9.**  Let `f ∈ SP` be any-dimensional psd.  Suppose that there exist `d` and
`0 ≠ q ∈ ℝ[[X_1, X_2, …]]` such that for every `n ∈ ℕ` the truncation `q^{(n)}` is a polynomial
of degree `≤ 2d` and both `q^{(n)}` and `q^{(n)} f^{(n)}` are sums of squares.  Then there exists
an any-dimensional sos `h ∈ SΣ ∖ {0}` with `h f ∈ SΣ`.

(The hypothesis `f ∈ SP` of the paper is not needed for the proof; it follows from the other
hypotheses.) -/
theorem proposition_3_9 (f : Λ) (_hf : AnyDimPSD f) (d : ℕ) (q : FSeries) (hq : q ≠ 0)
    (h : ∀ n, 0 < n → ∃ a : Poly n, IsTrunc q n a ∧ a.totalDegree ≤ 2 * d ∧ IsSOS a ∧
      IsSOS (a * trunc n f)) :
    ∃ H : Λ, H ≠ 0 ∧ AnyDimSOS H ∧ AnyDimSOS (H * f) := by
  obtain ⟨H, hH0, -, hH1, hH2⟩ := proposition_3_9' f d q hq h
  exact ⟨H, hH0, hH1, hH2⟩

end AnyDim
end
