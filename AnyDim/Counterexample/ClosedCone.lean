module

public import AnyDim.Counterexample.FormalSeries

/-!
# The cone of sums of squares of bounded degree is closed

Source: used in the proof of Proposition 3.9 of Debus--Schabert ("the cone of sums of squares of
degree `≤ 2e` in `ℝ[X_1, …, X_m]_{≤ 2e}` is closed [26, 2.4.6 Proposition]").

* `isSOS_of_tendsto`: if `s_k` are sums of squares of degree `≤ 2D` in `m` variables converging
  coefficientwise to `t`, then `t` is a sum of squares.
* `isClosed_sos_cone`: the same as a closedness statement in the finite-dimensional coefficient
  space.

The proof parametrizes sums of squares of degree `≤ 2D` by Gram-type parameters
(`Phi c = ∑_k (polyOfₗ (c k))²`), shows that `c ↦ Phi c` is coercive (`exists_coercive`), and
applies Bolzano--Weierstrass.

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AnyDim

open MvPolynomial Filter Topology

/-! ### The cone of sums of squares of bounded degree is closed -/

section ClosedCone

variable {m D : ℕ}

/-- Index type for the monomials `X^α` of `Poly m` with all exponents `≤ D`. -/
abbrev MIdx (m D : ℕ) := Fin m → Fin (D + 1)

/-- The exponent vector of the monomial indexed by `a`. -/
def mono (a : MIdx m D) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)

theorem mono_apply (a : MIdx m D) (i : Fin m) : mono a i = a i := rfl

theorem mono_injective : Function.Injective (mono (m := m) (D := D)) := by
  intro a b hab
  funext i
  have := congrArg (fun e : Fin m →₀ ℕ => e i) hab
  simp only [mono_apply] at this
  exact Fin.ext this

theorem degree_mono_le (a : MIdx m D) : (mono a).degree ≤ m * D := by
  rw [Finsupp.degree_eq_sum]
  calc ∑ i, mono a i ≤ ∑ _i : Fin m, D :=
        Finset.sum_le_sum fun i _ => by rw [mono_apply]; exact Nat.lt_succ_iff.1 (a i).isLt
    _ = m * D := by simp

/-- Every monomial of a polynomial of total degree `≤ D` is indexed by `MIdx m D`. -/
theorem exists_mono_eq {q : Poly m} (hq : q.totalDegree ≤ D) {e : Fin m →₀ ℕ}
    (he : e ∈ q.support) : ∃ a : MIdx m D, mono a = e := by
  have hle : ∀ i, e i ≤ D := fun i =>
    (Finsupp.le_degree i e).trans ((le_totalDegree he).trans hq)
  refine ⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩
  ext i
  rfl

/-- The polynomial with coefficient vector `v` (on the monomials indexed by `MIdx m D`). -/
def polyOfₗ (m D : ℕ) : (MIdx m D → ℝ) →ₗ[ℝ] Poly m :=
  ∑ a : MIdx m D, (monomial (mono a)).comp (LinearMap.proj a)

theorem polyOfₗ_apply (v : MIdx m D → ℝ) :
    polyOfₗ m D v = ∑ a, monomial (mono a) (v a) := by
  simp only [polyOfₗ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem coeff_polyOfₗ_mono (v : MIdx m D → ℝ) (a : MIdx m D) :
    (polyOfₗ m D v).coeff (mono a) = v a := by
  rw [polyOfₗ_apply, coeff_sum, Finset.sum_eq_single a]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro b _ hba
    rw [coeff_monomial, ite_eq_right]
    exact fun h => hba (mono_injective h)
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem coeff_polyOfₗ_of_forall_ne (v : MIdx m D → ℝ) {e : Fin m →₀ ℕ}
    (he : ∀ a : MIdx m D, mono a ≠ e) : (polyOfₗ m D v).coeff e = 0 := by
  rw [polyOfₗ_apply, coeff_sum]
  exact Finset.sum_eq_zero fun a _ => by rw [coeff_monomial, ite_eq_right (he a)]

theorem polyOfₗ_coeff {q : Poly m} (hq : q.totalDegree ≤ D) :
    polyOfₗ m D (fun a => q.coeff (mono a)) = q := by
  ext e
  by_cases h : ∃ a : MIdx m D, mono a = e
  · obtain ⟨a, rfl⟩ := h
    rw [coeff_polyOfₗ_mono]
  · rw [coeff_polyOfₗ_of_forall_ne _ (fun a ha => h ⟨a, ha⟩)]
    by_contra hne
    exact h (exists_mono_eq hq (mem_support_iff.2 (Ne.symm hne)))

theorem polyOfₗ_eq_zero_iff (v : MIdx m D → ℝ) : polyOfₗ m D v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext a
    rw [← coeff_polyOfₗ_mono v a, h]
    rfl
  · rintro rfl
    exact map_zero _

theorem totalDegree_polyOfₗ_le (v : MIdx m D → ℝ) :
    (polyOfₗ m D v).totalDegree ≤ m * D := by
  rw [polyOfₗ_apply]
  refine (totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun a _ => (totalDegree_monomial_le _ _).trans ?_
  exact degree_mono_le a

/-- Evaluation of the monomial indexed by `a` at `x`. -/
def monoEval (x : Fin m → ℝ) (a : MIdx m D) : ℝ := eval x (monomial (mono a) (1 : ℝ))

theorem eval_polyOfₗ (v : MIdx m D → ℝ) (x : Fin m → ℝ) :
    eval x (polyOfₗ m D v) = ∑ a, v a * monoEval x a := by
  rw [polyOfₗ_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monoEval, eval_monomial, eval_monomial, one_mul]

/-- The parameter space of Gram-type representations: `card (MIdx m D)` polynomials of degree
`≤ D` with coefficient vectors indexed by `MIdx m D`. -/
abbrev Par (m D : ℕ) := MIdx m D → MIdx m D → ℝ

/-- The sum of squares with parameter `c`. -/
def Phi (c : Par m D) : Poly m := ∑ k, polyOfₗ m D (c k) ^ 2

theorem isSOS_Phi (c : Par m D) : IsSOS (Phi c) := by
  let e := Fintype.equivFin (MIdx m D)
  exact ⟨Fintype.card (MIdx m D), fun j => polyOfₗ m D (c (e.symm j)),
    (e.symm.sum_comp fun i => polyOfₗ m D (c i) ^ 2).symm⟩

theorem Phi_eq_zero_iff (c : Par m D) : Phi c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext k
    exact (polyOfₗ_eq_zero_iff _).1 (sum_sq_eq_zero h k)
  · rintro rfl
    simp [Phi]

theorem Phi_smul (r : ℝ) (c : Par m D) : Phi (r • c) = r ^ 2 • Phi c := by
  unfold Phi
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, map_smul, smul_pow]

theorem totalDegree_Phi_le (c : Par m D) : (Phi c).totalDegree ≤ 2 * (m * D) := by
  unfold Phi
  refine (totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun k _ => (totalDegree_pow _ _).trans ?_
  exact Nat.mul_le_mul_left 2 (totalDegree_polyOfₗ_le _)

theorem continuous_coeff_polyOfₗ (e : Fin m →₀ ℕ) :
    Continuous fun v : MIdx m D → ℝ => (polyOfₗ m D v).coeff e :=
  ((lcoeff ℝ e).comp (polyOfₗ m D)).continuous_of_finiteDimensional

theorem continuous_coeff_Phi (e : Fin m →₀ ℕ) :
    Continuous fun c : Par m D => (Phi c).coeff e := by
  classical
  unfold Phi
  simp only [coeff_sum, pow_two, coeff_mul]
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun x _ => ?_
  exact ((continuous_coeff_polyOfₗ x.1).comp (continuous_apply k)).mul
    ((continuous_coeff_polyOfₗ x.2).comp (continuous_apply k))

theorem exists_Phi_eq {s : Poly m} (hs : IsSOS s) (hdeg : s.totalDegree ≤ 2 * D) :
    ∃ c : Par m D, Phi c = s := by
  obtain ⟨r, q, hsq, hq⟩ := sos_degree_bound hs hdeg
  -- the linear functionals `ℓ j v = ∑ a, (q j).coeff (mono a) * v a`
  let ℓ : Fin r → (MIdx m D → ℝ) →ₗ[ℝ] ℝ := fun j =>
    ∑ a, (q j).coeff (mono a) • LinearMap.proj a
  have hℓ : ∀ j v, ℓ j v = ∑ a, (q j).coeff (mono a) * v a := by
    intro j v
    simp only [ℓ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  have heval : ∀ j x, eval x (q j) = ℓ j (monoEval x) := by
    intro j x
    conv_lhs => rw [← polyOfₗ_coeff (hq j)]
    rw [eval_polyOfₗ, hℓ]
  -- the Gram bilinear form
  let β : LinearMap.BilinForm ℝ (MIdx m D → ℝ) := ∑ j, (ℓ j).smulRight (ℓ j)
  have hβ : ∀ u v, β u v = ∑ j, ℓ j u * ℓ j v := by
    intro u v
    simp only [β, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      smul_eq_mul]
  have hsymm : β.IsSymm :=
    ⟨fun u v => by rw [hβ, hβ]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _⟩
  have hnonneg : ∀ v, 0 ≤ β v v := fun v => by
    rw [hβ]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨bas, hbas⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 hsymm)
  -- reindex the orthogonal basis by `MIdx m D`
  have hcard :
      Fintype.card (Fin (Module.finrank ℝ (MIdx m D → ℝ))) = Fintype.card (MIdx m D) := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
  let σ : Fin (Module.finrank ℝ (MIdx m D → ℝ)) ≃ MIdx m D := Fintype.equivOfCardEq hcard
  let bas' := bas.reindex σ
  have hbas' : ∀ i j, i ≠ j → β (bas' i) (bas' j) = 0 := by
    intro i j hij
    simp only [bas', Module.Basis.reindex_apply]
    exact hbas (fun h => hij (σ.symm.injective h))
  -- diagonalization: `β v v = ∑ k, (√β_k · coord_k v)^2`
  have hdiag : ∀ v, β v v = ∑ k, (Real.sqrt (β (bas' k) (bas' k)) * bas'.coord k v) ^ 2 := by
    intro v
    conv_lhs => rw [← bas'.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hbas' j i hji, mul_zero]) (by simp),
      mul_pow, Real.sq_sqrt (hnonneg _)]
    ring
  -- the parameters
  let c : Par m D := fun k a =>
    Real.sqrt (β (bas' k) (bas' k)) * bas'.coord k (fun b => if a = b then 1 else 0)
  refine ⟨c, MvPolynomial.funext fun x => ?_⟩
  have hck : ∀ k, eval x (polyOfₗ m D (c k)) =
      Real.sqrt (β (bas' k) (bas' k)) * bas'.coord k (monoEval x) := by
    intro k
    rw [eval_polyOfₗ, LinearMap.pi_apply_eq_sum_univ (bas'.coord k) (monoEval x), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [c, smul_eq_mul]
    ring
  have h1 : eval x (Phi c) = β (monoEval x) (monoEval x) := by
    simp only [Phi, map_sum, map_pow, hck]
    rw [hdiag]
  have h2 : eval x s = β (monoEval x) (monoEval x) := by
    rw [hsq, map_sum, hβ]
    simp only [map_pow, heval]
    exact Finset.sum_congr rfl fun j _ => pow_two _
  rw [h1, h2]

/-- The finite set of exponent vectors of degree `≤ 2 m D`. -/
def expSet (m D : ℕ) : Finset (Fin m →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (2 * (m * D))).toFinset

theorem mem_expSet {e : Fin m →₀ ℕ} : e ∈ expSet m D ↔ e.degree ≤ 2 * (m * D) := by
  simp [expSet]

/-- Λ continuous "norm" on polynomials of degree `≤ 2 m D`: the sum of the squared
coefficients. -/
def tau (m D : ℕ) (q : Poly m) : ℝ := ∑ e ∈ expSet m D, q.coeff e ^ 2

theorem tau_nonneg (q : Poly m) : 0 ≤ tau m D q :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tau_eq_zero {q : Poly m} (hq : q.totalDegree ≤ 2 * (m * D)) (h : tau m D q = 0) :
    q = 0 := by
  ext e
  change q.coeff e = 0
  by_cases he : e ∈ expSet m D
  · exact pow_eq_zero_iff two_ne_zero |>.1 <|
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h e he
  · rw [mem_expSet, not_le] at he
    exact coeff_eq_zero_of_totalDegree_lt (hq.trans_lt he)

theorem tau_smul (r : ℝ) (q : Poly m) : tau m D (r • q) = r ^ 2 * tau m D q := by
  unfold tau
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_pow]

theorem continuous_tau_Phi : Continuous fun c : Par m D => tau m D (Phi c) := by
  unfold tau
  exact continuous_finsetSum _ fun e _ => (continuous_coeff_Phi e).pow 2

theorem tendsto_tau {s : ℕ → Poly m} {t : Poly m}
    (hlim : ∀ e, Tendsto (fun k => (s k).coeff e) atTop (𝓝 (t.coeff e))) :
    Tendsto (fun k => tau m D (s k)) atTop (𝓝 (tau m D t)) := by
  unfold tau
  exact tendsto_finsetSum _ fun e _ => (hlim e).pow 2

theorem tau_Phi_pos {c : Par m D} (hc : c ≠ 0) : 0 < tau m D (Phi c) := by
  refine lt_of_le_of_ne (tau_nonneg _) fun h => hc ?_
  exact (Phi_eq_zero_iff c).1 (tau_eq_zero (totalDegree_Phi_le c) h.symm)

theorem exists_coercive (m D : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c : Par m D, κ * ‖c‖ ^ 4 ≤ tau m D (Phi c) := by
  have hcpt : IsCompact (Metric.sphere (0 : Par m D) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : Par m D) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨c₀, hc₀, hmin⟩ :=
    hcpt.exists_isMinOn hne (continuous_tau_Phi (m := m) (D := D)).continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    rw [h, Metric.mem_sphere, dist_zero_right, norm_zero] at hc₀
    exact zero_ne_one hc₀
  refine ⟨tau m D (Phi c₀), tau_Phi_pos hc₀ne, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero]
    simp only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero]
    exact tau_nonneg _
  · have hnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    set u := ‖c‖⁻¹ • c with hu
    have hu1 : u ∈ Metric.sphere (0 : Par m D) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnorm.ne']
    have hcu : c = ‖c‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hmin' : tau m D (Phi c₀) ≤ tau m D (Phi u) := hmin hu1
    calc tau m D (Phi c₀) * ‖c‖ ^ 4 ≤ tau m D (Phi u) * ‖c‖ ^ 4 := by gcongr
      _ = tau m D (Phi c) := by
        conv_rhs => rw [hcu, Phi_smul, tau_smul]
        ring

theorem isSOS_of_tendsto (s : ℕ → Poly m) (t : Poly m) (hsos : ∀ k, IsSOS (s k))
    (hdeg : ∀ k, (s k).totalDegree ≤ 2 * D)
    (hlim : ∀ e, Tendsto (fun k => (s k).coeff e) atTop (𝓝 (t.coeff e))) : IsSOS t := by
  choose c hc using fun k => exists_Phi_eq (hsos k) (hdeg k)
  obtain ⟨κ, hκ, hcoer⟩ := exists_coercive m D
  obtain ⟨M, hM⟩ := (tendsto_tau (D := D) hlim).bddAbove_range
  -- the parameters are bounded
  have hbound : ∀ k, ‖c k‖ ≤ max 1 (M / κ) := by
    intro k
    have h1 : κ * ‖c k‖ ^ 4 ≤ M := by
      calc κ * ‖c k‖ ^ 4 ≤ tau m D (Phi (c k)) := hcoer (c k)
        _ = tau m D (s k) := by rw [hc k]
        _ ≤ M := hM (Set.mem_range_self k)
    have h2 : ‖c k‖ ^ 4 ≤ M / κ := by rwa [le_div_iff₀ hκ, mul_comm]
    by_cases h : ‖c k‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · push Not at h
      have h3 : ‖c k‖ ≤ ‖c k‖ ^ 4 := by
        calc ‖c k‖ = ‖c k‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖c k‖ ^ 4 := pow_le_pow_right₀ h.le (by norm_num)
      exact (h3.trans h2).trans (le_max_right _ _)
  -- Bolzano--Weierstrass
  obtain ⟨c₀, -, φ, hφ, hlim'⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : Par m D)) (r := max 1 (M / κ)))
    (fun k => mem_closedBall_zero_iff.mpr (hbound k))
  have ht : t = Phi c₀ := by
    ext e
    have h1 : Tendsto (fun i => (s (φ i)).coeff e) atTop (𝓝 ((Phi c₀).coeff e)) := by
      have := ((continuous_coeff_Phi e).tendsto c₀).comp hlim'
      simpa [Function.comp_def, hc] using this
    have h2 : Tendsto (fun i => (s (φ i)).coeff e) atTop (𝓝 (t.coeff e)) :=
      (hlim e).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h2 h1
  rw [ht]
  exact isSOS_Phi c₀

/-! The closedness statement in the finite-dimensional coefficient space of the
polynomials of degree `≤ 2D`. -/

/-- The finite set of exponent vectors of degree `≤ k`. -/
def degSet (m k : ℕ) : Finset (Fin m →₀ ℕ) := (Finsupp.finite_of_degree_le k).toFinset

theorem mem_degSet {k : ℕ} {e : Fin m →₀ ℕ} : e ∈ degSet m k ↔ e.degree ≤ k := by
  simp [degSet]

/-- The polynomial with coefficient vector `c` on the monomials of degree `≤ k`. -/
def toPolyₗ (m k : ℕ) : (degSet m k → ℝ) →ₗ[ℝ] Poly m :=
  ∑ v : degSet m k, (monomial v.1).comp (LinearMap.proj v)

theorem toPolyₗ_apply {k : ℕ} (c : degSet m k → ℝ) :
    toPolyₗ m k c = ∑ v : degSet m k, monomial v.1 (c v) := by
  simp only [toPolyₗ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem coeff_toPolyₗ_of_mem {k : ℕ} (c : degSet m k → ℝ) {e : Fin m →₀ ℕ}
    (he : e ∈ degSet m k) : (toPolyₗ m k c).coeff e = c ⟨e, he⟩ := by
  rw [toPolyₗ_apply, coeff_sum, Finset.sum_eq_single ⟨e, he⟩]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro v _ hv
    rw [coeff_monomial, ite_eq_right]
    intro h
    exact hv (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_toPolyₗ_of_not_mem {k : ℕ} (c : degSet m k → ℝ) {e : Fin m →₀ ℕ}
    (he : e ∉ degSet m k) : (toPolyₗ m k c).coeff e = 0 := by
  rw [toPolyₗ_apply, coeff_sum]
  exact Finset.sum_eq_zero fun v _ => by
    rw [coeff_monomial, ite_eq_right]
    intro h
    exact he (h ▸ v.2)

theorem totalDegree_toPolyₗ_le {k : ℕ} (c : degSet m k → ℝ) :
    (toPolyₗ m k c).totalDegree ≤ k := by
  rw [toPolyₗ_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun v _ => ?_)
  exact (totalDegree_monomial_le _ _).trans (mem_degSet.1 v.2)

/-- Every polynomial of degree `≤ k` is `toPolyₗ m k` of its coefficient vector. -/
theorem toPolyₗ_coeff {k : ℕ} {q : Poly m} (hq : q.totalDegree ≤ k) :
    toPolyₗ m k (fun v => q.coeff v.1) = q := by
  ext e
  by_cases he : e ∈ degSet m k
  · rw [coeff_toPolyₗ_of_mem _ he]
  · rw [coeff_toPolyₗ_of_not_mem _ he]
    rw [mem_degSet, not_le] at he
    exact (coeff_eq_zero_of_totalDegree_lt (hq.trans_lt he)).symm

/-- **Closedness of the sos cone** ([26, 2.4.6 Proposition] of the paper), in fixed dimension and
degree: in the coefficient space
`degSet m (2 * D) → ℝ` of the polynomials of degree `≤ 2D` in `m` variables, the coefficient
vectors of sums of squares form a closed set. -/
theorem isClosed_sos_cone (m D : ℕ) :
    IsClosed {c : degSet m (2 * D) → ℝ | IsSOS (toPolyₗ m (2 * D) c)} := by
  refine IsSeqClosed.isClosed fun c c₀ hc hlim => ?_
  refine isSOS_of_tendsto (D := D) (fun k => toPolyₗ m (2 * D) (c k)) _ hc
    (fun k => totalDegree_toPolyₗ_le _) fun e => ?_
  by_cases he : e ∈ degSet m (2 * D)
  · simp only [coeff_toPolyₗ_of_mem _ he]
    exact tendsto_pi_nhds.1 hlim ⟨e, he⟩
  · simp only [coeff_toPolyₗ_of_not_mem _ he]
    exact tendsto_const_nhds

end ClosedCone

end AnyDim
end
