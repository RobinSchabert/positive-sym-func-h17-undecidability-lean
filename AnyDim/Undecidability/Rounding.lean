module

public import AnyDim.Undecidability.Basic

/-!
# Section 2.2: Approximating integer vectors with symmetric functions (Lemma 2.3)

Source: Debus--Schabert, Section 2.2.

Fix `k ≥ 1`.  The data labels are `a_j = j + 1` (`1 ≤ j ≤ k`); with the zero-based index
`j : Fin k` used here, `label k j = j + 2`.  Together with the two auxiliary labels `1/2`
and `1` they form `𝒜 = {1/2, 1, 2, …, k + 1}`, a set with `m = k + 2` elements.

* `Qpoly k = Q(T) = ∏_{a ∈ 𝒜} (T - a)`, `Rpoly k = R(T) = T Q(T)`.
* `ell k j = ℓ_j(T)`, the rational Lagrange polynomial: degree `m`, `ℓ_j(0) = 0`,
  `ℓ_j(a) = 1_{a = a_j}` for `a ∈ 𝒜`.
* `nearest k t = ρ(t)`: the point of `{0} ∪ 𝒜` nearest to `t ≥ 0`, the smaller one in a tie;
  `roundInd k j t = ρ_j(t) = 1_{ρ(t) = a_j}`.
* `Cconst k = C`: the explicit integer constant of Lemma 2.3, see (4) (computable from `k`).
* For a finite tuple `z` with `z_i ≥ 0`: `Ssum z j = S_j`, `Ncount z j = N_j ∈ ℕ`,
  `Usum z = U`, `Esum k z = E`.
* Lemma 2.3: inequality (1) `abs_ell_sub_roundInd_le`, and (3)
  `lemma_2_3_dist` (`‖S - N‖² ≤ k C² U E`) and `lemma_2_3_norm` (`‖N‖² ≤ 16 U²`).

All proofs in this file are complete (no `sorry`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace AnyDim.Undecidability

variable (k : ℕ)

/-! ### Labels and the polynomials `Q`, `R`, `ℓ_j` -/

/-- The data label `a_j = j + 1` of the paper (`1 ≤ j ≤ k`); with the zero-based index
`j : Fin k`, this is `j + 2`.  Its multiplicity in a tuple encodes the `j`-th integer. -/
def label (j : Fin k) : ℚ := ((j : ℕ) : ℚ) + 2

/-- The label set `𝒜 = {1/2, 1, 2, …, k + 1}`.  The labels `1/2` and `1` enforce the
normalization `p_1 = p_2` in Lemma 2.5 and Section 2.4. -/
def labels : Finset ℚ := {1 / 2, 1} ∪ Finset.univ.image (label k)

/-- `m = k + 2`, the number of labels. -/
def mconst : ℕ := k + 2

/-- `Q(T) = ∏_{a ∈ 𝒜} (T - a)`. -/
def Qpoly : Polynomial ℚ := ∏ a ∈ labels k, (Polynomial.X - Polynomial.C a)

/-- `R(T) = T Q(T)`. -/
def Rpoly : Polynomial ℚ := Polynomial.X * Qpoly k

/-- The rational Lagrange polynomial of Section 2.2:
`ℓ_j(T) = (T / a_j) ∏_{a ∈ 𝒜 ∖ {a_j}} (T - a) / (a_j - a)`. -/
def ell (j : Fin k) : Polynomial ℚ :=
  Polynomial.C (1 / label k j) * Polynomial.X *
    ∏ a ∈ (labels k).erase (label k j),
      (Polynomial.C (1 / (label k j - a)) * (Polynomial.X - Polynomial.C a))

theorem label_pos (j : Fin k) : 0 < label k j := by
  unfold label; positivity

theorem label_mem_labels (j : Fin k) : label k j ∈ labels k := by
  unfold labels
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))

theorem label_injective : Function.Injective (label k) := by
  intro i j hij
  unfold label at hij
  exact Fin.ext (by exact_mod_cast (add_right_cancel hij))

theorem mem_labels_iff {a : ℚ} :
    a ∈ labels k ↔ a = 1 / 2 ∨ a = 1 ∨ ∃ j, label k j = a := by
  unfold labels
  simp [Finset.mem_insert, Finset.mem_image]

theorem two_le_label (j : Fin k) : 2 ≤ label k j := by
  unfold label
  have : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := Nat.cast_nonneg _
  linarith

/-- Every label is at most `k + 1`. -/
theorem label_le {a : ℚ} (ha : a ∈ labels k) : a ≤ (k : ℚ) + 1 := by
  rcases (mem_labels_iff k).mp ha with rfl | rfl | ⟨j, rfl⟩
  · have : (0 : ℚ) ≤ k := Nat.cast_nonneg _
    linarith
  · have : (0 : ℚ) ≤ k := Nat.cast_nonneg _
    linarith
  · unfold label
    have : ((j : ℕ) : ℚ) + 1 ≤ k := by exact_mod_cast j.isLt
    linarith

/-- `|𝒜| = m = k + 2`. -/
theorem card_labels : (labels k).card = mconst k := by
  unfold labels mconst
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (label_injective k),
    Finset.card_univ, Fintype.card_fin, Finset.card_pair (by norm_num)]
  · ring
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    have := two_le_label k j
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h | h <;> rw [h] at this <;> norm_num at this

/-- `deg Q = m`. -/
theorem Qpoly_natDegree : (Qpoly k).natDegree = mconst k := by
  unfold Qpoly
  rw [← card_labels k]
  exact Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ (fun a => a)

theorem Qpoly_monic : (Qpoly k).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a

/-- `Q(a) = 0` for every label `a ∈ 𝒜`. -/
theorem Qpoly_eval_label {a : ℚ} (ha : a ∈ labels k) : (Qpoly k).eval a = 0 := by
  unfold Qpoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero ha (by simp)

/-- `D_j(T) = R(T) / (T - a_j) = T ∏_{a ∈ 𝒜 ∖ {a_j}} (T - a)` (degree `m`). -/
def Dpoly (j : Fin k) : Polynomial ℚ :=
  Polynomial.X * ∏ a ∈ (labels k).erase (label k j), (Polynomial.X - Polynomial.C a)

/-- The denominator `a_j ∏_{a ∈ 𝒜 ∖ {a_j}} (a_j - a)` of `ℓ_j`; it equals `R'(a_j)`. -/
def ellDenom (j : Fin k) : ℚ :=
  label k j * ∏ a ∈ (labels k).erase (label k j), (label k j - a)

theorem ellDenom_ne_zero (j : Fin k) : ellDenom k j ≠ 0 := by
  unfold ellDenom
  refine mul_ne_zero (label_pos k j).ne' (Finset.prod_ne_zero_iff.mpr fun a ha => ?_)
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm

theorem ell_eq_C_mul_Dpoly (j : Fin k) :
    ell k j = Polynomial.C (1 / ellDenom k j) * Dpoly k j := by
  unfold ell Dpoly ellDenom
  rw [Finset.prod_mul_distrib, ← map_prod Polynomial.C]
  simp only [one_div, mul_inv, map_mul, Finset.prod_inv_distrib]
  ring

/-- `R(T) = (T - a_j) D_j(T)`. -/
theorem Rpoly_eq_mul_Dpoly (j : Fin k) :
    Rpoly k = (Polynomial.X - Polynomial.C (label k j)) * Dpoly k j := by
  unfold Rpoly Qpoly Dpoly
  rw [← Finset.mul_prod_erase _ _ (label_mem_labels k j)]
  ring

theorem Dpoly_eval_label (j : Fin k) : (Dpoly k j).eval (label k j) = ellDenom k j := by
  unfold Dpoly ellDenom
  simp [Polynomial.eval_prod]

theorem Dpoly_ne_zero (j : Fin k) : Dpoly k j ≠ 0 := by
  unfold Dpoly
  exact mul_ne_zero Polynomial.X_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun a _ => Polynomial.X_sub_C_ne_zero a)

/-- `deg D_j = m`. -/
theorem Dpoly_natDegree (j : Fin k) : (Dpoly k j).natDegree = mconst k := by
  unfold Dpoly
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun a _ => Polynomial.X_sub_C_ne_zero a),
    Polynomial.natDegree_X, Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ (fun a => a),
    Finset.card_erase_of_mem (label_mem_labels k j), card_labels]
  unfold mconst
  omega

/-- `deg ℓ_j = m`. -/
theorem ell_natDegree (j : Fin k) : (ell k j).natDegree = mconst k := by
  rw [ell_eq_C_mul_Dpoly, Polynomial.natDegree_C_mul (one_div_ne_zero (ellDenom_ne_zero k j)),
    Dpoly_natDegree]

/-- `ℓ_j(0) = 0`. -/
theorem ell_eval_zero (j : Fin k) : (ell k j).eval 0 = 0 := by
  simp [ell]

theorem ell_coeff_zero (j : Fin k) : (ell k j).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact ell_eval_zero k j

/-- `ℓ_j(a) = 1_{a = a_j}` for every label `a ∈ 𝒜`. -/
theorem ell_eval_label (j : Fin k) {a : ℚ} (ha : a ∈ labels k) :
    (ell k j).eval a = if a = label k j then 1 else 0 := by
  rw [ell_eq_C_mul_Dpoly, Polynomial.eval_mul, Polynomial.eval_C]
  split_ifs with h
  · rw [h, Dpoly_eval_label, one_div, inv_mul_cancel₀ (ellDenom_ne_zero k j)]
  · unfold Dpoly
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, ha⟩) (by simp)]
    simp

/-- `R'(a_j) = a_j ∏_{a ≠ a_j} (a_j - a)` (`a_j` is a simple root of `R`). -/
theorem derivative_Rpoly_eval_label (j : Fin k) :
    (Polynomial.derivative (Rpoly k)).eval (label k j) = ellDenom k j := by
  rw [Rpoly_eq_mul_Dpoly, Polynomial.derivative_mul, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_mul, Dpoly_eval_label]
  simp

/-- The second expression for `ℓ_j`: `(T - a_j) ℓ_j(T) = R(T) / R'(a_j)`. -/
theorem sub_mul_ell_eq (j : Fin k) :
    (Polynomial.X - Polynomial.C (label k j)) * ell k j =
      Polynomial.C (1 / (Polynomial.derivative (Rpoly k)).eval (label k j)) * Rpoly k := by
  rw [derivative_Rpoly_eval_label, ell_eq_C_mul_Dpoly, Rpoly_eq_mul_Dpoly]
  ring

theorem derivative_Rpoly_eval_label_ne_zero (j : Fin k) :
    (Polynomial.derivative (Rpoly k)).eval (label k j) ≠ 0 := by
  rw [derivative_Rpoly_eval_label]
  exact ellDenom_ne_zero k j

/-! ### Nearest-point rounding `ρ` -/

/-- The set `{0} ∪ 𝒜` as a finite set of real numbers. -/
def labels0 : Finset ℝ := insert 0 ((labels k).image (fun a : ℚ => (a : ℝ)))

theorem zero_mem_labels0 : (0 : ℝ) ∈ labels0 k := by
  simp [labels0]

theorem label_mem_labels0 (j : Fin k) : ((label k j : ℚ) : ℝ) ∈ labels0 k := by
  unfold labels0
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (label_mem_labels k j))

theorem coe_mem_labels0 {a : ℚ} (ha : a ∈ labels k) : ((a : ℚ) : ℝ) ∈ labels0 k := by
  unfold labels0
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)

/-- The nearest-point candidates `{a ∈ {0} ∪ 𝒜 : |t - a| ≤ |t - b| for all b}` form a
nonempty set. -/
theorem nearestCandidates_nonempty (t : ℝ) :
    ((labels0 k).filter (fun a => ∀ b ∈ labels0 k, |t - a| ≤ |t - b|)).Nonempty := by
  obtain ⟨a, ha, h⟩ :=
    (labels0 k).exists_min_image (fun a => |t - a|) ⟨0, zero_mem_labels0 k⟩
  exact Finset.filter_nonempty_iff.mpr ⟨a, ha, h⟩

/-- `ρ(t)`: a nearest point of `{0} ∪ 𝒜` to `t`, choosing the smaller point in a tie. -/
def nearest (t : ℝ) : ℝ :=
  ((labels0 k).filter (fun a => ∀ b ∈ labels0 k, |t - a| ≤ |t - b|)).min'
    (nearestCandidates_nonempty k t)

/-- `ρ_j(t) = 1_{ρ(t) = a_j}`. -/
def roundInd (j : Fin k) (t : ℝ) : ℝ :=
  if nearest k t = ((label k j : ℚ) : ℝ) then 1 else 0

theorem nearest_mem (t : ℝ) : nearest k t ∈ labels0 k :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (nearestCandidates_nonempty k t))).1

theorem nearest_isNearest (t : ℝ) : ∀ b ∈ labels0 k, |t - nearest k t| ≤ |t - b| :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (nearestCandidates_nonempty k t))).2

/-- In a tie the smaller point is chosen. -/
theorem nearest_le_of_isNearest (t : ℝ) {a : ℝ} (ha : a ∈ labels0 k)
    (h : ∀ b ∈ labels0 k, |t - a| ≤ |t - b|) : nearest k t ≤ a :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨ha, h⟩)

/-- Every element of `{0} ∪ 𝒜` is a half-integer `m / 2`. -/
theorem exists_nat_of_mem_labels0 {a : ℝ} (ha : a ∈ labels0 k) : ∃ m : ℕ, a = (m : ℝ) / 2 := by
  unfold labels0 at ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact ⟨0, by simp⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    rcases (mem_labels_iff k).mp hq with rfl | rfl | ⟨j, rfl⟩
    · exact ⟨1, by push_cast; ring⟩
    · exact ⟨2, by push_cast; ring⟩
    · refine ⟨2 * (j : ℕ) + 4, ?_⟩
      unfold label
      push_cast
      ring

/-- Two distinct elements of `{0} ∪ 𝒜` are at distance at least `1/2`. -/
theorem labels0_dist {a b : ℝ} (ha : a ∈ labels0 k) (hb : b ∈ labels0 k) (hab : a ≠ b) :
    1 / 2 ≤ |a - b| := by
  obtain ⟨ma, rfl⟩ := exists_nat_of_mem_labels0 k ha
  obtain ⟨mb, rfl⟩ := exists_nat_of_mem_labels0 k hb
  have hne : ma ≠ mb := fun h => hab (by rw [h])
  rcases lt_or_gt_of_ne hne with h | h
  · have : (ma : ℝ) + 1 ≤ mb := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have : (mb : ℝ) + 1 ≤ ma := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem labels0_nonneg {a : ℝ} (ha : a ∈ labels0 k) : 0 ≤ a := by
  obtain ⟨m, rfl⟩ := exists_nat_of_mem_labels0 k ha
  positivity

theorem half_le_of_mem_labels0 {a : ℝ} (ha : a ∈ labels0 k) (ha0 : a ≠ 0) : 1 / 2 ≤ a := by
  have := labels0_dist k ha (zero_mem_labels0 k) ha0
  rwa [sub_zero, abs_of_nonneg (labels0_nonneg k ha)] at this

/-- A label is its own nearest point. -/
theorem nearest_of_mem {a : ℝ} (ha : a ∈ labels0 k) : nearest k a = a := by
  have h := nearest_isNearest k a a ha
  rw [sub_self, abs_zero] at h
  have := abs_nonpos_iff.mp h
  linarith

/-- If `ρ(t) ≠ a_j` then `|t - a_j| ≥ 1/4` (nearest-point rounding). -/
theorem quarter_le_of_nearest_ne (j : Fin k) {t : ℝ}
    (h : nearest k t ≠ ((label k j : ℚ) : ℝ)) : 1 / 4 ≤ |t - ((label k j : ℚ) : ℝ)| := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := nearest_isNearest k t _ (label_mem_labels0 k j)
  have h2 := labels0_dist k (label_mem_labels0 k j) (nearest_mem k t) (Ne.symm h)
  have h3 := abs_sub_le ((label k j : ℚ) : ℝ) t (nearest k t)
  rw [abs_sub_comm ((label k j : ℚ) : ℝ) t] at h3
  linarith

/-- If `ρ(t) = a_j` then every other label `b` has `|t - b| ≥ 1/4`. -/
theorem quarter_le_of_nearest_eq (j : Fin k) {t : ℝ}
    (h : nearest k t = ((label k j : ℚ) : ℝ)) {b : ℝ} (hb : b ∈ labels0 k)
    (hbj : b ≠ ((label k j : ℚ) : ℝ)) : 1 / 4 ≤ |t - b| := by
  have h1 := nearest_isNearest k t b hb
  rw [h] at h1
  have h2 := labels0_dist k (label_mem_labels0 k j) hb (Ne.symm hbj)
  have h3 := abs_sub_le ((label k j : ℚ) : ℝ) t b
  rw [abs_sub_comm ((label k j : ℚ) : ℝ) t] at h3
  linarith

/-- If `ρ(t) ≠ 0` then `t ≥ 1/4`. -/
theorem quarter_le_of_nearest_ne_zero {t : ℝ} (ht : 0 ≤ t) (h : nearest k t ≠ 0) :
    1 / 4 ≤ t := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := nearest_isNearest k t 0 (zero_mem_labels0 k)
  rw [sub_zero, abs_of_nonneg ht] at h1
  have h2 := half_le_of_mem_labels0 k (nearest_mem k t) h
  have h3 : |t - nearest k t| = nearest k t - t := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-! ### The constant `C` of Lemma 2.3 -/

/-- `M_j(T) = (ℓ_j(T) - 1) / (T - a_j)` (exact division, degree `m - 1`). -/
def Mpoly (j : Fin k) : Polynomial ℚ :=
  (ell k j - 1) /ₘ (Polynomial.X - Polynomial.C (label k j))

/-- `B_j`: the sum of the absolute values of the coefficients of `M_j`. -/
def Bconst (j : Fin k) : ℚ :=
  ∑ i ∈ (Mpoly k j).support, |(Mpoly k j).coeff i|

/-- `T_0 = 2 (k + 1)`. -/
def T0 : ℚ := 2 * ((k : ℚ) + 1)

/-- The rounding constant `C` of Lemma 2.3 (effectively computable from `k`), see (4):
`C = max (1, max_j ⌈4 / |R'(a_j)|⌉, max_j ⌈4^m B_j T_0^{m-1}⌉)`, as in the proof of
Lemma 2.3 (the ceilings only enlarge the lower bound (4), which is allowed there). -/
def Cconst : ℕ :=
  max 1
    (max (Finset.univ.sup fun j : Fin k =>
            Nat.ceil (4 / |(Polynomial.derivative (Rpoly k)).eval (label k j)|))
         (Finset.univ.sup fun j : Fin k =>
            Nat.ceil (4 ^ mconst k * Bconst k j * T0 k ^ (mconst k - 1))))

theorem one_le_Cconst : 1 ≤ Cconst k := le_max_left _ _

theorem Cconst_pos : 0 < Cconst k := one_le_Cconst k

/-- `C ≥ 4 / |R'(a_j)|` for every `j`. -/
theorem four_div_le_Cconst (j : Fin k) :
    4 / |(Polynomial.derivative (Rpoly k)).eval (label k j)| ≤ (Cconst k : ℚ) := by
  refine (Nat.le_ceil _).trans ?_
  have h : Nat.ceil (4 / |(Polynomial.derivative (Rpoly k)).eval (label k j)|) ≤ Cconst k :=
    (Finset.le_sup (f := fun j : Fin k =>
        Nat.ceil (4 / |(Polynomial.derivative (Rpoly k)).eval (label k j)|))
      (Finset.mem_univ j)).trans ((le_max_left _ _).trans (le_max_right _ _))
  exact_mod_cast h

/-- `C ≥ 4^m B_j T_0^{m-1}` for every `j`. -/
theorem bound_le_Cconst (j : Fin k) :
    4 ^ mconst k * Bconst k j * T0 k ^ (mconst k - 1) ≤ (Cconst k : ℚ) := by
  refine (Nat.le_ceil _).trans ?_
  have h : Nat.ceil (4 ^ mconst k * Bconst k j * T0 k ^ (mconst k - 1)) ≤ Cconst k :=
    (Finset.le_sup (f := fun j : Fin k =>
        Nat.ceil (4 ^ mconst k * Bconst k j * T0 k ^ (mconst k - 1)))
      (Finset.mem_univ j)).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact_mod_cast h

/-! ### Lemma 2.3 -/

theorem T0_cast : ((T0 k : ℚ) : ℝ) = 2 * ((k : ℝ) + 1) := by
  unfold T0; push_cast; ring

theorem one_le_T0 : (1 : ℝ) ≤ ((T0 k : ℚ) : ℝ) := by
  rw [T0_cast]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  linarith

/-- `R(t) = t Q(t)`. -/
theorem aeval_Rpoly (t : ℝ) :
    Polynomial.aeval t (Rpoly k) = t * Polynomial.aeval t (Qpoly k) := by
  simp [Rpoly]

/-- The formula for `ℓ_j` at a real point: `(t - a_j) ℓ_j(t) = R(t) / R'(a_j)`. -/
theorem sub_mul_aeval_ell (j : Fin k) (t : ℝ) :
    (t - ((label k j : ℚ) : ℝ)) * Polynomial.aeval t (ell k j) =
      ((1 / (Polynomial.derivative (Rpoly k)).eval (label k j) : ℚ) : ℝ) *
        (t * Polynomial.aeval t (Qpoly k)) := by
  have := congrArg (Polynomial.aeval t) (sub_mul_ell_eq k j)
  simpa [Rpoly] using this

/-- Branch `ρ(t) ≠ a_j` of Lemma 2.3: here `ρ_j(t) = 0`. -/
theorem abs_ell_le_of_nearest_ne (j : Fin k) {t : ℝ} (ht : 0 ≤ t)
    (h : nearest k t ≠ ((label k j : ℚ) : ℝ)) :
    |Polynomial.aeval t (ell k j)| ≤ (Cconst k : ℝ) * t * |Polynomial.aeval t (Qpoly k)| := by
  have hu := quarter_le_of_nearest_ne k j h
  have hid := sub_mul_aeval_ell k j t
  have hC : 4 * |((1 / (Polynomial.derivative (Rpoly k)).eval (label k j) : ℚ) : ℝ)| ≤
      (Cconst k : ℝ) := by
    have h4 := four_div_le_Cconst k j
    have : (4 : ℝ) * |((1 / (Polynomial.derivative (Rpoly k)).eval (label k j) : ℚ) : ℝ)| =
        ((4 / |(Polynomial.derivative (Rpoly k)).eval (label k j)| : ℚ) : ℝ) := by
      push_cast
      rw [abs_div, abs_one]; ring
    rw [this]
    exact_mod_cast h4
  set u := t - ((label k j : ℚ) : ℝ)
  set Aval := Polynomial.aeval t (ell k j)
  set B := t * Polynomial.aeval t (Qpoly k)
  set c : ℝ := ((1 / (Polynomial.derivative (Rpoly k)).eval (label k j) : ℚ) : ℝ)
  have habs : |Aval| * |u| = |c| * |B| := by rw [← abs_mul, ← abs_mul, mul_comm, hid]
  have hB : |B| = t * |Polynomial.aeval t (Qpoly k)| := by rw [abs_mul, abs_of_nonneg ht]
  have h1 : 1 ≤ 4 * |u| := by linarith
  calc |Aval| = |Aval| * 1 := (mul_one _).symm
    _ ≤ |Aval| * (4 * |u|) := by gcongr
    _ = 4 * (|Aval| * |u|) := by ring
    _ = (4 * |c|) * |B| := by rw [habs]; ring
    _ ≤ (Cconst k : ℝ) * |B| := by gcongr
    _ = (Cconst k : ℝ) * t * |Polynomial.aeval t (Qpoly k)| := by rw [hB]; ring

/-- A univariate polynomial is bounded by the sum of the absolute values of its coefficients
times `M^d`, where `|t| ≤ M`, `1 ≤ M` and `d` bounds the degree. -/
theorem abs_aeval_le_sum_abs_coeff (p : Polynomial ℚ) {t M : ℝ} (hM : 1 ≤ M) (ht : |t| ≤ M)
    {d : ℕ} (hd : p.natDegree ≤ d) :
    |Polynomial.aeval t p| ≤ ((∑ i ∈ p.support, |p.coeff i| : ℚ) : ℝ) * M ^ d := by
  have hsum : ((∑ i ∈ p.support, |p.coeff i| : ℚ) : ℝ) =
      ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| := by
    push_cast
    exact Finset.sum_subset Polynomial.supp_subset_range_natDegree_succ
      (fun i _ hi => by simp [Polynomial.notMem_support_iff.mp hi])
  rw [hsum, Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Rat.smul_def, abs_mul, abs_pow]
  have hi' : i ≤ d := by have := Finset.mem_range.mp hi; omega
  have h0 : 0 ≤ |t| := abs_nonneg t
  calc |(p.coeff i : ℝ)| * |t| ^ i ≤ |(p.coeff i : ℝ)| * M ^ i := by gcongr
    _ ≤ |(p.coeff i : ℝ)| * M ^ d := by gcongr

/-- `(T - a_j) M_j(T) = ℓ_j(T) - 1` (the division is exact). -/
theorem Mpoly_mul (j : Fin k) :
    (Polynomial.X - Polynomial.C (label k j)) * Mpoly k j = ell k j - 1 := by
  unfold Mpoly
  rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
  simp [Polynomial.IsRoot, ell_eval_label k j (label_mem_labels k j)]

/-- `deg M_j ≤ m - 1`. -/
theorem Mpoly_natDegree_le (j : Fin k) : (Mpoly k j).natDegree ≤ mconst k - 1 := by
  unfold Mpoly
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _), Polynomial.natDegree_X_sub_C]
  have := Polynomial.natDegree_sub_le (ell k j) 1
  rw [ell_natDegree, Polynomial.natDegree_one] at this
  omega

/-- A lower bound for `|D_j(t)|` from lower bounds for its `m` factors. -/
theorem Dpoly_abs_ge (j : Fin k) {t μ : ℝ} (hμ : 0 ≤ μ) (ht : μ ≤ |t|)
    (h : ∀ a ∈ (labels k).erase (label k j), μ ≤ |t - (a : ℝ)|) :
    μ ^ mconst k ≤ |Polynomial.aeval t (Dpoly k j)| := by
  unfold Dpoly
  simp only [map_mul, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast]
  rw [abs_mul, Finset.abs_prod]
  have hcard : ((labels k).erase (label k j)).card = mconst k - 1 := by
    rw [Finset.card_erase_of_mem (label_mem_labels k j), card_labels]
  have hm : μ ^ mconst k = μ * μ ^ (mconst k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by unfold mconst; omega)]
  rw [hm]
  refine mul_le_mul ht ?_ (pow_nonneg hμ _) (abs_nonneg _)
  rw [← hcard, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hμ) h

/-- Branch `ρ(t) = a_j` of Lemma 2.3: here `ρ_j(t) = 1`. -/
theorem abs_ell_sub_one_le_of_nearest_eq (j : Fin k) {t : ℝ} (ht : 0 ≤ t)
    (h : nearest k t = ((label k j : ℚ) : ℝ)) :
    |Polynomial.aeval t (ell k j) - 1| ≤ (Cconst k : ℝ) * t * |Polynomial.aeval t (Qpoly k)| := by
  have hM : Polynomial.aeval t (ell k j) - 1 =
      (t - ((label k j : ℚ) : ℝ)) * Polynomial.aeval t (Mpoly k j) := by
    have := congrArg (Polynomial.aeval t) (Mpoly_mul k j)
    simpa using this.symm
  have hR : t * Polynomial.aeval t (Qpoly k) =
      (t - ((label k j : ℚ) : ℝ)) * Polynomial.aeval t (Dpoly k j) := by
    have := congrArg (Polynomial.aeval t) (Rpoly_eq_mul_Dpoly k j)
    simpa [Rpoly] using this
  have hC : (4 : ℝ) ^ mconst k * (Bconst k j : ℝ) * ((T0 k : ℚ) : ℝ) ^ (mconst k - 1) ≤
      (Cconst k : ℝ) := by
    have h' := Rat.cast_le (K := ℝ) |>.mpr (bound_le_Cconst k j)
    push_cast at h'
    exact h'
  have hC0 : (0 : ℝ) ≤ Cconst k := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ Bconst k j := by
    unfold Bconst; push_cast
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT0 := one_le_T0 k
  have hT0c := T0_cast k
  have hm1 : mconst k = (mconst k - 1) + 1 := by unfold mconst; omega
  -- the key estimate `|M_j(t)| ≤ C |D_j(t)|`
  have key : |Polynomial.aeval t (Mpoly k j)| ≤ (Cconst k : ℝ) * |Polynomial.aeval t (Dpoly k j)| := by
    rcases le_or_gt t ((T0 k : ℚ) : ℝ) with hle | hlt
    · -- `0 ≤ t ≤ T_0`
      have hq : ∀ a ∈ (labels k).erase (label k j), (1 / 4 : ℝ) ≤ |t - (a : ℝ)| := fun a ha =>
        quarter_le_of_nearest_eq k j h (coe_mem_labels0 k (Finset.mem_of_mem_erase ha))
          (by exact_mod_cast Finset.ne_of_mem_erase ha)
      have ht4 : (1 / 4 : ℝ) ≤ |t| := by
        rw [abs_of_nonneg ht]
        refine quarter_le_of_nearest_ne_zero k ht ?_
        rw [h]
        exact_mod_cast (label_pos k j).ne'
      have hD := Dpoly_abs_ge k j (by norm_num) ht4 hq
      have hMb := abs_aeval_le_sum_abs_coeff (Mpoly k j) hT0
        (by rw [abs_of_nonneg ht]; exact hle) (Mpoly_natDegree_le k j)
      have h41 : (4 : ℝ) ^ mconst k * (1 / 4) ^ mconst k = 1 := by
        rw [← mul_pow]; norm_num
      calc |Polynomial.aeval t (Mpoly k j)|
          ≤ (Bconst k j : ℝ) * ((T0 k : ℚ) : ℝ) ^ (mconst k - 1) := hMb
        _ = ((4 : ℝ) ^ mconst k * (1 / 4) ^ mconst k) *
              ((Bconst k j : ℝ) * ((T0 k : ℚ) : ℝ) ^ (mconst k - 1)) := by rw [h41, one_mul]
        _ = ((4 : ℝ) ^ mconst k * (Bconst k j : ℝ) * ((T0 k : ℚ) : ℝ) ^ (mconst k - 1)) *
              (1 / 4) ^ mconst k := by ring
        _ ≤ (Cconst k : ℝ) * (1 / 4) ^ mconst k := by gcongr
        _ ≤ (Cconst k : ℝ) * |Polynomial.aeval t (Dpoly k j)| := by gcongr
    · -- `t ≥ T_0 = 2 (k + 1)`
      have hq : ∀ a ∈ (labels k).erase (label k j), t / 2 ≤ |t - (a : ℝ)| := fun a ha => by
        have ha' : (a : ℝ) ≤ (k : ℝ) + 1 := by
          exact_mod_cast label_le k (Finset.mem_of_mem_erase ha)
        rw [abs_of_nonneg (by linarith)]
        linarith
      have ht2 : t / 2 ≤ |t| := by rw [abs_of_nonneg ht]; linarith
      have hD := Dpoly_abs_ge k j (by linarith) ht2 hq
      have hMb := abs_aeval_le_sum_abs_coeff (Mpoly k j) (M := t) (by linarith)
        (by rw [abs_of_nonneg ht]) (Mpoly_natDegree_le k j)
      -- `2^m B ≤ C T_0`
      have hCB : (2 : ℝ) ^ mconst k * (Bconst k j : ℝ) ≤ (Cconst k : ℝ) * ((T0 k : ℚ) : ℝ) := by
        have h24 : (2 : ℝ) ^ mconst k ≤ 4 ^ mconst k := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have hT1 : (1 : ℝ) ≤ ((T0 k : ℚ) : ℝ) ^ mconst k := one_le_pow₀ hT0
        have hTm : ((T0 k : ℚ) : ℝ) ^ mconst k =
            ((T0 k : ℚ) : ℝ) ^ (mconst k - 1) * ((T0 k : ℚ) : ℝ) := by
          conv_lhs => rw [hm1]
          exact pow_succ _ _
        calc (2 : ℝ) ^ mconst k * (Bconst k j : ℝ)
            ≤ 4 ^ mconst k * (Bconst k j : ℝ) := by gcongr
          _ ≤ 4 ^ mconst k * (Bconst k j : ℝ) * ((T0 k : ℚ) : ℝ) ^ mconst k := by
              exact le_mul_of_one_le_right (by positivity) hT1
          _ = (4 ^ mconst k * (Bconst k j : ℝ) * ((T0 k : ℚ) : ℝ) ^ (mconst k - 1)) *
                ((T0 k : ℚ) : ℝ) := by rw [hTm]; ring
          _ ≤ (Cconst k : ℝ) * ((T0 k : ℚ) : ℝ) := by gcongr
      have h2m : (2 : ℝ) ^ mconst k = 2 ^ (mconst k - 1) * 2 := by
        conv_lhs => rw [hm1]
        exact pow_succ _ _
      have hpow : (2 : ℝ) ^ (mconst k - 1) * (t / 2) ^ (mconst k - 1) = t ^ (mconst k - 1) := by
        rw [← mul_pow]; congr 1; ring
      have hCt : (Cconst k : ℝ) * ((T0 k : ℚ) : ℝ) ≤ (Cconst k : ℝ) * t :=
        mul_le_mul_of_nonneg_left hlt.le hC0
      have hstep : (Bconst k j : ℝ) * 2 ^ (mconst k - 1) ≤ (Cconst k : ℝ) * (t / 2) := by
        rw [h2m] at hCB
        linarith
      have hpos : (0 : ℝ) ≤ (t / 2) ^ (mconst k - 1) := by positivity
      calc |Polynomial.aeval t (Mpoly k j)|
          ≤ (Bconst k j : ℝ) * t ^ (mconst k - 1) := hMb
        _ = (Bconst k j : ℝ) * 2 ^ (mconst k - 1) * (t / 2) ^ (mconst k - 1) := by
            rw [mul_assoc, hpow]
        _ ≤ (Cconst k : ℝ) * (t / 2) * (t / 2) ^ (mconst k - 1) :=
            mul_le_mul_of_nonneg_right hstep hpos
        _ = (Cconst k : ℝ) * (t / 2) ^ mconst k := by
            conv_rhs => rw [hm1, pow_succ]
            ring
        _ ≤ (Cconst k : ℝ) * |Polynomial.aeval t (Dpoly k j)| := by gcongr
  have hB : (Cconst k : ℝ) * t * |Polynomial.aeval t (Qpoly k)| =
      (Cconst k : ℝ) * (|t - ((label k j : ℚ) : ℝ)| * |Polynomial.aeval t (Dpoly k j)|) := by
    rw [← abs_mul, ← hR, abs_mul, abs_of_nonneg ht]
    ring
  rw [hM, abs_mul, hB]
  calc |t - ((label k j : ℚ) : ℝ)| * |Polynomial.aeval t (Mpoly k j)|
      ≤ |t - ((label k j : ℚ) : ℝ)| * ((Cconst k : ℝ) * |Polynomial.aeval t (Dpoly k j)|) := by
        gcongr
    _ = (Cconst k : ℝ) * (|t - ((label k j : ℚ) : ℝ)| * |Polynomial.aeval t (Dpoly k j)|) := by
        ring

/-- **Lemma 2.3, inequality (1):** `|ℓ_j(t) - ρ_j(t)| ≤ C t |Q(t)|` for `t ≥ 0`. -/
theorem abs_ell_sub_roundInd_le (j : Fin k) {t : ℝ} (ht : 0 ≤ t) :
    |Polynomial.aeval t (ell k j) - roundInd k j t| ≤
      (Cconst k : ℝ) * t * |Polynomial.aeval t (Qpoly k)| := by
  unfold roundInd
  split_ifs with h
  · exact abs_ell_sub_one_le_of_nearest_eq k j ht h
  · rw [sub_zero]
    exact abs_ell_le_of_nearest_ne k j ht h

/-! ### Tuple quantities `S_j, N_j, U, E` -/

/-- `E = ∑_i z_i Q(z_i)²`. -/
def Esum {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ∑ i, z i * (Polynomial.aeval (z i) (Qpoly k)) ^ 2

variable {k}

/-- `S_j = ∑_i ℓ_j(z_i)`. -/
def Ssum {n : ℕ} (z : Fin n → ℝ) (j : Fin k) : ℝ :=
  ∑ i, Polynomial.aeval (z i) (ell k j)

/-- `N_j = ∑_i ρ_j(z_i)`, the number of coordinates rounded to `a_j` (a natural number). -/
def Ncount {n : ℕ} (z : Fin n → ℝ) (j : Fin k) : ℕ :=
  (Finset.univ.filter fun i => nearest k (z i) = ((label k j : ℚ) : ℝ)).card

/-- `U = ∑_i z_i`. -/
def Usum {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ∑ i, z i

theorem Usum_eq_tuplePower {n : ℕ} (z : Fin n → ℝ) : Usum z = tuplePower z 1 := by
  simp [Usum, tuplePower]

theorem Usum_nonneg {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) : 0 ≤ Usum z :=
  Finset.sum_nonneg fun i _ => hz i

theorem Esum_nonneg {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) : 0 ≤ Esum k z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)

/-- `N_j = ∑_i ρ_j(z_i)` as a real number. -/
theorem Ncount_eq_sum_roundInd {n : ℕ} (z : Fin n → ℝ) (j : Fin k) :
    (Ncount z j : ℝ) = ∑ i, roundInd k j (z i) := by
  unfold Ncount roundInd
  rw [Finset.card_filter]
  push_cast
  rfl

/-- Triangle inequality applied to (1). -/
theorem abs_Ssum_sub_Ncount_le {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) (j : Fin k) :
    |Ssum z j - Ncount z j| ≤
      (Cconst k : ℝ) * ∑ i, z i * |Polynomial.aeval (z i) (Qpoly k)| := by
  rw [Ncount_eq_sum_roundInd]
  unfold Ssum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_assoc]
  exact abs_ell_sub_roundInd_le k j (hz i)

/-- Cauchy–Schwarz: `(∑ z_i |Q(z_i)|)² ≤ U E`. -/
theorem sq_sum_le_Usum_mul_Esum {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∑ i, z i * |Polynomial.aeval (z i) (Qpoly k)|) ^ 2 ≤ Usum z * Esum k z := by
  unfold Usum Esum
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => hz i)
    (fun i _ => mul_nonneg (hz i) (sq_nonneg _)) (fun i _ => le_of_eq ?_)
  rw [mul_pow, sq_abs]
  ring

/-- **Lemma 2.3, first inequality in (3):** `‖S - N‖₂² ≤ k C² U E`. -/
theorem lemma_2_3_dist {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∑ j : Fin k, (Ssum z j - Ncount z j) ^ 2 ≤
      (k : ℝ) * (Cconst k : ℝ) ^ 2 * Usum z * Esum k z := by
  have hterm : ∀ j : Fin k,
      (Ssum z j - Ncount z j) ^ 2 ≤ (Cconst k : ℝ) ^ 2 * (Usum z * Esum k z) := by
    intro j
    have h1 := abs_Ssum_sub_Ncount_le hz j
    have h2 := sq_sum_le_Usum_mul_Esum (k := k) hz
    have hC : (0 : ℝ) ≤ Cconst k := Nat.cast_nonneg _
    have hsum : (0 : ℝ) ≤ ∑ i, z i * |Polynomial.aeval (z i) (Qpoly k)| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (abs_nonneg _)
    calc (Ssum z j - Ncount z j) ^ 2
        = |Ssum z j - Ncount z j| ^ 2 := (sq_abs _).symm
      _ ≤ ((Cconst k : ℝ) * ∑ i, z i * |Polynomial.aeval (z i) (Qpoly k)|) ^ 2 := by
          gcongr
      _ = (Cconst k : ℝ) ^ 2 * (∑ i, z i * |Polynomial.aeval (z i) (Qpoly k)|) ^ 2 := by
          ring
      _ ≤ (Cconst k : ℝ) ^ 2 * (Usum z * Esum k z) := by gcongr
  calc ∑ j : Fin k, (Ssum z j - Ncount z j) ^ 2
      ≤ ∑ _j : Fin k, (Cconst k : ℝ) ^ 2 * (Usum z * Esum k z) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (k : ℝ) * (Cconst k : ℝ) ^ 2 * Usum z * Esum k z := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- At most one `ρ_j(t)` is nonzero. -/
theorem sum_roundInd_le (t : ℝ) : ∑ j : Fin k, roundInd k j t ≤ 1 := by
  unfold roundInd
  rw [Finset.sum_boole]
  norm_cast
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact label_injective k (by exact_mod_cast ha.symm.trans hb)

/-- `∑_j N_j ≤ 4 U`: every coordinate rounded to a data label is at least `1/4`. -/
theorem sum_Ncount_le {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∑ j : Fin k, (Ncount z j : ℝ) ≤ 4 * Usum z := by
  simp only [Ncount_eq_sum_roundInd]
  rw [Finset.sum_comm]
  unfold Usum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h0 : nearest k (z i) = 0
  · have : ∑ j : Fin k, roundInd k j (z i) = 0 := Finset.sum_eq_zero fun j _ => by
      unfold roundInd
      split_ifs with hc
      · exfalso
        rw [h0] at hc
        exact (label_pos k j).ne (by exact_mod_cast hc)
      · rfl
    rw [this]
    linarith [hz i]
  · have h14 := quarter_le_of_nearest_ne_zero k (hz i) h0
    have := sum_roundInd_le (k := k) (z i)
    linarith

/-- **Lemma 2.3, second inequality in (3):** `‖N‖₂² ≤ 16 U²`. -/
theorem lemma_2_3_norm {n : ℕ} {z : Fin n → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∑ j : Fin k, (Ncount z j : ℝ) ^ 2 ≤ 16 * Usum z ^ 2 := by
  have h1 : ∑ j : Fin k, (Ncount z j : ℝ) ^ 2 ≤ (∑ j : Fin k, (Ncount z j : ℝ)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => Nat.cast_nonneg _
  have h2 := sum_Ncount_le (k := k) hz
  have h3 : (0 : ℝ) ≤ ∑ j : Fin k, (Ncount z j : ℝ) :=
    Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  calc ∑ j : Fin k, (Ncount z j : ℝ) ^ 2
      ≤ (∑ j : Fin k, (Ncount z j : ℝ)) ^ 2 := h1
    _ ≤ (4 * Usum z) ^ 2 := by gcongr
    _ = 16 * Usum z ^ 2 := by ring

end AnyDim.Undecidability

end
