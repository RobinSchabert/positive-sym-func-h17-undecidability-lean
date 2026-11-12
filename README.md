# Lean 4 formalization: Hilbert's 17th problem for symmetric functions

This repository contains a Lean 4 / Mathlib formalization of the two main results of

> Sebastian Debus, Robin Schabert,
> *Hilbert's 17th problem for symmetric functions: undecidability and a counterexample*,
> preprint, 2026.

A symmetric function `f ∈ Λ = ℝ[p₁, p₂, …]` is *any-dimensional psd* if every truncation
`f⁽ⁿ⁾ ∈ ℝ[X₁, …, Xₙ]` is nonnegative on `ℝⁿ`, and *any-dimensional sos* if every truncation is a
sum of squares. The paper proves, and this repository formalizes:

1. **Undecidability (Section 2).** An explicit map `P ↦ H_P` from integer polynomials to
   homogeneous even symmetric functions with rational coefficients such that `H_P` is
   any-dimensional psd if and only if `P` has no zero in `ℕ₀ᵏ` (Proposition 2.6, Theorem 2.2).
2. **A counterexample to Hilbert's 17th problem for symmetric functions (Section 3).** The octic

   `F = 4p₁²(p₃ − 4p₁³)² + 9p₂(p₆ − 8p₁²p₄ + 16p₁⁴p₂) − 16p₁⁸`

   is positive definite in every number of variables, but there is no nonzero formal power
   series `Q` of bounded degree such that `Q⁽ⁿ⁾` and `Q⁽ⁿ⁾F⁽ⁿ⁾` are sums of squares for all `n`
   (Theorem 3.1). In particular `F` is not a sum of squares in the quotient field of `Λ`
   (Corollary 3.6).

## Where to start

Read [`AnyDim/Paper.lean`](AnyDim/Paper.lean). It follows the paper statement by statement:
every formalized result is restated there under its number in the paper, with a docstring that
records each deviation from the paper's wording, and the file ends with the list of what is not
formalized. The two main theorems read as follows.

```lean
/-- Theorem 2.2 (the reduction). -/
theorem theorem_2_2 (P : MvPolynomial (Fin k) ℤ) :
    (∀ n : ℕ, 0 < n → ∀ x : Fin n → ℚ,
      0 ≤ MvPolynomial.aeval (fun r : ℕ+ => ∑ i, x i ^ (r : ℕ)) (HP P)) ↔ ¬ HasNatZero P

/-- Theorem 3.1. -/
theorem theorem_3_1 :
    WHomogeneous F 8 ∧
    (∀ n : ℕ, 0 < n → ∀ x : Fin n → ℝ, x ≠ 0 → 0 < MvPolynomial.eval x (trunc n F)) ∧
    ¬ ∃ (Q : FSeries) (D : ℕ), Q ≠ 0 ∧ ∀ n : ℕ, 0 < n →
      ∃ a : Poly n, IsTrunc Q n a ∧ a.totalDegree ≤ D ∧ IsSOS a ∧ IsSOS (a * trunc n F)
```

## Status

The project builds with Lean `v4.35.0-rc3` and the Mathlib commit pinned in `lakefile.lean` and
`lake-manifest.json`.

There is **exactly one `sorry`**: Blekherman's theorem on symmetric sums of squares on the
hypercube (Theorem 3.2 of the paper, `AnyDim.theorem_3_2` in
[`AnyDim/Counterexample/Blekherman.lean`](AnyDim/Counterexample/Blekherman.lean)). The paper
quotes this theorem from the literature, and it is used here as a black box in the same way.
There are no custom axioms and no uses of `native_decide`.

| depends on Theorem 3.2 (`sorryAx`) | fully proved (`propext`, `Classical.choice`, `Quot.sound` only) |
|---|---|
| Corollary 3.3 | Lemma 2.3, Lemma 2.5, Proposition 2.6, Theorem 2.2 |
| Corollary 3.4 | Theorem 3.1, Corollary 3.6, Proposition 3.9 |

**Theorem 3.1 does not depend on the unproved Theorem 3.2.** Its proof only needs *some* lower
bound for the degree of sos multipliers of `F⁽ⁿ⁾` that grows with `n`. The directory
[`AnyDim/Counterexample/Elementary/`](AnyDim/Counterexample/Elementary) contains a self-contained
proof of a weaker version of Corollary 3.3 (an explicit pseudo-expectation on the hypercube,
valid for `deg Q ≤ n/2 − 2` instead of `deg Q ≤ n`). It gives

* `corollary_3_4_elementary`: `deg Q > (n − 20)/3`, fully proved, instead of
* `corollary_3_4`: `deg Q > (n − 8)/2`, the paper's bound, which uses Theorem 3.2.

Both bounds come from the same formalized argument (`no_multiplier_of_cubeNonneg`), which is the
proof of Corollary 3.4 in the paper, parametrized by the conclusion of Corollary 3.3.

## Building and checking

```
lake exe cache get
lake build
```

`lake build` reports a single warning ("declaration uses `sorry`"), for `AnyDim.theorem_3_2`.

The axioms of all results in `AnyDim/Paper.lean` are recorded at the end of that file with
`#guard_msgs`, so the build fails if any of them acquires a new axiom or a `sorry`. To print the
axioms, run

```
lake env lean Audit.lean
```

The following two commands confirm that there is one `sorry` and no `axiom` or `native_decide`:

```
grep -rnE '^\s*sorry' AnyDim                  # one hit, in AnyDim/Counterexample/Blekherman.lean
grep -rnE '^\s*axiom |native_decide' AnyDim   # no hits
```

## What is not formalized

* **Decidability.** The notions "decision problem" and "undecidable" are not formalized, and
  neither are the theorem of Davis, Putnam, Robinson and Matiyasevich and the theorem of Jones
  (Remark 2.1). Theorem 2.2 is formalized as the many-one reduction `P ↦ H_P`: the truncations of
  `H_P` are nonnegative on `ℚⁿ` for all `n` if and only if `P` has no zero in `ℕ₀ᵏ`. That
  `P ↦ H_P` is computable is not a formal statement; it is visible from the definition, which
  uses only explicit finite rational arithmetic (`Cconst`, `Kconst`, `dBound`, `Lconst`, `QP`,
  `homogenize`).
* **The proof of Theorem 3.2** (Blekherman), see above.
* **Section 4** (trace polynomials and entanglement criteria), Remark 3.8, the remarks on the
  Vandermonde cell, and the discussion of the real spectrum in Remark 3.5.

## Layout

```
AnyDim/Paper.lean                          the paper, statement by statement (start here)
AnyDim/Basic.lean                          Λ, truncation, any-dimensional psd/sos, degrees
AnyDim/Undecidability/Basic.lean           rational symmetric functions, bridge to Λ
AnyDim/Undecidability/Rounding.lean        Section 2.2, Lemma 2.3
AnyDim/Undecidability/Encoding.lean        Section 2.3, Lemma 2.5
AnyDim/Undecidability/Homogenization.lean  Remark 2.4, (7), (8), (10), (11)
AnyDim/Undecidability/Main.lean            Proposition 2.6, Theorem 2.2
AnyDim/Counterexample/Octic.lean           F, Theorem 3.1 (1)
AnyDim/Counterexample/Blekherman.lean      Theorem 3.2 (sorry), Corollary 3.3
AnyDim/Counterexample/Specialization.lean  the substitutions in the proof of Corollary 3.4
AnyDim/Counterexample/Geometry.lean        algebraic independence, open-set argument
AnyDim/Counterexample/Symmetric.lean       Reynolds operator, power-sum form of the FTSP
AnyDim/Counterexample/MultiplierDegree.lean  Corollary 3.4
AnyDim/Counterexample/FormalSeries.lean    formal power series of bounded degree
AnyDim/Counterexample/ClosedCone.lean      closedness of the sos cone
AnyDim/Counterexample/Proposition39.lean   Proposition 3.9
AnyDim/Counterexample/Elementary/          elementary replacement for Corollaries 3.3, 3.4
AnyDim/Counterexample/Main.lean            Theorem 3.1, Corollary 3.6, Remarks 3.5, 3.7
Audit.lean                                 prints the axioms of the main results
```

## The paper and the Lean names

The column "statement" gives the name in `AnyDim/Paper.lean` (namespace `AnyDim.Paper`); the
column "development" gives the declarations it refers to (namespace `AnyDim`, for Section 2
`AnyDim.Undecidability`).

### Section 1: notation

| paper | Lean |
|---|---|
| `Λ = ℝ[p₁, p₂, …]`, `Λ_ℚ` | `Λ := MvPolynomial ℕ+ ℝ`, `Λℚ`, inclusion `toΛ` |
| truncation `f ↦ f⁽ⁿ⁾` | `trunc n : Λ →ₐ[ℝ] Poly n`, value `evalTrunc f x` |
| any-dimensional psd / sos, `SP`, `SΣ` | `AnyDimPSD`, `AnyDimSOS` (`AnyDimPD` for positive definite) |
| homogeneous of degree `d`, `deg f ≤ d` | `WHomogeneous f d`, `WDegLE f d` (grading `deg p_r = r`) |
| `ℝ[[X₁, X₂, …]]`, `g⁽ⁿ⁾` | `FSeries`, `restrict n`; `IsTrunc g n a` says "the polynomial `a` is `g⁽ⁿ⁾`" |
| bounded degree | `∃ D, ∀ n, ∃ a, IsTrunc g n a ∧ a.totalDegree ≤ D` (`definition_boundedDegree`) |
| `Λ ⊆ ℝ[[X₁, X₂, …]]` | `toSeries` (`symmetric_function_as_series`) |

### Section 2: undecidability

| paper | statement | development | file |
|---|---|---|---|
| `A`, `m`, `a_j`, `Q`, `R`, `ℓ_j`, `ρ`, `ρ_j` | `lagrange_polynomials` | `labels`, `mconst`, `label`, `Qpoly`, `Rpoly`, `ell`, `nearest`, `roundInd` | `Rounding.lean` |
| Lemma 2.3 with (1), (2), (3), (4) | `lemma_2_3` | `Cconst`, `Ssum`, `Ncount`, `Usum`, `Esum`; `abs_ell_sub_roundInd_le`, `lemma_2_3_dist`, `lemma_2_3_norm` | `Rounding.lean` |
| Remark 2.4, (7) | `remark_2_4` | `powerSumPoly`, `Spoly`, `Upoly`, `Epoly` | `Homogenization.lean` |
| `b_j`, `K_P`, `Q_P` (6), (8) | `definition_QP` | `bcoef`, `Kconst`, `QP`, `Lconst`, `QP_wdeg`, `QP_mem_supported` | `Encoding.lean`, `Homogenization.lean` |
| Lemma 2.5, claim (9) | `lemma_2_5` | `lemma_2_5_a`, `lemma_2_5_b`, `lemma_2_5_claim`, `witness` | `Encoding.lean` |
| normalization (10) | `normalization_10` | `normalize`, `tuplePower_normalize` | `Homogenization.lean` |
| `H_P` (11) | `definition_11` | `HP`, `homogenize`, `HP_eq_fraction` | `Homogenization.lean`, `Main.lean` |
| Proposition 2.6 | `proposition_2_6` | `HP_mem_supported`, `HP_wHomogeneous`, `proposition_2_6_a`, `proposition_2_6_b`, `HP_anyDimPSD_iff` | `Main.lean` |
| Theorem 2.2 | `theorem_2_2`, `theorem_2_2_real`, `theorem_2_2_nine` | `NonnegOnRat`, `nonnegOnRat_iff` | `Main.lean` |

### Section 3: counterexample

| paper | statement | development | file |
|---|---|---|---|
| `F` | `definition_F` | `F`, `Fexpr`, `F_wHomogeneous` | `Octic.lean` |
| Theorem 3.1 | `theorem_3_1`, `theorem_3_1_in_particular` | `theorem_3_1_1`, `theorem_3_1_2`, `no_anyDimSOS_multiplier` | `Octic.lean`, `Main.lean` |
| `σ`, (12) | `inequality_12` | `sigma`, `abs_cube_sub_sigma_le` | `Octic.lean` |
| `k`, `D`, (13) | `inequality_13` | `kInt`, `Dval`, `sq_p3_sub_kInt_le` | `Octic.lean` |
| `F ≥ 16p₁⁸` | `theorem_3_1_1_addendum` | `sixteen_mul_le_evalTrunc_F` | `Octic.lean` |
| Theorem 3.2 (Blekherman) | `theorem_3_2` | `AnyDim.theorem_3_2` (**`sorry`**) | `Blekherman.lean` |
| Corollary 3.3 | `corollary_3_3` | `AnyDim.corollary_3_3` | `Blekherman.lean` |
| `c_k(T)`, `q(T, z)`, `f(T, z)` | | `univariateTail`, `psi`, `evalAt_withTail_cube`, `psi_F_at_zero` | `Specialization.lean` |
| algebraic independence of the `c_k(1/2) + p_k` | | `powerSubst_injective`, `psi_ne_zero` | `Geometry.lean` |
| Reynolds operator, fundamental theorem of symmetric polynomials | | `symmetrize`, `exists_trunc_eq_of_totalDegree_le` | `Symmetric.lean` |
| Corollary 3.4 | `corollary_3_4` | `no_multiplier_of_cubeNonneg`, `AnyDim.corollary_3_4` | `MultiplierDegree.lean` |
| Remark 3.5 | `remark_3_5` | `phi` | `Main.lean` |
| Corollary 3.6 | `corollary_3_6` | `F_not_sos_in_fractionRing`, `F_no_krivine_stengle` | `Main.lean` |
| Remark 3.7 | `remark_3_7` | `balancedPoint`, `remark_3_7_sphere` | `Main.lean` |
| closedness of the sos cone | | `isSOS_of_tendsto`, `isClosed_sos_cone` | `ClosedCone.lean` |
| Proposition 3.9 | `proposition_3_9` | `exists_multiplier_of_bounded_degree` | `Proposition39.lean` |
| (not in the paper) | `corollary_3_3_elementary`, `corollary_3_4_elementary` | `AnyDim.Elementary.*` | `Elementary/CubeBound.lean` |

## Conventions and small differences to the paper

* **Indices.** The paper's variables `X₁, X₂, …` are `X₀, X₁, …` in Lean (`Fin n`, `ℕ`); the
  paper's `Y₁, …, Y_k` and `a_j = j + 1` (`1 ≤ j ≤ k`) are indexed by `j : Fin k` with
  `label k j = j + 2`. The power sums are indexed by `ℕ+`, so there is no `p₀`.
* **`n ∈ ℕ = {1, 2, …}`.** `AnyDimSOS` quantifies over `n ≥ 1`. `AnyDimPSD` and `AnyDimPD`
  quantify over all `n ≥ 0`; this is equivalent (`anyDimPSD_iff`, `anyDimPD_iff`). The statements
  in `AnyDim/Paper.lean` use `n ≥ 1` throughout.
* **Degrees.** "Degree" of a symmetric function refers to the grading `deg p_r = r`
  (`WDegLE`, `WHomogeneous`), not to `MvPolynomial.totalDegree` in the variables `p_r`.
* **`H_P`** is defined without denominators (`homogenize`); `definition_11` proves that this is
  formula (11) in the quotient field of `Λ_ℚ`.
* **Lemma 2.5** is proved for every `d ≥ 1` with `deg P ≤ d`; the paper uses
  `d = max{1, deg P}` (`dBound`).
* **Theorem 3.2** is stated for the function `x ↦ ∑ⱼ gⱼ(x)²` on `{0,1}ⁿ` with
  `deg gⱼ ≤ d ≤ n/2`, assumed to be of the form `q(∑ xᵢ)` with `deg q ≤ n`. This makes it
  symmetric and nonnegative and determines `q`.
* **Proposition 3.9.** The hypothesis `f ∈ SP` is kept in the statement but is not needed in the
  proof. The second part of **Corollary 3.6** is proved without assuming `q ≠ 0`.

## AI declaration

This formalization was produced with significant input from large language models. The proofs
are checked by Lean. The statements in `AnyDim/Paper.lean` are the part that has to be compared
with the paper by a human reader.

## Citing

```bibtex
@unpublished{DebusSchabert2026,
  author = {Debus, Sebastian and Schabert, Robin},
  title  = {Hilbert's 17th problem for symmetric functions: undecidability and a counterexample},
  year   = {2026},
  note   = {Preprint}
}
```

## License

Apache License 2.0, see [`LICENSE`](LICENSE). This is the license of Mathlib.
