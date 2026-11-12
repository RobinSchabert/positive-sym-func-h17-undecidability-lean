module

public import AnyDim.Basic
public import AnyDim.Undecidability.Main
public import AnyDim.Counterexample.Main
public import AnyDim.Paper

/-!
# Hilbert's 17th problem for symmetric functions: undecidability and a counterexample

Lean 4 formalization of the two main results of

  S. Debus, R. Schabert, *Hilbert's 17th problem for symmetric functions: undecidability and a
  counterexample* (preprint, 2026).

* `AnyDim.Paper`: the paper, statement by statement.  Start reading there.
* `AnyDim.Basic`: the ring `Λ = ℝ[p_1, p_2, …]`, truncations, any-dimensional psd / sos.
* `AnyDim.Undecidability.*`: Section 2 (Lemma 2.3, Lemma 2.5, Proposition 2.6, Theorem 2.2).
* `AnyDim.Counterexample.*`: Section 3 (Theorem 3.1, Theorem 3.2 [stated, not proved],
  Corollaries 3.3, 3.4, 3.6, Proposition 3.9, Remarks 3.5 and 3.7).

See `README.md` for a map from the paper to the Lean declarations.
-/
