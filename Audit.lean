import AnyDim

/-!
# Axiom audit

Prints the axioms used by the results restated in `AnyDim/Paper.lean`.  Run with

  lake env lean Audit.lean

after `lake build`.  The same information is checked at build time by the `#guard_msgs` commands
at the end of `AnyDim/Paper.lean`.

Expected output: every result in the first block depends only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound`; the three results in the second block also depend on `sorryAx`,
because they use Blekherman's theorem (Theorem 3.2 of the paper), which is stated without proof.
-/

open AnyDim.Paper

-- ## Block 1: complete proofs

-- Section 2: undecidability
#print axioms lemma_2_3
#print axioms remark_2_4
#print axioms definition_QP
#print axioms lemma_2_5
#print axioms definition_11
#print axioms proposition_2_6
#print axioms theorem_2_2
#print axioms theorem_2_2_real
#print axioms theorem_2_2_nine

-- Section 3: the counterexample
#print axioms theorem_3_1
#print axioms theorem_3_1_in_particular
#print axioms inequality_12
#print axioms inequality_13
#print axioms remark_3_5
#print axioms corollary_3_6
#print axioms remark_3_7
#print axioms proposition_3_9
#print axioms corollary_3_3_elementary
#print axioms corollary_3_4_elementary

-- ## Block 2: results that depend on Blekherman's theorem (`sorryAx`)

#print axioms theorem_3_2
#print axioms corollary_3_3
#print axioms corollary_3_4
