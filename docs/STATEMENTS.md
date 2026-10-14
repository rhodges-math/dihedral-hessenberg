# Statements of the paper and their Lean counterparts

Each statement of *Dot actions and Hessenberg spaces for dihedral groups* (Jonathan
Boretsky, Reuven Hodges, Nathan Lesnevich, Tyrrell McAllister, and Joseph Pappe, 2026),
[arXiv:2610.16001](https://arxiv.org/abs/2610.16001),
with its status and the Lean declarations that formalize it, in the order of the paper.
The index covers every theorem, proposition, lemma, corollary, definition, displayed
equation, example and remark of the paper, and the mathematical statements made in its
prose and figures. Numbers are those printed in the paper (arXiv:2610.16001v1), and labels
are its LaTeX labels; a statement without a number is given with its section. A short note follows a
statement whose Lean statement or proof differs from the paper. Names are shown without
the prefix `Schubert.`; paths are relative to the repository root.

| Statement | Label | Status |
| --- | --- | --- |
| Theorem 1 | `intthm:poincare_hilbert` | formalized |
| Theorem 2 | `intthm:basis` | formalized |
| Theorem 3 | `intthm:dotaction` | formalized |
| Example 2.1 | — | formalized |
| Lemma 2.2 | `lem:reflect_divisible` | formalized |
| The dihedral group, its reduced words and its root system (Section 2.2) | — | formalized |
| Example 2.3 | `ex:reflection` | formalized |
| Equation (1) | `eq:left_inversion_set` | formalized |
| Equation (2) | `eq:right_inversion_set` | formalized |
| Lemma 2.4 | `lem:rank_two_bruhat_facts` | formalized |
| The irreducible representations of $I\_2(n)$ and the coset representations $C\_\gamma$ (Section 2.3) | — | formalized |
| Equation (3) | `eq:reflection_coset_decomposition` | formalized |
| Example 2.5 | — | formalized |
| Definition 2.6 | `def:root_poset` | formalized |
| The Hasse diagrams of the root poset (Section 2.4) | — | formalized |
| Remark 2.7 | — | formalized |
| The list of Hessenberg spaces (Section 2.4) | — | formalized |
| Remark 2.8 | — | formalized |
| Remark 2.9 | — | formalized |
| Definition 2.10 | `def:inversion_set` | formalized |
| The labeled Cayley graph (Section 2.4) | — | formalized |
| Example 2.11 | `ex:cayley` | formalized |
| The acyclic orientation of the Cayley graph and the order $\prec\_H$ (Section 2.4) | — | formalized |
| Example 2.12 | — | formalized |
| Example 2.13 | — | formalized |
| The module of splines (Section 2.5) | — | formalized |
| The spline diagrams for $I\_2(3)$ (Section 2.5) | — | formalized |
| The spline diagrams for $I\_2(4)$ (Section 2.5) | — | formalized |
| Edge labels and conjugate reflections (Section 2.5) | — | formalized |
| Lemma 2.14 | — | formalized |
| Lemma 2.15 | — | formalized |
| Constant and orbit splines and the two module structures (Section 2.5) | — | formalized |
| Equation (4) | `eqn:left_action` | formalized |
| Equation (5) | `eqn:right_action` | formalized |
| Lemma 2.16 | — | formalized |
| Definition 2.17 | `def:upper_triangular` | formalized |
| Remark 2.18 | — | formalized |
| Lemma 2.19 | `lem:upper_triangular` | formalized |
| Definition 2.20 | `def:flowup` | formalized |
| Definition 2.21 | — | formalized |
| Lemma 2.22 | `lem:dot_action_preserves_splines` | formalized |
| Equation (6) | `eqndef:left_quotient` | formalized |
| Equation (7) | `eqndef:right_quotient` | formalized |
| Lemma 3.1 | `lem:left_edges_full_graph` | formalized |
| Equation (8) | `eq:left_spline_condition_full` | formalized |
| Lemma 3.2 | `lem:divided_difference_spline` | formalized |
| Equation (9) | `eq:divided_difference_spline` | formalized |
| Equation (10) | `eq:top_schubert_spline` | formalized |
| Equation (11) | `eq:schubert_recursion` | formalized |
| Proposition 3.3 | `prop:schubert_flowup` | formalized |
| Equation (12) | `eq:schubert_diagonal_value` | formalized |
| Theorem 3.4 | `thm:schubert_rational` | formalized |
| Linear forms of distinct positive roots are not proportional (Section 3) | — | formalized |
| Proposition 3.5 | `prop:schubert_basis` | formalized |
| Corollary 3.6 | `cor:schubert_hilbert_series` | formalized |
| Lemma 3.7 | `lem:borel_presentation_schubert_splines` | formalized |
| Equation (13) | `eq:borel_presentation_schubert_splines` | formalized |
| The tensor decomposition over the fixed field (Section 3) | — | formalized |
| The invariants of $I\_2(n)$ and freeness over them (Section 3) | — | formalized |
| Proposition 3.8 | `prop:left_schubert_rep` | formalized |
| Proposition 3.9 | `prop:right_schubert_rep` | formalized |
| Remark 3.10 | — | formalized |
| Remark 3.11 | — | formalized |
| Lemma 4.1 | `lem:generalized_divided_difference` | formalized |
| Equation (14) | `eq:divided_difference` | formalized |
| Lemma 4.2 | `lem:leftright_length` | formalized |
| Lemma 4.3 | `lem:simple_degree_changes` | formalized |
| Corollary 4.4 | `cor:existence_upper_elts` | formalized |
| Equation (15) | `eq:top_spline` | formalized |
| Theorem 4.5 | `thm:flowup` | formalized |
| Example 4.6 | `ex:generators_exist` | formalized |
| Corollary 4.7 | `cor:rank_gf` | formalized |
| Lemma 5.1 | `lem:regular` | formalized |
| Corollary 5.2 | `cor:rationally_smooth` | formalized |
| Proposition 5.3 | `prop:flowup_explicit_setup` | formalized |
| Proposition 5.4 | `prop:linear_independence` | formalized |
| Corollary 5.5 | `cor:admissible_block_independence` | formalized |
| Equation (16) | `eq:Ph_representation` | formalized |
| Remark 6.1 | — | formalized |
| Definition 6.2 | `def:H_dominant` | formalized |
| Remark 6.3 | — | formalized |
| Theorem 6.4 | `thm:left_representation` | formalized |
| Equation (17) | `eq:left_hessenberg_representation` | formalized |
| Remark 6.5 | — | formalized |
| Example 6.6 | — | formalized |
| Example 6.7 | — | formalized |
| Example 6.8 | — | formalized |
| Graded equivariant freeness (Section 6) | — | formalized |
| Equation (18) | `eq:left_equivariant_freeness` | formalized |
| Proposition 6.9 | `prop:left_quotient_duality` | formalized |
| Equation (19) | `eq:left_representation_duality` | formalized |
| The representations of $I\_2(n)$ are self-dual (Section 6) | — | formalized |
| Lemma 6.10 | `lem:trivial_left_subreps` | formalized |
| Equation (20) | `eq:left_middle_subtraction` | formalized |
| The decomposition of the polynomials of low degree (Section 6) | — | formalized |
| Corollary 6.11 | `cor:not_permutation` | formalized |
| Equation (21) | `eq:right_equivariant_freeness` | formalized |
| Proposition 7.1 | `prop:right_quotient_duality` | formalized |
| Equation (22) | `eq:right_representation_duality` | formalized |
| Lemma 7.2 | `lem:coinv_right_subreps` | formalized |
| Equation (23) | `eq:h_coinvariant` | formalized |
| Theorem 7.3 | `thm:right_representation` | formalized |
| Equation (24) | `eq:right_hessenberg_representation` | formalized |

## Statements

### Theorem 1 (`intthm:poincare_hilbert`)

Status: **formalized**

Here the rank generating function is defined as $\sum\_d\dim\_{\mathbb{C}}(\mathcal{M}\_H/(x,y)\mathcal{M}\_H)\_d\\,q^d$.

- `DihedralSplines.HessenbergIdeal.poincare_hilbert` ([DihedralHessenberg/Paper/FlowupHilbert.lean](../DihedralHessenberg/Paper/FlowupHilbert.lean))
- `DihedralSplines.HessenbergIdeal.hilbertSeries_coeff` ([DihedralHessenberg/Paper/FlowupHilbert.lean](../DihedralHessenberg/Paper/FlowupHilbert.lean))
- `DihedralSplines.HessenbergIdeal.hilbertSeries_rank` ([DihedralHessenberg/Paper/FlowupHilbert.lean](../DihedralHessenberg/Paper/FlowupHilbert.lean))
- `DihedralSplines.FlowupSpline.Left.basis_apply` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.basis_apply` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))

### Theorem 2 (`intthm:basis`)

Status: **formalized**

- `DihedralSplines.FlowupSpline.basis_explicit` ([DihedralHessenberg/Paper/FlowupExplicitBasis.lean](../DihedralHessenberg/Paper/FlowupExplicitBasis.lean))
- `DihedralSplines.FlowupSpline.shape` ([DihedralHessenberg/Paper/FlowupBoundary.lean](../DihedralHessenberg/Paper/FlowupBoundary.lean))
- `DihedralSplines.BoundaryForm.formula` ([DihedralHessenberg/Paper/BoundaryForm.lean](../DihedralHessenberg/Paper/BoundaryForm.lean))
- `DihedralSplines.BoundaryForm.coefficient_ne` ([DihedralHessenberg/Paper/BoundaryForm.lean](../DihedralHessenberg/Paper/BoundaryForm.lean))

### Theorem 3 (`intthm:dotaction`)

Status: **formalized**

Here a graded representation is recorded as the series $\sum\_d\[V\_d\]\\,q^d$ over the representation ring of $I\_2(n)$.

- `DihedralSplines.HessenbergIdeal.Left.graded_class` ([DihedralHessenberg/Paper/QuotientClass.lean](../DihedralHessenberg/Paper/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_even` ([DihedralHessenberg/Paper/LeftEvenClass.lean](../DihedralHessenberg/Paper/LeftEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_odd` ([DihedralHessenberg/Paper/LeftOddClass.lean](../DihedralHessenberg/Paper/LeftOddClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.class_palindromic` ([DihedralHessenberg/Paper/LeftClassPalindrome.lean](../DihedralHessenberg/Paper/LeftClassPalindrome.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class` ([DihedralHessenberg/Paper/QuotientClass.lean](../DihedralHessenberg/Paper/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_even` ([DihedralHessenberg/Paper/RightEvenClass.lean](../DihedralHessenberg/Paper/RightEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_odd` ([DihedralHessenberg/Paper/RightOddClass.lean](../DihedralHessenberg/Paper/RightOddClass.lean))

### Example 2.1

Status: **formalized**

- `Dihedral.triangular_basis_images` ([DihedralHessenberg/Dihedral/TriangularSubstitution.lean](../DihedralHessenberg/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_first_variable` ([DihedralHessenberg/Dihedral/TriangularSubstitution.lean](../DihedralHessenberg/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_second_variable` ([DihedralHessenberg/Dihedral/TriangularSubstitution.lean](../DihedralHessenberg/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_monomial` ([DihedralHessenberg/Dihedral/TriangularSubstitution.lean](../DihedralHessenberg/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_sum` ([DihedralHessenberg/Dihedral/TriangularSubstitution.lean](../DihedralHessenberg/Dihedral/TriangularSubstitution.lean))

### Lemma 2.2 (`lem:reflect_divisible`)

Status: **formalized**

The proof uses $f\equiv s\_\alpha(f)$ modulo $t\_\alpha$ instead of the Nullstellensatz.

- `DihedralSplines.reflection_difference` ([DihedralHessenberg/Paper/ReflectionLemma.lean](../DihedralHessenberg/Paper/ReflectionLemma.lean))

### The dihedral group, its reduced words and its root system (Section 2.2)

Status: **formalized**

Here $I\_2(n)$ is Mathlib's `DihedralGroup n`, with $s\_1$ and $s\_2$ the reflections `sr 0` and `sr 1`.

- `Dihedral.presentationEquiv_firstSimpleReflection` ([DihedralHessenberg/Dihedral/CoxeterSystem.lean](../DihedralHessenberg/Dihedral/CoxeterSystem.lean))
- `Dihedral.presentationEquiv_secondSimpleReflection` ([DihedralHessenberg/Dihedral/CoxeterSystem.lean](../DihedralHessenberg/Dihedral/CoxeterSystem.lean))
- `Dihedral.reduced_word_alternating` ([DihedralHessenberg/Dihedral/ReducedUnique.lean](../DihedralHessenberg/Dihedral/ReducedUnique.lean))
- `Dihedral.unique_reduced_of_ne_longest` ([DihedralHessenberg/Dihedral/ReducedUnique.lean](../DihedralHessenberg/Dihedral/ReducedUnique.lean))
- `Dihedral.longest_reduced_words` ([DihedralHessenberg/Dihedral/ReducedUnique.lean](../DihedralHessenberg/Dihedral/ReducedUnique.lean))
- `Dihedral.vectorOperator_injective` ([DihedralHessenberg/Dihedral/FaithfulRealization.lean](../DihedralHessenberg/Dihedral/FaithfulRealization.lean))
- `Dihedral.PositiveRoot.realAction_reflection` ([DihedralHessenberg/Dihedral/FaithfulRealization.lean](../DihedralHessenberg/Dihedral/FaithfulRealization.lean))
- `Dihedral.positiveReflectionEquiv` ([DihedralHessenberg/Dihedral/RootReflectionVectors.lean](../DihedralHessenberg/Dihedral/RootReflectionVectors.lean))
- `Dihedral.numbered_even_reflection` ([DihedralHessenberg/Dihedral/RootNumbering.lean](../DihedralHessenberg/Dihedral/RootNumbering.lean))
- `Dihedral.numbered_odd_reflection` ([DihedralHessenberg/Dihedral/RootNumbering.lean](../DihedralHessenberg/Dihedral/RootNumbering.lean))
- `Dihedral.roots_neg_iff` ([DihedralHessenberg/Dihedral/RootAxioms.lean](../DihedralHessenberg/Dihedral/RootAxioms.lean))
- `Dihedral.roots_unit` ([DihedralHessenberg/Dihedral/RootAxioms.lean](../DihedralHessenberg/Dihedral/RootAxioms.lean))
- `Dihedral.roots_proportional` ([DihedralHessenberg/Dihedral/RootAxioms.lean](../DihedralHessenberg/Dihedral/RootAxioms.lean))
- `Dihedral.roots_reflection_mem` ([DihedralHessenberg/Dihedral/RootAxioms.lean](../DihedralHessenberg/Dihedral/RootAxioms.lean))
- `Dihedral.Separator.partition` ([DihedralHessenberg/Dihedral/RootSeparator.lean](../DihedralHessenberg/Dihedral/RootSeparator.lean))
- `Dihedral.Separator.reflectionEquiv` ([DihedralHessenberg/Dihedral/RootSeparator.lean](../DihedralHessenberg/Dihedral/RootSeparator.lean))
- `Dihedral.Separator.exists_chamber` ([DihedralHessenberg/Dihedral/RootChambers.lean](../DihedralHessenberg/Dihedral/RootChambers.lean))
- `Dihedral.Separator.unique_nearest_pair` ([DihedralHessenberg/Dihedral/HyperplaneDistance.lean](../DihedralHessenberg/Dihedral/HyperplaneDistance.lean))
- `Dihedral.Separator.foot_pairing` ([DihedralHessenberg/Dihedral/HyperplaneDistance.lean](../DihedralHessenberg/Dihedral/HyperplaneDistance.lean))
- `Dihedral.Separator.distance_min` ([DihedralHessenberg/Dihedral/HyperplaneDistance.lean](../DihedralHessenberg/Dihedral/HyperplaneDistance.lean))
- `Dihedral.Separator.Frame.nearest_pair` ([DihedralHessenberg/Dihedral/RootFrame.lean](../DihedralHessenberg/Dihedral/RootFrame.lean))
- `Dihedral.Separator.Frame.generate` ([DihedralHessenberg/Dihedral/RootFrame.lean](../DihedralHessenberg/Dihedral/RootFrame.lean))
- `Dihedral.Separator.singleton_ne_top` ([DihedralHessenberg/Dihedral/RootFrame.lean](../DihedralHessenberg/Dihedral/RootFrame.lean))
- `Dihedral.Separator.disjoint` ([DihedralHessenberg/Dihedral/RootSeparator.lean](../DihedralHessenberg/Dihedral/RootSeparator.lean))
- `Dihedral.bruhatLE_iff_exists_sublist` ([DihedralHessenberg/Dihedral/CoxeterSystem.lean](../DihedralHessenberg/Dihedral/CoxeterSystem.lean))

### Example 2.3 (`ex:reflection`)

Status: **formalized**

- `Dihedral.polygonVertices` ([DihedralHessenberg/Dihedral/PolygonVertices.lean](../DihedralHessenberg/Dihedral/PolygonVertices.lean))
- `Dihedral.polygon_small_offsets` ([DihedralHessenberg/Dihedral/PolygonVertices.lean](../DihedralHessenberg/Dihedral/PolygonVertices.lean))
- `Dihedral.polygon_scaled_angles` ([DihedralHessenberg/Dihedral/PolygonVertices.lean](../DihedralHessenberg/Dihedral/PolygonVertices.lean))
- `Dihedral.polygon_action_mem` ([DihedralHessenberg/Dihedral/PolygonVertices.lean](../DihedralHessenberg/Dihedral/PolygonVertices.lean))
- `Dihedral.PositiveRoot.axis_drawn` ([DihedralHessenberg/Dihedral/PolygonAxes.lean](../DihedralHessenberg/Dihedral/PolygonAxes.lean))
- `Dihedral.drawn_axis_fixed` ([DihedralHessenberg/Dihedral/PolygonAxes.lean](../DihedralHessenberg/Dihedral/PolygonAxes.lean))
- `Dihedral.positiveRoots_unit_angles` ([DihedralHessenberg/Dihedral/UnitDirections.lean](../DihedralHessenberg/Dihedral/UnitDirections.lean))
- `Dihedral.PositiveRoot.reflection_axis` ([DihedralHessenberg/Dihedral/UnitDirections.lean](../DihedralHessenberg/Dihedral/UnitDirections.lean))
- `Dihedral.PositiveRoot.fixed_iff_axis` ([DihedralHessenberg/Dihedral/UnitDirections.lean](../DihedralHessenberg/Dihedral/UnitDirections.lean))

### Equation (1) (`eq:left_inversion_set`)

Status: **formalized**

- `Dihedral.leftInversionSet` ([DihedralHessenberg/Dihedral/RootInversionSets.lean](../DihedralHessenberg/Dihedral/RootInversionSets.lean))
- `Dihedral.leftInversionSet_descent` ([DihedralHessenberg/Dihedral/RootInversionDescent.lean](../DihedralHessenberg/Dihedral/RootInversionDescent.lean))
- `Dihedral.PositiveRoot.left_descent` ([DihedralHessenberg/Dihedral/RootInversionDescent.lean](../DihedralHessenberg/Dihedral/RootInversionDescent.lean))

### Equation (2) (`eq:right_inversion_set`)

Status: **formalized**

- `Dihedral.rightInversionSet` ([DihedralHessenberg/Dihedral/RootInversionSets.lean](../DihedralHessenberg/Dihedral/RootInversionSets.lean))
- `Dihedral.rightInversionSet_descent` ([DihedralHessenberg/Dihedral/RootInversionDescent.lean](../DihedralHessenberg/Dihedral/RootInversionDescent.lean))
- `Dihedral.PositiveRoot.right_descent` ([DihedralHessenberg/Dihedral/RootInversionDescent.lean](../DihedralHessenberg/Dihedral/RootInversionDescent.lean))

### Lemma 2.4 (`lem:rank_two_bruhat_facts`)

Status: **formalized**

The equality $\lvert N\_L(w)\rvert=\ell(w)$ is proved from the inversion sequence of a reduced word instead of a gallery, and part (2) is stated for every $u$.

- `Dihedral.unique_root_descent` ([DihedralHessenberg/Dihedral/RankTwoRootVectors.lean](../DihedralHessenberg/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.unique_root_ascent` ([DihedralHessenberg/Dihedral/RankTwoRootVectors.lean](../DihedralHessenberg/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.length_eq_longest` ([DihedralHessenberg/Dihedral/RankTwoRootVectors.lean](../DihedralHessenberg/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.bruhatLE_iff_eq_or_length_lt` ([DihedralHessenberg/Dihedral/RankTwoBruhat.lean](../DihedralHessenberg/Dihedral/RankTwoBruhat.lean))
- `Dihedral.ncard_leftInversionSet` ([DihedralHessenberg/Dihedral/RootSubsetCard.lean](../DihedralHessenberg/Dihedral/RootSubsetCard.lean))
- `Dihedral.PositiveRoot.left_ascent` ([DihedralHessenberg/Dihedral/RankTwoRootVectors.lean](../DihedralHessenberg/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.PositiveRoot.left_ascent_disjoint` ([DihedralHessenberg/Dihedral/RankTwoRootVectors.lean](../DihedralHessenberg/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.PositiveRoot.right_ascent` ([DihedralHessenberg/Dihedral/RankTwoRootVectors.lean](../DihedralHessenberg/Dihedral/RankTwoRootVectors.lean))

### The irreducible representations of $I\_2(n)$ and the coset representations $C\_\gamma$ (Section 2.3)

Status: **formalized**

Cited in the paper and proved here: the listed representations are irreducible, pairwise nonisomorphic, and as many as the conjugacy classes.

- `Dihedral.irreducible_dimension` ([DihedralHessenberg/Dihedral/RepresentationClassification.lean](../DihedralHessenberg/Dihedral/RepresentationClassification.lean))
- `Dihedral.irrep_counts_odd` ([DihedralHessenberg/Dihedral/IrrepDimensionCounts.lean](../DihedralHessenberg/Dihedral/IrrepDimensionCounts.lean))
- `Dihedral.irrep_counts_even` ([DihedralHessenberg/Dihedral/IrrepDimensionCounts.lean](../DihedralHessenberg/Dihedral/IrrepDimensionCounts.lean))
- `Dihedral.scalarFDRep` ([DihedralHessenberg/Dihedral/IrreducibleFamily.lean](../DihedralHessenberg/Dihedral/IrreducibleFamily.lean))
- `Dihedral.signCharacter_length` ([DihedralHessenberg/Dihedral/ScalarCharacterFacts.lean](../DihedralHessenberg/Dihedral/ScalarCharacterFacts.lean))
- `Dihedral.signFDRep_character` ([DihedralHessenberg/Dihedral/ScalarCharacters.lean](../DihedralHessenberg/Dihedral/ScalarCharacters.lean))
- `Dihedral.evenScalarCharacter_rotation` ([DihedralHessenberg/Dihedral/ScalarCharacters.lean](../DihedralHessenberg/Dihedral/ScalarCharacters.lean))
- `Dihedral.evenScalarCharacter_s1` ([DihedralHessenberg/Dihedral/ScalarCharacters.lean](../DihedralHessenberg/Dihedral/ScalarCharacters.lean))
- `Dihedral.frequencyFDRep_finrank` ([DihedralHessenberg/Dihedral/FrequencyRepresentation.lean](../DihedralHessenberg/Dihedral/FrequencyRepresentation.lean))
- `Dihedral.frequencyFDRep_simple_of_lower_half` ([DihedralHessenberg/Dihedral/FrequencyDistinction.lean](../DihedralHessenberg/Dihedral/FrequencyDistinction.lean))
- `Dihedral.Frequency.character_zpow` ([DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean](../DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.Frequency.character_zpow_s1` ([DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean](../DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.frequency_one` ([DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean](../DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.frequency_one_iso` ([DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean](../DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.irreducible_classification` ([DihedralHessenberg/Dihedral/RepresentationClassification.lean](../DihedralHessenberg/Dihedral/RepresentationClassification.lean))
- `Dihedral.irrepFDRep_iso_iff_eq` ([DihedralHessenberg/Dihedral/IrreducibleClassification.lean](../DihedralHessenberg/Dihedral/IrreducibleClassification.lean))
- `Dihedral.PositiveRoot.scalarCharacter_reflection` ([DihedralHessenberg/Dihedral/RootScalarCharacter.lean](../DihedralHessenberg/Dihedral/RootScalarCharacter.lean))
- `Dihedral.PositiveRoot.scalarCharacter_unique` ([DihedralHessenberg/Dihedral/RootScalarCharacter.lean](../DihedralHessenberg/Dihedral/RootScalarCharacter.lean))
- `Dihedral.PositiveRoot.cosetFDRep` ([DihedralHessenberg/Dihedral/CosetFDRep.lean](../DihedralHessenberg/Dihedral/CosetFDRep.lean))
- `Dihedral.PositiveRoot.coset_odd_iso` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_iso` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))

### Equation (3) (`eq:reflection_coset_decomposition`)

Status: **formalized**

Cited in the paper and proved here, by comparing characters.

- `Dihedral.PositiveRoot.cosetFDRep` ([DihedralHessenberg/Dihedral/CosetFDRep.lean](../DihedralHessenberg/Dihedral/CosetFDRep.lean))
- `Dihedral.PositiveRoot.coset_odd_iso` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_iso` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_odd_class` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_class` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.scalarCharacter_reflection` ([DihedralHessenberg/Dihedral/RootScalarCharacter.lean](../DihedralHessenberg/Dihedral/RootScalarCharacter.lean))
- `Dihedral.PositiveRoot.scalarCharacter_unique` ([DihedralHessenberg/Dihedral/RootScalarCharacter.lean](../DihedralHessenberg/Dihedral/RootScalarCharacter.lean))

### Example 2.5

Status: **formalized**

- `DihedralSplines.square_first_matrix` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_second_matrix` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_longest` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_third_reflection` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_simple_sign` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_third_sign` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_simple_trivial` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `DihedralSplines.square_trivial_character` ([DihedralHessenberg/Paper/SquareAction.lean](../DihedralHessenberg/Paper/SquareAction.lean))
- `Dihedral.frequency_one` ([DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean](../DihedralHessenberg/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.signCharacter_length` ([DihedralHessenberg/Dihedral/ScalarCharacterFacts.lean](../DihedralHessenberg/Dihedral/ScalarCharacterFacts.lean))

### Definition 2.6 (`def:root_poset`)

Status: **formalized**

- `DihedralSplines.RootOrder` ([DihedralHessenberg/Paper/RootOrder.lean](../DihedralHessenberg/Paper/RootOrder.lean))
- `DihedralSplines.rootOrder` ([DihedralHessenberg/Paper/RootOrder.lean](../DihedralHessenberg/Paper/RootOrder.lean))
- `DihedralSplines.rootOrder_refl` ([DihedralHessenberg/Paper/RootOrder.lean](../DihedralHessenberg/Paper/RootOrder.lean))
- `DihedralSplines.rootOrder_trans` ([DihedralHessenberg/Paper/RootOrder.lean](../DihedralHessenberg/Paper/RootOrder.lean))
- `DihedralSplines.rootOrder_antisymm` ([DihedralHessenberg/Paper/RootOrder.lean](../DihedralHessenberg/Paper/RootOrder.lean))

### The Hasse diagrams of the root poset (Section 2.4)

Status: **formalized**

- `DihedralSplines.rootOrder_layers` ([DihedralHessenberg/Paper/HessenbergVectorClassification.lean](../DihedralHessenberg/Paper/HessenbergVectorClassification.lean))
- `DihedralSplines.rootOrder_lt_iff` ([DihedralHessenberg/Paper/RootOrderCovers.lean](../DihedralHessenberg/Paper/RootOrderCovers.lean))
- `DihedralSplines.rootOrder_covBy_iff` ([DihedralHessenberg/Paper/RootOrderCovers.lean](../DihedralHessenberg/Paper/RootOrderCovers.lean))
- `DihedralSplines.layer_card` ([DihedralHessenberg/Paper/RootOrderCovers.lean](../DihedralHessenberg/Paper/RootOrderCovers.lean))

### Remark 2.7

Status: **formalized**

- `DihedralSplines.rootOrder_length` ([DihedralHessenberg/Paper/RootVectorComparison.lean](../DihedralHessenberg/Paper/RootVectorComparison.lean))
- `DihedralSplines.rootOrder_bruhat` ([DihedralHessenberg/Paper/RootVectorComparison.lean](../DihedralHessenberg/Paper/RootVectorComparison.lean))

### The list of Hessenberg spaces (Section 2.4)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal` ([DihedralHessenberg/Paper/HessenbergObjects.lean](../DihedralHessenberg/Paper/HessenbergObjects.lean))
- `DihedralSplines.HessenbergIdeal.classification` ([DihedralHessenberg/Paper/HessenbergVectorClassification.lean](../DihedralHessenberg/Paper/HessenbergVectorClassification.lean))
- `DihedralSplines.HessenbergIdeal.exists_initial` ([DihedralHessenberg/Paper/HessenbergVectorClassification.lean](../DihedralHessenberg/Paper/HessenbergVectorClassification.lean))
- `DihedralSplines.HessenbergIdeal.exists_other` ([DihedralHessenberg/Paper/HessenbergVectorClassification.lean](../DihedralHessenberg/Paper/HessenbergVectorClassification.lean))
- `DihedralSplines.HessenbergIdeal.natCard` ([DihedralHessenberg/Paper/HessenbergVectorClassification.lean](../DihedralHessenberg/Paper/HessenbergVectorClassification.lean))

### Remark 2.8

Status: **formalized**

- `Dihedral.PositiveRoot.depth` ([DihedralHessenberg/Dihedral/RootDepth.lean](../DihedralHessenberg/Dihedral/RootDepth.lean))
- `Dihedral.DepthStep` ([DihedralHessenberg/Dihedral/RootDepthOrder.lean](../DihedralHessenberg/Dihedral/RootDepthOrder.lean))
- `Dihedral.PositiveRoot.depth_layer` ([DihedralHessenberg/Dihedral/RootDepthLayers.lean](../DihedralHessenberg/Dihedral/RootDepthLayers.lean))
- `Dihedral.depth_step_iff` ([DihedralHessenberg/Dihedral/RootDepthChains.lean](../DihedralHessenberg/Dihedral/RootDepthChains.lean))
- `Dihedral.depth_order_iff` ([DihedralHessenberg/Dihedral/RootDepthChains.lean](../DihedralHessenberg/Dihedral/RootDepthChains.lean))
- `Dihedral.Separator.label_ideal_signs` ([DihedralHessenberg/Paper/ChamberSplines.lean](../DihedralHessenberg/Paper/ChamberSplines.lean))
- `Dihedral.Separator.spline_signs` ([DihedralHessenberg/Paper/ChamberSplines.lean](../DihedralHessenberg/Paper/ChamberSplines.lean))
- `Dihedral.Separator.spline_set_signs` ([DihedralHessenberg/Paper/ChamberSplines.lean](../DihedralHessenberg/Paper/ChamberSplines.lean))
- `DihedralSplines.six_depth_counterexample` ([DihedralHessenberg/Paper/HexagonDepthCounterexample.lean](../DihedralHessenberg/Paper/HexagonDepthCounterexample.lean))
- `DihedralSplines.six_three_root_ideal` ([DihedralHessenberg/Paper/SixRootIdeal.lean](../DihedralHessenberg/Paper/SixRootIdeal.lean))

### Remark 2.9

Status: **formalized**

Here $B\_2$, $C\_2$ and $G\_2$ are obtained from the unit roots of $I\_2(4)$ and $I\_2(6)$ by rescaling one orbit of roots.

- `DihedralSplines.four_orders_differ` ([DihedralHessenberg/Paper/CrystallographicComparison.lean](../DihedralHessenberg/Paper/CrystallographicComparison.lean))
- `DihedralSplines.four_lower_ideals` ([DihedralHessenberg/Paper/CrystallographicComparison.lean](../DihedralHessenberg/Paper/CrystallographicComparison.lean))
- `DihedralSplines.six_unit_not_g2` ([DihedralHessenberg/Paper/CrystallographicComparison.lean](../DihedralHessenberg/Paper/CrystallographicComparison.lean))
- `DihedralSplines.six_g2_not_unit` ([DihedralHessenberg/Paper/CrystallographicComparison.lean](../DihedralHessenberg/Paper/CrystallographicComparison.lean))
- `Dihedral.RootLattice.a2_order` ([DihedralHessenberg/Paper/CrystallographicComparison.lean](../DihedralHessenberg/Paper/CrystallographicComparison.lean))
- `Dihedral.RootLattice.a2_lower_iff` ([DihedralHessenberg/Paper/CrystallographicComparison.lean](../DihedralHessenberg/Paper/CrystallographicComparison.lean))
- `Dihedral.RootLattice.a2_crystallographic` ([DihedralHessenberg/Dihedral/Crystallographic.lean](../DihedralHessenberg/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.b2_crystallographic` ([DihedralHessenberg/Dihedral/Crystallographic.lean](../DihedralHessenberg/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.c2_crystallographic` ([DihedralHessenberg/Dihedral/Crystallographic.lean](../DihedralHessenberg/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.g2_crystallographic` ([DihedralHessenberg/Dihedral/Crystallographic.lean](../DihedralHessenberg/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.a2GroupEquiv` ([DihedralHessenberg/Dihedral/RadialReflectionGroup.lean](../DihedralHessenberg/Dihedral/RadialReflectionGroup.lean))
- `Dihedral.RootLattice.b2GroupEquiv` ([DihedralHessenberg/Dihedral/RadialReflectionGroup.lean](../DihedralHessenberg/Dihedral/RadialReflectionGroup.lean))
- `Dihedral.RootLattice.c2GroupEquiv` ([DihedralHessenberg/Dihedral/RadialReflectionGroup.lean](../DihedralHessenberg/Dihedral/RadialReflectionGroup.lean))
- `Dihedral.RootLattice.g2GroupEquiv` ([DihedralHessenberg/Dihedral/RadialReflectionGroup.lean](../DihedralHessenberg/Dihedral/RadialReflectionGroup.lean))

### Definition 2.10 (`def:inversion_set`)

Status: **formalized**

- `Dihedral.RootSubset.inversions` ([DihedralHessenberg/Dihedral/RootInversionSets.lean](../DihedralHessenberg/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.length` ([DihedralHessenberg/Dihedral/RootInversionSets.lean](../DihedralHessenberg/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.mem_inversions` ([DihedralHessenberg/Dihedral/RootInversionSets.lean](../DihedralHessenberg/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.inversions_finite` ([DihedralHessenberg/Dihedral/RootInversionSets.lean](../DihedralHessenberg/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.inversions_bijOn` ([DihedralHessenberg/Dihedral/RootSubsetImages.lean](../DihedralHessenberg/Dihedral/RootSubsetImages.lean))
- `Dihedral.rightInversionSet_descent` ([DihedralHessenberg/Dihedral/RootInversionDescent.lean](../DihedralHessenberg/Dihedral/RootInversionDescent.lean))
- `Dihedral.PositiveRoot.right_descent` ([DihedralHessenberg/Dihedral/RootInversionDescent.lean](../DihedralHessenberg/Dihedral/RootInversionDescent.lean))

### The labeled Cayley graph (Section 2.4)

Status: **formalized**

- `Dihedral.RootSubset.edges` ([DihedralHessenberg/Paper/PaperGraph.lean](../DihedralHessenberg/Paper/PaperGraph.lean))
- `Dihedral.RootSubset.mem_edges` ([DihedralHessenberg/Paper/PaperGraph.lean](../DihedralHessenberg/Paper/PaperGraph.lean))
- `Dihedral.RootSubset.edgeLabel_edge` ([DihedralHessenberg/Paper/PaperGraph.lean](../DihedralHessenberg/Paper/PaperGraph.lean))
- `Dihedral.RootSubset.edgeLabel_eq_action` ([DihedralHessenberg/Paper/PaperGraph.lean](../DihedralHessenberg/Paper/PaperGraph.lean))
- `Dihedral.RootSubset.edgeEquiv` ([DihedralHessenberg/Paper/PaperGraph.lean](../DihedralHessenberg/Paper/PaperGraph.lean))
- `Dihedral.RootSubset.label_reverse` ([DihedralHessenberg/Paper/PaperGraph.lean](../DihedralHessenberg/Paper/PaperGraph.lean))

### Example 2.11 (`ex:cayley`)

Status: **formalized**

- `DihedralSplines.Triangle.selected` ([DihedralHessenberg/Paper/TriangleCayley.lean](../DihedralHessenberg/Paper/TriangleCayley.lean))
- `DihedralSplines.Triangle.pairs` ([DihedralHessenberg/Paper/TriangleCayley.lean](../DihedralHessenberg/Paper/TriangleCayley.lean))
- `DihedralSplines.Triangle.edges` ([DihedralHessenberg/Paper/TriangleCayley.lean](../DihedralHessenberg/Paper/TriangleCayley.lean))
- `DihedralSplines.Triangle.edge_labels` ([DihedralHessenberg/Paper/TriangleCayley.lean](../DihedralHessenberg/Paper/TriangleCayley.lean))
- `DihedralSplines.Triangle.inversions` ([DihedralHessenberg/Paper/TriangleCayley.lean](../DihedralHessenberg/Paper/TriangleCayley.lean))
- `DihedralSplines.Square.selected` ([DihedralHessenberg/Paper/SquareCayley.lean](../DihedralHessenberg/Paper/SquareCayley.lean))
- `DihedralSplines.Square.pairs` ([DihedralHessenberg/Paper/SquareCayley.lean](../DihedralHessenberg/Paper/SquareCayley.lean))
- `DihedralSplines.Square.edges` ([DihedralHessenberg/Paper/SquareCayley.lean](../DihedralHessenberg/Paper/SquareCayley.lean))
- `DihedralSplines.Square.edge_labels` ([DihedralHessenberg/Paper/SquareCayley.lean](../DihedralHessenberg/Paper/SquareCayley.lean))

### The acyclic orientation of the Cayley graph and the order $\prec\_H$ (Section 2.4)

Status: **formalized**

- `Dihedral.RootSubset.orientedEdges` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.reachable` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.acyclic` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.incoming_card` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.partialOrder` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.reachable_strict_iff` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.partialOrder_lt` ([DihedralHessenberg/Paper/OrientedGraph.lean](../DihedralHessenberg/Paper/OrientedGraph.lean))
- `Dihedral.RootSubset.edge_length_ne` ([DihedralHessenberg/Paper/OrientedEdgeLengths.lean](../DihedralHessenberg/Paper/OrientedEdgeLengths.lean))
- `Dihedral.RootSubset.oriented_xor_reverse` ([DihedralHessenberg/Paper/OrientedEdgeLengths.lean](../DihedralHessenberg/Paper/OrientedEdgeLengths.lean))

### Example 2.12

Status: **formalized**

- `Dihedral.RootSubset.simple_reachable` ([DihedralHessenberg/Paper/SimpleOrientedGraph.lean](../DihedralHessenberg/Paper/SimpleOrientedGraph.lean))
- `Dihedral.rightWeakLE_prefix` ([DihedralHessenberg/Dihedral/RightWeak.lean](../DihedralHessenberg/Dihedral/RightWeak.lean))
- `Dihedral.RootSubset.full_reachable` ([DihedralHessenberg/Paper/FullOrientedGraph.lean](../DihedralHessenberg/Paper/FullOrientedGraph.lean))

### Example 2.13

Status: **formalized**

- `DihedralSplines.pentagon_oriented` ([DihedralHessenberg/Paper/PentagonOrientation.lean](../DihedralHessenberg/Paper/PentagonOrientation.lean))
- `DihedralSplines.pentagon_cover_iff` ([DihedralHessenberg/Paper/PentagonHasse.lean](../DihedralHessenberg/Paper/PentagonHasse.lean))
- `DihedralSplines.pentagon_hasse` ([DihedralHessenberg/Paper/PentagonHasse.lean](../DihedralHessenberg/Paper/PentagonHasse.lean))

### The module of splines (Section 2.5)

Status: **formalized**

- `Dihedral.RootSubset.IsSpline` ([DihedralHessenberg/Paper/PaperSpline.lean](../DihedralHessenberg/Paper/PaperSpline.lean))
- `Dihedral.RootSubset.splineAlgebra` ([DihedralHessenberg/Paper/PaperSpline.lean](../DihedralHessenberg/Paper/PaperSpline.lean))
- `Dihedral.RootSubset.mem_splineAlgebra` ([DihedralHessenberg/Paper/PaperSpline.lean](../DihedralHessenberg/Paper/PaperSpline.lean))
- `DihedralSplines.HessenbergIdeal.splineEquiv_apply` ([DihedralHessenberg/Paper/PaperIdeal.lean](../DihedralHessenberg/Paper/PaperIdeal.lean))

### The spline diagrams for $I\_2(3)$ (Section 2.5)

Status: **formalized**

- `DihedralSplines.TriangleIllustrations.value` ([DihedralHessenberg/Paper/TriangleSplines.lean](../DihedralHessenberg/Paper/TriangleSplines.lean))
- `DihedralSplines.TriangleIllustrations.word_values` ([DihedralHessenberg/Paper/TriangleSplines.lean](../DihedralHessenberg/Paper/TriangleSplines.lean))
- `DihedralSplines.TriangleIllustrations.rows` ([DihedralHessenberg/Paper/TriangleSplines.lean](../DihedralHessenberg/Paper/TriangleSplines.lean))
- `DihedralSplines.TriangleIllustrations.isSpline` ([DihedralHessenberg/Paper/TriangleSplines.lean](../DihedralHessenberg/Paper/TriangleSplines.lean))

### The spline diagrams for $I\_2(4)$ (Section 2.5)

Status: **formalized**

- `DihedralSplines.SquareIllustrations.value` ([DihedralHessenberg/Paper/SquareSplines.lean](../DihedralHessenberg/Paper/SquareSplines.lean))
- `DihedralSplines.SquareIllustrations.word_values` ([DihedralHessenberg/Paper/SquareSplines.lean](../DihedralHessenberg/Paper/SquareSplines.lean))
- `DihedralSplines.SquareIllustrations.rows` ([DihedralHessenberg/Paper/SquareSplines.lean](../DihedralHessenberg/Paper/SquareSplines.lean))
- `DihedralSplines.SquareIllustrations.isSpline` ([DihedralHessenberg/Paper/SquareSplines.lean](../DihedralHessenberg/Paper/SquareSplines.lean))

### Edge labels and conjugate reflections (Section 2.5)

Status: **formalized**

- `Dihedral.RootSubset.edgeLabel_eq_form_iff` ([DihedralHessenberg/Paper/EdgeLabelReflection.lean](../DihedralHessenberg/Paper/EdgeLabelReflection.lean))

### Lemma 2.14

Status: **formalized**

- `Dihedral.RootSubset.splineAlgebra` ([DihedralHessenberg/Paper/PaperSpline.lean](../DihedralHessenberg/Paper/PaperSpline.lean))
- `Dihedral.RootSubset.mem_splineAlgebra` ([DihedralHessenberg/Paper/PaperSpline.lean](../DihedralHessenberg/Paper/PaperSpline.lean))

### Lemma 2.15

Status: **formalized**

- `Dihedral.RootSubset.piece` ([DihedralHessenberg/Paper/PaperGrading.lean](../DihedralHessenberg/Paper/PaperGrading.lean))
- `Dihedral.RootSubset.mem_piece` ([DihedralHessenberg/Paper/PaperGrading.lean](../DihedralHessenberg/Paper/PaperGrading.lean))
- `Dihedral.RootSubset.component_apply` ([DihedralHessenberg/Paper/PaperGrading.lean](../DihedralHessenberg/Paper/PaperGrading.lean))
- `Dihedral.RootSubset.piece_isInternal` ([DihedralHessenberg/Paper/PaperGrading.lean](../DihedralHessenberg/Paper/PaperGrading.lean))
- `Dihedral.RootSubset.gradedAlgebra` ([DihedralHessenberg/Paper/PaperGrading.lean](../DihedralHessenberg/Paper/PaperGrading.lean))

### Constant and orbit splines and the two module structures (Section 2.5)

Status: **formalized**

- `Dihedral.RootSubset.constantHom` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.orbitHom` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.constantHom_injective` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.orbitHom_injective` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.one_apply` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.xLeft_apply` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.yLeft_apply` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.xRight_apply` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.yRight_apply` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.constantHom_mem_piece` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.orbitHom_mem_piece` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.Left.smul_mem_piece` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.Right.smul_mem_piece` ([DihedralHessenberg/Paper/PaperCoordinates.lean](../DihedralHessenberg/Paper/PaperCoordinates.lean))
- `Dihedral.RootSubset.Left.module_finite` ([DihedralHessenberg/Paper/PaperScalarTransport.lean](../DihedralHessenberg/Paper/PaperScalarTransport.lean))
- `Dihedral.RootSubset.Right.module_finite` ([DihedralHessenberg/Paper/PaperScalarTransport.lean](../DihedralHessenberg/Paper/PaperScalarTransport.lean))
- `Dihedral.RootSubset.Left.homogeneous_generators` ([DihedralHessenberg/Paper/PaperModuleFinite.lean](../DihedralHessenberg/Paper/PaperModuleFinite.lean))
- `Dihedral.RootSubset.Right.homogeneous_generators` ([DihedralHessenberg/Paper/PaperModuleFinite.lean](../DihedralHessenberg/Paper/PaperModuleFinite.lean))
- `Dihedral.RootSubset.not_moduleFinite` ([DihedralHessenberg/Paper/PaperModuleFinite.lean](../DihedralHessenberg/Paper/PaperModuleFinite.lean))

### Equation (4) (`eqn:left_action`)

Status: **formalized**

- `Dihedral.RootSubset.left_formula` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.constantHom_aeval` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))

### Equation (5) (`eqn:right_action`)

Status: **formalized**

- `Dihedral.RootSubset.right_formula` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.orbitHom_aeval` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))

### Lemma 2.16

Status: **formalized**

The proof counts the generators of each degree with the flow-up basis of Theorem 4.5.

- `DihedralSplines.HessenbergIdeal.Left.minimal_degree_count` ([DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean](../DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Left.minimal_degrees_eq` ([DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean](../DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Right.minimal_degree_count` ([DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean](../DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Right.minimal_degrees_eq` ([DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean](../DihedralHessenberg/Paper/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Left.minimal_finite` ([DihedralHessenberg/Paper/MinimalGeneratorFinite.lean](../DihedralHessenberg/Paper/MinimalGeneratorFinite.lean))
- `DihedralSplines.HessenbergIdeal.Right.minimal_finite` ([DihedralHessenberg/Paper/MinimalGeneratorFinite.lean](../DihedralHessenberg/Paper/MinimalGeneratorFinite.lean))

### Definition 2.17 (`def:upper_triangular`)

Status: **formalized**

- `Splines.PolynomialGraph.IsUpperAt` ([DihedralHessenberg/Splines/UpperTriangular.lean](../DihedralHessenberg/Splines/UpperTriangular.lean))
- `Splines.PolynomialGraph.IsUpperFamily` ([DihedralHessenberg/Splines/UpperTriangular.lean](../DihedralHessenberg/Splines/UpperTriangular.lean))
- `Splines.PolynomialGraph.upperAt_ideal` ([DihedralHessenberg/Splines/UpperTriangular.lean](../DihedralHessenberg/Splines/UpperTriangular.lean))
- `Splines.PolynomialGraph.upperFamily_ideal` ([DihedralHessenberg/Splines/UpperTriangular.lean](../DihedralHessenberg/Splines/UpperTriangular.lean))

### Remark 2.18

Status: **formalized**

- `Splines.PolynomialGraph.upper_matrix` ([DihedralHessenberg/Splines/UpperTriangular.lean](../DihedralHessenberg/Splines/UpperTriangular.lean))

### Lemma 2.19 (`lem:upper_triangular`)

Status: **formalized**

Here the splines need not be homogeneous, and $\deg\overline{\rho}\_w$ is the largest degree of the values of $\overline{\rho}\_w$.

- `DihedralSplines.TriangularFamily.Left.basis` ([DihedralHessenberg/Paper/FamilyBasis.lean](../DihedralHessenberg/Paper/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Left.basis_apply` ([DihedralHessenberg/Paper/FamilyBasis.lean](../DihedralHessenberg/Paper/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Left.minimal` ([DihedralHessenberg/Paper/FamilyBasis.lean](../DihedralHessenberg/Paper/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Right.basis` ([DihedralHessenberg/Paper/FamilyBasis.lean](../DihedralHessenberg/Paper/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Right.basis_apply` ([DihedralHessenberg/Paper/FamilyBasis.lean](../DihedralHessenberg/Paper/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Right.minimal` ([DihedralHessenberg/Paper/FamilyBasis.lean](../DihedralHessenberg/Paper/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.projectedValue_mem` ([DihedralHessenberg/Paper/FamilyProjection.lean](../DihedralHessenberg/Paper/FamilyProjection.lean))
- `DihedralSplines.TriangularFamily.projectedValue_diagonal` ([DihedralHessenberg/Paper/FamilyProjection.lean](../DihedralHessenberg/Paper/FamilyProjection.lean))
- `DihedralSplines.TriangularFamily.Left.piece_finrank` ([DihedralHessenberg/Paper/FamilyRank.lean](../DihedralHessenberg/Paper/FamilyRank.lean))
- `DihedralSplines.TriangularFamily.Right.piece_finrank` ([DihedralHessenberg/Paper/FamilyRank.lean](../DihedralHessenberg/Paper/FamilyRank.lean))
- `DihedralSplines.TriangularFamily.Left.rankPolynomial_eq` ([DihedralHessenberg/Paper/FamilyRank.lean](../DihedralHessenberg/Paper/FamilyRank.lean))
- `DihedralSplines.TriangularFamily.Right.rankPolynomial_eq` ([DihedralHessenberg/Paper/FamilyRank.lean](../DihedralHessenberg/Paper/FamilyRank.lean))
- `DihedralSplines.HessenbergIdeal.Left.rankPolynomial_coeff` ([DihedralHessenberg/Paper/FamilyRank.lean](../DihedralHessenberg/Paper/FamilyRank.lean))
- `DihedralSplines.HessenbergIdeal.Right.rankPolynomial_coeff` ([DihedralHessenberg/Paper/FamilyRank.lean](../DihedralHessenberg/Paper/FamilyRank.lean))

### Definition 2.20 (`def:flowup`)

Status: **formalized**

- `DihedralSplines.TriangularFamily.Left.IsFlowup` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Right.IsFlowup` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Left.isFlowup_iff` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Right.isFlowup_iff` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.IsMember` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.At` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.family_at` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.at_least` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Left.member_iff` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Right.member_iff` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))

### Definition 2.21

Status: **formalized**

- `Dihedral.RootSubset.dot` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.dot_apply` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.dot_one` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.dot_mul` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.dotAction` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))

### Lemma 2.22 (`lem:dot_action_preserves_splines`)

Status: **formalized**

- `Dihedral.RootSubset.dot` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))
- `Dihedral.RootSubset.dot_apply` ([DihedralHessenberg/Paper/PaperAction.lean](../DihedralHessenberg/Paper/PaperAction.lean))

### Equation (6) (`eqndef:left_quotient`)

Status: **formalized**

- `Dihedral.RootSubset.Left.ideal_span` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.ideal_smul_top` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.Quotient` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.quotientMap` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.backendEquiv_map` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.piece` ([DihedralHessenberg/Paper/PaperQuotientGrading.lean](../DihedralHessenberg/Paper/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Left.gradedAlgebra` ([DihedralHessenberg/Paper/PaperQuotientGrading.lean](../DihedralHessenberg/Paper/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Left.dot_map` ([DihedralHessenberg/Paper/PaperQuotientAction.lean](../DihedralHessenberg/Paper/PaperQuotientAction.lean))
- `Dihedral.RootSubset.Left.pieceRepresentation` ([DihedralHessenberg/Paper/PaperQuotientAction.lean](../DihedralHessenberg/Paper/PaperQuotientAction.lean))

### Equation (7) (`eqndef:right_quotient`)

Status: **formalized**

- `Dihedral.RootSubset.Right.ideal_span` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.ideal_smul_top` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.Quotient` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.quotientMap` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.backendEquiv_map` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.piece` ([DihedralHessenberg/Paper/PaperQuotientGrading.lean](../DihedralHessenberg/Paper/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Right.gradedAlgebra` ([DihedralHessenberg/Paper/PaperQuotientGrading.lean](../DihedralHessenberg/Paper/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Right.dot_map` ([DihedralHessenberg/Paper/PaperQuotientAction.lean](../DihedralHessenberg/Paper/PaperQuotientAction.lean))
- `Dihedral.RootSubset.Right.pieceRepresentation` ([DihedralHessenberg/Paper/PaperQuotientAction.lean](../DihedralHessenberg/Paper/PaperQuotientAction.lean))

### Lemma 3.1 (`lem:left_edges_full_graph`)

Status: **formalized**

- `Dihedral.RootSubset.full_iff_left` ([DihedralHessenberg/Paper/PaperFull.lean](../DihedralHessenberg/Paper/PaperFull.lean))
- `DihedralSplines.HessenbergIdeal.full_iff_left` ([DihedralHessenberg/Paper/PaperFull.lean](../DihedralHessenberg/Paper/PaperFull.lean))

### Equation (8) (`eq:left_spline_condition_full`)

Status: **formalized**

- `Dihedral.RootSubset.full_algebra_eq` ([DihedralHessenberg/Paper/PaperFull.lean](../DihedralHessenberg/Paper/PaperFull.lean))
- `DihedralSplines.HessenbergIdeal.full_algebra_eq` ([DihedralHessenberg/Paper/PaperFull.lean](../DihedralHessenberg/Paper/PaperFull.lean))

### Lemma 3.2 (`lem:divided_difference_spline`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.full_edge` ([DihedralHessenberg/Paper/SchubertOperators.lean](../DihedralHessenberg/Paper/SchubertOperators.lean))
- `DihedralSplines.SchubertSpline.difference` ([DihedralHessenberg/Paper/SchubertOperators.lean](../DihedralHessenberg/Paper/SchubertOperators.lean))
- `DihedralSplines.SchubertSpline.difference_mul` ([DihedralHessenberg/Paper/SchubertOperators.lean](../DihedralHessenberg/Paper/SchubertOperators.lean))

### Equation (9) (`eq:divided_difference_spline`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.difference` ([DihedralHessenberg/Paper/SchubertOperators.lean](../DihedralHessenberg/Paper/SchubertOperators.lean))
- `DihedralSplines.SchubertSpline.difference_mul` ([DihedralHessenberg/Paper/SchubertOperators.lean](../DihedralHessenberg/Paper/SchubertOperators.lean))

### Equation (10) (`eq:top_schubert_spline`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.top` ([DihedralHessenberg/Paper/SchubertConstruction.lean](../DihedralHessenberg/Paper/SchubertConstruction.lean))
- `DihedralSplines.SchubertSpline.top_apply` ([DihedralHessenberg/Paper/SchubertConstruction.lean](../DihedralHessenberg/Paper/SchubertConstruction.lean))
- `DihedralSplines.SchubertSpline.spline_top` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))

### Equation (11) (`eq:schubert_recursion`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.spline_one` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.spline_top` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.spline_step` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.ascentRoot_spec` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.ascentRoot_eq` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))

### Proposition 3.3 (`prop:schubert_flowup`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.homogeneous` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.support` ([DihedralHessenberg/Paper/SchubertRecursion.lean](../DihedralHessenberg/Paper/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.diagonal_product` ([DihedralHessenberg/Paper/SchubertDiagonal.lean](../DihedralHessenberg/Paper/SchubertDiagonal.lean))
- `DihedralSplines.SchubertSpline.degree` ([DihedralHessenberg/Paper/SchubertBasis.lean](../DihedralHessenberg/Paper/SchubertBasis.lean))

### Equation (12) (`eq:schubert_diagonal_value`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.diagonalProduct` ([DihedralHessenberg/Paper/SchubertDiagonal.lean](../DihedralHessenberg/Paper/SchubertDiagonal.lean))
- `DihedralSplines.SchubertSpline.diagonal_product` ([DihedralHessenberg/Paper/SchubertDiagonal.lean](../DihedralHessenberg/Paper/SchubertDiagonal.lean))

### Theorem 3.4 (`thm:schubert_rational`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.rationalRoots` ([DihedralHessenberg/Paper/SchubertRational.lean](../DihedralHessenberg/Paper/SchubertRational.lean))
- `DihedralSplines.SchubertSpline.rationalProduct` ([DihedralHessenberg/Paper/SchubertRational.lean](../DihedralHessenberg/Paper/SchubertRational.lean))
- `DihedralSplines.SchubertSpline.rational_formula` ([DihedralHessenberg/Paper/SchubertRational.lean](../DihedralHessenberg/Paper/SchubertRational.lean))
- `DihedralSplines.SchubertSpline.support_exact` ([DihedralHessenberg/Paper/SchubertLocalization.lean](../DihedralHessenberg/Paper/SchubertLocalization.lean))

### Linear forms of distinct positive roots are not proportional (Section 3)

Status: **formalized**

- `Dihedral.PositiveRoot.form_ne_zero` ([DihedralHessenberg/Dihedral/RootObjectAction.lean](../DihedralHessenberg/Dihedral/RootObjectAction.lean))
- `Dihedral.PositiveRoot.form_not_proportional` ([DihedralHessenberg/Dihedral/RootFormProperties.lean](../DihedralHessenberg/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.form_not_associated` ([DihedralHessenberg/Dihedral/RootFormProperties.lean](../DihedralHessenberg/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.form_relPrime` ([DihedralHessenberg/Dihedral/RootFormProperties.lean](../DihedralHessenberg/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.action_not_proportional` ([DihedralHessenberg/Dihedral/RootObjectAction.lean](../DihedralHessenberg/Dihedral/RootObjectAction.lean))
- `Dihedral.PositiveRoot.action_not_associated` ([DihedralHessenberg/Dihedral/RootFormProperties.lean](../DihedralHessenberg/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.action_relPrime` ([DihedralHessenberg/Dihedral/RootObjectAction.lean](../DihedralHessenberg/Dihedral/RootObjectAction.lean))

### Proposition 3.5 (`prop:schubert_basis`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.left_basis` ([DihedralHessenberg/Paper/SchubertBasis.lean](../DihedralHessenberg/Paper/SchubertBasis.lean))
- `DihedralSplines.SchubertSpline.right_basis` ([DihedralHessenberg/Paper/SchubertBasis.lean](../DihedralHessenberg/Paper/SchubertBasis.lean))
- `DihedralSplines.SchubertSpline.homogeneous_basis` ([DihedralHessenberg/Paper/SchubertBasis.lean](../DihedralHessenberg/Paper/SchubertBasis.lean))
- `DihedralSplines.SchubertSpline.degree` ([DihedralHessenberg/Paper/SchubertBasis.lean](../DihedralHessenberg/Paper/SchubertBasis.lean))

### Corollary 3.6 (`cor:schubert_hilbert_series`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.length_sum` ([DihedralHessenberg/Paper/SchubertHilbert.lean](../DihedralHessenberg/Paper/SchubertHilbert.lean))
- `DihedralSplines.SchubertSpline.length_factor` ([DihedralHessenberg/Paper/SchubertHilbert.lean](../DihedralHessenberg/Paper/SchubertHilbert.lean))
- `DihedralSplines.SchubertSpline.hilbert_formula` ([DihedralHessenberg/Paper/SchubertHilbert.lean](../DihedralHessenberg/Paper/SchubertHilbert.lean))

### Lemma 3.7 (`lem:borel_presentation_schubert_splines`)

Status: **formalized**

Injectivity of $\Psi$ is proved by Dedekind's independence of characters instead of by localization.

- `DihedralSplines.borelEquiv` ([DihedralHessenberg/Paper/BorelEquivalence.lean](../DihedralHessenberg/Paper/BorelEquivalence.lean))
- `DihedralSplines.borelEquiv_tmul` ([DihedralHessenberg/Paper/BorelEquivalence.lean](../DihedralHessenberg/Paper/BorelEquivalence.lean))
- `DihedralSplines.borelTensorPiece` ([DihedralHessenberg/Paper/BorelTensorGrading.lean](../DihedralHessenberg/Paper/BorelTensorGrading.lean))
- `DihedralSplines.borelTensorPiece_map` ([DihedralHessenberg/Paper/BorelTensorGrading.lean](../DihedralHessenberg/Paper/BorelTensorGrading.lean))
- `DihedralSplines.borelEquiv_xLeft` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yLeft` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_xRight` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yRight` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_dot` ([DihedralHessenberg/Paper/BorelAction.lean](../DihedralHessenberg/Paper/BorelAction.lean))

### Equation (13) (`eq:borel_presentation_schubert_splines`)

Status: **formalized**

- `DihedralSplines.borelEquiv` ([DihedralHessenberg/Paper/BorelEquivalence.lean](../DihedralHessenberg/Paper/BorelEquivalence.lean))
- `DihedralSplines.borelEquiv_tmul` ([DihedralHessenberg/Paper/BorelEquivalence.lean](../DihedralHessenberg/Paper/BorelEquivalence.lean))

### The tensor decomposition over the fixed field (Section 3)

Status: **formalized**

- `Dihedral.first_tensor_localization` ([DihedralHessenberg/Dihedral/FirstLocalization.lean](../DihedralHessenberg/Dihedral/FirstLocalization.lean))
- `Dihedral.second_tensor_unit` ([DihedralHessenberg/Dihedral/FirstLocalization.lean](../DihedralHessenberg/Dihedral/FirstLocalization.lean))
- `Dihedral.fraction_localization` ([DihedralHessenberg/Dihedral/FractionLocalization.lean](../DihedralHessenberg/Dihedral/FractionLocalization.lean))
- `Dihedral.fraction_fixed_subfield` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fraction_fixed_galois` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fraction_fixed_isGalois` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fixedTensorEquiv` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fixedTensorEquiv_tmul` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.polynomialFixedEquiv` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.polynomialFixedEquiv_tmul` ([DihedralHessenberg/Dihedral/FixedFractionTensor.lean](../DihedralHessenberg/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fractionPolynomialEquiv` ([DihedralHessenberg/Dihedral/FractionLocalization.lean](../DihedralHessenberg/Dihedral/FractionLocalization.lean))
- `Dihedral.fractionPolynomialEquiv_tmul` ([DihedralHessenberg/Dihedral/FractionLocalization.lean](../DihedralHessenberg/Dihedral/FractionLocalization.lean))
- `Dihedral.tensorEvaluation_localized` ([DihedralHessenberg/Dihedral/BorelLocalization.lean](../DihedralHessenberg/Dihedral/BorelLocalization.lean))
- `DihedralSplines.borelHom_injective` ([DihedralHessenberg/Paper/BorelSplineMap.lean](../DihedralHessenberg/Paper/BorelSplineMap.lean))

### The invariants of $I\_2(n)$ and freeness over them (Section 3)

Status: **formalized**

Cited in the paper and proved here: with $u=x+iy$ and $v=x-iy$, the invariants $uv$ and $u^n+(-1)^nv^n$ generate $\mathbb{C}\[x,y\]^{I\_2(n)}$ freely, and $\mathbb{C}\[x,y\]$ is free of rank $2n$ over it.

- `Dihedral.Invariants.eq_generator_adjoin` ([DihedralHessenberg/Dihedral/InvariantGeneration.lean](../DihedralHessenberg/Dihedral/InvariantGeneration.lean))
- `Dihedral.basicInvariants_algebraicIndependent` ([DihedralHessenberg/Dihedral/BasicInvariantIndependence.lean](../DihedralHessenberg/Dihedral/BasicInvariantIndependence.lean))
- `Dihedral.nonempty_invariantPolynomialEquiv` ([DihedralHessenberg/Dihedral/InvariantPolynomialRing.lean](../DihedralHessenberg/Dihedral/InvariantPolynomialRing.lean))
- `Dihedral.Invariants.polynomial_free` ([DihedralHessenberg/Dihedral/InvariantFreeness.lean](../DihedralHessenberg/Dihedral/InvariantFreeness.lean))
- `Dihedral.Invariants.polynomial_finrank` ([DihedralHessenberg/Dihedral/InvariantFreeness.lean](../DihedralHessenberg/Dihedral/InvariantFreeness.lean))
- `Dihedral.coinvariantAlgebra_finite` ([DihedralHessenberg/Dihedral/CoinvariantFinite.lean](../DihedralHessenberg/Dihedral/CoinvariantFinite.lean))
- `Dihedral.quadraticInvariant_totalDegree` ([DihedralHessenberg/Dihedral/InvariantDegrees.lean](../DihedralHessenberg/Dihedral/InvariantDegrees.lean))
- `Dihedral.higherInvariant_totalDegree` ([DihedralHessenberg/Dihedral/InvariantDegrees.lean](../DihedralHessenberg/Dihedral/InvariantDegrees.lean))
- `Dihedral.Coinvariant.regular_iso` ([DihedralHessenberg/Dihedral/CoinvariantRegular.lean](../DihedralHessenberg/Dihedral/CoinvariantRegular.lean))

### Proposition 3.8 (`prop:left_schubert_rep`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.left_class_coeff` ([DihedralHessenberg/Paper/FullLeftClass.lean](../DihedralHessenberg/Paper/FullLeftClass.lean))
- `DihedralSplines.SchubertSpline.left_class_polynomial` ([DihedralHessenberg/Paper/FullLeftClass.lean](../DihedralHessenberg/Paper/FullLeftClass.lean))
- `DihedralSplines.SchubertSpline.left_class_length_sum` ([DihedralHessenberg/Paper/FullLeftClass.lean](../DihedralHessenberg/Paper/FullLeftClass.lean))
- `DihedralSplines.SchubertSpline.left_class_geometric` ([DihedralHessenberg/Paper/FullLeftClass.lean](../DihedralHessenberg/Paper/FullLeftClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.full_piece_iso` ([DihedralHessenberg/Paper/LeftFixedRepresentation.lean](../DihedralHessenberg/Paper/LeftFixedRepresentation.lean))

### Proposition 3.9 (`prop:right_schubert_rep`)

Status: **formalized**

The trace formula is checked element by element from the graded characters of the coinvariant algebra, instead of from a regular sequence of invariants.

- `DihedralSplines.SchubertSpline.right_piece_iso` ([DihedralHessenberg/Paper/FullRightClass.lean](../DihedralHessenberg/Paper/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.right_class_coinvariant` ([DihedralHessenberg/Paper/FullRightClass.lean](../DihedralHessenberg/Paper/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.right_class_coeff` ([DihedralHessenberg/Paper/FullRightClass.lean](../DihedralHessenberg/Paper/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.right_character_degree` ([DihedralHessenberg/Paper/FullRightClass.lean](../DihedralHessenberg/Paper/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.rightTrace` ([DihedralHessenberg/Paper/FullRightTrace.lean](../DihedralHessenberg/Paper/FullRightTrace.lean))
- `DihedralSplines.SchubertSpline.rightTrace_determinant` ([DihedralHessenberg/Paper/FullRightDeterminant.lean](../DihedralHessenberg/Paper/FullRightDeterminant.lean))
- `DihedralSplines.SchubertSpline.rightTrace_formula` ([DihedralHessenberg/Paper/FullRightDeterminant.lean](../DihedralHessenberg/Paper/FullRightDeterminant.lean))
- `DihedralSplines.SchubertSpline.rightTrace_one` ([DihedralHessenberg/Paper/FullRightDeterminant.lean](../DihedralHessenberg/Paper/FullRightDeterminant.lean))
- `DihedralSplines.SchubertSpline.polynomial_one_iso` ([DihedralHessenberg/Paper/FullRightDeterminant.lean](../DihedralHessenberg/Paper/FullRightDeterminant.lean))
- `Dihedral.vectorDenominator` ([DihedralHessenberg/Dihedral/VectorDenominator.lean](../DihedralHessenberg/Dihedral/VectorDenominator.lean))

### Remark 3.10

Status: **formalized**

- `DihedralSplines.SchubertSpline.full_piece_finrank_eq` ([DihedralHessenberg/Paper/FullQuotientComparison.lean](../DihedralHessenberg/Paper/FullQuotientComparison.lean))
- `DihedralSplines.SchubertSpline.full_piece_linearEquiv` ([DihedralHessenberg/Paper/FullQuotientComparison.lean](../DihedralHessenberg/Paper/FullQuotientComparison.lean))
- `DihedralSplines.SchubertSpline.full_piece_not_iso` ([DihedralHessenberg/Paper/FullQuotientComparison.lean](../DihedralHessenberg/Paper/FullQuotientComparison.lean))
- `DihedralSplines.borelEquiv_dot` ([DihedralHessenberg/Paper/BorelAction.lean](../DihedralHessenberg/Paper/BorelAction.lean))
- `DihedralSplines.borelEquiv_xLeft` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yLeft` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_xRight` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yRight` ([DihedralHessenberg/Paper/BorelCoordinates.lean](../DihedralHessenberg/Paper/BorelCoordinates.lean))
- `DihedralSplines.fullCoinvariantEquiv_mk` ([DihedralHessenberg/Paper/FullCoinvariantEquivalence.lean](../DihedralHessenberg/Paper/FullCoinvariantEquivalence.lean))
- `DihedralSplines.fullCoinvariantEquiv_equivariant` ([DihedralHessenberg/Paper/FullCoinvariantEquivalence.lean](../DihedralHessenberg/Paper/FullCoinvariantEquivalence.lean))
- `DihedralSplines.fullCoinvariantPieceEquiv` ([DihedralHessenberg/Paper/FullCoinvariantEquivalence.lean](../DihedralHessenberg/Paper/FullCoinvariantEquivalence.lean))
- `Dihedral.RootSubset.Left.coordinate_zero` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.coordinate_zero` ([DihedralHessenberg/Paper/PaperQuotient.lean](../DihedralHessenberg/Paper/PaperQuotient.lean))

### Remark 3.11

Status: **formalized**

Cited in the paper and proved here for $I\_2(n)$.

- `Dihedral.DoubleCoinvariant.relations_invariants` ([DihedralHessenberg/Dihedral/DoubleCoinvariant.lean](../DihedralHessenberg/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.tensorEquiv` ([DihedralHessenberg/Dihedral/DoubleCoinvariant.lean](../DihedralHessenberg/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.scalarEquiv` ([DihedralHessenberg/Dihedral/DoubleCoinvariant.lean](../DihedralHessenberg/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.tensorEquiv_first` ([DihedralHessenberg/Dihedral/DoubleCoinvariant.lean](../DihedralHessenberg/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.tensorEquiv_second` ([DihedralHessenberg/Dihedral/DoubleCoinvariant.lean](../DihedralHessenberg/Dihedral/DoubleCoinvariant.lean))
- `DihedralSplines.DoubleCoinvariant.localization` ([DihedralHessenberg/Paper/DoubleLocalization.lean](../DihedralHessenberg/Paper/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.schubert_basis` ([DihedralHessenberg/Paper/DoubleLocalization.lean](../DihedralHessenberg/Paper/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.localization_image` ([DihedralHessenberg/Paper/DoubleLocalization.lean](../DihedralHessenberg/Paper/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.localization_inverse` ([DihedralHessenberg/Paper/DoubleLocalization.lean](../DihedralHessenberg/Paper/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.root_form_real` ([DihedralHessenberg/Paper/DoubleLocalization.lean](../DihedralHessenberg/Paper/DoubleLocalization.lean))
- `Dihedral.polynomialAction_inverse_X` ([DihedralHessenberg/Dihedral/PolynomialPullback.lean](../DihedralHessenberg/Dihedral/PolynomialPullback.lean))
- `Dihedral.inverseCoordinate_eval` ([DihedralHessenberg/Dihedral/PolynomialPullback.lean](../DihedralHessenberg/Dihedral/PolynomialPullback.lean))

### Lemma 4.1 (`lem:generalized_divided_difference`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.dividedDifference` ([DihedralHessenberg/Paper/PaperDividedDifference.lean](../DihedralHessenberg/Paper/PaperDividedDifference.lean))
- `DihedralSplines.HessenbergIdeal.dividedDifference_mul` ([DihedralHessenberg/Paper/PaperDividedDifference.lean](../DihedralHessenberg/Paper/PaperDividedDifference.lean))
- `DihedralSplines.HessenbergIdeal.dividedDifference_unique` ([DihedralHessenberg/Paper/PaperDividedDifference.lean](../DihedralHessenberg/Paper/PaperDividedDifference.lean))

### Equation (14) (`eq:divided_difference`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.dividedDifference` ([DihedralHessenberg/Paper/PaperDividedDifference.lean](../DihedralHessenberg/Paper/PaperDividedDifference.lean))
- `DihedralSplines.HessenbergIdeal.dividedDifference_mul` ([DihedralHessenberg/Paper/PaperDividedDifference.lean](../DihedralHessenberg/Paper/PaperDividedDifference.lean))

### Lemma 4.2 (`lem:leftright_length`)

Status: **formalized**

- `Dihedral.PositiveRoot.ascent_length` ([DihedralHessenberg/Dihedral/RootReflectionLengthVectors.lean](../DihedralHessenberg/Dihedral/RootReflectionLengthVectors.lean))
- `Dihedral.PositiveRoot.descent_length` ([DihedralHessenberg/Dihedral/RootReflectionLengthVectors.lean](../DihedralHessenberg/Dihedral/RootReflectionLengthVectors.lean))

### Lemma 4.3 (`lem:simple_degree_changes`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.inversions_no_edge` ([DihedralHessenberg/Paper/HessenbergVectorDegree.lean](../DihedralHessenberg/Paper/HessenbergVectorDegree.lean))
- `DihedralSplines.HessenbergIdeal.length_edge` ([DihedralHessenberg/Paper/HessenbergVectorDegree.lean](../DihedralHessenberg/Paper/HessenbergVectorDegree.lean))
- `DihedralSplines.HessenbergIdeal.edge_range` ([DihedralHessenberg/Paper/HessenbergVectorDegree.lean](../DihedralHessenberg/Paper/HessenbergVectorDegree.lean))
- `DihedralSplines.HessenbergIdeal.length_full` ([DihedralHessenberg/Paper/HessenbergVectorDegree.lean](../DihedralHessenberg/Paper/HessenbergVectorDegree.lean))

### Corollary 4.4 (`cor:existence_upper_elts`)

Status: **formalized**

Stated for every $w\in I\_2(n)$.

- `DihedralSplines.FlowupSpline.spline` ([DihedralHessenberg/Paper/FlowupRecursion.lean](../DihedralHessenberg/Paper/FlowupRecursion.lean))
- `DihedralSplines.FlowupSpline.degree` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.support` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.diagonal` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Left.basis_apply` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.basis_apply` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.TriangularFamily.family_at` ([DihedralHessenberg/Paper/FlowupBasisPredicate.lean](../DihedralHessenberg/Paper/FlowupBasisPredicate.lean))

### Equation (15) (`eq:top_spline`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.topSpline` ([DihedralHessenberg/Paper/PaperTop.lean](../DihedralHessenberg/Paper/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_apply` ([DihedralHessenberg/Paper/PaperTop.lean](../DihedralHessenberg/Paper/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_nonzero` ([DihedralHessenberg/Paper/PaperTop.lean](../DihedralHessenberg/Paper/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_mem_piece` ([DihedralHessenberg/Paper/PaperTop.lean](../DihedralHessenberg/Paper/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_support` ([DihedralHessenberg/Paper/PaperTop.lean](../DihedralHessenberg/Paper/PaperTop.lean))

### Theorem 4.5 (`thm:flowup`)

Status: **formalized**

- `DihedralSplines.FlowupSpline.family` ([DihedralHessenberg/Paper/FlowupRecursion.lean](../DihedralHessenberg/Paper/FlowupRecursion.lean))
- `DihedralSplines.FlowupSpline.degree` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.support` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.diagonal` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Left.basis_apply` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.basis_apply` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.spline_one` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_top` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_low` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_high` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_no_edge` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))

### Example 4.6 (`ex:generators_exist`)

Status: **formalized**

- `DihedralSplines.Pentagon.generator` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.initial_formulas` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.operator_formulas` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.certificates` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.whole_degrees` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.family_vertex` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.bases` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.left_rank` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.right_rank` ([DihedralHessenberg/Paper/PentagonFamily.lean](../DihedralHessenberg/Paper/PentagonFamily.lean))
- `DihedralSplines.Pentagon.generator_eq_spline` ([DihedralHessenberg/Paper/PentagonRecursion.lean](../DihedralHessenberg/Paper/PentagonRecursion.lean))
- `DihedralSplines.Pentagon.edges` ([DihedralHessenberg/Paper/PentagonGraph.lean](../DihedralHessenberg/Paper/PentagonGraph.lean))
- `DihedralSplines.Pentagon.edge_labels` ([DihedralHessenberg/Paper/PentagonGraph.lean](../DihedralHessenberg/Paper/PentagonGraph.lean))
- `DihedralSplines.Pentagon.top_values` ([DihedralHessenberg/Paper/PentagonTop.lean](../DihedralHessenberg/Paper/PentagonTop.lean))

### Corollary 4.7 (`cor:rank_gf`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.lengthPolynomial_even` ([DihedralHessenberg/Paper/HessenbergLengthPolynomialClosed.lean](../DihedralHessenberg/Paper/HessenbergLengthPolynomialClosed.lean))
- `DihedralSplines.HessenbergIdeal.lengthPolynomial_odd` ([DihedralHessenberg/Paper/HessenbergLengthPolynomialClosed.lean](../DihedralHessenberg/Paper/HessenbergLengthPolynomialClosed.lean))
- `DihedralSplines.HessenbergIdeal.lengthPolynomial_reverse` ([DihedralHessenberg/Paper/LengthPolynomialSymmetry.lean](../DihedralHessenberg/Paper/LengthPolynomialSymmetry.lean))
- `DihedralSplines.FlowupSpline.Left.rank_eq` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.rank_eq` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.HessenbergIdeal.hilbertSeries_formula` ([DihedralHessenberg/Paper/FlowupHilbert.lean](../DihedralHessenberg/Paper/FlowupHilbert.lean))
- `DihedralSplines.HessenbergIdeal.coeff_piecewise` ([DihedralHessenberg/Paper/HessenbergLengthPolynomialClosed.lean](../DihedralHessenberg/Paper/HessenbergLengthPolynomialClosed.lean))

### Lemma 5.1 (`lem:regular`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.first_regular` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.second_regular` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.edge` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.boundary_card` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.eq_of_edges` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))

### Corollary 5.2 (`cor:rationally_smooth`)

Status: **formalized**

The uniqueness is deduced from the first part instead of by comparing values modulo $t\_\beta$.

- `DihedralSplines.HessenbergIdeal.Block.first` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.second` ([DihedralHessenberg/Paper/HessenbergBlock.lean](../DihedralHessenberg/Paper/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.localized` ([DihedralHessenberg/Paper/BlockLocalization.lean](../DihedralHessenberg/Paper/BlockLocalization.lean))
- `DihedralSplines.HessenbergIdeal.Block.localized_function` ([DihedralHessenberg/Paper/BlockLocalization.lean](../DihedralHessenberg/Paper/BlockLocalization.lean))
- `DihedralSplines.HessenbergIdeal.Block.normalized_unique` ([DihedralHessenberg/Paper/BlockLocalization.lean](../DihedralHessenberg/Paper/BlockLocalization.lean))

### Proposition 5.3 (`prop:flowup_explicit_setup`)

Status: **formalized**

- `DihedralSplines.FlowupSpline.block_shape` ([DihedralHessenberg/Paper/FlowupBlock.lean](../DihedralHessenberg/Paper/FlowupBlock.lean))
- `DihedralSplines.FlowupSpline.high_block` ([DihedralHessenberg/Paper/FlowupBlock.lean](../DihedralHessenberg/Paper/FlowupBlock.lean))
- `DihedralSplines.FlowupSpline.homogeneous` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.diagonal` ([DihedralHessenberg/Paper/FlowupBasis.lean](../DihedralHessenberg/Paper/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.spline_top` ([DihedralHessenberg/Paper/FlowupEquations.lean](../DihedralHessenberg/Paper/FlowupEquations.lean))

### Proposition 5.4 (`prop:linear_independence`)

Status: **formalized**

- `Dihedral.RootSubset.AlternatingBlocks` ([DihedralHessenberg/Paper/BlockIndependence.lean](../DihedralHessenberg/Paper/BlockIndependence.lean))
- `Dihedral.RootSubset.independent` ([DihedralHessenberg/Paper/BlockIndependence.lean](../DihedralHessenberg/Paper/BlockIndependence.lean))
- `Dihedral.RootSubset.boundaryFunction` ([DihedralHessenberg/Paper/BoundaryRelations.lean](../DihedralHessenberg/Paper/BoundaryRelations.lean))
- `Dihedral.length_rootReflection` ([DihedralHessenberg/Dihedral/AlternatingWords.lean](../DihedralHessenberg/Dihedral/AlternatingWords.lean))

### Corollary 5.5 (`cor:admissible_block_independence`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.AdmissibleBlocks` ([DihedralHessenberg/Paper/AdmissibleIndependence.lean](../DihedralHessenberg/Paper/AdmissibleIndependence.lean))
- `DihedralSplines.HessenbergIdeal.admissible_iff` ([DihedralHessenberg/Paper/AdmissibleIndependence.lean](../DihedralHessenberg/Paper/AdmissibleIndependence.lean))
- `DihedralSplines.HessenbergIdeal.admissible_independent` ([DihedralHessenberg/Paper/AdmissibleIndependence.lean](../DihedralHessenberg/Paper/AdmissibleIndependence.lean))

### Equation (16) (`eq:Ph_representation`)

Status: **formalized**

- `Dihedral.Frequency.partialSum` ([DihedralHessenberg/Dihedral/FrequencySum.lean](../DihedralHessenberg/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_zero` ([DihedralHessenberg/Dihedral/FrequencySum.lean](../DihedralHessenberg/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_succ` ([DihedralHessenberg/Dihedral/FrequencySum.lean](../DihedralHessenberg/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_terms_simple` ([DihedralHessenberg/Dihedral/FrequencySum.lean](../DihedralHessenberg/Dihedral/FrequencySum.lean))

### Remark 6.1

Status: **formalized**

- `Dihedral.Frequency.partialSum_finrank` ([DihedralHessenberg/Dihedral/FrequencySum.lean](../DihedralHessenberg/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_split_class` ([DihedralHessenberg/Dihedral/FrequencyTail.lean](../DihedralHessenberg/Dihedral/FrequencyTail.lean))
- `Dihedral.PositiveRoot.coset_odd_complement` ([DihedralHessenberg/Dihedral/FrequencyTail.lean](../DihedralHessenberg/Dihedral/FrequencyTail.lean))
- `Dihedral.PositiveRoot.coset_even_complement` ([DihedralHessenberg/Dihedral/FrequencyTail.lean](../DihedralHessenberg/Dihedral/FrequencyTail.lean))
- `Dihedral.PositiveRoot.coset_odd_iso` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_iso` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_odd_class` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_class` ([DihedralHessenberg/Dihedral/CosetDecomposition.lean](../DihedralHessenberg/Dihedral/CosetDecomposition.lean))

### Definition 6.2 (`def:H_dominant`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.IsDominant` ([DihedralHessenberg/Paper/HessenbergVectorDominant.lean](../DihedralHessenberg/Paper/HessenbergVectorDominant.lean))
- `DihedralSplines.HessenbergIdeal.isDominant_indexed` ([DihedralHessenberg/Paper/HessenbergVectorDominant.lean](../DihedralHessenberg/Paper/HessenbergVectorDominant.lean))

### Remark 6.3

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.dominant_even` ([DihedralHessenberg/Paper/DominanceEven.lean](../DihedralHessenberg/Paper/DominanceEven.lean))
- `DihedralSplines.HessenbergIdeal.dominant_odd_unique` ([DihedralHessenberg/Paper/DominanceOdd.lean](../DihedralHessenberg/Paper/DominanceOdd.lean))
- `DihedralSplines.HessenbergIdeal.odd_choices` ([DihedralHessenberg/Paper/OddIdealChoice.lean](../DihedralHessenberg/Paper/OddIdealChoice.lean))
- `DihedralSplines.HessenbergIdeal.odd_choice` ([DihedralHessenberg/Paper/OddIdealChoice.lean](../DihedralHessenberg/Paper/OddIdealChoice.lean))
- `DihedralSplines.HessenbergIdeal.odd_choice_whole` ([DihedralHessenberg/Paper/OddIdealWhole.lean](../DihedralHessenberg/Paper/OddIdealWhole.lean))
- `DihedralSplines.HessenbergIdeal.odd_choices_whole` ([DihedralHessenberg/Paper/OddIdealWhole.lean](../DihedralHessenberg/Paper/OddIdealWhole.lean))

### Theorem 6.4 (`thm:left_representation`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.graded_class` ([DihedralHessenberg/Paper/QuotientClass.lean](../DihedralHessenberg/Paper/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_even` ([DihedralHessenberg/Paper/LeftEvenClass.lean](../DihedralHessenberg/Paper/LeftEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_odd` ([DihedralHessenberg/Paper/LeftOddClass.lean](../DihedralHessenberg/Paper/LeftOddClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.class_palindromic` ([DihedralHessenberg/Paper/LeftClassPalindrome.lean](../DihedralHessenberg/Paper/LeftClassPalindrome.lean))

### Equation (17) (`eq:left_hessenberg_representation`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.graded_class` ([DihedralHessenberg/Paper/QuotientClass.lean](../DihedralHessenberg/Paper/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_even` ([DihedralHessenberg/Paper/LeftEvenClass.lean](../DihedralHessenberg/Paper/LeftEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_odd` ([DihedralHessenberg/Paper/LeftOddClass.lean](../DihedralHessenberg/Paper/LeftOddClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.class_palindromic` ([DihedralHessenberg/Paper/LeftClassPalindrome.lean](../DihedralHessenberg/Paper/LeftClassPalindrome.lean))

### Remark 6.5

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.dimension_rank` ([DihedralHessenberg/Paper/LeftDimensions.lean](../DihedralHessenberg/Paper/LeftDimensions.lean))
- `DihedralSplines.HessenbergIdeal.Left.dimension_length` ([DihedralHessenberg/Paper/LeftDimensions.lean](../DihedralHessenberg/Paper/LeftDimensions.lean))
- `DihedralSplines.HessenbergIdeal.Left.dimension_even` ([DihedralHessenberg/Paper/LeftDimensions.lean](../DihedralHessenberg/Paper/LeftDimensions.lean))
- `DihedralSplines.HessenbergIdeal.Left.dimension_odd` ([DihedralHessenberg/Paper/LeftDimensions.lean](../DihedralHessenberg/Paper/LeftDimensions.lean))
- `FiniteGroupCharacters.dimensionHom` ([DihedralHessenberg/FiniteGroupCharacters/RepresentationDimension.lean](../DihedralHessenberg/FiniteGroupCharacters/RepresentationDimension.lean))
- `FiniteGroupCharacters.dimensionHom_of` ([DihedralHessenberg/FiniteGroupCharacters/RepresentationDimension.lean](../DihedralHessenberg/FiniteGroupCharacters/RepresentationDimension.lean))
- `FiniteGroupCharacters.graded_dimension_coeff` ([DihedralHessenberg/FiniteGroupCharacters/RepresentationDimension.lean](../DihedralHessenberg/FiniteGroupCharacters/RepresentationDimension.lean))

### Example 6.6

Status: **formalized**

- `DihedralSplines.SchubertSpline.full_odd_class` ([DihedralHessenberg/Paper/FullLeftExtension.lean](../DihedralHessenberg/Paper/FullLeftExtension.lean))
- `DihedralSplines.SchubertSpline.full_even_half` ([DihedralHessenberg/Paper/FullLeftExtension.lean](../DihedralHessenberg/Paper/FullLeftExtension.lean))
- `DihedralSplines.SchubertSpline.left_class_geometric` ([DihedralHessenberg/Paper/FullLeftClass.lean](../DihedralHessenberg/Paper/FullLeftClass.lean))

### Example 6.7

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.two_simple_middle` ([DihedralHessenberg/Paper/TwoSimpleClass.lean](../DihedralHessenberg/Paper/TwoSimpleClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.two_simple_class` ([DihedralHessenberg/Paper/TwoSimpleClass.lean](../DihedralHessenberg/Paper/TwoSimpleClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.two_simple_odd` ([DihedralHessenberg/Paper/TwoSimpleClass.lean](../DihedralHessenberg/Paper/TwoSimpleClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.two_simple_even` ([DihedralHessenberg/Paper/TwoSimpleClass.lean](../DihedralHessenberg/Paper/TwoSimpleClass.lean))
- `Dihedral.Frequency.partialSum_after_one` ([DihedralHessenberg/Dihedral/FrequencyClass.lean](../DihedralHessenberg/Dihedral/FrequencyClass.lean))

### Example 6.8

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.withoutLast_class_even` ([DihedralHessenberg/Paper/MissingTopClass.lean](../DihedralHessenberg/Paper/MissingTopClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.withoutLast_class_odd` ([DihedralHessenberg/Paper/MissingTopClass.lean](../DihedralHessenberg/Paper/MissingTopClass.lean))

### Graded equivariant freeness (Section 6)

Status: **formalized**

- `Dihedral.RootSubset.Left.graded_section` ([DihedralHessenberg/Paper/SplineGradedSection.lean](../DihedralHessenberg/Paper/SplineGradedSection.lean))
- `DihedralSplines.HessenbergIdeal.Left.tensor_free` ([DihedralHessenberg/Paper/HessenbergTensorFree.lean](../DihedralHessenberg/Paper/HessenbergTensorFree.lean))
- `DihedralSplines.HessenbergIdeal.Left.degree_tensor_iso` ([DihedralHessenberg/Paper/HessenbergConvolution.lean](../DihedralHessenberg/Paper/HessenbergConvolution.lean))

### Equation (18) (`eq:left_equivariant_freeness`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.tensor_free` ([DihedralHessenberg/Paper/HessenbergTensorFree.lean](../DihedralHessenberg/Paper/HessenbergTensorFree.lean))

### Proposition 6.9 (`prop:left_quotient_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.pairingActionEquiv` ([DihedralHessenberg/Paper/QuotientDuality.lean](../DihedralHessenberg/Paper/QuotientDuality.lean))
- `DihedralSplines.HessenbergIdeal.Left.complementary_dual_iso` ([DihedralHessenberg/Paper/QuotientDuality.lean](../DihedralHessenberg/Paper/QuotientDuality.lean))
- `DihedralSplines.FlowupSpline.Left.pairingEquiv` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Left.multiplication_nondegenerate` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Left.pairingEquiv_apply` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Left.pairingEquiv_dot` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.HessenbergIdeal.Left.top_iso` ([DihedralHessenberg/Paper/TopRepresentation.lean](../DihedralHessenberg/Paper/TopRepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.complementary_dual` ([DihedralHessenberg/Paper/QuotientSymmetry.lean](../DihedralHessenberg/Paper/QuotientSymmetry.lean))

### Equation (19) (`eq:left_representation_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.complementary_dual` ([DihedralHessenberg/Paper/QuotientSymmetry.lean](../DihedralHessenberg/Paper/QuotientSymmetry.lean))
- `DihedralSplines.HessenbergIdeal.Left.top_iso` ([DihedralHessenberg/Paper/TopRepresentation.lean](../DihedralHessenberg/Paper/TopRepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.complementary_iso` ([DihedralHessenberg/Paper/QuotientSymmetry.lean](../DihedralHessenberg/Paper/QuotientSymmetry.lean))
- `Dihedral.self_dual` ([DihedralHessenberg/Dihedral/SelfDual.lean](../DihedralHessenberg/Dihedral/SelfDual.lean))

### The representations of $I\_2(n)$ are self-dual (Section 6)

Status: **formalized**

- `Dihedral.isConj_inv` ([DihedralHessenberg/Dihedral/SelfDualScope.lean](../DihedralHessenberg/Dihedral/SelfDualScope.lean))
- `Dihedral.irreducible_self_dual` ([DihedralHessenberg/Dihedral/SelfDualScope.lean](../DihedralHessenberg/Dihedral/SelfDualScope.lean))
- `Dihedral.self_dual` ([DihedralHessenberg/Dihedral/SelfDual.lean](../DihedralHessenberg/Dihedral/SelfDual.lean))

### Lemma 6.10 (`lem:trivial_left_subreps`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.trivialSource_embedding` ([DihedralHessenberg/Paper/TrivialLeftEmbedding.lean](../DihedralHessenberg/Paper/TrivialLeftEmbedding.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialSubpiece_iso` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialRange` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialRange_above` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation_class` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialInclusion` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialInclusion_injective` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivial_subrepresentation` ([DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean](../DihedralHessenberg/Paper/TrivialLeftSubrepresentation.lean))

### Equation (20) (`eq:left_middle_subtraction`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.middle_subtraction` ([DihedralHessenberg/Paper/LeftMiddleSubtraction.lean](../DihedralHessenberg/Paper/LeftMiddleSubtraction.lean))

### The decomposition of the polynomials of low degree (Section 6)

Status: **formalized**

- `Dihedral.polynomialPiece_frequency_iso` ([DihedralHessenberg/Dihedral/PolynomialDecomposition.lean](../DihedralHessenberg/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomialPiece_even_iso` ([DihedralHessenberg/Dihedral/PolynomialDecomposition.lean](../DihedralHessenberg/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomialPiece_odd_iso` ([DihedralHessenberg/Dihedral/PolynomialDecomposition.lean](../DihedralHessenberg/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomialPiece_frequency_simple` ([DihedralHessenberg/Dihedral/PolynomialDecomposition.lean](../DihedralHessenberg/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomial_weighted_class` ([DihedralHessenberg/Dihedral/PolynomialMultiplicity.lean](../DihedralHessenberg/Dihedral/PolynomialMultiplicity.lean))
- `DihedralSplines.HessenbergIdeal.Left.removed_weighted_class` ([DihedralHessenberg/Paper/HessenbergRemovedClass.lean](../DihedralHessenberg/Paper/HessenbergRemovedClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.removed_frequency_class` ([DihedralHessenberg/Paper/HessenbergRemovedClass.lean](../DihedralHessenberg/Paper/HessenbergRemovedClass.lean))

### Corollary 6.11 (`cor:not_permutation`)

Status: **formalized**

- `DihedralSplines.Pentagon.whole_class` ([DihedralHessenberg/Paper/PentagonRepresentation.lean](../DihedralHessenberg/Paper/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.whole_iso` ([DihedralHessenberg/Paper/PentagonRepresentation.lean](../DihedralHessenberg/Paper/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.rotation_character` ([DihedralHessenberg/Paper/PentagonRepresentation.lean](../DihedralHessenberg/Paper/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.rotation_not_nat` ([DihedralHessenberg/Paper/PentagonRepresentation.lean](../DihedralHessenberg/Paper/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.not_permutation` ([DihedralHessenberg/Paper/PentagonRepresentation.lean](../DihedralHessenberg/Paper/PentagonRepresentation.lean))

### Equation (21) (`eq:right_equivariant_freeness`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.orbit_tensor_free` ([DihedralHessenberg/Paper/OrbitTensorFree.lean](../DihedralHessenberg/Paper/OrbitTensorFree.lean))
- `Dihedral.RootSubset.Right.scalar_range` ([DihedralHessenberg/Paper/OrbitScalarRepresentation.lean](../DihedralHessenberg/Paper/OrbitScalarRepresentation.lean))
- `Dihedral.RootSubset.Right.scalarPiece_iso` ([DihedralHessenberg/Paper/OrbitScalarRepresentation.lean](../DihedralHessenberg/Paper/OrbitScalarRepresentation.lean))

### Proposition 7.1 (`prop:right_quotient_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.pairingActionEquiv` ([DihedralHessenberg/Paper/QuotientDuality.lean](../DihedralHessenberg/Paper/QuotientDuality.lean))
- `DihedralSplines.HessenbergIdeal.Right.complementary_dual_iso` ([DihedralHessenberg/Paper/QuotientDuality.lean](../DihedralHessenberg/Paper/QuotientDuality.lean))
- `DihedralSplines.FlowupSpline.Right.pairingEquiv` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Right.multiplication_nondegenerate` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Right.pairingEquiv_apply` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Right.pairingEquiv_dot` ([DihedralHessenberg/Paper/QuotientPairing.lean](../DihedralHessenberg/Paper/QuotientPairing.lean))
- `DihedralSplines.HessenbergIdeal.Right.top_iso` ([DihedralHessenberg/Paper/TopRepresentation.lean](../DihedralHessenberg/Paper/TopRepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.sign_complementary` ([DihedralHessenberg/Paper/QuotientSymmetry.lean](../DihedralHessenberg/Paper/QuotientSymmetry.lean))

### Equation (22) (`eq:right_representation_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.sign_complementary` ([DihedralHessenberg/Paper/QuotientSymmetry.lean](../DihedralHessenberg/Paper/QuotientSymmetry.lean))
- `DihedralSplines.HessenbergIdeal.Right.top_iso` ([DihedralHessenberg/Paper/TopRepresentation.lean](../DihedralHessenberg/Paper/TopRepresentation.lean))

### Lemma 7.2 (`lem:coinv_right_subreps`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.coRange` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coRange_above` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation_class` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coInclusion` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coInclusion_injective` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.co_subrepresentation` ([DihedralHessenberg/Paper/CoGradedSubrepresentation.lean](../DihedralHessenberg/Paper/CoGradedSubrepresentation.lean))

### Equation (23) (`eq:h_coinvariant`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.coClass` ([DihedralHessenberg/Paper/CoinvariantPattern.lean](../DihedralHessenberg/Paper/CoinvariantPattern.lean))
- `DihedralSplines.HessenbergIdeal.coClass_even` ([DihedralHessenberg/Paper/CoinvariantPattern.lean](../DihedralHessenberg/Paper/CoinvariantPattern.lean))
- `DihedralSplines.HessenbergIdeal.coClass_odd` ([DihedralHessenberg/Paper/CoinvariantPattern.lean](../DihedralHessenberg/Paper/CoinvariantPattern.lean))

### Theorem 7.3 (`thm:right_representation`)

Status: **formalized**

The piece of degree $h$ is computed directly, as in Theorem 6.4, instead of by comparison with $\mathrm{L}\_H$.

- `DihedralSplines.HessenbergIdeal.Right.graded_class` ([DihedralHessenberg/Paper/QuotientClass.lean](../DihedralHessenberg/Paper/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_even` ([DihedralHessenberg/Paper/RightEvenClass.lean](../DihedralHessenberg/Paper/RightEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_odd` ([DihedralHessenberg/Paper/RightOddClass.lean](../DihedralHessenberg/Paper/RightOddClass.lean))

### Equation (24) (`eq:right_hessenberg_representation`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.graded_class` ([DihedralHessenberg/Paper/QuotientClass.lean](../DihedralHessenberg/Paper/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_even` ([DihedralHessenberg/Paper/RightEvenClass.lean](../DihedralHessenberg/Paper/RightEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_odd` ([DihedralHessenberg/Paper/RightOddClass.lean](../DihedralHessenberg/Paper/RightOddClass.lean))
