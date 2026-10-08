# Statements of the paper and their Lean counterparts

Each statement of *Dot actions and Hessenberg spaces for dihedral groups* (Jonathan
Boretsky, Reuven Hodges, Nathan Lesnevich, Tyrrell McAllister, and Joseph Pappe, 2026),
with its status and the Lean declarations that formalize it, in the order of the paper.
The index covers every theorem, proposition, lemma, corollary, definition, displayed
equation, example and remark of the paper, and the mathematical statements made in its
prose and figures. Numbers are those printed in the paper, and labels are its LaTeX
labels; a statement without a number is given with its section. A short note follows a
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

- `DihedralSplines.HessenbergIdeal.poincare_hilbert` ([Schubert/DihedralSplines/FlowupHilbert.lean](../Schubert/DihedralSplines/FlowupHilbert.lean))
- `DihedralSplines.HessenbergIdeal.hilbertSeries_coeff` ([Schubert/DihedralSplines/FlowupHilbert.lean](../Schubert/DihedralSplines/FlowupHilbert.lean))
- `DihedralSplines.HessenbergIdeal.hilbertSeries_rank` ([Schubert/DihedralSplines/FlowupHilbert.lean](../Schubert/DihedralSplines/FlowupHilbert.lean))
- `DihedralSplines.FlowupSpline.Left.basis_apply` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.basis_apply` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))

### Theorem 2 (`intthm:basis`)

Status: **formalized**

- `DihedralSplines.FlowupSpline.basis_explicit` ([Schubert/DihedralSplines/FlowupExplicitBasis.lean](../Schubert/DihedralSplines/FlowupExplicitBasis.lean))
- `DihedralSplines.FlowupSpline.shape` ([Schubert/DihedralSplines/FlowupBoundary.lean](../Schubert/DihedralSplines/FlowupBoundary.lean))
- `DihedralSplines.BoundaryForm.formula` ([Schubert/DihedralSplines/BoundaryForm.lean](../Schubert/DihedralSplines/BoundaryForm.lean))
- `DihedralSplines.BoundaryForm.coefficient_ne` ([Schubert/DihedralSplines/BoundaryForm.lean](../Schubert/DihedralSplines/BoundaryForm.lean))

### Theorem 3 (`intthm:dotaction`)

Status: **formalized**

Here a graded representation is recorded as the series $\sum\_d\[V\_d\]\\,q^d$ over the representation ring of $I\_2(n)$.

- `DihedralSplines.HessenbergIdeal.Left.graded_class` ([Schubert/DihedralSplines/QuotientClass.lean](../Schubert/DihedralSplines/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_even` ([Schubert/DihedralSplines/LeftEvenClass.lean](../Schubert/DihedralSplines/LeftEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_odd` ([Schubert/DihedralSplines/LeftOddClass.lean](../Schubert/DihedralSplines/LeftOddClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.class_palindromic` ([Schubert/DihedralSplines/LeftClassPalindrome.lean](../Schubert/DihedralSplines/LeftClassPalindrome.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class` ([Schubert/DihedralSplines/QuotientClass.lean](../Schubert/DihedralSplines/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_even` ([Schubert/DihedralSplines/RightEvenClass.lean](../Schubert/DihedralSplines/RightEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_odd` ([Schubert/DihedralSplines/RightOddClass.lean](../Schubert/DihedralSplines/RightOddClass.lean))

### Example 2.1

Status: **formalized**

- `Dihedral.triangular_basis_images` ([Schubert/Dihedral/TriangularSubstitution.lean](../Schubert/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_first_variable` ([Schubert/Dihedral/TriangularSubstitution.lean](../Schubert/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_second_variable` ([Schubert/Dihedral/TriangularSubstitution.lean](../Schubert/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_monomial` ([Schubert/Dihedral/TriangularSubstitution.lean](../Schubert/Dihedral/TriangularSubstitution.lean))
- `Dihedral.triangular_sum` ([Schubert/Dihedral/TriangularSubstitution.lean](../Schubert/Dihedral/TriangularSubstitution.lean))

### Lemma 2.2 (`lem:reflect_divisible`)

Status: **formalized**

The proof uses $f\equiv s\_\alpha(f)$ modulo $t\_\alpha$ instead of the Nullstellensatz.

- `DihedralSplines.reflection_difference` ([Schubert/DihedralSplines/ReflectionLemma.lean](../Schubert/DihedralSplines/ReflectionLemma.lean))

### The dihedral group, its reduced words and its root system (Section 2.2)

Status: **formalized**

Here $I\_2(n)$ is Mathlib's `DihedralGroup n`, with $s\_1$ and $s\_2$ the reflections `sr 0` and `sr 1`.

- `Dihedral.presentationEquiv_firstSimpleReflection` ([Schubert/Dihedral/CoxeterSystem.lean](../Schubert/Dihedral/CoxeterSystem.lean))
- `Dihedral.presentationEquiv_secondSimpleReflection` ([Schubert/Dihedral/CoxeterSystem.lean](../Schubert/Dihedral/CoxeterSystem.lean))
- `Dihedral.reduced_word_alternating` ([Schubert/Dihedral/ReducedUnique.lean](../Schubert/Dihedral/ReducedUnique.lean))
- `Dihedral.unique_reduced_of_ne_longest` ([Schubert/Dihedral/ReducedUnique.lean](../Schubert/Dihedral/ReducedUnique.lean))
- `Dihedral.longest_reduced_words` ([Schubert/Dihedral/ReducedUnique.lean](../Schubert/Dihedral/ReducedUnique.lean))
- `Dihedral.vectorOperator_injective` ([Schubert/Dihedral/FaithfulRealization.lean](../Schubert/Dihedral/FaithfulRealization.lean))
- `Dihedral.PositiveRoot.realAction_reflection` ([Schubert/Dihedral/FaithfulRealization.lean](../Schubert/Dihedral/FaithfulRealization.lean))
- `Dihedral.positiveReflectionEquiv` ([Schubert/Dihedral/RootReflectionVectors.lean](../Schubert/Dihedral/RootReflectionVectors.lean))
- `Dihedral.numbered_even_reflection` ([Schubert/Dihedral/RootNumbering.lean](../Schubert/Dihedral/RootNumbering.lean))
- `Dihedral.numbered_odd_reflection` ([Schubert/Dihedral/RootNumbering.lean](../Schubert/Dihedral/RootNumbering.lean))
- `Dihedral.roots_neg_iff` ([Schubert/Dihedral/RootAxioms.lean](../Schubert/Dihedral/RootAxioms.lean))
- `Dihedral.roots_unit` ([Schubert/Dihedral/RootAxioms.lean](../Schubert/Dihedral/RootAxioms.lean))
- `Dihedral.roots_proportional` ([Schubert/Dihedral/RootAxioms.lean](../Schubert/Dihedral/RootAxioms.lean))
- `Dihedral.roots_reflection_mem` ([Schubert/Dihedral/RootAxioms.lean](../Schubert/Dihedral/RootAxioms.lean))
- `Dihedral.Separator.partition` ([Schubert/Dihedral/RootSeparator.lean](../Schubert/Dihedral/RootSeparator.lean))
- `Dihedral.Separator.reflectionEquiv` ([Schubert/Dihedral/RootSeparator.lean](../Schubert/Dihedral/RootSeparator.lean))
- `Dihedral.Separator.exists_chamber` ([Schubert/Dihedral/RootChambers.lean](../Schubert/Dihedral/RootChambers.lean))
- `Dihedral.Separator.unique_nearest_pair` ([Schubert/Dihedral/HyperplaneDistance.lean](../Schubert/Dihedral/HyperplaneDistance.lean))
- `Dihedral.Separator.foot_pairing` ([Schubert/Dihedral/HyperplaneDistance.lean](../Schubert/Dihedral/HyperplaneDistance.lean))
- `Dihedral.Separator.distance_min` ([Schubert/Dihedral/HyperplaneDistance.lean](../Schubert/Dihedral/HyperplaneDistance.lean))
- `Dihedral.Separator.Frame.nearest_pair` ([Schubert/Dihedral/RootFrame.lean](../Schubert/Dihedral/RootFrame.lean))
- `Dihedral.Separator.Frame.generate` ([Schubert/Dihedral/RootFrame.lean](../Schubert/Dihedral/RootFrame.lean))
- `Dihedral.Separator.singleton_ne_top` ([Schubert/Dihedral/RootFrame.lean](../Schubert/Dihedral/RootFrame.lean))
- `Dihedral.Separator.disjoint` ([Schubert/Dihedral/RootSeparator.lean](../Schubert/Dihedral/RootSeparator.lean))
- `Dihedral.bruhatLE_iff_exists_sublist` ([Schubert/Dihedral/CoxeterSystem.lean](../Schubert/Dihedral/CoxeterSystem.lean))

### Example 2.3 (`ex:reflection`)

Status: **formalized**

- `Dihedral.polygonVertices` ([Schubert/Dihedral/PolygonVertices.lean](../Schubert/Dihedral/PolygonVertices.lean))
- `Dihedral.polygon_small_offsets` ([Schubert/Dihedral/PolygonVertices.lean](../Schubert/Dihedral/PolygonVertices.lean))
- `Dihedral.polygon_scaled_angles` ([Schubert/Dihedral/PolygonVertices.lean](../Schubert/Dihedral/PolygonVertices.lean))
- `Dihedral.polygon_action_mem` ([Schubert/Dihedral/PolygonVertices.lean](../Schubert/Dihedral/PolygonVertices.lean))
- `Dihedral.PositiveRoot.axis_drawn` ([Schubert/Dihedral/PolygonAxes.lean](../Schubert/Dihedral/PolygonAxes.lean))
- `Dihedral.drawn_axis_fixed` ([Schubert/Dihedral/PolygonAxes.lean](../Schubert/Dihedral/PolygonAxes.lean))
- `Dihedral.positiveRoots_unit_angles` ([Schubert/Dihedral/UnitDirections.lean](../Schubert/Dihedral/UnitDirections.lean))
- `Dihedral.PositiveRoot.reflection_axis` ([Schubert/Dihedral/UnitDirections.lean](../Schubert/Dihedral/UnitDirections.lean))
- `Dihedral.PositiveRoot.fixed_iff_axis` ([Schubert/Dihedral/UnitDirections.lean](../Schubert/Dihedral/UnitDirections.lean))

### Equation (1) (`eq:left_inversion_set`)

Status: **formalized**

- `Dihedral.leftInversionSet` ([Schubert/Dihedral/RootInversionSets.lean](../Schubert/Dihedral/RootInversionSets.lean))
- `Dihedral.leftInversionSet_descent` ([Schubert/Dihedral/RootInversionDescent.lean](../Schubert/Dihedral/RootInversionDescent.lean))
- `Dihedral.PositiveRoot.left_descent` ([Schubert/Dihedral/RootInversionDescent.lean](../Schubert/Dihedral/RootInversionDescent.lean))

### Equation (2) (`eq:right_inversion_set`)

Status: **formalized**

- `Dihedral.rightInversionSet` ([Schubert/Dihedral/RootInversionSets.lean](../Schubert/Dihedral/RootInversionSets.lean))
- `Dihedral.rightInversionSet_descent` ([Schubert/Dihedral/RootInversionDescent.lean](../Schubert/Dihedral/RootInversionDescent.lean))
- `Dihedral.PositiveRoot.right_descent` ([Schubert/Dihedral/RootInversionDescent.lean](../Schubert/Dihedral/RootInversionDescent.lean))

### Lemma 2.4 (`lem:rank_two_bruhat_facts`)

Status: **formalized**

The equality $\lvert N\_L(w)\rvert=\ell(w)$ is proved from the inversion sequence of a reduced word instead of a gallery, and part (2) is stated for every $u$.

- `Dihedral.unique_root_descent` ([Schubert/Dihedral/RankTwoRootVectors.lean](../Schubert/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.unique_root_ascent` ([Schubert/Dihedral/RankTwoRootVectors.lean](../Schubert/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.length_eq_longest` ([Schubert/Dihedral/RankTwoRootVectors.lean](../Schubert/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.bruhatLE_iff_eq_or_length_lt` ([Schubert/Dihedral/RankTwoBruhat.lean](../Schubert/Dihedral/RankTwoBruhat.lean))
- `Dihedral.ncard_leftInversionSet` ([Schubert/Dihedral/RootSubsetCard.lean](../Schubert/Dihedral/RootSubsetCard.lean))
- `Dihedral.PositiveRoot.left_ascent` ([Schubert/Dihedral/RankTwoRootVectors.lean](../Schubert/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.PositiveRoot.left_ascent_disjoint` ([Schubert/Dihedral/RankTwoRootVectors.lean](../Schubert/Dihedral/RankTwoRootVectors.lean))
- `Dihedral.PositiveRoot.right_ascent` ([Schubert/Dihedral/RankTwoRootVectors.lean](../Schubert/Dihedral/RankTwoRootVectors.lean))

### The irreducible representations of $I\_2(n)$ and the coset representations $C\_\gamma$ (Section 2.3)

Status: **formalized**

Cited in the paper and proved here: the listed representations are irreducible, pairwise nonisomorphic, and as many as the conjugacy classes.

- `Dihedral.irreducible_dimension` ([Schubert/Dihedral/RepresentationClassification.lean](../Schubert/Dihedral/RepresentationClassification.lean))
- `Dihedral.irrep_counts_odd` ([Schubert/Dihedral/IrrepDimensionCounts.lean](../Schubert/Dihedral/IrrepDimensionCounts.lean))
- `Dihedral.irrep_counts_even` ([Schubert/Dihedral/IrrepDimensionCounts.lean](../Schubert/Dihedral/IrrepDimensionCounts.lean))
- `Dihedral.scalarFDRep` ([Schubert/Dihedral/IrreducibleFamily.lean](../Schubert/Dihedral/IrreducibleFamily.lean))
- `Dihedral.signCharacter_length` ([Schubert/Dihedral/ScalarCharacterFacts.lean](../Schubert/Dihedral/ScalarCharacterFacts.lean))
- `Dihedral.signFDRep_character` ([Schubert/Dihedral/ScalarCharacters.lean](../Schubert/Dihedral/ScalarCharacters.lean))
- `Dihedral.evenScalarCharacter_rotation` ([Schubert/Dihedral/ScalarCharacters.lean](../Schubert/Dihedral/ScalarCharacters.lean))
- `Dihedral.evenScalarCharacter_s1` ([Schubert/Dihedral/ScalarCharacters.lean](../Schubert/Dihedral/ScalarCharacters.lean))
- `Dihedral.frequencyFDRep_finrank` ([Schubert/Dihedral/FrequencyRepresentation.lean](../Schubert/Dihedral/FrequencyRepresentation.lean))
- `Dihedral.frequencyFDRep_simple_of_lower_half` ([Schubert/Dihedral/FrequencyDistinction.lean](../Schubert/Dihedral/FrequencyDistinction.lean))
- `Dihedral.Frequency.character_zpow` ([Schubert/Dihedral/FrequencyPowerCharacter.lean](../Schubert/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.Frequency.character_zpow_s1` ([Schubert/Dihedral/FrequencyPowerCharacter.lean](../Schubert/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.frequency_one` ([Schubert/Dihedral/FrequencyPowerCharacter.lean](../Schubert/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.frequency_one_iso` ([Schubert/Dihedral/FrequencyPowerCharacter.lean](../Schubert/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.irreducible_classification` ([Schubert/Dihedral/RepresentationClassification.lean](../Schubert/Dihedral/RepresentationClassification.lean))
- `Dihedral.irrepFDRep_iso_iff_eq` ([Schubert/Dihedral/IrreducibleClassification.lean](../Schubert/Dihedral/IrreducibleClassification.lean))
- `Dihedral.PositiveRoot.scalarCharacter_reflection` ([Schubert/Dihedral/RootScalarCharacter.lean](../Schubert/Dihedral/RootScalarCharacter.lean))
- `Dihedral.PositiveRoot.scalarCharacter_unique` ([Schubert/Dihedral/RootScalarCharacter.lean](../Schubert/Dihedral/RootScalarCharacter.lean))
- `Dihedral.PositiveRoot.cosetFDRep` ([Schubert/Dihedral/CosetFDRep.lean](../Schubert/Dihedral/CosetFDRep.lean))
- `Dihedral.PositiveRoot.coset_odd_iso` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_iso` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))

### Equation (3) (`eq:reflection_coset_decomposition`)

Status: **formalized**

Cited in the paper and proved here, by comparing characters.

- `Dihedral.PositiveRoot.cosetFDRep` ([Schubert/Dihedral/CosetFDRep.lean](../Schubert/Dihedral/CosetFDRep.lean))
- `Dihedral.PositiveRoot.coset_odd_iso` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_iso` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_odd_class` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_class` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.scalarCharacter_reflection` ([Schubert/Dihedral/RootScalarCharacter.lean](../Schubert/Dihedral/RootScalarCharacter.lean))
- `Dihedral.PositiveRoot.scalarCharacter_unique` ([Schubert/Dihedral/RootScalarCharacter.lean](../Schubert/Dihedral/RootScalarCharacter.lean))

### Example 2.5

Status: **formalized**

- `DihedralSplines.square_first_matrix` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_second_matrix` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_longest` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_third_reflection` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_simple_sign` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_third_sign` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_simple_trivial` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `DihedralSplines.square_trivial_character` ([Schubert/DihedralSplines/SquareAction.lean](../Schubert/DihedralSplines/SquareAction.lean))
- `Dihedral.frequency_one` ([Schubert/Dihedral/FrequencyPowerCharacter.lean](../Schubert/Dihedral/FrequencyPowerCharacter.lean))
- `Dihedral.signCharacter_length` ([Schubert/Dihedral/ScalarCharacterFacts.lean](../Schubert/Dihedral/ScalarCharacterFacts.lean))

### Definition 2.6 (`def:root_poset`)

Status: **formalized**

- `DihedralSplines.RootOrder` ([Schubert/DihedralSplines/RootOrder.lean](../Schubert/DihedralSplines/RootOrder.lean))
- `DihedralSplines.rootOrder` ([Schubert/DihedralSplines/RootOrder.lean](../Schubert/DihedralSplines/RootOrder.lean))
- `DihedralSplines.rootOrder_refl` ([Schubert/DihedralSplines/RootOrder.lean](../Schubert/DihedralSplines/RootOrder.lean))
- `DihedralSplines.rootOrder_trans` ([Schubert/DihedralSplines/RootOrder.lean](../Schubert/DihedralSplines/RootOrder.lean))
- `DihedralSplines.rootOrder_antisymm` ([Schubert/DihedralSplines/RootOrder.lean](../Schubert/DihedralSplines/RootOrder.lean))

### The Hasse diagrams of the root poset (Section 2.4)

Status: **formalized**

- `DihedralSplines.rootOrder_layers` ([Schubert/DihedralSplines/HessenbergVectorClassification.lean](../Schubert/DihedralSplines/HessenbergVectorClassification.lean))
- `DihedralSplines.rootOrder_lt_iff` ([Schubert/DihedralSplines/RootOrderCovers.lean](../Schubert/DihedralSplines/RootOrderCovers.lean))
- `DihedralSplines.rootOrder_covBy_iff` ([Schubert/DihedralSplines/RootOrderCovers.lean](../Schubert/DihedralSplines/RootOrderCovers.lean))
- `DihedralSplines.layer_card` ([Schubert/DihedralSplines/RootOrderCovers.lean](../Schubert/DihedralSplines/RootOrderCovers.lean))

### Remark 2.7

Status: **formalized**

- `DihedralSplines.rootOrder_length` ([Schubert/DihedralSplines/RootVectorComparison.lean](../Schubert/DihedralSplines/RootVectorComparison.lean))
- `DihedralSplines.rootOrder_bruhat` ([Schubert/DihedralSplines/RootVectorComparison.lean](../Schubert/DihedralSplines/RootVectorComparison.lean))

### The list of Hessenberg spaces (Section 2.4)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal` ([Schubert/DihedralSplines/HessenbergObjects.lean](../Schubert/DihedralSplines/HessenbergObjects.lean))
- `DihedralSplines.HessenbergIdeal.classification` ([Schubert/DihedralSplines/HessenbergVectorClassification.lean](../Schubert/DihedralSplines/HessenbergVectorClassification.lean))
- `DihedralSplines.HessenbergIdeal.exists_initial` ([Schubert/DihedralSplines/HessenbergVectorClassification.lean](../Schubert/DihedralSplines/HessenbergVectorClassification.lean))
- `DihedralSplines.HessenbergIdeal.exists_other` ([Schubert/DihedralSplines/HessenbergVectorClassification.lean](../Schubert/DihedralSplines/HessenbergVectorClassification.lean))
- `DihedralSplines.HessenbergIdeal.natCard` ([Schubert/DihedralSplines/HessenbergVectorClassification.lean](../Schubert/DihedralSplines/HessenbergVectorClassification.lean))

### Remark 2.8

Status: **formalized**

- `Dihedral.PositiveRoot.depth` ([Schubert/Dihedral/RootDepth.lean](../Schubert/Dihedral/RootDepth.lean))
- `Dihedral.DepthStep` ([Schubert/Dihedral/RootDepthOrder.lean](../Schubert/Dihedral/RootDepthOrder.lean))
- `Dihedral.PositiveRoot.depth_layer` ([Schubert/Dihedral/RootDepthLayers.lean](../Schubert/Dihedral/RootDepthLayers.lean))
- `Dihedral.depth_step_iff` ([Schubert/Dihedral/RootDepthChains.lean](../Schubert/Dihedral/RootDepthChains.lean))
- `Dihedral.depth_order_iff` ([Schubert/Dihedral/RootDepthChains.lean](../Schubert/Dihedral/RootDepthChains.lean))
- `Dihedral.Separator.label_ideal_signs` ([Schubert/DihedralSplines/ChamberSplines.lean](../Schubert/DihedralSplines/ChamberSplines.lean))
- `Dihedral.Separator.spline_signs` ([Schubert/DihedralSplines/ChamberSplines.lean](../Schubert/DihedralSplines/ChamberSplines.lean))
- `Dihedral.Separator.spline_set_signs` ([Schubert/DihedralSplines/ChamberSplines.lean](../Schubert/DihedralSplines/ChamberSplines.lean))
- `DihedralSplines.six_depth_counterexample` ([Schubert/DihedralSplines/HexagonDepthCounterexample.lean](../Schubert/DihedralSplines/HexagonDepthCounterexample.lean))
- `DihedralSplines.six_three_root_ideal` ([Schubert/DihedralSplines/SixRootIdeal.lean](../Schubert/DihedralSplines/SixRootIdeal.lean))

### Remark 2.9

Status: **formalized**

Here $B\_2$, $C\_2$ and $G\_2$ are obtained from the unit roots of $I\_2(4)$ and $I\_2(6)$ by rescaling one orbit of roots.

- `DihedralSplines.four_orders_differ` ([Schubert/DihedralSplines/CrystallographicComparison.lean](../Schubert/DihedralSplines/CrystallographicComparison.lean))
- `DihedralSplines.four_lower_ideals` ([Schubert/DihedralSplines/CrystallographicComparison.lean](../Schubert/DihedralSplines/CrystallographicComparison.lean))
- `DihedralSplines.six_unit_not_g2` ([Schubert/DihedralSplines/CrystallographicComparison.lean](../Schubert/DihedralSplines/CrystallographicComparison.lean))
- `DihedralSplines.six_g2_not_unit` ([Schubert/DihedralSplines/CrystallographicComparison.lean](../Schubert/DihedralSplines/CrystallographicComparison.lean))
- `Dihedral.RootLattice.a2_order` ([Schubert/DihedralSplines/CrystallographicComparison.lean](../Schubert/DihedralSplines/CrystallographicComparison.lean))
- `Dihedral.RootLattice.a2_lower_iff` ([Schubert/DihedralSplines/CrystallographicComparison.lean](../Schubert/DihedralSplines/CrystallographicComparison.lean))
- `Dihedral.RootLattice.a2_crystallographic` ([Schubert/Dihedral/Crystallographic.lean](../Schubert/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.b2_crystallographic` ([Schubert/Dihedral/Crystallographic.lean](../Schubert/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.c2_crystallographic` ([Schubert/Dihedral/Crystallographic.lean](../Schubert/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.g2_crystallographic` ([Schubert/Dihedral/Crystallographic.lean](../Schubert/Dihedral/Crystallographic.lean))
- `Dihedral.RootLattice.a2GroupEquiv` ([Schubert/Dihedral/RadialReflectionGroup.lean](../Schubert/Dihedral/RadialReflectionGroup.lean))
- `Dihedral.RootLattice.b2GroupEquiv` ([Schubert/Dihedral/RadialReflectionGroup.lean](../Schubert/Dihedral/RadialReflectionGroup.lean))
- `Dihedral.RootLattice.c2GroupEquiv` ([Schubert/Dihedral/RadialReflectionGroup.lean](../Schubert/Dihedral/RadialReflectionGroup.lean))
- `Dihedral.RootLattice.g2GroupEquiv` ([Schubert/Dihedral/RadialReflectionGroup.lean](../Schubert/Dihedral/RadialReflectionGroup.lean))

### Definition 2.10 (`def:inversion_set`)

Status: **formalized**

- `Dihedral.RootSubset.inversions` ([Schubert/Dihedral/RootInversionSets.lean](../Schubert/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.length` ([Schubert/Dihedral/RootInversionSets.lean](../Schubert/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.mem_inversions` ([Schubert/Dihedral/RootInversionSets.lean](../Schubert/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.inversions_finite` ([Schubert/Dihedral/RootInversionSets.lean](../Schubert/Dihedral/RootInversionSets.lean))
- `Dihedral.RootSubset.inversions_bijOn` ([Schubert/Dihedral/RootSubsetImages.lean](../Schubert/Dihedral/RootSubsetImages.lean))
- `Dihedral.rightInversionSet_descent` ([Schubert/Dihedral/RootInversionDescent.lean](../Schubert/Dihedral/RootInversionDescent.lean))
- `Dihedral.PositiveRoot.right_descent` ([Schubert/Dihedral/RootInversionDescent.lean](../Schubert/Dihedral/RootInversionDescent.lean))

### The labeled Cayley graph (Section 2.4)

Status: **formalized**

- `Dihedral.RootSubset.edges` ([Schubert/DihedralSplines/PaperGraph.lean](../Schubert/DihedralSplines/PaperGraph.lean))
- `Dihedral.RootSubset.mem_edges` ([Schubert/DihedralSplines/PaperGraph.lean](../Schubert/DihedralSplines/PaperGraph.lean))
- `Dihedral.RootSubset.edgeLabel_edge` ([Schubert/DihedralSplines/PaperGraph.lean](../Schubert/DihedralSplines/PaperGraph.lean))
- `Dihedral.RootSubset.edgeLabel_eq_action` ([Schubert/DihedralSplines/PaperGraph.lean](../Schubert/DihedralSplines/PaperGraph.lean))
- `Dihedral.RootSubset.edgeEquiv` ([Schubert/DihedralSplines/PaperGraph.lean](../Schubert/DihedralSplines/PaperGraph.lean))
- `Dihedral.RootSubset.label_reverse` ([Schubert/DihedralSplines/PaperGraph.lean](../Schubert/DihedralSplines/PaperGraph.lean))

### Example 2.11 (`ex:cayley`)

Status: **formalized**

- `DihedralSplines.Triangle.selected` ([Schubert/DihedralSplines/TriangleCayley.lean](../Schubert/DihedralSplines/TriangleCayley.lean))
- `DihedralSplines.Triangle.pairs` ([Schubert/DihedralSplines/TriangleCayley.lean](../Schubert/DihedralSplines/TriangleCayley.lean))
- `DihedralSplines.Triangle.edges` ([Schubert/DihedralSplines/TriangleCayley.lean](../Schubert/DihedralSplines/TriangleCayley.lean))
- `DihedralSplines.Triangle.edge_labels` ([Schubert/DihedralSplines/TriangleCayley.lean](../Schubert/DihedralSplines/TriangleCayley.lean))
- `DihedralSplines.Triangle.inversions` ([Schubert/DihedralSplines/TriangleCayley.lean](../Schubert/DihedralSplines/TriangleCayley.lean))
- `DihedralSplines.Square.selected` ([Schubert/DihedralSplines/SquareCayley.lean](../Schubert/DihedralSplines/SquareCayley.lean))
- `DihedralSplines.Square.pairs` ([Schubert/DihedralSplines/SquareCayley.lean](../Schubert/DihedralSplines/SquareCayley.lean))
- `DihedralSplines.Square.edges` ([Schubert/DihedralSplines/SquareCayley.lean](../Schubert/DihedralSplines/SquareCayley.lean))
- `DihedralSplines.Square.edge_labels` ([Schubert/DihedralSplines/SquareCayley.lean](../Schubert/DihedralSplines/SquareCayley.lean))

### The acyclic orientation of the Cayley graph and the order $\prec\_H$ (Section 2.4)

Status: **formalized**

- `Dihedral.RootSubset.orientedEdges` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.reachable` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.acyclic` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.incoming_card` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.partialOrder` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.reachable_strict_iff` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.partialOrder_lt` ([Schubert/DihedralSplines/OrientedGraph.lean](../Schubert/DihedralSplines/OrientedGraph.lean))
- `Dihedral.RootSubset.edge_length_ne` ([Schubert/DihedralSplines/OrientedEdgeLengths.lean](../Schubert/DihedralSplines/OrientedEdgeLengths.lean))
- `Dihedral.RootSubset.oriented_xor_reverse` ([Schubert/DihedralSplines/OrientedEdgeLengths.lean](../Schubert/DihedralSplines/OrientedEdgeLengths.lean))

### Example 2.12

Status: **formalized**

- `Dihedral.RootSubset.simple_reachable` ([Schubert/DihedralSplines/SimpleOrientedGraph.lean](../Schubert/DihedralSplines/SimpleOrientedGraph.lean))
- `Dihedral.rightWeakLE_prefix` ([Schubert/Dihedral/RightWeak.lean](../Schubert/Dihedral/RightWeak.lean))
- `Dihedral.RootSubset.full_reachable` ([Schubert/DihedralSplines/FullOrientedGraph.lean](../Schubert/DihedralSplines/FullOrientedGraph.lean))

### Example 2.13

Status: **formalized**

- `DihedralSplines.pentagon_oriented` ([Schubert/DihedralSplines/PentagonOrientation.lean](../Schubert/DihedralSplines/PentagonOrientation.lean))
- `DihedralSplines.pentagon_cover_iff` ([Schubert/DihedralSplines/PentagonHasse.lean](../Schubert/DihedralSplines/PentagonHasse.lean))
- `DihedralSplines.pentagon_hasse` ([Schubert/DihedralSplines/PentagonHasse.lean](../Schubert/DihedralSplines/PentagonHasse.lean))

### The module of splines (Section 2.5)

Status: **formalized**

- `Dihedral.RootSubset.IsSpline` ([Schubert/DihedralSplines/PaperSpline.lean](../Schubert/DihedralSplines/PaperSpline.lean))
- `Dihedral.RootSubset.splineAlgebra` ([Schubert/DihedralSplines/PaperSpline.lean](../Schubert/DihedralSplines/PaperSpline.lean))
- `Dihedral.RootSubset.mem_splineAlgebra` ([Schubert/DihedralSplines/PaperSpline.lean](../Schubert/DihedralSplines/PaperSpline.lean))
- `DihedralSplines.HessenbergIdeal.splineEquiv_apply` ([Schubert/DihedralSplines/PaperIdeal.lean](../Schubert/DihedralSplines/PaperIdeal.lean))

### The spline diagrams for $I\_2(3)$ (Section 2.5)

Status: **formalized**

- `DihedralSplines.TriangleIllustrations.value` ([Schubert/DihedralSplines/TriangleSplines.lean](../Schubert/DihedralSplines/TriangleSplines.lean))
- `DihedralSplines.TriangleIllustrations.word_values` ([Schubert/DihedralSplines/TriangleSplines.lean](../Schubert/DihedralSplines/TriangleSplines.lean))
- `DihedralSplines.TriangleIllustrations.rows` ([Schubert/DihedralSplines/TriangleSplines.lean](../Schubert/DihedralSplines/TriangleSplines.lean))
- `DihedralSplines.TriangleIllustrations.isSpline` ([Schubert/DihedralSplines/TriangleSplines.lean](../Schubert/DihedralSplines/TriangleSplines.lean))

### The spline diagrams for $I\_2(4)$ (Section 2.5)

Status: **formalized**

- `DihedralSplines.SquareIllustrations.value` ([Schubert/DihedralSplines/SquareSplines.lean](../Schubert/DihedralSplines/SquareSplines.lean))
- `DihedralSplines.SquareIllustrations.word_values` ([Schubert/DihedralSplines/SquareSplines.lean](../Schubert/DihedralSplines/SquareSplines.lean))
- `DihedralSplines.SquareIllustrations.rows` ([Schubert/DihedralSplines/SquareSplines.lean](../Schubert/DihedralSplines/SquareSplines.lean))
- `DihedralSplines.SquareIllustrations.isSpline` ([Schubert/DihedralSplines/SquareSplines.lean](../Schubert/DihedralSplines/SquareSplines.lean))

### Edge labels and conjugate reflections (Section 2.5)

Status: **formalized**

- `Dihedral.RootSubset.edgeLabel_eq_form_iff` ([Schubert/DihedralSplines/EdgeLabelReflection.lean](../Schubert/DihedralSplines/EdgeLabelReflection.lean))

### Lemma 2.14

Status: **formalized**

- `Dihedral.RootSubset.splineAlgebra` ([Schubert/DihedralSplines/PaperSpline.lean](../Schubert/DihedralSplines/PaperSpline.lean))
- `Dihedral.RootSubset.mem_splineAlgebra` ([Schubert/DihedralSplines/PaperSpline.lean](../Schubert/DihedralSplines/PaperSpline.lean))

### Lemma 2.15

Status: **formalized**

- `Dihedral.RootSubset.piece` ([Schubert/DihedralSplines/PaperGrading.lean](../Schubert/DihedralSplines/PaperGrading.lean))
- `Dihedral.RootSubset.mem_piece` ([Schubert/DihedralSplines/PaperGrading.lean](../Schubert/DihedralSplines/PaperGrading.lean))
- `Dihedral.RootSubset.component_apply` ([Schubert/DihedralSplines/PaperGrading.lean](../Schubert/DihedralSplines/PaperGrading.lean))
- `Dihedral.RootSubset.piece_isInternal` ([Schubert/DihedralSplines/PaperGrading.lean](../Schubert/DihedralSplines/PaperGrading.lean))
- `Dihedral.RootSubset.gradedAlgebra` ([Schubert/DihedralSplines/PaperGrading.lean](../Schubert/DihedralSplines/PaperGrading.lean))

### Constant and orbit splines and the two module structures (Section 2.5)

Status: **formalized**

- `Dihedral.RootSubset.constantHom` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.orbitHom` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.constantHom_injective` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.orbitHom_injective` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.one_apply` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.xLeft_apply` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.yLeft_apply` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.xRight_apply` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.yRight_apply` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.constantHom_mem_piece` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.orbitHom_mem_piece` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.Left.smul_mem_piece` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.Right.smul_mem_piece` ([Schubert/DihedralSplines/PaperCoordinates.lean](../Schubert/DihedralSplines/PaperCoordinates.lean))
- `Dihedral.RootSubset.Left.module_finite` ([Schubert/DihedralSplines/PaperScalarTransport.lean](../Schubert/DihedralSplines/PaperScalarTransport.lean))
- `Dihedral.RootSubset.Right.module_finite` ([Schubert/DihedralSplines/PaperScalarTransport.lean](../Schubert/DihedralSplines/PaperScalarTransport.lean))
- `Dihedral.RootSubset.Left.homogeneous_generators` ([Schubert/DihedralSplines/PaperModuleFinite.lean](../Schubert/DihedralSplines/PaperModuleFinite.lean))
- `Dihedral.RootSubset.Right.homogeneous_generators` ([Schubert/DihedralSplines/PaperModuleFinite.lean](../Schubert/DihedralSplines/PaperModuleFinite.lean))
- `Dihedral.RootSubset.not_moduleFinite` ([Schubert/DihedralSplines/PaperModuleFinite.lean](../Schubert/DihedralSplines/PaperModuleFinite.lean))

### Equation (4) (`eqn:left_action`)

Status: **formalized**

- `Dihedral.RootSubset.left_formula` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.constantHom_aeval` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))

### Equation (5) (`eqn:right_action`)

Status: **formalized**

- `Dihedral.RootSubset.right_formula` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.orbitHom_aeval` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))

### Lemma 2.16

Status: **formalized**

The proof counts the generators of each degree with the flow-up basis of Theorem 4.5.

- `DihedralSplines.HessenbergIdeal.Left.minimal_degree_count` ([Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean](../Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Left.minimal_degrees_eq` ([Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean](../Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Right.minimal_degree_count` ([Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean](../Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Right.minimal_degrees_eq` ([Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean](../Schubert/DihedralSplines/MinimalHomogeneousDegrees.lean))
- `DihedralSplines.HessenbergIdeal.Left.minimal_finite` ([Schubert/DihedralSplines/MinimalGeneratorFinite.lean](../Schubert/DihedralSplines/MinimalGeneratorFinite.lean))
- `DihedralSplines.HessenbergIdeal.Right.minimal_finite` ([Schubert/DihedralSplines/MinimalGeneratorFinite.lean](../Schubert/DihedralSplines/MinimalGeneratorFinite.lean))

### Definition 2.17 (`def:upper_triangular`)

Status: **formalized**

- `Splines.PolynomialGraph.IsUpperAt` ([Schubert/Splines/UpperTriangular.lean](../Schubert/Splines/UpperTriangular.lean))
- `Splines.PolynomialGraph.IsUpperFamily` ([Schubert/Splines/UpperTriangular.lean](../Schubert/Splines/UpperTriangular.lean))
- `Splines.PolynomialGraph.upperAt_ideal` ([Schubert/Splines/UpperTriangular.lean](../Schubert/Splines/UpperTriangular.lean))
- `Splines.PolynomialGraph.upperFamily_ideal` ([Schubert/Splines/UpperTriangular.lean](../Schubert/Splines/UpperTriangular.lean))

### Remark 2.18

Status: **formalized**

- `Splines.PolynomialGraph.upper_matrix` ([Schubert/Splines/UpperTriangular.lean](../Schubert/Splines/UpperTriangular.lean))

### Lemma 2.19 (`lem:upper_triangular`)

Status: **formalized**

Here the splines need not be homogeneous, and $\deg\overline{\rho}\_w$ is the largest degree of the values of $\overline{\rho}\_w$.

- `DihedralSplines.TriangularFamily.Left.basis` ([Schubert/DihedralSplines/FamilyBasis.lean](../Schubert/DihedralSplines/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Left.basis_apply` ([Schubert/DihedralSplines/FamilyBasis.lean](../Schubert/DihedralSplines/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Left.minimal` ([Schubert/DihedralSplines/FamilyBasis.lean](../Schubert/DihedralSplines/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Right.basis` ([Schubert/DihedralSplines/FamilyBasis.lean](../Schubert/DihedralSplines/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Right.basis_apply` ([Schubert/DihedralSplines/FamilyBasis.lean](../Schubert/DihedralSplines/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.Right.minimal` ([Schubert/DihedralSplines/FamilyBasis.lean](../Schubert/DihedralSplines/FamilyBasis.lean))
- `DihedralSplines.TriangularFamily.projectedValue_mem` ([Schubert/DihedralSplines/FamilyProjection.lean](../Schubert/DihedralSplines/FamilyProjection.lean))
- `DihedralSplines.TriangularFamily.projectedValue_diagonal` ([Schubert/DihedralSplines/FamilyProjection.lean](../Schubert/DihedralSplines/FamilyProjection.lean))
- `DihedralSplines.TriangularFamily.Left.piece_finrank` ([Schubert/DihedralSplines/FamilyRank.lean](../Schubert/DihedralSplines/FamilyRank.lean))
- `DihedralSplines.TriangularFamily.Right.piece_finrank` ([Schubert/DihedralSplines/FamilyRank.lean](../Schubert/DihedralSplines/FamilyRank.lean))
- `DihedralSplines.TriangularFamily.Left.rankPolynomial_eq` ([Schubert/DihedralSplines/FamilyRank.lean](../Schubert/DihedralSplines/FamilyRank.lean))
- `DihedralSplines.TriangularFamily.Right.rankPolynomial_eq` ([Schubert/DihedralSplines/FamilyRank.lean](../Schubert/DihedralSplines/FamilyRank.lean))
- `DihedralSplines.HessenbergIdeal.Left.rankPolynomial_coeff` ([Schubert/DihedralSplines/FamilyRank.lean](../Schubert/DihedralSplines/FamilyRank.lean))
- `DihedralSplines.HessenbergIdeal.Right.rankPolynomial_coeff` ([Schubert/DihedralSplines/FamilyRank.lean](../Schubert/DihedralSplines/FamilyRank.lean))

### Definition 2.20 (`def:flowup`)

Status: **formalized**

- `DihedralSplines.TriangularFamily.Left.IsFlowup` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Right.IsFlowup` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Left.isFlowup_iff` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Right.isFlowup_iff` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.IsMember` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.At` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.family_at` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.at_least` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Left.member_iff` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))
- `DihedralSplines.TriangularFamily.Right.member_iff` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))

### Definition 2.21

Status: **formalized**

- `Dihedral.RootSubset.dot` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.dot_apply` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.dot_one` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.dot_mul` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.dotAction` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))

### Lemma 2.22 (`lem:dot_action_preserves_splines`)

Status: **formalized**

- `Dihedral.RootSubset.dot` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))
- `Dihedral.RootSubset.dot_apply` ([Schubert/DihedralSplines/PaperAction.lean](../Schubert/DihedralSplines/PaperAction.lean))

### Equation (6) (`eqndef:left_quotient`)

Status: **formalized**

- `Dihedral.RootSubset.Left.ideal_span` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.ideal_smul_top` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.Quotient` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.quotientMap` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.backendEquiv_map` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Left.piece` ([Schubert/DihedralSplines/PaperQuotientGrading.lean](../Schubert/DihedralSplines/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Left.gradedAlgebra` ([Schubert/DihedralSplines/PaperQuotientGrading.lean](../Schubert/DihedralSplines/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Left.dot_map` ([Schubert/DihedralSplines/PaperQuotientAction.lean](../Schubert/DihedralSplines/PaperQuotientAction.lean))
- `Dihedral.RootSubset.Left.pieceRepresentation` ([Schubert/DihedralSplines/PaperQuotientAction.lean](../Schubert/DihedralSplines/PaperQuotientAction.lean))

### Equation (7) (`eqndef:right_quotient`)

Status: **formalized**

- `Dihedral.RootSubset.Right.ideal_span` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.ideal_smul_top` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.Quotient` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.quotientMap` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.backendEquiv_map` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.piece` ([Schubert/DihedralSplines/PaperQuotientGrading.lean](../Schubert/DihedralSplines/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Right.gradedAlgebra` ([Schubert/DihedralSplines/PaperQuotientGrading.lean](../Schubert/DihedralSplines/PaperQuotientGrading.lean))
- `Dihedral.RootSubset.Right.dot_map` ([Schubert/DihedralSplines/PaperQuotientAction.lean](../Schubert/DihedralSplines/PaperQuotientAction.lean))
- `Dihedral.RootSubset.Right.pieceRepresentation` ([Schubert/DihedralSplines/PaperQuotientAction.lean](../Schubert/DihedralSplines/PaperQuotientAction.lean))

### Lemma 3.1 (`lem:left_edges_full_graph`)

Status: **formalized**

- `Dihedral.RootSubset.full_iff_left` ([Schubert/DihedralSplines/PaperFull.lean](../Schubert/DihedralSplines/PaperFull.lean))
- `DihedralSplines.HessenbergIdeal.full_iff_left` ([Schubert/DihedralSplines/PaperFull.lean](../Schubert/DihedralSplines/PaperFull.lean))

### Equation (8) (`eq:left_spline_condition_full`)

Status: **formalized**

- `Dihedral.RootSubset.full_algebra_eq` ([Schubert/DihedralSplines/PaperFull.lean](../Schubert/DihedralSplines/PaperFull.lean))
- `DihedralSplines.HessenbergIdeal.full_algebra_eq` ([Schubert/DihedralSplines/PaperFull.lean](../Schubert/DihedralSplines/PaperFull.lean))

### Lemma 3.2 (`lem:divided_difference_spline`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.full_edge` ([Schubert/DihedralSplines/SchubertOperators.lean](../Schubert/DihedralSplines/SchubertOperators.lean))
- `DihedralSplines.SchubertSpline.difference` ([Schubert/DihedralSplines/SchubertOperators.lean](../Schubert/DihedralSplines/SchubertOperators.lean))
- `DihedralSplines.SchubertSpline.difference_mul` ([Schubert/DihedralSplines/SchubertOperators.lean](../Schubert/DihedralSplines/SchubertOperators.lean))

### Equation (9) (`eq:divided_difference_spline`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.difference` ([Schubert/DihedralSplines/SchubertOperators.lean](../Schubert/DihedralSplines/SchubertOperators.lean))
- `DihedralSplines.SchubertSpline.difference_mul` ([Schubert/DihedralSplines/SchubertOperators.lean](../Schubert/DihedralSplines/SchubertOperators.lean))

### Equation (10) (`eq:top_schubert_spline`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.top` ([Schubert/DihedralSplines/SchubertConstruction.lean](../Schubert/DihedralSplines/SchubertConstruction.lean))
- `DihedralSplines.SchubertSpline.top_apply` ([Schubert/DihedralSplines/SchubertConstruction.lean](../Schubert/DihedralSplines/SchubertConstruction.lean))
- `DihedralSplines.SchubertSpline.spline_top` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))

### Equation (11) (`eq:schubert_recursion`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.spline_one` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.spline_top` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.spline_step` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.ascentRoot_spec` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.ascentRoot_eq` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))

### Proposition 3.3 (`prop:schubert_flowup`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.homogeneous` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.support` ([Schubert/DihedralSplines/SchubertRecursion.lean](../Schubert/DihedralSplines/SchubertRecursion.lean))
- `DihedralSplines.SchubertSpline.diagonal_product` ([Schubert/DihedralSplines/SchubertDiagonal.lean](../Schubert/DihedralSplines/SchubertDiagonal.lean))
- `DihedralSplines.SchubertSpline.degree` ([Schubert/DihedralSplines/SchubertBasis.lean](../Schubert/DihedralSplines/SchubertBasis.lean))

### Equation (12) (`eq:schubert_diagonal_value`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.diagonalProduct` ([Schubert/DihedralSplines/SchubertDiagonal.lean](../Schubert/DihedralSplines/SchubertDiagonal.lean))
- `DihedralSplines.SchubertSpline.diagonal_product` ([Schubert/DihedralSplines/SchubertDiagonal.lean](../Schubert/DihedralSplines/SchubertDiagonal.lean))

### Theorem 3.4 (`thm:schubert_rational`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.rationalRoots` ([Schubert/DihedralSplines/SchubertRational.lean](../Schubert/DihedralSplines/SchubertRational.lean))
- `DihedralSplines.SchubertSpline.rationalProduct` ([Schubert/DihedralSplines/SchubertRational.lean](../Schubert/DihedralSplines/SchubertRational.lean))
- `DihedralSplines.SchubertSpline.rational_formula` ([Schubert/DihedralSplines/SchubertRational.lean](../Schubert/DihedralSplines/SchubertRational.lean))
- `DihedralSplines.SchubertSpline.support_exact` ([Schubert/DihedralSplines/SchubertLocalization.lean](../Schubert/DihedralSplines/SchubertLocalization.lean))

### Linear forms of distinct positive roots are not proportional (Section 3)

Status: **formalized**

- `Dihedral.PositiveRoot.form_ne_zero` ([Schubert/Dihedral/RootObjectAction.lean](../Schubert/Dihedral/RootObjectAction.lean))
- `Dihedral.PositiveRoot.form_not_proportional` ([Schubert/Dihedral/RootFormProperties.lean](../Schubert/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.form_not_associated` ([Schubert/Dihedral/RootFormProperties.lean](../Schubert/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.form_relPrime` ([Schubert/Dihedral/RootFormProperties.lean](../Schubert/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.action_not_proportional` ([Schubert/Dihedral/RootObjectAction.lean](../Schubert/Dihedral/RootObjectAction.lean))
- `Dihedral.PositiveRoot.action_not_associated` ([Schubert/Dihedral/RootFormProperties.lean](../Schubert/Dihedral/RootFormProperties.lean))
- `Dihedral.PositiveRoot.action_relPrime` ([Schubert/Dihedral/RootObjectAction.lean](../Schubert/Dihedral/RootObjectAction.lean))

### Proposition 3.5 (`prop:schubert_basis`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.left_basis` ([Schubert/DihedralSplines/SchubertBasis.lean](../Schubert/DihedralSplines/SchubertBasis.lean))
- `DihedralSplines.SchubertSpline.right_basis` ([Schubert/DihedralSplines/SchubertBasis.lean](../Schubert/DihedralSplines/SchubertBasis.lean))
- `DihedralSplines.SchubertSpline.homogeneous_basis` ([Schubert/DihedralSplines/SchubertBasis.lean](../Schubert/DihedralSplines/SchubertBasis.lean))
- `DihedralSplines.SchubertSpline.degree` ([Schubert/DihedralSplines/SchubertBasis.lean](../Schubert/DihedralSplines/SchubertBasis.lean))

### Corollary 3.6 (`cor:schubert_hilbert_series`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.length_sum` ([Schubert/DihedralSplines/SchubertHilbert.lean](../Schubert/DihedralSplines/SchubertHilbert.lean))
- `DihedralSplines.SchubertSpline.length_factor` ([Schubert/DihedralSplines/SchubertHilbert.lean](../Schubert/DihedralSplines/SchubertHilbert.lean))
- `DihedralSplines.SchubertSpline.hilbert_formula` ([Schubert/DihedralSplines/SchubertHilbert.lean](../Schubert/DihedralSplines/SchubertHilbert.lean))

### Lemma 3.7 (`lem:borel_presentation_schubert_splines`)

Status: **formalized**

Injectivity of $\Psi$ is proved by Dedekind's independence of characters instead of by localization.

- `DihedralSplines.borelEquiv` ([Schubert/DihedralSplines/BorelEquivalence.lean](../Schubert/DihedralSplines/BorelEquivalence.lean))
- `DihedralSplines.borelEquiv_tmul` ([Schubert/DihedralSplines/BorelEquivalence.lean](../Schubert/DihedralSplines/BorelEquivalence.lean))
- `DihedralSplines.borelTensorPiece` ([Schubert/DihedralSplines/BorelTensorGrading.lean](../Schubert/DihedralSplines/BorelTensorGrading.lean))
- `DihedralSplines.borelTensorPiece_map` ([Schubert/DihedralSplines/BorelTensorGrading.lean](../Schubert/DihedralSplines/BorelTensorGrading.lean))
- `DihedralSplines.borelEquiv_xLeft` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yLeft` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_xRight` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yRight` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_dot` ([Schubert/DihedralSplines/BorelAction.lean](../Schubert/DihedralSplines/BorelAction.lean))

### Equation (13) (`eq:borel_presentation_schubert_splines`)

Status: **formalized**

- `DihedralSplines.borelEquiv` ([Schubert/DihedralSplines/BorelEquivalence.lean](../Schubert/DihedralSplines/BorelEquivalence.lean))
- `DihedralSplines.borelEquiv_tmul` ([Schubert/DihedralSplines/BorelEquivalence.lean](../Schubert/DihedralSplines/BorelEquivalence.lean))

### The tensor decomposition over the fixed field (Section 3)

Status: **formalized**

- `Dihedral.first_tensor_localization` ([Schubert/Dihedral/FirstLocalization.lean](../Schubert/Dihedral/FirstLocalization.lean))
- `Dihedral.second_tensor_unit` ([Schubert/Dihedral/FirstLocalization.lean](../Schubert/Dihedral/FirstLocalization.lean))
- `Dihedral.fraction_localization` ([Schubert/Dihedral/FractionLocalization.lean](../Schubert/Dihedral/FractionLocalization.lean))
- `Dihedral.fraction_fixed_subfield` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fraction_fixed_galois` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fraction_fixed_isGalois` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fixedTensorEquiv` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fixedTensorEquiv_tmul` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.polynomialFixedEquiv` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.polynomialFixedEquiv_tmul` ([Schubert/Dihedral/FixedFractionTensor.lean](../Schubert/Dihedral/FixedFractionTensor.lean))
- `Dihedral.fractionPolynomialEquiv` ([Schubert/Dihedral/FractionLocalization.lean](../Schubert/Dihedral/FractionLocalization.lean))
- `Dihedral.fractionPolynomialEquiv_tmul` ([Schubert/Dihedral/FractionLocalization.lean](../Schubert/Dihedral/FractionLocalization.lean))
- `Dihedral.tensorEvaluation_localized` ([Schubert/Dihedral/BorelLocalization.lean](../Schubert/Dihedral/BorelLocalization.lean))
- `DihedralSplines.borelHom_injective` ([Schubert/DihedralSplines/BorelSplineMap.lean](../Schubert/DihedralSplines/BorelSplineMap.lean))

### The invariants of $I\_2(n)$ and freeness over them (Section 3)

Status: **formalized**

Cited in the paper and proved here: with $u=x+iy$ and $v=x-iy$, the invariants $uv$ and $u^n+(-1)^nv^n$ generate $\mathbb{C}\[x,y\]^{I\_2(n)}$ freely, and $\mathbb{C}\[x,y\]$ is free of rank $2n$ over it.

- `Dihedral.Invariants.eq_generator_adjoin` ([Schubert/Dihedral/InvariantGeneration.lean](../Schubert/Dihedral/InvariantGeneration.lean))
- `Dihedral.basicInvariants_algebraicIndependent` ([Schubert/Dihedral/BasicInvariantIndependence.lean](../Schubert/Dihedral/BasicInvariantIndependence.lean))
- `Dihedral.nonempty_invariantPolynomialEquiv` ([Schubert/Dihedral/InvariantPolynomialRing.lean](../Schubert/Dihedral/InvariantPolynomialRing.lean))
- `Dihedral.Invariants.polynomial_free` ([Schubert/Dihedral/InvariantFreeness.lean](../Schubert/Dihedral/InvariantFreeness.lean))
- `Dihedral.Invariants.polynomial_finrank` ([Schubert/Dihedral/InvariantFreeness.lean](../Schubert/Dihedral/InvariantFreeness.lean))
- `Dihedral.coinvariantAlgebra_finite` ([Schubert/Dihedral/CoinvariantFinite.lean](../Schubert/Dihedral/CoinvariantFinite.lean))
- `Dihedral.quadraticInvariant_totalDegree` ([Schubert/Dihedral/InvariantDegrees.lean](../Schubert/Dihedral/InvariantDegrees.lean))
- `Dihedral.higherInvariant_totalDegree` ([Schubert/Dihedral/InvariantDegrees.lean](../Schubert/Dihedral/InvariantDegrees.lean))
- `Dihedral.Coinvariant.regular_iso` ([Schubert/Dihedral/CoinvariantRegular.lean](../Schubert/Dihedral/CoinvariantRegular.lean))

### Proposition 3.8 (`prop:left_schubert_rep`)

Status: **formalized**

- `DihedralSplines.SchubertSpline.left_class_coeff` ([Schubert/DihedralSplines/FullLeftClass.lean](../Schubert/DihedralSplines/FullLeftClass.lean))
- `DihedralSplines.SchubertSpline.left_class_polynomial` ([Schubert/DihedralSplines/FullLeftClass.lean](../Schubert/DihedralSplines/FullLeftClass.lean))
- `DihedralSplines.SchubertSpline.left_class_length_sum` ([Schubert/DihedralSplines/FullLeftClass.lean](../Schubert/DihedralSplines/FullLeftClass.lean))
- `DihedralSplines.SchubertSpline.left_class_geometric` ([Schubert/DihedralSplines/FullLeftClass.lean](../Schubert/DihedralSplines/FullLeftClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.full_piece_iso` ([Schubert/DihedralSplines/LeftFixedRepresentation.lean](../Schubert/DihedralSplines/LeftFixedRepresentation.lean))

### Proposition 3.9 (`prop:right_schubert_rep`)

Status: **formalized**

The trace formula is checked element by element from the graded characters of the coinvariant algebra, instead of from a regular sequence of invariants.

- `DihedralSplines.SchubertSpline.right_piece_iso` ([Schubert/DihedralSplines/FullRightClass.lean](../Schubert/DihedralSplines/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.right_class_coinvariant` ([Schubert/DihedralSplines/FullRightClass.lean](../Schubert/DihedralSplines/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.right_class_coeff` ([Schubert/DihedralSplines/FullRightClass.lean](../Schubert/DihedralSplines/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.right_character_degree` ([Schubert/DihedralSplines/FullRightClass.lean](../Schubert/DihedralSplines/FullRightClass.lean))
- `DihedralSplines.SchubertSpline.rightTrace` ([Schubert/DihedralSplines/FullRightTrace.lean](../Schubert/DihedralSplines/FullRightTrace.lean))
- `DihedralSplines.SchubertSpline.rightTrace_determinant` ([Schubert/DihedralSplines/FullRightDeterminant.lean](../Schubert/DihedralSplines/FullRightDeterminant.lean))
- `DihedralSplines.SchubertSpline.rightTrace_formula` ([Schubert/DihedralSplines/FullRightDeterminant.lean](../Schubert/DihedralSplines/FullRightDeterminant.lean))
- `DihedralSplines.SchubertSpline.rightTrace_one` ([Schubert/DihedralSplines/FullRightDeterminant.lean](../Schubert/DihedralSplines/FullRightDeterminant.lean))
- `DihedralSplines.SchubertSpline.polynomial_one_iso` ([Schubert/DihedralSplines/FullRightDeterminant.lean](../Schubert/DihedralSplines/FullRightDeterminant.lean))
- `Dihedral.vectorDenominator` ([Schubert/Dihedral/VectorDenominator.lean](../Schubert/Dihedral/VectorDenominator.lean))

### Remark 3.10

Status: **formalized**

- `DihedralSplines.SchubertSpline.full_piece_finrank_eq` ([Schubert/DihedralSplines/FullQuotientComparison.lean](../Schubert/DihedralSplines/FullQuotientComparison.lean))
- `DihedralSplines.SchubertSpline.full_piece_linearEquiv` ([Schubert/DihedralSplines/FullQuotientComparison.lean](../Schubert/DihedralSplines/FullQuotientComparison.lean))
- `DihedralSplines.SchubertSpline.full_piece_not_iso` ([Schubert/DihedralSplines/FullQuotientComparison.lean](../Schubert/DihedralSplines/FullQuotientComparison.lean))
- `DihedralSplines.borelEquiv_dot` ([Schubert/DihedralSplines/BorelAction.lean](../Schubert/DihedralSplines/BorelAction.lean))
- `DihedralSplines.borelEquiv_xLeft` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yLeft` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_xRight` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.borelEquiv_yRight` ([Schubert/DihedralSplines/BorelCoordinates.lean](../Schubert/DihedralSplines/BorelCoordinates.lean))
- `DihedralSplines.fullCoinvariantEquiv_mk` ([Schubert/DihedralSplines/FullCoinvariantEquivalence.lean](../Schubert/DihedralSplines/FullCoinvariantEquivalence.lean))
- `DihedralSplines.fullCoinvariantEquiv_equivariant` ([Schubert/DihedralSplines/FullCoinvariantEquivalence.lean](../Schubert/DihedralSplines/FullCoinvariantEquivalence.lean))
- `DihedralSplines.fullCoinvariantPieceEquiv` ([Schubert/DihedralSplines/FullCoinvariantEquivalence.lean](../Schubert/DihedralSplines/FullCoinvariantEquivalence.lean))
- `Dihedral.RootSubset.Left.coordinate_zero` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))
- `Dihedral.RootSubset.Right.coordinate_zero` ([Schubert/DihedralSplines/PaperQuotient.lean](../Schubert/DihedralSplines/PaperQuotient.lean))

### Remark 3.11

Status: **formalized**

Cited in the paper and proved here for $I\_2(n)$.

- `Dihedral.DoubleCoinvariant.relations_invariants` ([Schubert/Dihedral/DoubleCoinvariant.lean](../Schubert/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.tensorEquiv` ([Schubert/Dihedral/DoubleCoinvariant.lean](../Schubert/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.scalarEquiv` ([Schubert/Dihedral/DoubleCoinvariant.lean](../Schubert/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.tensorEquiv_first` ([Schubert/Dihedral/DoubleCoinvariant.lean](../Schubert/Dihedral/DoubleCoinvariant.lean))
- `Dihedral.DoubleCoinvariant.tensorEquiv_second` ([Schubert/Dihedral/DoubleCoinvariant.lean](../Schubert/Dihedral/DoubleCoinvariant.lean))
- `DihedralSplines.DoubleCoinvariant.localization` ([Schubert/DihedralSplines/DoubleLocalization.lean](../Schubert/DihedralSplines/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.schubert_basis` ([Schubert/DihedralSplines/DoubleLocalization.lean](../Schubert/DihedralSplines/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.localization_image` ([Schubert/DihedralSplines/DoubleLocalization.lean](../Schubert/DihedralSplines/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.localization_inverse` ([Schubert/DihedralSplines/DoubleLocalization.lean](../Schubert/DihedralSplines/DoubleLocalization.lean))
- `DihedralSplines.DoubleCoinvariant.root_form_real` ([Schubert/DihedralSplines/DoubleLocalization.lean](../Schubert/DihedralSplines/DoubleLocalization.lean))
- `Dihedral.polynomialAction_inverse_X` ([Schubert/Dihedral/PolynomialPullback.lean](../Schubert/Dihedral/PolynomialPullback.lean))
- `Dihedral.inverseCoordinate_eval` ([Schubert/Dihedral/PolynomialPullback.lean](../Schubert/Dihedral/PolynomialPullback.lean))

### Lemma 4.1 (`lem:generalized_divided_difference`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.dividedDifference` ([Schubert/DihedralSplines/PaperDividedDifference.lean](../Schubert/DihedralSplines/PaperDividedDifference.lean))
- `DihedralSplines.HessenbergIdeal.dividedDifference_mul` ([Schubert/DihedralSplines/PaperDividedDifference.lean](../Schubert/DihedralSplines/PaperDividedDifference.lean))
- `DihedralSplines.HessenbergIdeal.dividedDifference_unique` ([Schubert/DihedralSplines/PaperDividedDifference.lean](../Schubert/DihedralSplines/PaperDividedDifference.lean))

### Equation (14) (`eq:divided_difference`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.dividedDifference` ([Schubert/DihedralSplines/PaperDividedDifference.lean](../Schubert/DihedralSplines/PaperDividedDifference.lean))
- `DihedralSplines.HessenbergIdeal.dividedDifference_mul` ([Schubert/DihedralSplines/PaperDividedDifference.lean](../Schubert/DihedralSplines/PaperDividedDifference.lean))

### Lemma 4.2 (`lem:leftright_length`)

Status: **formalized**

- `Dihedral.PositiveRoot.ascent_length` ([Schubert/Dihedral/RootReflectionLengthVectors.lean](../Schubert/Dihedral/RootReflectionLengthVectors.lean))
- `Dihedral.PositiveRoot.descent_length` ([Schubert/Dihedral/RootReflectionLengthVectors.lean](../Schubert/Dihedral/RootReflectionLengthVectors.lean))

### Lemma 4.3 (`lem:simple_degree_changes`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.inversions_no_edge` ([Schubert/DihedralSplines/HessenbergVectorDegree.lean](../Schubert/DihedralSplines/HessenbergVectorDegree.lean))
- `DihedralSplines.HessenbergIdeal.length_edge` ([Schubert/DihedralSplines/HessenbergVectorDegree.lean](../Schubert/DihedralSplines/HessenbergVectorDegree.lean))
- `DihedralSplines.HessenbergIdeal.edge_range` ([Schubert/DihedralSplines/HessenbergVectorDegree.lean](../Schubert/DihedralSplines/HessenbergVectorDegree.lean))
- `DihedralSplines.HessenbergIdeal.length_full` ([Schubert/DihedralSplines/HessenbergVectorDegree.lean](../Schubert/DihedralSplines/HessenbergVectorDegree.lean))

### Corollary 4.4 (`cor:existence_upper_elts`)

Status: **formalized**

Stated for every $w\in I\_2(n)$.

- `DihedralSplines.FlowupSpline.spline` ([Schubert/DihedralSplines/FlowupRecursion.lean](../Schubert/DihedralSplines/FlowupRecursion.lean))
- `DihedralSplines.FlowupSpline.degree` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.support` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.diagonal` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Left.basis_apply` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.basis_apply` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.TriangularFamily.family_at` ([Schubert/DihedralSplines/FlowupBasisPredicate.lean](../Schubert/DihedralSplines/FlowupBasisPredicate.lean))

### Equation (15) (`eq:top_spline`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.topSpline` ([Schubert/DihedralSplines/PaperTop.lean](../Schubert/DihedralSplines/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_apply` ([Schubert/DihedralSplines/PaperTop.lean](../Schubert/DihedralSplines/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_nonzero` ([Schubert/DihedralSplines/PaperTop.lean](../Schubert/DihedralSplines/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_mem_piece` ([Schubert/DihedralSplines/PaperTop.lean](../Schubert/DihedralSplines/PaperTop.lean))
- `DihedralSplines.HessenbergIdeal.topSpline_support` ([Schubert/DihedralSplines/PaperTop.lean](../Schubert/DihedralSplines/PaperTop.lean))

### Theorem 4.5 (`thm:flowup`)

Status: **formalized**

- `DihedralSplines.FlowupSpline.family` ([Schubert/DihedralSplines/FlowupRecursion.lean](../Schubert/DihedralSplines/FlowupRecursion.lean))
- `DihedralSplines.FlowupSpline.degree` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.support` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.diagonal` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Left.basis_apply` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.basis_apply` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.spline_one` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_top` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_low` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_high` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))
- `DihedralSplines.FlowupSpline.spline_no_edge` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))

### Example 4.6 (`ex:generators_exist`)

Status: **formalized**

- `DihedralSplines.Pentagon.generator` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.initial_formulas` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.operator_formulas` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.certificates` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.whole_degrees` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.family_vertex` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.bases` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.left_rank` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.right_rank` ([Schubert/DihedralSplines/PentagonFamily.lean](../Schubert/DihedralSplines/PentagonFamily.lean))
- `DihedralSplines.Pentagon.generator_eq_spline` ([Schubert/DihedralSplines/PentagonRecursion.lean](../Schubert/DihedralSplines/PentagonRecursion.lean))
- `DihedralSplines.Pentagon.edges` ([Schubert/DihedralSplines/PentagonGraph.lean](../Schubert/DihedralSplines/PentagonGraph.lean))
- `DihedralSplines.Pentagon.edge_labels` ([Schubert/DihedralSplines/PentagonGraph.lean](../Schubert/DihedralSplines/PentagonGraph.lean))
- `DihedralSplines.Pentagon.top_values` ([Schubert/DihedralSplines/PentagonTop.lean](../Schubert/DihedralSplines/PentagonTop.lean))

### Corollary 4.7 (`cor:rank_gf`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.lengthPolynomial_even` ([Schubert/DihedralSplines/HessenbergLengthPolynomialClosed.lean](../Schubert/DihedralSplines/HessenbergLengthPolynomialClosed.lean))
- `DihedralSplines.HessenbergIdeal.lengthPolynomial_odd` ([Schubert/DihedralSplines/HessenbergLengthPolynomialClosed.lean](../Schubert/DihedralSplines/HessenbergLengthPolynomialClosed.lean))
- `DihedralSplines.HessenbergIdeal.lengthPolynomial_reverse` ([Schubert/DihedralSplines/LengthPolynomialSymmetry.lean](../Schubert/DihedralSplines/LengthPolynomialSymmetry.lean))
- `DihedralSplines.FlowupSpline.Left.rank_eq` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.Right.rank_eq` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.HessenbergIdeal.hilbertSeries_formula` ([Schubert/DihedralSplines/FlowupHilbert.lean](../Schubert/DihedralSplines/FlowupHilbert.lean))
- `DihedralSplines.HessenbergIdeal.coeff_piecewise` ([Schubert/DihedralSplines/HessenbergLengthPolynomialClosed.lean](../Schubert/DihedralSplines/HessenbergLengthPolynomialClosed.lean))

### Lemma 5.1 (`lem:regular`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.first_regular` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.second_regular` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.edge` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.boundary_card` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.eq_of_edges` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))

### Corollary 5.2 (`cor:rationally_smooth`)

Status: **formalized**

The uniqueness is deduced from the first part instead of by comparing values modulo $t\_\beta$.

- `DihedralSplines.HessenbergIdeal.Block.first` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.second` ([Schubert/DihedralSplines/HessenbergBlock.lean](../Schubert/DihedralSplines/HessenbergBlock.lean))
- `DihedralSplines.HessenbergIdeal.Block.localized` ([Schubert/DihedralSplines/BlockLocalization.lean](../Schubert/DihedralSplines/BlockLocalization.lean))
- `DihedralSplines.HessenbergIdeal.Block.localized_function` ([Schubert/DihedralSplines/BlockLocalization.lean](../Schubert/DihedralSplines/BlockLocalization.lean))
- `DihedralSplines.HessenbergIdeal.Block.normalized_unique` ([Schubert/DihedralSplines/BlockLocalization.lean](../Schubert/DihedralSplines/BlockLocalization.lean))

### Proposition 5.3 (`prop:flowup_explicit_setup`)

Status: **formalized**

- `DihedralSplines.FlowupSpline.block_shape` ([Schubert/DihedralSplines/FlowupBlock.lean](../Schubert/DihedralSplines/FlowupBlock.lean))
- `DihedralSplines.FlowupSpline.high_block` ([Schubert/DihedralSplines/FlowupBlock.lean](../Schubert/DihedralSplines/FlowupBlock.lean))
- `DihedralSplines.FlowupSpline.homogeneous` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.diagonal` ([Schubert/DihedralSplines/FlowupBasis.lean](../Schubert/DihedralSplines/FlowupBasis.lean))
- `DihedralSplines.FlowupSpline.spline_top` ([Schubert/DihedralSplines/FlowupEquations.lean](../Schubert/DihedralSplines/FlowupEquations.lean))

### Proposition 5.4 (`prop:linear_independence`)

Status: **formalized**

- `Dihedral.RootSubset.AlternatingBlocks` ([Schubert/DihedralSplines/BlockIndependence.lean](../Schubert/DihedralSplines/BlockIndependence.lean))
- `Dihedral.RootSubset.independent` ([Schubert/DihedralSplines/BlockIndependence.lean](../Schubert/DihedralSplines/BlockIndependence.lean))
- `Dihedral.RootSubset.boundaryFunction` ([Schubert/DihedralSplines/BoundaryRelations.lean](../Schubert/DihedralSplines/BoundaryRelations.lean))
- `Dihedral.length_rootReflection` ([Schubert/Dihedral/AlternatingWords.lean](../Schubert/Dihedral/AlternatingWords.lean))

### Corollary 5.5 (`cor:admissible_block_independence`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.AdmissibleBlocks` ([Schubert/DihedralSplines/AdmissibleIndependence.lean](../Schubert/DihedralSplines/AdmissibleIndependence.lean))
- `DihedralSplines.HessenbergIdeal.admissible_iff` ([Schubert/DihedralSplines/AdmissibleIndependence.lean](../Schubert/DihedralSplines/AdmissibleIndependence.lean))
- `DihedralSplines.HessenbergIdeal.admissible_independent` ([Schubert/DihedralSplines/AdmissibleIndependence.lean](../Schubert/DihedralSplines/AdmissibleIndependence.lean))

### Equation (16) (`eq:Ph_representation`)

Status: **formalized**

- `Dihedral.Frequency.partialSum` ([Schubert/Dihedral/FrequencySum.lean](../Schubert/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_zero` ([Schubert/Dihedral/FrequencySum.lean](../Schubert/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_succ` ([Schubert/Dihedral/FrequencySum.lean](../Schubert/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_terms_simple` ([Schubert/Dihedral/FrequencySum.lean](../Schubert/Dihedral/FrequencySum.lean))

### Remark 6.1

Status: **formalized**

- `Dihedral.Frequency.partialSum_finrank` ([Schubert/Dihedral/FrequencySum.lean](../Schubert/Dihedral/FrequencySum.lean))
- `Dihedral.Frequency.partialSum_split_class` ([Schubert/Dihedral/FrequencyTail.lean](../Schubert/Dihedral/FrequencyTail.lean))
- `Dihedral.PositiveRoot.coset_odd_complement` ([Schubert/Dihedral/FrequencyTail.lean](../Schubert/Dihedral/FrequencyTail.lean))
- `Dihedral.PositiveRoot.coset_even_complement` ([Schubert/Dihedral/FrequencyTail.lean](../Schubert/Dihedral/FrequencyTail.lean))
- `Dihedral.PositiveRoot.coset_odd_iso` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_iso` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_odd_class` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))
- `Dihedral.PositiveRoot.coset_even_class` ([Schubert/Dihedral/CosetDecomposition.lean](../Schubert/Dihedral/CosetDecomposition.lean))

### Definition 6.2 (`def:H_dominant`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.IsDominant` ([Schubert/DihedralSplines/HessenbergVectorDominant.lean](../Schubert/DihedralSplines/HessenbergVectorDominant.lean))
- `DihedralSplines.HessenbergIdeal.isDominant_indexed` ([Schubert/DihedralSplines/HessenbergVectorDominant.lean](../Schubert/DihedralSplines/HessenbergVectorDominant.lean))

### Remark 6.3

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.dominant_even` ([Schubert/DihedralSplines/DominanceEven.lean](../Schubert/DihedralSplines/DominanceEven.lean))
- `DihedralSplines.HessenbergIdeal.dominant_odd_unique` ([Schubert/DihedralSplines/DominanceOdd.lean](../Schubert/DihedralSplines/DominanceOdd.lean))
- `DihedralSplines.HessenbergIdeal.odd_choices` ([Schubert/DihedralSplines/OddIdealChoice.lean](../Schubert/DihedralSplines/OddIdealChoice.lean))
- `DihedralSplines.HessenbergIdeal.odd_choice` ([Schubert/DihedralSplines/OddIdealChoice.lean](../Schubert/DihedralSplines/OddIdealChoice.lean))
- `DihedralSplines.HessenbergIdeal.odd_choice_whole` ([Schubert/DihedralSplines/OddIdealWhole.lean](../Schubert/DihedralSplines/OddIdealWhole.lean))
- `DihedralSplines.HessenbergIdeal.odd_choices_whole` ([Schubert/DihedralSplines/OddIdealWhole.lean](../Schubert/DihedralSplines/OddIdealWhole.lean))

### Theorem 6.4 (`thm:left_representation`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.graded_class` ([Schubert/DihedralSplines/QuotientClass.lean](../Schubert/DihedralSplines/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_even` ([Schubert/DihedralSplines/LeftEvenClass.lean](../Schubert/DihedralSplines/LeftEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_odd` ([Schubert/DihedralSplines/LeftOddClass.lean](../Schubert/DihedralSplines/LeftOddClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.class_palindromic` ([Schubert/DihedralSplines/LeftClassPalindrome.lean](../Schubert/DihedralSplines/LeftClassPalindrome.lean))

### Equation (17) (`eq:left_hessenberg_representation`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.graded_class` ([Schubert/DihedralSplines/QuotientClass.lean](../Schubert/DihedralSplines/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_even` ([Schubert/DihedralSplines/LeftEvenClass.lean](../Schubert/DihedralSplines/LeftEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.graded_class_odd` ([Schubert/DihedralSplines/LeftOddClass.lean](../Schubert/DihedralSplines/LeftOddClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.class_palindromic` ([Schubert/DihedralSplines/LeftClassPalindrome.lean](../Schubert/DihedralSplines/LeftClassPalindrome.lean))

### Remark 6.5

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.dimension_rank` ([Schubert/DihedralSplines/LeftDimensions.lean](../Schubert/DihedralSplines/LeftDimensions.lean))
- `DihedralSplines.HessenbergIdeal.Left.dimension_length` ([Schubert/DihedralSplines/LeftDimensions.lean](../Schubert/DihedralSplines/LeftDimensions.lean))
- `DihedralSplines.HessenbergIdeal.Left.dimension_even` ([Schubert/DihedralSplines/LeftDimensions.lean](../Schubert/DihedralSplines/LeftDimensions.lean))
- `DihedralSplines.HessenbergIdeal.Left.dimension_odd` ([Schubert/DihedralSplines/LeftDimensions.lean](../Schubert/DihedralSplines/LeftDimensions.lean))
- `FiniteGroupCharacters.dimensionHom` ([Schubert/FiniteGroupCharacters/RepresentationDimension.lean](../Schubert/FiniteGroupCharacters/RepresentationDimension.lean))
- `FiniteGroupCharacters.dimensionHom_of` ([Schubert/FiniteGroupCharacters/RepresentationDimension.lean](../Schubert/FiniteGroupCharacters/RepresentationDimension.lean))
- `FiniteGroupCharacters.graded_dimension_coeff` ([Schubert/FiniteGroupCharacters/RepresentationDimension.lean](../Schubert/FiniteGroupCharacters/RepresentationDimension.lean))

### Example 6.6

Status: **formalized**

- `DihedralSplines.SchubertSpline.full_odd_class` ([Schubert/DihedralSplines/FullLeftExtension.lean](../Schubert/DihedralSplines/FullLeftExtension.lean))
- `DihedralSplines.SchubertSpline.full_even_half` ([Schubert/DihedralSplines/FullLeftExtension.lean](../Schubert/DihedralSplines/FullLeftExtension.lean))
- `DihedralSplines.SchubertSpline.left_class_geometric` ([Schubert/DihedralSplines/FullLeftClass.lean](../Schubert/DihedralSplines/FullLeftClass.lean))

### Example 6.7

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.two_simple_middle` ([Schubert/DihedralSplines/TwoSimpleClass.lean](../Schubert/DihedralSplines/TwoSimpleClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.two_simple_class` ([Schubert/DihedralSplines/TwoSimpleClass.lean](../Schubert/DihedralSplines/TwoSimpleClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.two_simple_odd` ([Schubert/DihedralSplines/TwoSimpleClass.lean](../Schubert/DihedralSplines/TwoSimpleClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.two_simple_even` ([Schubert/DihedralSplines/TwoSimpleClass.lean](../Schubert/DihedralSplines/TwoSimpleClass.lean))
- `Dihedral.Frequency.partialSum_after_one` ([Schubert/Dihedral/FrequencyClass.lean](../Schubert/Dihedral/FrequencyClass.lean))

### Example 6.8

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.withoutLast_class_even` ([Schubert/DihedralSplines/MissingTopClass.lean](../Schubert/DihedralSplines/MissingTopClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.withoutLast_class_odd` ([Schubert/DihedralSplines/MissingTopClass.lean](../Schubert/DihedralSplines/MissingTopClass.lean))

### Graded equivariant freeness (Section 6)

Status: **formalized**

- `Dihedral.RootSubset.Left.graded_section` ([Schubert/DihedralSplines/SplineGradedSection.lean](../Schubert/DihedralSplines/SplineGradedSection.lean))
- `DihedralSplines.HessenbergIdeal.Left.tensor_free` ([Schubert/DihedralSplines/HessenbergTensorFree.lean](../Schubert/DihedralSplines/HessenbergTensorFree.lean))
- `DihedralSplines.HessenbergIdeal.Left.degree_tensor_iso` ([Schubert/DihedralSplines/HessenbergConvolution.lean](../Schubert/DihedralSplines/HessenbergConvolution.lean))

### Equation (18) (`eq:left_equivariant_freeness`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.tensor_free` ([Schubert/DihedralSplines/HessenbergTensorFree.lean](../Schubert/DihedralSplines/HessenbergTensorFree.lean))

### Proposition 6.9 (`prop:left_quotient_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.pairingActionEquiv` ([Schubert/DihedralSplines/QuotientDuality.lean](../Schubert/DihedralSplines/QuotientDuality.lean))
- `DihedralSplines.HessenbergIdeal.Left.complementary_dual_iso` ([Schubert/DihedralSplines/QuotientDuality.lean](../Schubert/DihedralSplines/QuotientDuality.lean))
- `DihedralSplines.FlowupSpline.Left.pairingEquiv` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Left.multiplication_nondegenerate` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Left.pairingEquiv_apply` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Left.pairingEquiv_dot` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.HessenbergIdeal.Left.top_iso` ([Schubert/DihedralSplines/TopRepresentation.lean](../Schubert/DihedralSplines/TopRepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.complementary_dual` ([Schubert/DihedralSplines/QuotientSymmetry.lean](../Schubert/DihedralSplines/QuotientSymmetry.lean))

### Equation (19) (`eq:left_representation_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.complementary_dual` ([Schubert/DihedralSplines/QuotientSymmetry.lean](../Schubert/DihedralSplines/QuotientSymmetry.lean))
- `DihedralSplines.HessenbergIdeal.Left.top_iso` ([Schubert/DihedralSplines/TopRepresentation.lean](../Schubert/DihedralSplines/TopRepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.complementary_iso` ([Schubert/DihedralSplines/QuotientSymmetry.lean](../Schubert/DihedralSplines/QuotientSymmetry.lean))
- `Dihedral.self_dual` ([Schubert/Dihedral/SelfDual.lean](../Schubert/Dihedral/SelfDual.lean))

### The representations of $I\_2(n)$ are self-dual (Section 6)

Status: **formalized**

- `Dihedral.isConj_inv` ([Schubert/Dihedral/SelfDualScope.lean](../Schubert/Dihedral/SelfDualScope.lean))
- `Dihedral.irreducible_self_dual` ([Schubert/Dihedral/SelfDualScope.lean](../Schubert/Dihedral/SelfDualScope.lean))
- `Dihedral.self_dual` ([Schubert/Dihedral/SelfDual.lean](../Schubert/Dihedral/SelfDual.lean))

### Lemma 6.10 (`lem:trivial_left_subreps`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.trivialSource_embedding` ([Schubert/DihedralSplines/TrivialLeftEmbedding.lean](../Schubert/DihedralSplines/TrivialLeftEmbedding.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialSubpiece_iso` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialRange` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialRange_above` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation_class` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialInclusion` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivialInclusion_injective` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Left.trivial_subrepresentation` ([Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean](../Schubert/DihedralSplines/TrivialLeftSubrepresentation.lean))

### Equation (20) (`eq:left_middle_subtraction`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Left.middle_subtraction` ([Schubert/DihedralSplines/LeftMiddleSubtraction.lean](../Schubert/DihedralSplines/LeftMiddleSubtraction.lean))

### The decomposition of the polynomials of low degree (Section 6)

Status: **formalized**

- `Dihedral.polynomialPiece_frequency_iso` ([Schubert/Dihedral/PolynomialDecomposition.lean](../Schubert/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomialPiece_even_iso` ([Schubert/Dihedral/PolynomialDecomposition.lean](../Schubert/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomialPiece_odd_iso` ([Schubert/Dihedral/PolynomialDecomposition.lean](../Schubert/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomialPiece_frequency_simple` ([Schubert/Dihedral/PolynomialDecomposition.lean](../Schubert/Dihedral/PolynomialDecomposition.lean))
- `Dihedral.polynomial_weighted_class` ([Schubert/Dihedral/PolynomialMultiplicity.lean](../Schubert/Dihedral/PolynomialMultiplicity.lean))
- `DihedralSplines.HessenbergIdeal.Left.removed_weighted_class` ([Schubert/DihedralSplines/HessenbergRemovedClass.lean](../Schubert/DihedralSplines/HessenbergRemovedClass.lean))
- `DihedralSplines.HessenbergIdeal.Left.removed_frequency_class` ([Schubert/DihedralSplines/HessenbergRemovedClass.lean](../Schubert/DihedralSplines/HessenbergRemovedClass.lean))

### Corollary 6.11 (`cor:not_permutation`)

Status: **formalized**

- `DihedralSplines.Pentagon.whole_class` ([Schubert/DihedralSplines/PentagonRepresentation.lean](../Schubert/DihedralSplines/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.whole_iso` ([Schubert/DihedralSplines/PentagonRepresentation.lean](../Schubert/DihedralSplines/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.rotation_character` ([Schubert/DihedralSplines/PentagonRepresentation.lean](../Schubert/DihedralSplines/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.rotation_not_nat` ([Schubert/DihedralSplines/PentagonRepresentation.lean](../Schubert/DihedralSplines/PentagonRepresentation.lean))
- `DihedralSplines.Pentagon.not_permutation` ([Schubert/DihedralSplines/PentagonRepresentation.lean](../Schubert/DihedralSplines/PentagonRepresentation.lean))

### Equation (21) (`eq:right_equivariant_freeness`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.orbit_tensor_free` ([Schubert/DihedralSplines/OrbitTensorFree.lean](../Schubert/DihedralSplines/OrbitTensorFree.lean))
- `Dihedral.RootSubset.Right.scalar_range` ([Schubert/DihedralSplines/OrbitScalarRepresentation.lean](../Schubert/DihedralSplines/OrbitScalarRepresentation.lean))
- `Dihedral.RootSubset.Right.scalarPiece_iso` ([Schubert/DihedralSplines/OrbitScalarRepresentation.lean](../Schubert/DihedralSplines/OrbitScalarRepresentation.lean))

### Proposition 7.1 (`prop:right_quotient_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.pairingActionEquiv` ([Schubert/DihedralSplines/QuotientDuality.lean](../Schubert/DihedralSplines/QuotientDuality.lean))
- `DihedralSplines.HessenbergIdeal.Right.complementary_dual_iso` ([Schubert/DihedralSplines/QuotientDuality.lean](../Schubert/DihedralSplines/QuotientDuality.lean))
- `DihedralSplines.FlowupSpline.Right.pairingEquiv` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Right.multiplication_nondegenerate` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Right.pairingEquiv_apply` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.FlowupSpline.Right.pairingEquiv_dot` ([Schubert/DihedralSplines/QuotientPairing.lean](../Schubert/DihedralSplines/QuotientPairing.lean))
- `DihedralSplines.HessenbergIdeal.Right.top_iso` ([Schubert/DihedralSplines/TopRepresentation.lean](../Schubert/DihedralSplines/TopRepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.sign_complementary` ([Schubert/DihedralSplines/QuotientSymmetry.lean](../Schubert/DihedralSplines/QuotientSymmetry.lean))

### Equation (22) (`eq:right_representation_duality`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.sign_complementary` ([Schubert/DihedralSplines/QuotientSymmetry.lean](../Schubert/DihedralSplines/QuotientSymmetry.lean))
- `DihedralSplines.HessenbergIdeal.Right.top_iso` ([Schubert/DihedralSplines/TopRepresentation.lean](../Schubert/DihedralSplines/TopRepresentation.lean))

### Lemma 7.2 (`lem:coinv_right_subreps`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.coRange` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coRange_above` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation_class` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coInclusion` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.coInclusion_injective` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))
- `DihedralSplines.HessenbergIdeal.Right.co_subrepresentation` ([Schubert/DihedralSplines/CoGradedSubrepresentation.lean](../Schubert/DihedralSplines/CoGradedSubrepresentation.lean))

### Equation (23) (`eq:h_coinvariant`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.coClass` ([Schubert/DihedralSplines/CoinvariantPattern.lean](../Schubert/DihedralSplines/CoinvariantPattern.lean))
- `DihedralSplines.HessenbergIdeal.coClass_even` ([Schubert/DihedralSplines/CoinvariantPattern.lean](../Schubert/DihedralSplines/CoinvariantPattern.lean))
- `DihedralSplines.HessenbergIdeal.coClass_odd` ([Schubert/DihedralSplines/CoinvariantPattern.lean](../Schubert/DihedralSplines/CoinvariantPattern.lean))

### Theorem 7.3 (`thm:right_representation`)

Status: **formalized**

The piece of degree $h$ is computed directly, as in Theorem 6.4, instead of by comparison with $\mathrm{L}\_H$.

- `DihedralSplines.HessenbergIdeal.Right.graded_class` ([Schubert/DihedralSplines/QuotientClass.lean](../Schubert/DihedralSplines/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_even` ([Schubert/DihedralSplines/RightEvenClass.lean](../Schubert/DihedralSplines/RightEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_odd` ([Schubert/DihedralSplines/RightOddClass.lean](../Schubert/DihedralSplines/RightOddClass.lean))

### Equation (24) (`eq:right_hessenberg_representation`)

Status: **formalized**

- `DihedralSplines.HessenbergIdeal.Right.graded_class` ([Schubert/DihedralSplines/QuotientClass.lean](../Schubert/DihedralSplines/QuotientClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_even` ([Schubert/DihedralSplines/RightEvenClass.lean](../Schubert/DihedralSplines/RightEvenClass.lean))
- `DihedralSplines.HessenbergIdeal.Right.graded_class_odd` ([Schubert/DihedralSplines/RightOddClass.lean](../Schubert/DihedralSplines/RightOddClass.lean))
