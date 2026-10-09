import DihedralHessenberg.Paper.Main
import DihedralHessenberg.Dihedral.Main
import DihedralHessenberg.Splines.Main
import DihedralHessenberg.FiniteGroupCharacters.Main

/-!
# Audit of the paper's statements

For every statement of the paper listed in `docs/STATEMENTS.md`, in the order of the paper,
prints the signature of each Lean declaration that formalizes it, with its hypotheses, and its
transitive axiom dependencies. A declaration listed for several statements is printed once.
The expected axioms are only `propext`, `Classical.choice` and `Quot.sound`.
-/

set_option pp.fieldNotation false

-- Theorem 1 (`intthm:poincare_hilbert`)
#check @Schubert.DihedralSplines.HessenbergIdeal.poincare_hilbert
#print axioms Schubert.DihedralSplines.HessenbergIdeal.poincare_hilbert
#check @Schubert.DihedralSplines.HessenbergIdeal.hilbertSeries_coeff
#print axioms Schubert.DihedralSplines.HessenbergIdeal.hilbertSeries_coeff
#check @Schubert.DihedralSplines.HessenbergIdeal.hilbertSeries_rank
#print axioms Schubert.DihedralSplines.HessenbergIdeal.hilbertSeries_rank
#check @Schubert.DihedralSplines.FlowupSpline.Left.basis_apply
#print axioms Schubert.DihedralSplines.FlowupSpline.Left.basis_apply
#check @Schubert.DihedralSplines.FlowupSpline.Right.basis_apply
#print axioms Schubert.DihedralSplines.FlowupSpline.Right.basis_apply

-- Theorem 2 (`intthm:basis`)
#check @Schubert.DihedralSplines.FlowupSpline.basis_explicit
#print axioms Schubert.DihedralSplines.FlowupSpline.basis_explicit
#check @Schubert.DihedralSplines.FlowupSpline.shape
#print axioms Schubert.DihedralSplines.FlowupSpline.shape
#check @Schubert.DihedralSplines.BoundaryForm.formula
#print axioms Schubert.DihedralSplines.BoundaryForm.formula
#check @Schubert.DihedralSplines.BoundaryForm.coefficient_ne
#print axioms Schubert.DihedralSplines.BoundaryForm.coefficient_ne

-- Theorem 3 (`intthm:dotaction`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_even
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_odd
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.class_palindromic
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.class_palindromic
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_even
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_odd

-- Example 2.1 (`source-line-226`)
#check @Schubert.Dihedral.triangular_basis_images
#print axioms Schubert.Dihedral.triangular_basis_images
#check @Schubert.Dihedral.triangular_first_variable
#print axioms Schubert.Dihedral.triangular_first_variable
#check @Schubert.Dihedral.triangular_second_variable
#print axioms Schubert.Dihedral.triangular_second_variable
#check @Schubert.Dihedral.triangular_monomial
#print axioms Schubert.Dihedral.triangular_monomial
#check @Schubert.Dihedral.triangular_sum
#print axioms Schubert.Dihedral.triangular_sum

-- Lemma 2.2 (`lem:reflect_divisible`)
#check @Schubert.DihedralSplines.reflection_difference
#print axioms Schubert.DihedralSplines.reflection_difference

-- Unnumbered statement, Section 2.2 (The Dihedral Group and Root Systems) (`unlabeled:group-and-root-realization`)
#check @Schubert.Dihedral.presentationEquiv_firstSimpleReflection
#print axioms Schubert.Dihedral.presentationEquiv_firstSimpleReflection
#check @Schubert.Dihedral.presentationEquiv_secondSimpleReflection
#print axioms Schubert.Dihedral.presentationEquiv_secondSimpleReflection
#check @Schubert.Dihedral.reduced_word_alternating
#print axioms Schubert.Dihedral.reduced_word_alternating
#check @Schubert.Dihedral.unique_reduced_of_ne_longest
#print axioms Schubert.Dihedral.unique_reduced_of_ne_longest
#check @Schubert.Dihedral.longest_reduced_words
#print axioms Schubert.Dihedral.longest_reduced_words
#check @Schubert.Dihedral.vectorOperator_injective
#print axioms Schubert.Dihedral.vectorOperator_injective
#check @Schubert.Dihedral.PositiveRoot.realAction_reflection
#print axioms Schubert.Dihedral.PositiveRoot.realAction_reflection
#check @Schubert.Dihedral.positiveReflectionEquiv
#print axioms Schubert.Dihedral.positiveReflectionEquiv
#check @Schubert.Dihedral.numbered_even_reflection
#print axioms Schubert.Dihedral.numbered_even_reflection
#check @Schubert.Dihedral.numbered_odd_reflection
#print axioms Schubert.Dihedral.numbered_odd_reflection
#check @Schubert.Dihedral.roots_neg_iff
#print axioms Schubert.Dihedral.roots_neg_iff
#check @Schubert.Dihedral.roots_unit
#print axioms Schubert.Dihedral.roots_unit
#check @Schubert.Dihedral.roots_proportional
#print axioms Schubert.Dihedral.roots_proportional
#check @Schubert.Dihedral.roots_reflection_mem
#print axioms Schubert.Dihedral.roots_reflection_mem
#check @Schubert.Dihedral.Separator.partition
#print axioms Schubert.Dihedral.Separator.partition
#check @Schubert.Dihedral.Separator.reflectionEquiv
#print axioms Schubert.Dihedral.Separator.reflectionEquiv
#check @Schubert.Dihedral.Separator.exists_chamber
#print axioms Schubert.Dihedral.Separator.exists_chamber
#check @Schubert.Dihedral.Separator.unique_nearest_pair
#print axioms Schubert.Dihedral.Separator.unique_nearest_pair
#check @Schubert.Dihedral.Separator.foot_pairing
#print axioms Schubert.Dihedral.Separator.foot_pairing
#check @Schubert.Dihedral.Separator.distance_min
#print axioms Schubert.Dihedral.Separator.distance_min
#check @Schubert.Dihedral.Separator.Frame.nearest_pair
#print axioms Schubert.Dihedral.Separator.Frame.nearest_pair
#check @Schubert.Dihedral.Separator.Frame.generate
#print axioms Schubert.Dihedral.Separator.Frame.generate
#check @Schubert.Dihedral.Separator.singleton_ne_top
#print axioms Schubert.Dihedral.Separator.singleton_ne_top
#check @Schubert.Dihedral.Separator.disjoint
#print axioms Schubert.Dihedral.Separator.disjoint
#check @Schubert.Dihedral.bruhatLE_iff_exists_sublist
#print axioms Schubert.Dihedral.bruhatLE_iff_exists_sublist

-- Example 2.3 (`ex:reflection`)
#check @Schubert.Dihedral.polygonVertices
#print axioms Schubert.Dihedral.polygonVertices
#check @Schubert.Dihedral.polygon_small_offsets
#print axioms Schubert.Dihedral.polygon_small_offsets
#check @Schubert.Dihedral.polygon_scaled_angles
#print axioms Schubert.Dihedral.polygon_scaled_angles
#check @Schubert.Dihedral.polygon_action_mem
#print axioms Schubert.Dihedral.polygon_action_mem
#check @Schubert.Dihedral.PositiveRoot.axis_drawn
#print axioms Schubert.Dihedral.PositiveRoot.axis_drawn
#check @Schubert.Dihedral.drawn_axis_fixed
#print axioms Schubert.Dihedral.drawn_axis_fixed
#check @Schubert.Dihedral.positiveRoots_unit_angles
#print axioms Schubert.Dihedral.positiveRoots_unit_angles
#check @Schubert.Dihedral.PositiveRoot.reflection_axis
#print axioms Schubert.Dihedral.PositiveRoot.reflection_axis
#check @Schubert.Dihedral.PositiveRoot.fixed_iff_axis
#print axioms Schubert.Dihedral.PositiveRoot.fixed_iff_axis

-- Equation (1) (`eq:left_inversion_set`)
#check @Schubert.Dihedral.leftInversionSet
#print axioms Schubert.Dihedral.leftInversionSet
#check @Schubert.Dihedral.leftInversionSet_descent
#print axioms Schubert.Dihedral.leftInversionSet_descent
#check @Schubert.Dihedral.PositiveRoot.left_descent
#print axioms Schubert.Dihedral.PositiveRoot.left_descent

-- Equation (2) (`eq:right_inversion_set`)
#check @Schubert.Dihedral.rightInversionSet
#print axioms Schubert.Dihedral.rightInversionSet
#check @Schubert.Dihedral.rightInversionSet_descent
#print axioms Schubert.Dihedral.rightInversionSet_descent
#check @Schubert.Dihedral.PositiveRoot.right_descent
#print axioms Schubert.Dihedral.PositiveRoot.right_descent

-- Lemma 2.4 (`lem:rank_two_bruhat_facts`)
#check @Schubert.Dihedral.unique_root_descent
#print axioms Schubert.Dihedral.unique_root_descent
#check @Schubert.Dihedral.unique_root_ascent
#print axioms Schubert.Dihedral.unique_root_ascent
#check @Schubert.Dihedral.length_eq_longest
#print axioms Schubert.Dihedral.length_eq_longest
#check @Schubert.Dihedral.bruhatLE_iff_eq_or_length_lt
#print axioms Schubert.Dihedral.bruhatLE_iff_eq_or_length_lt
#check @Schubert.Dihedral.ncard_leftInversionSet
#print axioms Schubert.Dihedral.ncard_leftInversionSet
#check @Schubert.Dihedral.PositiveRoot.left_ascent
#print axioms Schubert.Dihedral.PositiveRoot.left_ascent
#check @Schubert.Dihedral.PositiveRoot.left_ascent_disjoint
#print axioms Schubert.Dihedral.PositiveRoot.left_ascent_disjoint
#check @Schubert.Dihedral.PositiveRoot.right_ascent
#print axioms Schubert.Dihedral.PositiveRoot.right_ascent

-- Unnumbered statement, Section 2.3 (Representations) (`unlabeled:representation-classification`)
#check @Schubert.Dihedral.irreducible_dimension
#print axioms Schubert.Dihedral.irreducible_dimension
#check @Schubert.Dihedral.irrep_counts_odd
#print axioms Schubert.Dihedral.irrep_counts_odd
#check @Schubert.Dihedral.irrep_counts_even
#print axioms Schubert.Dihedral.irrep_counts_even
#check @Schubert.Dihedral.scalarFDRep
#print axioms Schubert.Dihedral.scalarFDRep
#check @Schubert.Dihedral.signCharacter_length
#print axioms Schubert.Dihedral.signCharacter_length
#check @Schubert.Dihedral.signFDRep_character
#print axioms Schubert.Dihedral.signFDRep_character
#check @Schubert.Dihedral.evenScalarCharacter_rotation
#print axioms Schubert.Dihedral.evenScalarCharacter_rotation
#check @Schubert.Dihedral.evenScalarCharacter_s1
#print axioms Schubert.Dihedral.evenScalarCharacter_s1
#check @Schubert.Dihedral.frequencyFDRep_finrank
#print axioms Schubert.Dihedral.frequencyFDRep_finrank
#check @Schubert.Dihedral.frequencyFDRep_simple_of_lower_half
#print axioms Schubert.Dihedral.frequencyFDRep_simple_of_lower_half
#check @Schubert.Dihedral.Frequency.character_zpow
#print axioms Schubert.Dihedral.Frequency.character_zpow
#check @Schubert.Dihedral.Frequency.character_zpow_s1
#print axioms Schubert.Dihedral.Frequency.character_zpow_s1
#check @Schubert.Dihedral.frequency_one
#print axioms Schubert.Dihedral.frequency_one
#check @Schubert.Dihedral.frequency_one_iso
#print axioms Schubert.Dihedral.frequency_one_iso
#check @Schubert.Dihedral.irreducible_classification
#print axioms Schubert.Dihedral.irreducible_classification
#check @Schubert.Dihedral.irrepFDRep_iso_iff_eq
#print axioms Schubert.Dihedral.irrepFDRep_iso_iff_eq
#check @Schubert.Dihedral.PositiveRoot.scalarCharacter_reflection
#print axioms Schubert.Dihedral.PositiveRoot.scalarCharacter_reflection
#check @Schubert.Dihedral.PositiveRoot.scalarCharacter_unique
#print axioms Schubert.Dihedral.PositiveRoot.scalarCharacter_unique
#check @Schubert.Dihedral.PositiveRoot.cosetFDRep
#print axioms Schubert.Dihedral.PositiveRoot.cosetFDRep
#check @Schubert.Dihedral.PositiveRoot.coset_odd_iso
#print axioms Schubert.Dihedral.PositiveRoot.coset_odd_iso
#check @Schubert.Dihedral.PositiveRoot.coset_even_iso
#print axioms Schubert.Dihedral.PositiveRoot.coset_even_iso

-- Equation (3) (`eq:reflection_coset_decomposition`)
-- `Schubert.Dihedral.PositiveRoot.cosetFDRep`: printed above
-- `Schubert.Dihedral.PositiveRoot.coset_odd_iso`: printed above
-- `Schubert.Dihedral.PositiveRoot.coset_even_iso`: printed above
#check @Schubert.Dihedral.PositiveRoot.coset_odd_class
#print axioms Schubert.Dihedral.PositiveRoot.coset_odd_class
#check @Schubert.Dihedral.PositiveRoot.coset_even_class
#print axioms Schubert.Dihedral.PositiveRoot.coset_even_class
-- `Schubert.Dihedral.PositiveRoot.scalarCharacter_reflection`: printed above
-- `Schubert.Dihedral.PositiveRoot.scalarCharacter_unique`: printed above

-- Example 2.5 (`source-line-482`)
#check @Schubert.DihedralSplines.square_first_matrix
#print axioms Schubert.DihedralSplines.square_first_matrix
#check @Schubert.DihedralSplines.square_second_matrix
#print axioms Schubert.DihedralSplines.square_second_matrix
#check @Schubert.DihedralSplines.square_longest
#print axioms Schubert.DihedralSplines.square_longest
#check @Schubert.DihedralSplines.square_third_reflection
#print axioms Schubert.DihedralSplines.square_third_reflection
#check @Schubert.DihedralSplines.square_simple_sign
#print axioms Schubert.DihedralSplines.square_simple_sign
#check @Schubert.DihedralSplines.square_third_sign
#print axioms Schubert.DihedralSplines.square_third_sign
#check @Schubert.DihedralSplines.square_simple_trivial
#print axioms Schubert.DihedralSplines.square_simple_trivial
#check @Schubert.DihedralSplines.square_trivial_character
#print axioms Schubert.DihedralSplines.square_trivial_character
-- `Schubert.Dihedral.frequency_one`: printed above
-- `Schubert.Dihedral.signCharacter_length`: printed above

-- Definition 2.6 (`def:root_poset`)
#check @Schubert.DihedralSplines.RootOrder
#print axioms Schubert.DihedralSplines.RootOrder
#check @Schubert.DihedralSplines.rootOrder
#print axioms Schubert.DihedralSplines.rootOrder
#check @Schubert.DihedralSplines.rootOrder_refl
#print axioms Schubert.DihedralSplines.rootOrder_refl
#check @Schubert.DihedralSplines.rootOrder_trans
#print axioms Schubert.DihedralSplines.rootOrder_trans
#check @Schubert.DihedralSplines.rootOrder_antisymm
#print axioms Schubert.DihedralSplines.rootOrder_antisymm

-- Unnumbered statement, Section 2.4 (The Root Poset) (`unlabeled:root-poset-hasse-diagrams`)
#check @Schubert.DihedralSplines.rootOrder_layers
#print axioms Schubert.DihedralSplines.rootOrder_layers
#check @Schubert.DihedralSplines.rootOrder_lt_iff
#print axioms Schubert.DihedralSplines.rootOrder_lt_iff
#check @Schubert.DihedralSplines.rootOrder_covBy_iff
#print axioms Schubert.DihedralSplines.rootOrder_covBy_iff
#check @Schubert.DihedralSplines.layer_card
#print axioms Schubert.DihedralSplines.layer_card

-- Remark 2.7 (`source-line-538`)
#check @Schubert.DihedralSplines.rootOrder_length
#print axioms Schubert.DihedralSplines.rootOrder_length
#check @Schubert.DihedralSplines.rootOrder_bruhat
#print axioms Schubert.DihedralSplines.rootOrder_bruhat

-- Unnumbered statement, Section 2.4 (The Root Poset) (`unlabeled:hessenberg-space-classification`)
#check @Schubert.DihedralSplines.HessenbergIdeal
#print axioms Schubert.DihedralSplines.HessenbergIdeal
#check @Schubert.DihedralSplines.HessenbergIdeal.classification
#print axioms Schubert.DihedralSplines.HessenbergIdeal.classification
#check @Schubert.DihedralSplines.HessenbergIdeal.exists_initial
#print axioms Schubert.DihedralSplines.HessenbergIdeal.exists_initial
#check @Schubert.DihedralSplines.HessenbergIdeal.exists_other
#print axioms Schubert.DihedralSplines.HessenbergIdeal.exists_other
#check @Schubert.DihedralSplines.HessenbergIdeal.natCard
#print axioms Schubert.DihedralSplines.HessenbergIdeal.natCard

-- Remark 2.8 (`source-line-548`)
#check @Schubert.Dihedral.PositiveRoot.depth
#print axioms Schubert.Dihedral.PositiveRoot.depth
#check @Schubert.Dihedral.DepthStep
#print axioms Schubert.Dihedral.DepthStep
#check @Schubert.Dihedral.PositiveRoot.depth_layer
#print axioms Schubert.Dihedral.PositiveRoot.depth_layer
#check @Schubert.Dihedral.depth_step_iff
#print axioms Schubert.Dihedral.depth_step_iff
#check @Schubert.Dihedral.depth_order_iff
#print axioms Schubert.Dihedral.depth_order_iff
#check @Schubert.Dihedral.Separator.label_ideal_signs
#print axioms Schubert.Dihedral.Separator.label_ideal_signs
#check @Schubert.Dihedral.Separator.spline_signs
#print axioms Schubert.Dihedral.Separator.spline_signs
#check @Schubert.Dihedral.Separator.spline_set_signs
#print axioms Schubert.Dihedral.Separator.spline_set_signs
#check @Schubert.DihedralSplines.six_depth_counterexample
#print axioms Schubert.DihedralSplines.six_depth_counterexample
#check @Schubert.DihedralSplines.six_three_root_ideal
#print axioms Schubert.DihedralSplines.six_three_root_ideal

-- Remark 2.9 (`source-line-647`)
#check @Schubert.DihedralSplines.four_orders_differ
#print axioms Schubert.DihedralSplines.four_orders_differ
#check @Schubert.DihedralSplines.four_lower_ideals
#print axioms Schubert.DihedralSplines.four_lower_ideals
#check @Schubert.DihedralSplines.six_unit_not_g2
#print axioms Schubert.DihedralSplines.six_unit_not_g2
#check @Schubert.DihedralSplines.six_g2_not_unit
#print axioms Schubert.DihedralSplines.six_g2_not_unit
#check @Schubert.Dihedral.RootLattice.a2_order
#print axioms Schubert.Dihedral.RootLattice.a2_order
#check @Schubert.Dihedral.RootLattice.a2_lower_iff
#print axioms Schubert.Dihedral.RootLattice.a2_lower_iff
#check @Schubert.Dihedral.RootLattice.a2_crystallographic
#print axioms Schubert.Dihedral.RootLattice.a2_crystallographic
#check @Schubert.Dihedral.RootLattice.b2_crystallographic
#print axioms Schubert.Dihedral.RootLattice.b2_crystallographic
#check @Schubert.Dihedral.RootLattice.c2_crystallographic
#print axioms Schubert.Dihedral.RootLattice.c2_crystallographic
#check @Schubert.Dihedral.RootLattice.g2_crystallographic
#print axioms Schubert.Dihedral.RootLattice.g2_crystallographic
#check @Schubert.Dihedral.RootLattice.a2GroupEquiv
#print axioms Schubert.Dihedral.RootLattice.a2GroupEquiv
#check @Schubert.Dihedral.RootLattice.b2GroupEquiv
#print axioms Schubert.Dihedral.RootLattice.b2GroupEquiv
#check @Schubert.Dihedral.RootLattice.c2GroupEquiv
#print axioms Schubert.Dihedral.RootLattice.c2GroupEquiv
#check @Schubert.Dihedral.RootLattice.g2GroupEquiv
#print axioms Schubert.Dihedral.RootLattice.g2GroupEquiv

-- Definition 2.10 (`def:inversion_set`)
#check @Schubert.Dihedral.RootSubset.inversions
#print axioms Schubert.Dihedral.RootSubset.inversions
#check @Schubert.Dihedral.RootSubset.length
#print axioms Schubert.Dihedral.RootSubset.length
#check @Schubert.Dihedral.RootSubset.mem_inversions
#print axioms Schubert.Dihedral.RootSubset.mem_inversions
#check @Schubert.Dihedral.RootSubset.inversions_finite
#print axioms Schubert.Dihedral.RootSubset.inversions_finite
#check @Schubert.Dihedral.RootSubset.inversions_bijOn
#print axioms Schubert.Dihedral.RootSubset.inversions_bijOn
-- `Schubert.Dihedral.rightInversionSet_descent`: printed above
-- `Schubert.Dihedral.PositiveRoot.right_descent`: printed above

-- Unnumbered statement, Section 2.4 (The Root Poset) (`unlabeled:labeled-cayley-graph`)
#check @Schubert.Dihedral.RootSubset.edges
#print axioms Schubert.Dihedral.RootSubset.edges
#check @Schubert.Dihedral.RootSubset.mem_edges
#print axioms Schubert.Dihedral.RootSubset.mem_edges
#check @Schubert.Dihedral.RootSubset.edgeLabel_edge
#print axioms Schubert.Dihedral.RootSubset.edgeLabel_edge
#check @Schubert.Dihedral.RootSubset.edgeLabel_eq_action
#print axioms Schubert.Dihedral.RootSubset.edgeLabel_eq_action
#check @Schubert.Dihedral.RootSubset.edgeEquiv
#print axioms Schubert.Dihedral.RootSubset.edgeEquiv
#check @Schubert.Dihedral.RootSubset.label_reverse
#print axioms Schubert.Dihedral.RootSubset.label_reverse

-- Example 2.11 (`ex:cayley`)
#check @Schubert.DihedralSplines.Triangle.selected
#print axioms Schubert.DihedralSplines.Triangle.selected
#check @Schubert.DihedralSplines.Triangle.pairs
#print axioms Schubert.DihedralSplines.Triangle.pairs
#check @Schubert.DihedralSplines.Triangle.edges
#print axioms Schubert.DihedralSplines.Triangle.edges
#check @Schubert.DihedralSplines.Triangle.edge_labels
#print axioms Schubert.DihedralSplines.Triangle.edge_labels
#check @Schubert.DihedralSplines.Triangle.inversions
#print axioms Schubert.DihedralSplines.Triangle.inversions
#check @Schubert.DihedralSplines.Square.selected
#print axioms Schubert.DihedralSplines.Square.selected
#check @Schubert.DihedralSplines.Square.pairs
#print axioms Schubert.DihedralSplines.Square.pairs
#check @Schubert.DihedralSplines.Square.edges
#print axioms Schubert.DihedralSplines.Square.edges
#check @Schubert.DihedralSplines.Square.edge_labels
#print axioms Schubert.DihedralSplines.Square.edge_labels

-- Unnumbered statement, Section 2.4 (The Root Poset) (`unlabeled:oriented-cayley-graph`)
#check @Schubert.Dihedral.RootSubset.orientedEdges
#print axioms Schubert.Dihedral.RootSubset.orientedEdges
#check @Schubert.Dihedral.RootSubset.reachable
#print axioms Schubert.Dihedral.RootSubset.reachable
#check @Schubert.Dihedral.RootSubset.acyclic
#print axioms Schubert.Dihedral.RootSubset.acyclic
#check @Schubert.Dihedral.RootSubset.incoming_card
#print axioms Schubert.Dihedral.RootSubset.incoming_card
#check @Schubert.Dihedral.RootSubset.partialOrder
#print axioms Schubert.Dihedral.RootSubset.partialOrder
#check @Schubert.Dihedral.RootSubset.reachable_strict_iff
#print axioms Schubert.Dihedral.RootSubset.reachable_strict_iff
#check @Schubert.Dihedral.RootSubset.partialOrder_lt
#print axioms Schubert.Dihedral.RootSubset.partialOrder_lt
#check @Schubert.Dihedral.RootSubset.edge_length_ne
#print axioms Schubert.Dihedral.RootSubset.edge_length_ne
#check @Schubert.Dihedral.RootSubset.oriented_xor_reverse
#print axioms Schubert.Dihedral.RootSubset.oriented_xor_reverse

-- Example 2.12 (`source-line-716`)
#check @Schubert.Dihedral.RootSubset.simple_reachable
#print axioms Schubert.Dihedral.RootSubset.simple_reachable
#check @Schubert.Dihedral.rightWeakLE_prefix
#print axioms Schubert.Dihedral.rightWeakLE_prefix
#check @Schubert.Dihedral.RootSubset.full_reachable
#print axioms Schubert.Dihedral.RootSubset.full_reachable

-- Example 2.13 (`source-line-719`)
#check @Schubert.DihedralSplines.pentagon_oriented
#print axioms Schubert.DihedralSplines.pentagon_oriented
#check @Schubert.DihedralSplines.pentagon_cover_iff
#print axioms Schubert.DihedralSplines.pentagon_cover_iff
#check @Schubert.DihedralSplines.pentagon_hasse
#print axioms Schubert.DihedralSplines.pentagon_hasse

-- Unnumbered statement, Section 2.5 (Splines and their Algebraic Properties) (`unlabeled:reflection-spline-module`)
#check @Schubert.Dihedral.RootSubset.IsSpline
#print axioms Schubert.Dihedral.RootSubset.IsSpline
#check @Schubert.Dihedral.RootSubset.splineAlgebra
#print axioms Schubert.Dihedral.RootSubset.splineAlgebra
#check @Schubert.Dihedral.RootSubset.mem_splineAlgebra
#print axioms Schubert.Dihedral.RootSubset.mem_splineAlgebra
#check @Schubert.DihedralSplines.HessenbergIdeal.splineEquiv_apply
#print axioms Schubert.DihedralSplines.HessenbergIdeal.splineEquiv_apply

-- Unnumbered statement, Section 2.5 (Splines and their Algebraic Properties) (`unlabeled:triangle-spline-illustrations`)
#check @Schubert.DihedralSplines.TriangleIllustrations.value
#print axioms Schubert.DihedralSplines.TriangleIllustrations.value
#check @Schubert.DihedralSplines.TriangleIllustrations.word_values
#print axioms Schubert.DihedralSplines.TriangleIllustrations.word_values
#check @Schubert.DihedralSplines.TriangleIllustrations.rows
#print axioms Schubert.DihedralSplines.TriangleIllustrations.rows
#check @Schubert.DihedralSplines.TriangleIllustrations.isSpline
#print axioms Schubert.DihedralSplines.TriangleIllustrations.isSpline

-- Unnumbered statement, Section 2.5 (Splines and their Algebraic Properties) (`unlabeled:square-spline-illustrations`)
#check @Schubert.DihedralSplines.SquareIllustrations.value
#print axioms Schubert.DihedralSplines.SquareIllustrations.value
#check @Schubert.DihedralSplines.SquareIllustrations.word_values
#print axioms Schubert.DihedralSplines.SquareIllustrations.word_values
#check @Schubert.DihedralSplines.SquareIllustrations.rows
#print axioms Schubert.DihedralSplines.SquareIllustrations.rows
#check @Schubert.DihedralSplines.SquareIllustrations.isSpline
#print axioms Schubert.DihedralSplines.SquareIllustrations.isSpline

-- Unnumbered statement, Section 2.5 (Splines and their Algebraic Properties) (`unlabeled:edge-label-reflection`)
#check @Schubert.Dihedral.RootSubset.edgeLabel_eq_form_iff
#print axioms Schubert.Dihedral.RootSubset.edgeLabel_eq_form_iff

-- Lemma 2.14 (`source-line-1047`)
-- `Schubert.Dihedral.RootSubset.splineAlgebra`: printed above
-- `Schubert.Dihedral.RootSubset.mem_splineAlgebra`: printed above

-- Lemma 2.15 (`source-line-1058`)
#check @Schubert.Dihedral.RootSubset.piece
#print axioms Schubert.Dihedral.RootSubset.piece
#check @Schubert.Dihedral.RootSubset.mem_piece
#print axioms Schubert.Dihedral.RootSubset.mem_piece
#check @Schubert.Dihedral.RootSubset.component_apply
#print axioms Schubert.Dihedral.RootSubset.component_apply
#check @Schubert.Dihedral.RootSubset.piece_isInternal
#print axioms Schubert.Dihedral.RootSubset.piece_isInternal
#check @Schubert.Dihedral.RootSubset.gradedAlgebra
#print axioms Schubert.Dihedral.RootSubset.gradedAlgebra

-- Unnumbered statement, Section 2.5 (Splines and their Algebraic Properties) (`unlabeled:constant-and-orbit-polynomial-splines`)
#check @Schubert.Dihedral.RootSubset.constantHom
#print axioms Schubert.Dihedral.RootSubset.constantHom
#check @Schubert.Dihedral.RootSubset.orbitHom
#print axioms Schubert.Dihedral.RootSubset.orbitHom
#check @Schubert.Dihedral.RootSubset.constantHom_injective
#print axioms Schubert.Dihedral.RootSubset.constantHom_injective
#check @Schubert.Dihedral.RootSubset.orbitHom_injective
#print axioms Schubert.Dihedral.RootSubset.orbitHom_injective
#check @Schubert.Dihedral.RootSubset.one_apply
#print axioms Schubert.Dihedral.RootSubset.one_apply
#check @Schubert.Dihedral.RootSubset.xLeft_apply
#print axioms Schubert.Dihedral.RootSubset.xLeft_apply
#check @Schubert.Dihedral.RootSubset.yLeft_apply
#print axioms Schubert.Dihedral.RootSubset.yLeft_apply
#check @Schubert.Dihedral.RootSubset.xRight_apply
#print axioms Schubert.Dihedral.RootSubset.xRight_apply
#check @Schubert.Dihedral.RootSubset.yRight_apply
#print axioms Schubert.Dihedral.RootSubset.yRight_apply
#check @Schubert.Dihedral.RootSubset.constantHom_mem_piece
#print axioms Schubert.Dihedral.RootSubset.constantHom_mem_piece
#check @Schubert.Dihedral.RootSubset.orbitHom_mem_piece
#print axioms Schubert.Dihedral.RootSubset.orbitHom_mem_piece
#check @Schubert.Dihedral.RootSubset.Left.smul_mem_piece
#print axioms Schubert.Dihedral.RootSubset.Left.smul_mem_piece
#check @Schubert.Dihedral.RootSubset.Right.smul_mem_piece
#print axioms Schubert.Dihedral.RootSubset.Right.smul_mem_piece
#check @Schubert.Dihedral.RootSubset.Left.module_finite
#print axioms Schubert.Dihedral.RootSubset.Left.module_finite
#check @Schubert.Dihedral.RootSubset.Right.module_finite
#print axioms Schubert.Dihedral.RootSubset.Right.module_finite
#check @Schubert.Dihedral.RootSubset.Left.homogeneous_generators
#print axioms Schubert.Dihedral.RootSubset.Left.homogeneous_generators
#check @Schubert.Dihedral.RootSubset.Right.homogeneous_generators
#print axioms Schubert.Dihedral.RootSubset.Right.homogeneous_generators
#check @Schubert.Dihedral.RootSubset.not_moduleFinite
#print axioms Schubert.Dihedral.RootSubset.not_moduleFinite

-- Equation (4) (`eqn:left_action`)
#check @Schubert.Dihedral.RootSubset.left_formula
#print axioms Schubert.Dihedral.RootSubset.left_formula
#check @Schubert.Dihedral.RootSubset.constantHom_aeval
#print axioms Schubert.Dihedral.RootSubset.constantHom_aeval

-- Equation (5) (`eqn:right_action`)
#check @Schubert.Dihedral.RootSubset.right_formula
#print axioms Schubert.Dihedral.RootSubset.right_formula
#check @Schubert.Dihedral.RootSubset.orbitHom_aeval
#print axioms Schubert.Dihedral.RootSubset.orbitHom_aeval

-- Lemma 2.16 (`source-line-1086`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.minimal_degree_count
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.minimal_degree_count
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.minimal_degrees_eq
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.minimal_degrees_eq
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.minimal_degree_count
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.minimal_degree_count
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.minimal_degrees_eq
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.minimal_degrees_eq
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.minimal_finite
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.minimal_finite
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.minimal_finite
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.minimal_finite

-- Definition 2.17 (`def:upper_triangular`)
#check @Schubert.Splines.PolynomialGraph.IsUpperAt
#print axioms Schubert.Splines.PolynomialGraph.IsUpperAt
#check @Schubert.Splines.PolynomialGraph.IsUpperFamily
#print axioms Schubert.Splines.PolynomialGraph.IsUpperFamily
#check @Schubert.Splines.PolynomialGraph.upperAt_ideal
#print axioms Schubert.Splines.PolynomialGraph.upperAt_ideal
#check @Schubert.Splines.PolynomialGraph.upperFamily_ideal
#print axioms Schubert.Splines.PolynomialGraph.upperFamily_ideal

-- Remark 2.18 (`source-line-1098`)
#check @Schubert.Splines.PolynomialGraph.upper_matrix
#print axioms Schubert.Splines.PolynomialGraph.upper_matrix

-- Lemma 2.19 (`lem:upper_triangular`)
#check @Schubert.DihedralSplines.TriangularFamily.Left.basis
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.basis
#check @Schubert.DihedralSplines.TriangularFamily.Left.basis_apply
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.basis_apply
#check @Schubert.DihedralSplines.TriangularFamily.Left.minimal
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.minimal
#check @Schubert.DihedralSplines.TriangularFamily.Right.basis
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.basis
#check @Schubert.DihedralSplines.TriangularFamily.Right.basis_apply
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.basis_apply
#check @Schubert.DihedralSplines.TriangularFamily.Right.minimal
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.minimal
#check @Schubert.DihedralSplines.TriangularFamily.projectedValue_mem
#print axioms Schubert.DihedralSplines.TriangularFamily.projectedValue_mem
#check @Schubert.DihedralSplines.TriangularFamily.projectedValue_diagonal
#print axioms Schubert.DihedralSplines.TriangularFamily.projectedValue_diagonal
#check @Schubert.DihedralSplines.TriangularFamily.Left.piece_finrank
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.piece_finrank
#check @Schubert.DihedralSplines.TriangularFamily.Right.piece_finrank
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.piece_finrank
#check @Schubert.DihedralSplines.TriangularFamily.Left.rankPolynomial_eq
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.rankPolynomial_eq
#check @Schubert.DihedralSplines.TriangularFamily.Right.rankPolynomial_eq
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.rankPolynomial_eq
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.rankPolynomial_coeff
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.rankPolynomial_coeff
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.rankPolynomial_coeff
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.rankPolynomial_coeff

-- Definition 2.20 (`def:flowup`)
#check @Schubert.DihedralSplines.TriangularFamily.Left.IsFlowup
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.IsFlowup
#check @Schubert.DihedralSplines.TriangularFamily.Right.IsFlowup
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.IsFlowup
#check @Schubert.DihedralSplines.TriangularFamily.Left.isFlowup_iff
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.isFlowup_iff
#check @Schubert.DihedralSplines.TriangularFamily.Right.isFlowup_iff
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.isFlowup_iff
#check @Schubert.DihedralSplines.TriangularFamily.IsMember
#print axioms Schubert.DihedralSplines.TriangularFamily.IsMember
#check @Schubert.DihedralSplines.TriangularFamily.At
#print axioms Schubert.DihedralSplines.TriangularFamily.At
#check @Schubert.DihedralSplines.TriangularFamily.family_at
#print axioms Schubert.DihedralSplines.TriangularFamily.family_at
#check @Schubert.DihedralSplines.TriangularFamily.at_least
#print axioms Schubert.DihedralSplines.TriangularFamily.at_least
#check @Schubert.DihedralSplines.TriangularFamily.Left.member_iff
#print axioms Schubert.DihedralSplines.TriangularFamily.Left.member_iff
#check @Schubert.DihedralSplines.TriangularFamily.Right.member_iff
#print axioms Schubert.DihedralSplines.TriangularFamily.Right.member_iff

-- Definition 2.21 (`source-line-1144`)
#check @Schubert.Dihedral.RootSubset.dot
#print axioms Schubert.Dihedral.RootSubset.dot
#check @Schubert.Dihedral.RootSubset.dot_apply
#print axioms Schubert.Dihedral.RootSubset.dot_apply
#check @Schubert.Dihedral.RootSubset.dot_one
#print axioms Schubert.Dihedral.RootSubset.dot_one
#check @Schubert.Dihedral.RootSubset.dot_mul
#print axioms Schubert.Dihedral.RootSubset.dot_mul
#check @Schubert.Dihedral.RootSubset.dotAction
#print axioms Schubert.Dihedral.RootSubset.dotAction

-- Lemma 2.22 (`lem:dot_action_preserves_splines`)
-- `Schubert.Dihedral.RootSubset.dot`: printed above
-- `Schubert.Dihedral.RootSubset.dot_apply`: printed above

-- Equation (6) (`eqndef:left_quotient`)
#check @Schubert.Dihedral.RootSubset.Left.ideal_span
#print axioms Schubert.Dihedral.RootSubset.Left.ideal_span
#check @Schubert.Dihedral.RootSubset.Left.ideal_smul_top
#print axioms Schubert.Dihedral.RootSubset.Left.ideal_smul_top
#check @Schubert.Dihedral.RootSubset.Left.Quotient
#print axioms Schubert.Dihedral.RootSubset.Left.Quotient
#check @Schubert.Dihedral.RootSubset.Left.quotientMap
#print axioms Schubert.Dihedral.RootSubset.Left.quotientMap
#check @Schubert.Dihedral.RootSubset.Left.backendEquiv_map
#print axioms Schubert.Dihedral.RootSubset.Left.backendEquiv_map
#check @Schubert.Dihedral.RootSubset.Left.piece
#print axioms Schubert.Dihedral.RootSubset.Left.piece
#check @Schubert.Dihedral.RootSubset.Left.gradedAlgebra
#print axioms Schubert.Dihedral.RootSubset.Left.gradedAlgebra
#check @Schubert.Dihedral.RootSubset.Left.dot_map
#print axioms Schubert.Dihedral.RootSubset.Left.dot_map
#check @Schubert.Dihedral.RootSubset.Left.pieceRepresentation
#print axioms Schubert.Dihedral.RootSubset.Left.pieceRepresentation

-- Equation (7) (`eqndef:right_quotient`)
#check @Schubert.Dihedral.RootSubset.Right.ideal_span
#print axioms Schubert.Dihedral.RootSubset.Right.ideal_span
#check @Schubert.Dihedral.RootSubset.Right.ideal_smul_top
#print axioms Schubert.Dihedral.RootSubset.Right.ideal_smul_top
#check @Schubert.Dihedral.RootSubset.Right.Quotient
#print axioms Schubert.Dihedral.RootSubset.Right.Quotient
#check @Schubert.Dihedral.RootSubset.Right.quotientMap
#print axioms Schubert.Dihedral.RootSubset.Right.quotientMap
#check @Schubert.Dihedral.RootSubset.Right.backendEquiv_map
#print axioms Schubert.Dihedral.RootSubset.Right.backendEquiv_map
#check @Schubert.Dihedral.RootSubset.Right.piece
#print axioms Schubert.Dihedral.RootSubset.Right.piece
#check @Schubert.Dihedral.RootSubset.Right.gradedAlgebra
#print axioms Schubert.Dihedral.RootSubset.Right.gradedAlgebra
#check @Schubert.Dihedral.RootSubset.Right.dot_map
#print axioms Schubert.Dihedral.RootSubset.Right.dot_map
#check @Schubert.Dihedral.RootSubset.Right.pieceRepresentation
#print axioms Schubert.Dihedral.RootSubset.Right.pieceRepresentation

-- Lemma 3.1 (`lem:left_edges_full_graph`)
#check @Schubert.Dihedral.RootSubset.full_iff_left
#print axioms Schubert.Dihedral.RootSubset.full_iff_left
#check @Schubert.DihedralSplines.HessenbergIdeal.full_iff_left
#print axioms Schubert.DihedralSplines.HessenbergIdeal.full_iff_left

-- Equation (8) (`eq:left_spline_condition_full`)
#check @Schubert.Dihedral.RootSubset.full_algebra_eq
#print axioms Schubert.Dihedral.RootSubset.full_algebra_eq
#check @Schubert.DihedralSplines.HessenbergIdeal.full_algebra_eq
#print axioms Schubert.DihedralSplines.HessenbergIdeal.full_algebra_eq

-- Lemma 3.2 (`lem:divided_difference_spline`)
#check @Schubert.DihedralSplines.SchubertSpline.full_edge
#print axioms Schubert.DihedralSplines.SchubertSpline.full_edge
#check @Schubert.DihedralSplines.SchubertSpline.difference
#print axioms Schubert.DihedralSplines.SchubertSpline.difference
#check @Schubert.DihedralSplines.SchubertSpline.difference_mul
#print axioms Schubert.DihedralSplines.SchubertSpline.difference_mul

-- Equation (9) (`eq:divided_difference_spline`)
-- `Schubert.DihedralSplines.SchubertSpline.difference`: printed above
-- `Schubert.DihedralSplines.SchubertSpline.difference_mul`: printed above

-- Equation (10) (`eq:top_schubert_spline`)
#check @Schubert.DihedralSplines.SchubertSpline.top
#print axioms Schubert.DihedralSplines.SchubertSpline.top
#check @Schubert.DihedralSplines.SchubertSpline.top_apply
#print axioms Schubert.DihedralSplines.SchubertSpline.top_apply
#check @Schubert.DihedralSplines.SchubertSpline.spline_top
#print axioms Schubert.DihedralSplines.SchubertSpline.spline_top

-- Equation (11) (`eq:schubert_recursion`)
#check @Schubert.DihedralSplines.SchubertSpline.spline_one
#print axioms Schubert.DihedralSplines.SchubertSpline.spline_one
-- `Schubert.DihedralSplines.SchubertSpline.spline_top`: printed above
#check @Schubert.DihedralSplines.SchubertSpline.spline_step
#print axioms Schubert.DihedralSplines.SchubertSpline.spline_step
#check @Schubert.DihedralSplines.SchubertSpline.ascentRoot_spec
#print axioms Schubert.DihedralSplines.SchubertSpline.ascentRoot_spec
#check @Schubert.DihedralSplines.SchubertSpline.ascentRoot_eq
#print axioms Schubert.DihedralSplines.SchubertSpline.ascentRoot_eq

-- Proposition 3.3 (`prop:schubert_flowup`)
#check @Schubert.DihedralSplines.SchubertSpline.homogeneous
#print axioms Schubert.DihedralSplines.SchubertSpline.homogeneous
#check @Schubert.DihedralSplines.SchubertSpline.support
#print axioms Schubert.DihedralSplines.SchubertSpline.support
#check @Schubert.DihedralSplines.SchubertSpline.diagonal_product
#print axioms Schubert.DihedralSplines.SchubertSpline.diagonal_product
#check @Schubert.DihedralSplines.SchubertSpline.degree
#print axioms Schubert.DihedralSplines.SchubertSpline.degree

-- Equation (12) (`eq:schubert_diagonal_value`)
#check @Schubert.DihedralSplines.SchubertSpline.diagonalProduct
#print axioms Schubert.DihedralSplines.SchubertSpline.diagonalProduct
-- `Schubert.DihedralSplines.SchubertSpline.diagonal_product`: printed above

-- Theorem 3.4 (`thm:schubert_rational`)
#check @Schubert.DihedralSplines.SchubertSpline.rationalRoots
#print axioms Schubert.DihedralSplines.SchubertSpline.rationalRoots
#check @Schubert.DihedralSplines.SchubertSpline.rationalProduct
#print axioms Schubert.DihedralSplines.SchubertSpline.rationalProduct
#check @Schubert.DihedralSplines.SchubertSpline.rational_formula
#print axioms Schubert.DihedralSplines.SchubertSpline.rational_formula
#check @Schubert.DihedralSplines.SchubertSpline.support_exact
#print axioms Schubert.DihedralSplines.SchubertSpline.support_exact

-- Unnumbered statement, Section 3 (The Schubert case) (`unlabeled:root-form-nonproportionality`)
#check @Schubert.Dihedral.PositiveRoot.form_ne_zero
#print axioms Schubert.Dihedral.PositiveRoot.form_ne_zero
#check @Schubert.Dihedral.PositiveRoot.form_not_proportional
#print axioms Schubert.Dihedral.PositiveRoot.form_not_proportional
#check @Schubert.Dihedral.PositiveRoot.form_not_associated
#print axioms Schubert.Dihedral.PositiveRoot.form_not_associated
#check @Schubert.Dihedral.PositiveRoot.form_relPrime
#print axioms Schubert.Dihedral.PositiveRoot.form_relPrime
#check @Schubert.Dihedral.PositiveRoot.action_not_proportional
#print axioms Schubert.Dihedral.PositiveRoot.action_not_proportional
#check @Schubert.Dihedral.PositiveRoot.action_not_associated
#print axioms Schubert.Dihedral.PositiveRoot.action_not_associated
#check @Schubert.Dihedral.PositiveRoot.action_relPrime
#print axioms Schubert.Dihedral.PositiveRoot.action_relPrime

-- Proposition 3.5 (`prop:schubert_basis`)
#check @Schubert.DihedralSplines.SchubertSpline.left_basis
#print axioms Schubert.DihedralSplines.SchubertSpline.left_basis
#check @Schubert.DihedralSplines.SchubertSpline.right_basis
#print axioms Schubert.DihedralSplines.SchubertSpline.right_basis
#check @Schubert.DihedralSplines.SchubertSpline.homogeneous_basis
#print axioms Schubert.DihedralSplines.SchubertSpline.homogeneous_basis
-- `Schubert.DihedralSplines.SchubertSpline.degree`: printed above

-- Corollary 3.6 (`cor:schubert_hilbert_series`)
#check @Schubert.DihedralSplines.SchubertSpline.length_sum
#print axioms Schubert.DihedralSplines.SchubertSpline.length_sum
#check @Schubert.DihedralSplines.SchubertSpline.length_factor
#print axioms Schubert.DihedralSplines.SchubertSpline.length_factor
#check @Schubert.DihedralSplines.SchubertSpline.hilbert_formula
#print axioms Schubert.DihedralSplines.SchubertSpline.hilbert_formula

-- Lemma 3.7 (`lem:borel_presentation_schubert_splines`)
#check @Schubert.DihedralSplines.borelEquiv
#print axioms Schubert.DihedralSplines.borelEquiv
#check @Schubert.DihedralSplines.borelEquiv_tmul
#print axioms Schubert.DihedralSplines.borelEquiv_tmul
#check @Schubert.DihedralSplines.borelTensorPiece
#print axioms Schubert.DihedralSplines.borelTensorPiece
#check @Schubert.DihedralSplines.borelTensorPiece_map
#print axioms Schubert.DihedralSplines.borelTensorPiece_map
#check @Schubert.DihedralSplines.borelEquiv_xLeft
#print axioms Schubert.DihedralSplines.borelEquiv_xLeft
#check @Schubert.DihedralSplines.borelEquiv_yLeft
#print axioms Schubert.DihedralSplines.borelEquiv_yLeft
#check @Schubert.DihedralSplines.borelEquiv_xRight
#print axioms Schubert.DihedralSplines.borelEquiv_xRight
#check @Schubert.DihedralSplines.borelEquiv_yRight
#print axioms Schubert.DihedralSplines.borelEquiv_yRight
#check @Schubert.DihedralSplines.borelEquiv_dot
#print axioms Schubert.DihedralSplines.borelEquiv_dot

-- Equation (13) (`eq:borel_presentation_schubert_splines`)
-- `Schubert.DihedralSplines.borelEquiv`: printed above
-- `Schubert.DihedralSplines.borelEquiv_tmul`: printed above

-- Unnumbered statement, Section 3 (The Schubert case) (`unlabeled:fixed-field-galois-step`)
#check @Schubert.Dihedral.first_tensor_localization
#print axioms Schubert.Dihedral.first_tensor_localization
#check @Schubert.Dihedral.second_tensor_unit
#print axioms Schubert.Dihedral.second_tensor_unit
#check @Schubert.Dihedral.fraction_localization
#print axioms Schubert.Dihedral.fraction_localization
#check @Schubert.Dihedral.fraction_fixed_subfield
#print axioms Schubert.Dihedral.fraction_fixed_subfield
#check @Schubert.Dihedral.fraction_fixed_galois
#print axioms Schubert.Dihedral.fraction_fixed_galois
#check @Schubert.Dihedral.fraction_fixed_isGalois
#print axioms Schubert.Dihedral.fraction_fixed_isGalois
#check @Schubert.Dihedral.fixedTensorEquiv
#print axioms Schubert.Dihedral.fixedTensorEquiv
#check @Schubert.Dihedral.fixedTensorEquiv_tmul
#print axioms Schubert.Dihedral.fixedTensorEquiv_tmul
#check @Schubert.Dihedral.polynomialFixedEquiv
#print axioms Schubert.Dihedral.polynomialFixedEquiv
#check @Schubert.Dihedral.polynomialFixedEquiv_tmul
#print axioms Schubert.Dihedral.polynomialFixedEquiv_tmul
#check @Schubert.Dihedral.fractionPolynomialEquiv
#print axioms Schubert.Dihedral.fractionPolynomialEquiv
#check @Schubert.Dihedral.fractionPolynomialEquiv_tmul
#print axioms Schubert.Dihedral.fractionPolynomialEquiv_tmul
#check @Schubert.Dihedral.tensorEvaluation_localized
#print axioms Schubert.Dihedral.tensorEvaluation_localized
#check @Schubert.DihedralSplines.borelHom_injective
#print axioms Schubert.DihedralSplines.borelHom_injective

-- Unnumbered statement, Section 3 (The Schubert case) (`unlabeled:invariants-and-freeness`)
#check @Schubert.Dihedral.Invariants.eq_generator_adjoin
#print axioms Schubert.Dihedral.Invariants.eq_generator_adjoin
#check @Schubert.Dihedral.basicInvariants_algebraicIndependent
#print axioms Schubert.Dihedral.basicInvariants_algebraicIndependent
#check @Schubert.Dihedral.nonempty_invariantPolynomialEquiv
#print axioms Schubert.Dihedral.nonempty_invariantPolynomialEquiv
#check @Schubert.Dihedral.Invariants.polynomial_free
#print axioms Schubert.Dihedral.Invariants.polynomial_free
#check @Schubert.Dihedral.Invariants.polynomial_finrank
#print axioms Schubert.Dihedral.Invariants.polynomial_finrank
#check @Schubert.Dihedral.coinvariantAlgebra_finite
#print axioms Schubert.Dihedral.coinvariantAlgebra_finite
#check @Schubert.Dihedral.quadraticInvariant_totalDegree
#print axioms Schubert.Dihedral.quadraticInvariant_totalDegree
#check @Schubert.Dihedral.higherInvariant_totalDegree
#print axioms Schubert.Dihedral.higherInvariant_totalDegree
#check @Schubert.Dihedral.Coinvariant.regular_iso
#print axioms Schubert.Dihedral.Coinvariant.regular_iso

-- Proposition 3.8 (`prop:left_schubert_rep`)
#check @Schubert.DihedralSplines.SchubertSpline.left_class_coeff
#print axioms Schubert.DihedralSplines.SchubertSpline.left_class_coeff
#check @Schubert.DihedralSplines.SchubertSpline.left_class_polynomial
#print axioms Schubert.DihedralSplines.SchubertSpline.left_class_polynomial
#check @Schubert.DihedralSplines.SchubertSpline.left_class_length_sum
#print axioms Schubert.DihedralSplines.SchubertSpline.left_class_length_sum
#check @Schubert.DihedralSplines.SchubertSpline.left_class_geometric
#print axioms Schubert.DihedralSplines.SchubertSpline.left_class_geometric
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.full_piece_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.full_piece_iso

-- Proposition 3.9 (`prop:right_schubert_rep`)
#check @Schubert.DihedralSplines.SchubertSpline.right_piece_iso
#print axioms Schubert.DihedralSplines.SchubertSpline.right_piece_iso
#check @Schubert.DihedralSplines.SchubertSpline.right_class_coinvariant
#print axioms Schubert.DihedralSplines.SchubertSpline.right_class_coinvariant
#check @Schubert.DihedralSplines.SchubertSpline.right_class_coeff
#print axioms Schubert.DihedralSplines.SchubertSpline.right_class_coeff
#check @Schubert.DihedralSplines.SchubertSpline.right_character_degree
#print axioms Schubert.DihedralSplines.SchubertSpline.right_character_degree
#check @Schubert.DihedralSplines.SchubertSpline.rightTrace
#print axioms Schubert.DihedralSplines.SchubertSpline.rightTrace
#check @Schubert.DihedralSplines.SchubertSpline.rightTrace_determinant
#print axioms Schubert.DihedralSplines.SchubertSpline.rightTrace_determinant
#check @Schubert.DihedralSplines.SchubertSpline.rightTrace_formula
#print axioms Schubert.DihedralSplines.SchubertSpline.rightTrace_formula
#check @Schubert.DihedralSplines.SchubertSpline.rightTrace_one
#print axioms Schubert.DihedralSplines.SchubertSpline.rightTrace_one
#check @Schubert.DihedralSplines.SchubertSpline.polynomial_one_iso
#print axioms Schubert.DihedralSplines.SchubertSpline.polynomial_one_iso
#check @Schubert.Dihedral.vectorDenominator
#print axioms Schubert.Dihedral.vectorDenominator

-- Remark 3.10 (`source-line-1624`)
#check @Schubert.DihedralSplines.SchubertSpline.full_piece_finrank_eq
#print axioms Schubert.DihedralSplines.SchubertSpline.full_piece_finrank_eq
#check @Schubert.DihedralSplines.SchubertSpline.full_piece_linearEquiv
#print axioms Schubert.DihedralSplines.SchubertSpline.full_piece_linearEquiv
#check @Schubert.DihedralSplines.SchubertSpline.full_piece_not_iso
#print axioms Schubert.DihedralSplines.SchubertSpline.full_piece_not_iso
-- `Schubert.DihedralSplines.borelEquiv_dot`: printed above
-- `Schubert.DihedralSplines.borelEquiv_xLeft`: printed above
-- `Schubert.DihedralSplines.borelEquiv_yLeft`: printed above
-- `Schubert.DihedralSplines.borelEquiv_xRight`: printed above
-- `Schubert.DihedralSplines.borelEquiv_yRight`: printed above
#check @Schubert.DihedralSplines.fullCoinvariantEquiv_mk
#print axioms Schubert.DihedralSplines.fullCoinvariantEquiv_mk
#check @Schubert.DihedralSplines.fullCoinvariantEquiv_equivariant
#print axioms Schubert.DihedralSplines.fullCoinvariantEquiv_equivariant
#check @Schubert.DihedralSplines.fullCoinvariantPieceEquiv
#print axioms Schubert.DihedralSplines.fullCoinvariantPieceEquiv
#check @Schubert.Dihedral.RootSubset.Left.coordinate_zero
#print axioms Schubert.Dihedral.RootSubset.Left.coordinate_zero
#check @Schubert.Dihedral.RootSubset.Right.coordinate_zero
#print axioms Schubert.Dihedral.RootSubset.Right.coordinate_zero

-- Remark 3.11 (`source-line-1633`)
#check @Schubert.Dihedral.DoubleCoinvariant.relations_invariants
#print axioms Schubert.Dihedral.DoubleCoinvariant.relations_invariants
#check @Schubert.Dihedral.DoubleCoinvariant.tensorEquiv
#print axioms Schubert.Dihedral.DoubleCoinvariant.tensorEquiv
#check @Schubert.Dihedral.DoubleCoinvariant.scalarEquiv
#print axioms Schubert.Dihedral.DoubleCoinvariant.scalarEquiv
#check @Schubert.Dihedral.DoubleCoinvariant.tensorEquiv_first
#print axioms Schubert.Dihedral.DoubleCoinvariant.tensorEquiv_first
#check @Schubert.Dihedral.DoubleCoinvariant.tensorEquiv_second
#print axioms Schubert.Dihedral.DoubleCoinvariant.tensorEquiv_second
#check @Schubert.DihedralSplines.DoubleCoinvariant.localization
#print axioms Schubert.DihedralSplines.DoubleCoinvariant.localization
#check @Schubert.DihedralSplines.DoubleCoinvariant.schubert_basis
#print axioms Schubert.DihedralSplines.DoubleCoinvariant.schubert_basis
#check @Schubert.DihedralSplines.DoubleCoinvariant.localization_image
#print axioms Schubert.DihedralSplines.DoubleCoinvariant.localization_image
#check @Schubert.DihedralSplines.DoubleCoinvariant.localization_inverse
#print axioms Schubert.DihedralSplines.DoubleCoinvariant.localization_inverse
#check @Schubert.DihedralSplines.DoubleCoinvariant.root_form_real
#print axioms Schubert.DihedralSplines.DoubleCoinvariant.root_form_real
#check @Schubert.Dihedral.polynomialAction_inverse_X
#print axioms Schubert.Dihedral.polynomialAction_inverse_X
#check @Schubert.Dihedral.inverseCoordinate_eval
#print axioms Schubert.Dihedral.inverseCoordinate_eval

-- Lemma 4.1 (`lem:generalized_divided_difference`)
#check @Schubert.DihedralSplines.HessenbergIdeal.dividedDifference
#print axioms Schubert.DihedralSplines.HessenbergIdeal.dividedDifference
#check @Schubert.DihedralSplines.HessenbergIdeal.dividedDifference_mul
#print axioms Schubert.DihedralSplines.HessenbergIdeal.dividedDifference_mul
#check @Schubert.DihedralSplines.HessenbergIdeal.dividedDifference_unique
#print axioms Schubert.DihedralSplines.HessenbergIdeal.dividedDifference_unique

-- Equation (14) (`eq:divided_difference`)
-- `Schubert.DihedralSplines.HessenbergIdeal.dividedDifference`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.dividedDifference_mul`: printed above

-- Lemma 4.2 (`lem:leftright_length`)
#check @Schubert.Dihedral.PositiveRoot.ascent_length
#print axioms Schubert.Dihedral.PositiveRoot.ascent_length
#check @Schubert.Dihedral.PositiveRoot.descent_length
#print axioms Schubert.Dihedral.PositiveRoot.descent_length

-- Lemma 4.3 (`lem:simple_degree_changes`)
#check @Schubert.DihedralSplines.HessenbergIdeal.inversions_no_edge
#print axioms Schubert.DihedralSplines.HessenbergIdeal.inversions_no_edge
#check @Schubert.DihedralSplines.HessenbergIdeal.length_edge
#print axioms Schubert.DihedralSplines.HessenbergIdeal.length_edge
#check @Schubert.DihedralSplines.HessenbergIdeal.edge_range
#print axioms Schubert.DihedralSplines.HessenbergIdeal.edge_range
#check @Schubert.DihedralSplines.HessenbergIdeal.length_full
#print axioms Schubert.DihedralSplines.HessenbergIdeal.length_full

-- Corollary 4.4 (`cor:existence_upper_elts`)
#check @Schubert.DihedralSplines.FlowupSpline.spline
#print axioms Schubert.DihedralSplines.FlowupSpline.spline
#check @Schubert.DihedralSplines.FlowupSpline.degree
#print axioms Schubert.DihedralSplines.FlowupSpline.degree
#check @Schubert.DihedralSplines.FlowupSpline.support
#print axioms Schubert.DihedralSplines.FlowupSpline.support
#check @Schubert.DihedralSplines.FlowupSpline.diagonal
#print axioms Schubert.DihedralSplines.FlowupSpline.diagonal
-- `Schubert.DihedralSplines.FlowupSpline.Left.basis_apply`: printed above
-- `Schubert.DihedralSplines.FlowupSpline.Right.basis_apply`: printed above
-- `Schubert.DihedralSplines.TriangularFamily.family_at`: printed above

-- Equation (15) (`eq:top_spline`)
#check @Schubert.DihedralSplines.HessenbergIdeal.topSpline
#print axioms Schubert.DihedralSplines.HessenbergIdeal.topSpline
#check @Schubert.DihedralSplines.HessenbergIdeal.topSpline_apply
#print axioms Schubert.DihedralSplines.HessenbergIdeal.topSpline_apply
#check @Schubert.DihedralSplines.HessenbergIdeal.topSpline_nonzero
#print axioms Schubert.DihedralSplines.HessenbergIdeal.topSpline_nonzero
#check @Schubert.DihedralSplines.HessenbergIdeal.topSpline_mem_piece
#print axioms Schubert.DihedralSplines.HessenbergIdeal.topSpline_mem_piece
#check @Schubert.DihedralSplines.HessenbergIdeal.topSpline_support
#print axioms Schubert.DihedralSplines.HessenbergIdeal.topSpline_support

-- Theorem 4.5 (`thm:flowup`)
#check @Schubert.DihedralSplines.FlowupSpline.family
#print axioms Schubert.DihedralSplines.FlowupSpline.family
-- `Schubert.DihedralSplines.FlowupSpline.degree`: printed above
-- `Schubert.DihedralSplines.FlowupSpline.support`: printed above
-- `Schubert.DihedralSplines.FlowupSpline.diagonal`: printed above
-- `Schubert.DihedralSplines.FlowupSpline.Left.basis_apply`: printed above
-- `Schubert.DihedralSplines.FlowupSpline.Right.basis_apply`: printed above
#check @Schubert.DihedralSplines.FlowupSpline.spline_one
#print axioms Schubert.DihedralSplines.FlowupSpline.spline_one
#check @Schubert.DihedralSplines.FlowupSpline.spline_top
#print axioms Schubert.DihedralSplines.FlowupSpline.spline_top
#check @Schubert.DihedralSplines.FlowupSpline.spline_low
#print axioms Schubert.DihedralSplines.FlowupSpline.spline_low
#check @Schubert.DihedralSplines.FlowupSpline.spline_high
#print axioms Schubert.DihedralSplines.FlowupSpline.spline_high
#check @Schubert.DihedralSplines.FlowupSpline.spline_no_edge
#print axioms Schubert.DihedralSplines.FlowupSpline.spline_no_edge

-- Example 4.6 (`ex:generators_exist`)
#check @Schubert.DihedralSplines.Pentagon.generator
#print axioms Schubert.DihedralSplines.Pentagon.generator
#check @Schubert.DihedralSplines.Pentagon.initial_formulas
#print axioms Schubert.DihedralSplines.Pentagon.initial_formulas
#check @Schubert.DihedralSplines.Pentagon.operator_formulas
#print axioms Schubert.DihedralSplines.Pentagon.operator_formulas
#check @Schubert.DihedralSplines.Pentagon.certificates
#print axioms Schubert.DihedralSplines.Pentagon.certificates
#check @Schubert.DihedralSplines.Pentagon.whole_degrees
#print axioms Schubert.DihedralSplines.Pentagon.whole_degrees
#check @Schubert.DihedralSplines.Pentagon.family_vertex
#print axioms Schubert.DihedralSplines.Pentagon.family_vertex
#check @Schubert.DihedralSplines.Pentagon.bases
#print axioms Schubert.DihedralSplines.Pentagon.bases
#check @Schubert.DihedralSplines.Pentagon.left_rank
#print axioms Schubert.DihedralSplines.Pentagon.left_rank
#check @Schubert.DihedralSplines.Pentagon.right_rank
#print axioms Schubert.DihedralSplines.Pentagon.right_rank
#check @Schubert.DihedralSplines.Pentagon.generator_eq_spline
#print axioms Schubert.DihedralSplines.Pentagon.generator_eq_spline
#check @Schubert.DihedralSplines.Pentagon.edges
#print axioms Schubert.DihedralSplines.Pentagon.edges
#check @Schubert.DihedralSplines.Pentagon.edge_labels
#print axioms Schubert.DihedralSplines.Pentagon.edge_labels
#check @Schubert.DihedralSplines.Pentagon.top_values
#print axioms Schubert.DihedralSplines.Pentagon.top_values

-- Corollary 4.7 (`cor:rank_gf`)
#check @Schubert.DihedralSplines.HessenbergIdeal.lengthPolynomial_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.lengthPolynomial_even
#check @Schubert.DihedralSplines.HessenbergIdeal.lengthPolynomial_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.lengthPolynomial_odd
#check @Schubert.DihedralSplines.HessenbergIdeal.lengthPolynomial_reverse
#print axioms Schubert.DihedralSplines.HessenbergIdeal.lengthPolynomial_reverse
#check @Schubert.DihedralSplines.FlowupSpline.Left.rank_eq
#print axioms Schubert.DihedralSplines.FlowupSpline.Left.rank_eq
#check @Schubert.DihedralSplines.FlowupSpline.Right.rank_eq
#print axioms Schubert.DihedralSplines.FlowupSpline.Right.rank_eq
#check @Schubert.DihedralSplines.HessenbergIdeal.hilbertSeries_formula
#print axioms Schubert.DihedralSplines.HessenbergIdeal.hilbertSeries_formula
#check @Schubert.DihedralSplines.HessenbergIdeal.coeff_piecewise
#print axioms Schubert.DihedralSplines.HessenbergIdeal.coeff_piecewise

-- Lemma 5.1 (`lem:regular`)
#check @Schubert.DihedralSplines.HessenbergIdeal.first_regular
#print axioms Schubert.DihedralSplines.HessenbergIdeal.first_regular
#check @Schubert.DihedralSplines.HessenbergIdeal.second_regular
#print axioms Schubert.DihedralSplines.HessenbergIdeal.second_regular
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.edge
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.edge
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.boundary_card
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.boundary_card
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.eq_of_edges
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.eq_of_edges

-- Corollary 5.2 (`cor:rationally_smooth`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.first
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.first
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.second
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.second
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.localized
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.localized
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.localized_function
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.localized_function
#check @Schubert.DihedralSplines.HessenbergIdeal.Block.normalized_unique
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Block.normalized_unique

-- Proposition 5.3 (`prop:flowup_explicit_setup`)
#check @Schubert.DihedralSplines.FlowupSpline.block_shape
#print axioms Schubert.DihedralSplines.FlowupSpline.block_shape
#check @Schubert.DihedralSplines.FlowupSpline.high_block
#print axioms Schubert.DihedralSplines.FlowupSpline.high_block
#check @Schubert.DihedralSplines.FlowupSpline.homogeneous
#print axioms Schubert.DihedralSplines.FlowupSpline.homogeneous
-- `Schubert.DihedralSplines.FlowupSpline.diagonal`: printed above
-- `Schubert.DihedralSplines.FlowupSpline.spline_top`: printed above

-- Proposition 5.4 (`prop:linear_independence`)
#check @Schubert.Dihedral.RootSubset.AlternatingBlocks
#print axioms Schubert.Dihedral.RootSubset.AlternatingBlocks
#check @Schubert.Dihedral.RootSubset.independent
#print axioms Schubert.Dihedral.RootSubset.independent
#check @Schubert.Dihedral.RootSubset.boundaryFunction
#print axioms Schubert.Dihedral.RootSubset.boundaryFunction
#check @Schubert.Dihedral.length_rootReflection
#print axioms Schubert.Dihedral.length_rootReflection

-- Corollary 5.5 (`cor:admissible_block_independence`)
#check @Schubert.DihedralSplines.HessenbergIdeal.AdmissibleBlocks
#print axioms Schubert.DihedralSplines.HessenbergIdeal.AdmissibleBlocks
#check @Schubert.DihedralSplines.HessenbergIdeal.admissible_iff
#print axioms Schubert.DihedralSplines.HessenbergIdeal.admissible_iff
#check @Schubert.DihedralSplines.HessenbergIdeal.admissible_independent
#print axioms Schubert.DihedralSplines.HessenbergIdeal.admissible_independent

-- Equation (16) (`eq:Ph_representation`)
#check @Schubert.Dihedral.Frequency.partialSum
#print axioms Schubert.Dihedral.Frequency.partialSum
#check @Schubert.Dihedral.Frequency.partialSum_zero
#print axioms Schubert.Dihedral.Frequency.partialSum_zero
#check @Schubert.Dihedral.Frequency.partialSum_succ
#print axioms Schubert.Dihedral.Frequency.partialSum_succ
#check @Schubert.Dihedral.Frequency.partialSum_terms_simple
#print axioms Schubert.Dihedral.Frequency.partialSum_terms_simple

-- Remark 6.1 (`source-line-2170`)
#check @Schubert.Dihedral.Frequency.partialSum_finrank
#print axioms Schubert.Dihedral.Frequency.partialSum_finrank
#check @Schubert.Dihedral.Frequency.partialSum_split_class
#print axioms Schubert.Dihedral.Frequency.partialSum_split_class
#check @Schubert.Dihedral.PositiveRoot.coset_odd_complement
#print axioms Schubert.Dihedral.PositiveRoot.coset_odd_complement
#check @Schubert.Dihedral.PositiveRoot.coset_even_complement
#print axioms Schubert.Dihedral.PositiveRoot.coset_even_complement
-- `Schubert.Dihedral.PositiveRoot.coset_odd_iso`: printed above
-- `Schubert.Dihedral.PositiveRoot.coset_even_iso`: printed above
-- `Schubert.Dihedral.PositiveRoot.coset_odd_class`: printed above
-- `Schubert.Dihedral.PositiveRoot.coset_even_class`: printed above

-- Definition 6.2 (`def:H_dominant`)
#check @Schubert.DihedralSplines.HessenbergIdeal.IsDominant
#print axioms Schubert.DihedralSplines.HessenbergIdeal.IsDominant
#check @Schubert.DihedralSplines.HessenbergIdeal.isDominant_indexed
#print axioms Schubert.DihedralSplines.HessenbergIdeal.isDominant_indexed

-- Remark 6.3 (`source-line-2176`)
#check @Schubert.DihedralSplines.HessenbergIdeal.dominant_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.dominant_even
#check @Schubert.DihedralSplines.HessenbergIdeal.dominant_odd_unique
#print axioms Schubert.DihedralSplines.HessenbergIdeal.dominant_odd_unique
#check @Schubert.DihedralSplines.HessenbergIdeal.odd_choices
#print axioms Schubert.DihedralSplines.HessenbergIdeal.odd_choices
#check @Schubert.DihedralSplines.HessenbergIdeal.odd_choice
#print axioms Schubert.DihedralSplines.HessenbergIdeal.odd_choice
#check @Schubert.DihedralSplines.HessenbergIdeal.odd_choice_whole
#print axioms Schubert.DihedralSplines.HessenbergIdeal.odd_choice_whole
#check @Schubert.DihedralSplines.HessenbergIdeal.odd_choices_whole
#print axioms Schubert.DihedralSplines.HessenbergIdeal.odd_choices_whole

-- Theorem 6.4 (`thm:left_representation`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_even`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_odd`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.class_palindromic`: printed above

-- Equation (17) (`eq:left_hessenberg_representation`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_even`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.graded_class_odd`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.class_palindromic`: printed above

-- Remark 6.5 (`source-line-2200`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_rank
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_rank
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_length
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_length
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_even
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.dimension_odd
#check @Schubert.FiniteGroupCharacters.dimensionHom
#print axioms Schubert.FiniteGroupCharacters.dimensionHom
#check @Schubert.FiniteGroupCharacters.dimensionHom_of
#print axioms Schubert.FiniteGroupCharacters.dimensionHom_of
#check @Schubert.FiniteGroupCharacters.graded_dimension_coeff
#print axioms Schubert.FiniteGroupCharacters.graded_dimension_coeff

-- Example 6.6 (`source-line-2203`)
#check @Schubert.DihedralSplines.SchubertSpline.full_odd_class
#print axioms Schubert.DihedralSplines.SchubertSpline.full_odd_class
#check @Schubert.DihedralSplines.SchubertSpline.full_even_half
#print axioms Schubert.DihedralSplines.SchubertSpline.full_even_half
-- `Schubert.DihedralSplines.SchubertSpline.left_class_geometric`: printed above

-- Example 6.7 (`source-line-2213`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_middle
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_middle
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_odd
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.two_simple_even
#check @Schubert.Dihedral.Frequency.partialSum_after_one
#print axioms Schubert.Dihedral.Frequency.partialSum_after_one

-- Example 6.8 (`source-line-2253`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.withoutLast_class_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.withoutLast_class_even
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.withoutLast_class_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.withoutLast_class_odd

-- Unnumbered statement, Section 6 (The Left Representation) (`unlabeled:graded-equivariant-nakayama`)
#check @Schubert.Dihedral.RootSubset.Left.graded_section
#print axioms Schubert.Dihedral.RootSubset.Left.graded_section
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.tensor_free
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.tensor_free
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.degree_tensor_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.degree_tensor_iso

-- Equation (18) (`eq:left_equivariant_freeness`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.tensor_free`: printed above

-- Proposition 6.9 (`prop:left_quotient_duality`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.pairingActionEquiv
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.pairingActionEquiv
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_dual_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_dual_iso
#check @Schubert.DihedralSplines.FlowupSpline.Left.pairingEquiv
#print axioms Schubert.DihedralSplines.FlowupSpline.Left.pairingEquiv
#check @Schubert.DihedralSplines.FlowupSpline.Left.multiplication_nondegenerate
#print axioms Schubert.DihedralSplines.FlowupSpline.Left.multiplication_nondegenerate
#check @Schubert.DihedralSplines.FlowupSpline.Left.pairingEquiv_apply
#print axioms Schubert.DihedralSplines.FlowupSpline.Left.pairingEquiv_apply
#check @Schubert.DihedralSplines.FlowupSpline.Left.pairingEquiv_dot
#print axioms Schubert.DihedralSplines.FlowupSpline.Left.pairingEquiv_dot
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.top_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.top_iso
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_dual
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_dual

-- Equation (19) (`eq:left_representation_duality`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_dual`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Left.top_iso`: printed above
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.complementary_iso
#check @Schubert.Dihedral.self_dual
#print axioms Schubert.Dihedral.self_dual

-- Unnumbered statement, Section 6 (The Left Representation) (`unlabeled:dihedral-representations-self-dual`)
#check @Schubert.Dihedral.isConj_inv
#print axioms Schubert.Dihedral.isConj_inv
#check @Schubert.Dihedral.irreducible_self_dual
#print axioms Schubert.Dihedral.irreducible_self_dual
-- `Schubert.Dihedral.self_dual`: printed above

-- Lemma 6.10 (`lem:trivial_left_subreps`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialSource_embedding
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialSource_embedding
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialSubpiece_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialSubpiece_iso
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialRange
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialRange
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialRange_above
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialRange_above
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialGradedRepresentation_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialInclusion
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialInclusion
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivialInclusion_injective
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivialInclusion_injective
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.trivial_subrepresentation
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.trivial_subrepresentation

-- Equation (20) (`eq:left_middle_subtraction`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.middle_subtraction
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.middle_subtraction

-- Unnumbered statement, Section 6 (The Left Representation) (`unlabeled:low-degree-symmetric-power-decomposition`)
#check @Schubert.Dihedral.polynomialPiece_frequency_iso
#print axioms Schubert.Dihedral.polynomialPiece_frequency_iso
#check @Schubert.Dihedral.polynomialPiece_even_iso
#print axioms Schubert.Dihedral.polynomialPiece_even_iso
#check @Schubert.Dihedral.polynomialPiece_odd_iso
#print axioms Schubert.Dihedral.polynomialPiece_odd_iso
#check @Schubert.Dihedral.polynomialPiece_frequency_simple
#print axioms Schubert.Dihedral.polynomialPiece_frequency_simple
#check @Schubert.Dihedral.polynomial_weighted_class
#print axioms Schubert.Dihedral.polynomial_weighted_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.removed_weighted_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.removed_weighted_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Left.removed_frequency_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Left.removed_frequency_class

-- Corollary 6.11 (`cor:not_permutation`)
#check @Schubert.DihedralSplines.Pentagon.whole_class
#print axioms Schubert.DihedralSplines.Pentagon.whole_class
#check @Schubert.DihedralSplines.Pentagon.whole_iso
#print axioms Schubert.DihedralSplines.Pentagon.whole_iso
#check @Schubert.DihedralSplines.Pentagon.rotation_character
#print axioms Schubert.DihedralSplines.Pentagon.rotation_character
#check @Schubert.DihedralSplines.Pentagon.rotation_not_nat
#print axioms Schubert.DihedralSplines.Pentagon.rotation_not_nat
#check @Schubert.DihedralSplines.Pentagon.not_permutation
#print axioms Schubert.DihedralSplines.Pentagon.not_permutation

-- Equation (21) (`eq:right_equivariant_freeness`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.orbit_tensor_free
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.orbit_tensor_free
#check @Schubert.Dihedral.RootSubset.Right.scalar_range
#print axioms Schubert.Dihedral.RootSubset.Right.scalar_range
#check @Schubert.Dihedral.RootSubset.Right.scalarPiece_iso
#print axioms Schubert.Dihedral.RootSubset.Right.scalarPiece_iso

-- Proposition 7.1 (`prop:right_quotient_duality`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.pairingActionEquiv
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.pairingActionEquiv
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.complementary_dual_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.complementary_dual_iso
#check @Schubert.DihedralSplines.FlowupSpline.Right.pairingEquiv
#print axioms Schubert.DihedralSplines.FlowupSpline.Right.pairingEquiv
#check @Schubert.DihedralSplines.FlowupSpline.Right.multiplication_nondegenerate
#print axioms Schubert.DihedralSplines.FlowupSpline.Right.multiplication_nondegenerate
#check @Schubert.DihedralSplines.FlowupSpline.Right.pairingEquiv_apply
#print axioms Schubert.DihedralSplines.FlowupSpline.Right.pairingEquiv_apply
#check @Schubert.DihedralSplines.FlowupSpline.Right.pairingEquiv_dot
#print axioms Schubert.DihedralSplines.FlowupSpline.Right.pairingEquiv_dot
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.top_iso
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.top_iso
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.sign_complementary
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.sign_complementary

-- Equation (22) (`eq:right_representation_duality`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.sign_complementary`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.top_iso`: printed above

-- Lemma 7.2 (`lem:coinv_right_subreps`)
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.coRange
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.coRange
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.coRange_above
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.coRange_above
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation_class
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.coGradedRepresentation_class
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.coInclusion
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.coInclusion
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.coInclusion_injective
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.coInclusion_injective
#check @Schubert.DihedralSplines.HessenbergIdeal.Right.co_subrepresentation
#print axioms Schubert.DihedralSplines.HessenbergIdeal.Right.co_subrepresentation

-- Equation (23) (`eq:h_coinvariant`)
#check @Schubert.DihedralSplines.HessenbergIdeal.coClass
#print axioms Schubert.DihedralSplines.HessenbergIdeal.coClass
#check @Schubert.DihedralSplines.HessenbergIdeal.coClass_even
#print axioms Schubert.DihedralSplines.HessenbergIdeal.coClass_even
#check @Schubert.DihedralSplines.HessenbergIdeal.coClass_odd
#print axioms Schubert.DihedralSplines.HessenbergIdeal.coClass_odd

-- Theorem 7.3 (`thm:right_representation`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_even`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_odd`: printed above

-- Equation (24) (`eq:right_hessenberg_representation`)
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_even`: printed above
-- `Schubert.DihedralSplines.HessenbergIdeal.Right.graded_class_odd`: printed above
