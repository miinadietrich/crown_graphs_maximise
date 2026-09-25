import SupportAnalyticalSolution
import SupportFormulaSolution
import SupportPairingSolution
import Crown.Main
import Crown.SmallGraph
import NumericalSolution
import SupportCatalogueSolution
import SupportCertificateSolution
import SupportCNFSolution
import SupportProbabilitySolution
import SupportRankDetailSolution
import SupportRankSolution
import SupportReductionSolution
import SupportSymmetrySolution
import SupportTraversalSolution
import SupportWordSolution

namespace Crown

theorem small_bipartite_two_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hcard : Fintype.card V ≤ 6) :
    KRepresentable G 2 :=
  small_bipartite_two_uniform_proof G hb hcard

end Crown

#print axioms Crown.balanced_matrix_representation_bound
#print axioms Crown.bipartite_representation_bound
#print axioms Crown.bipartite_representation_number_bound
#print axioms Crown.crown_representation_number
#print axioms Crown.crown_extremal
#print axioms Crown.small_bipartite_two_uniform
#print axioms Crown.crown_extremal_uniform_length
#print axioms Crown.Numerical.Arithmetic.Q_mul_factorial
#print axioms Crown.Numerical.Arithmetic.Q_pos
#print axioms Crown.Numerical.Arithmetic.M_denominator_pos
#print axioms Crown.Numerical.Arithmetic.M_eq_zero_of_negative
#print axioms Crown.Numerical.Arithmetic.M_eq_zero_of_large_z
#print axioms Crown.Numerical.Arithmetic.P_eq_zero_of_two_le_t
#print axioms Crown.Numerical.Arithmetic.P_eq_zero_of_large_z
#print axioms Crown.Numerical.Arithmetic.finiteSliceMaximum_iff
#print axioms Crown.Numerical.Arithmetic.table60_exact
#print axioms Crown.Numerical.Arithmetic.table61_exact
#print axioms Crown.Numerical.Arithmetic.table70_exact
#print axioms Crown.Numerical.Arithmetic.table71_exact
#print axioms Crown.Numerical.Arithmetic.P6_le
#print axioms Crown.Numerical.Arithmetic.P7_le
#print axioms Crown.Numerical.Arithmetic.Q6
#print axioms Crown.Numerical.Arithmetic.Q7
#print axioms Crown.Numerical.Arithmetic.P6_maximum_attained
#print axioms Crown.Numerical.Arithmetic.P7_maximum_attained
#print axioms Crown.Numerical.Arithmetic.P6_ratio
#print axioms Crown.Numerical.Arithmetic.P7_ratio
#print axioms Crown.Numerical.Arithmetic.union6
#print axioms Crown.Numerical.Arithmetic.union7
#print axioms Crown.Numerical.Arithmetic.orientation_tail
#print axioms Crown.Numerical.Arithmetic.orientation_base
#print axioms Crown.Numerical.Arithmetic.orientation_ratio_lt
#print axioms Crown.Numerical.Arithmetic.choose_even_two
#print axioms Crown.Numerical.Arithmetic.orientation_count_lt
#print axioms Crown.Numerical.Arithmetic.Q5
#print axioms Crown.Numerical.Arithmetic.M_swap_xy
#print axioms Crown.Numerical.Arithmetic.M_swap_yz
#print axioms Crown.Numerical.Arithmetic.M_permutation
#print axioms Crown.Numerical.Arithmetic.pair_counts_five_coverage
#print axioms Crown.Numerical.Arithmetic.pair_counts_five_values
#print axioms Crown.Numerical.Arithmetic.pair_counts_five_permutations
#print axioms Crown.Numerical.Arithmetic.M5_complement_le
#print axioms Crown.Numerical.Arithmetic.M5_le
#print axioms Crown.Numerical.Arithmetic.M5_maximum_attained
#print axioms Crown.Numerical.Arithmetic.pair5_ratio
#print axioms Crown.Numerical.Arithmetic.triple_candidates_five
#print axioms Crown.Numerical.Arithmetic.triple_candidates_five_attained
#print axioms Crown.Numerical.Arithmetic.theta5
#print axioms Crown.Numerical.Arithmetic.union5
#print axioms Crown.Numerical.Arithmetic.small_parts_bound
#print axioms Crown.Numerical.Arithmetic.even_unbalanced_bound
#print axioms Crown.Numerical.Arithmetic.odd_unbalanced_bound
#print axioms Crown.Numerical.Arithmetic.odd_near_balanced_bound
#print axioms Crown.Numerical.Arithmetic.odd_near_balanced_parameter
#print axioms Crown.Numerical.Counting.exists_avoiding_of_sum_card_lt
#print axioms Crown.Numerical.Counting.exists_avoiding_of_bounds
#print axioms Crown.Numerical.Counting.exists_avoiding_of_uniform_bound
#print axioms Crown.Numerical.Counting.exists_avoiding_two_families
#print axioms Crown.Numerical.Counting.card_orientations
#print axioms Crown.Numerical.Counting.card_vertex_pairs
#print axioms Crown.Numerical.Counting.exists_good_orientation
#print axioms Crown.CertificateData.catalogueUnion_iff_minimal
#print axioms Crown.CertificateData.minimal_obstruction_union_count
#print axioms Crown.CertificateData.minimal_obstruction_pair_count
#print axioms Crown.CertificateData.minimal_obstruction_triple_count
#print axioms Crown.CertificateData.all_templates_selected_iff
#print axioms Crown.ObstructionEncoding.encoding_iff_actual_obstruction
#print axioms Crown.ObstructionEncoding.satisfiable_iff_actual_obstruction
#print axioms Crown.CertificateSemantics.counter_cnf_iff
#print axioms Crown.CertificateSemantics.equality_cnf_iff
#print axioms Crown.CertificateSemantics.implication_clause_iff
#print axioms Crown.CertificateSemantics.lex_clause_iff
#print axioms Crown.CertificateSemantics.counter_zero
#print axioms Crown.CertificateSemantics.counter_above
#print axioms Crown.CertificateSemantics.counter_step
#print axioms Crown.CertificateSemantics.counter_eight_iff
#print axioms Crown.CertificateSemantics.bits_rank_inverse
#print axioms Crown.CertificateSemantics.rank_bits_inverse
#print axioms Crown.CertificateSemantics.maskBits_injective
#print axioms Crown.CertificateSemantics.maskBits_surjective
#print axioms Crown.CertificateSemantics.feasible_surjective
#print axioms Crown.CertificateSemantics.increasingRanks_complete
#print axioms Crown.CertificateSemantics.decreasingRanks_complete
#print axioms Crown.CertificateSemantics.pair_pattern_iff
#print axioms Crown.CertificateSemantics.triple_lower_upper_iff
#print axioms Crown.CertificateData.minimal_infeasible_iff
#print axioms Crown.CertificateData.minimal_obstruction_count
#print axioms Crown.CertificateData.distinct_pair_obstruction_count
#print axioms Crown.CertificateData.distinct_triple_obstruction_count
#print axioms Crown.RUPSoundness.rup_sound
#print axioms Crown.RUPSoundness.chain_preserves
#print axioms Crown.RUPSoundness.chain_empty_unsatisfiable
#print axioms Crown.RUPSoundness.root_conflict_unsatisfiable
#print axioms Crown.RUPSoundness.example_p_rup
#print axioms Crown.RUPSoundness.example_after_p_root
#print axioms Crown.RUPSoundness.example_unsatisfiable
#print axioms Crown.FamilyDomains.card_families
#print axioms Crown.FamilyDomains.card_balanced_families
#print axioms Crown.FamilyDomains.card_five_vertex_families
#print axioms Crown.FamilyDomains.extend_to_full_size
#print axioms Crown.FamilyDomains.feasible_restrict
#print axioms Crown.FamilyDomains.all_smaller_of_full
#print axioms Crown.FamilyEnumeration.unique_increasing_enumeration
#print axioms Crown.FamilyEnumeration.subset_domain
#print axioms Crown.FamilyEnumeration.card_increasing_families
#print axioms Crown.DirectStarCheck.accepts_iff_feasible
#print axioms Crown.DirectStarCheck.accepts_iff_distinct
#print axioms Crown.DirectStarCheck.direct_iff_implications
#print axioms Crown.ThreeRankCoding.encode_bijective
#print axioms Crown.ThreeRankCoding.completed_row_count
#print axioms Crown.ThreeRankCoding.comparison_entry_count
#print axioms Crown.ThreeRankCoding.at_most_seven_choices
#print axioms Crown.ReportHistograms.balanced6_agreement
#print axioms Crown.ReportHistograms.balanced6_total
#print axioms Crown.ReportHistograms.balanced6_failure_bin
#print axioms Crown.ReportHistograms.odd5_agreement
#print axioms Crown.ReportHistograms.odd5_total
#print axioms Crown.ReportHistograms.odd5_failure_bin
#print axioms Crown.ClauseNormalization.same_literals
#print axioms Crown.ClauseNormalization.deduplicate_literals
#print axioms Crown.ClauseNormalization.tautology_satisfied
#print axioms Crown.ClauseNormalization.omit_tautology
#print axioms Crown.ObstructionEncoding.encoding_iff
#print axioms Crown.ObstructionEncoding.encoding_iff_obstruction
#print axioms Crown.ObstructionEncoding.satisfiable_iff
#print axioms Crown.FiveSubsetFeasibility.fixed_subset
#print axioms Crown.CertificateGraph.exists_feasible
#print axioms Crown.CertificateSixGraph.exists_feasible
#print axioms Crown.Certificate.variable_occurs_iff
#print axioms Crown.Certificate.frozen_variable_count
#print axioms Crown.Certificate.frozen_clause_count
#print axioms Crown.Certificate.frozen_variables_bounded
#print axioms Crown.Certificate.frozen_first_clause
#print axioms Crown.Certificate.allocation_clause_redundant
#print axioms Crown.Certificate.pairing8Refutation
#print axioms Crown.Certificate.pairing8_unsatisfiable
#print axioms Crown.CertificateSix.pairing6Refutation
#print axioms Crown.CertificateSix.pairing6_unsatisfiable
#print axioms Crown.Orientations.bad_card_le_two
#print axioms Crown.Orientations.strict_zero_upper_fixed
#print axioms Crown.Orientations.bad_card_le_two_of_star
#print axioms Crown.Orientations.directed_bad_card_le_one
#print axioms Crown.Orientations.feasible_of_no_pairBad
#print axioms Crown.Orientations.exists_feasible_orientation
#print axioms Crown.PairTypes.global_directed_iff
#print axioms Crown.PairTypes.global_fixed_iff
#print axioms Crown.PairTypes.T_endpoint_card_le_one
#print axioms Crown.Matchings.card_orientedPairing
#print axioms Crown.Matchings.card_pairingOn
#print axioms Crown.Matchings.card_firstSetFiber
#print axioms Crown.Matchings.card_selectedFirstSets
#print axioms Crown.MatchingProbabilities.comparison_T_card_le_one
#print axioms Crown.MatchingProbabilities.card_comparison_multipleT
#print axioms Crown.MatchingBadCounts.card_badComparison_eq_P
#print axioms Crown.MatchingCounts.natCard_directedCrossEvent_finite
#print axioms Crown.MatchingCounts.directedCross_size_constraints
#print axioms Crown.MatchingCounts.configuration_count_factorial
#print axioms Crown.MatchingCounts.crossCount_eq_M
#print axioms Crown.MatchingFive.candidateTriples_card_le
#print axioms Crown.MatchingFive.matrix_representable
#print axioms Crown.MatchingExistence.matrix_representable6
#print axioms Crown.MatchingExistence.matrix_representable7
#print axioms Crown.ProbabilitySpecification.coordinates_exist
#print axioms Crown.ProbabilitySpecification.bad_pair_card
#print axioms Crown.ProbabilitySpecification.fixed_pair_card
#print axioms Crown.ProbabilitySpecification.triple_degrees
#print axioms Crown.ProbabilitySpecification.prescribed_pair_probability
#print axioms Crown.ProbabilitySpecification.residual_fiber
#print axioms Crown.ProbabilitySpecification.triple_residual_sets
#print axioms Crown.ProbabilitySpecification.triple_probability
#print axioms Crown.ProbabilitySpecification.feasible_five
#print axioms Crown.ProbabilitySpecification.feasible_six
#print axioms Crown.ProbabilitySpecification.feasible_seven
#print axioms Crown.Ranks.feasible_iff_distinct
#print axioms Crown.Ranks.completeEntry_lt_iff
#print axioms Crown.Ranks.multiStar_completion
#print axioms Crown.Ranks.feasible_iff_constraints
#print axioms Crown.Ranks.choice_exists_iff
#print axioms Crown.Ranks.feasible_iff_no_obstructions
#print axioms Crown.Ranks.central_triple_values
#print axioms Crown.Ranks.no_fixed_three_star_chain
#print axioms Crown.Ranks.no_fixed_two_star_fixed_chain
#print axioms Crown.Orders.coordinate_orders
#print axioms Crown.Orders.orders_nodup
#print axioms Crown.Orders.mem_orders
#print axioms Crown.Orders.coordinate_mono
#print axioms Crown.Orders.all_before_strict
#print axioms Crown.Blocks.restrict_block_cross
#print axioms Crown.Blocks.word_represents_rankGraph
#print axioms Crown.Blocks.feasible_representable
#print axioms Crown.Baseline.matrix_representable
#print axioms Crown.BaselineLiteral.word_represents_initialRankGraph
#print axioms Crown.BalancedLarge.matrix_representable
#print axioms Crown.OddRanks.no_fixed_pair
#print axioms Crown.OddRanks.obstruction_shape
#print axioms Crown.OddRanks.feasible_of_safe_three
#print axioms Crown.OddGraphs.matrix_representable_three
#print axioms Crown.CrownLower.crown_size_le_twice_multiplicity
#print axioms Crown.SmallGraphs.at_most_six_iff
#print axioms Crown.SmallGraphs.number_at_most_six_iff
#print axioms Crown.SmallGraphs.prism_not_bipartite
#print axioms Crown.SmallGraphs.wheel_not_bipartite
#print axioms Crown.UnorderedMatchings.perfect_pairings_six_card
#print axioms Crown.UnorderedMatchings.perfect_pairings_eight_card
#print axioms Crown.RankExample.example_obstruction
#print axioms Crown.RankLocalDetails.restrict_block_three
#print axioms Crown.RankLocalDetails.strict_forces_order
#print axioms Crown.RankLocalDetails.permutations_alternates_iff
#print axioms Crown.PartSizeBounds.baseline_halfceil
#print axioms Crown.PartSizeBounds.small_part
#print axioms Crown.PartSizeBounds.unbalanced_even
#print axioms Crown.PartSizeBounds.unbalanced_odd
#print axioms Crown.PartSizeBounds.near_odd
#print axioms Crown.exists_safe_odd_vertex_three
#print axioms Crown.CertificateSymmetry.mask_image_exists
#print axioms Crown.CertificateSymmetry.orbit_maximum
#print axioms Crown.CertificateSymmetry.obstruction_invariant
#print axioms Crown.CertificateSymmetry.canonical_bad_selection_explicit
#print axioms Crown.GosperTraversal.update_successor
#print axioms Crown.GosperTraversal.traversal_complete
#print axioms Crown.TupleTraversal.update_successor
#print axioms Crown.TupleTraversal.traversal_complete
#print axioms Crown.uniform_length
#print axioms Crown.represents_equiv
#print axioms Crown.represents_induce
#print axioms Crown.kRepresentable_induce
#print axioms Crown.minimum_uniform_length
#print axioms Crown.balanced_chain_endpoints
#print axioms Crown.alternates_append_swap
#print axioms Crown.represents_append_swap
#print axioms Crown.represents_sum_two
#print axioms Crown.represents_complete_twice

#print axioms Crown.PairingCoverage.feasible_reverse

#print axioms Crown.MatchingRepresentatives.card_anchoredPairing3

#print axioms Crown.MatchingRepresentatives.card_anchoredPairing4

#print axioms Crown.PairingStored3.coordinates_complete

#print axioms Crown.PairingStored3.allPairingsBad_iff_stored

#print axioms Crown.PairingStored4.coordinates_complete

#print axioms Crown.PairingStored4.allPairingsBad_iff_stored

#print axioms Crown.CertificateData.frozen_formula_satisfied

#print axioms Crown.CertificateSixData.reduced_formula_satisfied

#print axioms Crown.SpecialRows.feasible_iff
#print axioms Crown.OddGraphs.five_seven
