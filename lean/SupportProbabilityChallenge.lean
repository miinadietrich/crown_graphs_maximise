import Specification.ProbabilityDefinitions
import Specification.MatrixDefinitions

/-! Specification-only obligations. Proof placeholders never enter Solution.
Literal source headers retain their original names in the separate Challenge
environment; coordinate-explicit contracts use ProbabilitySpecification.
Numerical tables, domains and constants remain in NumericalChallenge. -/

set_option synthInstance.maxSize 1024
open scoped Classical
open Crown.Ranks Crown.Orientations Crown.PairTypes Crown.PairTypes.Colour
open Crown.Matchings Crown.MatchingProbabilities

namespace Crown.Orientations

-- Source: Crown/Orientations.lean
theorem bad_card_le_two {k : ℕ} (N M : NeighbourRow (Fin k)) :
    (badOrientations N M).card ≤ 2 := by
  sorry

-- Source: Crown/Orientations.lean
theorem strict_zero_upper_fixed {I : Type*} (N M : NeighbourRow I) (o : I → Bool)
    (h : StrictBelow (zeroRow N o) (zeroRow M o)) : ∀ i, M i ≠ (false, false) := by
  sorry

-- Source: Crown/Orientations.lean
theorem bad_card_le_two_of_star {k : ℕ} (N M : NeighbourRow (Fin k))
    (j : Fin k) (hj : N j = (false, false)) : (badOrientations N M).card ≤ 2 := by
  sorry

-- Source: Crown/Orientations.lean
theorem directed_bad_card_le_one {k : ℕ} (N M : NeighbourRow (Fin k))
    (hN : ∀ i, N i ≠ (false, false)) (hM : ∀ i, M i ≠ (false, false)) :
    (directedBad N M).card ≤ 1 := by
  sorry

-- Source: Crown/Orientations.lean
theorem feasible_of_no_pairBad {I V : Type*} [Nonempty I]
    (N : V → NeighbourRow I) (o : I → Bool)
    (hgood : ∀ b c, b ≠ c → ¬ PairBad (N b) (N c) o) :
    Feasible (fun b => row (N b) o) := by
  sorry

-- Source: Crown/Orientations.lean
theorem exists_feasible_orientation (k : ℕ) (hk : 8 ≤ k)
    (N : Fin (2 * k) → NeighbourRow (Fin k)) :
    ∃ o : Counting.Orientations k, Feasible (fun b => row (N b) o) := by
  sorry

end Crown.Orientations

namespace Crown.PairTypes

-- Source: Crown/PairTypes.lean
theorem global_directed_iff {I : Type*} (p : I → Colour × Colour) :
    (¬ DoubleStar (smaller p) ∧ ¬ DoubleStar (larger p) ∧
      StrictBelow (zeroRow (smaller p) (fun _ => false))
        (zeroRow (larger p) (fun _ => false))) ↔
      ((∀ i, Allowed (p i).1 (p i).2) ∧ AtMostOneExceptional p) := by
  sorry

-- Source: Crown/PairTypes.lean
theorem global_fixed_iff {I : Type*} (p : I → Colour × Colour) :
    (Fixed (row (smaller p) (fun _ => false)) ∧
      Fixed (row (larger p) (fun _ => false)) ∧
      StrictBelow (zeroRow (smaller p) (fun _ => false))
        (zeroRow (larger p) (fun _ => false))) ↔
      ∀ i, Ordinary (p i).1 (p i).2 := by
  sorry

-- Source: Crown/PairTypes.lean
theorem T_endpoint_card_le_one {k : Nat} (p : Fin k → Colour × Colour)
    (h : ¬ DoubleStar (smaller p) ∧ ¬ DoubleStar (larger p) ∧
      StrictBelow (zeroRow (smaller p) (fun _ => false))
        (zeroRow (larger p) (fun _ => false))) :
    (Finset.univ.filter (fun v : Fin k × Bool => endpoint p v = T)).card ≤ 1 := by
  sorry

end Crown.PairTypes

namespace Crown.Matchings

-- Source: Crown/Matchings.lean
theorem card_orientedPairing (k : ℕ) : Fintype.card (OrientedPairing k) = Arithmetic.Q k := by
  sorry

-- Source: Crown/Matchings.lean
theorem card_pairingOn {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (hV : Fintype.card V = 2 * k) : Fintype.card (PairingOn V) = Arithmetic.Q k := by
  sorry

-- Source: Crown/Matchings.lean
theorem card_firstSetFiber {k : ℕ} (s : FirstSets k) :
    Fintype.card {p : OrientedPairing k // p.1 = s} = k.factorial := by
  sorry

-- Source: Crown/Matchings.lean
theorem card_selectedFirstSets {k : ℕ} (T : Finset (FirstSets k)) :
    Fintype.card {p : OrientedPairing k // p.1 ∈ T} = T.card * k.factorial := by
  sorry

end Crown.Matchings

namespace Crown.MatchingProbabilities
variable {V : Type*} [DecidableEq V]

-- Source: Crown/MatchingProbabilities.lean
theorem comparison_T_card_le_one [Fintype V] (col : V → Colour) (p : PairingOn V)
    (h : Comparison col p) : (Finset.univ.filter (fun v => col v = Colour.T)).card ≤ 1 := by
  sorry

-- Source: Crown/MatchingProbabilities.lean
theorem card_comparison_multipleT [Fintype V] (col : V → Colour)
    (v w : V) (hv : col v = Colour.T) (hw : col w = Colour.T) (hne : v ≠ w) :
    Nat.card {p : PairingOn V // Comparison col p} = 0 := by
  sorry

end Crown.MatchingProbabilities

namespace Crown.MatchingBadCounts
variable {V : Type*} [DecidableEq V]

-- Source: Crown/MatchingBadCounts.lean
theorem card_badComparison_eq_P [Fintype V] (col : V → Colour)
    (k : ℕ) (hcard : Fintype.card V = 2*(k+1)) :
    Nat.card {p : PairingOn V // BadComparison col p} =
      Arithmetic.P (k+1) (Fintype.card (ColourClass col Colour.X))
        (Fintype.card (ColourClass col Colour.Y)) (Fintype.card (ColourClass col Colour.Z))
        (Fintype.card (ColourClass col Colour.T)) := by
  sorry

end Crown.MatchingBadCounts

namespace Crown.MatchingCounts
variable {X Y Z : Type*}

-- Source: Crown/MatchingCounts.lean
theorem natCard_directedCrossEvent_finite [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*k) :
    Nat.card {p : Matchings.PairingOn (ClassVertices X Y Z) // DirectedCrossEvent X Y Z p} =
      Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) (Fintype.card Y : ℤ) (Fintype.card Z : ℤ) := by
  sorry

-- Source: Crown/MatchingCounts.lean
theorem directedCross_size_constraints (k x y z : ℕ) (hsum : x+y+z = 2*k)
    (p : {p : Matchings.PairingOn (ClassVertices (Fin x) (Fin y) (Fin z)) //
      DirectedCrossEvent (Fin x) (Fin y) (Fin z) p}) : x ≤ k ∧ y ≤ k ∧ z ≤ k := by
  sorry

-- Source: Crown/MatchingCounts.lean
theorem configuration_count_factorial (α β γ : ℕ) :
    Fintype.card (Configuration α β γ) * (α.factorial * β.factorial * γ.factorial) =
      (α + β).factorial * (α + γ).factorial * (β + γ).factorial := by
  sorry

-- Source: Crown/MatchingCounts.lean
theorem crossCount_eq_M (k x y z : ℕ) (hsum : x+y+z = 2*k) :
    crossCount x y z = Arithmetic.M (k : ℤ) (x : ℤ) (y : ℤ) (z : ℤ) := by
  sorry

end Crown.MatchingCounts

namespace Crown.MatchingFive

-- Source: Crown/MatchingFive.lean
theorem candidateTriples_card_le (N : Fin 10 → Fin 10 → Bool) : (candidateTriples N).card ≤ 63 := by
  sorry

-- Source: Crown/MatchingFive.lean
theorem matrix_representable (M : Fin 10 → Fin 10 → Bool) :
    Crown.KRepresentable (Crown.BalancedLarge.matrixGraph M) 5 := by
  sorry

end Crown.MatchingFive

namespace Crown.MatchingExistence

-- Source: Crown/MatchingExistence.lean
theorem matrix_representable6 (M : Fin 12 → Fin 12 → Bool) :
    Crown.KRepresentable (Crown.BalancedLarge.matrixGraph M) 6 := by
  sorry

-- Source: Crown/MatchingExistence.lean
theorem matrix_representable7 (M : Fin 14 → Fin 14 → Bool) :
    Crown.KRepresentable (Crown.BalancedLarge.matrixGraph M) 7 := by
  sorry

end Crown.MatchingExistence
