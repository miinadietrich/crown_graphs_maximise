import Crown.PairingCoverage
import Crown.MatchingFive
import Crown.MatchingExistence

namespace Crown.ProbabilitySpecification
open Crown.Matchings Crown.Ranks Crown.Orientations
abbrev Coordinates (k : ℕ) := (Fin k × Bool) ≃ Fin (2*k)
def Realizes {k : ℕ} (p : PairingOn (Fin (2*k))) (e : Coordinates k) : Prop :=
  ∀ a b, DirectedPair p a b ↔ ∃ i, e (i,false) = a ∧ e (i,true) = b
def neighbourRow {k : ℕ} (N : Fin (2*k) → Bool) (e : Coordinates k) : NeighbourRow (Fin k) :=
  fun i => (N (e (i,false)),N (e (i,true)))
def rankRow {k : ℕ} (N : Fin (2*k) → Bool) (e : Coordinates k) : InitialRow (Fin k) :=
  row (neighbourRow N e) (fun _ => false)
def TriplePattern {k : ℕ} (l c u : Fin (2*k) → Bool) (e : Coordinates k) : Prop :=
  Fixed (rankRow l e) ∧ OneStar (rankRow c e) ∧ Fixed (rankRow u e) ∧
    PotentialBelow (rankRow l e) (rankRow c e) ∧ PotentialBelow (rankRow c e) (rankRow u e)
def TripleEvent {k : ℕ} (l c u : Fin (2*k) → Bool) (p : PairingOn (Fin (2*k))) : Prop :=
  ∃ e : Coordinates k, Realizes p e ∧ (TriplePattern l c u e ∨ TriplePattern u c l e)
def BadPairEvent {k : ℕ} (N M : Fin (2*k) → Bool) (p : PairingOn (Fin (2*k))) : Prop :=
  ∃ e : Coordinates k, Realizes p e ∧ PairBad (neighbourRow N e) (neighbourRow M e) (fun _ => false)
def FixedPairEvent {k : ℕ} (N M : Fin (2*k) → Bool) (p : PairingOn (Fin (2*k))) : Prop :=
  ∃ e : Coordinates k, Realizes p e ∧
    Crown.MatchingFixedCounts.FixedPairBad (neighbourRow N e) (neighbourRow M e)
def ResidualFirstSet {V : Type*} [DecidableEq V] (p : PairingOn V) (a b : V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ↔ v ∈ p.1 ∧ v ≠ a ∧ v ≠ b
end Crown.ProbabilitySpecification

namespace Crown.ProbabilitySpecification
open Crown.Matchings Crown.Ranks Crown.Orientations
open Crown.PairingCoordinates

set_option backward.isDefEq.respectTransparency false

theorem coordinates_realize {k : ℕ} (p : OrientedPairing k) :
    Realizes (constrainedEquiv k p) (coordinates p) := by
  intro a b
  constructor
  · intro h
    exact Crown.MatchingRanks.directedPair_coordinates p a b h
  · rintro ⟨i,rfl,rfl⟩
    exact Crown.MatchingRanks.coordinates_directedPair p i

theorem coordinates_exist (k : ℕ) (p : PairingOn (Fin (2*k))) :
    ∃ e : Coordinates k, Realizes p e := by
  let q := (constrainedEquiv k).symm p
  refine ⟨coordinates q,?_⟩
  have h := coordinates_realize q
  simpa [q] using h

theorem realized_pairing {k : ℕ} (p : PairingOn (Fin (2*k))) (e : Coordinates k)
    (h : Realizes p e) : constrainedEquiv k (ofCoordinates e) = p := by
  apply Crown.MatchingReversal.pairing_ext
  intro a b
  exact (directed_ofCoordinates e a b).trans (h a b).symm

theorem of_canonical {k : ℕ} (p : OrientedPairing k) : ofCoordinates (coordinates p) = p := by
  apply (constrainedEquiv k).injective
  exact realized_pairing _ _ (coordinates_realize p)

theorem feasible_five (N : Fin 10 → Fin 10 → Bool) :
    ∃ e : Coordinates 5, Feasible (fun v => rankRow (N v) e) := by
  obtain ⟨p,hp⟩ := Crown.MatchingFive.exists_feasible_matching N
  exact ⟨coordinates p,hp⟩

theorem feasible_six (N : Fin 12 → Fin 12 → Bool) :
    ∃ e : Coordinates 6, Feasible (fun v => rankRow (N v) e) := by
  obtain ⟨p,hp⟩ := Crown.MatchingExistence.exists_feasible_matching6 N
  exact ⟨coordinates p,hp⟩

theorem feasible_seven (N : Fin 14 → Fin 14 → Bool) :
    ∃ e : Coordinates 7, Feasible (fun v => rankRow (N v) e) := by
  obtain ⟨p,hp⟩ := Crown.MatchingExistence.exists_feasible_matching7 N
  exact ⟨coordinates p,hp⟩

#print axioms coordinates_exist
#print axioms of_canonical
#print axioms feasible_five
#print axioms feasible_six
#print axioms feasible_seven
end Crown.ProbabilitySpecification
