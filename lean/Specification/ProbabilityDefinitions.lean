import Specification.ProbabilityBaseDefinitions

set_option synthInstance.maxSize 1024

namespace Crown.MatchingBadCounts
open Crown.PairTypes Crown.Matchings Crown.MatchingProbabilities
def swapColour : Colour → Colour
  | .X => .Y | .Y => .X | .Z => .Z | .T => .T
def BadComparison {V : Type*} [DecidableEq V] (col : V → Colour) (p : PairingOn V) : Prop :=
  Comparison col p ∨ Comparison (fun v => swapColour (col v)) p
end Crown.MatchingBadCounts

namespace Crown.MatchingCounts
abbrev ClassVertices (X Y Z : Type*) := X ⊕ (Y ⊕ Z)
open scoped Classical in
def DirectedCrossEvent (X Y Z : Type*)
    (p : Crown.Matchings.PairingOn (ClassVertices X Y Z)) : Prop :=
  (∀ x, Sum.inl x ∈ p.1) ∧ (∀ y, Sum.inr (Sum.inl y) ∉ p.1) ∧
    ∀ z hz, ∃ y, (p.2 ⟨Sum.inr (Sum.inr z),hz⟩).val = Sum.inr (Sum.inl y)
abbrev Selection (n r : ℕ) := {s : Finset (Fin n) // s.card = r}
abbrev Selected {n r : ℕ} (s : Selection n r) := {v : Fin n // v ∈ s.val}
abbrev Rejected {n r : ℕ} (s : Selection n r) := {v : Fin n // v ∉ s.val}
abbrev Configuration (α β γ : ℕ) :=
  Σ XZ : Selection (α + β) β,
  Σ ZY : Selection (β + γ) γ,
  Σ YZ : Selection (α + γ) γ,
    (Selected XZ ≃ Rejected ZY) ×
      (Selected ZY ≃ Selected YZ) × (Rejected XZ ≃ Rejected YZ)
open scoped Classical in
noncomputable def crossCount (x y z : ℕ) : ℕ :=
  Fintype.card {p : Crown.Matchings.PairingOn (ClassVertices (Fin x) (Fin y) (Fin z)) //
    DirectedCrossEvent (Fin x) (Fin y) (Fin z) p}
end Crown.MatchingCounts

namespace Crown.MatchingFixedCounts
open Crown.Orientations Crown.Ranks
section
universe u_2
def FixedPairBad {I : Type u_2} (N M : NeighbourRow I) : Prop :=
  Fixed (row N (fun _ => false)) ∧ Fixed (row M (fun _ => false)) ∧
    (StrictBelow (zeroRow N (fun _ => false)) (zeroRow M (fun _ => false)) ∨
      StrictBelow (zeroRow M (fun _ => false)) (zeroRow N (fun _ => false)))
end
end Crown.MatchingFixedCounts

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

namespace Crown.MatchingFive
open scoped Classical
noncomputable def centres (N : Fin 10 → Fin 10 → Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun c => (Finset.univ.filter (fun a => N c a = true)).card = 8)
noncomputable def candidateTriples (N : Fin 10 → Fin 10 → Bool) : Finset (Fin 10 × Finset (Fin 10)) :=
  centres N ×ˢ (centres N)ᶜ.powersetCard 2
end Crown.MatchingFive
