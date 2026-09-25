import Specification.RankDefinitions
import Crown.ArithmeticDefinitions
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter

/-! Challenge-only orientation definitions. No solution proof imports. -/

namespace Crown.Orientations

open Crown.Ranks

abbrev NeighbourRow (I : Type*) := I → Bool × Bool

def entry : Bool × Bool → Bool → Option (Fin 3)
  | (false, false), _ => none
  | (true, true), _ => some 1
  | (true, false), o => if o then some 2 else some 0
  | (false, true), o => if o then some 0 else some 2

def row {I : Type*} (N : NeighbourRow I) (o : I → Bool) : InitialRow I :=
  fun i => entry (N i) (o i)

def zeroRow {I : Type*} (N : NeighbourRow I) (o : I → Bool) : CompletedRow I :=
  complete (row N o) false

def DoubleStar {I : Type*} (N : NeighbourRow I) : Prop :=
  ∃ i j, i ≠ j ∧ N i = (false, false) ∧ N j = (false, false)

/-- Multi-star rows are completed with both extremes, so only the other
rows contribute bad events. The remaining stars receive zero. -/
def PairBad {I : Type*} (N M : NeighbourRow I) (o : I → Bool) : Prop :=
  ¬ DoubleStar N ∧ ¬ DoubleStar M ∧
    (StrictBelow (zeroRow N o) (zeroRow M o) ∨ StrictBelow (zeroRow M o) (zeroRow N o))

noncomputable def badOrientations {k : ℕ} (N M : NeighbourRow (Fin k)) :
    Finset (Counting.Orientations k) := by
  classical
  exact Finset.univ.filter (PairBad N M)

noncomputable def directedBad {k : ℕ} (N M : NeighbourRow (Fin k)) :
    Finset (Counting.Orientations k) := by
  classical
  exact Finset.univ.filter (fun o => StrictBelow (zeroRow N o) (zeroRow M o))

end Crown.Orientations
