import Specification.OrientationDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.OddRanks
open Crown.Ranks
variable {k : ℕ} {B : Type*}

def degree (N : Orientations.NeighbourRow (Fin k)) : ℕ :=
  ∑ i, ((if (N i).1 then 1 else 0) + (if (N i).2 then 1 else 0))

def Centre (N : Orientations.NeighbourRow (Fin k)) (z : Fin k) : Prop :=
  ∀ i, N i = if i = z then (false, false) else (true, true)

def Safe (N : B → Orientations.NeighbourRow (Fin k)) (z : Fin k) : Prop :=
  (¬ ∃ c, Centre (N c) z) ∨
    ∀ l u, degree (N l) = k → degree (N u) = k →
      (N l z).1 = true → (N u z).1 = true → l = u

abbrev rows (N : B → Orientations.NeighbourRow (Fin k)) : B → InitialRow (Fin k) :=
  fun b => Orientations.row (N b) (fun _ => false)

end Crown.OddRanks
