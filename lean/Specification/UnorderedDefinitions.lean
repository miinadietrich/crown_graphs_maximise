import Crown.Definitions
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.UnorderedMatchings
variable {V : Type*} [Fintype V] [DecidableEq V]

def DisjointPairs (P : Finset (Finset V)) : Prop :=
  ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f

def IsPerfectPairing (P : Finset (Finset V)) : Prop :=
  (∀ e ∈ P, e.card = 2) ∧ DisjointPairs P ∧ P.biUnion id = Finset.univ

end Crown.UnorderedMatchings
