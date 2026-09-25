import Specification.RankDefinitions
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.Orders
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

noncomputable def enumeration : List V := (Finset.univ : Finset V).toList

noncomputable def sortByKey {K : Type*} [LinearOrder K] (key : V → K) : List V :=
  (enumeration (V := V)).mergeSort (fun b c => key b ≤ key c)

def Before (l : List V) (b c : V) : Prop := l.idxOf b < l.idxOf c

def rankSum (r : V → Ranks.CompletedRow (Fin k)) (b : V) : ℕ :=
  ∑ i, (r b i).val

noncomputable def firstKey (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k) (b : V) :
    ℕ ×ₗ (ℕᵒᵈ ×ₗ ℕ) :=
  toLex ((r b z).val, toLex (OrderDual.toDual (rankSum r b), enumeration.idxOf b))

noncomputable def firstOrder (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k) : List V :=
  sortByKey (firstKey r z)

noncomputable def laterKey (r : V → Ranks.CompletedRow (Fin k))
    (z i : Fin k) (b : V) : ℕ ×ₗ ℕᵒᵈ :=
  toLex ((r b i).val, OrderDual.toDual ((firstOrder r z).idxOf b))

noncomputable def orders (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) : List V :=
  if i = z then firstOrder r z else sortByKey (laterKey r z i)

end Crown.Orders
