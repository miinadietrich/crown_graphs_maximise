import Specification.RankDefinitions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-! The direct three-pair check uses base-five completed ranks. This is a
different encoding from the base-four initial rows of the closure certificate:
zero here is an actual completed extreme, not the sentinel for a star. -/
namespace Crown.ThreeRankCoding
open Crown.Ranks
open scoped Classical

def encode (r : CompletedRow (Fin 3)) : Fin 125 :=
  ⟨(r 0).val + 5*(r 1).val + 25*(r 2).val,by
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    have h2 := (r 2).isLt
    omega⟩


end Crown.ThreeRankCoding
