import Specification.RankDefinitions
import Specification.MatrixDefinitions

/-! Independent statements for the distinguished-coordinate argument and the
analytical five-by-seven case. This file belongs only to the Challenge build. -/

namespace Crown.SpecialRows
open Crown.Ranks
universe u
variable {k : Nat} {V : Type u} (rows : V → InitialRow (Fin k)) (z : Fin k)

theorem feasible_iff (hsp : ∀ b, rows b z = none ∨ rows b z = some 0)
    (hk : 3 ≤ k) :
    Feasible rows ↔ NoFixedPair rows ∧ ¬ ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  sorry

end Crown.SpecialRows

namespace Crown.OddGraphs
theorem five_seven (M : Fin 5 → Fin 7 → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) 3 := by
  sorry

end Crown.OddGraphs
