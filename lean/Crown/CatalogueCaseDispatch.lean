import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace Crown.CatalogueCaseDispatch

/-- A fixed finite split, checked once with an abstract proposition. -/
theorem forall_fin21 (P : Fin 21 → Prop)
    (h00 : P 0)
    (h01 : P 1)
    (h02 : P 2)
    (h03 : P 3)
    (h04 : P 4)
    (h05 : P 5)
    (h06 : P 6)
    (h07 : P 7)
    (h08 : P 8)
    (h09 : P 9)
    (h10 : P 10)
    (h11 : P 11)
    (h12 : P 12)
    (h13 : P 13)
    (h14 : P 14)
    (h15 : P 15)
    (h16 : P 16)
    (h17 : P 17)
    (h18 : P 18)
    (h19 : P 19)
    (h20 : P 20)
    : ∀ b, P b := by
  intro b
  fin_cases b <;> assumption

#print axioms forall_fin21
end Crown.CatalogueCaseDispatch
