import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import generated.ThreeClosureData
import Crown.FiniteClosureTables
namespace Crown.ThreeClosure
open Crown.Ranks Crown.FiniteClosureChecks
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def implicationBits (b : Fin 64) : Nat :=
  (if b.val < 32 then (if b.val < 16 then (if b.val < 8 then (if b.val < 4 then (if b.val < 2 then (if b.val < 1 then 0 else 0) else (if b.val < 3 then 0 else 0)) else (if b.val < 6 then (if b.val < 5 then 0 else 0) else (if b.val < 7 then 562958543486976 else 1688875630460928))) else (if b.val < 12 then (if b.val < 10 then (if b.val < 9 then 0 else 4503668347895808) else (if b.val < 11 then 5066626891382816 else 6192543978356832)) else (if b.val < 14 then (if b.val < 13 then 0 else 76562361914228736) else (if b.val < 15 then 77125320457716256 else 78251237544691296)))) else (if b.val < 24 then (if b.val < 20 then (if b.val < 18 then (if b.val < 17 then 0 else 0) else (if b.val < 19 then 8736 else 26208)) else (if b.val < 22 then (if b.val < 21 then 0 else 0) else (if b.val < 23 then 0 else 0))) else (if b.val < 28 then (if b.val < 26 then (if b.val < 25 then 224 else 0) else (if b.val < 27 then 0 else 0)) else (if b.val < 30 then (if b.val < 29 then 3808 else 0) else (if b.val < 31 then 0 else 0))))) else (if b.val < 48 then (if b.val < 40 then (if b.val < 36 then (if b.val < 34 then (if b.val < 33 then 0 else 286261248) else (if b.val < 35 then 286401056 else 286680672)) else (if b.val < 38 then (if b.val < 37 then 917504 else 0) else (if b.val < 39 then 0 else 0))) else (if b.val < 44 then (if b.val < 42 then (if b.val < 41 then 1966304 else 0) else (if b.val < 43 then 0 else 0)) else (if b.val < 46 then (if b.val < 45 then 18747104 else 0) else (if b.val < 47 then 0 else 0)))) else (if b.val < 56 then (if b.val < 52 then (if b.val < 50 then (if b.val < 49 then 0 else 18760703410176) else (if b.val < 51 then 18769293484576 else 18786473633376)) else (if b.val < 54 then (if b.val < 53 then 60130459648 else 0) else (if b.val < 55 then 0 else 0))) else (if b.val < 60 then (if b.val < 58 then (if b.val < 57 then 128850985184 else 0) else (if b.val < 59 then 0 else 0)) else (if b.val < 62 then (if b.val < 61 then 1228379393760 else 0) else (if b.val < 63 then 0 else 0))))))
noncomputable def lowerBits (b : Fin 64) : Nat :=
  (if b.val < 32 then (if b.val < 16 then (if b.val < 8 then (if b.val < 4 then (if b.val < 2 then (if b.val < 1 then 0 else 0) else (if b.val < 3 then 0 else 0)) else (if b.val < 6 then (if b.val < 5 then 0 else 0) else (if b.val < 7 then 0 else 0))) else (if b.val < 12 then (if b.val < 10 then (if b.val < 9 then 0 else 0) else (if b.val < 11 then 9007336695791616 else 27022010087374848)) else (if b.val < 14 then (if b.val < 13 then 0 else 0) else (if b.val < 15 then 153124723828457472 else 459374171485372416)))) else (if b.val < 24 then (if b.val < 20 then (if b.val < 18 then (if b.val < 17 then 0 else 0) else (if b.val < 19 then 0 else 0)) else (if b.val < 22 then (if b.val < 21 then 0 else 0) else (if b.val < 23 then 0 else 0))) else (if b.val < 28 then (if b.val < 26 then (if b.val < 25 then 0 else 0) else (if b.val < 27 then 0 else 0)) else (if b.val < 30 then (if b.val < 29 then 0 else 0) else (if b.val < 31 then 0 else 0))))) else (if b.val < 48 then (if b.val < 40 then (if b.val < 36 then (if b.val < 34 then (if b.val < 33 then 0 else 0) else (if b.val < 35 then 572522496 else 1717567488)) else (if b.val < 38 then (if b.val < 37 then 0 else 0) else (if b.val < 39 then 0 else 0))) else (if b.val < 44 then (if b.val < 42 then (if b.val < 41 then 14680064 else 0) else (if b.val < 43 then 0 else 0)) else (if b.val < 46 then (if b.val < 45 then 249561088 else 0) else (if b.val < 47 then 0 else 0)))) else (if b.val < 56 then (if b.val < 52 then (if b.val < 50 then (if b.val < 49 then 0 else 0) else (if b.val < 51 then 37521406820352 else 112564220461056)) else (if b.val < 54 then (if b.val < 53 then 0 else 0) else (if b.val < 55 then 0 else 0))) else (if b.val < 60 then (if b.val < 58 then (if b.val < 57 then 962087354368 else 0) else (if b.val < 59 then 0 else 0)) else (if b.val < 62 then (if b.val < 61 then 16355485024256 else 0) else (if b.val < 63 then 0 else 0))))))
noncomputable def implicationTable (b c : Fin 64) : Bool := (implicationBits b).testBit c.val
noncomputable def lowerTable (b c : Fin 64) : Bool := (lowerBits b).testBit c.val
theorem implicationTable_correct : ∀ b c, implicationTable b c = true ↔ Implies rows b c := by decide +kernel
theorem lowerTable_correct : ∀ b c, lowerTable b c = true ↔
    OneStar (rows b) ∧ Fixed (rows c) ∧ PotentialBelow (rows c) (rows b) := by decide +kernel
theorem rows_injective : Function.Injective rows := by decide +kernel
theorem rows_bijective : Function.Bijective rows := by
  apply (Fintype.bijective_iff_injective_and_card rows).mpr
  refine ⟨rows_injective, ?_⟩
  simp only [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_option]
  rfl
#print axioms implicationTable_correct
#print axioms lowerTable_correct
#print axioms rows_bijective
end Crown.ThreeClosure
