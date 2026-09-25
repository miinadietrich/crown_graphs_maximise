import Crown.Ranks
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic

/-! L14: the literal four-coordinate example of a central obstruction.
Prescribed values are encoded one lower, as throughout Crown.Ranks. -/
namespace Crown.RankExample
open Crown.Ranks

def exampleRows : Fin 3 → InitialRow (Fin 4) :=
  ![ ![some 1, some 0, some 0, some 0],
     ![none, some 1, some 1, some 1],
     ![some 0, some 2, some 2, some 2] ]

/-- Neither fixed outer row lies below the other, but both extreme completions
of the central row create a strict comparison, and no completion is feasible. -/
theorem example_obstruction :
    ¬ StrictBelow (complete (exampleRows 0) false) (complete (exampleRows 2) false) ∧
    ¬ StrictBelow (complete (exampleRows 2) false) (complete (exampleRows 0) false) ∧
    StrictBelow (complete (exampleRows 1) false) (complete (exampleRows 2) false) ∧
    StrictBelow (complete (exampleRows 0) false) (complete (exampleRows 1) true) ∧
    ¬ Feasible exampleRows := by
  refine ⟨by unfold StrictBelow; decide +kernel, by unfold StrictBelow; decide +kernel,
    by unfold StrictBelow; decide +kernel, by unfold StrictBelow; decide +kernel, ?_⟩
  intro hf
  have hn := (feasible_iff_no_obstructions (by decide : 4 ≤ 4) exampleRows).mp hf
  apply hn.2
  have hs : OneStar (exampleRows 1) := by
    refine ⟨0,rfl,?_⟩
    decide +kernel
  refine ⟨1,⟨hs,2,?_,?_⟩,⟨hs,0,?_,?_⟩⟩
  all_goals simp only [Fixed,PotentialBelow,PotentialEntry]
  all_goals decide +kernel

#print axioms example_obstruction
end Crown.RankExample
