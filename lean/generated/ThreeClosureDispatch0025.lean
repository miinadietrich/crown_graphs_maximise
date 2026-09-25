import generated.ThreeClosureFastSteps0025
import Crown.ThreeClosureDispatch
import Mathlib.Tactic.FinCases
namespace Crown.ThreeClosure
open Crown.Ranks Crown.FiniteClosureChecks
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
theorem dispatch0025 : ∀ i : Fin 17,
    StepCheck rows owner support core nextHint lastHint 6 (rangeIndex 2500 17 (by decide) i) := by
  intro i
  fin_cases i
  · exact fastStep2500
  · exact fastStep2501
  · exact fastStep2502
  · exact fastStep2503
  · exact fastStep2504
  · exact fastStep2505
  · exact fastStep2506
  · exact fastStep2507
  · exact fastStep2508
  · exact fastStep2509
  · exact fastStep2510
  · exact fastStep2511
  · exact fastStep2512
  · exact fastStep2513
  · exact fastStep2514
  · exact fastStep2515
  · exact fastStep2516
#print axioms dispatch0025
end Crown.ThreeClosure
