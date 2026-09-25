import generated.ThreeClosureData
namespace Crown.ThreeClosure
open Crown.Ranks Crown.FiniteClosureChecks
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
theorem seed_checked : SeedCheck rows owner support seed := by decide +kernel
theorem fixed_checked : FixedCheck rows core fixedHint := by decide +kernel
#print axioms seed_checked
#print axioms fixed_checked
end Crown.ThreeClosure
