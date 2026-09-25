import Crown.SmallGraphsSixChecks08
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem six_chunk_072 : ∀ r : Fin 256, ValidCandidate (r.val + 18432) := by decide +kernel
#print axioms six_chunk_072
theorem six_chunk_073 : ∀ r : Fin 256, ValidCandidate (r.val + 18688) := by decide +kernel
#print axioms six_chunk_073
theorem six_chunk_074 : ∀ r : Fin 256, ValidCandidate (r.val + 18944) := by decide +kernel
#print axioms six_chunk_074
theorem six_chunk_075 : ∀ r : Fin 256, ValidCandidate (r.val + 19200) := by decide +kernel
#print axioms six_chunk_075
theorem six_chunk_076 : ∀ r : Fin 256, ValidCandidate (r.val + 19456) := by decide +kernel
#print axioms six_chunk_076
theorem six_chunk_077 : ∀ r : Fin 256, ValidCandidate (r.val + 19712) := by decide +kernel
#print axioms six_chunk_077
theorem six_chunk_078 : ∀ r : Fin 256, ValidCandidate (r.val + 19968) := by decide +kernel
#print axioms six_chunk_078
theorem six_chunk_079 : ∀ r : Fin 256, ValidCandidate (r.val + 20224) := by decide +kernel
#print axioms six_chunk_079
end Crown.SmallGraphs
