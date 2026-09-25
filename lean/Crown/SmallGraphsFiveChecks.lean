import Crown.SmallGraphsFiveData
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem five_chunk_0 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+0)) 2 (wordsFive.getD (m.val+0) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_0
theorem five_chunk_1 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+64)) 2 (wordsFive.getD (m.val+64) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_1
theorem five_chunk_2 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+128)) 2 (wordsFive.getD (m.val+128) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_2
theorem five_chunk_3 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+192)) 2 (wordsFive.getD (m.val+192) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_3
theorem five_chunk_4 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+256)) 2 (wordsFive.getD (m.val+256) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_4
theorem five_chunk_5 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+320)) 2 (wordsFive.getD (m.val+320) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_5
theorem five_chunk_6 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+384)) 2 (wordsFive.getD (m.val+384) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_6
theorem five_chunk_7 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+448)) 2 (wordsFive.getD (m.val+448) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_7
theorem five_chunk_8 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+512)) 2 (wordsFive.getD (m.val+512) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_8
theorem five_chunk_9 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+576)) 2 (wordsFive.getD (m.val+576) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_9
theorem five_chunk_10 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+640)) 2 (wordsFive.getD (m.val+640) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_10
theorem five_chunk_11 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+704)) 2 (wordsFive.getD (m.val+704) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_11
theorem five_chunk_12 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+768)) 2 (wordsFive.getD (m.val+768) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_12
theorem five_chunk_13 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+832)) 2 (wordsFive.getD (m.val+832) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_13
theorem five_chunk_14 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+896)) 2 (wordsFive.getD (m.val+896) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_14
theorem five_chunk_15 : ∀ m : Fin 64, Crown.Represents (graph 5 (m.val+960)) 2 (wordsFive.getD (m.val+960) []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms five_chunk_15
theorem five_tables_indexed : ∀ q : Fin 16, ∀ r : Fin 64, Crown.Represents (graph 5 (r.val+q.val*64)) 2 (wordsFive.getD (r.val+q.val*64) []) := by
  intro q; fin_cases q
  · exact five_chunk_0
  · exact five_chunk_1
  · exact five_chunk_2
  · exact five_chunk_3
  · exact five_chunk_4
  · exact five_chunk_5
  · exact five_chunk_6
  · exact five_chunk_7
  · exact five_chunk_8
  · exact five_chunk_9
  · exact five_chunk_10
  · exact five_chunk_11
  · exact five_chunk_12
  · exact five_chunk_13
  · exact five_chunk_14
  · exact five_chunk_15

end Crown.SmallGraphs
