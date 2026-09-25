import Crown.SmallGraphPrismData
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def prismPermutations : List (List (Fin 6)) := prismWordsTree.toList
theorem prismPermutations_length : prismPermutations.length = 5040 := by decide +kernel
theorem prism_chunk_0 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+0) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_0
theorem prism_chunk_1 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+80) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_1
theorem prism_chunk_2 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+160) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_2
theorem prism_chunk_3 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+240) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_3
theorem prism_chunk_4 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+320) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_4
theorem prism_chunk_5 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+400) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_5
theorem prism_chunk_6 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+480) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_6
theorem prism_chunk_7 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+560) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_7
theorem prism_chunk_8 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+640) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_8
theorem prism_chunk_9 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+720) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_9
theorem prism_chunk_10 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+800) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_10
theorem prism_chunk_11 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+880) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_11
theorem prism_chunk_12 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+960) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_12
theorem prism_chunk_13 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1040) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_13
theorem prism_chunk_14 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1120) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_14
theorem prism_chunk_15 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1200) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_15
theorem prism_chunk_16 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1280) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_16
theorem prism_chunk_17 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1360) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_17
theorem prism_chunk_18 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1440) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_18
theorem prism_chunk_19 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1520) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_19
theorem prism_chunk_20 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1600) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_20
theorem prism_chunk_21 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1680) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_21
theorem prism_chunk_22 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1760) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_22
theorem prism_chunk_23 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1840) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_23
theorem prism_chunk_24 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+1920) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_24
theorem prism_chunk_25 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2000) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_25
theorem prism_chunk_26 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2080) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_26
theorem prism_chunk_27 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2160) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_27
theorem prism_chunk_28 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2240) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_28
theorem prism_chunk_29 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2320) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_29
theorem prism_chunk_30 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2400) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_30
theorem prism_chunk_31 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2480) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_31
theorem prism_chunk_32 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2560) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_32
theorem prism_chunk_33 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2640) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_33
theorem prism_chunk_34 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2720) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_34
theorem prism_chunk_35 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2800) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_35
theorem prism_chunk_36 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2880) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_36
theorem prism_chunk_37 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+2960) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_37
theorem prism_chunk_38 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3040) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_38
theorem prism_chunk_39 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3120) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_39
theorem prism_chunk_40 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3200) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_40
theorem prism_chunk_41 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3280) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_41
theorem prism_chunk_42 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3360) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_42
theorem prism_chunk_43 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3440) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_43
theorem prism_chunk_44 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3520) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_44
theorem prism_chunk_45 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3600) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_45
theorem prism_chunk_46 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3680) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_46
theorem prism_chunk_47 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3760) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_47
theorem prism_chunk_48 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3840) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_48
theorem prism_chunk_49 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+3920) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_49
theorem prism_chunk_50 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4000) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_50
theorem prism_chunk_51 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4080) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_51
theorem prism_chunk_52 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4160) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_52
theorem prism_chunk_53 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4240) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_53
theorem prism_chunk_54 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4320) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_54
theorem prism_chunk_55 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4400) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_55
theorem prism_chunk_56 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4480) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_56
theorem prism_chunk_57 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4560) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_57
theorem prism_chunk_58 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4640) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_58
theorem prism_chunk_59 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4720) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_59
theorem prism_chunk_60 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4800) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_60
theorem prism_chunk_61 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4880) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_61
theorem prism_chunk_62 : ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+4960) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms prism_chunk_62

end Crown.SmallGraphs
