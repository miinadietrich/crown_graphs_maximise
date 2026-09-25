import Crown.SmallGraphPrismChecks
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem prism_indexed : ∀ q : Fin 63, ∀ r : Fin 80, ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD (r.val+q.val*80) []) t) := by
  intro q; fin_cases q
  · exact prism_chunk_0
  · exact prism_chunk_1
  · exact prism_chunk_2
  · exact prism_chunk_3
  · exact prism_chunk_4
  · exact prism_chunk_5
  · exact prism_chunk_6
  · exact prism_chunk_7
  · exact prism_chunk_8
  · exact prism_chunk_9
  · exact prism_chunk_10
  · exact prism_chunk_11
  · exact prism_chunk_12
  · exact prism_chunk_13
  · exact prism_chunk_14
  · exact prism_chunk_15
  · exact prism_chunk_16
  · exact prism_chunk_17
  · exact prism_chunk_18
  · exact prism_chunk_19
  · exact prism_chunk_20
  · exact prism_chunk_21
  · exact prism_chunk_22
  · exact prism_chunk_23
  · exact prism_chunk_24
  · exact prism_chunk_25
  · exact prism_chunk_26
  · exact prism_chunk_27
  · exact prism_chunk_28
  · exact prism_chunk_29
  · exact prism_chunk_30
  · exact prism_chunk_31
  · exact prism_chunk_32
  · exact prism_chunk_33
  · exact prism_chunk_34
  · exact prism_chunk_35
  · exact prism_chunk_36
  · exact prism_chunk_37
  · exact prism_chunk_38
  · exact prism_chunk_39
  · exact prism_chunk_40
  · exact prism_chunk_41
  · exact prism_chunk_42
  · exact prism_chunk_43
  · exact prism_chunk_44
  · exact prism_chunk_45
  · exact prism_chunk_46
  · exact prism_chunk_47
  · exact prism_chunk_48
  · exact prism_chunk_49
  · exact prism_chunk_50
  · exact prism_chunk_51
  · exact prism_chunk_52
  · exact prism_chunk_53
  · exact prism_chunk_54
  · exact prism_chunk_55
  · exact prism_chunk_56
  · exact prism_chunk_57
  · exact prism_chunk_58
  · exact prism_chunk_59
  · exact prism_chunk_60
  · exact prism_chunk_61
  · exact prism_chunk_62
theorem prism_all_indices (i : Fin 5040) : ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord (prismWordsTree.getD i.val []) t) := by
  have hq : i.val / 80 < 63 := by omega
  have hr : i.val % 80 < 80 := Nat.mod_lt _ (by decide)
  have h := prism_indexed ⟨i.val / 80,hq⟩ ⟨i.val % 80,hr⟩
  have he : i.val % 80 + i.val / 80 * 80 = i.val := by omega
  simpa only [he] using h
theorem prism_permutations_fail : ∀ s ∈ [(1:Fin 6),2,3,4,4,5,5].permutations', ∀ t ∈ [(1:Fin 6),2,3].permutations', ¬Matches prism (gapWord s t) := by
  intro s hs t ht
  have hm : s ∈ prismPermutations := by simpa only [prismPermutations,prismWordsTree_coverage] using hs
  have hi : prismPermutations.idxOf s < prismPermutations.length := List.idxOf_lt_length_of_mem hm
  have hib : prismPermutations.idxOf s < 5040 := by simpa only [prismPermutations_length] using hi
  have he : prismWordsTree.getD (prismPermutations.idxOf s) [] = s := by
    rw [LookupTree.getD_eq _ prismWordsTree_valid]
    change prismPermutations.getD (prismPermutations.idxOf s) [] = s
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_idxOf hi
  have h := prism_all_indices ⟨prismPermutations.idxOf s,hib⟩ t ht
  simpa only [he] using h
#print axioms prism_permutations_fail
end Crown.SmallGraphs
