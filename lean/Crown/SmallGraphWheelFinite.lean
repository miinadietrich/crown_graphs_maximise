import Crown.SmallGraphExceptions
import Mathlib.Tactic.FinCases
namespace Crown.SmallGraphs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def wheelPermutations : List (List (Fin 6)) := [(1:Fin 6),2,3,4,5].permutations'
theorem wheelPermutations_length : wheelPermutations.length = 120 := by decide +kernel
theorem wheel_chunk_0 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+0) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_0
theorem wheel_chunk_1 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+10) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_1
theorem wheel_chunk_2 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+20) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_2
theorem wheel_chunk_3 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+30) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_3
theorem wheel_chunk_4 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+40) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_4
theorem wheel_chunk_5 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+50) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_5
theorem wheel_chunk_6 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+60) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_6
theorem wheel_chunk_7 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+70) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_7
theorem wheel_chunk_8 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+80) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_8
theorem wheel_chunk_9 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+90) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_9
theorem wheel_chunk_10 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+100) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_10
theorem wheel_chunk_11 : ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+110) []) t) := by
  unfold Matches Crown.Alternates Crown.restrictPair
  decide +kernel
#print axioms wheel_chunk_11
theorem wheel_indexed : ∀ q : Fin 12, ∀ r : Fin 10, ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD (r.val+q.val*10) []) t) := by
  intro q; fin_cases q
  · exact wheel_chunk_0
  · exact wheel_chunk_1
  · exact wheel_chunk_2
  · exact wheel_chunk_3
  · exact wheel_chunk_4
  · exact wheel_chunk_5
  · exact wheel_chunk_6
  · exact wheel_chunk_7
  · exact wheel_chunk_8
  · exact wheel_chunk_9
  · exact wheel_chunk_10
  · exact wheel_chunk_11
theorem wheel_all_indices (i : Fin 120) : ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord (wheelPermutations.getD i.val []) t) := by
  have hq : i.val / 10 < 12 := by omega
  have hr : i.val % 10 < 10 := Nat.mod_lt _ (by decide)
  have h := wheel_indexed ⟨i.val / 10,hq⟩ ⟨i.val % 10,hr⟩
  have he : i.val % 10 + i.val / 10 * 10 = i.val := by omega
  simpa only [he] using h
theorem wheel_permutations_fail : ∀ s ∈ [(1:Fin 6),2,3,4,5].permutations', ∀ t ∈ [(1:Fin 6),2,3,4,5].permutations', ¬Matches wheel (gapWord s t) := by
  intro s hs t ht
  have hm : s ∈ wheelPermutations := hs
  have hi : wheelPermutations.idxOf s < wheelPermutations.length := List.idxOf_lt_length_of_mem hm
  have hib : wheelPermutations.idxOf s < 120 := by simpa only [wheelPermutations_length] using hi
  have he : wheelPermutations.getD (wheelPermutations.idxOf s) [] = s := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_idxOf hi
  have h := wheel_all_indices ⟨wheelPermutations.idxOf s,hib⟩ t ht
  simpa only [he] using h
#print axioms wheel_permutations_fail
end Crown.SmallGraphs
