import Crown.SmallGraphsFive
import Crown.SmallGraphGaps
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Crown.SmallGraphs

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem representable_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {k : ℕ} (h : Crown.KRepresentable G k) : Crown.KRepresentable H k := by
  obtain ⟨w,hw⟩ := h
  exact ⟨_,Crown.represents_equiv e.toEquiv (fun _ _ => e.map_rel_iff) hw⟩

theorem at_most_five [Fintype V] (G : SimpleGraph V) (hc : Fintype.card V ≤ 5) :
    Crown.KRepresentable G 2 := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card V ≤ Fintype.card (Fin 5) by simpa using hc)
  exact Crown.kRepresentable_of_inducedEmbedding f (fun _ _ => SimpleGraph.map_adj_apply.symm)
    (all_five (G.map f))

/-- Multiplicity one upgrades to two by repeating the actual permutation. -/
theorem one_to_two {G : SimpleGraph V} (h : Crown.KRepresentable G 1) :
    Crown.KRepresentable G 2 := by
  obtain ⟨w,hw⟩ := h
  have hnd : w.Nodup := List.nodup_iff_count.mpr (fun a => by rw [hw.2.1 a])
  have hm : ∀ a, a ∈ w := fun a => List.count_pos_iff.mp (by rw [hw.2.1 a]; decide)
  refine ⟨w++w,by decide,?_,?_⟩
  · intro a; simp only [List.count_append,hw.2.1 a]
  · intro a b hab
    have ha : G.Adj a b := Crown.one_uniform_complete ⟨w,hw⟩ a b hab
    refine iff_of_true ha ?_
    unfold Crown.Alternates
    rw [Crown.restrictPair_append,Crown.Blocks.restrictPair_permutation w hnd a b (hm a) (hm b) hab]
    split_ifs <;> simp [List.isChain_cons_cons,hab,Ne.symm hab]

/-- The default zero for nonrepresentable graphs is excluded explicitly. -/
theorem number_le_two_iff {G : SimpleGraph V} (hr : Crown.Representable G) :
    Crown.representationNumber G ≤ 2 ↔ Crown.KRepresentable G 2 := by
  constructor
  · intro h
    have hp := Crown.representationNumber_pos hr
    have hs := Crown.representationNumber_spec hr
    have he : Crown.representationNumber G = 1 ∨ Crown.representationNumber G = 2 := by omega
    rcases he with he | he
    · exact one_to_two (he ▸ hs)
    · exact he ▸ hs
  · exact Crown.representationNumber_le

#print axioms at_most_five
#print axioms one_to_two
#print axioms number_le_two_iff
end Crown.SmallGraphs
