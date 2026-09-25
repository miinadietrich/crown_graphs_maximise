import Crown.SmallGraphsSixTables
import Crown.SmallGraphsTransfer
import Crown.SmallGraphPrism
import Crown.SmallGraphWheel

namespace Crown.SmallGraphs

/-- A checked lookup entry supplies either an actual representative or an
isomorphism from one of the two explicitly labelled exceptions. -/
theorem classify_mask (m : Fin 32768) :
    Crown.KRepresentable (graph 6 m.val) 2 ∨
      Nonempty (prism ≃g graph 6 m.val) ∨ Nonempty (wheel ≃g graph 6 m.val) := by
  classical
  obtain ⟨hkind,hrep,hperm,hupper⟩ := six_tables m
  have hadj := relation_of_upper (candidatePermutation m.val) hupper
  have hb : Function.Bijective (candidatePermutation m.val) :=
    all_vertex_permutations ⟨(candidateRecord m.val).2.2,hperm⟩
  let e := Equiv.ofBijective (candidatePermutation m.val) hb
  let eg : graph 6 (candidateSource m.val) ≃g graph 6 m.val :=
    { toEquiv := e, map_rel_iff' := by intro a b; exact hadj a b }
  by_cases hk : (candidateRecord m.val).1 = 0
  · left
    apply representable_iso eg
    have hi := hrep hk
    simpa [candidateSource,hk] using
      (show Crown.KRepresentable (graph 6 (representativeMasks.getD (candidateRecord m.val).2.1 0)) 2 from
        ⟨_,six_representatives ⟨(candidateRecord m.val).2.1,hi⟩⟩)
  · right
    by_cases hk1 : (candidateRecord m.val).1 = 1
    · left; exact ⟨by simpa [candidateSource,hk,hk1,prism] using eg⟩
    · right; exact ⟨by simpa [candidateSource,hk,hk1,wheel] using eg⟩

theorem classify_six (G : SimpleGraph (Fin 6)) :
    Crown.KRepresentable G 2 ∨ Nonempty (prism ≃g G) ∨ Nonempty (wheel ≃g G) := by
  obtain ⟨m,hm⟩ := encode_graph 6 G
  have hlen : (pairs 6).length = 15 := by decide
  have hmb : m.val < 32768 := by simpa [hlen] using m.isLt
  rw [← hm]
  exact classify_mask ⟨m.val,hmb⟩

theorem six_iff (G : SimpleGraph (Fin 6)) :
    Crown.KRepresentable G 2 ↔ ¬Nonempty (prism ≃g G) ∧ ¬Nonempty (wheel ≃g G) := by
  constructor
  · intro h
    constructor
    · rintro ⟨e⟩; exact prism_not_two (representable_iso e.symm h)
    · rintro ⟨e⟩; exact wheel_not_two (representable_iso e.symm h)
  · intro h
    rcases classify_six G with hp | hp | hw
    · exact hp
    · exact False.elim (h.1 hp)
    · exact False.elim (h.2 hw)

#print axioms classify_six
#print axioms six_iff
end Crown.SmallGraphs
