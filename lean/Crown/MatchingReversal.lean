import Crown.MatchingRepresentatives

/-! Simultaneous reversal of all endpoint orientations and its unique
representative whose distinguished vertex is a first endpoint. -/

namespace Crown.MatchingReversal
open Crown.Matchings Crown.MatchingRepresentatives
open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def reversePairing (p : PairingOn V) : PairingOn V :=
  ⟨p.1ᶜ, {
    toFun := fun a =>
      let b := p.2.symm ⟨a.val,Finset.mem_compl.mp a.property⟩
      ⟨b.val,by simpa using b.property⟩
    invFun := fun b =>
      let a := p.2 ⟨b.val,by simpa using b.property⟩
      ⟨a.val,Finset.mem_compl.mpr a.property⟩
    left_inv := by
      intro a
      apply Subtype.ext
      change (p.2 (p.2.symm ⟨a.val,Finset.mem_compl.mp a.property⟩)).val = a.val
      exact congrArg (fun x => x.val) (p.2.apply_symm_apply ⟨a.val,Finset.mem_compl.mp a.property⟩)
    right_inv := by
      intro b
      apply Subtype.ext
      change (p.2.symm (p.2 ⟨b.val,by simpa using b.property⟩)).val = b.val
      exact congrArg (fun x => x.val) (p.2.symm_apply_apply ⟨b.val,by simpa using b.property⟩) }⟩

theorem reversePairing_first (p : PairingOn V) : (reversePairing p).1 = p.1ᶜ := rfl

theorem directedPair_reverse (p : PairingOn V) (a b : V) :
    DirectedPair (reversePairing p) a b ↔ DirectedPair p b a := by
  constructor
  · intro h
    have ha : a ∉ p.1 := Finset.mem_compl.mp h.1
    have hb : b ∈ p.1 := by simpa only [reversePairing_first,Finset.notMem_compl] using h.2.1
    refine ⟨hb,ha,?_⟩
    intro hb' ha'
    apply p.2.symm.injective
    rw [p.2.symm_apply_apply]
    apply Subtype.ext
    exact (congrArg Subtype.val (h.2.2 h.1 h.2.1)).symm
  · intro h
    refine ⟨Finset.mem_compl.mpr h.2.1,?_,?_⟩
    · simpa only [reversePairing_first,Finset.notMem_compl] using h.1
    · intro ha hb
      apply Subtype.ext
      change (p.2.symm ⟨a,h.2.1⟩).val = b
      rw [← h.2.2 h.1 h.2.1,p.2.symm_apply_apply]

theorem mem_first_iff_directedPair (p : PairingOn V) (a : V) :
    a ∈ p.1 ↔ ∃ b, DirectedPair p a b := by
  constructor
  · intro ha
    exact ⟨(p.2 ⟨a,ha⟩).val,ha,(p.2 ⟨a,ha⟩).property,fun _ _ => rfl⟩
  · rintro ⟨b,hb⟩
    exact hb.1

theorem pairing_ext (p q : PairingOn V)
    (h : ∀ a b, DirectedPair p a b ↔ DirectedPair q a b) : p = q := by
  have hs : p.1 = q.1 := by
    ext a
    rw [mem_first_iff_directedPair,mem_first_iff_directedPair]
    exact exists_congr (fun b => h a b)
  rcases p with ⟨s,e⟩
  rcases q with ⟨t,f⟩
  change s = t at hs
  subst t
  apply congrArg (fun e : {v // v ∈ s} ≃ {v // v ∉ s} => (⟨s,e⟩ : PairingOn V))
  apply Equiv.ext
  intro a
  apply Subtype.ext
  have he : DirectedPair (⟨s,e⟩ : PairingOn V) a.val (e a).val :=
    ⟨a.property,(e a).property,fun _ _ => rfl⟩
  have hf := (h a.val (e a).val).mp he
  exact (congrArg Subtype.val (hf.2.2 a.property (e a).property)).symm

theorem reversePairing_involutive (p : PairingOn V) : reversePairing (reversePairing p) = p := by
  apply pairing_ext
  intro a b
  rw [directedPair_reverse,directedPair_reverse]

noncomputable def reversalEquiv : PairingOn V ≃ PairingOn V where
  toFun := reversePairing
  invFun := reversePairing
  left_inv := reversePairing_involutive
  right_inv := reversePairing_involutive

noncomputable def reverseOriented {k : ℕ} (p : OrientedPairing k) : OrientedPairing k :=
  (constrainedEquiv k).symm (reversePairing (constrainedEquiv k p))

theorem reverseOriented_first {k : ℕ} (p : OrientedPairing k) :
    (reverseOriented p).1.val = p.1.valᶜ := rfl

theorem reverseOriented_involutive {k : ℕ} (p : OrientedPairing k) :
    reverseOriented (reverseOriented p) = p := by
  simp only [reverseOriented,Equiv.apply_symm_apply,reversePairing_involutive,Equiv.symm_apply_apply]

theorem reverseOriented_directed {k : ℕ} (p : OrientedPairing k) (a b : Fin (2*k)) :
    DirectedPair (constrainedEquiv k (reverseOriented p)) a b ↔
      DirectedPair (constrainedEquiv k p) b a := by
  simp only [reverseOriented,Equiv.apply_symm_apply,directedPair_reverse]

/-- Each simultaneous-reversal orbit has exactly one anchored representative. -/
theorem unique_anchored_representative {k : ℕ} (v : Fin (2*k)) (p : OrientedPairing k) :
    ∃! q : AnchoredPairing k v, q.val = p ∨ q.val = reverseOriented p := by
  by_cases hv : v ∈ p.1.val
  · refine ⟨⟨p,hv⟩,Or.inl rfl,?_⟩
    intro q hq
    rcases hq with he | he
    · exact Subtype.ext he
    · have hn : v ∉ (reverseOriented p).1.val := by simp [reverseOriented_first,hv]
      exact False.elim (hn (he ▸ q.property))
  · have hr : v ∈ (reverseOriented p).1.val := by simp [reverseOriented_first,hv]
    refine ⟨⟨reverseOriented p,hr⟩,Or.inr rfl,?_⟩
    intro q hq
    rcases hq with he | he
    · exact False.elim (hv (he ▸ q.property))
    · exact Subtype.ext he

#print axioms directedPair_reverse
#print axioms reverseOriented_involutive
#print axioms unique_anchored_representative

end Crown.MatchingReversal
