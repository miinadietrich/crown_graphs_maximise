import Crown.PairingCoordinates

/-! Completeness criteria for stored oriented-pairing representatives. The
finite fingerprint check is only an injectivity witness; cardinality comes
from the independently proved oriented unordered pairing count. -/
namespace Crown.PairingCoverage
open Crown.Matchings Crown.MatchingRepresentatives Crown.MatchingReversal
open Crown.PairingCoordinates Crown.Ranks

set_option backward.isDefEq.respectTransparency false

theorem coordinate_change {k : ℕ} (p q : Coordinates k)
    (h : ofCoordinates p = ofCoordinates q) :
    ∃ e : Equiv.Perm (Fin k), ∀ i b, q (e i,b) = p (i,b) := by
  classical
  have hp : ∀ i, ∃ j, q (j,false) = p (i,false) ∧ q (j,true) = p (i,true) := by
    intro i
    apply (directed_ofCoordinates q _ _).mp
    rw [← h]
    exact (directed_ofCoordinates p _ _).mpr ⟨i,rfl,rfl⟩
  let f : Fin k → Fin k := fun i => Classical.choose (hp i)
  have hf : ∀ i b, q (f i,b) = p (i,b) := by
    intro i b
    cases b
    · exact (Classical.choose_spec (hp i)).1
    · exact (Classical.choose_spec (hp i)).2
  have hinj : Function.Injective f := by
    intro i j hij
    have he : p (i,false) = p (j,false) := (hf i false).symm.trans ((congrArg (fun a => q (a,false)) hij).trans (hf j false))
    exact congrArg Prod.fst (p.injective he)
  exact ⟨Equiv.ofBijective f ⟨hinj,Finite.surjective_of_injective hinj⟩,hf⟩

theorem anchored_family_complete {k n : ℕ} (v : Fin (2*k))
    (family : Fin n → Coordinates k)
    (ha : ∀ t, ∃ i, family t (i,false) = v)
    (hi : Function.Injective (fun t => fingerprint (family t)))
    (hc : n = Fintype.card (AnchoredPairing k v)) :
    ∀ q : AnchoredPairing k v, ∃ t, ofCoordinates (family t) = q.val := by
  classical
  let f : Fin n → AnchoredPairing k v := fun t => ⟨ofCoordinates (family t),by
    obtain ⟨i,he⟩ := ha t
    change v ∈ firstSet (family t)
    rw [← he]
    simp⟩
  have hf : Function.Injective f := by
    intro s t h
    apply hi
    exact fingerprint_eq_of_pairing_eq _ _ (congrArg Subtype.val h)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simpa using hc⟩
  intro q
  obtain ⟨t,ht⟩ := hbij.surjective q
  exact ⟨t,congrArg Subtype.val ht⟩

theorem family_complete_up_to_reversal {k n : ℕ} (v : Fin (2*k))
    (family : Fin n → Coordinates k)
    (hfamily : ∀ q : AnchoredPairing k v, ∃ t, ofCoordinates (family t) = q.val)
    (p : Coordinates k) :
    ∃ t, ofCoordinates (family t) = ofCoordinates p ∨
      ofCoordinates (family t) = reverseOriented (ofCoordinates p) := by
  obtain ⟨q,hq,_⟩ := unique_anchored_representative v (ofCoordinates p)
  obtain ⟨t,ht⟩ := hfamily q
  refine ⟨t,?_⟩
  rw [ht]
  exact hq

def rankRows {k : ℕ} {V : Type*} (p : Coordinates k) (N : V → Fin (2*k) → Bool) :
    V → InitialRow (Fin k) := fun v i =>
      Crown.Orientations.entry (N v (p (i,false)),N v (p (i,true))) false

theorem feasible_reindex {I J V : Type*} (e : I ≃ J) (rows : V → InitialRow J) :
    Feasible (fun v i => rows v (e i)) ↔ Feasible rows := by
  constructor
  · rintro ⟨r,hr,hn⟩
    refine ⟨fun v j => r v (e.symm j),?_,?_⟩
    · intro v j
      simpa using hr v (e.symm j)
    · intro v w hvw
      apply hn v w
      intro i
      simpa using hvw (e i)
  · rintro ⟨r,hr,hn⟩
    refine ⟨fun v i => r v (e i),fun v i => hr v (e i),?_⟩
    intro v w hvw
    apply hn v w
    intro j
    simpa using hvw (e.symm j)

theorem feasible_of_pairing_eq {k : ℕ} {V : Type*} (p q : Coordinates k)
    (h : ofCoordinates p = ofCoordinates q) (N : V → Fin (2*k) → Bool) :
    Feasible (rankRows p N) ↔ Feasible (rankRows q N) := by
  obtain ⟨e,he⟩ := coordinate_change p q h
  have hr : rankRows p N = fun v i => rankRows q N v (e i) := by
    funext v i
    simp only [rankRows,he]
  rw [hr]
  exact feasible_reindex e _

theorem feasible_reverse {k : ℕ} {V : Type*} (p : Coordinates k)
    (N : V → Fin (2*k) → Bool) :
    Feasible (rankRows (reverseCoordinates p) N) ↔ Feasible (rankRows p N) := by
  have hr : rankRows (reverseCoordinates p) N =
      fun v => Crown.RankReversal.mirror (rankRows p N v) := by
    funext v i
    change Crown.Orientations.entry (N v (p (i,true)),N v (p (i,false))) false =
      (Crown.Orientations.entry (N v (p (i,false)),N v (p (i,true))) false).map Fin.rev
    cases N v (p (i,false)) <;> cases N v (p (i,true)) <;> rfl
  rw [hr]
  exact Crown.RankReversal.feasible_mirror_iff _

theorem all_bad_iff_stored {k n : ℕ} {V : Type*}
    (family : Fin n → Coordinates k)
    (hfamily : ∀ p, ∃ t, ofCoordinates (family t) = ofCoordinates p ∨
      ofCoordinates (family t) = reverseOriented (ofCoordinates p))
    (N : V → Fin (2*k) → Bool) :
    (∀ p, ¬Feasible (rankRows p N)) ↔ ∀ t, ¬Feasible (rankRows (family t) N) := by
  constructor
  · intro h t
    exact h (family t)
  · intro h p hp
    obtain ⟨t,ht|ht⟩ := hfamily p
    · exact h t ((feasible_of_pairing_eq _ _ ht N).mpr hp)
    · have he : ofCoordinates (family t) = ofCoordinates (reverseCoordinates p) :=
        ht.trans (ofCoordinates_reverse p).symm
      exact h t ((feasible_of_pairing_eq _ _ he N).mpr ((feasible_reverse p N).mpr hp))

#print axioms anchored_family_complete
#print axioms family_complete_up_to_reversal
#print axioms coordinate_change
#print axioms feasible_of_pairing_eq
#print axioms feasible_reverse
#print axioms all_bad_iff_stored
end Crown.PairingCoverage
