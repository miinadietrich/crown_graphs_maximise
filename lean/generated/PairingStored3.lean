import generated.PairingStored3Check0000
import generated.PairingStored3Check0001
import generated.PairingStored3Check0002

namespace Crown.PairingStored3
open Crown.PairingCoordinates Crown.PairingCoverage Crown.Matchings Crown.MatchingRepresentatives
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem inverse_all (t : Fin 60) : inverseFingerprint (fingerprint (stored t)) = t := by
  have hall (b : Fin 3) (r : Fin 20) :
      inverseFingerprint (fingerprint (stored (⟨20*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ : Fin 60))) = ⟨20*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    fin_cases b
    · exact inverse_batch0000 r
    · exact inverse_batch0001 r
    · exact inverse_batch0002 r
  let b : Fin 3 := ⟨t.val/20,by omega⟩
  let r : Fin 20 := ⟨t.val%20,by omega⟩
  have ht : t = ⟨20*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [b,r]
    omega
  simpa only [←ht] using hall b r

theorem anchored (t : Fin 60) : ∃ i, stored t (i,false) = 0 := by
  refine ⟨0,?_⟩
  have hall (b : Fin 3) (r : Fin 20) :
      stored (⟨20*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ : Fin 60) (0,false) = 0 := by
    fin_cases b
    · exact anchor_batch0000 r
    · exact anchor_batch0001 r
    · exact anchor_batch0002 r
  let b : Fin 3 := ⟨t.val/20,by omega⟩
  let r : Fin 20 := ⟨t.val%20,by omega⟩
  have ht : t = ⟨20*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [b,r]
    omega
  simpa only [←ht] using hall b r

theorem fingerprint_injective : Function.Injective (fun t => fingerprint (stored t)) := by
  intro a b h
  have hh := congrArg inverseFingerprint h
  simpa only [inverse_all] using hh

theorem anchored_complete (q : AnchoredPairing 3 0) : ∃ t, ofCoordinates (stored t) = q.val :=
  anchored_family_complete 0 stored anchored fingerprint_injective (card_anchoredPairing3).symm q

theorem complete (p : Coordinates 3) : ∃ t, ofCoordinates (stored t) = ofCoordinates p ∨
    ofCoordinates (stored t) = Crown.MatchingReversal.reverseOriented (ofCoordinates p) :=
  family_complete_up_to_reversal 0 stored anchored_complete p

theorem all_bad_iff {V : Type*} (N : V → Fin 6 → Bool) :
    (∀ p : Coordinates 3, ¬Crown.Ranks.Feasible (rankRows p N)) ↔
      ∀ t, ¬Crown.Ranks.Feasible (rankRows (stored t) N) :=
  all_bad_iff_stored stored complete N

#print axioms inverse_all
#print axioms anchored_complete
#print axioms complete
#print axioms all_bad_iff
end Crown.PairingStored3
