import generated.PairingStored4Check0000
import generated.PairingStored4Check0001
import generated.PairingStored4Check0002
import generated.PairingStored4Check0003
import generated.PairingStored4Check0004
import generated.PairingStored4Check0005
import generated.PairingStored4Check0006
import generated.PairingStored4Check0007
import generated.PairingStored4Check0008
import generated.PairingStored4Check0009
import generated.PairingStored4Check0010
import generated.PairingStored4Check0011
import generated.PairingStored4Check0012
import generated.PairingStored4Check0013
import generated.PairingStored4Check0014
import generated.PairingStored4Check0015
import generated.PairingStored4Check0016
import generated.PairingStored4Check0017
import generated.PairingStored4Check0018
import generated.PairingStored4Check0019
import generated.PairingStored4Check0020

namespace Crown.PairingStored4
open Crown.PairingCoordinates Crown.PairingCoverage Crown.Matchings Crown.MatchingRepresentatives
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem inverse_all (t : Fin 840) : inverseFingerprint (fingerprint (stored t)) = t := by
  have hall (b : Fin 21) (r : Fin 40) :
      inverseFingerprint (fingerprint (stored (⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ : Fin 840))) = ⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    fin_cases b
    · exact inverse_batch0000 r
    · exact inverse_batch0001 r
    · exact inverse_batch0002 r
    · exact inverse_batch0003 r
    · exact inverse_batch0004 r
    · exact inverse_batch0005 r
    · exact inverse_batch0006 r
    · exact inverse_batch0007 r
    · exact inverse_batch0008 r
    · exact inverse_batch0009 r
    · exact inverse_batch0010 r
    · exact inverse_batch0011 r
    · exact inverse_batch0012 r
    · exact inverse_batch0013 r
    · exact inverse_batch0014 r
    · exact inverse_batch0015 r
    · exact inverse_batch0016 r
    · exact inverse_batch0017 r
    · exact inverse_batch0018 r
    · exact inverse_batch0019 r
    · exact inverse_batch0020 r
  let b : Fin 21 := ⟨t.val/40,by omega⟩
  let r : Fin 40 := ⟨t.val%40,by omega⟩
  have ht : t = ⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [b,r]
    omega
  simpa only [←ht] using hall b r

theorem anchored (t : Fin 840) : ∃ i, stored t (i,false) = 0 := by
  refine ⟨0,?_⟩
  have hall (b : Fin 21) (r : Fin 40) :
      stored (⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ : Fin 840) (0,false) = 0 := by
    fin_cases b
    · exact anchor_batch0000 r
    · exact anchor_batch0001 r
    · exact anchor_batch0002 r
    · exact anchor_batch0003 r
    · exact anchor_batch0004 r
    · exact anchor_batch0005 r
    · exact anchor_batch0006 r
    · exact anchor_batch0007 r
    · exact anchor_batch0008 r
    · exact anchor_batch0009 r
    · exact anchor_batch0010 r
    · exact anchor_batch0011 r
    · exact anchor_batch0012 r
    · exact anchor_batch0013 r
    · exact anchor_batch0014 r
    · exact anchor_batch0015 r
    · exact anchor_batch0016 r
    · exact anchor_batch0017 r
    · exact anchor_batch0018 r
    · exact anchor_batch0019 r
    · exact anchor_batch0020 r
  let b : Fin 21 := ⟨t.val/40,by omega⟩
  let r : Fin 40 := ⟨t.val%40,by omega⟩
  have ht : t = ⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [b,r]
    omega
  simpa only [←ht] using hall b r

theorem fingerprint_injective : Function.Injective (fun t => fingerprint (stored t)) := by
  intro a b h
  have hh := congrArg inverseFingerprint h
  simpa only [inverse_all] using hh

theorem anchored_complete (q : AnchoredPairing 4 0) : ∃ t, ofCoordinates (stored t) = q.val :=
  anchored_family_complete 0 stored anchored fingerprint_injective (card_anchoredPairing4).symm q

theorem complete (p : Coordinates 4) : ∃ t, ofCoordinates (stored t) = ofCoordinates p ∨
    ofCoordinates (stored t) = Crown.MatchingReversal.reverseOriented (ofCoordinates p) :=
  family_complete_up_to_reversal 0 stored anchored_complete p

theorem all_bad_iff {V : Type*} (N : V → Fin 8 → Bool) :
    (∀ p : Coordinates 4, ¬Crown.Ranks.Feasible (rankRows p N)) ↔
      ∀ t, ¬Crown.Ranks.Feasible (rankRows (stored t) N) :=
  all_bad_iff_stored stored complete N

#print axioms inverse_all
#print axioms anchored_complete
#print axioms complete
#print axioms all_bad_iff
end Crown.PairingStored4
