import Crown.PairingStoredThreeSemantics
import Crown.PairingStoredFourSemantics

/-! Direct statements for the actual stored representative families.
The coordinate formulas expose pair-order permutation and one simultaneous
endpoint reversal, without quotient or fingerprint assumptions. -/
namespace Crown.PairingStored3
open Crown.PairingCoordinates Crown.PairingCoverage

theorem coordinates_complete (p : Coordinates 3) :
    ∃ t : Fin 60, ∃ e : Equiv.Perm (Fin 3),
      (∀ i b, stored t (e i,b) = p (i,b)) ∨
      (∀ i b, stored t (e i,b) = p (i,!b)) := by
  obtain ⟨t,ht|ht⟩ := complete p
  · obtain ⟨e,he⟩ := coordinate_change p (stored t) ht.symm
    exact ⟨t,e,Or.inl he⟩
  · have hh : ofCoordinates (stored t) = ofCoordinates (reverseCoordinates p) :=
      ht.trans (ofCoordinates_reverse p).symm
    obtain ⟨e,he⟩ := coordinate_change (reverseCoordinates p) (stored t) hh.symm
    exact ⟨t,e,Or.inr he⟩

#print axioms coordinates_complete
end Crown.PairingStored3

namespace Crown.PairingStored4
open Crown.PairingCoordinates Crown.PairingCoverage

theorem coordinates_complete (p : Coordinates 4) :
    ∃ t : Fin 840, ∃ e : Equiv.Perm (Fin 4),
      (∀ i b, stored t (e i,b) = p (i,b)) ∨
      (∀ i b, stored t (e i,b) = p (i,!b)) := by
  obtain ⟨t,ht|ht⟩ := complete p
  · obtain ⟨e,he⟩ := coordinate_change p (stored t) ht.symm
    exact ⟨t,e,Or.inl he⟩
  · have hh : ofCoordinates (stored t) = ofCoordinates (reverseCoordinates p) :=
      ht.trans (ofCoordinates_reverse p).symm
    obtain ⟨e,he⟩ := coordinate_change (reverseCoordinates p) (stored t) hh.symm
    exact ⟨t,e,Or.inr he⟩

#print axioms coordinates_complete
end Crown.PairingStored4
