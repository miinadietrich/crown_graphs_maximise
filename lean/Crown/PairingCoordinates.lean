import Crown.MatchingReversal
import Crown.RankReversal

/-! Coordinate presentations of oriented unordered pairings. Pair order is
forgotten; endpoint orientation is retained. All vertex domains are unchanged. -/
namespace Crown.PairingCoordinates
open Crown.Matchings Crown.MatchingReversal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

abbrev Coordinates (k : ℕ) := (Fin k × Bool) ≃ Fin (2*k)

def firstSet {k : ℕ} (p : Coordinates k) : Finset (Fin (2*k)) :=
  Finset.univ.filter (fun a => (p.symm a).2 = false)

@[simp] theorem mem_firstSet {k : ℕ} (p : Coordinates k) (a : Fin (2*k)) :
    a ∈ firstSet p ↔ (p.symm a).2 = false := by simp [firstSet]

def firstEquiv {k : ℕ} (p : Coordinates k) : Fin k ≃ {a // a ∈ firstSet p} where
  toFun i := ⟨p (i,false),by simp⟩
  invFun a := (p.symm a.val).1
  left_inv i := by simp
  right_inv a := by
    apply Subtype.ext
    have ha := (mem_firstSet p a.val).mp a.property
    change p ((p.symm a.val).1,false) = a.val
    calc
      _ = p (p.symm a.val) := by
        apply congrArg p
        apply Prod.ext
        · rfl
        · exact ha.symm
      _ = _ := p.apply_symm_apply _

def secondEquiv {k : ℕ} (p : Coordinates k) : Fin k ≃ {a // a ∉ firstSet p} where
  toFun i := ⟨p (i,true),by simp⟩
  invFun a := (p.symm a.val).1
  left_inv i := by simp
  right_inv a := by
    apply Subtype.ext
    have ha : (p.symm a.val).2 = true := by
      have hn : (p.symm a.val).2 ≠ false := fun h => a.property ((mem_firstSet p _).mpr h)
      cases h : (p.symm a.val).2 <;> simp_all
    change p ((p.symm a.val).1,true) = a.val
    calc
      _ = p (p.symm a.val) := by
        apply congrArg p
        apply Prod.ext
        · rfl
        · exact ha.symm
      _ = _ := p.apply_symm_apply _

theorem firstSet_card {k : ℕ} (p : Coordinates k) : (firstSet p).card = k := by
  have h := Fintype.card_congr (firstEquiv p)
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm

def ofCoordinates {k : ℕ} (p : Coordinates k) : OrientedPairing k :=
  ⟨⟨firstSet p,firstSet_card p⟩,(firstEquiv p).symm.trans (secondEquiv p)⟩

theorem directed_ofCoordinates {k : ℕ} (p : Coordinates k) (a b : Fin (2*k)) :
    DirectedPair (constrainedEquiv k (ofCoordinates p)) a b ↔
      ∃ i, p (i,false) = a ∧ p (i,true) = b := by
  constructor
  · intro h
    let i := (firstEquiv p).symm ⟨a,h.1⟩
    refine ⟨i,?_,?_⟩
    · exact congrArg Subtype.val ((firstEquiv p).apply_symm_apply ⟨a,h.1⟩)
    · exact congrArg Subtype.val (h.2.2 h.1 h.2.1)
  · rintro ⟨i,rfl,rfl⟩
    refine ⟨by simp [constrainedEquiv,ofCoordinates],by simp [constrainedEquiv,ofCoordinates],?_⟩
    intro ha hb
    apply Subtype.ext
    change p (((firstEquiv p).symm ⟨p (i,false),ha⟩),true) = p (i,true)
    have h : (⟨p (i,false),ha⟩ : {a // a ∈ firstSet p}) = firstEquiv p i := rfl
    rw [h,Equiv.symm_apply_apply]

def permute {k : ℕ} (p : Coordinates k) (e : Equiv.Perm (Fin k)) : Coordinates k :=
  (Equiv.prodCongr e (Equiv.refl Bool)).trans p

theorem ofCoordinates_permute {k : ℕ} (p : Coordinates k) (e : Equiv.Perm (Fin k)) :
    ofCoordinates (permute p e) = ofCoordinates p := by
  apply (constrainedEquiv k).injective
  apply pairing_ext
  intro a b
  rw [directed_ofCoordinates,directed_ofCoordinates]
  constructor
  · rintro ⟨i,ha,hb⟩
    exact ⟨e i,ha,hb⟩
  · rintro ⟨i,ha,hb⟩
    refine ⟨e.symm i,?_,?_⟩
    · simpa [permute] using ha
    · simpa [permute] using hb

def flipEquiv (k : ℕ) : (Fin k × Bool) ≃ (Fin k × Bool) where
  toFun x := (x.1,!x.2)
  invFun x := (x.1,!x.2)
  left_inv x := by simp
  right_inv x := by simp

def reverseCoordinates {k : ℕ} (p : Coordinates k) : Coordinates k := (flipEquiv k).trans p

theorem ofCoordinates_reverse {k : ℕ} (p : Coordinates k) :
    ofCoordinates (reverseCoordinates p) = reverseOriented (ofCoordinates p) := by
  apply (constrainedEquiv k).injective
  apply pairing_ext
  intro a b
  rw [directed_ofCoordinates,reverseOriented_directed,directed_ofCoordinates]
  change (∃ i, p (i,true) = a ∧ p (i,false) = b) ↔ _
  exact exists_congr (fun _ => and_comm)

def fingerprint {k : ℕ} (p : Coordinates k) : ℕ :=
  ∑ i, (2*k+1) ^ (p (i,false)).val * ((p (i,true)).val+1)

noncomputable def pairingFingerprint {k : ℕ} (p : OrientedPairing k) : ℕ :=
  ∑ a : First p.1, (2*k+1)^a.val.val * ((p.2 a).val.val+1)

theorem fingerprint_ofCoordinates {k : ℕ} (p : Coordinates k) :
    pairingFingerprint (ofCoordinates p) = fingerprint p := by
  unfold pairingFingerprint fingerprint
  symm
  apply Fintype.sum_equiv (firstEquiv p)
  intro i
  change (2*k+1) ^ (p (i,false)).val * ((p (i,true)).val+1) =
    (2*k+1) ^ (p (i,false)).val * ((secondEquiv p ((firstEquiv p).symm (firstEquiv p i))).val.val+1)
  rw [Equiv.symm_apply_apply]
  rfl

theorem fingerprint_eq_of_pairing_eq {k : ℕ} (p q : Coordinates k)
    (h : ofCoordinates p = ofCoordinates q) : fingerprint p = fingerprint q := by
  rw [← fingerprint_ofCoordinates,← fingerprint_ofCoordinates,h]

#print axioms directed_ofCoordinates
#print axioms ofCoordinates_permute
#print axioms ofCoordinates_reverse
#print axioms fingerprint_eq_of_pairing_eq
end Crown.PairingCoordinates
