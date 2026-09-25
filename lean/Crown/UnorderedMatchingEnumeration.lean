import Crown.UnorderedMatchings
import Mathlib.Data.Finset.Max

/-! A complete recursive enumeration of unordered pairings. Each stage pairs
only the smallest remaining vertex, so no ordering or endpoint orientation is
enumerated. Completeness is proved before any finite cardinality evaluation. -/
namespace Crown.UnorderedMatchings
variable {V : Type*} [LinearOrder V]

def enumerate : ℕ → Finset V → Finset (Finset (Finset V))
  | 0, S => if S = ∅ then {∅} else ∅
  | d+1, S => if h : S.Nonempty then
      let a := S.min' h
      (S.erase a).biUnion fun b =>
        (enumerate d ((S.erase a).erase b)).image (fun P => insert {a,b} P)
    else ∅

private theorem pair_with_member {e : Finset V} {a : V} (he : e.card = 2) (ha : a ∈ e) :
    ∃ b, a ≠ b ∧ e = {a,b} := by
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨v,huv,rfl⟩
  · exact ⟨u,Ne.symm huv,Finset.pair_comm _ _⟩

private theorem remove_pair {P : Finset (Finset V)} {S : Finset V} {a b : V}
    (hd : DisjointPairs P) (hu : P.biUnion id = S) (he : {a,b} ∈ P) :
    (P.erase {a,b}).biUnion id = (S.erase a).erase b := by
  ext x
  simp only [Finset.mem_biUnion,Finset.mem_erase]
  constructor
  · rintro ⟨e,⟨hne,hm⟩,hx⟩
    have hxa : x ≠ a := by
      intro heq
      have hdis := hd e hm {a,b} he hne
      exact Finset.disjoint_left.mp hdis hx (by simp [heq])
    have hxb : x ≠ b := by
      intro heq
      have hdis := hd e hm {a,b} he hne
      exact Finset.disjoint_left.mp hdis hx (by simp [heq])
    refine ⟨hxb,hxa,?_⟩
    rw [← hu]
    exact Finset.mem_biUnion.mpr ⟨e,hm,hx⟩
  · rintro ⟨hxb,hxa,hx⟩
    rw [← hu] at hx
    obtain ⟨e,hm,hxe⟩ := Finset.mem_biUnion.mp hx
    refine ⟨e,⟨?_,hm⟩,hxe⟩
    intro heq
    subst e
    simpa [hxa,hxb] using hxe

/-- Every actual partition occurs in the recursive enumeration. -/
theorem enumerate_complete (d : ℕ) (S : Finset V) (P : Finset (Finset V))
    (he : ∀ e ∈ P, e.card = 2) (hd : DisjointPairs P)
    (hu : P.biUnion id = S) (hc : P.card = d) : P ∈ enumerate d S := by
  induction d generalizing S P with
  | zero =>
    have hp : P = ∅ := Finset.card_eq_zero.mp hc
    subst P
    have hs : S = ∅ := by simpa using hu.symm
    simp [enumerate,hs]
  | succ d ih =>
    have hPn : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e0,he0⟩ := hPn
    have he0n : e0.Nonempty := Finset.card_pos.mp (by rw [he e0 he0]; decide)
    obtain ⟨x,hx⟩ := he0n
    have hSn : S.Nonempty := ⟨x,by rw [← hu]; exact Finset.mem_biUnion.mpr ⟨e0,he0,hx⟩⟩
    let a := S.min' hSn
    have haS : a ∈ S := Finset.min'_mem _ hSn
    have haU : a ∈ P.biUnion id := by simpa [hu] using haS
    obtain ⟨e,heP,hae⟩ := Finset.mem_biUnion.mp haU
    obtain ⟨b,hab,heb⟩ := pair_with_member (he e heP) hae
    subst e
    have hbS : b ∈ S := by
      rw [← hu]
      exact Finset.mem_biUnion.mpr ⟨{a,b},heP,by simp⟩
    have hb : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,hbS⟩
    have hrem : P.erase {a,b} ∈ enumerate d ((S.erase a).erase b) := by
      apply ih
      · intro e hee
        exact he e (Finset.mem_of_mem_erase hee)
      · intro e hee f hff hne
        exact hd e (Finset.mem_of_mem_erase hee) f (Finset.mem_of_mem_erase hff) hne
      · exact remove_pair hd hu heP
      · rw [Finset.card_erase_of_mem heP,hc]
        omega
    rw [enumerate,dif_pos hSn]
    apply Finset.mem_biUnion.mpr
    refine ⟨b,hb,Finset.mem_image.mpr ⟨P.erase {a,b},hrem,?_⟩⟩
    exact Finset.insert_erase heP

#print axioms enumerate_complete
end Crown.UnorderedMatchings
