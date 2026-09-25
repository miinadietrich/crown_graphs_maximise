import Crown.CrownFourIntervals
import Mathlib.Data.List.Permutation

/-! Two actual gaps at a vertex of a two-uniform representation.
The gaps retain every other letter and its multiplicity. -/

namespace Crown.SmallGraphs

variable {V : Type*} [DecidableEq V]

theorem two_gaps {G : SimpleGraph V} {w : List V}
    (hr : Crown.Represents G 2 w) (v : V) :
    ∃ s t : List V, Crown.Represents G 2 ((v::s) ++ v::t) ∧
      v ∉ s ∧ v ∉ t ∧
      ∀ a, a ≠ v → (G.Adj v a ↔ s.count a = 1) := by
  obtain ⟨p,L,hw,hp,hL⟩ := Crown.CrownLower.exists_segments v w
  have hlen : L.length = 2 := by
    have hc := hr.2.1 v
    rw [hw,List.count_append,Crown.CrownLower.count_separator v L hL,
      List.count_eq_zero.mpr hp,Nat.zero_add] at hc
    exact hc
  obtain ⟨s,t,hLt⟩ := List.length_eq_two.mp hlen
  subst L
  have hs : v ∉ s := hL s (by simp)
  have ht : v ∉ t ++ p := by
    have ht := hL t (by simp)
    simpa using And.intro ht hp
  let W := (v::s) ++ v::(t++p)
  have hrot : Crown.Represents G 2 W := by
    have hh := Crown.represents_append_swap (hw ▸ hr)
    simpa [W,List.append_assoc] using hh
  refine ⟨s,t++p,hrot,hs,ht,?_⟩
  intro a hav
  have hva := Ne.symm hav
  constructor
  · intro ha
    have hc : Crown.Alternates ([s,t++p].flatMap (fun l => v::l)) v a := by
      simpa [W] using (hrot.2.2 v a hva).mp ha
    have hn : ∀ l ∈ [s,t++p], v ∉ l := by simpa using And.intro hs ht
    have hcounts : ([s,t++p].flatMap (fun l => v::l)).count a = [s,t++p].length := by
      simpa [W] using hrot.2.1 a
    exact Crown.CrownLower.segment_neighbour_count v a hva [s,t++p] hn hc hcounts s (by simp)
  · intro hsa
    have hta : (t++p).count a = 1 := by
      have hc := hrot.2.1 a
      simp [W,List.count_append,hva,hsa] at hc
      rw [List.count_append]
      omega
    have hrs : Crown.restrictPair s v a = [a] := by
      rw [Crown.Blocks.restrictPair_of_not_mem_left s v a hs,List.filter_eq,hsa]
      rfl
    have hrt : Crown.restrictPair (t++p) v a = [a] := by
      rw [Crown.Blocks.restrictPair_of_not_mem_left (t++p) v a ht,List.filter_eq,hta]
      rfl
    have he : Crown.restrictPair W v a = [v,a,v,a] := by
      simp only [W,Crown.restrictPair_append,Crown.Blocks.restrictPair_cons,
        true_or,if_true,hrs,hrt,List.cons_append,List.nil_append]
    apply (hrot.2.2 v a hva).mpr
    unfold Crown.Alternates
    rw [he]
    simp [List.isChain_cons_cons,hva,hav]

theorem gap_counts {G : SimpleGraph V} {s t : List V} {v a : V}
    (hr : Crown.Represents G 2 ((v::s) ++ v::t)) (hav : a ≠ v) :
    s.count a + t.count a = 2 := by
  simpa [List.count_append,Ne.symm hav] using hr.2.1 a

#print axioms two_gaps
#print axioms gap_counts

end Crown.SmallGraphs
