import Crown.CrownLowerSegments

/-! Splittable sets in the sense of Glen--Kitaev--Pyatkin, Section 2.
The definition requires an actual cyclic shift of the word and actual list
permutations, including all letters of the designated set. -/

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def IsPermutationOf (A : Set V) (l : List V) : Prop :=
  l.Nodup ∧ ∀ a, a ∈ l ↔ a ∈ A

def Splittable (w : List V) (k : ℕ) (A : Set V) : Prop := by
  classical
  exact ∃ u v : List V, ∃ L : List (List V), w = u ++ v ∧
    (v ++ u).filter (fun a => a ∈ A) = L.flatten ∧
    L.length = k ∧ ∀ l ∈ L, IsPermutationOf A l

/-- Proposition 1 of Glen--Kitaev--Pyatkin, proved from the list definition
of a uniform word representation and its cyclic invariance. -/
theorem neighbourhood_splittable {G : SimpleGraph V} {k : ℕ} {w : List V}
    (hw : Crown.Represents G k w) (v : V) : Splittable w k {a | G.Adj v a} := by
  classical
  have hv : v ∈ w := List.count_pos_iff.mp (by rw [hw.2.1 v]; exact hw.1)
  obtain ⟨u,t,hwt⟩ := List.mem_iff_append.mp hv
  have hrot : Crown.Represents G k ((v :: t) ++ u) :=
    Crown.represents_append_swap (by simpa only [hwt] using hw)
  obtain ⟨L,hL,hno⟩ := exists_segments_start v (t ++ u)
  have hrep : Crown.Represents G k (L.flatMap (fun l => v :: l)) := by
    rw [← hL]; exact hrot
  have hlen : L.length = k := (count_separator v L hno).symm.trans (hrep.2.1 v)
  have hcount : ∀ a, G.Adj v a → ∀ l ∈ L, l.count a = 1 := by
    intro a hva
    have hne : v ≠ a := G.ne_of_adj hva
    exact segment_neighbour_count v a hne L hno ((hrep.2.2 v a hne).mp hva)
      ((hrep.2.1 a).trans hlen.symm)
  let P := L.map (fun l => l.filter (fun a => G.Adj v a))
  refine ⟨u,v::t,P,hwt,?_,by simpa [P] using hlen,?_⟩
  · change ((v::t)++u).filter (fun a => G.Adj v a) = P.flatten
    rw [show (v::t)++u = L.flatMap (fun l => v::l) from hL]
    simp [P, List.flatMap_def, Function.comp_def]
  · intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    constructor
    · apply List.nodup_iff_count_eq_one.mpr
      intro a ha
      have hadj : G.Adj v a := by simpa using (List.mem_filter.mp ha).2
      rw [List.count_filter (by simpa using hadj)]
      exact hcount a hadj l hl
    · intro a
      constructor
      · intro ha; simpa using (List.mem_filter.mp ha).2
      · intro ha
        apply List.mem_filter.mpr
        exact ⟨List.count_pos_iff.mp (by rw [hcount a ha l hl]; omega), by simpa using ha⟩

theorem endpoint_card_bound {A : Type*} [Fintype A] {k : ℕ}
    (ends : Fin k × Bool → A) (hcover : Function.Surjective ends) :
    Fintype.card A ≤ 2*k := by
  have h := Fintype.card_le_of_surjective ends hcover
  simpa [Fintype.card_prod, Nat.mul_comm] using h

#print axioms neighbourhood_splittable
#print axioms endpoint_card_bound

end Crown.CrownLower
