import Crown.CrownLowerBetween

/-! Lifting a partition of a filtered word to consecutive factors of the
original word. This is the list-level bridge needed for the interval-count
argument in the crown lower bound. -/

namespace Crown.CrownLower

variable {V : Type*}

theorem lift_filter_blocks (p : V → Bool) (w : List V) (L : List (List V))
    (hne : L ≠ []) (hfilter : w.filter p = L.flatten) :
    ∃ W : List (List V), W.flatten = w ∧ W.map (List.filter p) = L := by
  induction L generalizing w with
  | nil => exact False.elim (hne rfl)
  | cons l L ih =>
    cases L with
    | nil => exact ⟨[w],by simp,by simpa using hfilter⟩
    | cons t L =>
      have hf : w.filter p = l ++ (t::L).flatten := hfilter
      obtain ⟨u,v,hw,hu,hv⟩ := List.filter_eq_append_iff.mp hf
      obtain ⟨W,hW,hmap⟩ := ih v (by simp) hv
      exact ⟨u::W,by simp [hW,hw],by simp [hu,hmap]⟩

theorem lift_filter_blocks_length (p : V → Bool) (w : List V) (L : List (List V))
    (hne : L ≠ []) (hfilter : w.filter p = L.flatten) :
    ∃ W : List (List V), W.flatten = w ∧ W.map (List.filter p) = L ∧ W.length = L.length := by
  obtain ⟨W,hw,hm⟩ := lift_filter_blocks p w L hne hfilter
  exact ⟨W,hw,hm,by rw [← hm,List.length_map]⟩

#print axioms lift_filter_blocks

end Crown.CrownLower
