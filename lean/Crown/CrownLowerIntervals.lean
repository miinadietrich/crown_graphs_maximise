import Crown.CrownLowerBlocks

/-! Exact occurrence counts in alternating factors. These bounds are the
numerical part of the interval argument in Glen--Kitaev--Pyatkin, Lemma 3. -/

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem binary_chain_count_le (a b : V) (hab : a ≠ b) (w : List V)
    (hm : ∀ x ∈ w, x = a ∨ x = b) (hc : w.IsChain (· ≠ ·)) :
    w.count a ≤ w.count b + 1 := by
  induction w using List.twoStepInduction with
  | nil => simp
  | singleton x =>
    rcases hm x (by simp) with rfl | rfl <;> simp [hab,Ne.symm hab]
  | cons_cons x y w ih _ =>
    have hx := hm x (by simp)
    have hy := hm y (by simp)
    have hxy : x ≠ y := (List.isChain_cons_cons.mp hc).1
    have hmw : ∀ z ∈ w, z = a ∨ z = b := fun z hz => hm z (by simp [hz])
    have hcw : w.IsChain (· ≠ ·) := hc.tail.tail
    have hi := ih hmw hcw
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · simpa [List.count_cons,hab,Ne.symm hab,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Nat.add_le_add_right hi 1
    · simpa [List.count_cons,hab,Ne.symm hab,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Nat.add_le_add_right hi 1
    · exact False.elim (hxy rfl)

theorem alternating_count_le (a b : V) (hab : a ≠ b) (w : List V)
    (hc : Crown.Alternates w a b) : w.count a ≤ w.count b + 1 := by
  have h := binary_chain_count_le a b hab (Crown.restrictPair w a b) ?_ hc
  · simpa [Crown.restrictPair,List.count_filter] using h
  · intro x hx
    simpa [Crown.restrictPair] using (List.mem_filter.mp hx).2

theorem alternating_factor_count_le (a b : V) (hab : a ≠ b) (w u : List V)
    (hc : Crown.Alternates w a b) (hu : u <:+: w) : u.count a ≤ u.count b + 1 := by
  apply alternating_count_le a b hab u
  exact List.IsChain.infix hc (List.IsInfix.filter _ hu)

theorem alternating_same_ends_count (a b : V) (hab : a ≠ b) (w : List V)
    (hc : Crown.Alternates w a b)
    (hh : a ∈ (Crown.restrictPair w a b).head?)
    (ht : a ∈ (Crown.restrictPair w a b).getLast?) :
    w.count a = w.count b + 1 := by
  have hp := (prefixOrder_iff_directedChain w a b hab).mpr
    ⟨hc,fun x hx => Option.mem_unique hx hh⟩
  have hcounts := hp w (List.prefix_refl w)
  have hne : w.count a ≠ w.count b := by
    intro he
    have hb := Crown.balanced_chain_endpoints a b hab (Crown.restrictPair w a b) ?_ ?_ hc
    · exact hb a hh a ht rfl
    · intro x hx
      simpa [Crown.restrictPair] using (List.mem_filter.mp hx).2
    · simpa [Crown.restrictPair,List.count_filter] using he
  omega

#print axioms alternating_factor_count_le
#print axioms alternating_same_ends_count

end Crown.CrownLower
