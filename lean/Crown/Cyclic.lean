import Crown.Words

/-! Cyclic rotation of positive uniform representations. The binary restriction
has equal letter counts; hence an alternating restriction also alternates at
its closing boundary. -/

namespace Crown

variable {V : Type*} [DecidableEq V]

theorem balanced_chain_endpoints (a b : V) (hab : a ≠ b) (w : List V)
    (hm : ∀ x ∈ w, x = a ∨ x = b) (he : w.count a = w.count b)
    (hc : w.IsChain (· ≠ ·)) :
    ∀ x ∈ w.head?, ∀ y ∈ w.getLast?, x ≠ y := by
  induction w using List.twoStepInduction with
  | nil => simp
  | singleton x =>
    rcases hm x (by simp) with rfl | rfl <;> simp [hab, Ne.symm hab] at he
  | cons_cons x y w ih _ =>
    have hx := hm x (by simp)
    have hy := hm y (by simp)
    have hxy : x ≠ y := (List.isChain_cons_cons.mp hc).1
    have hew : w.count a = w.count b := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp_all [List.count_cons, Ne.symm hab]
    have hmw : ∀ z ∈ w, z = a ∨ z = b := fun z hz => hm z (by simp [hz])
    have hcw : w.IsChain (· ≠ ·) := hc.tail.tail
    have hend := ih hmw hew hcw
    cases w with
    | nil => simpa using hxy
    | cons z zs =>
      have hz := hmw z (by simp)
      have hyz : y ≠ z := (List.isChain_cons_cons.mp hc.tail).1
      have hzx : z = x := by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          rcases hz with rfl | rfl <;>
          first | rfl | exact False.elim (hxy rfl) | exact False.elim (hyz rfl)
      subst z
      simpa using hend

theorem balanced_chain_swap (a b : V) (hab : a ≠ b) (u v : List V)
    (hm : ∀ x ∈ u ++ v, x = a ∨ x = b)
    (he : (u ++ v).count a = (u ++ v).count b)
    (hc : (u ++ v).IsChain (· ≠ ·)) : (v ++ u).IsChain (· ≠ ·) := by
  have hend := balanced_chain_endpoints a b hab (u ++ v) hm he hc
  apply hc.right_of_append.append hc.left_of_append
  intro x hx y hy
  have hu : u ≠ [] := by intro h; simp [h] at hy
  have hv : v ≠ [] := by intro h; simp [h] at hx
  apply Ne.symm
  apply hend y
  · simpa [List.head?_append, hu] using hy
  · simpa [List.getLast?_append, hv] using hx

theorem alternates_append_swap {u v : List V} {a b : V} (hab : a ≠ b)
    (he : (u ++ v).count a = (u ++ v).count b) :
    Alternates (u ++ v) a b ↔ Alternates (v ++ u) a b := by
  have step : ∀ u v : List V, (u ++ v).count a = (u ++ v).count b →
      Alternates (u ++ v) a b → Alternates (v ++ u) a b := by
    intro u v he hc
    rw [Alternates, restrictPair_append] at hc ⊢
    apply balanced_chain_swap a b hab _ _ ?_ ?_ hc
    · intro x hx
      have hx' : x ∈ restrictPair (u ++ v) a b := by
        simpa only [restrictPair_append] using hx
      simpa [restrictPair] using (List.mem_filter.mp hx').2
    · rw [← restrictPair_append]
      simpa [restrictPair, List.count_filter] using he
  exact ⟨step u v he, step v u (by simpa [List.count_append, Nat.add_comm] using he)⟩

theorem represents_append_swap {G : SimpleGraph V} {k : ℕ} {u v : List V}
    (h : Represents G k (u ++ v)) : Represents G k (v ++ u) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro a
    simpa [List.count_append, Nat.add_comm] using h.2.1 a
  · intro a b hab
    exact (h.2.2 a b hab).trans (alternates_append_swap hab ((h.2.1 a).trans (h.2.1 b).symm))

#print axioms represents_append_swap

end Crown
