import Crown.CrownLowerSplitting

/-! Alternation expressed by counts in every prefix. This supplies a precise
occurrence-order language for the lower-bound argument without identifying
different occurrences of the same letter. -/

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def PrefixOrder (w : List V) (a b : V) : Prop :=
  ∀ p, p <+: w → p.count b ≤ p.count a ∧ p.count a ≤ p.count b + 1

def DirectedChain (w : List V) (a b : V) : Prop :=
  Crown.Alternates w a b ∧ ∀ x ∈ (Crown.restrictPair w a b).head?, x = a

theorem prefixOrder_cons_first (w : List V) (a b : V) (hab : a ≠ b) :
    PrefixOrder (a::w) a b ↔ PrefixOrder w b a := by
  constructor
  · intro h p hp
    have hh := h (a::p) (List.cons_prefix_cons.mpr ⟨rfl,hp⟩)
    simp only [List.count_cons, beq_iff_eq, hab, if_false, if_true,
      Nat.zero_add, Nat.add_zero] at hh
    omega
  · intro h p hp
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
    · simp
    · have hh := h t ht
      simp only [List.count_cons, beq_iff_eq, hab, if_false, if_true,
        Nat.zero_add, Nat.add_zero]
      omega

theorem prefixOrder_cons_second (w : List V) (a b : V) (hab : a ≠ b) :
    ¬ PrefixOrder (b::w) a b := by
  intro h
  have hh := h [b] (by simp)
  simpa [hab,Ne.symm hab] using hh.1

theorem prefixOrder_cons_other (w : List V) (a b x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
    PrefixOrder (x::w) a b ↔ PrefixOrder w a b := by
  constructor
  · intro h p hp
    simpa [List.count_cons,hxa,hxb] using h (x::p) (List.cons_prefix_cons.mpr ⟨rfl,hp⟩)
  · intro h p hp
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
    · simp
    · simpa [List.count_cons,hxa,hxb] using h t ht

theorem directedChain_cons_first (w : List V) (a b : V) (hab : a ≠ b) :
    DirectedChain (a::w) a b ↔ DirectedChain w b a := by
  have he : Crown.restrictPair (a::w) a b = a :: Crown.restrictPair w a b := by
    simp [Crown.restrictPair]
  have hr := Crown.restrictPair_comm w b a
  simp only [DirectedChain,Crown.Alternates,he,hr,List.isChain_cons,List.head?_cons,
    Option.mem_some_iff,forall_eq,and_true]
  constructor
  · rintro ⟨⟨hh,hc⟩,_⟩
    refine ⟨hc,?_⟩
    intro x hx
    have hm := List.mem_of_mem_head? hx
    have hm' : x = a ∨ x = b := by simpa [Crown.restrictPair] using (List.mem_filter.mp hm).2
    exact hm'.resolve_left (fun hxa => hh x hx hxa.symm)
  · rintro ⟨hc,hh⟩
    refine ⟨⟨?_,hc⟩,?_⟩
    · intro x hx
      simpa [hh x hx] using hab
    · intro x hx; exact hx.symm

theorem directedChain_cons_second (w : List V) (a b : V) (hab : a ≠ b) :
    ¬ DirectedChain (b::w) a b := by
  intro h
  have he : Crown.restrictPair (b::w) a b = b :: Crown.restrictPair w a b := by
    simp [Crown.restrictPair]
  have hh := h.2 b (by rw [he]; simp)
  exact hab hh.symm

theorem directedChain_cons_other (w : List V) (a b x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
    DirectedChain (x::w) a b ↔ DirectedChain w a b := by
  simp [DirectedChain,Crown.Alternates,Crown.restrictPair,hxa,hxb]

theorem prefixOrder_iff_directedChain (w : List V) (a b : V) (hab : a ≠ b) :
    PrefixOrder w a b ↔ DirectedChain w a b := by
  induction w generalizing a b with
  | nil => simp [PrefixOrder,DirectedChain,Crown.Alternates,Crown.restrictPair]
  | cons x w ih =>
    by_cases hxa : x = a
    · subst x
      rw [prefixOrder_cons_first w a b hab,directedChain_cons_first w a b hab]
      exact ih b a (Ne.symm hab)
    · by_cases hxb : x = b
      · subst x
        exact iff_of_false (prefixOrder_cons_second w a b hab) (directedChain_cons_second w a b hab)
      · rw [prefixOrder_cons_other w a b x hxa hxb,directedChain_cons_other w a b x hxa hxb]
        exact ih a b hab

/-- The occurrence-order implication in the source's Lemma 2. A splittable
set supplies the final prefix bound, since its letters occur once per block. -/
theorem alternates_of_between (w : List V) (a b x : V) (hab : a ≠ b)
    (hax : PrefixOrder w a x) (hxb : PrefixOrder w x b)
    (hbound : ∀ p, p <+: w → p.count a ≤ p.count b + 1) : Crown.Alternates w a b := by
  apply ((prefixOrder_iff_directedChain w a b hab).mp ?_).1
  intro p hp
  exact ⟨Nat.le_trans (hxb p hp).1 (hax p hp).1,hbound p hp⟩

#print axioms prefixOrder_iff_directedChain
#print axioms alternates_of_between

end Crown.CrownLower
