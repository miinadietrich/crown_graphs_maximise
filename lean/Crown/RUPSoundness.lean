import Mathlib.Tactic.Sat.FromLRAT

namespace Crown.RUPSoundness

open Sat

abbrev Literals := List Literal
abbrev Formula := List Literals

/-- Every literal in the list is false under the valuation. -/
def FalseLiterals (v : Valuation) (a : Literals) : Prop :=
  ∀ l ∈ a, v.neg l

theorem false_of_all_neg (v : Valuation) (c : Literals) :
    v.satisfies c → FalseLiterals v c → False := by
  induction c with
  | nil => intro h _; exact h
  | cons l c ih =>
    intro h ha
    exact ih (h (ha l (by simp))) (fun m hm => ha m (by simp [hm]))

theorem clause_of_refutation (v : Valuation) (c : Literals) :
    (FalseLiterals v c → False) → v.satisfies c := by
  induction c with
  | nil => intro h; exact h (by intro l hl; cases hl)
  | cons l c ih =>
    intro h hl
    apply ih
    intro hc
    apply h
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hl
    · exact hc m hm

/-- Unit propagation reaches a falsified clause. In a unit step all literals
other than the designated literal are already false; its negation is then
false and is available in the rest of the derivation. -/
inductive Conflict (F : Formula) : Literals → Prop
  | conflict {a c : Literals} (hc : c ∈ F) (hsub : c ⊆ a) : Conflict F a
  | unit {a c : Literals} {l : Literal} (hc : c ∈ F) (hl : l ∈ c)
      (hother : ∀ m ∈ c, m = l ∨ m ∈ a)
      (next : Conflict F (l.negate :: a)) : Conflict F a

theorem conflict_sound {F : Formula} {a : Literals} (h : Conflict F a) (v : Valuation) :
    v.satisfies_fmla F → FalseLiterals v a → False := by
  induction h with
  | @conflict a c hc hsub =>
    intro hF ha
    exact false_of_all_neg v c (hF.prop c hc) (fun l hl => ha l (hsub hl))
  | @unit a c l hc hl hother next ih =>
    intro hF ha
    apply Valuation.by_cases (v := v) (l := l)
    · intro hneg
      apply ih hF
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hneg
      · exact ha m hm
    · intro hlfalse
      apply false_of_all_neg v c (hF.prop c hc)
      intro m hm
      rcases hother m hm with rfl | hm
      · exact hlfalse
      · exact ha m hm

/-- Falsifying the proposed clause and propagating to contradiction proves
that the original formula entails that clause. -/
theorem rup_sound {F : Formula} {c : Literals} (h : Conflict F c) : Sat.Fmla.proof F c := by
  intro v hF
  exact clause_of_refutation v c (conflict_sound h v hF)

/-- A finite sequence of accepted RUP additions. -/
inductive AdditionChain (F : Formula) : Formula → Prop
  | refl : AdditionChain F F
  | add {G : Formula} (previous : AdditionChain F G) (c : Literals)
      (proof : Conflict G c) : AdditionChain F (G ++ [c])

theorem chain_preserves {F G : Formula} (h : AdditionChain F G) (v : Valuation)
    (hF : v.satisfies_fmla F) : v.satisfies_fmla G := by
  induction h with
  | refl => exact hF
  | @add G previous c proof ih =>
    constructor
    change ∀ d : Literals, d ∈ G ++ [c] → v.satisfies d
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih.prop d hd
    · have he : d = c := by simpa using hd
      subst d
      exact rup_sound proof v ih

theorem chain_empty_unsatisfiable {F G : Formula} (h : AdditionChain F G)
    (hempty : ([] : Literals) ∈ G) (v : Valuation) : ¬ v.satisfies_fmla F := by
  intro hF
  exact (chain_preserves h v hF).prop ([] : Literals) hempty

theorem root_conflict_unsatisfiable {F G : Formula} (h : AdditionChain F G)
    (hroot : Conflict G []) (v : Valuation) : ¬ v.satisfies_fmla F := by
  intro hF
  exact conflict_sound hroot v (chain_preserves h v hF) (by intro l hl; cases hl)

/-- The four clauses from Appendix B.2, with atoms numbered zero and one. -/
def exampleFormula : Formula :=
  [[.pos 0, .pos 1], [.pos 0, .neg 1], [.neg 0, .pos 1], [.neg 0, .neg 1]]

theorem example_p_rup : Conflict exampleFormula [.pos 0] := by
  apply Conflict.unit (c := [.pos 0, .pos 1]) (l := .pos 1)
  · simp [exampleFormula, Literals]
  · simp
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inl rfl
  · apply Conflict.conflict (c := [.pos 0, .neg 1])
    · simp [exampleFormula, Literals]
    · intro m hm
      simpa only [Literal.negate, List.mem_cons, List.not_mem_nil, or_false, false_or, or_comm, or_assoc] using hm

theorem example_after_p_root : Conflict (exampleFormula ++ ([[.pos 0]] : Formula)) [] := by
  apply Conflict.unit (c := [.pos 0]) (l := .pos 0)
  · simp
  · simp
  · intro m hm
    exact Or.inl (by simpa using hm)
  · apply Conflict.unit (c := [.neg 0, .pos 1]) (l := .pos 1)
    · simp [exampleFormula, Literals]
    · simp
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact Or.inr (by simp [Literal.negate])
      · exact Or.inl rfl
    · apply Conflict.conflict (c := [.neg 0, .neg 1])
      · simp [exampleFormula, Literals]
      · intro m hm
        simpa only [Literal.negate, List.mem_cons, List.not_mem_nil, or_false, false_or, or_comm, or_assoc] using hm

theorem example_unsatisfiable (v : Valuation) : ¬ v.satisfies_fmla exampleFormula :=
  root_conflict_unsatisfiable (.add .refl [.pos 0] example_p_rup) example_after_p_root v

#print axioms rup_sound
#print axioms chain_preserves
#print axioms chain_empty_unsatisfiable
#print axioms root_conflict_unsatisfiable
#print axioms example_p_rup
#print axioms example_after_p_root
#print axioms example_unsatisfiable
end Crown.RUPSoundness
