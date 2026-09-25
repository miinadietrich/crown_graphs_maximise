import Crown.Ranks
import Mathlib.Data.Fin.Basic

namespace Crown.DirectStarCheck
open Crown.Ranks

def Accepts {I V : Type*} (rows : V → InitialRow I) : Prop :=
  ∃ t : V → Bool, ∀ b c, ¬MultiStar (rows b) → ¬MultiStar (rows c) →
    ¬StrictBelow (complete (rows b) (t b)) (complete (rows c) (t c))

/-- For a nonempty coordinate type, comparing distinct rows suffices. -/
theorem accepts_iff_distinct {I V : Type*} [Nonempty I]
    (rows : V → InitialRow I) :
    Accepts rows ↔ ∃ t : V → Bool, ∀ b c, b ≠ c →
      ¬MultiStar (rows b) → ¬MultiStar (rows c) →
      ¬StrictBelow (complete (rows b) (t b)) (complete (rows c) (t c)) := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,fun b c _ => ht b c⟩
  · rintro ⟨t,ht⟩
    refine ⟨t,fun b c hb hc => ?_⟩
    by_cases hbc : b = c
    · subst c
      intro h
      obtain ⟨i⟩ := ‹Nonempty I›
      exact (Nat.lt_irrefl _) (h i)
    · exact ht b c hbc hb hc

theorem accepts_iff_feasible {I V : Type*} (rows : V → InitialRow I) :
    Accepts rows ↔ Feasible rows := by
  classical
  constructor
  · rintro ⟨t,ht⟩
    let r : V → CompletedRow I := fun b =>
      if h : MultiStar (rows b) then Classical.choose (multiStar_completion (rows b) h)
      else complete (rows b) (t b)
    refine ⟨r,?_,?_⟩
    · intro b
      by_cases hb : MultiStar (rows b)
      · exact by simpa only [r,dif_pos hb] using
          (Classical.choose_spec (multiStar_completion (rows b) hb)).1
      · exact by simpa only [r,dif_neg hb] using complete_completes (rows b) (t b)
    · intro b c hlt
      by_cases hb : MultiStar (rows b)
      · exact (Classical.choose_spec (multiStar_completion (rows b) hb)).2 (r c) |>.1
          (by simpa only [r,dif_pos hb] using hlt)
      by_cases hc : MultiStar (rows c)
      · exact (Classical.choose_spec (multiStar_completion (rows c) hc)).2 (r b) |>.2
          (by simpa only [r,dif_pos hc] using hlt)
      exact ht b c hb hc (by simpa only [r,dif_neg hb,dif_neg hc] using hlt)
  · rintro ⟨r,hr,hn⟩
    let t : V → Bool := fun b =>
      if h : OneStar (rows b) then
        Classical.choose (oneStar_completion_coverage h (hr b)) else false
    have he : ∀ b, ¬MultiStar (rows b) → r b = complete (rows b) (t b) := by
      intro b hb
      rcases fixed_or_oneStar_of_not_multiStar (rows b) hb with hf | hs
      · exact fixed_completion_unique hf (hr b) (t b)
      · simpa only [t,dif_pos hs] using
          Classical.choose_spec (oneStar_completion_coverage hs (hr b))
    refine ⟨t,fun b c hb hc => ?_⟩
    rw [←he b hb,←he c hc]
    exact hn b c

/-- The direct extreme-choice test and the implication test have exactly
the same acceptance condition, including fixed-pair obstructions. -/
theorem direct_iff_implications {I V : Type*} (rows : V → InitialRow I) :
    Accepts rows ↔ NoFixedPair rows ∧
      ∃ t, ValidChoice (DirectOne rows) (DirectZero rows) (Implies rows) t := by
  rw [accepts_iff_feasible,feasible_iff_constraints]

#print axioms accepts_iff_feasible
#print axioms accepts_iff_distinct
#print axioms direct_iff_implications
end Crown.DirectStarCheck
