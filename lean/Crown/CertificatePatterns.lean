import Crown.CertificateCatalogue
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! The symbolic obstruction catalogue: minimality and exact cardinalities.
The finite reductions below concern 105 patterns of two or three four-entry
rows. They do not enumerate any graph or SAT assignment. -/

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

abbrev RankRow := InitialRow (Fin 4)

def patternSet (q : Pattern) : Set RankRow := {r | r ∈ patternRows q}

def rowSetFeasible (S : Set RankRow) : Prop := Feasible (fun r : S => r.val)

def MinimalInfeasible (S : Set RankRow) : Prop :=
  ¬ rowSetFeasible S ∧ ∀ T, T ⊂ S → rowSetFeasible T

theorem rowSet_infeasible_iff (S : Set RankRow) :
    ¬ rowSetFeasible S ↔ ∃ q, patternSet q ⊆ S := by
  rw [rowSetFeasible, infeasible_iff_patterns]
  constructor
  · rintro (⟨l, u, t, hl, hu⟩ | ⟨l, c, u, j, t, hl, hc, hu⟩)
    · refine ⟨.inl t, ?_⟩
      intro r hr
      simp only [patternSet, Set.mem_setOf_eq, patternRows, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hl ▸ l.property
      · exact hu ▸ u.property
    · refine ⟨.inr (j,t), ?_⟩
      intro r hr
      simp only [patternSet, Set.mem_setOf_eq, patternRows, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hl ▸ l.property
      · exact hc ▸ c.property
      · exact hu ▸ u.property
  · rintro ⟨q, hq⟩
    cases q with
    | inl t =>
      exact Or.inl ⟨⟨pairLower t, hq (by simp [patternSet, patternRows])⟩,
        ⟨pairUpper t, hq (by simp [patternSet, patternRows])⟩, t, rfl, rfl⟩
    | inr jt =>
      exact Or.inr ⟨⟨tripleLower jt.1 (decreasingRanks jt.2).1,
        hq (by simp [patternSet, patternRows])⟩,
        ⟨tripleCenter jt.1, hq (by simp [patternSet, patternRows])⟩,
        ⟨tripleUpper jt.1 (decreasingRanks jt.2).2,
        hq (by simp [patternSet, patternRows])⟩, jt.1, jt.2, rfl, rfl, rfl⟩

def rowMember (r : RankRow) (rs : List RankRow) : Bool := rs.any (sameRow r)

theorem rowMember_iff (r : RankRow) (rs : List RankRow) :
    rowMember r rs = true ↔ r ∈ rs := by
  simp [rowMember, List.any_eq_true, sameRow_iff]

def irredundancyCheck (q : Pattern) : Bool :=
  (patternRows q).all fun removed => patterns.all fun p =>
    ! (patternRows p).all (fun r => rowMember r (patternRows q) && !(sameRow r removed))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem patterns_irredundancy_checked : patterns.all irredundancyCheck = true := by
  rfl

theorem patterns_irredundant (q : Pattern) (removed : RankRow)
    (hr : removed ∈ patternRows q) :
    ¬ ∃ p, ∀ r ∈ patternRows p, r ∈ patternRows q ∧ r ≠ removed := by
  have hq := List.all_eq_true.mp patterns_irredundancy_checked q (patterns_complete q)
  have hr' := List.all_eq_true.mp hq removed hr
  rintro ⟨p, hp⟩
  have hbad := List.all_eq_true.mp hr' p (patterns_complete p)
  have htrue : (patternRows p).all
      (fun r => rowMember r (patternRows q) && !(sameRow r removed)) = true := by
    apply List.all_eq_true.mpr
    intro r hrp
    rcases hp r hrp with ⟨hm, hn⟩
    simp only [Bool.and_eq_true, rowMember_iff]
    refine ⟨hm, ?_⟩
    have he : sameRow r removed = false :=
      Bool.eq_false_iff.mpr (fun he => hn ((sameRow_iff r removed).mp he))
    simp [he]
  rw [htrue] at hbad
  cases hbad

theorem pattern_minimal (q : Pattern) : MinimalInfeasible (patternSet q) := by
  classical
  refine ⟨(rowSet_infeasible_iff _).mpr ⟨q, Set.Subset.refl _⟩, ?_⟩
  intro T hT
  by_contra hn
  obtain ⟨p, hp⟩ := (rowSet_infeasible_iff T).mp hn
  obtain ⟨r, hr, hrT⟩ := Set.exists_of_ssubset hT
  apply patterns_irredundant q r hr
  refine ⟨p, fun x hx => ⟨hT.subset (hp hx), ?_⟩⟩
  intro hxr
  exact hrT (hxr ▸ hp hx)

theorem minimal_infeasible_iff (S : Set RankRow) :
    MinimalInfeasible S ↔ ∃ q, S = patternSet q := by
  classical
  constructor
  · rintro ⟨hn, hmin⟩
    obtain ⟨q, hq⟩ := (rowSet_infeasible_iff S).mp hn
    refine ⟨q, ?_⟩
    by_contra hne
    have hs : patternSet q ⊂ S := Set.ssubset_iff_subset_ne.mpr ⟨hq, Ne.symm hne⟩
    exact (pattern_minimal q).1 (hmin _ hs)
  · rintro ⟨q, rfl⟩
    exact pattern_minimal q

def patternsSameSetCheck (q : Pattern) : Bool := patterns.all fun p =>
  if (patternRows p).all (fun r => rowMember r (patternRows q)) &&
      (patternRows q).all (fun r => rowMember r (patternRows p))
  then decide (p = q) else true

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem patterns_same_set_checked : patterns.all patternsSameSetCheck = true := by
  rfl

theorem patternSet_injective : Function.Injective patternSet := by
  intro p q hpq
  have hq := List.all_eq_true.mp patterns_same_set_checked q (patterns_complete q)
  have hp := List.all_eq_true.mp hq p (patterns_complete p)
  have h1 : (patternRows p).all (fun r => rowMember r (patternRows q)) = true := by
    apply List.all_eq_true.mpr
    intro r hr
    change r ∈ patternSet p at hr
    apply (rowMember_iff _ _).mpr
    change r ∈ patternSet q
    rw [← hpq]
    exact hr
  have h2 : (patternRows q).all (fun r => rowMember r (patternRows p)) = true := by
    apply List.all_eq_true.mpr
    intro r hr
    change r ∈ patternSet q at hr
    apply (rowMember_iff _ _).mpr
    change r ∈ patternSet p
    rw [hpq]
    exact hr
  simpa only [patternsSameSetCheck, h1, h2, Bool.true_and, ite_true,
    decide_eq_true_eq] using hp

theorem pair_pattern_count : Fintype.card (Fin 4 → Fin 3) = 81 := by decide
theorem triple_pattern_count : Fintype.card (Fin 4 × Fin 6) = 24 := by decide
theorem pattern_count : Fintype.card Pattern = 105 := by decide

noncomputable def minimalPatternEquiv :
    Pattern ≃ {S : Set RankRow // MinimalInfeasible S} :=
  Equiv.ofBijective (fun q => ⟨patternSet q, pattern_minimal q⟩) ⟨
    fun a b h => patternSet_injective (congrArg Subtype.val h), by
      intro S
      obtain ⟨q, hq⟩ := (minimal_infeasible_iff S.val).mp S.property
      exact ⟨q, Subtype.ext hq.symm⟩⟩

theorem minimal_obstruction_count :
    Nat.card {S : Set RankRow // MinimalInfeasible S} = 105 := by
  rw [← Nat.card_congr minimalPatternEquiv, Nat.card_eq_fintype_card]
  exact pattern_count

theorem distinct_pair_obstruction_count :
    Nat.card (Set.range (fun t : Fin 4 → Fin 3 => patternSet (.inl t))) = 81 := by
  have h : Function.Injective (fun t : Fin 4 → Fin 3 => patternSet (.inl t)) := by
    intro a b he
    exact Sum.inl.inj (patternSet_injective he)
  rw [← Nat.card_congr (Equiv.ofInjective _ h), Nat.card_eq_fintype_card]
  exact pair_pattern_count

theorem distinct_triple_obstruction_count :
    Nat.card (Set.range (fun jt : Fin 4 × Fin 6 => patternSet (.inr jt))) = 24 := by
  have h : Function.Injective (fun jt : Fin 4 × Fin 6 => patternSet (.inr jt)) := by
    intro a b he
    exact Sum.inr.inj (patternSet_injective he)
  rw [← Nat.card_congr (Equiv.ofInjective _ h), Nat.card_eq_fintype_card]
  exact triple_pattern_count

#print axioms pattern_minimal
#print axioms minimal_infeasible_iff
#print axioms patternSet_injective
#print axioms pattern_count
#print axioms minimal_obstruction_count
#print axioms distinct_pair_obstruction_count
#print axioms distinct_triple_obstruction_count
end Crown.CertificateData
