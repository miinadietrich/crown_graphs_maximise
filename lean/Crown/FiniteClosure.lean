import Crown.Ranks
import Mathlib.Data.Finset.Card

/-! Finite witnesses for implication closure. The certificate conditions
are mathematical propositions. Later finite data must prove each condition;
the witness-generating program is not part of the trusted proof. -/

namespace Crown.FiniteClosure
open Crown.Ranks

variable {V I : Type*} [DecidableEq V]

structure Certificate (rows : V → InitialRow I)
    (witnesses : V → List (Finset V)) (cores : List (Finset V)) (limit : ℕ) : Prop where
  seed : ∀ b u, OneStar (rows b) → Fixed (rows u) → PotentialBelow (rows b) (rows u) →
    ∃ w ∈ witnesses b, w ⊆ {b, u}
  step : ∀ b c w, w ∈ witnesses b → Implies rows b c → (insert c w).card ≤ limit →
    ∃ w' ∈ witnesses c, w' ⊆ insert c w
  terminal : ∀ b l w, w ∈ witnesses b → OneStar (rows b) →
    Fixed (rows l) → PotentialBelow (rows l) (rows b) → (insert l w).card ≤ limit →
    ∃ core ∈ cores, core ⊆ insert l w
  fixed : ∀ b c, Fixed (rows b) → Fixed (rows c) → PotentialBelow (rows b) (rows c) →
    ∃ core ∈ cores, core ⊆ {b, c}

theorem forced_witness (rows : V → InitialRow I)
    (witnesses : V → List (Finset V)) (cores : List (Finset V)) (limit : ℕ)
    (cert : Certificate rows witnesses cores limit) (s : Finset V) (hs : s.card ≤ limit)
    {b : {v // v ∈ s}}
    (hf : Forced (DirectOne (fun v : {v // v ∈ s} => rows v.val))
      (Implies (fun v : {v // v ∈ s} => rows v.val)) b) :
    ∃ w ∈ witnesses b.val, w ⊆ s := by
  induction hf with
  | @seed b hb =>
    obtain ⟨hb, u, hu, hbu⟩ := hb
    obtain ⟨w, hw, hsub⟩ := cert.seed b.val u.val hb hu hbu
    refine ⟨w, hw, hsub.trans ?_⟩
    exact Finset.insert_subset_iff.mpr ⟨b.property, Finset.singleton_subset_iff.mpr u.property⟩
  | @step b c _ hbc ih =>
    obtain ⟨w, hw, hsub⟩ := ih
    have hnew : insert c.val w ⊆ s := Finset.insert_subset_iff.mpr ⟨c.property, hsub⟩
    obtain ⟨w', hw', hsub'⟩ := cert.step b.val c.val w hw hbc
      ((Finset.card_le_card hnew).trans hs)
    exact ⟨w', hw', hsub'.trans hnew⟩

theorem feasible_of_no_core (rows : V → InitialRow I)
    (witnesses : V → List (Finset V)) (cores : List (Finset V)) (limit : ℕ)
    (cert : Certificate rows witnesses cores limit) (s : Finset V) (hs : s.card ≤ limit)
    (hcores : ∀ core ∈ cores, ¬ core ⊆ s) :
    Feasible (fun v : {v // v ∈ s} => rows v.val) := by
  classical
  apply (feasible_iff_constraints _).mpr
  constructor
  · intro b c hb hc hbc
    obtain ⟨core, hcore, hsub⟩ := cert.fixed b.val c.val hb hc hbc
    exact hcores core hcore (hsub.trans (Finset.insert_subset_iff.mpr
      ⟨b.property, Finset.singleton_subset_iff.mpr c.property⟩))
  · apply (choice_exists_iff _ _ _).mpr
    rintro ⟨b, hf, hb, l, hl, hlb⟩
    obtain ⟨w, hw, hsub⟩ := forced_witness rows witnesses cores limit cert s hs hf
    have hnew : insert l.val w ⊆ s := Finset.insert_subset_iff.mpr ⟨l.property, hsub⟩
    obtain ⟨core, hcore, hsub'⟩ := cert.terminal b.val l.val w hw hb hl hlb
      ((Finset.card_le_card hnew).trans hs)
    exact hcores core hcore (hsub'.trans hnew)

theorem selected_core_of_infeasible (rows : V → InitialRow I)
    (witnesses : V → List (Finset V)) (cores : List (Finset V)) (limit : ℕ)
    (cert : Certificate rows witnesses cores limit) (s : Finset V) (hs : s.card ≤ limit)
    (hbad : ¬ Feasible (fun v : {v // v ∈ s} => rows v.val)) :
    ∃ core ∈ cores, core ⊆ s := by
  classical
  by_contra h
  apply hbad
  exact feasible_of_no_core rows witnesses cores limit cert s hs
    (by simpa only [not_exists, not_and] using h)

#print axioms forced_witness
#print axioms feasible_of_no_core
#print axioms selected_core_of_infeasible

end Crown.FiniteClosure
