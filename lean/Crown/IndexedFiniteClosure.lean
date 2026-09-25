import Crown.FiniteClosure
import Mathlib.Data.Fintype.Basic

namespace Crown.IndexedFiniteClosure
open Crown.Ranks

variable {V I J : Type*} [DecidableEq V] [Fintype J]

noncomputable def family (owner : J → V) (support : J → Finset V) (b : V) :
    List (Finset V) := ((Finset.univ.filter (fun j => owner j = b)).toList).map support

theorem family_mem (owner : J → V) (support : J → Finset V) (b : V) (w : Finset V) :
    w ∈ family owner support b ↔ ∃ j, owner j = b ∧ support j = w := by
  classical
  simp [family]

structure Certificate (rows : V → InitialRow I) (owner : J → V)
    (support : J → Finset V) (cores : List (Finset V)) (limit : ℕ) : Prop where
  seed : ∀ b u, OneStar (rows b) → Fixed (rows u) → PotentialBelow (rows b) (rows u) →
    ∃ j, owner j = b ∧ support j ⊆ {b, u}
  step : ∀ j c, Implies rows (owner j) c → (insert c (support j)).card ≤ limit →
    ∃ j', owner j' = c ∧ support j' ⊆ insert c (support j)
  terminal : ∀ j l, OneStar (rows (owner j)) → Fixed (rows l) →
    PotentialBelow (rows l) (rows (owner j)) → (insert l (support j)).card ≤ limit →
    ∃ core ∈ cores, core ⊆ insert l (support j)
  fixed : ∀ b c, Fixed (rows b) → Fixed (rows c) → PotentialBelow (rows b) (rows c) →
    ∃ core ∈ cores, core ⊆ {b, c}

theorem Certificate.toCertificate {rows : V → InitialRow I} {owner : J → V}
    {support : J → Finset V} {cores : List (Finset V)} {limit : ℕ}
    (cert : Certificate rows owner support cores limit) :
    Crown.FiniteClosure.Certificate rows (family owner support) cores limit := by
  classical
  constructor
  · intro b u hb hu hbu
    obtain ⟨j, hj, hsub⟩ := cert.seed b u hb hu hbu
    exact ⟨support j, (family_mem _ _ _ _).mpr ⟨j, hj, rfl⟩, hsub⟩
  · intro b c w hw hbc hcard
    obtain ⟨j, hj, rfl⟩ := (family_mem _ _ _ _).mp hw
    obtain ⟨j', hj', hsub⟩ := cert.step j c (by simpa [hj] using hbc) hcard
    exact ⟨support j', (family_mem _ _ _ _).mpr ⟨j', hj', rfl⟩, hsub⟩
  · intro b l w hw hb hl hlb hcard
    obtain ⟨j, hj, rfl⟩ := (family_mem _ _ _ _).mp hw
    exact cert.terminal j l (by simpa [hj] using hb) hl (by simpa [hj] using hlb) hcard
  · exact cert.fixed

theorem selected_core_of_infeasible {rows : V → InitialRow I} {owner : J → V}
    {support : J → Finset V} {cores : List (Finset V)} {limit : ℕ}
    (cert : Certificate rows owner support cores limit) (s : Finset V) (hs : s.card ≤ limit)
    (hbad : ¬ Feasible (fun v : {v // v ∈ s} => rows v.val)) :
    ∃ core ∈ cores, core ⊆ s :=
  Crown.FiniteClosure.selected_core_of_infeasible rows (family owner support) cores limit
    cert.toCertificate s hs hbad

#print axioms Certificate.toCertificate
#print axioms selected_core_of_infeasible

end Crown.IndexedFiniteClosure
