import Crown.CertificateData
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

noncomputable def coverageCheck (rows : Fin 256 → InitialRow (Fin 4))
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935) (q : Pattern) : Bool :=
  decide (witness q ∈ template) &&
    (cores (witness q)).all (fun m => decide (rows m ∈ patternRows q))

theorem coverage_of_check (rows : Fin 256 → InitialRow (Fin 4))
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935)
    (h : ∀ q, coverageCheck rows cores template witness q = true) :
    Coverage rows cores template witness := by
  intro q
  simpa only [coverageCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    using h q

def sameRow (r s : InitialRow (Fin 4)) : Bool :=
  (r 0 == s 0) && (r 1 == s 1) && (r 2 == s 2) && (r 3 == s 3)

theorem sameRow_iff (r s : InitialRow (Fin 4)) : sameRow r s = true ↔ r = s := by
  simp only [sameRow, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    funext i
    fin_cases i <;> assumption
  · rintro rfl
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩

def patterns : List Pattern :=
  ((List.finRange 3).flatMap fun a => (List.finRange 3).flatMap fun b =>
    (List.finRange 3).flatMap fun c => (List.finRange 3).map fun d =>
      Sum.inl ![a, b, c, d]) ++
  ((List.finRange 4).flatMap fun j => (List.finRange 6).map fun t => Sum.inr (j,t))

theorem patterns_complete (q : Pattern) : q ∈ patterns := by
  cases q with
  | inl t =>
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨t 0, List.mem_finRange _, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨t 1, List.mem_finRange _, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨t 2, List.mem_finRange _, ?_⟩
    apply List.mem_map.mpr
    refine ⟨t 3, List.mem_finRange _, ?_⟩
    congr 1
    funext i
    fin_cases i <;> rfl
  | inr jt =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨jt.1, List.mem_finRange _, ?_⟩
    apply List.mem_map.mpr
    exact ⟨jt.2, List.mem_finRange _, rfl⟩

noncomputable def fastCoverageCheck (rows : Fin 256 → InitialRow (Fin 4))
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935) (q : Pattern) : Bool :=
  template.contains (witness q) &&
    (cores (witness q)).all (fun m => (patternRows q).any (sameRow (rows m)))

theorem coverage_of_fast_check (rows : Fin 256 → InitialRow (Fin 4))
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935)
    (h : patterns.all (fastCoverageCheck rows cores template witness) = true) :
    Coverage rows cores template witness := by
  intro q
  have hq := List.all_eq_true.mp h q (patterns_complete q)
  simpa [fastCoverageCheck, List.all_eq_true, List.any_eq_true, sameRow_iff] using hq

theorem pairsOfEquiv_covers (p : Pairing8) : Covers (pairsOfEquiv p) := by
  intro a
  obtain ⟨⟨i, b⟩, rfl⟩ := p.surjective a
  refine ⟨i, ?_⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem selected_template (p : Pairing8) (s : Fin 256 → Bool)
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935)
    (hcov : Coverage (fun m => rowOfMask (pairsOfEquiv p) (maskBits m))
      cores template witness)
    (hbad : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template, ∀ m ∈ cores c, s m = true :=
  selected_core_of_coverage _ (mask_rank_injective _ (pairsOfEquiv_covers p))
    s cores template witness hcov (hbad p)

end Crown.CertificateData
