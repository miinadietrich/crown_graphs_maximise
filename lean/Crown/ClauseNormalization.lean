import Crown.CertificateAssembly
import Mathlib.Data.List.Dedup

namespace Crown.ClauseNormalization
open Crown.CertificateSemantics Crown.CertificateAssembly
open scoped Classical

theorem same_literals (a : Nat → Bool) (c d : List Sat.Literal)
    (h : ∀ l, l ∈ c ↔ l ∈ d) :
    (valuation a).satisfies c ↔ (valuation a).satisfies d := by
  simp only [clause_iff_exists,h]

theorem deduplicate_literals (a : Nat → Bool) (c : List Sat.Literal) :
    (valuation a).satisfies c.dedup ↔ (valuation a).satisfies c := by
  classical
  exact same_literals a c.dedup c (fun _ => List.mem_dedup)

def Tautological (c : List Sat.Literal) : Prop :=
  ∃ l ∈ c, l.negate ∈ c

theorem tautology_satisfied (a : Nat → Bool) (c : List Sat.Literal)
    (h : Tautological c) : (valuation a).satisfies c := by
  obtain ⟨l,hl,hn⟩ := h
  apply (clause_iff_exists a c).mpr
  cases l with
  | pos n =>
    cases ha : a n with
    | false => exact ⟨.neg n,hn,by simp [literalValue,ha]⟩
    | true => exact ⟨.pos n,hl,ha⟩
  | neg n =>
    cases ha : a n with
    | false => exact ⟨.neg n,hl,by simp [literalValue,ha]⟩
    | true => exact ⟨.pos n,hn,ha⟩

theorem omit_tautology (a : Nat → Bool) (F : Sat.Fmla) (c : List Sat.Literal)
    (h : Tautological c) :
    (valuation a).satisfies_fmla (c :: F) ↔ (valuation a).satisfies_fmla F := by
  constructor
  · intro hf
    exact ⟨fun d hd => hf.prop d (List.mem_cons_of_mem _ hd)⟩
  · intro hf
    refine ⟨fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact tautology_satisfied a d h
    · exact hf.prop d hd

#print axioms same_literals
#print axioms deduplicate_literals
#print axioms tautology_satisfied
#print axioms omit_tautology
end Crown.ClauseNormalization
