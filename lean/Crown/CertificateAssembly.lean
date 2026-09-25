import Crown.CertificateValuation

namespace Crown.CertificateAssembly
open Crown.CertificateSemantics

theorem clause_iff_exists (a : Nat → Bool) (c : List Sat.Literal) :
    (valuation a).satisfies c ↔ ∃ l ∈ c, literalValue a l = true := by
  erw [clause_satisfied_iff]
  simp

theorem clause_mono (a : Nat → Bool) (c d : List Sat.Literal) (hsub : c ⊆ d)
    (h : (valuation a).satisfies c) : (valuation a).satisfies d := by
  obtain ⟨l, hl, ht⟩ := (clause_iff_exists a c).mp h
  exact (clause_iff_exists a d).mpr ⟨l, hsub hl, ht⟩

theorem formula_one (v : Sat.Valuation) (c : Sat.Clause) (h : v.satisfies c) :
    v.satisfies_fmla (Sat.Fmla.one c) := by
  refine ⟨fun d hd => ?_⟩
  have he : d = c := List.mem_singleton.mp hd
  exact he ▸ h

theorem formula_and (v : Sat.Valuation) (f g : Sat.Fmla)
    (hf : v.satisfies_fmla f) (hg : v.satisfies_fmla g) :
    v.satisfies_fmla (Sat.Fmla.and f g) := by
  refine ⟨fun c hc => ?_⟩
  rcases List.mem_append.mp hc with h | h
  · exact hf.prop c h
  · exact hg.prop c h

theorem gate_clause (a : Nat → Bool) (f : Sat.Fmla) (c d : List Sat.Literal)
    (hc : c ∈ f) (hsub : c ⊆ d) (hf : (valuation a).satisfies_fmla f) :
    (valuation a).satisfies d := clause_mono a c d hsub (hf.prop c hc)

def fixedOnRange (image : Fin 256 → Fin 256) (lo hi : Nat) : Bool :=
  (List.range' lo (hi-lo)).all (fun n =>
    if hn : n < 256 then decide (image ⟨n, hn⟩ = ⟨n, hn⟩) else true)

theorem fixedOnRange_spec (image : Fin 256 → Fin 256) (lo hi : Nat)
    (h : fixedOnRange image lo hi = true) (j : Fin 256)
    (hl : lo ≤ j.val) (hu : j.val < hi) : image j = j := by
  rw [fixedOnRange, List.all_eq_true] at h
  have hj : j.val ∈ List.range' lo (hi-lo) := by
    apply List.mem_range'.mpr
    exact ⟨j.val-lo, by omega, by omega⟩
  simpa only [dif_pos j.isLt, decide_eq_true_eq] using h j.val hj

#print axioms clause_mono
#print axioms formula_one
#print axioms formula_and
#print axioms gate_clause

end Crown.CertificateAssembly
