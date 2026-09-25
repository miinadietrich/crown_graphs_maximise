import Crown.CertificateAssembly

/-! The obstruction variables in the CNF are witnesses. They need not equal
the truth values of core containment in an arbitrary satisfying assignment. -/
namespace Crown.ObstructionEncoding

variable {v g t : ℕ}

def Encoding (cores : Fin g → List (Fin v)) (templates : Fin t → List (Fin g))
    (cap : ℕ) (s : Fin v → Bool) (c : Fin g → Bool) : Prop :=
  Fintype.card {m // s m = true} ≤ cap ∧
  (∀ i, c i = true → ∀ m ∈ cores i, s m = true) ∧
  (∀ j, ∃ i ∈ templates j, c i = true)

/-- Existential obstruction variables express exactly the selected-core
condition, without imposing their converses on arbitrary assignments. -/
theorem encoding_iff (cores : Fin g → List (Fin v))
    (templates : Fin t → List (Fin g)) (cap : ℕ) (s : Fin v → Bool) :
    (∃ c, Encoding cores templates cap s c) ↔
      Fintype.card {m // s m = true} ≤ cap ∧
      ∀ j, ∃ i ∈ templates j, ∀ m ∈ cores i, s m = true := by
  constructor
  · rintro ⟨c,hcard,himp,hcover⟩
    refine ⟨hcard,fun j => ?_⟩
    obtain ⟨i,hi,hc⟩ := hcover j
    exact ⟨i,hi,himp i hc⟩
  · rintro ⟨hcard,hcover⟩
    refine ⟨fun i => (cores i).all s,hcard,?_,?_⟩
    · intro i hi
      exact List.all_eq_true.mp hi
    · intro j
      obtain ⟨i,hi,hcore⟩ := hcover j
      exact ⟨i,hi,List.all_eq_true.mpr hcore⟩

/-- Any separately proved exact catalogue can instantiate the encoding
equivalence. Its completeness is an explicit premise of this generic lemma. -/
theorem encoding_iff_obstruction (cores : Fin g → List (Fin v))
    (templates : Fin t → List (Fin g)) (cap : ℕ)
    (bad : (Fin v → Bool) → Prop)
    (hcatalogue : ∀ s, bad s ↔ ∀ j, ∃ i ∈ templates j, ∀ m ∈ cores i, s m = true)
    (s : Fin v → Bool) :
    (∃ c, Encoding cores templates cap s c) ↔
      Fintype.card {m // s m = true} ≤ cap ∧ bad s := by
  rw [encoding_iff,hcatalogue]

theorem satisfiable_iff (cores : Fin g → List (Fin v))
    (templates : Fin t → List (Fin g)) (cap : ℕ)
    (bad : (Fin v → Bool) → Prop)
    (hcatalogue : ∀ s, bad s ↔ ∀ j, ∃ i ∈ templates j, ∀ m ∈ cores i, s m = true) :
    (∃ s c, Encoding cores templates cap s c) ↔
      ∃ s, Fintype.card {m // s m = true} ≤ cap ∧ bad s := by
  exact exists_congr (fun s => encoding_iff_obstruction cores templates cap bad hcatalogue s)

#print axioms encoding_iff
#print axioms encoding_iff_obstruction
#print axioms satisfiable_iff
end Crown.ObstructionEncoding
