import Crown.FiniteClosureChecks
import Crown.CertificateSixSemantics

namespace Crown.ThreeClosureTransport
open Crown.Ranks Crown.CertificateSemantics
open Crown.CertificateSixSemantics

def coverageCheck {q g : ℕ} (core : Fin q → Finset (Fin 64))
    (globalCores : Fin g → List (Fin 64)) (witness : Fin q → Fin g)
    (code : Fin 64 → Fin 64) : Bool :=
  (List.finRange q).all fun c => (globalCores (witness c)).all fun m => decide (code m ∈ core c)

theorem coverage_of_check {q g : ℕ} (rows : Fin 64 → InitialRow (Fin 3))
    (core : Fin q → Finset (Fin 64)) (p : Pairing6)
    (globalCores : Fin g → List (Fin 64)) (witness : Fin q → Fin g)
    (code : Fin 64 → Fin 64)
    (hcode : ∀ m, rows (code m) = rowOfMask (pairsOfEquiv p) (maskBits m))
    (h : coverageCheck core globalCores witness code = true) :
    ∀ c, witness c ∈ List.ofFn witness ∧ ∀ m ∈ globalCores (witness c),
      ∃ x ∈ core c, rows x = rowOfMask (pairsOfEquiv p) (maskBits m) := by
  intro c
  refine ⟨List.mem_ofFn.mpr ⟨c, rfl⟩, ?_⟩
  intro m hm
  have hc := List.all_eq_true.mp h c (List.mem_finRange _)
  have hmem := List.all_eq_true.mp hc m hm
  exact ⟨code m, of_decide_eq_true hmem, hcode m⟩

theorem selected_core {j q g : ℕ}
    (rows : Fin 64 → InitialRow (Fin 3)) (hrows : Function.Bijective rows)
    (owner : Fin j → Fin 64) (support : Fin j → Finset (Fin 64))
    (core : Fin q → Finset (Fin 64))
    (cert : IndexedFiniteClosure.Certificate rows owner support ((List.finRange q).map core) 6)
    (p : Pairing6) (globalCores : Fin g → List (Fin 64))
    (template : List (Fin g)) (witness : Fin q → Fin g)
    (hcover : ∀ c, witness c ∈ template ∧ ∀ m ∈ globalCores (witness c),
      ∃ x ∈ core c, rows x = rowOfMask (pairsOfEquiv p) (maskBits m))
    (s : Finset (Fin 64)) (hs : s.card ≤ 6)
    (hbad : ¬ Feasible (fun m : {m // m ∈ s} => rowOfMask (pairsOfEquiv p) (maskBits m.val))) :
    ∃ c ∈ template, ∀ m ∈ globalCores c, m ∈ s := by
  classical
  let e : Fin 64 ≃ InitialRow (Fin 3) := Equiv.ofBijective rows hrows
  let f : Fin 64 → Fin 64 := fun m => e.symm (rowOfMask (pairsOfEquiv p) (maskBits m))
  have hf : ∀ m, rows (f m) = rowOfMask (pairsOfEquiv p) (maskBits m) :=
    fun m => e.apply_symm_apply _
  let t := s.image f
  have ht : t.card ≤ 6 := (Finset.card_image_le).trans hs
  have hbad' : ¬ Feasible (fun x : {x // x ∈ t} => rows x.val) := by
    rintro ⟨r, hr, hn⟩
    apply hbad
    let lift : {m // m ∈ s} → {x // x ∈ t} := fun m =>
      ⟨f m.val, Finset.mem_image.mpr ⟨m.val, m.property, rfl⟩⟩
    refine ⟨fun m => r (lift m), ?_, fun m n => hn (lift m) (lift n)⟩
    intro m
    simpa only [lift, hf] using hr (lift m)
  obtain ⟨w, hw, hsub⟩ := IndexedFiniteClosure.selected_core_of_infeasible cert t ht hbad'
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hw
  refine ⟨witness c, (hcover c).1, ?_⟩
  intro m hm
  obtain ⟨x, hx, hxm⟩ := (hcover c).2 m hm
  obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp (hsub hx)
  have heq : rowOfMask (pairsOfEquiv p) (maskBits n) =
      rowOfMask (pairsOfEquiv p) (maskBits m) := by
    rw [← hf n, hnx, hxm]
  have hinj : Function.Injective (fun m : Fin 64 => rowOfMask (pairsOfEquiv p) (maskBits m)) :=
    mask_rank_injective _ (by
      intro a
      obtain ⟨⟨i,b⟩, rfl⟩ := p.surjective a
      refine ⟨i, ?_⟩
      cases b
      · exact Or.inl rfl
      · exact Or.inr rfl)
  exact hinj heq ▸ hn

#print axioms selected_core
end Crown.ThreeClosureTransport
