import Crown.Ranks
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

/-! Exact family domains and extension/downward-closure arguments. These
mathematical enumerations do not certify the compiled C++ executables. -/
namespace Crown.FamilyDomains
open Crown.Ranks

abbrev Families (n r : ℕ) := {s : Finset (Fin n) // s.card = r}

theorem card_families (n r : ℕ) : Fintype.card (Families n r) = Nat.choose n r := by
  simp [Families,Fintype.card_finset_len]

theorem card_balanced_families : Fintype.card (Families 64 6) = 74974368 := by
  rw [card_families]
  norm_num [Nat.choose]

theorem card_five_vertex_families : Fintype.card (Families 32 7) = 3365856 := by
  rw [card_families]
  norm_num [Nat.choose]

theorem extend_to_full_size {n r : ℕ} (hr : r ≤ n)
    (s : Finset (Fin n)) (hs : s.card ≤ r) :
    ∃ t : Families n r, s ⊆ t.val := by
  obtain ⟨t,hst,_,ht⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s) hs (by simpa using hr)
  exact ⟨⟨t,ht⟩,hst⟩

theorem feasible_restrict {I V : Type*} (rows : V → InitialRow I)
    (s t : Set V) (hst : s ⊆ t)
    (h : Feasible (fun x : t => rows x.val)) :
    Feasible (fun x : s => rows x.val) := by
  obtain ⟨r,hr,hn⟩ := h
  let f : s → t := fun x => ⟨x.val,hst x.property⟩
  exact ⟨fun x => r (f x),fun x => hr (f x),fun x y => hn (f x) (f y)⟩

/-- Verification for all full-size families extends to all smaller ones. -/
theorem all_smaller_of_full {n r : ℕ} {I P : Type*} (hr : r ≤ n)
    (rows : P → Fin n → InitialRow I)
    (h : ∀ t : Families n r, ∃ p, Feasible (fun x : {x // x ∈ t.val} => rows p x.val))
    (s : Finset (Fin n)) (hs : s.card ≤ r) :
    ∃ p, Feasible (fun x : {x // x ∈ s} => rows p x.val) := by
  obtain ⟨t,hst⟩ := extend_to_full_size hr s hs
  obtain ⟨p,hp⟩ := h t
  exact ⟨p,feasible_restrict (rows p) {x | x ∈ s} {x | x ∈ t.val} hst hp⟩

#print axioms card_families
#print axioms card_balanced_families
#print axioms card_five_vertex_families
#print axioms extend_to_full_size
#print axioms feasible_restrict
#print axioms all_smaller_of_full
end Crown.FamilyDomains
