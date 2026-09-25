import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

namespace Crown.CatalogueCardTransfer

/-- Transfer an abstract predicate to a finite set before computing its cardinality. -/
theorem card_subtype_and_eq_filter {α : Type*} [DecidableEq α]
    (U : Finset α) (P Q : α → Prop) [DecidablePred Q]
    (h : ∀ a, P a ↔ a ∈ U) :
    Nat.card {a // P a ∧ Q a} = (U.filter Q).card := by
  let e : {a // P a ∧ Q a} ≃ {a // a ∈ U.filter Q} :=
    Equiv.subtypeEquiv (Equiv.refl α) (fun a => by
      exact (and_congr_left (fun _ => h a)).trans Finset.mem_filter.symm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

#print axioms card_subtype_and_eq_filter
end Crown.CatalogueCardTransfer
