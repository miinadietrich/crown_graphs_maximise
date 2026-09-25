import Crown.Matchings
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Unordered perfect pairings as partitions into two-element sets. The
finite enumeration selects k edges from the choose(2k,2) possible pairs,
retaining precisely the pairwise disjoint families. -/

namespace Crown.UnorderedMatchings
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def DisjointPairs (P : Finset (Finset V)) : Prop :=
  ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f

instance (P : Finset (Finset V)) : Decidable (DisjointPairs P) := by
  unfold DisjointPairs
  exact @Finset.decidableDforallFinset _ P _
    (fun e _ => @Finset.decidableDforallFinset _ P _
      (fun f _ => inferInstance))

def IsPerfectPairing (P : Finset (Finset V)) : Prop :=
  (∀ e ∈ P, e.card = 2) ∧ DisjointPairs P ∧ P.biUnion id = Finset.univ

/-- The optimized finite domain; no ordering or orientation of pairs is present. -/
def families (k : ℕ) : Finset (Finset (Finset (Fin (2*k)))) :=
  ((Finset.univ.powersetCard 2).powersetCard k).filter DisjointPairs

abbrev Pairings (k : ℕ) := ↥(families k)

theorem mem_families (k : ℕ) (P : Finset (Finset (Fin (2*k)))) :
    P ∈ families k ↔ (∀ e ∈ P, e.card = 2) ∧ P.card = k ∧ DisjointPairs P := by
  constructor
  · intro h
    obtain ⟨hP,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨he,hk⟩ := Finset.mem_powersetCard.mp hP
    exact ⟨fun e hmem => (Finset.mem_powersetCard.mp (he hmem)).2,hk,hd⟩
  · rintro ⟨he,hk,hd⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_,hk⟩,hd⟩
    intro e hm
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,he e hm⟩

theorem disjoint_as_sets (P : Finset (Finset V)) (h : DisjointPairs P) :
    (P : Set (Finset V)).PairwiseDisjoint id := h

theorem union_card (P : Finset (Finset V)) (he : ∀ e ∈ P, e.card = 2)
    (hd : DisjointPairs P) : (P.biUnion id).card = 2 * P.card := by
  rw [Finset.card_biUnion (disjoint_as_sets P hd)]
  calc
    (∑ e ∈ P, (id e).card) = ∑ _e ∈ P, (2:ℕ) :=
      Finset.sum_congr rfl (fun e hm => he e hm)
    _ = 2 * P.card := by simp [Nat.mul_comm]

theorem mem_families_iff_perfect (k : ℕ) (P : Finset (Finset (Fin (2*k)))) :
    P ∈ families k ↔ IsPerfectPairing P := by
  rw [mem_families]
  constructor
  · rintro ⟨he,hk,hd⟩
    refine ⟨he,hd,?_⟩
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,Fintype.card_fin,union_card P he hd,hk]
  · rintro ⟨he,hd,hcover⟩
    have hc := union_card P he hd
    rw [hcover,Finset.card_univ,Fintype.card_fin] at hc
    exact ⟨he,by omega,hd⟩

/-- The counting type is equivalent to the literal partition definition. -/
def semanticEquiv (k : ℕ) : Pairings k ≃
    {P : Finset (Finset (Fin (2*k))) // IsPerfectPairing P} where
  toFun p := ⟨p.val,(mem_families_iff_perfect k p.val).mp p.property⟩
  invFun p := ⟨p.val,(mem_families_iff_perfect k p.val).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

#print axioms mem_families_iff_perfect
#print axioms semanticEquiv
end Crown.UnorderedMatchings
