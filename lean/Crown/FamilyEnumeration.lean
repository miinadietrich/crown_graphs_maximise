import Crown.FamilyDomains
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi

namespace Crown.FamilyEnumeration
open Crown.FamilyDomains
open scoped Classical

abbrev IncreasingFamily (n r : ℕ) := {v : Fin r → Fin n // StrictMono v}

noncomputable def tupleFamily {n r : ℕ} (v : IncreasingFamily n r) : Families n r :=
  ⟨Finset.univ.image v.val,by
    rw [Finset.card_image_of_injective _ v.property.injective]
    simp⟩

noncomputable def familyTuple {n r : ℕ} (s : Families n r) : IncreasingFamily n r :=
  ⟨s.val.orderEmbOfFin s.property,(s.val.orderEmbOfFin s.property).strictMono⟩

theorem tuple_family {n r : ℕ} (s : Families n r) :
    tupleFamily (familyTuple s) = s := by
  apply Subtype.ext
  exact Finset.image_orderEmbOfFin_univ _ _

theorem family_tuple {n r : ℕ} (v : IncreasingFamily n r) :
    familyTuple (tupleFamily v) = v := by
  apply Subtype.ext
  exact (Finset.orderEmbOfFin_unique (tupleFamily v).property
    (fun x => Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩) v.property).symm

noncomputable def tupleEquiv (n r : ℕ) : IncreasingFamily n r ≃ Families n r where
  toFun := tupleFamily
  invFun := familyTuple
  left_inv := family_tuple
  right_inv := tuple_family

/-- Every fixed-size family has exactly one increasing enumeration. -/
theorem unique_increasing_enumeration {n r : ℕ} (s : Families n r) :
    ∃! v : IncreasingFamily n r, tupleFamily v = s := by
  exact ⟨familyTuple s,tuple_family s,fun v hv => by
    have h := congrArg familyTuple hv
    simpa only [family_tuple] using h⟩

/-- The fixed-size subset enumeration has precisely the intended domain. -/
theorem subset_domain (n r : ℕ) (s : Finset (Fin n)) :
    s ∈ (Finset.univ : Finset (Fin n)).powersetCard r ↔ s.card = r := by
  simp

theorem card_increasing_families (n r : ℕ) :
    Fintype.card (IncreasingFamily n r) = Nat.choose n r := by
  rw [Fintype.card_congr (tupleEquiv n r),card_families]

#print axioms tuple_family
#print axioms family_tuple
#print axioms unique_increasing_enumeration
#print axioms subset_domain
#print axioms card_increasing_families
end Crown.FamilyEnumeration
