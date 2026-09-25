import Crown.Matchings
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators

namespace Crown.MatchingCounts

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

abbrev Selection (n r : ℕ) := {s : Finset (Fin n) // s.card = r}
abbrev Selected {n r : ℕ} (s : Selection n r) := {v : Fin n // v ∈ s.val}
abbrev Rejected {n r : ℕ} (s : Selection n r) := {v : Fin n // v ∉ s.val}

/-- XZ chooses which X vertices pair with Z; ZY and YZ choose the two
sets paired from Z to Y. All remaining X and Y vertices pair together. -/
abbrev Configuration (α β γ : ℕ) :=
  Σ XZ : Selection (α + β) β,
  Σ ZY : Selection (β + γ) γ,
  Σ YZ : Selection (α + γ) γ,
    (Selected XZ ≃ Rejected ZY) ×
      (Selected ZY ≃ Selected YZ) × (Rejected XZ ≃ Rejected YZ)

theorem card_selection (n r : ℕ) : Fintype.card (Selection n r) = Nat.choose n r := by
  simp [Selection]

theorem card_selected {n r : ℕ} (s : Selection n r) : Fintype.card (Selected s) = r := by
  simpa using s.property

theorem card_rejected {n r : ℕ} (s : Selection n r) : Fintype.card (Rejected s) = n - r := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, card_selected]

theorem card_equiv_of_cards {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (n : ℕ)
    (hA : Fintype.card A = n) (hB : Fintype.card B = n) :
    Fintype.card (A ≃ B) = n.factorial := by
  let e : A ≃ B := Fintype.equivOfCardEq (hA.trans hB.symm)
  rw [Fintype.card_equiv e, hA]

theorem card_configuration_fiber (α β γ : ℕ)
    (XZ : Selection (α + β) β) (ZY : Selection (β + γ) γ) (YZ : Selection (α + γ) γ) :
    Fintype.card ((Selected XZ ≃ Rejected ZY) ×
      (Selected ZY ≃ Selected YZ) × (Rejected XZ ≃ Rejected YZ)) =
        β.factorial * (γ.factorial * α.factorial) := by
  rw [Fintype.card_prod, Fintype.card_prod]
  rw [card_equiv_of_cards β (card_selected XZ) (by rw [card_rejected]; omega)]
  rw [card_equiv_of_cards γ (card_selected ZY) (card_selected YZ)]
  rw [card_equiv_of_cards α (by rw [card_rejected]; omega) (by rw [card_rejected]; omega)]

theorem card_configuration (α β γ : ℕ) : Fintype.card (Configuration α β γ) =
    Nat.choose (α + β) β * Nat.choose (α + γ) γ * Nat.choose (β + γ) γ *
      β.factorial * γ.factorial * α.factorial := by
  change Fintype.card (Σ XZ : Selection (α + β) β,
    Σ ZY : Selection (β + γ) γ, Σ YZ : Selection (α + γ) γ,
      (Selected XZ ≃ Rejected ZY) ×
        (Selected ZY ≃ Selected YZ) × (Rejected XZ ≃ Rejected YZ)) = _
  simp_rw [Fintype.card_sigma, card_configuration_fiber]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_selection]
  ac_rfl

theorem configuration_count_factorial (α β γ : ℕ) :
    Fintype.card (Configuration α β γ) * (α.factorial * β.factorial * γ.factorial) =
      (α + β).factorial * (α + γ).factorial * (β + γ).factorial := by
  rw [card_configuration]
  have hx := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left β α)
  have hy := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left γ α)
  have hz := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left γ β)
  simp only [Nat.add_sub_cancel_right] at hx hy hz
  calc
    _ = (Nat.choose (α + β) β * β.factorial * α.factorial) *
        (Nat.choose (α + γ) γ * γ.factorial * α.factorial) *
        (Nat.choose (β + γ) γ * γ.factorial * β.factorial) := by ac_rfl
    _ = _ := by rw [hx, hy, hz]

theorem card_configuration_eq_M (α β γ : ℕ) : Fintype.card (Configuration α β γ) =
    Arithmetic.M ((α + β + γ : ℕ) : ℤ) ((α + β : ℕ) : ℤ) ((α + γ : ℕ) : ℤ) ((β + γ : ℕ) : ℤ) := by
  unfold Arithmetic.M
  split_ifs with hc
  · have hx : (((α + β + γ : ℕ) : ℤ) - (α + β : ℕ)).toNat = γ := by omega
    have hy : (((α + β + γ : ℕ) : ℤ) - (α + γ : ℕ)).toNat = β := by omega
    have hz : (((α + β + γ : ℕ) : ℤ) - (β + γ : ℕ)).toNat = α := by omega
    simp only [Int.toNat_natCast, hx, hy, hz]
    have hp : γ.factorial * β.factorial * α.factorial =
        α.factorial * β.factorial * γ.factorial := by ac_rfl
    rw [hp, ← configuration_count_factorial]
    exact (Nat.mul_div_cancel _
      (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos α) (Nat.factorial_pos β)) (Nat.factorial_pos γ))).symm
  · exfalso
    apply hc
    omega

#print axioms card_configuration_eq_M

section RestrictedEmbeddings

variable (A B C D : Type*)

abbrev RestrictedEmbedding :=
  {e : B ⊕ A ↪ C ⊕ D // ∀ b, ∃ c, e (Sum.inl b) = Sum.inl c}

abbrev AvoidRange (f : B ↪ C) :=
  {y : C ⊕ D // ∀ b, y ≠ Sum.inl (f b)}

abbrev RestrictedData := Σ f : B ↪ C, A ↪ AvoidRange B C D f

def extractEmbedding (e : RestrictedEmbedding A B C D) : B ↪ C where
  toFun b := (e.val (Sum.inl b)).getLeft (by
    obtain ⟨c,hc⟩ := e.property b
    simp [hc])
  inj' := by
    intro b₁ b₂ h
    have h₁ := Sum.inl_getLeft (e.val (Sum.inl b₁)) (by obtain ⟨c,hc⟩ := e.property b₁; simp [hc])
    have h₂ := Sum.inl_getLeft (e.val (Sum.inl b₂)) (by obtain ⟨c,hc⟩ := e.property b₂; simp [hc])
    have he : e.val (Sum.inl b₁) = e.val (Sum.inl b₂) := h₁.symm.trans ((congrArg Sum.inl h).trans h₂)
    exact Sum.inl_injective (e.val.injective he)

theorem extractEmbedding_spec (e : RestrictedEmbedding A B C D) (b : B) :
    e.val (Sum.inl b) = Sum.inl (extractEmbedding A B C D e b) :=
  (Sum.inl_getLeft _ _).symm
noncomputable def restrictedEmbeddingEquiv : RestrictedEmbedding A B C D ≃ RestrictedData A B C D where
  toFun e := ⟨extractEmbedding A B C D e,
    ⟨fun a => ⟨e.val (Sum.inr a), by
      intro b h
      have he := e.val.injective (h.trans (extractEmbedding_spec A B C D e b).symm)
      cases he⟩,
      by intro a₁ a₂ h; exact Sum.inr_injective (e.val.injective (congrArg Subtype.val h))⟩⟩
  invFun q := ⟨⟨fun x => match x with
      | Sum.inl b => Sum.inl (q.1 b)
      | Sum.inr a => (q.2 a).val,
    by
      intro x y h
      cases x with
      | inl b =>
        cases y with
        | inl c => exact congrArg Sum.inl (q.1.injective (Sum.inl_injective h))
        | inr a => exact False.elim ((q.2 a).property b h.symm)
      | inr a =>
        cases y with
        | inl b => exact False.elim ((q.2 a).property b h)
        | inr c => exact congrArg Sum.inr (q.2.injective (Subtype.ext h))⟩,
    fun b => ⟨q.1 b, rfl⟩⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    cases x with
    | inl b => exact (extractEmbedding_spec A B C D e b).symm
    | inr a => rfl
  right_inv _ := rfl

open scoped Classical in
theorem card_avoidRange [Fintype B] [Fintype C] [Fintype D] (f : B ↪ C) :
    Fintype.card (AvoidRange B C D f) = Fintype.card C + Fintype.card D - Fintype.card B := by
  let j : B ↪ C ⊕ D := f.trans Function.Embedding.inl
  let e : AvoidRange B C D f ≃ {y : C ⊕ D // y ∉ Set.range j} :=
    Equiv.subtypeEquivProp (by
      funext y
      apply propext
      simp only [Set.mem_range, not_exists, j, Function.Embedding.trans_apply,
        Function.Embedding.inl_apply, ne_eq]
      simp only [eq_comm])
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_sum]

open scoped Classical in
theorem card_restrictedEmbedding [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (hcard : Fintype.card A + Fintype.card B = Fintype.card C + Fintype.card D) :
    Fintype.card (RestrictedEmbedding A B C D) =
      (Fintype.card C).descFactorial (Fintype.card B) * (Fintype.card A).factorial := by
  rw [Fintype.card_congr (restrictedEmbeddingEquiv A B C D), Fintype.card_sigma]
  have hterm (f : B ↪ C) : Fintype.card (A ↪ AvoidRange B C D f) = (Fintype.card A).factorial := by
    rw [Fintype.card_embedding_eq, card_avoidRange]
    have he : Fintype.card C + Fintype.card D - Fintype.card B = Fintype.card A := by omega
    rw [he, Nat.descFactorial_self]
  simp_rw [hterm]
  simp [Fintype.card_embedding_eq]

noncomputable def equivEmbeddingOfCardEq {E F : Type*} [Fintype E] [Fintype F]
    (hc : Fintype.card E = Fintype.card F) : (E ≃ F) ≃ (E ↪ F) where
  toFun e := e.toEmbedding
  invFun e := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective,hc⟩)
  left_inv e := by ext x; rfl
  right_inv e := by ext x; rfl

abbrev RestrictedEquiv :=
  {e : B ⊕ A ≃ C ⊕ D // ∀ b, ∃ c, e (Sum.inl b) = Sum.inl c}

open scoped Classical in
theorem card_restrictedEquiv [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (hcard : Fintype.card A + Fintype.card B = Fintype.card C + Fintype.card D) :
    Fintype.card (RestrictedEquiv A B C D) =
      (Fintype.card C).descFactorial (Fintype.card B) * (Fintype.card A).factorial := by
  have hc : Fintype.card (B ⊕ A) = Fintype.card (C ⊕ D) := by
    simp only [Fintype.card_sum]
    omega
  let e : RestrictedEquiv A B C D ≃ RestrictedEmbedding A B C D :=
    Equiv.subtypeEquiv (equivEmbeddingOfCardEq hc) (fun _ => Iff.rfl)
  rw [Fintype.card_congr e, card_restrictedEmbedding A B C D hcard]
open scoped Classical in
theorem natCard_restrictedEquiv [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (hcard : Fintype.card A + Fintype.card B = Fintype.card C + Fintype.card D) :
    Nat.card (RestrictedEquiv A B C D) =
      (Fintype.card C).descFactorial (Fintype.card B) * (Fintype.card A).factorial := by
  rw [Nat.card_eq_fintype_card]
  exact card_restrictedEquiv A B C D hcard
end RestrictedEmbeddings

abbrev CrossPairing (α β γ : ℕ) :=
  Σ t : Selection (β + γ) γ,
    RestrictedEquiv (Fin (α + β)) (Selected t) (Fin (α + γ)) (Rejected t)

open scoped Classical in
set_option maxHeartbeats 400000 in
theorem card_crossPairing (α β γ : ℕ) : Fintype.card (CrossPairing α β γ) =
    Arithmetic.M ((α+β+γ : ℕ) : ℤ) ((α+β : ℕ) : ℤ) ((α+γ : ℕ) : ℤ) ((β+γ : ℕ) : ℤ) := by
  rw [← card_configuration_eq_M, card_configuration]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Σ t : Selection (β+γ) γ,
    RestrictedEquiv (Fin (α+β)) (Selected t) (Fin (α+γ)) (Rejected t)) = _
  rw [Nat.card_sigma]
  have hterm (t : Selection (β+γ) γ) :
      Nat.card (RestrictedEquiv (Fin (α+β)) (Selected t) (Fin (α+γ)) (Rejected t)) =
      (α+γ).descFactorial γ * (α+β).factorial := by
    have hc : Fintype.card (Fin (α+β)) + Fintype.card (Selected t) =
        Fintype.card (Fin (α+γ)) + Fintype.card (Rejected t) := by
      rw [Fintype.card_fin, Fintype.card_fin, card_selected, card_rejected]
      omega
    have hh := natCard_restrictedEquiv (Fin (α+β)) (Selected t) (Fin (α+γ)) (Rejected t) hc
    exact hh.trans (by rw [Fintype.card_fin, Fintype.card_fin, card_selected])
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_selection,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hx := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left β α)
  simp only [Nat.add_sub_cancel_right] at hx
  rw [← hx]
  ac_rfl
section ClassSets

open scoped Classical

variable (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z]

abbrev ClassVertices := X ⊕ (Y ⊕ Z)
abbrev ClassFirstSets := {s : Finset (ClassVertices X Y Z) //
  (∀ x, Sum.inl x ∈ s) ∧ (∀ y, Sum.inr (Sum.inl y) ∉ s)}

noncomputable def classZSet (s : ClassFirstSets X Y Z) : Finset Z :=
  Finset.univ.filter (fun z => Sum.inr (Sum.inr z) ∈ s.val)

noncomputable def classSetEquiv : ClassFirstSets X Y Z ≃ Finset Z where
  toFun := classZSet X Y Z
  invFun t := ⟨Finset.univ.filter (fun v => match v with
    | Sum.inl _ => True
    | Sum.inr (Sum.inl _) => False
    | Sum.inr (Sum.inr z) => z ∈ t), by simp⟩
  left_inv s := by
    apply Subtype.ext
    ext v
    cases v with
    | inl x => simp [classZSet, s.property.1 x]
    | inr v => cases v with
      | inl y => simp [classZSet, s.property.2 y]
      | inr z => simp [classZSet]
  right_inv t := by ext z; simp [classZSet]

noncomputable def classFirstEquiv (s : ClassFirstSets X Y Z) :
    {v : ClassVertices X Y Z // v ∈ s.val} ≃ ({z : Z // z ∈ classZSet X Y Z s} ⊕ X) where
  toFun v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl x => exact Sum.inr x
    | inr v => cases v with
      | inl y => exact False.elim (s.property.2 y hv)
      | inr z => exact Sum.inl ⟨z, by simpa [classZSet] using hv⟩
  invFun v := match v with
    | Sum.inl z => ⟨Sum.inr (Sum.inr z.val), (Finset.mem_filter.mp z.property).2⟩
    | Sum.inr x => ⟨Sum.inl x, s.property.1 x⟩
  left_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl x => rfl
    | inr v => cases v with
      | inl y => exact False.elim (s.property.2 y hv)
      | inr z => rfl
  right_inv v := by cases v <;> rfl

noncomputable def classSecondEquiv (s : ClassFirstSets X Y Z) :
    {v : ClassVertices X Y Z // v ∉ s.val} ≃ (Y ⊕ {z : Z // z ∉ classZSet X Y Z s}) where
  toFun v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl x => exact False.elim (hv (s.property.1 x))
    | inr v => cases v with
      | inl y => exact Sum.inl y
      | inr z => exact Sum.inr ⟨z, by simpa [classZSet] using hv⟩
  invFun v := match v with
    | Sum.inl y => ⟨Sum.inr (Sum.inl y), s.property.2 y⟩
    | Sum.inr z => ⟨Sum.inr (Sum.inr z.val), fun h => z.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
  left_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl x => exact False.elim (hv (s.property.1 x))
    | inr v => cases v with
      | inl y => rfl
      | inr z => rfl
  right_inv v := by cases v <;> rfl

omit [Fintype X] [Fintype Y] in
theorem classSecondEquiv_symm_inl (s : ClassFirstSets X Y Z) (y : Y) :
    ((classSecondEquiv X Y Z s).symm (Sum.inl y)).val = Sum.inr (Sum.inl y) := rfl
omit [Fintype X] [Fintype Y] in
theorem classSecondEquiv_inl (s : ClassFirstSets X Y Z)
    (v : {v : ClassVertices X Y Z // v ∉ s.val}) (y : Y) :
    classSecondEquiv X Y Z s v = Sum.inl y ↔ v.val = Sum.inr (Sum.inl y) := by
  constructor
  · intro h
    have hh := congrArg (fun z => ((classSecondEquiv X Y Z s).symm z).val) h
    simpa only [Equiv.symm_apply_apply, classSecondEquiv_symm_inl] using hh
  · intro h
    have hh : v = (classSecondEquiv X Y Z s).symm (Sum.inl y) := Subtype.ext (h.trans (classSecondEquiv_symm_inl X Y Z s y).symm)
    rw [hh, Equiv.apply_symm_apply]

def ZtoY (s : ClassFirstSets X Y Z)
    (e : {v : ClassVertices X Y Z // v ∈ s.val} ≃ {v : ClassVertices X Y Z // v ∉ s.val}) : Prop :=
  ∀ z hz, ∃ y, (e ⟨Sum.inr (Sum.inr z), hz⟩).val = Sum.inr (Sum.inl y)

abbrev ClassPairing := Σ s : ClassFirstSets X Y Z,
  {e : {v : ClassVertices X Y Z // v ∈ s.val} ≃ {v : ClassVertices X Y Z // v ∉ s.val} // ZtoY X Y Z s e}

noncomputable def classFiberEquiv (s : ClassFirstSets X Y Z) :
    {e : {v : ClassVertices X Y Z // v ∈ s.val} ≃ {v : ClassVertices X Y Z // v ∉ s.val} // ZtoY X Y Z s e} ≃
      RestrictedEquiv X {z : Z // z ∈ classZSet X Y Z s} Y {z : Z // z ∉ classZSet X Y Z s} :=
  Equiv.subtypeEquiv (Equiv.equivCongr (classFirstEquiv X Y Z s) (classSecondEquiv X Y Z s)) (by
    intro e
    constructor
    · intro h z
      have hz : Sum.inr (Sum.inr z.val) ∈ s.val := (Finset.mem_filter.mp z.property).2
      obtain ⟨y,hy⟩ := h z.val hz
      refine ⟨y, ?_⟩
      change classSecondEquiv X Y Z s (e ⟨Sum.inr (Sum.inr z.val), hz⟩) = Sum.inl y
      exact (classSecondEquiv_inl X Y Z s _ y).mpr hy
    · intro h z hz
      let z' : {z : Z // z ∈ classZSet X Y Z s} := ⟨z, by simpa [classZSet] using hz⟩
      obtain ⟨y,hy⟩ := h z'
      refine ⟨y, ?_⟩
      apply (classSecondEquiv_inl X Y Z s _ y).mp
      exact hy)

noncomputable def classPairingEquiv : ClassPairing X Y Z ≃
    (Σ t : Finset Z, RestrictedEquiv X {z : Z // z ∈ t} Y {z : Z // z ∉ t}) :=
  Equiv.sigmaCongr (classSetEquiv X Y Z) (classFiberEquiv X Y Z)

/-- The full pairing event with directions XY, XZ and ZY. First endpoints
include every X vertex and no Y vertex; each first Z vertex pairs to Y. -/
def DirectedCrossEvent (p : Matchings.PairingOn (ClassVertices X Y Z)) : Prop :=
  (∀ x, Sum.inl x ∈ p.1) ∧ (∀ y, Sum.inr (Sum.inl y) ∉ p.1) ∧
    ∀ z hz, ∃ y, (p.2 ⟨Sum.inr (Sum.inr z), hz⟩).val = Sum.inr (Sum.inl y)

def CrossDirection : ClassVertices X Y Z → ClassVertices X Y Z → Prop
  | Sum.inl _, Sum.inr (Sum.inl _) => True
  | Sum.inl _, Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => True
  | _, _ => False

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem directedCrossEvent_iff (p : Matchings.PairingOn (ClassVertices X Y Z)) :
    DirectedCrossEvent X Y Z p ↔
      ∀ a, CrossDirection X Y Z a.val (p.2 a).val := by
  constructor
  · rintro ⟨hx,hy,hz⟩ a
    rcases a with ⟨a,ha⟩
    cases a with
    | inl x =>
      have hnot := (p.2 ⟨Sum.inl x,ha⟩).property
      cases he : (p.2 ⟨Sum.inl x,ha⟩).val with
      | inl x' => rw [he] at hnot; exact False.elim (hnot (hx x'))
      | inr v => cases v <;> trivial
    | inr v => cases v with
      | inl y => exact False.elim (hy y ha)
      | inr z => obtain ⟨y,he⟩ := hz z ha; rw [he]; trivial
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro x
      by_contra hx
      let b : {v : ClassVertices X Y Z // v ∉ p.1} := ⟨Sum.inl x,hx⟩
      have hh := h (p.2.symm b)
      rw [Equiv.apply_symm_apply] at hh
      change CrossDirection X Y Z (p.2.symm b).val (Sum.inl x) at hh
      cases he : (p.2.symm b).val with
      | inl _ => rw [he] at hh; exact hh
      | inr v => rw [he] at hh; cases v <;> exact hh
    · intro y hy
      have hh := h ⟨Sum.inr (Sum.inl y),hy⟩
      cases (p.2 ⟨Sum.inr (Sum.inl y),hy⟩).val <;> exact hh
    · intro z hz
      have hh := h ⟨Sum.inr (Sum.inr z),hz⟩
      cases he : (p.2 ⟨Sum.inr (Sum.inr z),hz⟩).val with
      | inl x => rw [he] at hh; exact False.elim hh
      | inr v => cases v with
        | inl y => exact ⟨y,rfl⟩
        | inr z' => rw [he] at hh; exact False.elim hh
noncomputable def classPairingEventEquiv : ClassPairing X Y Z ≃
    {p : Matchings.PairingOn (ClassVertices X Y Z) // DirectedCrossEvent X Y Z p} where
  toFun p := ⟨⟨p.1.val,p.2.val⟩,p.1.property.1,p.1.property.2,p.2.property⟩
  invFun p := ⟨⟨p.val.1,p.property.1,p.property.2.1⟩,p.val.2,p.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end ClassSets
open scoped Classical in
theorem card_directedCrossEvent (α β γ : ℕ) :
    Fintype.card {p : Matchings.PairingOn (ClassVertices (Fin (α+β)) (Fin (α+γ)) (Fin (β+γ))) //
      DirectedCrossEvent (Fin (α+β)) (Fin (α+γ)) (Fin (β+γ)) p} =
      Arithmetic.M ((α+β+γ : ℕ) : ℤ) ((α+β : ℕ) : ℤ) ((α+γ : ℕ) : ℤ) ((β+γ : ℕ) : ℤ) := by
  rw [← Fintype.card_congr (classPairingEventEquiv (Fin (α+β)) (Fin (α+γ)) (Fin (β+γ))),
    Fintype.card_congr (classPairingEquiv (Fin (α+β)) (Fin (α+γ)) (Fin (β+γ)))]
  let F := fun t : Finset (Fin (β+γ)) =>
    RestrictedEquiv (Fin (α+β)) {z : Fin (β+γ) // z ∈ t} (Fin (α+γ)) {z : Fin (β+γ) // z ∉ t}
  have hforced (t : Finset (Fin (β+γ))) (e : F t) : t.card = γ := by
    have h := Fintype.card_congr e.val
    simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin, Fintype.card_subtype_compl] at h
    have ht : t.card ≤ β+γ := by simpa using Finset.card_le_univ t
    omega
  let eqv := Equiv.sigmaSubtypeEquivOfSubset F (fun t => t.card = γ) hforced
  rw [← Fintype.card_congr eqv]
  exact card_crossPairing α β γ

open scoped Classical in
noncomputable def crossCount (x y z : ℕ) : ℕ :=
  Fintype.card {p : Matchings.PairingOn (ClassVertices (Fin x) (Fin y) (Fin z)) //
    DirectedCrossEvent (Fin x) (Fin y) (Fin z) p}

open scoped Classical in
theorem directedCross_size_constraints (k x y z : ℕ) (hsum : x+y+z = 2*k)
    (p : {p : Matchings.PairingOn (ClassVertices (Fin x) (Fin y) (Fin z)) //
      DirectedCrossEvent (Fin x) (Fin y) (Fin z) p}) : x ≤ k ∧ y ≤ k ∧ z ≤ k := by
  let q := classPairingEquiv (Fin x) (Fin y) (Fin z)
    ((classPairingEventEquiv (Fin x) (Fin y) (Fin z)).symm p)
  let f : RestrictedEmbedding (Fin x) {v : Fin z // v ∈ q.1} (Fin y) {v : Fin z // v ∉ q.1} :=
    ⟨q.2.val.toEmbedding,q.2.property⟩
  have hle := Fintype.card_le_of_embedding
    (extractEmbedding (Fin x) {v : Fin z // v ∈ q.1} (Fin y) {v : Fin z // v ∉ q.1} f)
  have hbal := Fintype.card_congr q.2.val
  simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin,
    Fintype.card_subtype_compl] at hle hbal
  have ht : q.1.card ≤ z := by simpa using Finset.card_le_univ q.1
  omega

open scoped Classical in
theorem crossCount_eq_M (k x y z : ℕ) (hsum : x+y+z = 2*k) :
    crossCount x y z = Arithmetic.M (k : ℤ) (x : ℤ) (y : ℤ) (z : ℤ) := by
  by_cases hvalid : x ≤ k ∧ y ≤ k ∧ z ≤ k
  · have hx : x = (k-z)+(k-y) := by omega
    have hy : y = (k-z)+(k-x) := by omega
    have hz : z = (k-y)+(k-x) := by omega
    have hh : crossCount ((k-z)+(k-y)) ((k-z)+(k-x)) ((k-y)+(k-x)) =
        Arithmetic.M (((k-z)+(k-y)+(k-x) : ℕ) : ℤ)
          (((k-z)+(k-y) : ℕ) : ℤ) (((k-z)+(k-x) : ℕ) : ℤ) (((k-y)+(k-x) : ℕ) : ℤ) :=
      card_directedCrossEvent (k-z) (k-y) (k-x)
    have hk : (k-z)+(k-y)+(k-x) = k := by omega
    rw [hk] at hh
    simpa only [← hx, ← hy, ← hz] using hh
  · have hempty : IsEmpty {p : Matchings.PairingOn (ClassVertices (Fin x) (Fin y) (Fin z)) //
        DirectedCrossEvent (Fin x) (Fin y) (Fin z) p} :=
      ⟨fun p => hvalid (directedCross_size_constraints k x y z hsum p)⟩
    have hc : crossCount x y z = 0 := by
      let := hempty
      exact Fintype.card_eq_zero
    rw [hc]
    unfold Arithmetic.M
    split_ifs with h
    · exfalso; apply hvalid; omega
    · rfl

section ClassTransport

open scoped Classical

variable {X Y Z X' Y' Z' : Type*}

def classRelabel (ex : X ≃ X') (ey : Y ≃ Y') (ez : Z ≃ Z') :
    ClassVertices X Y Z ≃ ClassVertices X' Y' Z' :=
  Equiv.sumCongr ex (Equiv.sumCongr ey ez)

theorem crossDirection_classRelabel (ex : X ≃ X') (ey : Y ≃ Y') (ez : Z ≃ Z')
    (a b : ClassVertices X Y Z) :
    CrossDirection X' Y' Z' (classRelabel ex ey ez a) (classRelabel ex ey ez b) ↔
      CrossDirection X Y Z a b := by
  cases a with
  | inl x => cases b with
    | inl x' => rfl
    | inr b => cases b <;> rfl
  | inr a => cases a <;> cases b with
    | inl x' => rfl
    | inr b => cases b <;> rfl

theorem directedCrossEvent_respects (p : Matchings.PairingOn (ClassVertices X Y Z)) :
    DirectedCrossEvent X Y Z p ↔ Matchings.Respects p (CrossDirection X Y Z) := by
  rw [directedCrossEvent_iff]
  constructor
  · intro h a b hp
    have hh := h ⟨a,hp.1⟩
    rw [hp.2.2 hp.1 hp.2.1] at hh
    exact hh
  · intro h a
    exact h a.val (p.2 a).val ⟨a.property,(p.2 a).property,fun _ _ => rfl⟩

theorem directedCrossEvent_relabel (ex : X ≃ X') (ey : Y ≃ Y') (ez : Z ≃ Z')
    (p : Matchings.PairingOn (ClassVertices X Y Z)) :
    DirectedCrossEvent X' Y' Z' (Matchings.relabel (classRelabel ex ey ez) p) ↔
      DirectedCrossEvent X Y Z p := by
  rw [directedCrossEvent_respects,Matchings.respects_relabel,directedCrossEvent_respects]
  simp only [Matchings.Respects,crossDirection_classRelabel]

theorem card_directedCrossEvent_finite [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*k) :
    Fintype.card {p : Matchings.PairingOn (ClassVertices X Y Z) // DirectedCrossEvent X Y Z p} =
      Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) (Fintype.card Y : ℤ) (Fintype.card Z : ℤ) := by
  let ex := Fintype.equivFin X
  let ey := Fintype.equivFin Y
  let ez := Fintype.equivFin Z
  let e : {p : Matchings.PairingOn (ClassVertices X Y Z) // DirectedCrossEvent X Y Z p} ≃
      {p : Matchings.PairingOn (ClassVertices (Fin (Fintype.card X)) (Fin (Fintype.card Y)) (Fin (Fintype.card Z))) //
        DirectedCrossEvent (Fin (Fintype.card X)) (Fin (Fintype.card Y)) (Fin (Fintype.card Z)) p} :=
    Equiv.subtypeEquiv (Matchings.relabel (classRelabel ex ey ez))
      (fun p => (directedCrossEvent_relabel ex ey ez p).symm)
  rw [Fintype.card_congr e]
  exact crossCount_eq_M k (Fintype.card X) (Fintype.card Y) (Fintype.card Z) hsum

theorem natCard_directedCrossEvent_finite [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*k) :
    Nat.card {p : Matchings.PairingOn (ClassVertices X Y Z) // DirectedCrossEvent X Y Z p} =
      Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) (Fintype.card Y : ℤ) (Fintype.card Z : ℤ) := by
  rw [Nat.card_eq_fintype_card]
  exact card_directedCrossEvent_finite k hsum
end ClassTransport

#print axioms card_directedCrossEvent_finite#print axioms crossCount_eq_M#print axioms card_directedCrossEvent#print axioms card_restrictedEmbedding

end Crown.MatchingCounts
