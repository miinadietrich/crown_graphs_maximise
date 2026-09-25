import Crown.MatchingCounts

/-!
# Exceptional pairs in the directed comparison count

The counts in this module concern actual subsets of the oriented-unordered
pairing sample space. A specified exceptional edge is deleted by the
equivalence in `Matchings`; the remaining edge relation is transported to
the three-class event counted in `MatchingCounts`.
-/

namespace Crown.ExceptionalCounts

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

open Crown.Matchings Crown.MatchingCounts
open scoped BigOperators Classical

variable (X Y Z : Type*)

abbrev yVertex (y : Y) : ClassVertices X Y Z := Sum.inr (Sum.inl y)

def deleteYEquiv (a b : Y) :
    ClassVertices X (ResidualVertices a b) Z ≃
      ResidualVertices (yVertex X Y Z a) (yVertex X Y Z b) where
  toFun v := match v with
    | Sum.inl x => ⟨Sum.inl x, by simp [yVertex]⟩
    | Sum.inr (Sum.inl y) => ⟨yVertex X Y Z y.val, by
        constructor
        · intro h; exact y.property.1 (Sum.inl_injective (Sum.inr_injective h))
        · intro h; exact y.property.2 (Sum.inl_injective (Sum.inr_injective h))⟩
    | Sum.inr (Sum.inr z) => ⟨Sum.inr (Sum.inr z), by simp [yVertex]⟩
  invFun v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl x => exact Sum.inl x
    | inr v => cases v with
      | inl y => exact Sum.inr (Sum.inl ⟨y,by
          constructor
          · intro h; exact hv.1 (congrArg (yVertex X Y Z) h)
          · intro h; exact hv.2 (congrArg (yVertex X Y Z) h)⟩)
      | inr z => exact Sum.inr (Sum.inr z)
  left_inv v := by
    cases v with
    | inl x => rfl
    | inr v => cases v <;> rfl
  right_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl x => rfl
    | inr v => cases v <;> rfl

theorem crossDirection_deleteY (a b : Y)
    (v w : ClassVertices X (ResidualVertices a b) Z) :
    CrossDirection X Y Z (deleteYEquiv X Y Z a b v).val (deleteYEquiv X Y Z a b w).val ↔
      CrossDirection X (ResidualVertices a b) Z v w := by
  cases v with
  | inl x => cases w with
    | inl x' => rfl
    | inr w => cases w <;> rfl
  | inr v => cases v <;> cases w with
    | inl x' => rfl
    | inr w => cases w <;> rfl

noncomputable def residualYEventEquiv [Fintype X] [Fintype Y] [Fintype Z] (a b : Y) :
    {p : PairingOn (ClassVertices X (ResidualVertices a b) Z) //
      DirectedCrossEvent X (ResidualVertices a b) Z p} ≃
    {q : PairingOn (ResidualVertices (yVertex X Y Z a) (yVertex X Y Z b)) //
      Respects q (fun v w => CrossDirection X Y Z v.val w.val)} :=
  Equiv.subtypeEquiv (relabel (deleteYEquiv X Y Z a b)) (by
    intro p
    have h := respects_relabel (deleteYEquiv X Y Z a b) p
      (fun v w => CrossDirection X Y Z v.val w.val)
    rw [directedCrossEvent_respects]
    simp only [Respects,crossDirection_deleteY] at h
    exact h.symm)

/-- Each specified directed YY pair contributes the residual M count.
The subtraction in the final M argument is integer subtraction. -/
theorem card_YY_exception [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*(k+1))
    (a b : Y) (hab : a ≠ b) :
    Nat.card {p : PairingOn (ClassVertices X Y Z) //
      ExceptPairEvent p (yVertex X Y Z a) (yVertex X Y Z b) (CrossDirection X Y Z)} =
      Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-2) (Fintype.card Z : ℤ) := by
  have hab' : yVertex X Y Z a ≠ yVertex X Y Z b := by
    intro h; exact hab (Sum.inl_injective (Sum.inr_injective h))
  have hres := card_residualVertices a b hab
  have hsum' : Fintype.card X + Fintype.card (ResidualVertices a b) + Fintype.card Z = 2*k := by omega
  rw [natCard_exceptPairEvent _ _ hab', ← Nat.card_congr (residualYEventEquiv X Y Z a b)]
  rw [natCard_directedCrossEvent_finite k hsum']
  congr 1
  omega

def yyPairEmbedding : Y × Y ↪ ClassVertices X Y Z × ClassVertices X Y Z where
  toFun q := (yVertex X Y Z q.1,yVertex X Y Z q.2)
  inj' := by
    intro q r h
    apply Prod.ext
    · exact Sum.inl_injective (Sum.inr_injective (congrArg Prod.fst h))
    · exact Sum.inl_injective (Sum.inr_injective (congrArg Prod.snd h))

noncomputable def yyPairs [Fintype Y] : Finset (ClassVertices X Y Z × ClassVertices X Y Z) :=
  (Finset.univ.filter (fun q : Y × Y => q.1 ≠ q.2)).map (yyPairEmbedding X Y Z)

theorem yyPairs_not_ordinary [Fintype Y] :
    ∀ e ∈ yyPairs X Y Z, ¬ CrossDirection X Y Z e.1 e.2 := by
  intro e he
  obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_map.mp he
  exact id

theorem card_orderedDistinct [Fintype Y] :
    Fintype.card {q : Y × Y // q.1 ≠ q.2} = Fintype.card Y * (Fintype.card Y-1) := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : Y => a ≠ b)),
    Fintype.card_sigma]
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq', Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem card_yyPairs [Fintype Y] : (yyPairs X Y Z).card =
    Fintype.card Y * (Fintype.card Y-1) := by
  rw [yyPairs, Finset.card_map, ← Fintype.card_subtype, card_orderedDistinct]

theorem card_one_YY [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*(k+1)) :
    Nat.card {p : PairingOn (ClassVertices X Y Z) //
      OneExceptional p (CrossDirection X Y Z) (yyPairs X Y Z)} =
      Fintype.card Y * (Fintype.card Y-1) *
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-2) (Fintype.card Z : ℤ) := by
  rw [natCard_oneExceptional _ _ (yyPairs_not_ordinary X Y Z)]
  have hterm (e : {e // e ∈ yyPairs X Y Z}) :
      Nat.card {p : PairingOn (ClassVertices X Y Z) //
        ExceptPairEvent p e.val.1 e.val.2 (CrossDirection X Y Z)} =
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-2) (Fintype.card Z : ℤ) := by
    rcases e with ⟨e,he⟩
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_map.mp he
    exact card_YY_exception X Y Z k hsum a b (Finset.mem_filter.mp hab).2
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, card_yyPairs, Nat.cast_id]

theorem card_ordinary_or_YY [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*(k+1)) :
    Nat.card {p : PairingOn (ClassVertices X Y Z) //
      Respects p (CrossDirection X Y Z) ∨ OneExceptional p (CrossDirection X Y Z) (yyPairs X Y Z)} =
      Arithmetic.M ((k+1 : ℕ) : ℤ) (Fintype.card X : ℤ) (Fintype.card Y : ℤ) (Fintype.card Z : ℤ) +
      Fintype.card Y * (Fintype.card Y-1) *
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-2) (Fintype.card Z : ℤ) := by
  rw [Nat.card_congr (subtypeOrEquiv _ _ (show Disjoint (fun p : PairingOn (ClassVertices X Y Z) => Respects p (CrossDirection X Y Z))
      (fun p => OneExceptional p (CrossDirection X Y Z) (yyPairs X Y Z)) from by
    intro q hR hE p hp
    obtain ⟨e,he⟩ := hE p hp
    exact yyPairs_not_ordinary X Y Z e.val e.property (hR p hp e.val.1 e.val.2 he.1))), Nat.card_sum]
  · rw [card_one_YY X Y Z k hsum]
    congr 1
    let e : {p : PairingOn (ClassVertices X Y Z) // Respects p (CrossDirection X Y Z)} ≃
        {p : PairingOn (ClassVertices X Y Z) // DirectedCrossEvent X Y Z p} :=
      Equiv.subtypeEquivProp (by funext p; exact propext (directedCrossEvent_respects p).symm)
    rw [Nat.card_congr e, natCard_directedCrossEvent_finite (k+1) hsum]

def deleteOneYEquiv (a : Y) :
    ClassVertices X {y : Y // y ≠ a} Z ≃ {v : ClassVertices X Y Z // v ≠ yVertex X Y Z a} :=
  let ey : {y : Y // y ≠ a} ≃ ResidualVertices a a :=
    Equiv.subtypeEquivProp (by funext y; exact (and_self _).symm)
  let ev : ResidualVertices (yVertex X Y Z a) (yVertex X Y Z a) ≃
      {v : ClassVertices X Y Z // v ≠ yVertex X Y Z a} :=
    Equiv.subtypeEquivProp (by funext v; exact (and_self _))
  (classRelabel (Equiv.refl X) ey (Equiv.refl Z)).trans ((deleteYEquiv X Y Z a a).trans ev)

def deleteNoneEquiv {V : Type*} (a : V) :
    {v : V // v ≠ a} ≃ ResidualVertices (none : Option V) (some a) where
  toFun v := ⟨some v.val, by simp [v.property]⟩
  invFun v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | none => exact False.elim (hv.1 rfl)
    | some v => exact ⟨v,fun h => hv.2 (congrArg some h)⟩
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | none => exact False.elim (hv.1 rfl)
    | some v => rfl

def deleteTYEquiv (a : Y) :
    ClassVertices X {y : Y // y ≠ a} Z ≃
      ResidualVertices (none : Option (ClassVertices X Y Z)) (some (yVertex X Y Z a)) :=
  (deleteOneYEquiv X Y Z a).trans (deleteNoneEquiv (yVertex X Y Z a))

def TDirection : Option (ClassVertices X Y Z) → Option (ClassVertices X Y Z) → Prop
  | some a, some b => CrossDirection X Y Z a b
  | _, _ => False

theorem crossDirection_deleteTY (a : Y)
    (v w : ClassVertices X {y : Y // y ≠ a} Z) :
    TDirection X Y Z (deleteTYEquiv X Y Z a v).val (deleteTYEquiv X Y Z a w).val ↔
      CrossDirection X {y : Y // y ≠ a} Z v w := by
  cases v with
  | inl x => cases w with
    | inl x' => rfl
    | inr w => cases w <;> rfl
  | inr v => cases v <;> cases w with
    | inl x' => rfl
    | inr w => cases w <;> rfl

noncomputable def residualTYEventEquiv [Fintype X] [Fintype Y] [Fintype Z] (a : Y) :
    {p : PairingOn (ClassVertices X {y : Y // y ≠ a} Z) //
      DirectedCrossEvent X {y : Y // y ≠ a} Z p} ≃
    {q : PairingOn (ResidualVertices (none : Option (ClassVertices X Y Z)) (some (yVertex X Y Z a))) //
      Respects q (fun v w => TDirection X Y Z v.val w.val)} :=
  Equiv.subtypeEquiv (relabel (deleteTYEquiv X Y Z a)) (by
    intro p
    have h := respects_relabel (deleteTYEquiv X Y Z a) p
      (fun v w => TDirection X Y Z v.val w.val)
    rw [directedCrossEvent_respects]
    simp only [Respects,crossDirection_deleteTY] at h
    exact h.symm)

theorem card_TY_exception [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z + 1 = 2*(k+1)) (a : Y) :
    Nat.card {p : PairingOn (Option (ClassVertices X Y Z)) //
      ExceptPairEvent p none (some (yVertex X Y Z a)) (TDirection X Y Z)} =
      Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-1) (Fintype.card Z : ℤ) := by
  have hres : Fintype.card {y : Y // y ≠ a} + 1 = Fintype.card Y := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have hpos := Fintype.card_pos_iff.mpr (Nonempty.intro a)
    omega
  have hsum' : Fintype.card X + Fintype.card {y : Y // y ≠ a} + Fintype.card Z = 2*k := by omega
  rw [natCard_exceptPairEvent _ _ (by simp), ← Nat.card_congr (residualTYEventEquiv X Y Z a)]
  rw [natCard_directedCrossEvent_finite k hsum']
  congr 1
  omega

theorem card_YT_exception [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z + 1 = 2*(k+1)) (a : Y) :
    Nat.card {p : PairingOn (Option (ClassVertices X Y Z)) //
      ExceptPairEvent p (some (yVertex X Y Z a)) none (TDirection X Y Z)} =
      Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-1) (Fintype.card Z : ℤ) := by
  rw [← natCard_exceptPair_reverse none (some (yVertex X Y Z a)) (by simp)]
  exact card_TY_exception X Y Z k hsum a

def tyPairEmbedding : Bool × Y ↪ Option (ClassVertices X Y Z) × Option (ClassVertices X Y Z) where
  toFun q := if q.1 then (some (yVertex X Y Z q.2),none) else (none,some (yVertex X Y Z q.2))
  inj' := by
    rintro ⟨s,a⟩ ⟨t,b⟩ h
    cases s <;> cases t <;> simp_all [yVertex]

noncomputable def tyPairs [Fintype Y] : Finset (Option (ClassVertices X Y Z) × Option (ClassVertices X Y Z)) :=
  Finset.univ.map (tyPairEmbedding X Y Z)

theorem tyPairs_not_ordinary [Fintype Y] :
    ∀ e ∈ tyPairs X Y Z, ¬ TDirection X Y Z e.1 e.2 := by
  intro e he
  obtain ⟨⟨s,a⟩,_,rfl⟩ := Finset.mem_map.mp he
  cases s <;> exact id

theorem card_tyPairs [Fintype Y] : (tyPairs X Y Z).card = 2 * Fintype.card Y := by
  simp [tyPairs,Fintype.card_prod]

theorem card_one_TY_or_YT [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z + 1 = 2*(k+1)) :
    Nat.card {p : PairingOn (Option (ClassVertices X Y Z)) //
      OneExceptional p (TDirection X Y Z) (tyPairs X Y Z)} =
      2 * Fintype.card Y *
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-1) (Fintype.card Z : ℤ) := by
  rw [natCard_oneExceptional _ _ (tyPairs_not_ordinary X Y Z)]
  have hterm (e : {e // e ∈ tyPairs X Y Z}) :
      Nat.card {p : PairingOn (Option (ClassVertices X Y Z)) //
        ExceptPairEvent p e.val.1 e.val.2 (TDirection X Y Z)} =
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-1) (Fintype.card Z : ℤ) := by
    rcases e with ⟨e,he⟩
    obtain ⟨⟨s,a⟩,_,rfl⟩ := Finset.mem_map.mp he
    cases s with
    | false => exact card_TY_exception X Y Z k hsum a
    | true => exact card_YT_exception X Y Z k hsum a
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, card_tyPairs, Nat.cast_id]

#print axioms card_one_TY_or_YT
#print axioms card_TY_exception
#print axioms card_YT_exception
#print axioms card_ordinary_or_YY
#print axioms card_YY_exception

end Crown.ExceptionalCounts
