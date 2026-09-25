import Crown.ExceptionalCounts
import Crown.PairTypes

/-! The comparison event on the full oriented-unordered pairing space.
Colours are arbitrary incidence labels. The predicates below refer to
actual directed pairs; their equivalence with rank comparisons is separate
from the cardinality calculation. -/

namespace Crown.MatchingProbabilities

open Crown.Matchings Crown.MatchingCounts Crown.ExceptionalCounts Crown.PairTypes
open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V]

theorem directedPair_ne (p : PairingOn V) (a b : V) (h : DirectedPair p a b) : a ≠ b :=
  fun he => h.2.1 (he ▸ h.1)

theorem vertex_incident (p : PairingOn V) (v : V) :
    ∃ a b, DirectedPair p a b ∧ (v = a ∨ v = b) := by
  by_cases hv : v ∈ p.1
  · let b := p.2 ⟨v,hv⟩
    exact ⟨v,b.val,⟨hv,b.property,fun _ _ => rfl⟩,Or.inl rfl⟩
  · let a := p.2.symm ⟨v,hv⟩
    exact ⟨a.val,v,⟨a.property,hv,fun _ _ => p.2.apply_symm_apply ⟨v,hv⟩⟩,Or.inr rfl⟩

theorem ordinary_exceptional_disjoint :
    ∀ a b : Colour, Ordinary a b → ¬ Exceptional a b := by decide +kernel

def Comparison (col : V → Colour) (p : PairingOn V) : Prop :=
  (∀ a b, DirectedPair p a b → Allowed (col a) (col b)) ∧
    ∀ a b c d, DirectedPair p a b → DirectedPair p c d →
      Exceptional (col a) (col b) → Exceptional (col c) (col d) → a = c

def ordinaryRelation (col : V → Colour) : V → V → Prop :=
  fun a b => Ordinary (col a) (col b)

noncomputable def exceptionPairs [Fintype V] (col : V → Colour) : Finset (V × V) :=
  Finset.univ.filter (fun q => q.1 ≠ q.2 ∧ Exceptional (col q.1) (col q.2))

theorem comparison_iff_event [Fintype V] (col : V → Colour) (p : PairingOn V) :
    Comparison col p ↔
      Respects p (ordinaryRelation col) ∨ OneExceptional p (ordinaryRelation col) (exceptionPairs col) := by
  constructor
  · rintro ⟨hall,huniq⟩
    by_cases hex : ∃ a b, DirectedPair p a b ∧ Exceptional (col a) (col b)
    · obtain ⟨a,b,hab,hex⟩ := hex
      right
      refine ⟨⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,directedPair_ne p a b hab,hex⟩⟩,hab,?_⟩
      intro c d hcd
      rcases hall c d hcd with ho | he
      · exact Or.inr ho
      · exact Or.inl (huniq c d a b hcd hab he hex)
    · left
      intro a b hab
      exact (hall a b hab).resolve_right (fun he => hex ⟨a,b,hab,he⟩)
  · rintro (hR | ⟨e,he⟩)
    · refine ⟨fun a b hab => Or.inl (hR a b hab),?_⟩
      intro a b c d hab _ hex _
      exact False.elim (ordinary_exceptional_disjoint _ _ (hR a b hab) hex)
    · have hex := (Finset.mem_filter.mp e.property).2.2
      refine ⟨?_,?_⟩
      · intro a b hab
        rcases he.2 a b hab with ha | ho
        · have hab' : DirectedPair p e.val.1 b := ha ▸ hab
          have hb := directedPair_same_first p e.val.1 b e.val.2 hab' he.1
          exact Or.inr (by simpa [ha,hb] using hex)
        · exact Or.inl ho
      · intro a b c d hab hcd heab hecd
        have ha := (he.2 a b hab).resolve_right (fun ho => ordinary_exceptional_disjoint _ _ ho heab)
        have hc := (he.2 c d hcd).resolve_right (fun ho => ordinary_exceptional_disjoint _ _ ho hecd)
        exact ha.trans hc.symm

theorem comparison_T_unique (col : V → Colour) (p : PairingOn V) (h : Comparison col p)
    (v w : V) (hv : col v = Colour.T) (hw : col w = Colour.T) : v = w := by
  obtain ⟨a,b,hab,hvab⟩ := vertex_incident p v
  obtain ⟨c,d,hcd,hwcd⟩ := vertex_incident p w
  have hea : Exceptional (col a) (col b) := allowed_T_exceptional _ _ (h.1 a b hab) (by
    rcases hvab with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv)
  have hec : Exceptional (col c) (col d) := allowed_T_exceptional _ _ (h.1 c d hcd) (by
    rcases hwcd with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw)
  have hac := h.2 a b c d hab hcd hea hec
  subst c
  have hbd := directedPair_same_first p a b d hab hcd
  subst d
  have hn := allowed_not_TT _ _ (h.1 a b hab)
  rcases hvab with rfl | rfl <;> rcases hwcd with rfl | rfl
  · rfl
  · exact False.elim (hn ⟨hv,hw⟩)
  · exact False.elim (hn ⟨hw,hv⟩)
  · rfl

theorem comparison_T_card_le_one [Fintype V] (col : V → Colour) (p : PairingOn V)
    (h : Comparison col p) : (Finset.univ.filter (fun v => col v = Colour.T)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  exact comparison_T_unique col p h v w (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2

theorem comparison_relabel {W : Type*} [DecidableEq W] (e : V ≃ W)
    (col : W → Colour) (p : PairingOn V) :
    Comparison col (relabel e p) ↔ Comparison (fun v => col (e v)) p := by
  constructor
  · rintro ⟨hall,huniq⟩
    refine ⟨fun a b hab => hall (e a) (e b) ((directedPair_relabel e p a b).mpr hab),?_⟩
    intro a b c d hab hcd heab hecd
    apply e.injective
    exact huniq (e a) (e b) (e c) (e d) ((directedPair_relabel e p a b).mpr hab)
      ((directedPair_relabel e p c d).mpr hcd) heab hecd
  · rintro ⟨hall,huniq⟩
    constructor
    · intro a b hab
      obtain ⟨a,rfl⟩ := e.surjective a
      obtain ⟨b,rfl⟩ := e.surjective b
      exact hall a b ((directedPair_relabel e p a b).mp hab)
    · intro a b c d hab hcd heab hecd
      obtain ⟨a,rfl⟩ := e.surjective a
      obtain ⟨b,rfl⟩ := e.surjective b
      obtain ⟨c,rfl⟩ := e.surjective c
      obtain ⟨d,rfl⟩ := e.surjective d
      exact congrArg e (huniq a b c d ((directedPair_relabel e p a b).mp hab)
        ((directedPair_relabel e p c d).mp hcd) heab hecd)

section TaggedClasses

variable (X Y Z : Type*)

def classColour : ClassVertices X Y Z → Colour
  | Sum.inl _ => Colour.X
  | Sum.inr (Sum.inl _) => Colour.Y
  | Sum.inr (Sum.inr _) => Colour.Z

def optionColour : Option (ClassVertices X Y Z) → Colour
  | none => Colour.T
  | some v => classColour X Y Z v

theorem ordinary_classColour (v w : ClassVertices X Y Z) :
    Ordinary (classColour X Y Z v) (classColour X Y Z w) ↔ CrossDirection X Y Z v w := by
  rcases v with x | y | z <;> rcases w with x' | y' | z' <;>
    simp [classColour,Ordinary,CrossDirection]

theorem ordinaryRelation_classColour : ordinaryRelation (classColour X Y Z) = CrossDirection X Y Z := by
  funext v w
  exact propext (ordinary_classColour X Y Z v w)

theorem exceptionPairs_classColour [Fintype X] [Fintype Y] [Fintype Z] :
    exceptionPairs (classColour X Y Z) = yyPairs X Y Z := by
  ext q
  rcases q with ⟨v,w⟩
  simp only [exceptionPairs,Finset.mem_filter,Finset.mem_univ,true_and,
    yyPairs,Finset.mem_map]
  rcases v with x | y | z <;> rcases w with x' | y' | z' <;>
    simp [yyPairEmbedding,classColour,Exceptional,yVertex,Function.Embedding.coeFn_mk]

theorem comparison_classColour [Fintype X] [Fintype Y] [Fintype Z]
    (p : PairingOn (ClassVertices X Y Z)) :
    Comparison (classColour X Y Z) p ↔
      Respects p (CrossDirection X Y Z) ∨ OneExceptional p (CrossDirection X Y Z) (yyPairs X Y Z) := by
  rw [comparison_iff_event,ordinaryRelation_classColour,exceptionPairs_classColour]

theorem card_comparison_classColour [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z = 2*(k+1)) :
    Nat.card {p : PairingOn (ClassVertices X Y Z) // Comparison (classColour X Y Z) p} =
      Arithmetic.M ((k+1 : ℕ) : ℤ) (Fintype.card X : ℤ) (Fintype.card Y : ℤ) (Fintype.card Z : ℤ) +
      Fintype.card Y * (Fintype.card Y-1) *
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-2) (Fintype.card Z : ℤ) := by
  let e := Equiv.subtypeEquivProp (show
      (fun p : PairingOn (ClassVertices X Y Z) => Comparison (classColour X Y Z) p) =
      (fun p => Respects p (CrossDirection X Y Z) ∨ OneExceptional p (CrossDirection X Y Z) (yyPairs X Y Z)) from by
    funext p
    exact propext (comparison_classColour X Y Z p))
  rw [Nat.card_congr e,card_ordinary_or_YY X Y Z k hsum]

theorem ordinaryRelation_optionColour :
    ordinaryRelation (optionColour X Y Z) = TDirection X Y Z := by
  funext v w
  apply propext
  cases v with
  | none => cases w <;> simp [ordinaryRelation,optionColour,Ordinary,TDirection]
  | some v => cases w with
    | none => simp [ordinaryRelation,optionColour,Ordinary,TDirection]
    | some w => exact ordinary_classColour X Y Z v w

theorem allowed_none_left (v : Option (ClassVertices X Y Z)) :
    Allowed Colour.T (optionColour X Y Z v) ↔ ∃ y, v = some (yVertex X Y Z y) := by
  cases v with
  | none => simp [optionColour,Allowed,Ordinary,Exceptional]
  | some v => rcases v with x | y | z <;>
      simp [optionColour,classColour,Allowed,Ordinary,Exceptional,yVertex]

theorem allowed_none_right (v : Option (ClassVertices X Y Z)) :
    Allowed (optionColour X Y Z v) Colour.T ↔ ∃ y, v = some (yVertex X Y Z y) := by
  cases v with
  | none => simp [optionColour,Allowed,Ordinary,Exceptional]
  | some v => rcases v with x | y | z <;>
      simp [optionColour,classColour,Allowed,Ordinary,Exceptional,yVertex]

theorem mem_tyPairs_iff [Fintype Y] (a b : Option (ClassVertices X Y Z)) :
    (a,b) ∈ tyPairs X Y Z ↔
      (∃ y, a = none ∧ b = some (yVertex X Y Z y)) ∨
      (∃ y, a = some (yVertex X Y Z y) ∧ b = none) := by
  constructor
  · intro h
    obtain ⟨⟨s,y⟩,_,he⟩ := Finset.mem_map.mp h
    cases s
    · exact Or.inl ⟨y,(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩
    · exact Or.inr ⟨y,(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩
  · rintro (⟨y,rfl,rfl⟩ | ⟨y,rfl,rfl⟩)
    · exact Finset.mem_map.mpr ⟨(false,y),Finset.mem_univ _,rfl⟩
    · exact Finset.mem_map.mpr ⟨(true,y),Finset.mem_univ _,rfl⟩

theorem comparison_optionColour [Fintype X] [Fintype Y] [Fintype Z]
    (p : PairingOn (Option (ClassVertices X Y Z))) :
    Comparison (optionColour X Y Z) p ↔
      OneExceptional p (TDirection X Y Z) (tyPairs X Y Z) := by
  constructor
  · intro h
    obtain ⟨a,b,hab,ht⟩ := vertex_incident p none
    have he : (a,b) ∈ tyPairs X Y Z := by
      apply (mem_tyPairs_iff X Y Z a b).mpr
      rcases ht with ht | ht
      · subst a
        obtain ⟨y,rfl⟩ := (allowed_none_left X Y Z b).mp (h.1 none b hab)
        exact Or.inl ⟨y,rfl,rfl⟩
      · subst b
        obtain ⟨y,rfl⟩ := (allowed_none_right X Y Z a).mp (h.1 a none hab)
        exact Or.inr ⟨y,rfl,rfl⟩
    have hex : Exceptional (optionColour X Y Z a) (optionColour X Y Z b) :=
      allowed_T_exceptional _ _ (h.1 a b hab) (by
        rcases ht with ht | ht
        · exact Or.inl (by rw [← ht]; rfl)
        · exact Or.inr (by rw [← ht]; rfl))
    refine ⟨⟨(a,b),he⟩,hab,?_⟩
    intro c d hcd
    rcases h.1 c d hcd with ho | he'
    · right
      exact Eq.mp (congrFun (congrFun (ordinaryRelation_optionColour X Y Z) c) d) ho
    · exact Or.inl (h.2 c d a b hcd hab he' hex)
  · rintro ⟨e,he⟩
    apply (comparison_iff_event (optionColour X Y Z) p).mpr
    right
    have hem : e.val ∈ exceptionPairs (optionColour X Y Z) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,directedPair_ne p _ _ he.1,?_⟩
      rcases (mem_tyPairs_iff X Y Z e.val.1 e.val.2).mp e.property with
        ⟨y,ha,hb⟩ | ⟨y,ha,hb⟩ <;>
        simp [ha,hb,optionColour,classColour,yVertex,Exceptional]
    refine ⟨⟨e.val,hem⟩,he.1,?_⟩
    intro a b hab
    rcases he.2 a b hab with ha | ho
    · exact Or.inl ha
    · right
      exact Eq.mp (congrFun (congrFun (ordinaryRelation_optionColour X Y Z).symm a) b) ho

theorem card_comparison_optionColour [Fintype X] [Fintype Y] [Fintype Z]
    (k : ℕ) (hsum : Fintype.card X + Fintype.card Y + Fintype.card Z + 1 = 2*(k+1)) :
    Nat.card {p : PairingOn (Option (ClassVertices X Y Z)) // Comparison (optionColour X Y Z) p} =
      2 * Fintype.card Y *
        Arithmetic.M (k : ℤ) (Fintype.card X : ℤ) ((Fintype.card Y : ℤ)-1) (Fintype.card Z : ℤ) := by
  let e := Equiv.subtypeEquivProp (show
      (fun p : PairingOn (Option (ClassVertices X Y Z)) => Comparison (optionColour X Y Z) p) =
      (fun p => OneExceptional p (TDirection X Y Z) (tyPairs X Y Z)) from by
    funext p
    exact propext (comparison_optionColour X Y Z p))
  rw [Nat.card_congr e,card_one_TY_or_YT X Y Z k hsum]

end TaggedClasses

abbrev ColourClass (col : V → Colour) (c : Colour) := {v : V // col v = c}

noncomputable def noTEquiv (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T) :
    ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z) ≃ V where
  toFun
    | Sum.inl v => v.val
    | Sum.inr (Sum.inl v) => v.val
    | Sum.inr (Sum.inr v) => v.val
  invFun v := if hx : col v = Colour.X then Sum.inl ⟨v,hx⟩
    else if hy : col v = Colour.Y then Sum.inr (Sum.inl ⟨v,hy⟩)
    else Sum.inr (Sum.inr ⟨v,by cases h : col v <;> simp_all⟩)
  left_inv v := by
    rcases v with x | y | z
    · simp [x.property]
    · simp [y.property]
    · simp [z.property]
  right_inv v := by dsimp; split_ifs <;> rfl

theorem noTEquiv_colour (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T)
    (v : ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z)) :
    col (noTEquiv col ht v) =
      classColour (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z) v := by
  rcases v with x | y | z
  · exact x.property
  · exact y.property
  · exact z.property

noncomputable def oneTEquiv (col : V → Colour) (t : V) (ht : col t = Colour.T)
    (hunique : ∀ v, col v = Colour.T → v = t) :
    Option (ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z)) ≃ V where
  toFun
    | none => t
    | some (Sum.inl v) => v.val
    | some (Sum.inr (Sum.inl v)) => v.val
    | some (Sum.inr (Sum.inr v)) => v.val
  invFun v := if hx : col v = Colour.X then some (Sum.inl ⟨v,hx⟩)
    else if hy : col v = Colour.Y then some (Sum.inr (Sum.inl ⟨v,hy⟩))
    else if hz : col v = Colour.Z then some (Sum.inr (Sum.inr ⟨v,hz⟩))
    else none
  left_inv v := by
    cases v with
    | none => simp [ht]
    | some v =>
        rcases v with x | y | z
        · simp [x.property]
        · simp [y.property]
        · simp [z.property]
  right_inv v := by
    dsimp
    split_ifs with hx hy hz
    · rfl
    · rfl
    · rfl
    · apply (hunique v _).symm
      cases h : col v <;> simp_all

theorem oneTEquiv_colour (col : V → Colour) (t : V) (ht : col t = Colour.T)
    (hunique : ∀ v, col v = Colour.T → v = t)
    (v : Option (ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z))) :
    col (oneTEquiv col t ht hunique v) =
      optionColour (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z) v := by
  cases v with
  | none => exact ht
  | some v =>
      rcases v with x | y | z
      · exact x.property
      · exact y.property
      · exact z.property

noncomputable def comparisonNoTEquiv [Fintype V] (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T) :
    {p : PairingOn (ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z)) //
      Comparison (classColour (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z)) p} ≃
    {p : PairingOn V // Comparison col p} :=
  Equiv.subtypeEquiv (relabel (noTEquiv col ht)) (by
    intro p
    have h := comparison_relabel (noTEquiv col ht) col p
    simp only [noTEquiv_colour] at h
    exact h.symm)

noncomputable def comparisonOneTEquiv [Fintype V] (col : V → Colour) (t : V) (ht : col t = Colour.T)
    (hunique : ∀ v, col v = Colour.T → v = t) :
    {p : PairingOn (Option (ClassVertices (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z))) //
      Comparison (optionColour (ColourClass col Colour.X) (ColourClass col Colour.Y) (ColourClass col Colour.Z)) p} ≃
    {p : PairingOn V // Comparison col p} :=
  Equiv.subtypeEquiv (relabel (oneTEquiv col t ht hunique)) (by
    intro p
    have h := comparison_relabel (oneTEquiv col t ht hunique) col p
    simp only [oneTEquiv_colour] at h
    exact h.symm)

theorem card_comparison_noT [Fintype V] (col : V → Colour) (ht : ∀ v, col v ≠ Colour.T)
    (k : ℕ) (hcard : Fintype.card V = 2*(k+1)) :
    Nat.card {p : PairingOn V // Comparison col p} =
      Arithmetic.M ((k+1 : ℕ) : ℤ) (Fintype.card (ColourClass col Colour.X) : ℤ)
        (Fintype.card (ColourClass col Colour.Y) : ℤ) (Fintype.card (ColourClass col Colour.Z) : ℤ) +
      Fintype.card (ColourClass col Colour.Y) * (Fintype.card (ColourClass col Colour.Y)-1) *
        Arithmetic.M (k : ℤ) (Fintype.card (ColourClass col Colour.X) : ℤ)
          ((Fintype.card (ColourClass col Colour.Y) : ℤ)-2) (Fintype.card (ColourClass col Colour.Z) : ℤ) := by
  have hsum := (Fintype.card_congr (noTEquiv col ht)).trans hcard
  simp only [ClassVertices,Fintype.card_sum] at hsum
  rw [← Nat.card_congr (comparisonNoTEquiv col ht)]
  exact card_comparison_classColour _ _ _ k (by omega)

theorem card_comparison_oneT [Fintype V] (col : V → Colour) (t : V) (ht : col t = Colour.T)
    (hunique : ∀ v, col v = Colour.T → v = t)
    (k : ℕ) (hcard : Fintype.card V = 2*(k+1)) :
    Nat.card {p : PairingOn V // Comparison col p} =
      2 * Fintype.card (ColourClass col Colour.Y) *
        Arithmetic.M (k : ℤ) (Fintype.card (ColourClass col Colour.X) : ℤ)
          ((Fintype.card (ColourClass col Colour.Y) : ℤ)-1) (Fintype.card (ColourClass col Colour.Z) : ℤ) := by
  have hsum := (Fintype.card_congr (oneTEquiv col t ht hunique)).trans hcard
  simp only [ClassVertices,Fintype.card_sum,Fintype.card_option] at hsum
  rw [← Nat.card_congr (comparisonOneTEquiv col t ht hunique)]
  exact card_comparison_optionColour _ _ _ k (by omega)

theorem card_comparison_multipleT [Fintype V] (col : V → Colour)
    (v w : V) (hv : col v = Colour.T) (hw : col w = Colour.T) (hne : v ≠ w) :
    Nat.card {p : PairingOn V // Comparison col p} = 0 := by
  have : IsEmpty {p : PairingOn V // Comparison col p} :=
    ⟨fun p => hne (comparison_T_unique col p.val p.property v w hv hw)⟩
  exact Nat.card_of_isEmpty

#print axioms card_comparison_classColour
#print axioms card_comparison_optionColour
#print axioms comparison_iff_event
#print axioms comparison_T_card_le_one
#print axioms card_comparison_noT
#print axioms card_comparison_oneT
#print axioms card_comparison_multipleT

end Crown.MatchingProbabilities
