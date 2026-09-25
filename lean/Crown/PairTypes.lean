import Crown.Orientations

/-!
# The six directed pair types in the comparison count

The four colours describe incidence to the smaller and larger rows, in that
order. Endpoint pairs are ordered. Prescribed ranks use the rank convention
of `Crown.Ranks`, and an unprescribed entry is completed by zero.
-/
namespace Crown.PairTypes
open Crown.Ranks Crown.Orientations

inductive Colour where
  | X | Y | Z | T
  deriving DecidableEq

open Colour

instance : Fintype Colour where
  elems := {X, Y, Z, T}
  complete := by intro a; cases a <;> simp

def bits : Colour → Bool × Bool
  | X => (true, false)
  | Y => (false, true)
  | Z => (true, true)
  | T => (false, false)

def colourOfBits : Bool × Bool → Colour
  | (true, false) => X
  | (false, true) => Y
  | (true, true) => Z
  | (false, false) => T

theorem bits_colourOfBits : ∀ b : Bool × Bool, bits (colourOfBits b) = b := by
  decide +kernel

theorem colourOfBits_bits : ∀ a : Colour, colourOfBits (bits a) = a := by
  decide +kernel

def colourEquiv : Colour ≃ Bool × Bool where
  toFun := bits
  invFun := colourOfBits
  left_inv := colourOfBits_bits
  right_inv := bits_colourOfBits

def smallerEntry (a b : Colour) : Option (Fin 3) :=
  entry ((bits a).1, (bits b).1) false

def largerEntry (a b : Colour) : Option (Fin 3) :=
  entry ((bits a).2, (bits b).2) false

def Ordinary (a b : Colour) : Prop :=
  (a = X ∧ b = Y) ∨ (a = X ∧ b = Z) ∨ (a = Z ∧ b = Y)

def Exceptional (a b : Colour) : Prop :=
  (a = Y ∧ b = Y) ∨ (a = T ∧ b = Y) ∨ (a = Y ∧ b = T)

def Allowed (a b : Colour) : Prop := Ordinary a b ∨ Exceptional a b

instance (a b : Colour) : Decidable (Ordinary a b) := by unfold Ordinary; infer_instance
instance (a b : Colour) : Decidable (Exceptional a b) := by unfold Exceptional; infer_instance
instance (a b : Colour) : Decidable (Allowed a b) := by unfold Allowed; infer_instance

/-- Precisely XY, XZ, ZY, YY, TY and YT give a strict directed comparison. -/
theorem local_strict_iff : ∀ a b : Colour,
    completeEntry (smallerEntry a b) false < completeEntry (largerEntry a b) false ↔
      Allowed a b := by decide +kernel

theorem local_exceptional_iff : ∀ a b : Colour, Allowed a b →
    (smallerEntry a b = none ↔ Exceptional a b) := by decide +kernel

theorem local_larger_fixed : ∀ a b : Colour, Allowed a b → largerEntry a b ≠ none := by
  decide +kernel

theorem local_fixed_iff : ∀ a b : Colour,
    (smallerEntry a b ≠ none ∧ largerEntry a b ≠ none ∧
      completeEntry (smallerEntry a b) false < completeEntry (largerEntry a b) false) ↔
      Ordinary a b := by decide +kernel

theorem ordinary_no_T : ∀ a b : Colour, Ordinary a b → a ≠ T ∧ b ≠ T := by
  decide +kernel

theorem allowed_T_exceptional : ∀ a b : Colour,
    Allowed a b → (a = T ∨ b = T) → Exceptional a b := by decide +kernel

theorem allowed_not_TT : ∀ a b : Colour, Allowed a b → ¬ (a = T ∧ b = T) := by
  decide +kernel

def smaller {I : Type*} (p : I → Colour × Colour) : NeighbourRow I :=
  fun i => ((bits (p i).1).1, (bits (p i).2).1)

def larger {I : Type*} (p : I → Colour × Colour) : NeighbourRow I :=
  fun i => ((bits (p i).1).2, (bits (p i).2).2)

def AtMostOneExceptional {I : Type*} (p : I → Colour × Colour) : Prop :=
  ∀ i j, Exceptional (p i).1 (p i).2 → Exceptional (p j).1 (p j).2 → i = j

theorem strict_iff_allowed {I : Type*} (p : I → Colour × Colour) :
    StrictBelow (zeroRow (smaller p) (fun _ => false))
      (zeroRow (larger p) (fun _ => false)) ↔ ∀ i, Allowed (p i).1 (p i).2 := by
  exact forall_congr' (fun i => local_strict_iff (p i).1 (p i).2)

theorem exceptional_iff_zero_bits : ∀ a b : Colour, Allowed a b →
    (Exceptional a b ↔ ((bits a).1, (bits b).1) = (false, false)) := by
  decide +kernel

/-- Multiple unprescribed entries are excluded explicitly, as in the counting rule. -/
theorem global_directed_iff {I : Type*} (p : I → Colour × Colour) :
    (¬ DoubleStar (smaller p) ∧ ¬ DoubleStar (larger p) ∧
      StrictBelow (zeroRow (smaller p) (fun _ => false))
        (zeroRow (larger p) (fun _ => false))) ↔
      ((∀ i, Allowed (p i).1 (p i).2) ∧ AtMostOneExceptional p) := by
  constructor
  · rintro ⟨hN, _, hs⟩
    have ha := (strict_iff_allowed p).mp hs
    refine ⟨ha, ?_⟩
    intro i j hi hj
    by_contra hij
    exact hN ⟨i, j, hij,
      (exceptional_iff_zero_bits _ _ (ha i)).mp hi,
      (exceptional_iff_zero_bits _ _ (ha j)).mp hj⟩
  · rintro ⟨ha, huniq⟩
    refine ⟨?_, ?_, (strict_iff_allowed p).mpr ha⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      exact hij (huniq i j ((exceptional_iff_zero_bits _ _ (ha i)).mpr hi)
        ((exceptional_iff_zero_bits _ _ (ha j)).mpr hj))
    · rintro ⟨i, _, _, hi, _⟩
      apply local_larger_fixed (p i).1 (p i).2 (ha i)
      exact (entry_none_iff _ false).mpr hi

/-- The fixed/fixed case consists exactly of the three ordinary types. -/
theorem global_fixed_iff {I : Type*} (p : I → Colour × Colour) :
    (Fixed (row (smaller p) (fun _ => false)) ∧
      Fixed (row (larger p) (fun _ => false)) ∧
      StrictBelow (zeroRow (smaller p) (fun _ => false))
        (zeroRow (larger p) (fun _ => false))) ↔
      ∀ i, Ordinary (p i).1 (p i).2 := by
  constructor
  · rintro ⟨hN, hM, hs⟩ i
    exact (local_fixed_iff _ _).mp ⟨hN i, hM i, hs i⟩
  · intro h
    refine ⟨fun i => ((local_fixed_iff _ _).mpr (h i)).1,
      fun i => ((local_fixed_iff _ _).mpr (h i)).2.1,
      fun i => ((local_fixed_iff _ _).mpr (h i)).2.2⟩

/-- Read the colour of an endpoint in a coordinate presentation. -/
def endpoint {I : Type*} (p : I → Colour × Colour) (v : I × Bool) : Colour :=
  if v.2 then (p v.1).2 else (p v.1).1

theorem T_endpoint_exceptional {I : Type*} (p : I → Colour × Colour)
    (ha : ∀ i, Allowed (p i).1 (p i).2) (v : I × Bool)
    (hv : endpoint p v = T) : Exceptional (p v.1).1 (p v.1).2 := by
  apply allowed_T_exceptional _ _ (ha v.1)
  cases hb : v.2
  · exact Or.inl (by simpa [endpoint, hb] using hv)
  · exact Or.inr (by simpa [endpoint, hb] using hv)

theorem T_endpoint_unique {I : Type*} (p : I → Colour × Colour)
    (ha : ∀ i, Allowed (p i).1 (p i).2) (hu : AtMostOneExceptional p)
    (v w : I × Bool) (hv : endpoint p v = T) (hw : endpoint p w = T) : v = w := by
  have hi : v.1 = w.1 := hu v.1 w.1 (T_endpoint_exceptional p ha v hv)
    (T_endpoint_exceptional p ha w hw)
  rcases v with ⟨i, a⟩
  rcases w with ⟨j, b⟩
  dsimp at hi
  subst j
  congr 1
  cases a <;> cases b <;> simp_all [endpoint]
  all_goals exact False.elim (allowed_not_TT _ _ (ha i) ⟨by assumption, by assumption⟩)

/-- P06: two T vertices are impossible in a comparable pair of retained rows. -/
theorem T_endpoint_card_le_one {k : Nat} (p : Fin k → Colour × Colour)
    (h : ¬ DoubleStar (smaller p) ∧ ¬ DoubleStar (larger p) ∧
      StrictBelow (zeroRow (smaller p) (fun _ => false))
        (zeroRow (larger p) (fun _ => false))) :
    (Finset.univ.filter (fun v : Fin k × Bool => endpoint p v = T)).card ≤ 1 := by
  obtain ⟨ha, hu⟩ := (global_directed_iff p).mp h
  apply Finset.card_le_one.mpr
  intro v hv w hw
  exact T_endpoint_unique p ha hu v w (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2

#print axioms local_strict_iff
#print axioms global_directed_iff
#print axioms global_fixed_iff
#print axioms T_endpoint_card_le_one
end Crown.PairTypes
