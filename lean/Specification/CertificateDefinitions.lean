import Specification.ThreeRankCoding
import Specification.RankDefinitions
import Crown.Definitions
import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sort
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.Dedup

/-! Independently reviewable Challenge-only definitions. Literal definitions
are copied from the development sources identified in the provenance file.
No solution-side theorem module is imported. These definitions must never be
imported alongside their solution-side names in one Lean environment. -/
open scoped Classical

namespace Crown.CertificateSemantics

open Crown.Ranks

def literalValue (a : Nat → Bool) : Sat.Literal → Bool
  | .pos n => a n
  | .neg n => !(a n)

def valuation (a : Nat → Bool) : Sat.Valuation := fun n => a n = true

def counterCNF (z u x w : Sat.Literal) : Sat.Fmla :=
  [[u.negate, z], [x.negate, w.negate, z], [z.negate, u, x], [z.negate, u, w]]

def equalityCNF (z e x y : Sat.Literal) : Sat.Fmla :=
  [[z.negate, e], [z.negate, x.negate, y], [z.negate, x, y.negate],
    [e.negate, x.negate, y.negate, z], [e.negate, x, y, z]]

def prefixCount (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => prefixCount s i + if s i then 1 else 0

def counterValue (s : Nat → Bool) (i j : Nat) : Bool := decide (j ≤ prefixCount s i)

def rankOfBits : Bool → Bool → Option (Fin 3)
  | false, false => none
  | true, false => some 0
  | true, true => some 1
  | false, true => some 2

def bitsOfRank : Option (Fin 3) → Bool × Bool
  | none => (false, false)
  | some u => if u = 0 then (true, false) else if u = 1 then (true, true) else (false, true)

def rowOfMask {I A : Type} (pairs : I → A × A) (mask : A → Bool) : InitialRow I :=
  fun i => rankOfBits (mask (pairs i).1) (mask (pairs i).2)

def maskBits (m : Fin 256) : Fin 8 → Bool := fun i => m.val.testBit i.val

abbrev Pairing8 := (Fin 4 × Bool) ≃ Fin 8

def pairsOfEquiv (p : Pairing8) : Fin 4 → Fin 8 × Fin 8 :=
  fun i => (p (i, false), p (i, true))

def AllPairingsBad {V : Type} (masks : V → Fin 256) : Prop :=
  ∀ p : Pairing8, ¬ Feasible (fun v => rowOfMask (pairsOfEquiv p) (maskBits (masks v)))

def Covers {I A : Type} (pairs : I → A × A) : Prop :=
  ∀ a, ∃ i, a = (pairs i).1 ∨ a = (pairs i).2

def selectorNat (s : Fin 256 → Bool) (n : Nat) : Bool :=
  if h : n < 256 then s ⟨n, h⟩ else false

def increasingRanks (t : Fin 3) : Fin 3 × Fin 3 :=
  if t = 0 then (0,1) else if t = 1 then (0,2) else (1,2)

def decreasingRanks (t : Fin 6) : Fin 3 × Fin 3 :=
  if t = 0 then (0,0) else if t = 1 then (1,0) else if t = 2 then (1,1)
  else if t = 3 then (2,0) else if t = 4 then (2,1) else (2,2)

def pairLower {I : Type} (t : I → Fin 3) : InitialRow I :=
  fun i => some (increasingRanks (t i)).1

def pairUpper {I : Type} (t : I → Fin 3) : InitialRow I :=
  fun i => some (increasingRanks (t i)).2

def tripleLower {I : Type} [DecidableEq I] (j : I) (a : Fin 3) : InitialRow I :=
  fun i => some (if i = j then a else 0)

def tripleCenter {I : Type} [DecidableEq I] (j : I) : InitialRow I :=
  fun i => if i = j then none else some 1

def tripleUpper {I : Type} [DecidableEq I] (j : I) (b : Fin 3) : InitialRow I :=
  fun i => some (if i = j then b else 2)

end Crown.CertificateSemantics

namespace Crown.CertificateSixSemantics

open Crown.Ranks Crown.CertificateSemantics

def maskBits (m : Fin 64) : Fin 6 → Bool := fun i => m.val.testBit i.val

abbrev Pairing6 := (Fin 3 × Bool) ≃ Fin 6

def pairsOfEquiv (p : Pairing6) : Fin 3 → Fin 6 × Fin 6 :=
  fun i => (p (i, false), p (i, true))

def AllPairingsBad {V : Type} (masks : V → Fin 64) : Prop :=
  ∀ p : Pairing6, ¬ Feasible (fun v => rowOfMask (pairsOfEquiv p) (maskBits (masks v)))

end Crown.CertificateSixSemantics

namespace Crown.CertificateData

open Crown.Ranks Crown.CertificateSemantics

abbrev Pattern := (Fin 4 → Fin 3) ⊕ (Fin 4 × Fin 6)

def patternRows : Pattern → List (InitialRow (Fin 4))
  | .inl t => [pairLower t, pairUpper t]
  | .inr (j, t) => [tripleLower j (decreasingRanks t).1,
      tripleCenter j, tripleUpper j (decreasingRanks t).2]

end Crown.CertificateData

namespace Crown.CertificateData

open Crown.Ranks Crown.CertificateSemantics

abbrev RankRow := InitialRow (Fin 4)

def patternSet (q : Pattern) : Set RankRow := {r | r ∈ patternRows q}

def rowSetFeasible (S : Set RankRow) : Prop := Feasible (fun r : S => r.val)

def MinimalInfeasible (S : Set RankRow) : Prop :=
  ¬ rowSetFeasible S ∧ ∀ T, T ⊂ S → rowSetFeasible T

end Crown.CertificateData

namespace Crown.RUPSoundness

open Sat

abbrev Literals := List Literal

abbrev Formula := List Literals

def FalseLiterals (v : Valuation) (a : Literals) : Prop :=
  ∀ l ∈ a, v.neg l

inductive Conflict (F : Formula) : Literals → Prop
  | conflict {a c : Literals} (hc : c ∈ F) (hsub : c ⊆ a) : Conflict F a
  | unit {a c : Literals} {l : Literal} (hc : c ∈ F) (hl : l ∈ c)
      (hother : ∀ m ∈ c, m = l ∨ m ∈ a)
      (next : Conflict F (l.negate :: a)) : Conflict F a

inductive AdditionChain (F : Formula) : Formula → Prop
  | refl : AdditionChain F F
  | add {G : Formula} (previous : AdditionChain F G) (c : Literals)
      (proof : Conflict G c) : AdditionChain F (G ++ [c])

def exampleFormula : Formula :=
  [[.pos 0, .pos 1], [.pos 0, .neg 1], [.neg 0, .pos 1], [.neg 0, .neg 1]]

end Crown.RUPSoundness

namespace Crown.FamilyDomains

open Crown.Ranks

abbrev Families (n r : ℕ) := {s : Finset (Fin n) // s.card = r}

end Crown.FamilyDomains

namespace Crown.FamilyEnumeration

open Crown.FamilyDomains

abbrev IncreasingFamily (n r : ℕ) := {v : Fin r → Fin n // StrictMono v}

noncomputable def tupleFamily {n r : ℕ} (v : IncreasingFamily n r) : Families n r :=
  ⟨Finset.univ.image v.val,by
    rw [Finset.card_image_of_injective _ v.property.injective]
    simp⟩

end Crown.FamilyEnumeration

namespace Crown.DirectStarCheck

open Crown.Ranks

def Accepts {I V : Type*} (rows : V → InitialRow I) : Prop :=
  ∃ t : V → Bool, ∀ b c, ¬MultiStar (rows b) → ¬MultiStar (rows c) →
    ¬StrictBelow (complete (rows b) (t b)) (complete (rows c) (t c))

end Crown.DirectStarCheck


namespace Crown.ReportHistograms

def balanced6 : List Nat := [62716396, 9909762, 1900054, 330678, 65917, 17266, 8157, 11708, 7122, 2287, 1361, 568, 1584, 778, 262, 46, 258, 61, 1, 6, 7, 2, 0, 0, 62, 12, 2, 0, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def balanced6_independent : List Nat := [62716396, 9909762, 1900054, 330678, 65917, 17266, 8157, 11708, 7122, 2287, 1361, 568, 1584, 778, 262, 46, 258, 61, 1, 6, 7, 2, 0, 0, 62, 12, 2, 0, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def odd5 : List Nat := [3342105, 0, 23400, 0, 350, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def odd5_independent : List Nat := [3342105, 0, 23400, 0, 350, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

end Crown.ReportHistograms

namespace Crown.ClauseNormalization

def Tautological (c : List Sat.Literal) : Prop :=
  ∃ l ∈ c, l.negate ∈ c

end Crown.ClauseNormalization

namespace Crown.ObstructionEncoding

variable {v g t : ℕ}

def Encoding (cores : Fin g → List (Fin v)) (templates : Fin t → List (Fin g))
    (cap : ℕ) (s : Fin v → Bool) (c : Fin g → Bool) : Prop :=
  Fintype.card {m // s m = true} ≤ cap ∧
  (∀ i, c i = true → ∀ m ∈ cores i, s m = true) ∧
  (∀ j, ∃ i ∈ templates j, c i = true)

end Crown.ObstructionEncoding
