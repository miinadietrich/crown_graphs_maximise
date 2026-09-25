import Crown.Definitions

namespace Crown.CrownFourFinite

local instance : BEq (Fin 4) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Fin 4) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

instance (w : List (Fin 4)) (a b : Fin 4) : Decidable (Crown.Alternates w a b) :=
  inferInstanceAs (Decidable ((Crown.restrictPair w a b).IsChain (· ≠ ·)))

def IntervalPattern (w : List (Fin 4)) (z : Fin 4) (lo len : Fin 9) : Prop :=
  ∀ i : Fin 4, ((w.drop lo.val).take len.val).count i = 1 ↔ i ≠ z

instance (w : List (Fin 4)) (z : Fin 4) (lo len : Fin 9) :
    Decidable (IntervalPattern w z lo len) := by
  unfold IntervalPattern
  infer_instance

def Obstructed (w : List (Fin 4)) : Prop :=
  (∀ i : Fin 4, w.count i = 2) →
  (∀ a b : Fin 4, a ≠ b → ¬ Crown.Alternates w a b) →
  ∃ z : Fin 4, ∀ lo len : Fin 9, ¬ IntervalPattern w z lo len

instance (w : List (Fin 4)) : Decidable (Obstructed w) := by
  unfold Obstructed
  infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem check_012 : ∀ d e f g h : Fin 4, Obstructed [0,1,2,d,e,f,g,h] := by
  decide +kernel

#print axioms check_012

end Crown.CrownFourFinite
