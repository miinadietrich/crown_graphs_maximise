import Mathlib.Data.List.Defs
import Lean
namespace Crown.CompactFiniteData
def decode64 (n : ℕ) : List (Fin 64) :=
  if h : n = 0 then [] else
    ⟨(n-1)%64, Nat.mod_lt _ (by decide)⟩ :: decode64 ((n-1)/64)
termination_by n
decreasing_by
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt (Nat.pos_of_ne_zero h) (by decide))
end Crown.CompactFiniteData
