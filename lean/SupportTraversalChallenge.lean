import Crown.EnumeratorDefinitions
import Mathlib.Data.Nat.Choose.Basic

namespace Crown.GosperTraversal
open Crown.EnumeratorDefinitions

theorem update_successor (n r x : ℕ) (hn : n ≤ 64) (hr : 0 < r) (hrn : r ≤ n)
    (hx : ValidMask n r x) (hlast : x ≠ lastMask n r) :
    0 < lowBit64 x ∧ x + lowBit64 x < 2^64 ∧
    ValidMask n r (gosperRaw x) ∧ x < gosperRaw x ∧
    ∀ y, ValidMask n r y → x < y → gosperRaw x ≤ y := by
  sorry

theorem traversal_complete (n r : ℕ) (hn : n ≤ 64) (hr : 0 < r) (hrn : r ≤ n) :
    (∀ x, ValidMask n r x ↔ ∃ j < Nat.choose n r,
      (gosperStep n r)^[j] (firstMask r) = x) ∧
    (gosperStep n r)^[Nat.choose n r-1] (firstMask r) = lastMask n r ∧
    StrictMonoOn (fun j => (gosperStep n r)^[j] (firstMask r)) (Set.Iio (Nat.choose n r)) := by
  sorry
end Crown.GosperTraversal

namespace Crown.TupleTraversal
open Crown.EnumeratorDefinitions

theorem update_successor (n r : ℕ) (hrn : r ≤ n) (a : TupleState r)
    (ha : ValidTuple n r a) :
    (tupleNext n r a = none ↔ a = lastTuple n r) ∧
    ∀ b, tupleNext n r a = some b → ValidTuple n r b ∧ LexLess a b ∧
      ∀ c, ValidTuple n r c → LexLess a c → b = c ∨ LexLess b c := by
  sorry

theorem traversal_complete (n r : ℕ) (hrn : r ≤ n) :
    (∀ a, ValidTuple n r a ↔ ∃ j < Nat.choose n r,
      (tupleStep n r)^[j] (firstTuple r) = a) ∧
    (tupleStep n r)^[Nat.choose n r-1] (firstTuple r) = lastTuple n r ∧
    (∀ i j, i < j → j < Nat.choose n r →
      LexLess ((tupleStep n r)^[i] (firstTuple r)) ((tupleStep n r)^[j] (firstTuple r))) := by
  sorry
end Crown.TupleTraversal
