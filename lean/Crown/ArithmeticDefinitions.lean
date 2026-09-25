import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.VecNotation

namespace Crown.Arithmetic

/-- The factorial quotient from D15/P05. Every argument is signed, including
the shifted first argument. A negative argument gives zero before `toNat`
is used, so natural truncated subtraction cannot alter the domain. -/
def M (k x y z : ℤ) : ℕ :=
  if 0 ≤ k ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ k ∧ y ≤ k ∧ z ≤ k ∧
      x + y + z = 2 * k then
    x.toNat.factorial * y.toNat.factorial * z.toNat.factorial /
      ((k - x).toNat.factorial * (k - y).toNat.factorial * (k - z).toNat.factorial)
  else 0

/-- Number of oriented, unordered pairings, as a numerical expression.
Its interpretation as a count is a separate combinatorial obligation. -/
def Q (k : ℕ) : ℕ := (2 * k).factorial / k.factorial

/-- P07/P08, with signed shifts in every occurrence of `M`. -/
def P (k x y z t : ℕ) : ℕ :=
  if t = 0 then
    2 * M k x y z + y * (y - 1) * M ((k : ℤ) - 1) x ((y : ℤ) - 2) z +
      x * (x - 1) * M ((k : ℤ) - 1) ((x : ℤ) - 2) y z
  else if t = 1 then
    2 * y * M ((k : ℤ) - 1) x ((y : ℤ) - 1) z +
      2 * x * M ((k : ℤ) - 1) ((x : ℤ) - 1) y z
  else 0

/-- The full natural-number domain for a table entry, including attainment. -/
def IsSliceMaximum (k z t a : ℕ) : Prop :=
  (∀ x y : ℕ, x + y + z + t = 2 * k → P k x y z t ≤ a) ∧
  ∃ x y : ℕ, x + y + z + t = 2 * k ∧ P k x y z t = a

/-- A reduced finite test: the partition equation uniquely determines `y`.
The guard proves that subtraction has not truncated a negative number. -/
def FiniteSliceMaximum (k z t a : ℕ) : Prop :=
  (∀ x : Fin (2 * k + 1), x.val + z + t ≤ 2 * k →
    P k x.val (2 * k - (x.val + z + t)) z t ≤ a) ∧
  ∃ x : Fin (2 * k + 1), x.val + z + t ≤ 2 * k ∧
    P k x.val (2 * k - (x.val + z + t)) z t = a

instance (k z t a : ℕ) : Decidable (FiniteSliceMaximum k z t a) :=
  by unfold FiniteSliceMaximum; infer_instance

def table60 : Fin 7 → ℕ := ![5040, 5040, 7200, 8640, 8064, 5040, 1440]
def table61 : Fin 7 → ℕ := ![1440, 2400, 2880, 3456, 2880, 1440, 0]
def table70 : Fin 8 → ℕ := ![40320, 40320, 60480, 79200, 86400, 72000, 40320, 10080]
def table71 : Fin 8 → ℕ := ![10080, 17280, 21600, 28800, 28800, 23040, 10080, 0]

def theta (k : ℕ) : ℚ := 2 / (((2 * k - 1) * Nat.choose (2 * k - 2) (k - 1) : ℕ) : ℚ)

end Crown.Arithmetic

namespace Crown.Counting

/-- Each of k independently oriented pairs has two choices. -/
abbrev Orientations (k : ℕ) := Fin k → Bool

end Crown.Counting
