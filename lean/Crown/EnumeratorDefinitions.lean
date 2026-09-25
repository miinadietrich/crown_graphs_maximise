import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Iterate

namespace Crown.EnumeratorDefinitions

/-- The number of selected neighbourhood masks, within the full n-mask universe. -/
def weight (n x : ℕ) : ℕ := ((Finset.range n).filter (fun i => x.testBit i = true)).card

def ValidMask (n r x : ℕ) : Prop := x < 2^n ∧ weight n x = r

def firstMask (r : ℕ) : ℕ := 2^r-1

def lastMask (n r : ℕ) : ℕ := (2^r-1) * 2^(n-r)

/-- Exact mathematical expression corresponding to c=s&(-s). -/
def lowBit64 (x : ℕ) : ℕ := x &&& (2^64-x)

/-- Exact unbounded arithmetic expression for the source update, on states
where the separate no-overflow and positive-divisor obligations hold. -/
def gosperRaw (x : ℕ) : ℕ :=
  let c := lowBit64 x
  let R := x+c
  (((R ^^^ x) >>> 2) / c) ||| R

def gosperStep (n r x : ℕ) : ℕ := if x = lastMask n r then x else gosperRaw x

abbrev TupleState (r : ℕ) := Fin r → ℕ

def ValidTuple (n r : ℕ) (a : TupleState r) : Prop := StrictMono a ∧ ∀ i, a i < n

def firstTuple (r : ℕ) : TupleState r := fun i => i.val

def lastTuple (n r : ℕ) : TupleState r := fun i => n-r+i.val

def LexLess {r : ℕ} (a b : TupleState r) : Prop :=
  ∃ j, a j < b j ∧ ∀ i, i < j → a i = b i

def movable (n r : ℕ) (a : TupleState r) : Finset (Fin r) :=
  Finset.univ.filter (fun j => a j < n-r+j.val)

/-- Increment the rightmost movable position and make the remaining tail
consecutive. The source's search from r-1 downward selects this maximum. -/
def tupleNext (n r : ℕ) (a : TupleState r) : Option (TupleState r) :=
  if h : (movable n r a).Nonempty then
    let j := (movable n r a).max' h
    some (fun i => if i < j then a i else a j+1+(i.val-j.val))
  else none

def tupleStep (n r : ℕ) (a : TupleState r) : TupleState r :=
  (tupleNext n r a).getD a

end Crown.EnumeratorDefinitions
