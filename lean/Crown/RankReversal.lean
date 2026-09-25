import Crown.Orientations
import Mathlib.Tactic.FinCases

/-! Simultaneous reversal of endpoint orientations reflects every prescribed
rank r to 4-r and exchanges the two extreme completions. This preserves
feasibility in every dimension, including the three-pair certificate case. -/

namespace Crown.RankReversal
open Crown.Ranks Crown.Orientations

variable {I V : Type*}

def mirror (r : InitialRow I) : InitialRow I := fun i => (r i).map Fin.rev

theorem completion_entry_mirror : ∀ (a : Option (Fin 3)) (r : Fin 5),
    (match a.map Fin.rev with
     | none => r.rev = 0 ∨ r.rev = 4
     | some u => r.rev = prescribed u) ↔
    (match a with
     | none => r = 0 ∨ r = 4
     | some u => r = prescribed u) := by
  intro a r
  cases a with
  | none =>
    change (r.rev = 0 ∨ r.rev = 4) ↔ (r = 0 ∨ r = 4)
    fin_cases r <;> decide +kernel
  | some u =>
    change r.rev = prescribed u.rev ↔ r = prescribed u
    fin_cases u <;> fin_cases r <;> decide +kernel

theorem completes_mirror (r : InitialRow I) (s : CompletedRow I) :
    Completes (mirror r) (fun i => (s i).rev) ↔ Completes r s := by
  exact forall_congr' (fun i => completion_entry_mirror (r i) (s i))

theorem strictBelow_mirror (r s : CompletedRow I) :
    StrictBelow (fun i => (r i).rev) (fun i => (s i).rev) ↔ StrictBelow s r := by
  exact forall_congr' (fun _ => Fin.rev_lt_rev)

theorem mirror_involutive (r : InitialRow I) : mirror (mirror r) = r := by
  funext i
  cases h : r i <;> simp [mirror,h]

theorem feasible_mirror (rows : V → InitialRow I) (h : Feasible rows) :
    Feasible (fun b => mirror (rows b)) := by
  obtain ⟨r,hr,hn⟩ := h
  refine ⟨fun b i => (r b i).rev,fun b => (completes_mirror _ _).mpr (hr b),?_⟩
  intro b c hc
  exact hn c b ((strictBelow_mirror _ _).mp hc)

theorem feasible_mirror_iff (rows : V → InitialRow I) :
    Feasible (fun b => mirror (rows b)) ↔ Feasible rows := by
  constructor
  · intro h
    have hm := feasible_mirror (fun b => mirror (rows b)) h
    simpa only [mirror_involutive] using hm
  · exact feasible_mirror rows

theorem entry_flip : ∀ (bits : Bool × Bool) (o : Bool),
    entry bits (!o) = (entry bits o).map Fin.rev := by decide +kernel

theorem row_flip (N : NeighbourRow I) (o : I → Bool) :
    row N (fun i => !(o i)) = mirror (row N o) := by
  funext i
  exact entry_flip (N i) (o i)

/-- Reversing every pair preserves the full existence of valid completions. -/
theorem feasible_flip_all (N : V → NeighbourRow I) (o : I → Bool) :
    Feasible (fun b => row (N b) (fun i => !(o i))) ↔
      Feasible (fun b => row (N b) o) := by
  simp only [row_flip]
  exact feasible_mirror_iff _

#print axioms completion_entry_mirror
#print axioms feasible_mirror_iff
#print axioms feasible_flip_all
end Crown.RankReversal
