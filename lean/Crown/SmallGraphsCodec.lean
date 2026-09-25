import Crown.Words
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Init.Data.BitVec.Lemmas

namespace Crown.SmallGraphs

def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    ((List.finRange n).filter (fun b => a < b)).map (fun b => (a,b))

def pairIndex {n : ℕ} (a b : Fin n) : ℕ :=
  (pairs n).idxOf (min a b,max a b)

def graph (n mask : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ mask.testBit (pairIndex a b) = true
  symm := ⟨by intro a b h; simpa [pairIndex,min_comm,max_comm,ne_comm] using h⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance (n mask : ℕ) : DecidableRel (graph n mask).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem pair_mem {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (min a b,max a b) ∈ pairs n := by
  simp [pairs,List.mem_flatMap,hab,Ne.symm hab]

theorem encode_graph (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ mask : Fin (2 ^ (pairs n).length), graph n mask.val = G := by
  classical
  let bits := (pairs n).map (fun p => decide (G.Adj p.1 p.2))
  let bv := BitVec.ofBoolListLE bits
  have hb : bv.toNat < 2 ^ (pairs n).length := by
    simpa [bv,bits] using bv.isLt
  refine ⟨⟨bv.toNat,hb⟩,?_⟩
  ext a b
  by_cases hab : a = b
  · subst b; simp [graph]
  have hi : pairIndex a b < (pairs n).length :=
    List.idxOf_lt_length_of_mem (pair_mem a b hab)
  have ht : bv.toNat.testBit (pairIndex a b) =
      decide (G.Adj (min a b) (max a b)) := by
    change bv.getLsbD (pairIndex a b) = _
    rw [BitVec.getLsbD_ofBoolListLE]
    have hil : pairIndex a b < bits.length := by simpa [bits] using hi
    rw [List.getD_eq_getElem _ _ hil]
    simp only [bits,List.getElem_map]
    have he : (pairs n)[pairIndex a b] = (min a b,max a b) := List.getElem_idxOf hi
    rw [he]
  change (a ≠ b ∧ bv.toNat.testBit (pairIndex a b) = true) ↔ G.Adj a b
  rw [ht,decide_eq_true_eq,and_iff_right hab]
  rcases le_total a b with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h,G.adj_comm]

#print axioms encode_graph

end Crown.SmallGraphs
