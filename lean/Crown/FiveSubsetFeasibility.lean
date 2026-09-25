import Crown.OddFeasibility
import Crown.CertificateSixSemantics
import Mathlib.Logic.Equiv.Option

namespace Crown.FiveSubsetFeasibility
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics

theorem isolated_vertex {B : Type*} [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 7) (M : Fin 6 → B → Bool)
    (z : Fin 6) (hz : ∀ b, M z b = false) :
    ∃ p : Pairing6, Feasible (fun b =>
      rowOfMask (pairsOfEquiv p) (fun a => M a b)) := by
  classical
  let A := {a : Fin 6 // a ≠ z}
  let f : Option A ≃ Fin 6 := Equiv.optionSubtypeNe z
  have hA : Fintype.card A = 5 := by
    have hc := Fintype.card_congr f
    simp only [Fintype.card_option,Fintype.card_fin] at hc
    omega
  let M' : A → B → Bool := fun a b => M a.val b
  obtain ⟨e,he⟩ := OddGraphs.exists_feasible_pairing_three 3 (by decide)
    (by simpa using hA) (by simpa [hA] using hB) M'
  have hbit : ∀ b x, OddGraphs.optBit M' b x = M (f x) b := by
    intro b x
    cases x with
    | none => exact (hz b).symm
    | some a => rfl
  have hr : OddRanks.rows (OddGraphs.pairedBits M' e) =
      fun b => rowOfMask (pairsOfEquiv (e.trans f)) (fun a => M a b) := by
    funext b i
    change Orientations.entry
      (OddGraphs.optBit M' b (e (i,false)),OddGraphs.optBit M' b (e (i,true))) false = _
    rw [hbit,hbit]
    change Orientations.entry (M (f (e (i,false))) b,M (f (e (i,true))) b) false =
      rankOfBits (M (f (e (i,false))) b) (M (f (e (i,true))) b)
    cases M (f (e (i,false))) b <;> cases M (f (e (i,true))) b <;> rfl
  exact ⟨e.trans f,hr ▸ he⟩

/-- Every family of at most seven subsets of any fixed five-element subset
of the six vertices has a feasible pairing. Repetitions are allowed. -/
theorem fixed_subset {B : Type*} [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 7) (S : Finset (Fin 6)) (hS : S.card = 5)
    (N : B → Finset (Fin 6)) (hN : ∀ b, N b ⊆ S) :
    ∃ p : Pairing6, Feasible (fun b =>
      rowOfMask (pairsOfEquiv p) (fun a => decide (a ∈ N b))) := by
  obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show S.card < (Finset.univ : Finset (Fin 6)).card by simpa [hS])
  exact isolated_vertex hB (fun a b => decide (a ∈ N b)) z
    (fun b => by simp [show z ∉ N b from fun h => hz (hN b h)])

#print axioms isolated_vertex
#print axioms fixed_subset
end Crown.FiveSubsetFeasibility
