import Crown.BalancedLarge

/-! Transport of the block construction along an arbitrary pairing of one
part of a bipartite graph. The feasibility hypothesis is explicit here;
the counting and certificate arguments supply it in the applications. -/

namespace Crown.PairingWords

open Crown.BalancedLarge

variable {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B] {k : ℕ}

def neighbours (p : (Fin k × Bool) ≃ A) (M : A → B → Bool) :
    B → Orientations.NeighbourRow (Fin k) :=
  fun b i => (M (p (i, false)) b, M (p (i, true)) b)

theorem of_feasible (hk : 3 ≤ k) (p : (Fin k × Bool) ≃ A)
    (M : A → B → Bool)
    (h : Ranks.Feasible (fun b => Orientations.row (neighbours p M b) (fun _ => false))) :
    KRepresentable (matrixGraph M) k := by
  classical
  obtain ⟨w, hw⟩ := Blocks.feasible_representable hk _ h
  have hr : KRepresentable (rawGraph (neighbours p M)) k :=
    ⟨w.map (alphabetSwap (fun _ => false)),
      represents_equiv (alphabetSwap (fun _ => false))
        (swap_adj (neighbours p M) (fun _ => false)) hw⟩
  obtain ⟨v, hv⟩ := hr
  let e := Equiv.sumCongr p (Equiv.refl B)
  refine ⟨v.map e, represents_equiv e ?_ hv⟩
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => cases a with | mk i s => cases s <;> rfl
  | inr a =>
    cases b with
    | inl b => cases b with | mk i s => cases s <;> rfl
    | inr b => rfl

#print axioms of_feasible

end Crown.PairingWords
