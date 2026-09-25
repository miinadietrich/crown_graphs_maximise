import Crown.PairingWords
import Crown.CertificateSemantics

/-! A finite mask theorem implies the corresponding matrix theorem. Passing
to distinct masks retains repeated neighbourhoods, empty types and isolated
vertices in the original graph. -/
namespace Crown.MaskGraphTransport
open Crown.Ranks Crown.CertificateSemantics Crown.BalancedLarge

theorem matrix_of_masks {k masks cap : ℕ} (hk : 3 ≤ k)
    (bits : Fin masks → Fin (2*k) → Bool) (hbits : Function.Surjective bits)
    (hfinite : ∀ s : Fin masks → Bool, Fintype.card {m // s m = true} ≤ cap →
      ∃ p : (Fin k × Bool) ≃ Fin (2*k),
        Feasible (fun m : {m // s m = true} =>
          rowOfMask (fun i => (p (i,false),p (i,true))) (bits m.val)))
    {B : Type*} [Fintype B] [DecidableEq B] (hB : Fintype.card B ≤ cap)
    (M : Fin (2*k) → B → Bool) : KRepresentable (matrixGraph M) k := by
  classical
  let f : B → Fin masks := fun b => Classical.choose (hbits (fun a => M a b))
  have hf : ∀ b, bits (f b) = fun a => M a b := fun b => Classical.choose_spec (hbits _)
  let S : Finset (Fin masks) := Finset.univ.image f
  let s : Fin masks → Bool := fun m => decide (m ∈ S)
  have hS : S.card ≤ cap := (Finset.card_image_le).trans (by simpa using hB)
  have hs : Fintype.card {m // s m = true} ≤ cap := by
    simpa [s,Fintype.card_subtype] using hS
  obtain ⟨p,r,hr,hn⟩ := hfinite s hs
  let lift : B → {m // s m = true} := fun b => ⟨f b, by simp [s,S]⟩
  have hrow : ∀ b, Orientations.row (PairingWords.neighbours p M b) (fun _ => false) =
      rowOfMask (fun i => (p (i,false),p (i,true))) (bits (lift b).val) := by
    intro b
    funext i
    change Orientations.entry (M (p (i,false)) b, M (p (i,true)) b) false =
      rankOfBits (bits (f b) (p (i,false))) (bits (f b) (p (i,true)))
    rw [hf b]
    dsimp only
    cases M (p (i,false)) b <;> cases M (p (i,true)) b <;> rfl
  apply PairingWords.of_feasible hk p M
  refine ⟨fun b => r (lift b), ?_, fun b c => hn (lift b) (lift c)⟩
  intro b
  change Completes (Orientations.row (PairingWords.neighbours p M b) (fun _ => false))
    (r (lift b))
  rw [hrow b]
  exact hr (lift b)

#print axioms matrix_of_masks
end Crown.MaskGraphTransport
