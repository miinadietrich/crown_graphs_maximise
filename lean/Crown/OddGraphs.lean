import Crown.OddRanks
import Crown.OddSelection
import Crown.BalancedLarge
import Mathlib.Data.Fintype.BigOperators

/-! R07--R09: an actual representation for the odd smaller part. The pairing
contains a prescribed real vertex and a fresh isolated vertex; both the
neighbourhood cardinality and the final graph are transported explicitly. -/

namespace Crown.OddGraphs

variable {k : ℕ} {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem exists_pairing (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1) (a : A)
    (z : Fin k) : ∃ e : (Fin k × Bool) ≃ Option A,
      e (z,false) = some a ∧ e (z,true) = none := by
  classical
  have hcard : Fintype.card (Fin k × Bool) = Fintype.card (Option A) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_option, hA]
    omega
  let e₀ := Fintype.equivOfCardEq hcard
  let e₁ := e₀.trans (Equiv.swap (e₀ (z,true)) none)
  have he₁ : e₁ (z,true) = none := by simp [e₁]
  have hne : e₁ (z,false) ≠ none := by
    intro hh
    have hp := e₁.injective (hh.trans he₁.symm)
    cases hp
  let e := e₁.trans (Equiv.swap (e₁ (z,false)) (some a))
  refine ⟨e, by simp [e], ?_⟩
  simp only [e, Equiv.trans_apply, he₁]
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hne) (by simp)

def optBit (M : A → B → Bool) (b : B) : Option A → Bool
  | none => false
  | some a => M a b

def pairedBits (M : A → B → Bool) (e : (Fin k × Bool) ≃ Option A) :
    B → Orientations.NeighbourRow (Fin k) :=
  fun b i => (optBit M b (e (i,false)), optBit M b (e (i,true)))

def neighbourhood (M : A → B → Bool) (b : B) : Finset A :=
  Finset.univ.filter (fun a => M a b = true)

theorem paired_degree (M : A → B → Bool) (e : (Fin k × Bool) ≃ Option A) (b : B) :
    OddRanks.degree (pairedBits M e b) = (neighbourhood M b).card := by
  classical
  have hs : OddRanks.degree (pairedBits M e b) =
      ∑ p : Fin k × Bool, if optBit M b (e p) then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [OddRanks.degree, pairedBits, Fintype.sum_bool]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.add_comm _ _
  calc
    OddRanks.degree (pairedBits M e b) = _ := hs
    _ = ∑ p : Option A, if optBit M b p then 1 else 0 :=
      Equiv.sum_comp e (fun p => if optBit M b p then (1 : ℕ) else 0)
    _ = (neighbourhood M b).card := by
      rw [Fintype.sum_option]
      change 0 + (∑ a : A, if M a b = true then (1 : ℕ) else 0) =
        (Finset.univ.filter (fun a => M a b = true)).card
      rw [Nat.zero_add]
      exact (Finset.card_filter (fun a => M a b = true) Finset.univ).symm

theorem centre_neighbourhood (M : A → B → Bool) (e : (Fin k × Bool) ≃ Option A)
    (a : A) (z : Fin k) (hez : e (z,false) = some a) (hed : e (z,true) = none)
    (b : B) (hc : OddRanks.Centre (pairedBits M e b) z) :
    neighbourhood M b = Finset.univ.erase a := by
  ext x
  simp only [neighbourhood, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true]
  obtain ⟨⟨i,s⟩, hi⟩ := e.surjective (some x)
  have hcz := hc i
  by_cases hiz : i = z
  · subst i
    cases s with
    | false =>
      have hxa : x = a := Option.some.inj (hi.symm.trans hez)
      subst x
      have hz := congrArg Prod.fst hcz
      have hm : M a b = false := by simpa [pairedBits, hez, optBit] using hz
      simp [hm]
    | true => rw [hed] at hi; cases hi
  · have hxa : x ≠ a := by
      intro hxa
      have hp := e.injective (hi.trans (congrArg some hxa) |>.trans hez.symm)
      exact hiz (congrArg Prod.fst hp)
    have hm : M x b = true := by
      cases s with
      | false => simpa [pairedBits, hiz, hi, optBit] using congrArg Prod.fst hcz
      | true => simpa [pairedBits, hiz, hi, optBit] using congrArg Prod.snd hcz
    simp [hm, hxa]

theorem safe_pairedBits (M : A → B → Bool) (e : (Fin k × Bool) ≃ Option A)
    (a : A) (z : Fin k) (hez : e (z,false) = some a) (hed : e (z,true) = none)
    (hs : (¬ ∃ c, neighbourhood M c = Finset.univ.erase a) ∨
      ∀ l u, (neighbourhood M l).card = k → (neighbourhood M u).card = k →
        a ∈ neighbourhood M l → a ∈ neighbourhood M u → l = u) :
    OddRanks.Safe (pairedBits M e) z := by
  rcases hs with hn | hu
  · left
    rintro ⟨c,hc⟩
    exact hn ⟨c,centre_neighbourhood M e a z hez hed c hc⟩
  · right
    intro l u hl hu' hal hau
    apply hu l u
    · simpa only [paired_degree] using hl
    · simpa only [paired_degree] using hu'
    · simpa [neighbourhood, pairedBits, hez, optBit] using hal
    · simpa [neighbourhood, pairedBits, hez, optBit] using hau

def addDummyEmbedding : A ⊕ B ↪ Option A ⊕ B where
  toFun := Sum.map some id
  inj' := by intro a b h; cases a <;> cases b <;> simpa using h

/-- Every Boolean bipartite matrix with an odd part of size 2k−1 and at
most 2k+1 rows has an actual k-uniform representative, for k≥3. -/
theorem matrix_representable_three (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (M : A → B → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) k := by
  classical
  obtain ⟨a,ha⟩ := Crown.exists_safe_odd_vertex_three k hk hA hB (neighbourhood M)
  let z : Fin k := ⟨0,by omega⟩
  obtain ⟨e,hez,hed⟩ := exists_pairing hk hA a z
  have hsp : ∀ b, (pairedBits M e b z).2 = false := by
    intro b; simp [pairedBits, hed, optBit]
  have hf := OddRanks.feasible_of_safe_three hk (pairedBits M e) z hsp
    (safe_pairedBits M e a z hez hed ha)
  obtain ⟨w,hw⟩ := Blocks.feasible_representable (by omega : 3 ≤ k) _ hf
  let es := BalancedLarge.alphabetSwap (B := B) (fun _ : Fin k => false)
  have hr := Crown.represents_equiv es (BalancedLarge.swap_adj (pairedBits M e) _) hw
  let et := Equiv.sumCongr e (Equiv.refl B)
  have ht : Crown.KRepresentable (BalancedLarge.matrixGraph (fun p b => optBit M b p)) k := by
    refine ⟨_, Crown.represents_equiv et ?_ hr⟩
    intro p q
    cases p with
    | inl p =>
      cases q with
      | inl q => rfl
      | inr q => cases p with | mk i s => cases s <;> rfl
    | inr p =>
      cases q with
      | inl q => cases q with | mk i s => cases s <;> rfl
      | inr q => rfl
  apply Crown.kRepresentable_of_inducedEmbedding addDummyEmbedding _ ht
  intro p q; cases p <;> cases q <;> rfl

theorem matrix_representable (k : ℕ) (hk : 4 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (M : A → B → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) k :=
  matrix_representable_three k (by omega) hA hB M

/-- The five-by-seven finite case follows from the distinguished-coordinate argument. -/
theorem five_seven (M : Fin 5 → Fin 7 → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) 3 :=
  matrix_representable_three 3 (by decide) (by simp) (by simp) M

#print axioms exists_pairing
#print axioms paired_degree
#print axioms centre_neighbourhood
#print axioms matrix_representable
#print axioms matrix_representable_three
#print axioms five_seven

end Crown.OddGraphs
