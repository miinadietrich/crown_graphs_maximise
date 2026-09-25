import Crown.CrownLower
import Crown.BalancedLarge

namespace Crown.CrownUpper

open Crown.Blocks

variable {A : Type*} [DecidableEq A]

def graph (A : Type*) : SimpleGraph (Bool × A) where
  Adj a b := a.1 ≠ b.1 ∧ a.2 ≠ b.2
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def embedding {k : ℕ} (e : A ↪ Fin k × Bool) : (Bool × A) ↪ Alphabet k A where
  toFun p := match p.1 with
    | false => Sum.inl (e p.2)
    | true => Sum.inr p.2
  inj' := by
    rintro ⟨s,a⟩ ⟨t,b⟩ h
    cases s <;> cases t
    · have he : a = b := e.injective (Sum.inl.inj h)
      subst b; rfl
    · cases h
    · cases h
    · have he : a = b := Sum.inr.inj h
      subst b; rfl

theorem of_rank_pattern [Fintype A] {k : ℕ} (hk : 3 ≤ k)
    (e : A ↪ Fin k × Bool) (r : A → Ranks.CompletedRow (Fin k))
    (hno : ∀ a b, ¬ Ranks.StrictBelow (r a) (r b))
    (hadj : ∀ a b, RankAdjacent (r b (e a).1) (e a).2 ↔ a ≠ b) :
    Crown.KRepresentable (graph A) k := by
  obtain ⟨π,hπ,hm,ho⟩ := Orders.coordinate_orders (by omega) r (fun a b _ => hno a b)
  have hr : Crown.KRepresentable (rankGraph r) k :=
    ⟨Blocks.word r π,Blocks.word_represents_rankGraph hk r π hπ hm ho⟩
  apply Crown.kRepresentable_of_inducedEmbedding (embedding e) _ hr
  rintro ⟨s,a⟩ ⟨t,b⟩
  cases s <;> cases t
  · change (false ≠ false ∧ a ≠ b) ↔ False
    simp
  · change (false ≠ true ∧ a ≠ b) ↔ RankAdjacent (r b (e a).1) (e a).2
    exact ⟨fun h => (hadj a b).mpr h.2,fun h => ⟨by decide,(hadj a b).mp h⟩⟩
  · change (true ≠ false ∧ a ≠ b) ↔ RankAdjacent (r a (e b).1) (e b).2
    exact ⟨fun h => (hadj b a).mpr (Ne.symm h.2),fun h => ⟨by decide,Ne.symm ((hadj b a).mp h)⟩⟩
  · change (true ≠ true ∧ a ≠ b) ↔ False
    simp

theorem transport_card [Fintype A] {n k : ℕ} (hcard : Fintype.card A = n)
    (h : Crown.KRepresentable (graph A) k) : Crown.KRepresentable (Crown.crownGraph n) k := by
  classical
  let e : A ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let E : (Bool × A) ≃ (Bool × Fin n) := Equiv.prodCongr (Equiv.refl Bool) e
  obtain ⟨w,hw⟩ := h
  refine ⟨w.map E,Crown.represents_equiv E ?_ hw⟩
  intro a b
  change (a.1 ≠ b.1 ∧ e a.2 ≠ e b.2) ↔ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)
  simp only [ne_eq,e.injective.eq_iff]

def evenRank {k : ℕ} (b : Fin k × Bool) (i : Fin k) : Fin 5 :=
  if i = b.1 then if b.2 then 1 else 3 else 2

theorem evenRank_adj {k : ℕ} (a b : Fin k × Bool) :
    RankAdjacent (evenRank b a.1) a.2 ↔ a ≠ b := by
  rcases a with ⟨i,s⟩
  rcases b with ⟨j,t⟩
  by_cases hij : i = j
  · subst j
    cases s <;> cases t <;> simp [evenRank,RankAdjacent]
  · cases s <;> cases t <;> simp [evenRank,RankAdjacent,hij,Prod.ext_iff]

theorem even_representable (k : ℕ) (hk : 3 ≤ k) :
    Crown.KRepresentable (Crown.crownGraph (2*k)) k := by
  apply transport_card (A := Fin k × Bool) (by simp [Nat.mul_comm])
  apply of_rank_pattern hk (Function.Embedding.refl _) evenRank
  · intro b c h
    obtain ⟨i,hib,hic⟩ := Blocks.coordinate_avoiding_two hk b.1 c.1
    have hi := h i
    simpa [evenRank,hib,hic] using hi
  · exact evenRank_adj

def Real (k : ℕ) (z : Fin k) := {b : Fin k × Bool // b ≠ (z,true)}
instance {k : ℕ} {z : Fin k} : Fintype (Real k z) := inferInstanceAs (Fintype {b : Fin k × Bool // b ≠ (z,true)})
instance {k : ℕ} {z : Fin k} : DecidableEq (Real k z) := inferInstanceAs (DecidableEq {b : Fin k × Bool // b ≠ (z,true)})

def oddRank {k : ℕ} (z : Fin k) (b : Real k z) (i : Fin k) : Fin 5 :=
  if i = z then if b.val.1 = z then 0 else 1 else evenRank b.val i

theorem real_special_side {k : ℕ} (z : Fin k) (a : Real k z) (ha : a.val.1 = z) : a.val.2 = false := by
  cases hs : a.val.2 with
  | false => rfl
  | true => exact False.elim (a.property (Prod.ext ha hs))

theorem oddRank_adj {k : ℕ} (z : Fin k) (a b : Real k z) :
    RankAdjacent (oddRank z b a.val.1) a.val.2 ↔ a ≠ b := by
  by_cases ha : a.val.1 = z
  · have has := real_special_side z a ha
    by_cases hb : b.val.1 = z
    · have hbs := real_special_side z b hb
      have he : a = b := Subtype.ext (Prod.ext (ha.trans hb.symm) (has.trans hbs.symm))
      simp [oddRank,ha,hb,has,he,RankAdjacent]
    · have he : a ≠ b := fun he => hb (he ▸ ha)
      simp [oddRank,ha,hb,has,he,RankAdjacent]
  · rw [oddRank,if_neg ha,evenRank_adj]
    constructor
    · intro h he
      exact h (congrArg Subtype.val he)
    · intro h he
      exact h (Subtype.ext he)

theorem odd_representable (k : ℕ) (hk : 3 ≤ k) :
    Crown.KRepresentable (Crown.crownGraph (2*k-1)) k := by
  let z : Fin k := ⟨0,by omega⟩
  have hcard : Fintype.card (Real k z) = 2*k-1 := by
    change Fintype.card {b : Fin k × Bool // ¬ b = (z,true)} = _
    rw [Fintype.card_subtype_compl]
    simp [Nat.mul_comm]
  apply transport_card hcard
  apply of_rank_pattern hk (Function.Embedding.subtype _) (oddRank z)
  · intro b c h
    obtain ⟨i,hib,hic⟩ := Blocks.coordinate_avoiding_two hk b.val.1 c.val.1
    have hi := h i
    by_cases hiz : i = z
    · have hbz : b.val.1 ≠ z := fun he => hib (hiz.trans he.symm)
      have hcz : c.val.1 ≠ z := fun he => hic (hiz.trans he.symm)
      simpa [oddRank,hiz,hbz,hcz] using hi
    · simpa [oddRank,evenRank,hiz,hib,hic] using hi
  · exact oddRank_adj z

theorem halfCeil_representable (n : ℕ) (hn : 5 ≤ n) :
    Crown.KRepresentable (Crown.crownGraph n) (Crown.halfCeil n) := by
  let k := Crown.halfCeil n
  have hk : 3 ≤ k := by dsimp [k,Crown.halfCeil]; omega
  have hcases : n = 2*k ∨ n = 2*k-1 := by dsimp [k,Crown.halfCeil]; omega
  change Crown.KRepresentable (Crown.crownGraph n) k
  rcases hcases with he | he
  · rw [he]
    exact even_representable k hk
  · rw [he]
    exact odd_representable k hk

theorem representationNumber_eq (n : ℕ) (hn : 5 ≤ n) :
    Crown.representationNumber (Crown.crownGraph n) = Crown.halfCeil n := by
  have hrep := halfCeil_representable n hn
  exact Nat.le_antisymm (Crown.representationNumber_le hrep)
    (Crown.CrownLower.halfCeil_le_representationNumber hn ⟨_,hrep⟩)

#print axioms even_representable
#print axioms odd_representable
#print axioms halfCeil_representable
#print axioms representationNumber_eq

end Crown.CrownUpper
