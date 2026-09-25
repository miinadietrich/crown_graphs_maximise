import Crown.CrownLowerCounts

/-! The closed-interval capacity bound in Lemma 3 of Glen--Kitaev--Pyatkin.
The split set consists of every unprimed crown vertex except one. -/

namespace Crown.CrownLower

local instance {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩
local instance {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

def leftExcept {n : ℕ} (z : Fin n) : Set (Bool × Fin n) :=
  {v | v.1 = false ∧ v.2 ≠ z}

instance {n : ℕ} (z : Fin n) : DecidablePred (· ∈ leftExcept z) :=
  fun v => inferInstanceAs (Decidable (v.1 = false ∧ v.2 ≠ z))

theorem avoiding_four {n : ℕ} (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ x : Fin n, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  classical
  have hsmall : ({a,b,c,d} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have hh := Finset.card_le_four (a := a) (b := b) (c := c) (d := d)
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  exact ⟨x,by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hx⟩

theorem leftExcept_has_other {n : ℕ} (hn : 4 ≤ n) (z : Fin n) :
    ∀ a ∈ leftExcept z, ∃ c ∈ leftExcept z, c ≠ a := by
  intro a ha
  obtain ⟨i,hiz,hia,_⟩ := Ranks.coordinate_avoiding_three hn z a.2 a.2
  exact ⟨(false,i),⟨rfl,hiz⟩,fun he => hia (congrArg Prod.snd he)⟩

theorem core_avoids_prime {n k : ℕ} (z : Fin n)
    (d : List (Bool × Fin n) × List (Bool × Fin n))
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hrep : Crown.Represents (Crown.crownGraph n) k (blockWord (d::D)))
    (hD : ∀ t ∈ d::D, GoodBlock (leftExcept z) t)
    (a b : Bool × Fin n) (ha : a ∈ leftExcept z) (hb : b ∈ leftExcept z) (hab : a ≠ b)
    (has : StartsIn (fun y => decide (y = a)) d.1)
    (hbe : EndsIn (fun y => decide (y = b)) d.1)
    (x : Fin n) (hxa : x ≠ a.2) (hxb : x ≠ b.2) : (true,x) ∉ d.1 := by
  have hnab : ¬ (Crown.crownGraph n).Adj a b := by
    change ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)
    simp [ha.1,hb.1]
  have hax : (Crown.crownGraph n).Adj a (true,x) := ⟨by simp [ha.1],Ne.symm hxa⟩
  have hxb' : (Crown.crownGraph n).Adj (true,x) b := ⟨by simp [hb.1],hxb⟩
  exact no_common_neighbour_in_first_core (leftExcept z) d D hrep hD a b (true,x)
    ha hb hab hnab has hbe hax hxb'

theorem core_missing_count_le_one {n k : ℕ} (hn : 4 ≤ n) (z : Fin n)
    (d : List (Bool × Fin n) × List (Bool × Fin n))
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hrep : Crown.Represents (Crown.crownGraph n) k (blockWord (d::D)))
    (hD : ∀ t ∈ d::D, GoodBlock (leftExcept z) t) : d.1.count (false,z) ≤ 1 := by
  classical
  obtain ⟨a,b,ha,hb,hab,has,hbe⟩ := goodBlock_endpoints (leftExcept z) d (hD d (by simp))
    (leftExcept_has_other hn z)
  obtain ⟨x,hxz,hxa,hxb⟩ := Ranks.coordinate_avoiding_three hn z a.2 b.2
  have hx := core_avoids_prime z d D hrep hD a b ha hb hab has hbe x hxa hxb
  have hed : (Crown.crownGraph n).Adj (false,z) (true,x) := ⟨by simp,Ne.symm hxz⟩
  have halt := (hrep.2.2 (false,z) (true,x) (by simp)).mp hed
  have hin : d.1 <:+: blockWord (d::D) :=
    ⟨[],d.2 ++ blockWord D,by simp [blockWord,List.append_assoc]⟩
  have hc := alternating_factor_count_le (false,z) (true,x) (by simp) _ d.1 halt hin
  simpa [List.count_eq_zero.mpr hx] using hc

/-- Every span beginning with the first core and ending with the last core
of t consecutive blocks has at most t occurrences of the missing letter.
Here the span has at least two blocks; the one-block case is above. -/
theorem prefix_span_missing_count_le {n k : ℕ} (hn : 5 ≤ n) (z : Fin n)
    (d e : List (Bool × Fin n) × List (Bool × Fin n))
    (T R : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hrep : Crown.Represents (Crown.crownGraph n) k (blockWord (d::(T ++ e::R))))
    (hD : ∀ t ∈ d::(T ++ e::R), GoodBlock (leftExcept z) t) :
    (blockWord (d::T) ++ e.1).count (false,z) ≤ T.length + 2 := by
  classical
  have hd := hD d (by simp)
  have he := hD e (by simp)
  obtain ⟨a,b,ha,hb,hab,has,hbe⟩ := goodBlock_endpoints (leftExcept z) d hd
    (leftExcept_has_other (by omega) z)
  obtain ⟨_,c,_,hc,_,_,hce⟩ := goodBlock_endpoints (leftExcept z) e he
    (leftExcept_has_other (by omega) z)
  obtain ⟨x,hxz,hxa,hxb,hxc⟩ := avoiding_four hn z a.2 b.2 c.2
  have hx := core_avoids_prime z d (T++e::R) hrep hD a b ha hb hab has hbe x hxa hxb
  let U := blockWord (d::T) ++ e.1
  have hin : U <:+: blockWord (d::(T++e::R)) :=
    ⟨[],e.2 ++ blockWord R,by simp [U,blockWord,List.flatMap_append,List.append_assoc]⟩
  have hadj : (Crown.crownGraph n).Adj c (true,x) := ⟨by simp [hc.1],Ne.symm hxc⟩
  have hne : c ≠ (true,x) := (Crown.crownGraph n).ne_of_adj hadj
  have hchain : Crown.Alternates U c (true,x) :=
    List.IsChain.infix ((hrep.2.2 c (true,x) hne).mp hadj) (List.IsInfix.filter _ hin)
  have hcmem : c ∈ d.1 := List.count_pos_iff.mp (by rw [goodBlock_core_count _ d hd c hc]; omega)
  have hhead : c ∈ (Crown.restrictPair U c (true,x)).head? := by
    have hu : U = d.1 ++ (d.2 ++ blockWord T ++ e.1) := by simp [U,blockWord,List.append_assoc]
    rw [hu,pair_head_of_prefix d.1 _ c (true,x) hcmem hx]
    simp
  have hlast : c ∈ (Crown.restrictPair U c (true,x)).getLast? := by
    obtain ⟨s,c',hs,hc'⟩ := hce
    have hcc : c' = c := by simpa using hc'
    subst c'
    simp [U,hs,Crown.restrictPair,List.filter_append,List.append_assoc]
  have hbalance := alternating_same_ends_count c (true,x) hne U hchain hhead hlast
  have hccount : U.count c = T.length + 2 := by
    have hpre : ∀ t ∈ d::T, GoodBlock (leftExcept z) t := by
      intro t ht
      rcases List.mem_cons.mp ht with ht | ht
      · exact ht ▸ hd
      · exact hD t (by simp [ht])
    change (blockWord (d::T) ++ e.1).count c = T.length + 2
    rw [List.count_append,goodBlocks_count _ (d::T) hpre c hc,goodBlock_core_count _ e he c hc]
    simp
  have hadjz : (Crown.crownGraph n).Adj (false,z) (true,x) := ⟨by simp,Ne.symm hxz⟩
  have hchainz := (hrep.2.2 (false,z) (true,x) (by simp)).mp hadjz
  have hbound := alternating_factor_count_le (false,z) (true,x) (by simp) _ U hchainz hin
  change U.count (false,z) ≤ T.length + 2
  omega

#print axioms core_missing_count_le_one
#print axioms prefix_span_missing_count_le

end Crown.CrownLower
