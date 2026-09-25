import Crown.CrownLowerFullSide

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def endpointLetters (D : List (List V × List V)) : List V :=
  D.flatMap (fun d => d.1.take 1 ++ d.1.reverse.take 1)

theorem endpointLetters_length (D : List (List V × List V)) :
    (endpointLetters D).length ≤ 2 * D.length := by
  induction D with
  | nil => simp [endpointLetters]
  | cons d D ih =>
    have h1 : (d.1.take 1).length ≤ 1 := by simp only [List.length_take]; omega
    have h2 : (d.1.reverse.take 1).length ≤ 1 := by simp only [List.length_take]; omega
    simp only [endpointLetters,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
    omega

theorem endpointLetters_mem (D : List (List V × List V))
    (d : List V × List V) (hd : d ∈ D) (a : V)
    (ha : StartsIn (fun x => decide (x = a)) d.1 ∨ EndsIn (fun x => decide (x = a)) d.1) :
    a ∈ endpointLetters D := by
  apply List.mem_flatMap.mpr
  refine ⟨d,hd,?_⟩
  rcases ha with ⟨b,t,hb,he⟩ | ⟨t,b,hb,he⟩
  · have hba : b = a := by simpa using he
    subst b
    simp [hb]
  · have hba : b = a := by simpa using he
    subst b
    simp [hb]

theorem alternating_constant_pairs (a b : V) (hab : a ≠ b) (L : List α) :
    (L.flatMap (fun _ => [a,b])).IsChain (· ≠ ·) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp [List.isChain_cons_cons,hab]
    | cons y L =>
      change (a::b::a::b::L.flatMap (fun _ => [a,b])).IsChain (· ≠ ·)
      exact List.isChain_cons_cons.mpr ⟨hab,List.isChain_cons_cons.mpr ⟨Ne.symm hab,ih⟩⟩

local instance {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩
local instance {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

theorem leftSide_has_other {n : ℕ} (hn : 4 ≤ n) :
    ∀ a ∈ leftSide n, ∃ c ∈ leftSide n, c ≠ a := by
  intro a ha
  obtain ⟨i,hia,_,_⟩ := Ranks.coordinate_avoiding_three hn a.2 a.2 a.2
  exact ⟨(false,i),rfl,fun he => hia (congrArg Prod.snd he)⟩

theorem prime_absent_core_of_no_endpoint {n k : ℕ} (hn : 4 ≤ n) (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hD : ∀ d ∈ D, GoodBlock (leftSide n) d)
    (hno : ∀ d ∈ D, ¬ StartsIn (fun v => decide (v = (false,z))) d.1 ∧
      ¬ EndsIn (fun v => decide (v = (false,z))) d.1) :
    ∀ d ∈ D, (true,z) ∉ d.1 := by
  intro d hd
  obtain ⟨P,Q,hPQ⟩ := List.mem_iff_append.mp hd
  have hrot : Crown.Represents (Crown.crownGraph n) k (blockWord (d::(Q++P))) := by
    simpa only [List.cons_append] using rotate_block_representation P (d::Q) (hPQ ▸ hr)
  have hgood : ∀ e ∈ d::(Q++P), GoodBlock (leftSide n) e := by
    intro e he
    exact hD e (by simpa [hPQ,List.mem_append,or_assoc,or_comm,or_left_comm] using he)
  obtain ⟨a,b,ha,hb,hab,has,hbe⟩ := goodBlock_endpoints (leftSide n) d (hD d hd)
    (leftSide_has_other hn)
  have haf : a.1 = false := ha
  have hbf : b.1 = false := hb
  have haz : a.2 ≠ z := by
    intro he
    have hea : a = (false,z) := Prod.ext haf he
    exact (hno d hd).1 (hea ▸ has)
  have hbz : b.2 ≠ z := by
    intro he
    have heb : b = (false,z) := Prod.ext hbf he
    exact (hno d hd).2 (heb ▸ hbe)
  have hnab : ¬ (Crown.crownGraph n).Adj a b := by
    change ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)
    simp [haf,hbf]
  have hax : (Crown.crownGraph n).Adj a (true,z) := ⟨by simp [haf],haz⟩
  have hxb : (Crown.crownGraph n).Adj (true,z) b := ⟨by simp [hbf],Ne.symm hbz⟩
  exact no_common_neighbour_in_first_core (leftSide n) d (Q++P) hrot hgood a b (true,z)
    ha hb hab hnab has hbe hax hxb

theorem gap_prime_count_le_one {n k : ℕ} (hn : 4 ≤ n) (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hD : ∀ d ∈ D, GoodBlock (leftSide n) d) :
    ∀ d ∈ D, d.2.count (true,z) ≤ 1 := by
  intro d hd
  obtain ⟨i,hiz,_,_⟩ := Ranks.coordinate_avoiding_three hn z z z
  have hi : (false,i) ∈ leftSide n := rfl
  have hc := goodBlock_gap_count (leftSide n) d (hD d hd) (false,i) hi
  obtain ⟨P,Q,hPQ⟩ := List.mem_iff_append.mp hd
  have hin : d.2 <:+: blockWord D :=
    ⟨blockWord P ++ d.1,blockWord Q,by simp [hPQ,blockWord,List.flatMap_append,List.append_assoc]⟩
  have hed : (Crown.crownGraph n).Adj (true,z) (false,i) := ⟨by simp,Ne.symm hiz⟩
  have halt := (hr.2.2 (true,z) (false,i) (by simp)).mp hed
  simpa [hc] using alternating_factor_count_le (true,z) (false,i) (by simp) _ d.2 halt hin

/-- Lemma 4 of Glen--Kitaev--Pyatkin: every unprimed letter is an endpoint
of a canonical permutation core. -/
theorem endpoint_coverage {n k : ℕ} (hn : 4 ≤ n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hlen : D.length = k) (hD : ∀ d ∈ D, GoodBlock (leftSide n) d) (z : Fin n) :
    ∃ d ∈ D, StartsIn (fun v => decide (v = (false,z))) d.1 ∨
      EndsIn (fun v => decide (v = (false,z))) d.1 := by
  classical
  by_contra h
  have hno : ∀ d ∈ D, ¬ StartsIn (fun v => decide (v = (false,z))) d.1 ∧
      ¬ EndsIn (fun v => decide (v = (false,z))) d.1 := by
    intro d hd
    exact ⟨fun hs => h ⟨d,hd,Or.inl hs⟩,fun he => h ⟨d,hd,Or.inr he⟩⟩
  have hcore := prime_absent_core_of_no_endpoint hn z D hr hD hno
  have hgap := gap_prime_count_le_one hn z D hr hD
  have hsum : (D.map (fun d => d.2.count (true,z))).sum = D.length := by
    have he := hr.2.1 (true,z)
    rw [blockWord,List.count_flatMap] at he
    have hm : D.map (fun d => (d.1 ++ d.2).count (true,z)) =
        D.map (fun d => d.2.count (true,z)) := by
      apply List.map_congr_left
      intro d hd
      simp [List.count_append,List.count_eq_zero.mpr (hcore d hd)]
    simpa only [Function.comp_def,hm,hlen] using he
  have hall := all_one_of_sum_eq_length (D.map (fun d => d.2.count (true,z)))
    (by intro m hm; obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm; exact hgap d hd)
    (by simpa only [List.length_map] using hsum)
  have hcell : ∀ d ∈ D, Crown.restrictPair (d.1 ++ d.2) (false,z) (true,z) = [(false,z),(true,z)] := by
    intro d hd
    have hfirst : Crown.restrictPair d.1 (false,z) (true,z) = [(false,z)] := by
      rw [Crown.restrictPair_comm,Blocks.restrictPair_of_not_mem_left _ (true,z) (false,z) (hcore d hd),
        List.filter_eq,goodBlock_core_count (leftSide n) d (hD d hd) (false,z) rfl]
      simp
    have hsecond : Crown.restrictPair d.2 (false,z) (true,z) = [(true,z)] := by
      have hnot : (false,z) ∉ d.2 := List.count_eq_zero.mp
        (goodBlock_gap_count (leftSide n) d (hD d hd) (false,z) rfl)
      rw [Blocks.restrictPair_of_not_mem_left _ (false,z) (true,z) hnot,List.filter_eq,
        hall _ (List.mem_map.mpr ⟨d,hd,rfl⟩)]
      simp
    rw [Crown.restrictPair_append,hfirst,hsecond]
    rfl
  have hrestriction : Crown.restrictPair (blockWord D) (false,z) (true,z) =
      D.flatMap (fun _ => [(false,z),(true,z)]) := by
    unfold Crown.restrictPair blockWord
    rw [List.filter_flatMap,List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro d hd
    exact hcell d hd
  have halt : Crown.Alternates (blockWord D) (false,z) (true,z) := by
    unfold Crown.Alternates
    rw [hrestriction]
    exact alternating_constant_pairs (false,z) (true,z) (by simp) D
  have hed := (hr.2.2 (false,z) (true,z) (by simp)).mpr halt
  exact hed.2 rfl

#print axioms endpoint_coverage

end Crown.CrownLower
