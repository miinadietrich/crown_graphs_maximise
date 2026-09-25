import Crown.CrownLowerProjection

/-! The full unprimed side is splittable for crowns of order at least ten.
The source's greedy allocation is implemented by the checked minimum-prefix
rotation and the literal list allocation in CrownLowerAllocation. -/

namespace Crown.CrownLower

local instance {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩
local instance {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

theorem count_project_word {n : ℕ} (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hD : ∀ d ∈ D, GoodBlock (leftExcept z) d) :
    (allocationWord (false,z) (D.map (projectBlock z))).count (false,z) =
      (blockWord D).count (false,z) := by
  rw [allocationWord_project z D hD]
  exact List.count_filter (by simp)

theorem insert_leftExcept {n : ℕ} (z : Fin n) :
    insert (false,z) (leftExcept z) = leftSide n := by
  ext v
  rcases v with ⟨b,i⟩
  cases b <;> by_cases hi : i = z <;> simp [leftExcept,leftSide,hi]

theorem full_side_permutations {n k : ℕ} (hn : 5 ≤ n) (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hlen : D.length = k) (hD : ∀ d ∈ D, GoodBlock (leftExcept z) d)
    (hnonneg : ∀ P, P <+: D → 0 ≤ weightSum (blockWeight (false,z)) P) :
    ∃ L : List (List (Bool × Fin n)),
      (blockWord D).filter (fun v => v.1 = false) = L.flatten ∧
      L.length = k ∧ ∀ l ∈ L, IsPermutationOf (leftSide n) l := by
  classical
  have hperm : ∀ d ∈ D.map (projectBlock z),
      IsPermutationOf (leftExcept z) (d.1.filter (fun v => v ≠ (false,z))) := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    simpa only [projectBlock,filter_left_except] using (hD e he).1
  have ht : 0 + (allocationWord (false,z) (D.map (projectBlock z))).count (false,z) =
      (D.map (projectBlock z)).length := by
    rw [Nat.zero_add,count_project_word z D hD,List.length_map,hlen,hr.2.1]
  have hlo : ∀ P, P <+: D.map (projectBlock z) →
      P.length ≤ 0 + (allocationWord (false,z) P).count (false,z) := by
    intro P hP
    obtain ⟨P',hP',rfl⟩ := List.prefix_map_iff.mp hP
    have hpGood : ∀ d ∈ P', GoodBlock (leftExcept z) d :=
      fun d hd => hD d (hP'.subset hd)
    rw [Nat.zero_add,List.length_map,count_project_word z P' hpGood]
    have hh := hnonneg P' hP'
    rw [weightSum_blockWeight] at hh
    omega
  have hup : ∀ P d R, D.map (projectBlock z) = P ++ d::R →
      0 + (allocationWord (false,z) P ++ d.1).count (false,z) ≤ P.length + 1 := by
    intro P d R heq
    obtain ⟨P',S,hDS,hP,hS⟩ := List.map_eq_append_iff.mp heq
    obtain ⟨e,R',hS',he,hR⟩ := List.map_eq_cons_iff.mp hS
    have hDe : D = P' ++ e::R' := by simpa [hS'] using hDS
    subst P
    subst d
    have hpGood : ∀ d ∈ P', GoodBlock (leftExcept z) d := by
      intro d hd
      exact hD d (by simp [hDe,hd])
    simp only [Nat.zero_add,List.count_append,List.length_map,projectBlock]
    rw [count_project_word z P' hpGood,
      List.count_filter (p := fun v : Bool × Fin n => decide (v.1 = false)) (by simp)]
    have hh := closed_prefix_capacity hn z P' e R' (hDe ▸ hr)
      (fun e he => hD e (by simpa only [hDe] using he))
    simpa only [List.count_append] using hh
  obtain ⟨L,hL,hLL,hLP⟩ := allocate_missing (leftExcept z) (false,z)
    (by simp [leftExcept]) (D.map (projectBlock z)) 0 hperm ht hlo hup
  refine ⟨L,?_,by simpa [hlen] using hLL,?_⟩
  · simpa [allocationWord_project z D hD] using hL
  · simpa only [insert_leftExcept z] using hLP

/-- Lemma 3 of Glen--Kitaev--Pyatkin, in an existence form sufficient for
all representation-number lower bounds. The resulting word represents the
same crown with the same multiplicity. -/
theorem exists_full_side_split {n k : ℕ} (hn : 5 ≤ n) (w : List (Bool × Fin n))
    (hw : Crown.Represents (Crown.crownGraph n) k w) :
    ∃ w', Crown.Represents (Crown.crownGraph n) k w' ∧ Splittable w' k (leftSide n) := by
  classical
  let z : Fin n := ⟨0,by omega⟩
  have hN : {v | (Crown.crownGraph n).Adj (true,z) v} = leftExcept z := by
    apply Set.ext
    rintro ⟨b,i⟩
    change (true ≠ b ∧ z ≠ i) ↔ (b = false ∧ i ≠ z)
    cases b
    · exact ⟨fun h => ⟨rfl,Ne.symm h.2⟩,fun h => ⟨by decide,Ne.symm h.2⟩⟩
    · simp
  have hsplit : Splittable w k (leftExcept z) :=
    hN ▸ neighbourhood_splittable hw (true,z)
  obtain ⟨i,hiz,_,_⟩ := Ranks.coordinate_avoiding_three (by omega) z z z
  have hA : (leftExcept z).Nonempty := ⟨(false,i),rfl,hiz⟩
  obtain ⟨D,hDrep,hDlen,hDgood⟩ := canonical_representation hw (leftExcept z) hA hsplit
  have hzero : weightSum (blockWeight (false,z)) D = 0 := by
    rw [weightSum_blockWeight,hDrep.2.1,hDlen]
    omega
  obtain ⟨P,Q,hDQ,hmin⟩ := exists_nonnegative_rotation (blockWeight (false,z)) D hzero
  have hrot := rotate_block_representation P Q (hDQ ▸ hDrep)
  have hlen : (Q++P).length = k := by simpa [hDQ,List.length_append,Nat.add_comm] using hDlen
  have hgood : ∀ d ∈ Q++P, GoodBlock (leftExcept z) d := by
    intro d hd
    exact hDgood d (by simpa [hDQ,List.mem_append,or_comm] using hd)
  obtain ⟨L,hL,hLL,hLP⟩ := full_side_permutations hn z (Q++P) hrot hlen hgood hmin
  refine ⟨blockWord (Q++P),hrot,[],blockWord (Q++P),L,by simp,?_,hLL,hLP⟩
  simp only [List.append_nil]
  calc
    _ = (blockWord (Q++P)).filter (fun v => v.1 = false) := by
      apply List.filter_congr
      intro v hv
      by_cases hf : v.1 = false <;> simp [leftSide,hf]
    _ = L.flatten := hL

#print axioms full_side_permutations
#print axioms exists_full_side_split

end Crown.CrownLower
