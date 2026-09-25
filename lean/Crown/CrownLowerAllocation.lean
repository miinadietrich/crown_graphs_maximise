import Crown.CrownLowerCycle

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem permutation_insert_of_count (A : Set V) (z : V) (hz : z ∉ A) (l : List V)
    (hp : IsPermutationOf A (l.filter (fun a => a ≠ z))) (hc : l.count z = 1) :
    IsPermutationOf (insert z A) l := by
  have hcount : ∀ a, l.count a ≤ 1 := by
    intro a
    by_cases haz : a = z
    · simpa [haz,hc]
    · have hh := List.nodup_iff_count_le_one.mp hp.1 a
      rwa [List.count_filter (p := fun x => decide (x ≠ z)) (a := a) (by simpa using haz)] at hh
  refine ⟨List.nodup_iff_count_le_one.mpr hcount,?_⟩
  intro a
  by_cases haz : a = z
  · subst a
    simp only [Set.mem_insert_iff, true_or, iff_true]
    exact List.count_pos_iff.mp (by omega)
  · have hh := hp.2 a
    simpa [List.mem_filter,haz] using hh

def allocationWord (z : V) (D : List (List V × ℕ)) : List V :=
  D.flatMap (fun d => d.1 ++ List.replicate d.2 z)

@[simp] theorem allocationWord_nil (z : V) : allocationWord z [] = [] := rfl
@[simp] theorem allocationWord_cons (z : V) (d : List V × ℕ) (D : List (List V × ℕ)) :
    allocationWord z (d::D) = d.1 ++ List.replicate d.2 z ++ allocationWord z D := rfl
@[simp] theorem allocationWord_append (z : V) (D E : List (List V × ℕ)) :
    allocationWord z (D++E) = allocationWord z D ++ allocationWord z E := by
  simp [allocationWord,List.flatMap_append]

/-- Allocation of the missing letter. The two prefix inequalities are exactly
closed-core capacity and nonnegative open-block balance. -/
theorem allocate_missing (A : Set V) (z : V) (hz : z ∉ A)
    (D : List (List V × ℕ)) (r : ℕ)
    (hperm : ∀ d ∈ D, IsPermutationOf A (d.1.filter (fun a => a ≠ z)))
    (htotal : r + (allocationWord z D).count z = D.length)
    (hlower : ∀ P, P <+: D → P.length ≤ r + (allocationWord z P).count z)
    (hupper : ∀ P d R, D = P ++ d::R →
      r + (allocationWord z P ++ d.1).count z ≤ P.length + 1) :
    ∃ L : List (List V), List.replicate r z ++ allocationWord z D = L.flatten ∧
      L.length = D.length ∧ ∀ l ∈ L, IsPermutationOf (insert z A) l := by
  induction D generalizing r with
  | nil =>
    have hr : r = 0 := by simpa using htotal
    exact ⟨[],by simp [hr],rfl,by simp⟩
  | cons d D ih =>
    have hsmall : r + d.1.count z ≤ 1 := by simpa using hupper [] d D rfl
    have hlarge : 1 ≤ r + d.1.count z + d.2 := by
      simpa [List.count_append,Nat.add_assoc] using hlower [d] (by simp)
    let t := 1 - (r + d.1.count z)
    let r' := d.2 - t
    have htr : t + r' = d.2 := by dsimp [t,r']; omega
    have hone : r + d.1.count z + t = 1 := by dsimp [t]; omega
    have hbalance : r + d.1.count z + d.2 = 1 + r' := by omega
    let l := List.replicate r z ++ d.1 ++ List.replicate t z
    have hl : IsPermutationOf (insert z A) l := by
      apply permutation_insert_of_count A z hz l
      · simpa [l,List.filter_append] using hperm d (by simp)
      · simp only [l,List.count_append,List.count_replicate_self]
        exact hone
    have ht' : r' + (allocationWord z D).count z = D.length := by
      simp only [allocationWord_cons,List.count_append,List.count_replicate_self,List.length_cons] at htotal
      omega
    have hlo' : ∀ P, P <+: D → P.length ≤ r' + (allocationWord z P).count z := by
      intro P hP
      have hh := hlower (d::P) (List.cons_prefix_cons.mpr ⟨rfl,hP⟩)
      simp only [allocationWord_cons,List.count_append,List.count_replicate_self,List.length_cons] at hh
      omega
    have hup' : ∀ P e R, D = P ++ e::R →
        r' + (allocationWord z P ++ e.1).count z ≤ P.length + 1 := by
      intro P e R he
      have hh := hupper (d::P) e R (by simp [he])
      simp only [allocationWord_cons,List.count_append,List.count_replicate_self,List.length_cons] at hh ⊢
      omega
    obtain ⟨L,hL,hlen,hLp⟩ := ih r' (fun d hd => hperm d (by simp [hd])) ht' hlo' hup'
    refine ⟨l::L,?_,by simp [hlen],?_⟩
    · simp only [List.flatten_cons,← hL,l,allocationWord_cons]
      rw [show d.2 = t + r' from htr.symm,List.replicate_add]
      simp only [List.replicate_add,List.append_assoc]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hl
      · exact hLp q hq

#print axioms allocate_missing

end Crown.CrownLower
