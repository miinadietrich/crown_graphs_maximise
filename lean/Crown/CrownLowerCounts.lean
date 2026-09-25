import Crown.CrownLowerCore

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem goodBlock_core_count (A : Set V) [DecidablePred (· ∈ A)]
    (d : List V × List V) (hd : GoodBlock A d) (a : V) (ha : a ∈ A) : d.1.count a = 1 := by
  have h := List.count_eq_one_of_mem hd.1.1 ((hd.1.2 a).mpr ha)
  rw [List.count_filter (p := fun x => decide (x ∈ A)) (a := a) (by simpa using ha)] at h
  exact h

theorem goodBlock_gap_count (A : Set V) [DecidablePred (· ∈ A)]
    (d : List V × List V) (hd : GoodBlock A d) (a : V) (ha : a ∈ A) : d.2.count a = 0 := by
  have h := congrArg (List.count a) hd.2.1
  rw [List.count_filter (p := fun x => decide (x ∈ A)) (a := a) (by simpa using ha)] at h
  simpa using h

theorem goodBlocks_count (A : Set V) [DecidablePred (· ∈ A)]
    (D : List (List V × List V)) (hD : ∀ d ∈ D, GoodBlock A d) (a : V) (ha : a ∈ A) :
    (blockWord D).count a = D.length := by
  induction D with
  | nil => simp [blockWord]
  | cons d D ih =>
    have hd := hD d (by simp)
    have ht := ih (fun d hd => hD d (by simp [hd]))
    change ((d.1 ++ d.2) ++ blockWord D).count a = (d::D).length
    rw [List.count_append,List.count_append,goodBlock_core_count A d hd a ha,
      goodBlock_gap_count A d hd a ha,ht]
    simp [Nat.add_comm]

theorem nodup_endpoints_ne (l : List V) (hn : l.Nodup) (a b : V)
    (hs : StartsIn (fun x => decide (x = a)) l) (he : EndsIn (fun x => decide (x = b)) l)
    (hother : ∃ c ∈ l, c ≠ a) : a ≠ b := by
  intro hab
  subst b
  obtain ⟨a',s,hs,ha'⟩ := hs
  have haa : a' = a := by simpa using ha'
  subst a'
  obtain ⟨t,b,he,hb⟩ := he
  have hba : b = a := by simpa using hb
  subst b
  cases t with
  | nil =>
    obtain ⟨c,hc,hca⟩ := hother
    simp [he] at hc
    exact hca hc
  | cons x t =>
    have hcons : a::s = x::(t++[a]) := by simpa [hs] using he
    have htail : s = t++[a] := (List.cons.inj hcons).2
    have hnot : a ∉ s := (List.nodup_cons.mp (hs ▸ hn)).1
    exact hnot (by simp [htail])

theorem goodBlock_endpoints (A : Set V) [DecidablePred (· ∈ A)]
    (d : List V × List V) (hd : GoodBlock A d)
    (hA : ∀ a ∈ A, ∃ c ∈ A, c ≠ a) :
    ∃ a b : V, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧
      StartsIn (fun x => decide (x = a)) d.1 ∧ EndsIn (fun x => decide (x = b)) d.1 := by
  obtain ⟨a,s,hs,ha⟩ := hd.2.2.1
  obtain ⟨t,b,he,hb⟩ := hd.2.2.2
  have haA : a ∈ A := by simpa using ha
  have hbA : b ∈ A := by simpa using hb
  have hs' : StartsIn (fun x => decide (x = a)) (d.1.filter (fun x => x ∈ A)) :=
    ⟨a,s.filter (fun x => x ∈ A),by simp [hs,haA],by simp⟩
  have he' : EndsIn (fun x => decide (x = b)) (d.1.filter (fun x => x ∈ A)) :=
    ⟨t.filter (fun x => x ∈ A),b,by simp [he,hbA],by simp⟩
  have hab : a ≠ b := by
    apply nodup_endpoints_ne _ hd.1.1 a b hs' he'
    obtain ⟨c,hc,hca⟩ := hA a haA
    exact ⟨c,(hd.1.2 c).mpr hc,hca⟩
  exact ⟨a,b,haA,hbA,hab,⟨a,s,hs,by simp⟩,⟨t,b,he,by simp⟩⟩

#print axioms goodBlocks_count
#print axioms goodBlock_endpoints

end Crown.CrownLower
