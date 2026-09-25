import Crown.CrownLowerIntervals

/-! Canonical consecutive factors for a permutation-split word. The factors
are cut in the original word, not merely in its filtered subsequence. -/

namespace Crown.CrownLower

variable {V : Type*}

def StartsIn (p : V → Bool) (w : List V) : Prop :=
  ∃ a t, w = a::t ∧ p a = true

def EndsIn (p : V → Bool) (w : List V) : Prop :=
  ∃ t a, w = t ++ [a] ∧ p a = true

theorem startsIn_append (p : V → Bool) (u v : List V) (h : StartsIn p u) :
    StartsIn p (u ++ v) := by
  obtain ⟨a,t,rfl,ha⟩ := h
  exact ⟨a,t++v,rfl,ha⟩

theorem startsIn_of_append (p : V → Bool) (u v : List V) (hu : u ≠ [])
    (h : StartsIn p (u ++ v)) : StartsIn p u := by
  cases u with
  | nil => contradiction
  | cons a u =>
    obtain ⟨b,t,he,hb⟩ := h
    have hab : a = b := (List.cons.inj he).1
    exact ⟨a,u,rfl,by simpa [hab] using hb⟩

theorem first_selected_split (p : V → Bool) (w : List V) (hne : w.filter p ≠ []) :
    ∃ u v, w = u ++ v ∧ u.filter p = [] ∧ StartsIn p v := by
  obtain ⟨a,t,ht⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨u,v,hw,hu,ha,_⟩ := List.filter_eq_cons_iff.mp ht
  exact ⟨u,a::v,hw,by simpa only [List.filter_eq_nil_iff] using hu,⟨a,v,rfl,ha⟩⟩

theorem initial_permutation_blocks (p : V → Bool) (w : List V) (L : List (List V))
    (hne : L ≠ []) (hparts : ∀ l ∈ L, l ≠ []) (hf : w.filter p = L.flatten) :
    ∃ q : List V, ∃ W : List (List V), w = q ++ W.flatten ∧ q.filter p = [] ∧
      W.map (List.filter p) = L ∧ ∀ s ∈ W, StartsIn p s := by
  induction L generalizing w with
  | nil => contradiction
  | cons l L ih =>
    have hl : l ≠ [] := hparts l (by simp)
    have htail : ∀ t ∈ L, t ≠ [] := fun t ht => hparts t (by simp [ht])
    have hfa : w.filter p = l ++ L.flatten := hf
    obtain ⟨u,v,hw,hu,hv⟩ := List.filter_eq_append_iff.mp hfa
    obtain ⟨q,r,hur,hq,hr⟩ := first_selected_split p u (by rw [hu]; exact hl)
    have hrf : r.filter p = l := by simpa [hur,hq] using hu
    cases L with
    | nil =>
      have hv0 : v.filter p = [] := by simpa using hv
      refine ⟨q,[r++v],?_,hq,?_,?_⟩
      · simp [hw,hur,List.append_assoc]
      · simp [hrf,hv0]
      · simpa using startsIn_append p r v hr
    | cons t L =>
      obtain ⟨s,W,hvw,hs,hW,hstart⟩ := ih v (by simp) htail hv
      refine ⟨q,(r++s)::W,?_,hq,?_,?_⟩
      · simp [hw,hur,hvw,List.append_assoc]
      · simp [hrf,hs,hW]
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact startsIn_append p r s hr
        · exact hstart a ha

theorem append_last_blocks (p : V → Bool) (W : List (List V)) (q : List V)
    (hne : W ≠ []) (hq : q.filter p = []) (hstart : ∀ s ∈ W, StartsIn p s) :
    ∃ W' : List (List V), W'.flatten = W.flatten ++ q ∧ W'.map (List.filter p) = W.map (List.filter p) ∧
      ∀ s ∈ W', StartsIn p s := by
  induction W with
  | nil => contradiction
  | cons w W ih =>
    have hw := hstart w (by simp)
    cases W with
    | nil =>
      exact ⟨[w++q],by simp,by simp [hq],by simpa using startsIn_append p w q hw⟩
    | cons t W =>
      obtain ⟨W',he,hm,hs⟩ := ih (by simp) (fun s h => hstart s (by simp [h]))
      exact ⟨w::W',by simp [he,List.append_assoc],by simp [hm],by simpa using And.intro hw hs⟩

theorem canonical_permutation_blocks (p : V → Bool) (w : List V) (L : List (List V))
    (hne : L ≠ []) (hparts : ∀ l ∈ L, l ≠ []) (hf : w.filter p = L.flatten) :
    ∃ q u : List V, ∃ W : List (List V), w = q ++ u ∧
      W.flatten = u ++ q ∧ W.map (List.filter p) = L ∧ ∀ s ∈ W, StartsIn p s := by
  obtain ⟨q,W,hw,hq,hm,hs⟩ := initial_permutation_blocks p w L hne hparts hf
  have hWne : W ≠ [] := by intro he; simp [he] at hm; exact hne hm
  obtain ⟨W',he,hm',hs'⟩ := append_last_blocks p W q hWne hq hs
  exact ⟨q,W.flatten,W',hw,he,hm'.trans hm,hs'⟩

theorem ending_core (p : V → Bool) (w : List V) (hne : w.filter p ≠ []) :
    ∃ c g : List V, w = c ++ g ∧ g.filter p = [] ∧ c ≠ [] ∧ EndsIn p c := by
  induction w with
  | nil => simp at hne
  | cons a w ih =>
    by_cases hw : w.filter p = []
    · have ha : p a = true := by
        cases hpa : p a <;> simp_all
      exact ⟨[a],w,rfl,hw,by simp,⟨[],a,rfl,ha⟩⟩
    · obtain ⟨c,g,hcg,hg,hc,he⟩ := ih hw
      obtain ⟨t,b,hcb,hb⟩ := he
      exact ⟨a::c,g,by simp [hcg],hg,by simp,⟨a::t,b,by simp [hcb],hb⟩⟩

theorem core_and_gap (p : V → Bool) (w : List V) (hs : StartsIn p w) :
    ∃ c g : List V, w = c ++ g ∧ c.filter p = w.filter p ∧ g.filter p = [] ∧
      StartsIn p c ∧ EndsIn p c := by
  have hne : w.filter p ≠ [] := by
    obtain ⟨a,t,rfl,ha⟩ := hs
    simp [ha]
  obtain ⟨c,g,hw,hg,hc,he⟩ := ending_core p w hne
  exact ⟨c,g,hw,by simp [hw,hg],hg,startsIn_of_append p c g hc (hw ▸ hs),he⟩

#print axioms canonical_permutation_blocks
#print axioms core_and_gap

end Crown.CrownLower
