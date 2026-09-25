import Crown.CrownLowerCanonical

/-! Canonical factors P_i I_i in the original representing word. Each core
starts and ends in the split set, and each intervening factor avoids it. -/

namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def GoodBlock (A : Set V) [DecidablePred (· ∈ A)] (d : List V × List V) : Prop :=
  IsPermutationOf A (d.1.filter (fun a => a ∈ A)) ∧
    d.2.filter (fun a => a ∈ A) = [] ∧
    StartsIn (fun a => decide (a ∈ A)) d.1 ∧ EndsIn (fun a => decide (a ∈ A)) d.1

def blockWord (D : List (List V × List V)) : List V := D.flatMap (fun d => d.1 ++ d.2)

theorem decompose_good_blocks (A : Set V) [DecidablePred (· ∈ A)] (W : List (List V))
    (hperm : ∀ w ∈ W, IsPermutationOf A (w.filter (fun a => a ∈ A)))
    (hstart : ∀ w ∈ W, StartsIn (fun a => decide (a ∈ A)) w) :
    ∃ D : List (List V × List V), blockWord D = W.flatten ∧ D.length = W.length ∧
      ∀ d ∈ D, GoodBlock A d := by
  induction W with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons w W ih =>
    obtain ⟨c,g,hw,hc,hg,hcs,hce⟩ := core_and_gap _ w (hstart w (by simp))
    obtain ⟨D,hD,hlen,hgood⟩ := ih (fun w hw => hperm w (by simp [hw]))
      (fun w hw => hstart w (by simp [hw]))
    refine ⟨(c,g)::D,?_,by simpa using hlen,?_⟩
    · simp [blockWord,hw,← hD]
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨hc.symm ▸ hperm w (by simp),hg,hcs,hce⟩
      · exact hgood d hd

theorem canonical_representation {G : SimpleGraph V} {k : ℕ} {w : List V}
    (hrep : Crown.Represents G k w) (A : Set V) [DecidablePred (· ∈ A)] (hA : A.Nonempty)
    (hsplit : Splittable w k A) :
    ∃ D : List (List V × List V), Crown.Represents G k (blockWord D) ∧ D.length = k ∧
      ∀ d ∈ D, GoodBlock A d := by
  classical
  obtain ⟨u,v,L,hw,hfilter,hlen,hperm⟩ := hsplit
  have hrot : Crown.Represents G k (v++u) := Crown.represents_append_swap (hw ▸ hrep)
  have hk := hrep.1
  have hne : L ≠ [] := by intro he; simp [he] at hlen; omega
  have hparts : ∀ l ∈ L, l ≠ [] := by
    intro l hl he
    obtain ⟨a,ha⟩ := hA
    have hm := ((hperm l hl).2 a).mpr ha
    simpa [he] using hm
  have hfilter' : (v++u).filter (fun a => decide (a ∈ A)) = L.flatten := by
    calc
      _ = (v++u).filter (fun a => @decide (a ∈ A) (Classical.propDecidable _)) := by
        apply List.filter_congr
        intro a ha
        simp
      _ = L.flatten := hfilter
  obtain ⟨q,t,W,hwt,hW,hmap,hstart⟩ := canonical_permutation_blocks
    (fun a => decide (a ∈ A)) (v++u) L hne hparts hfilter'
  have hrot' : Crown.Represents G k W.flatten := by
    rw [hW]
    exact Crown.represents_append_swap (hwt ▸ hrot)
  have hpermW : ∀ s ∈ W, IsPermutationOf A (s.filter (fun a => a ∈ A)) := by
    intro s hs
    apply hperm
    rw [← hmap]
    exact List.mem_map.mpr ⟨s,hs,rfl⟩
  obtain ⟨D,hD,hDL,hgood⟩ := decompose_good_blocks A W hpermW hstart
  refine ⟨D,hD ▸ hrot',?_,hgood⟩
  have hWL : W.length = L.length := by rw [← hmap,List.length_map]
  omega

theorem rotate_block_representation {G : SimpleGraph V} {k : ℕ}
    (P Q : List (List V × List V)) (hrep : Crown.Represents G k (blockWord (P++Q))) :
    Crown.Represents G k (blockWord (Q++P)) := by
  simp only [blockWord,List.flatMap_append] at hrep ⊢
  exact Crown.represents_append_swap hrep

#print axioms canonical_representation

end Crown.CrownLower
