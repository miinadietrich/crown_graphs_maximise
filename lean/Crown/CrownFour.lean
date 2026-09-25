import Crown.CrownFourFinite
import Crown.CrownFourIntervals
import Crown.SmallCrowns

/-! The four-crown requires multiplicity three. The finite obstruction
concerns all labelled eight-letter words; the interval bridge below is proved
for the actual representing word, without a normalization assumption. -/

namespace Crown.CrownFour

local instance : BEq (Fin 4) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Fin 4) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp
local instance : BEq (Bool × Fin 4) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Bool × Fin 4) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

def leftWord (w : List (Bool × Fin 4)) : List (Fin 4) :=
  w.filterMap fun v => if v.1 then none else some v.2

theorem map_leftWord (w : List (Bool × Fin 4)) :
    (leftWord w).map (fun i => (false,i)) = w.filter (fun v => !v.1) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rcases v with ⟨b,i⟩
    cases b <;> simp [leftWord] at ih ⊢ <;> exact ih

theorem count_leftWord (w : List (Bool × Fin 4)) (i : Fin 4) :
    (leftWord w).count i = w.count (false,i) := by
  have hinj : Function.Injective (fun i : Fin 4 => (false,i)) := by
    intro a b h
    exact congrArg Prod.snd h
  rw [← List.count_map_of_injective (leftWord w) _ hinj, map_leftWord]
  exact List.count_filter (by simp)

theorem alternates_leftWord (w : List (Bool × Fin 4)) (a b : Fin 4) :
    Crown.Alternates (leftWord w) a b ↔ Crown.Alternates w (false,a) (false,b) := by
  have hinj : Function.Injective (fun i : Fin 4 => (false,i)) := by
    intro a b h
    exact congrArg Prod.snd h
  rw [← Crown.alternates_map _ hinj, map_leftWord]
  unfold Crown.Alternates
  have he : w.filter (fun v => !v.1) = w.filter (fun v => decide (v.1 = false)) := by
    apply List.filter_congr
    intro v _
    cases v.1 <;> rfl
  rw [he,Crown.restrictPair_filter (fun v : Bool × Fin 4 => v.1 = false) w
    (false,a) (false,b) rfl rfl]

theorem interval_parameters {w s : List (Fin 4)} (hlen : w.length = 8)
    (hs : s <:+: w) :
    ∃ lo len : Fin 9, (w.drop lo.val).take len.val = s := by
  obtain ⟨p,q,he⟩ := hs
  have hp : p.length < 9 := by
    have hh := congrArg List.length he
    simp only [List.length_append] at hh
    omega
  have hl : s.length < 9 := by
    have hh := congrArg List.length he
    simp only [List.length_append] at hh
    omega
  refine ⟨⟨p.length,hp⟩,⟨s.length,hl⟩,?_⟩
  rw [← he]
  simp [List.append_assoc]

theorem not_two_representable : ¬Crown.KRepresentable (Crown.crownGraph 4) 2 := by
  rintro ⟨w,hw⟩
  have hu : Crown.Uniform 2 (leftWord w) := by
    intro i
    exact (count_leftWord w i).trans (hw.2.1 (false,i))
  have hl : (leftWord w).length = 8 := by
    simpa using Crown.uniform_length hu
  have hn : ∀ a b : Fin 4, a ≠ b → ¬Crown.Alternates (leftWord w) a b := by
    intro a b hab ha
    have hh := (hw.2.2 (false,a) (false,b) (by simpa using hab)).mpr
      ((alternates_leftWord w a b).mp ha)
    simpa [Crown.crownGraph] using hh
  obtain ⟨z,hz⟩ := Crown.CrownFourFinite.obstruction_length_eight (leftWord w) hl hu hn
  obtain ⟨s,hs,hi⟩ := Crown.CrownFourIntervals.two_occurrence_interval w hw (true,z)
  have hsub : leftWord s <:+: leftWord w := hs.filterMap _
  obtain ⟨lo,len,he⟩ := interval_parameters hl hsub
  apply hz lo len
  intro i
  rw [he,count_leftWord]
  have hh := hi (false,i) (by simp)
  simpa [Crown.crownGraph,ne_comm] using hh.symm

theorem representationNumber_eq : Crown.representationNumber (Crown.crownGraph 4) = 3 := by
  obtain ⟨hr,hu⟩ := Crown.crown_four_upper
  have hl := Crown.crown_two_le 4 (by decide) hr
  have hn : Crown.representationNumber (Crown.crownGraph 4) ≠ 2 := by
    intro he
    exact not_two_representable (he ▸ Crown.representationNumber_spec hr)
  omega

#print axioms not_two_representable
#print axioms representationNumber_eq

end Crown.CrownFour
