import Crown.Words

namespace Crown

def crownWord1 : List (Bool × Fin 1) :=
  [(false,0), (false,0), (true,0), (true,0)]

def crownWord2 : List (Bool × Fin 2) :=
  [(false,0), (true,1), (false,0), (true,1),
   (false,1), (true,0), (false,1), (true,0)]

def crownWord3 : List (Bool × Fin 3) :=
  [(false,0), (true,2), (true,1), (false,0), (false,2), (true,1),
   (true,0), (false,2), (false,1), (true,0), (true,2), (false,1)]

def crownWord4 : List (Bool × Fin 4) :=
  [(false,0), (true,1), (false,1), (true,2), (true,3), (false,0),
   (true,0), (false,1), (false,2), (true,3), (false,3), (true,0),
   (true,1), (false,2), (true,2), (false,3), (false,1), (false,0),
   (true,0), (true,3), (true,2), (true,1), (false,3), (false,2)]

theorem crownWord1_represents : Represents (crownGraph 1) 2 crownWord1 := by
  unfold Represents Uniform Alternates crownGraph restrictPair crownWord1
  decide
theorem crownWord2_represents : Represents (crownGraph 2) 2 crownWord2 := by
  unfold Represents Uniform Alternates crownGraph restrictPair crownWord2
  decide
theorem crownWord3_represents : Represents (crownGraph 3) 2 crownWord3 := by
  unfold Represents Uniform Alternates crownGraph restrictPair crownWord3
  decide
theorem crownWord4_represents : Represents (crownGraph 4) 3 crownWord4 := by
  unfold Represents Uniform Alternates crownGraph restrictPair crownWord4
  decide

theorem crown_two_le (n : ℕ) (hn : 1 ≤ n) (hr : Representable (crownGraph n)) :
    2 ≤ representationNumber (crownGraph n) := by
  let i : Fin n := ⟨0, by omega⟩
  apply two_le_representationNumber_of_nonedge hr
    (a := (false, i)) (b := (true, i))
  · simp
  · simp [crownGraph]

theorem crown_one_value : Representable (crownGraph 1) ∧
    representationNumber (crownGraph 1) = 2 := by
  have hw : KRepresentable (crownGraph 1) 2 := ⟨_, crownWord1_represents⟩
  have hr : Representable (crownGraph 1) := ⟨2, hw⟩
  exact ⟨hr, Nat.le_antisymm (representationNumber_le hw) (crown_two_le 1 (by decide) hr)⟩

theorem crown_two_value : Representable (crownGraph 2) ∧
    representationNumber (crownGraph 2) = 2 := by
  have hw : KRepresentable (crownGraph 2) 2 := ⟨_, crownWord2_represents⟩
  have hr : Representable (crownGraph 2) := ⟨2, hw⟩
  exact ⟨hr, Nat.le_antisymm (representationNumber_le hw) (crown_two_le 2 (by decide) hr)⟩

theorem crown_three_value : Representable (crownGraph 3) ∧
    representationNumber (crownGraph 3) = 2 := by
  have hw : KRepresentable (crownGraph 3) 2 := ⟨_, crownWord3_represents⟩
  have hr : Representable (crownGraph 3) := ⟨2, hw⟩
  exact ⟨hr, Nat.le_antisymm (representationNumber_le hw) (crown_two_le 3 (by decide) hr)⟩

theorem crown_four_upper : Representable (crownGraph 4) ∧
    representationNumber (crownGraph 4) ≤ 3 := by
  have hw : KRepresentable (crownGraph 4) 3 := ⟨_, crownWord4_represents⟩
  exact ⟨⟨3, hw⟩, representationNumber_le hw⟩

#print axioms crown_one_value
#print axioms crown_two_value
#print axioms crown_three_value
#print axioms crown_four_upper

end Crown
