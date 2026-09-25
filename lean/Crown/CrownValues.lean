import Crown.CrownUpper
import Crown.CrownFour
import Crown.GraphBasics

namespace Crown

/-- Exact crown values at every positive part size, including all small cases. -/
theorem crown_representation_number (n : ℕ) (hn : 1 ≤ n) :
    Representable (crownGraph n) ∧ representationNumber (crownGraph n) = crownValue n := by
  by_cases hlarge : 5 ≤ n
  · refine ⟨⟨halfCeil n, CrownUpper.halfCeil_representable n hlarge⟩, ?_⟩
    simpa [crownValue, show ¬n ≤ 3 by omega, show n ≠ 4 by omega]
      using CrownUpper.representationNumber_eq n hlarge
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa [crownValue] using crown_one_value
    · simpa [crownValue] using crown_two_value
    · simpa [crownValue] using crown_three_value
    · exact ⟨crown_four_upper.1, CrownFour.representationNumber_eq⟩

/-- The crown attains its minimum positive uniform length for every n>=5. -/
theorem crown_minimum_uniform_length (n : ℕ) (hn : 5 ≤ n) :
    ∃ w, Represents (crownGraph n) (halfCeil n) w ∧
      w.length = (2*n)*halfCeil n ∧
      ∀ k u, Represents (crownGraph n) k u → w.length ≤ u.length := by
  have hr : Representable (crownGraph n) := ⟨_, CrownUpper.halfCeil_representable n hn⟩
  simpa only [CrownUpper.representationNumber_eq n hn, crown_card] using
    minimum_uniform_length hr

#print axioms crown_representation_number
#print axioms crown_minimum_uniform_length
end Crown
