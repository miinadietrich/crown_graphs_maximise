import Crown.CrownFourFiniteData

namespace Crown.CrownFourFinite

theorem obstruction_length_eight (w : List (Fin 4)) (hlen : w.length = 8) : Obstructed w := by
  let f : Fin 8 → Fin 4 := fun i => w[i.val]'(by simpa [hlen] using i.isLt)
  have hf : List.ofFn f = w := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [← hf]
  change Obstructed [f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7]
  exact all_words _ _ _ _ _ _ _ _

#print axioms all_words
#print axioms obstruction_length_eight

end Crown.CrownFourFinite
