import generated.ThreeClosureData
namespace Crown.ThreeClosure
/-- Index a contiguous interval of the complete 2,517-state certificate. -/
def rangeIndex (start count : Nat) (h : start + count ≤ 2517) (i : Fin count) : Fin 2517 :=
  ⟨start + i.val, by omega⟩
end Crown.ThreeClosure
