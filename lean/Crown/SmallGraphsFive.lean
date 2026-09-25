import Crown.SmallGraphsFiveChecks
namespace Crown.SmallGraphs
theorem all_five_masks (m : Fin 1024) : Crown.Represents (graph 5 m.val) 2 (wordsFive.getD m.val []) := by
  have hq : m.val / 64 < 16 := by omega
  have hr : m.val % 64 < 64 := Nat.mod_lt _ (by decide)
  have h := five_tables_indexed ⟨m.val / 64,hq⟩ ⟨m.val % 64,hr⟩
  have he : m.val % 64 + m.val / 64 * 64 = m.val := by omega
  simpa only [he] using h
theorem all_five (G : SimpleGraph (Fin 5)) : Crown.KRepresentable G 2 := by
  obtain ⟨m,hm⟩ := encode_graph 5 G
  have hlen : (pairs 5).length = 10 := by decide
  have hm' : m.val < 1024 := by simpa [hlen] using m.isLt
  rw [← hm]
  exact ⟨_,all_five_masks ⟨m.val,hm'⟩⟩
#print axioms all_five_masks
#print axioms all_five
end Crown.SmallGraphs
