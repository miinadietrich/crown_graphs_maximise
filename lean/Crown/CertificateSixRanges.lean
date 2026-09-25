import Crown.CertificateAssembly
namespace Crown.CertificateSixAssembly

def fixedOnRange (image : Fin 64 → Fin 64) (lo hi : Nat) : Bool :=
  (List.range' lo (hi-lo)).all (fun n =>
    if hn : n < 64 then decide (image ⟨n, hn⟩ = ⟨n, hn⟩) else true)

theorem fixedOnRange_spec (image : Fin 64 → Fin 64) (lo hi : Nat)
    (h : fixedOnRange image lo hi = true) (j : Fin 64)
    (hl : lo ≤ j.val) (hu : j.val < hi) : image j = j := by
  rw [fixedOnRange, List.all_eq_true] at h
  have hj : j.val ∈ List.range' lo (hi-lo) := by
    apply List.mem_range'.mpr
    exact ⟨j.val-lo, by omega, by omega⟩
  simpa only [dif_pos j.isLt, decide_eq_true_eq] using h j.val hj

end Crown.CertificateSixAssembly
