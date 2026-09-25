import generated.CatalogueConverseUnion

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_obstruction_union_count :
    Nat.card {M : Finset (Fin 256) //
      ∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M} = 4935 := by
  simp_rw [← catalogueUnion_iff_minimal]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using catalogue_union_count

#print axioms minimal_obstruction_union_count
end Crown.CertificateData
