import generated.CatalogueConverseStored

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem catalogueUnion_iff_minimal (M : Finset (Fin 256)) :
    M ∈ catalogueUnion ↔ ∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M := by
  rw [minimalMask_exists_iff_stored Crown.PairingStored4.stored Crown.PairingStored4.complete]
  change M ∈ catalogueUnion ↔ ∃ t, MinimalMaskFamily (pairingRows (pairings t)) M
  simp only [catalogueUnion,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_image,List.mem_toFinset,minimal_mask_iff_stored_template]

#print axioms catalogueUnion_iff_minimal
end Crown.CertificateData
