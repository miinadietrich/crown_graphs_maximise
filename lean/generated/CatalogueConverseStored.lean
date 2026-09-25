import Crown.CatalogueCaseDispatch
import generated.CatalogueConverseDispatch0000
import generated.CatalogueConverseDispatch0001
import generated.CatalogueConverseDispatch0002
import generated.CatalogueConverseDispatch0003
import generated.CatalogueConverseDispatch0004
import generated.CatalogueConverseDispatch0005
import generated.CatalogueConverseDispatch0006
import generated.CatalogueConverseDispatch0007
import generated.CatalogueConverseDispatch0008
import generated.CatalogueConverseDispatch0009
import generated.CatalogueConverseDispatch0010
import generated.CatalogueConverseDispatch0011
import generated.CatalogueConverseDispatch0012
import generated.CatalogueConverseDispatch0013
import generated.CatalogueConverseDispatch0014
import generated.CatalogueConverseDispatch0015
import generated.CatalogueConverseDispatch0016
import generated.CatalogueConverseDispatch0017
import generated.CatalogueConverseDispatch0018
import generated.CatalogueConverseDispatch0019
import generated.CatalogueConverseDispatch0020

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template (t : Fin 840) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings t)) M ↔
      ∃ c ∈ templates t, (cores c).toFinset = M := by
  have hall : ∀ (b : Fin 21) (r : Fin 40), MinimalMaskFamily (pairingRows (pairings (⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ : Fin 840))) M ↔ ∃ c ∈ templates (⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
    apply Crown.CatalogueCaseDispatch.forall_fin21
    · intro r
      exact minimal_mask_iff_stored_template_block0000 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0001 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0002 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0003 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0004 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0005 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0006 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0007 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0008 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0009 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0010 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0011 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0012 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0013 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0014 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0015 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0016 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0017 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0018 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0019 r M
    · intro r
      exact minimal_mask_iff_stored_template_block0020 r M
  let b : Fin 21 := ⟨t.val/40,by omega⟩
  let r : Fin 40 := ⟨t.val%40,by omega⟩
  have ht : t = ⟨40*b.val+r.val,by have hb := b.isLt; have hr := r.isLt; omega⟩ := by
    apply Fin.ext
    dsimp [b,r]
    omega
  have h := hall b r
  rw [←ht] at h
  exact h

#print axioms minimal_mask_iff_stored_template
end Crown.CertificateData
