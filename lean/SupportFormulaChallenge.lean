import Specification.FormulaAssignment

import Specification.SixFormulaAssignment

import Specification.CatalogueTemplates

import Specification.SixCatalogueTemplates

import generated.CertificateChunk0000

import generated.CertificateSixChunk0000

namespace Crown.CertificateData

open Crown.CertificateSemantics 

theorem frozen_formula_satisfied
    (s : Fin 256 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 8)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s)
    (hcores : ∀ t : Fin 840, ∃ c ∈ templates t, ∀ m ∈ cores c, s m = true)
    : (valuation (assignment s)).satisfies_fmla Crown.Certificate.pairing8Formula := by
  sorry

end Crown.CertificateData

namespace Crown.CertificateSixData

open Crown.CertificateSemantics Crown.CertificateSixSemantics

theorem reduced_formula_satisfied
    (s : Fin 64 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 6)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s)
    (hcores : ∀ t : Fin 60, ∃ c ∈ templates t, ∀ m ∈ cores c, s m = true)
    : (valuation (assignment s)).satisfies_fmla Crown.CertificateSix.pairing6Formula := by
  sorry

end Crown.CertificateSixData
