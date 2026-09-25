import generated.CertificateSixFormulaKernelAggregate
namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
theorem reduced_formula_satisfied
    (s : Fin 64 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 6)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s)
    (hcores : ∀ t : Fin 60, ∃ c ∈ templates t, ∀ m ∈ cores c, s m = true)
    : (valuation (assignment s)).satisfies_fmla Crown.CertificateSix.pairing6Formula :=
  kernel_reduced_formula_satisfied s hcard hmax hcores
#print axioms reduced_formula_satisfied
end Crown.CertificateSixData
