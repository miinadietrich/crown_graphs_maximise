import Crown.CertificateSixGateData

/-! Keep semantic Boolean values opaque while checking concrete variable
indices. Each lookup is first a small equality of variable descriptors. -/
namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation

theorem positive_of_descriptor (s : Fin 64 → Bool) (n : Nat) (v : Variable)
    (h : descriptor n = v) : literalValue (assignment s) (.pos n) = value s v := by
  exact congrArg (value s) h

theorem positive_lex_of_descriptor (s : Fin 64 → Bool) (n : Nat)
    (d : Fin 6 ≃ Fin 6) (i : Fin 64) (h : descriptor n = .lex d i) :
    literalValue (assignment s) (.pos n) = lexAfter s d i :=
  positive_of_descriptor s n (.lex d i) h

theorem positive_select (s : Fin 64 → Bool) (i : Fin 64) :
    literalValue (assignment s) (.pos i.val) = s i := assignment_select s i

theorem negative_falsum (s : Fin 64 → Bool) :
    literalValue (assignment s) (.neg 64) = true := by
  change Bool.not (assignment s 64) = true
  rw [assignment_falsum]
  rfl

#print axioms positive_of_descriptor
#print axioms positive_lex_of_descriptor
#print axioms positive_select
#print axioms negative_falsum
end Crown.CertificateSixData
