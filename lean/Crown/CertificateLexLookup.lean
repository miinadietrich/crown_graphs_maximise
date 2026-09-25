import Crown.CertificateGateData

/-! Keep semantic Boolean values opaque while checking concrete variable
indices. Each lookup is first a small equality of variable descriptors. -/
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation

theorem positive_of_descriptor (s : Fin 256 → Bool) (n : Nat) (v : Variable)
    (h : descriptor n = v) : literalValue (assignment s) (.pos n) = value s v := by
  exact congrArg (value s) h

theorem positive_lex_of_descriptor (s : Fin 256 → Bool) (n : Nat)
    (d : Fin 8 ≃ Fin 8) (i : Fin 256) (h : descriptor n = .lex d i) :
    literalValue (assignment s) (.pos n) = lexAfter s d i :=
  positive_of_descriptor s n (.lex d i) h

theorem positive_select (s : Fin 256 → Bool) (i : Fin 256) :
    literalValue (assignment s) (.pos i.val) = s i := assignment_select s i

theorem negative_falsum (s : Fin 256 → Bool) :
    literalValue (assignment s) (.neg 256) = true := by
  change Bool.not (assignment s 256) = true
  rw [assignment_falsum]
  rfl

#print axioms positive_of_descriptor
#print axioms positive_lex_of_descriptor
#print axioms positive_select
#print axioms negative_falsum
end Crown.CertificateData
