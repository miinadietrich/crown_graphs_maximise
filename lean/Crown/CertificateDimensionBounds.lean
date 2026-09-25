import Crown.CertificateDimensionData

namespace Crown.Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem frozen_variables_bounded :
    pairing8Formula.all (fun c => (c : List Sat.Literal).all
      (fun l => decide (variableIndex l < 10116))) = true := by decide +kernel

#print axioms frozen_variables_bounded

end Crown.Certificate
