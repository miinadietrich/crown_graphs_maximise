import generated.CertificateSixLearnedGroup0030

set_option Elab.async false
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
checked_lrat_direct_kernel Crown.CertificateSix Crown.CertificateSix.pairing6Formula 144977 145077
  (include_str "six_ancestry/formula.cnf")
  (include_str "six_ancestry/learned.cnf")
  (include_str "six_lrat_groups/group0031.lrat")

#print axioms Crown.CertificateSix.step_145076
