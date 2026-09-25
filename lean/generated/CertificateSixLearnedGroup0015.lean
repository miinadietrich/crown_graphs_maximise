import generated.CertificateSixLearnedGroup0014

set_option Elab.async false
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
checked_lrat_direct_kernel Crown.CertificateSix Crown.CertificateSix.pairing6Formula 143377 143477
  (include_str "six_ancestry/formula.cnf")
  (include_str "six_ancestry/learned.cnf")
  (include_str "six_lrat_groups/group0015.lrat")

#print axioms Crown.CertificateSix.step_143476
