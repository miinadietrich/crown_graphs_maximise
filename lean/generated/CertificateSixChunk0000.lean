import generated.CertificateReplaySix

namespace Crown.CertificateSix
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
checked_cnf_formula_six pairing6Formula
  (include_str "six_ancestry/formula.cnf")
end Crown.CertificateSix
