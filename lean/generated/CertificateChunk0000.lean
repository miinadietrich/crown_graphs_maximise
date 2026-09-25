import generated.CertificateReplay

namespace Crown.Certificate

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
checked_cnf_formula pairing8Formula
  (include_str "../data/pairing8.cnf")

end Crown.Certificate
