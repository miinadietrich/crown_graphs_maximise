import generated.CertificateSixChunk0001
import generated.CertificateSixOriginal0142
import generated.CertificateReplayDirectKernel

set_option Elab.async false
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
checked_lrat_direct_kernel Crown.CertificateSix Crown.CertificateSix.pairing6Formula 141952 141977
  (include_str "six_ancestry/formula.cnf")
  (include_str "six_ancestry/learned.cnf")
  (include_str "six_lrat/part0002.lrat")
