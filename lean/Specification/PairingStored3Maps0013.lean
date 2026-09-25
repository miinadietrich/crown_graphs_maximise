import Specification.PairingDefinitions
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0052 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 4 else 2)))) (by decide +kernel)

noncomputable def pairing0053 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 2 else 4)))) (by decide +kernel)

noncomputable def pairing0054 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 4 else 2)))) (by decide +kernel)

noncomputable def pairing0055 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 2 else 4)))) (by decide +kernel)

end Crown.CertificateSixData
