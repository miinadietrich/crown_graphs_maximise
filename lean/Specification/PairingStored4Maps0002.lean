import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0080 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0081 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0082 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0083 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0084 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0085 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0086 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0087 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0088 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0089 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0090 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0091 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0092 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0093 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0094 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0095 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0096 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0097 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0098 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0099 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0100 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0101 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0102 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0103 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0104 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0105 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0106 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0107 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0108 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0109 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0110 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0111 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0112 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0113 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0114 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0115 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0116 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0117 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0118 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0119 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)
end Crown.CertificateData
