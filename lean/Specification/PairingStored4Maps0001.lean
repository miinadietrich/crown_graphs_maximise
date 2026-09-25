import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0040 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0041 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0042 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0043 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0044 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0045 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0046 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0047 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0048 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0049 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0050 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0051 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0052 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0053 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0054 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0055 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0056 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0057 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0058 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0059 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0060 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0061 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0062 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0063 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0064 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0065 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0066 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0067 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0068 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0069 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0070 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0071 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0072 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0073 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0074 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0075 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0076 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0077 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0078 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0079 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)
end Crown.CertificateData
