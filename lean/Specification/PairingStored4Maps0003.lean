import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0120 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0121 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0122 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0123 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0124 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0125 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0126 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0127 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0128 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0129 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0130 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0131 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0132 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0133 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0134 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0135 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0136 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0137 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0138 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0139 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0140 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0141 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0142 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0143 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0144 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0145 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0146 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0147 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0148 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0149 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0150 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0151 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0152 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0153 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0154 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0155 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0156 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0157 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0158 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0159 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)
end Crown.CertificateData
