import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0160 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0161 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0162 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0163 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0164 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0165 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0166 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0167 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0168 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0169 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0170 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0171 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0172 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0173 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0174 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0175 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0176 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0177 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0178 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0179 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0180 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0181 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0182 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0183 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0184 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0185 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0186 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0187 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0188 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0189 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0190 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0191 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0192 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0193 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0194 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0195 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0196 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0197 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0198 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0199 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)
end Crown.CertificateData
