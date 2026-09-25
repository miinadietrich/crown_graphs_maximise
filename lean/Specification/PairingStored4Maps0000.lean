import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0000 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0001 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0002 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0003 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0004 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0005 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0006 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0007 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0008 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0009 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0010 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0011 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0012 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0013 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0014 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0015 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0016 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0017 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0018 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0019 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 3 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0020 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0021 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0022 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0023 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0024 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0025 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0026 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0027 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0028 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0029 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0030 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0031 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0032 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0033 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0034 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0035 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0036 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0037 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0038 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0039 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)
end Crown.CertificateData
