import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0320 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0321 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0322 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0323 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0324 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0325 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0326 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0327 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0328 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0329 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0330 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0331 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0332 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0333 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0334 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0335 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0336 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0337 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0338 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0339 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0340 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0341 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0342 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0343 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0344 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0345 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0346 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0347 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0348 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0349 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0350 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0351 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0352 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0353 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0354 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0355 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0356 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0357 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0358 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0359 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)
end Crown.CertificateData
