import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0480 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0481 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0482 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0483 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0484 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0485 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0486 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0487 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0488 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0489 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0490 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0491 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0492 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0493 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0494 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0495 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0496 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0497 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0498 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0499 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0500 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0501 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0502 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0503 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0504 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0505 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0506 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0507 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0508 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0509 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0510 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0511 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0512 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0513 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0514 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0515 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0516 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0517 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0518 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0519 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)
end Crown.CertificateData
