import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0520 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0521 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0522 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0523 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0524 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0525 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0526 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0527 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0528 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0529 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0530 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0531 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0532 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0533 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0534 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0535 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0536 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0537 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0538 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0539 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0540 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0541 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0542 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0543 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0544 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0545 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0546 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0547 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0548 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0549 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0550 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0551 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0552 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0553 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0554 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0555 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0556 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0557 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0558 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0559 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)
end Crown.CertificateData
