import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0640 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0641 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0642 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0643 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0644 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0645 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0646 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0647 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0648 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0649 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0650 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0651 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0652 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0653 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0654 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0655 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0656 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0657 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0658 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0659 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0660 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0661 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0662 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0663 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0664 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0665 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0666 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0667 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0668 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0669 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0670 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0671 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0672 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0673 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0674 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0675 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0676 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0677 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0678 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0679 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)
end Crown.CertificateData
