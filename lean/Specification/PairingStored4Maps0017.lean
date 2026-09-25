import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0680 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0681 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0682 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0683 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0684 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0685 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0686 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def pairing0687 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def pairing0688 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0689 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0690 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0691 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0692 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0693 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0694 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0695 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0696 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0697 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0698 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0699 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0700 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0701 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0702 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0703 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0704 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0705 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0706 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0707 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0708 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0709 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0710 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0711 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0712 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0713 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0714 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0715 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0716 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0717 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0718 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0719 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)
end Crown.CertificateData
