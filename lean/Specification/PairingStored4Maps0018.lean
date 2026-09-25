import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0720 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0721 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0722 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0723 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0724 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0725 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0726 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0727 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0728 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0729 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0730 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0731 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0732 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0733 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0734 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0735 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0736 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0737 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0738 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0739 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0740 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0741 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0742 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0743 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0744 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0745 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0746 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0747 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0748 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0749 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0750 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0751 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0752 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0753 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0754 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0755 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0756 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0757 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0758 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0759 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)
end Crown.CertificateData
