import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0760 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0761 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0762 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0763 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0764 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0765 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0766 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0767 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0768 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0769 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0770 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0771 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0772 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0773 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0774 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0775 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0776 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0777 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0778 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0779 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0780 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0781 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0782 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0783 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0784 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0785 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0786 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0787 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0788 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0789 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0790 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0791 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0792 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0793 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0794 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0795 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0796 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0797 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0798 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0799 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)
end Crown.CertificateData
