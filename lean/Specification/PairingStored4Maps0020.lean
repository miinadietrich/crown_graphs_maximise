import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0800 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0801 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0802 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0803 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0804 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0805 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0806 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def pairing0807 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def pairing0808 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0809 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0810 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0811 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0812 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0813 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0814 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0815 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0816 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0817 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0818 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0819 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0820 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0821 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0822 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def pairing0823 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def pairing0824 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0825 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0826 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0827 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0828 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0829 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0830 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def pairing0831 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def pairing0832 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0833 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0834 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0835 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0836 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0837 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def pairing0838 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def pairing0839 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)
end Crown.CertificateData
