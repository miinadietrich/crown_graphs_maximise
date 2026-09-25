import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0280 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0281 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0282 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0283 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0284 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0285 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0286 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0287 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0288 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0289 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0290 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0291 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0292 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0293 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0294 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0295 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0296 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0297 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0298 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0299 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0300 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0301 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0302 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def pairing0303 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def pairing0304 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0305 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0306 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0307 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0308 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0309 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0310 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def pairing0311 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def pairing0312 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0313 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0314 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0315 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0316 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0317 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0318 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0319 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)
end Crown.CertificateData
