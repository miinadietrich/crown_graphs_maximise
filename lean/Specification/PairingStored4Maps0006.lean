import Specification.PairingDefinitions
namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def pairing0240 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0241 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0242 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0243 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0244 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0245 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0246 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0247 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0248 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0249 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0250 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0251 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0252 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0253 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0254 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0255 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0256 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0257 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0258 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0259 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0260 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0261 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0262 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def pairing0263 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def pairing0264 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0265 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0266 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0267 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0268 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0269 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0270 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def pairing0271 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def pairing0272 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0273 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0274 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0275 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0276 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0277 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def pairing0278 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def pairing0279 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)
end Crown.CertificateData
