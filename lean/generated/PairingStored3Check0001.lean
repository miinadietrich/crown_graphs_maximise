import generated.PairingStored3Data

namespace Crown.PairingStored3
open Crown.PairingCoordinates Crown.PairingCoverage Crown.Matchings Crown.MatchingRepresentatives
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem inverse_0020 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0020) = 20 := by decide +kernel
private theorem anchor_0020 : Crown.CertificateSixData.pairing0020 (0,false) = 0 := by decide +kernel
private theorem inverse_0021 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0021) = 21 := by decide +kernel
private theorem anchor_0021 : Crown.CertificateSixData.pairing0021 (0,false) = 0 := by decide +kernel
private theorem inverse_0022 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0022) = 22 := by decide +kernel
private theorem anchor_0022 : Crown.CertificateSixData.pairing0022 (0,false) = 0 := by decide +kernel
private theorem inverse_0023 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0023) = 23 := by decide +kernel
private theorem anchor_0023 : Crown.CertificateSixData.pairing0023 (0,false) = 0 := by decide +kernel
private theorem inverse_0024 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0024) = 24 := by decide +kernel
private theorem anchor_0024 : Crown.CertificateSixData.pairing0024 (0,false) = 0 := by decide +kernel
private theorem inverse_0025 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0025) = 25 := by decide +kernel
private theorem anchor_0025 : Crown.CertificateSixData.pairing0025 (0,false) = 0 := by decide +kernel
private theorem inverse_0026 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0026) = 26 := by decide +kernel
private theorem anchor_0026 : Crown.CertificateSixData.pairing0026 (0,false) = 0 := by decide +kernel
private theorem inverse_0027 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0027) = 27 := by decide +kernel
private theorem anchor_0027 : Crown.CertificateSixData.pairing0027 (0,false) = 0 := by decide +kernel
private theorem inverse_0028 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0028) = 28 := by decide +kernel
private theorem anchor_0028 : Crown.CertificateSixData.pairing0028 (0,false) = 0 := by decide +kernel
private theorem inverse_0029 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0029) = 29 := by decide +kernel
private theorem anchor_0029 : Crown.CertificateSixData.pairing0029 (0,false) = 0 := by decide +kernel
private theorem inverse_0030 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0030) = 30 := by decide +kernel
private theorem anchor_0030 : Crown.CertificateSixData.pairing0030 (0,false) = 0 := by decide +kernel
private theorem inverse_0031 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0031) = 31 := by decide +kernel
private theorem anchor_0031 : Crown.CertificateSixData.pairing0031 (0,false) = 0 := by decide +kernel
private theorem inverse_0032 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0032) = 32 := by decide +kernel
private theorem anchor_0032 : Crown.CertificateSixData.pairing0032 (0,false) = 0 := by decide +kernel
private theorem inverse_0033 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0033) = 33 := by decide +kernel
private theorem anchor_0033 : Crown.CertificateSixData.pairing0033 (0,false) = 0 := by decide +kernel
private theorem inverse_0034 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0034) = 34 := by decide +kernel
private theorem anchor_0034 : Crown.CertificateSixData.pairing0034 (0,false) = 0 := by decide +kernel
private theorem inverse_0035 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0035) = 35 := by decide +kernel
private theorem anchor_0035 : Crown.CertificateSixData.pairing0035 (0,false) = 0 := by decide +kernel
private theorem inverse_0036 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0036) = 36 := by decide +kernel
private theorem anchor_0036 : Crown.CertificateSixData.pairing0036 (0,false) = 0 := by decide +kernel
private theorem inverse_0037 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0037) = 37 := by decide +kernel
private theorem anchor_0037 : Crown.CertificateSixData.pairing0037 (0,false) = 0 := by decide +kernel
private theorem inverse_0038 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0038) = 38 := by decide +kernel
private theorem anchor_0038 : Crown.CertificateSixData.pairing0038 (0,false) = 0 := by decide +kernel
private theorem inverse_0039 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0039) = 39 := by decide +kernel
private theorem anchor_0039 : Crown.CertificateSixData.pairing0039 (0,false) = 0 := by decide +kernel

theorem inverse_batch0001 (r : Fin 20) :
    inverseFingerprint (fingerprint (stored ⟨20+r.val,by omega⟩)) = ⟨20+r.val,by omega⟩ := by
  fin_cases r
  · exact inverse_0020
  · exact inverse_0021
  · exact inverse_0022
  · exact inverse_0023
  · exact inverse_0024
  · exact inverse_0025
  · exact inverse_0026
  · exact inverse_0027
  · exact inverse_0028
  · exact inverse_0029
  · exact inverse_0030
  · exact inverse_0031
  · exact inverse_0032
  · exact inverse_0033
  · exact inverse_0034
  · exact inverse_0035
  · exact inverse_0036
  · exact inverse_0037
  · exact inverse_0038
  · exact inverse_0039

theorem anchor_batch0001 (r : Fin 20) :
    stored ⟨20+r.val,by omega⟩ (0,false) = 0 := by
  fin_cases r
  · exact anchor_0020
  · exact anchor_0021
  · exact anchor_0022
  · exact anchor_0023
  · exact anchor_0024
  · exact anchor_0025
  · exact anchor_0026
  · exact anchor_0027
  · exact anchor_0028
  · exact anchor_0029
  · exact anchor_0030
  · exact anchor_0031
  · exact anchor_0032
  · exact anchor_0033
  · exact anchor_0034
  · exact anchor_0035
  · exact anchor_0036
  · exact anchor_0037
  · exact anchor_0038
  · exact anchor_0039
#print axioms inverse_batch0001
#print axioms anchor_batch0001
end Crown.PairingStored3
