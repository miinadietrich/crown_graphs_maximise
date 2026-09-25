import generated.PairingStored3Data

namespace Crown.PairingStored3
open Crown.PairingCoordinates Crown.PairingCoverage Crown.Matchings Crown.MatchingRepresentatives
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem inverse_0040 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0040) = 40 := by decide +kernel
private theorem anchor_0040 : Crown.CertificateSixData.pairing0040 (0,false) = 0 := by decide +kernel
private theorem inverse_0041 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0041) = 41 := by decide +kernel
private theorem anchor_0041 : Crown.CertificateSixData.pairing0041 (0,false) = 0 := by decide +kernel
private theorem inverse_0042 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0042) = 42 := by decide +kernel
private theorem anchor_0042 : Crown.CertificateSixData.pairing0042 (0,false) = 0 := by decide +kernel
private theorem inverse_0043 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0043) = 43 := by decide +kernel
private theorem anchor_0043 : Crown.CertificateSixData.pairing0043 (0,false) = 0 := by decide +kernel
private theorem inverse_0044 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0044) = 44 := by decide +kernel
private theorem anchor_0044 : Crown.CertificateSixData.pairing0044 (0,false) = 0 := by decide +kernel
private theorem inverse_0045 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0045) = 45 := by decide +kernel
private theorem anchor_0045 : Crown.CertificateSixData.pairing0045 (0,false) = 0 := by decide +kernel
private theorem inverse_0046 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0046) = 46 := by decide +kernel
private theorem anchor_0046 : Crown.CertificateSixData.pairing0046 (0,false) = 0 := by decide +kernel
private theorem inverse_0047 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0047) = 47 := by decide +kernel
private theorem anchor_0047 : Crown.CertificateSixData.pairing0047 (0,false) = 0 := by decide +kernel
private theorem inverse_0048 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0048) = 48 := by decide +kernel
private theorem anchor_0048 : Crown.CertificateSixData.pairing0048 (0,false) = 0 := by decide +kernel
private theorem inverse_0049 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0049) = 49 := by decide +kernel
private theorem anchor_0049 : Crown.CertificateSixData.pairing0049 (0,false) = 0 := by decide +kernel
private theorem inverse_0050 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0050) = 50 := by decide +kernel
private theorem anchor_0050 : Crown.CertificateSixData.pairing0050 (0,false) = 0 := by decide +kernel
private theorem inverse_0051 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0051) = 51 := by decide +kernel
private theorem anchor_0051 : Crown.CertificateSixData.pairing0051 (0,false) = 0 := by decide +kernel
private theorem inverse_0052 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0052) = 52 := by decide +kernel
private theorem anchor_0052 : Crown.CertificateSixData.pairing0052 (0,false) = 0 := by decide +kernel
private theorem inverse_0053 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0053) = 53 := by decide +kernel
private theorem anchor_0053 : Crown.CertificateSixData.pairing0053 (0,false) = 0 := by decide +kernel
private theorem inverse_0054 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0054) = 54 := by decide +kernel
private theorem anchor_0054 : Crown.CertificateSixData.pairing0054 (0,false) = 0 := by decide +kernel
private theorem inverse_0055 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0055) = 55 := by decide +kernel
private theorem anchor_0055 : Crown.CertificateSixData.pairing0055 (0,false) = 0 := by decide +kernel
private theorem inverse_0056 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0056) = 56 := by decide +kernel
private theorem anchor_0056 : Crown.CertificateSixData.pairing0056 (0,false) = 0 := by decide +kernel
private theorem inverse_0057 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0057) = 57 := by decide +kernel
private theorem anchor_0057 : Crown.CertificateSixData.pairing0057 (0,false) = 0 := by decide +kernel
private theorem inverse_0058 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0058) = 58 := by decide +kernel
private theorem anchor_0058 : Crown.CertificateSixData.pairing0058 (0,false) = 0 := by decide +kernel
private theorem inverse_0059 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0059) = 59 := by decide +kernel
private theorem anchor_0059 : Crown.CertificateSixData.pairing0059 (0,false) = 0 := by decide +kernel

theorem inverse_batch0002 (r : Fin 20) :
    inverseFingerprint (fingerprint (stored ⟨40+r.val,by omega⟩)) = ⟨40+r.val,by omega⟩ := by
  fin_cases r
  · exact inverse_0040
  · exact inverse_0041
  · exact inverse_0042
  · exact inverse_0043
  · exact inverse_0044
  · exact inverse_0045
  · exact inverse_0046
  · exact inverse_0047
  · exact inverse_0048
  · exact inverse_0049
  · exact inverse_0050
  · exact inverse_0051
  · exact inverse_0052
  · exact inverse_0053
  · exact inverse_0054
  · exact inverse_0055
  · exact inverse_0056
  · exact inverse_0057
  · exact inverse_0058
  · exact inverse_0059

theorem anchor_batch0002 (r : Fin 20) :
    stored ⟨40+r.val,by omega⟩ (0,false) = 0 := by
  fin_cases r
  · exact anchor_0040
  · exact anchor_0041
  · exact anchor_0042
  · exact anchor_0043
  · exact anchor_0044
  · exact anchor_0045
  · exact anchor_0046
  · exact anchor_0047
  · exact anchor_0048
  · exact anchor_0049
  · exact anchor_0050
  · exact anchor_0051
  · exact anchor_0052
  · exact anchor_0053
  · exact anchor_0054
  · exact anchor_0055
  · exact anchor_0056
  · exact anchor_0057
  · exact anchor_0058
  · exact anchor_0059
#print axioms inverse_batch0002
#print axioms anchor_batch0002
end Crown.PairingStored3
