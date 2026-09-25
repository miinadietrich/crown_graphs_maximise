import generated.PairingStored3Data

namespace Crown.PairingStored3
open Crown.PairingCoordinates Crown.PairingCoverage Crown.Matchings Crown.MatchingRepresentatives
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem inverse_0000 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0000) = 0 := by decide +kernel
private theorem anchor_0000 : Crown.CertificateSixData.pairing0000 (0,false) = 0 := by decide +kernel
private theorem inverse_0001 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0001) = 1 := by decide +kernel
private theorem anchor_0001 : Crown.CertificateSixData.pairing0001 (0,false) = 0 := by decide +kernel
private theorem inverse_0002 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0002) = 2 := by decide +kernel
private theorem anchor_0002 : Crown.CertificateSixData.pairing0002 (0,false) = 0 := by decide +kernel
private theorem inverse_0003 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0003) = 3 := by decide +kernel
private theorem anchor_0003 : Crown.CertificateSixData.pairing0003 (0,false) = 0 := by decide +kernel
private theorem inverse_0004 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0004) = 4 := by decide +kernel
private theorem anchor_0004 : Crown.CertificateSixData.pairing0004 (0,false) = 0 := by decide +kernel
private theorem inverse_0005 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0005) = 5 := by decide +kernel
private theorem anchor_0005 : Crown.CertificateSixData.pairing0005 (0,false) = 0 := by decide +kernel
private theorem inverse_0006 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0006) = 6 := by decide +kernel
private theorem anchor_0006 : Crown.CertificateSixData.pairing0006 (0,false) = 0 := by decide +kernel
private theorem inverse_0007 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0007) = 7 := by decide +kernel
private theorem anchor_0007 : Crown.CertificateSixData.pairing0007 (0,false) = 0 := by decide +kernel
private theorem inverse_0008 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0008) = 8 := by decide +kernel
private theorem anchor_0008 : Crown.CertificateSixData.pairing0008 (0,false) = 0 := by decide +kernel
private theorem inverse_0009 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0009) = 9 := by decide +kernel
private theorem anchor_0009 : Crown.CertificateSixData.pairing0009 (0,false) = 0 := by decide +kernel
private theorem inverse_0010 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0010) = 10 := by decide +kernel
private theorem anchor_0010 : Crown.CertificateSixData.pairing0010 (0,false) = 0 := by decide +kernel
private theorem inverse_0011 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0011) = 11 := by decide +kernel
private theorem anchor_0011 : Crown.CertificateSixData.pairing0011 (0,false) = 0 := by decide +kernel
private theorem inverse_0012 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0012) = 12 := by decide +kernel
private theorem anchor_0012 : Crown.CertificateSixData.pairing0012 (0,false) = 0 := by decide +kernel
private theorem inverse_0013 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0013) = 13 := by decide +kernel
private theorem anchor_0013 : Crown.CertificateSixData.pairing0013 (0,false) = 0 := by decide +kernel
private theorem inverse_0014 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0014) = 14 := by decide +kernel
private theorem anchor_0014 : Crown.CertificateSixData.pairing0014 (0,false) = 0 := by decide +kernel
private theorem inverse_0015 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0015) = 15 := by decide +kernel
private theorem anchor_0015 : Crown.CertificateSixData.pairing0015 (0,false) = 0 := by decide +kernel
private theorem inverse_0016 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0016) = 16 := by decide +kernel
private theorem anchor_0016 : Crown.CertificateSixData.pairing0016 (0,false) = 0 := by decide +kernel
private theorem inverse_0017 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0017) = 17 := by decide +kernel
private theorem anchor_0017 : Crown.CertificateSixData.pairing0017 (0,false) = 0 := by decide +kernel
private theorem inverse_0018 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0018) = 18 := by decide +kernel
private theorem anchor_0018 : Crown.CertificateSixData.pairing0018 (0,false) = 0 := by decide +kernel
private theorem inverse_0019 : inverseFingerprint (fingerprint Crown.CertificateSixData.pairing0019) = 19 := by decide +kernel
private theorem anchor_0019 : Crown.CertificateSixData.pairing0019 (0,false) = 0 := by decide +kernel

theorem inverse_batch0000 (r : Fin 20) :
    inverseFingerprint (fingerprint (stored ⟨0+r.val,by omega⟩)) = ⟨0+r.val,by omega⟩ := by
  fin_cases r
  · exact inverse_0000
  · exact inverse_0001
  · exact inverse_0002
  · exact inverse_0003
  · exact inverse_0004
  · exact inverse_0005
  · exact inverse_0006
  · exact inverse_0007
  · exact inverse_0008
  · exact inverse_0009
  · exact inverse_0010
  · exact inverse_0011
  · exact inverse_0012
  · exact inverse_0013
  · exact inverse_0014
  · exact inverse_0015
  · exact inverse_0016
  · exact inverse_0017
  · exact inverse_0018
  · exact inverse_0019

theorem anchor_batch0000 (r : Fin 20) :
    stored ⟨0+r.val,by omega⟩ (0,false) = 0 := by
  fin_cases r
  · exact anchor_0000
  · exact anchor_0001
  · exact anchor_0002
  · exact anchor_0003
  · exact anchor_0004
  · exact anchor_0005
  · exact anchor_0006
  · exact anchor_0007
  · exact anchor_0008
  · exact anchor_0009
  · exact anchor_0010
  · exact anchor_0011
  · exact anchor_0012
  · exact anchor_0013
  · exact anchor_0014
  · exact anchor_0015
  · exact anchor_0016
  · exact anchor_0017
  · exact anchor_0018
  · exact anchor_0019
#print axioms inverse_batch0000
#print axioms anchor_batch0000
end Crown.PairingStored3
