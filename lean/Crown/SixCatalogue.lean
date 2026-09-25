import generated.SixCatalogueBatch0000
import generated.SixCatalogueBatch0001
import generated.SixCatalogueBatch0002
import generated.SixCatalogueBatch0003
import generated.SixCatalogueBatch0004
import generated.SixCatalogueBatch0005
import generated.SixCatalogueBatch0006
import generated.SixCatalogueBatch0007
import generated.SixCatalogueBatch0008
import generated.SixCatalogueBatch0009
import generated.SixCatalogueBatch0010
import generated.SixCatalogueBatch0011
import generated.SixCatalogueBatch0012
import generated.SixCatalogueBatch0013
import generated.SixCatalogueBatch0014
import Mathlib.Tactic.FinCases
namespace Crown.CertificateSixData
open Crown.CertificateSixSemantics
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem all_templates_selected (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∀ t, ∃ c ∈ templates t, ∀ m ∈ cores c, s m = true := by
  intro t
  fin_cases t
  · exact selected0000 s hs hb
  · exact selected0001 s hs hb
  · exact selected0002 s hs hb
  · exact selected0003 s hs hb
  · exact selected0004 s hs hb
  · exact selected0005 s hs hb
  · exact selected0006 s hs hb
  · exact selected0007 s hs hb
  · exact selected0008 s hs hb
  · exact selected0009 s hs hb
  · exact selected0010 s hs hb
  · exact selected0011 s hs hb
  · exact selected0012 s hs hb
  · exact selected0013 s hs hb
  · exact selected0014 s hs hb
  · exact selected0015 s hs hb
  · exact selected0016 s hs hb
  · exact selected0017 s hs hb
  · exact selected0018 s hs hb
  · exact selected0019 s hs hb
  · exact selected0020 s hs hb
  · exact selected0021 s hs hb
  · exact selected0022 s hs hb
  · exact selected0023 s hs hb
  · exact selected0024 s hs hb
  · exact selected0025 s hs hb
  · exact selected0026 s hs hb
  · exact selected0027 s hs hb
  · exact selected0028 s hs hb
  · exact selected0029 s hs hb
  · exact selected0030 s hs hb
  · exact selected0031 s hs hb
  · exact selected0032 s hs hb
  · exact selected0033 s hs hb
  · exact selected0034 s hs hb
  · exact selected0035 s hs hb
  · exact selected0036 s hs hb
  · exact selected0037 s hs hb
  · exact selected0038 s hs hb
  · exact selected0039 s hs hb
  · exact selected0040 s hs hb
  · exact selected0041 s hs hb
  · exact selected0042 s hs hb
  · exact selected0043 s hs hb
  · exact selected0044 s hs hb
  · exact selected0045 s hs hb
  · exact selected0046 s hs hb
  · exact selected0047 s hs hb
  · exact selected0048 s hs hb
  · exact selected0049 s hs hb
  · exact selected0050 s hs hb
  · exact selected0051 s hs hb
  · exact selected0052 s hs hb
  · exact selected0053 s hs hb
  · exact selected0054 s hs hb
  · exact selected0055 s hs hb
  · exact selected0056 s hs hb
  · exact selected0057 s hs hb
  · exact selected0058 s hs hb
  · exact selected0059 s hs hb
#print axioms all_templates_selected
end Crown.CertificateSixData
