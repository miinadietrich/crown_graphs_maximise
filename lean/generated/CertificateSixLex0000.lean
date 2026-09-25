import Crown.CertificateSixLexLookup
import Crown.CertificateSixRanges

namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly Crown.CertificateSixAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_0_62_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation0 62 := by
  exact (negative_falsum s).trans ((lex_first s permutation0 62 (by intro j hj; rw [image0_eq]; exact fixedOnRange_spec image0 63 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_0_62_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation0 62) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 64) = permuteMask permutation0 62 by rw [image0_eq]; rfl))

theorem lex_0_62_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 492) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation0 62 (assignment s)
    (Sat.Literal.pos 492) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 61) (positive_of_descriptor s 492 (.lex permutation0 62) (by rfl)) (lex_0_62_prefix s) (positive_select s 62) (lex_0_62_image s)

theorem lex_0_62_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation0 62 (hmax permutation0) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 61) (lex_0_62_prefix s) (positive_select s 62) (lex_0_62_image s)

theorem lex_0_62_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 492), (Sat.Literal.neg 64)] :=
  (lex_0_62_gate s).prop _ (List.Mem.head _)

theorem lex_0_62_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 492), (Sat.Literal.neg 62), (Sat.Literal.pos 61)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_62_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 492), (Sat.Literal.pos 62), (Sat.Literal.neg 61)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_62_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 62), (Sat.Literal.neg 61), (Sat.Literal.pos 492)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_62_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.pos 61), (Sat.Literal.pos 492)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 492) = lexBefore s permutation0 61 := by
  exact (positive_lex_of_descriptor s 492 permutation0 62 (by rfl)).trans ((lex_skipped s permutation0 61 62 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation0 61) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 64) = permuteMask permutation0 61 by rw [image0_eq]; rfl))

theorem lex_0_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 493) (Sat.Literal.pos 492) (Sat.Literal.pos 61) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation0 61 (assignment s)
    (Sat.Literal.pos 493) (Sat.Literal.pos 492) (Sat.Literal.pos 61) (Sat.Literal.pos 62) (positive_of_descriptor s 493 (.lex permutation0 61) (by rfl)) (lex_0_61_prefix s) (positive_select s 61) (lex_0_61_image s)

theorem lex_0_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 492), (Sat.Literal.pos 61), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation0 61 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 492) (Sat.Literal.pos 61) (Sat.Literal.pos 62) (lex_0_61_prefix s) (positive_select s 61) (lex_0_61_image s)

theorem lex_0_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 493), (Sat.Literal.pos 492)] :=
  (lex_0_61_gate s).prop _ (List.Mem.head _)

theorem lex_0_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 493), (Sat.Literal.neg 61), (Sat.Literal.pos 62)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 493), (Sat.Literal.pos 61), (Sat.Literal.neg 62)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 492), (Sat.Literal.neg 61), (Sat.Literal.neg 62), (Sat.Literal.pos 493)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 492), (Sat.Literal.pos 61), (Sat.Literal.pos 62), (Sat.Literal.pos 493)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 493) = lexBefore s permutation0 58 := by
  exact (positive_lex_of_descriptor s 493 permutation0 61 (by rfl)).trans ((lex_skipped s permutation0 58 61 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 59 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation0 58) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 64) = permuteMask permutation0 58 by rw [image0_eq]; rfl))

theorem lex_0_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 494) (Sat.Literal.pos 493) (Sat.Literal.pos 58) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation0 58 (assignment s)
    (Sat.Literal.pos 494) (Sat.Literal.pos 493) (Sat.Literal.pos 58) (Sat.Literal.pos 57) (positive_of_descriptor s 494 (.lex permutation0 58) (by rfl)) (lex_0_58_prefix s) (positive_select s 58) (lex_0_58_image s)

theorem lex_0_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 493), (Sat.Literal.pos 58), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation0 58 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 493) (Sat.Literal.pos 58) (Sat.Literal.pos 57) (lex_0_58_prefix s) (positive_select s 58) (lex_0_58_image s)

theorem lex_0_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 494), (Sat.Literal.pos 493)] :=
  (lex_0_58_gate s).prop _ (List.Mem.head _)

theorem lex_0_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 494), (Sat.Literal.neg 58), (Sat.Literal.pos 57)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 494), (Sat.Literal.pos 58), (Sat.Literal.neg 57)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 493), (Sat.Literal.neg 58), (Sat.Literal.neg 57), (Sat.Literal.pos 494)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 493), (Sat.Literal.pos 58), (Sat.Literal.pos 57), (Sat.Literal.pos 494)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_57_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 494) = lexBefore s permutation0 57 := by
  exact (positive_lex_of_descriptor s 494 permutation0 58 (by rfl)).trans ((lex_skipped s permutation0 57 58 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_57_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation0 57) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation0 57 by rw [image0_eq]; rfl))

theorem lex_0_57_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 495) (Sat.Literal.pos 494) (Sat.Literal.pos 57) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation0 57 (assignment s)
    (Sat.Literal.pos 495) (Sat.Literal.pos 494) (Sat.Literal.pos 57) (Sat.Literal.pos 58) (positive_of_descriptor s 495 (.lex permutation0 57) (by rfl)) (lex_0_57_prefix s) (positive_select s 57) (lex_0_57_image s)

theorem lex_0_57_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 494), (Sat.Literal.pos 57), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation0 57 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 494) (Sat.Literal.pos 57) (Sat.Literal.pos 58) (lex_0_57_prefix s) (positive_select s 57) (lex_0_57_image s)

theorem lex_0_57_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 495), (Sat.Literal.pos 494)] :=
  (lex_0_57_gate s).prop _ (List.Mem.head _)

theorem lex_0_57_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 495), (Sat.Literal.neg 57), (Sat.Literal.pos 58)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_57_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 495), (Sat.Literal.pos 57), (Sat.Literal.neg 58)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_57_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 494), (Sat.Literal.neg 57), (Sat.Literal.neg 58), (Sat.Literal.pos 495)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_57_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 494), (Sat.Literal.pos 57), (Sat.Literal.pos 58), (Sat.Literal.pos 495)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_54_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 495) = lexBefore s permutation0 54 := by
  exact (positive_lex_of_descriptor s 495 permutation0 57 (by rfl)).trans ((lex_skipped s permutation0 54 57 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 55 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_54_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation0 54) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation0 54 by rw [image0_eq]; rfl))

theorem lex_0_54_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 496) (Sat.Literal.pos 495) (Sat.Literal.pos 54) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation0 54 (assignment s)
    (Sat.Literal.pos 496) (Sat.Literal.pos 495) (Sat.Literal.pos 54) (Sat.Literal.pos 53) (positive_of_descriptor s 496 (.lex permutation0 54) (by rfl)) (lex_0_54_prefix s) (positive_select s 54) (lex_0_54_image s)

theorem lex_0_54_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 495), (Sat.Literal.pos 54), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation0 54 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 495) (Sat.Literal.pos 54) (Sat.Literal.pos 53) (lex_0_54_prefix s) (positive_select s 54) (lex_0_54_image s)

theorem lex_0_54_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 496), (Sat.Literal.pos 495)] :=
  (lex_0_54_gate s).prop _ (List.Mem.head _)

theorem lex_0_54_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 496), (Sat.Literal.neg 54), (Sat.Literal.pos 53)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_54_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 496), (Sat.Literal.pos 54), (Sat.Literal.neg 53)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_54_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 495), (Sat.Literal.neg 54), (Sat.Literal.neg 53), (Sat.Literal.pos 496)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_54_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 495), (Sat.Literal.pos 54), (Sat.Literal.pos 53), (Sat.Literal.pos 496)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 496) = lexBefore s permutation0 53 := by
  exact (positive_lex_of_descriptor s 496 permutation0 54 (by rfl)).trans ((lex_skipped s permutation0 53 54 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation0 53) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 64) = permuteMask permutation0 53 by rw [image0_eq]; rfl))

theorem lex_0_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 497) (Sat.Literal.pos 496) (Sat.Literal.pos 53) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation0 53 (assignment s)
    (Sat.Literal.pos 497) (Sat.Literal.pos 496) (Sat.Literal.pos 53) (Sat.Literal.pos 54) (positive_of_descriptor s 497 (.lex permutation0 53) (by rfl)) (lex_0_53_prefix s) (positive_select s 53) (lex_0_53_image s)

theorem lex_0_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 496), (Sat.Literal.pos 53), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation0 53 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 496) (Sat.Literal.pos 53) (Sat.Literal.pos 54) (lex_0_53_prefix s) (positive_select s 53) (lex_0_53_image s)

theorem lex_0_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 497), (Sat.Literal.pos 496)] :=
  (lex_0_53_gate s).prop _ (List.Mem.head _)

theorem lex_0_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 497), (Sat.Literal.neg 53), (Sat.Literal.pos 54)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 497), (Sat.Literal.pos 53), (Sat.Literal.neg 54)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 496), (Sat.Literal.neg 53), (Sat.Literal.neg 54), (Sat.Literal.pos 497)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 496), (Sat.Literal.pos 53), (Sat.Literal.pos 54), (Sat.Literal.pos 497)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 497) = lexBefore s permutation0 50 := by
  exact (positive_lex_of_descriptor s 497 permutation0 53 (by rfl)).trans ((lex_skipped s permutation0 50 53 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 51 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation0 50) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 64) = permuteMask permutation0 50 by rw [image0_eq]; rfl))

theorem lex_0_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 498) (Sat.Literal.pos 497) (Sat.Literal.pos 50) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation0 50 (assignment s)
    (Sat.Literal.pos 498) (Sat.Literal.pos 497) (Sat.Literal.pos 50) (Sat.Literal.pos 49) (positive_of_descriptor s 498 (.lex permutation0 50) (by rfl)) (lex_0_50_prefix s) (positive_select s 50) (lex_0_50_image s)

theorem lex_0_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 497), (Sat.Literal.pos 50), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation0 50 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 497) (Sat.Literal.pos 50) (Sat.Literal.pos 49) (lex_0_50_prefix s) (positive_select s 50) (lex_0_50_image s)

theorem lex_0_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 498), (Sat.Literal.pos 497)] :=
  (lex_0_50_gate s).prop _ (List.Mem.head _)

theorem lex_0_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 498), (Sat.Literal.neg 50), (Sat.Literal.pos 49)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 498), (Sat.Literal.pos 50), (Sat.Literal.neg 49)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 497), (Sat.Literal.neg 50), (Sat.Literal.neg 49), (Sat.Literal.pos 498)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 497), (Sat.Literal.pos 50), (Sat.Literal.pos 49), (Sat.Literal.pos 498)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_49_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 498) = lexBefore s permutation0 49 := by
  exact (positive_lex_of_descriptor s 498 permutation0 50 (by rfl)).trans ((lex_skipped s permutation0 49 50 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_49_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation0 49) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation0 49 by rw [image0_eq]; rfl))

theorem lex_0_49_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 499) (Sat.Literal.pos 498) (Sat.Literal.pos 49) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation0 49 (assignment s)
    (Sat.Literal.pos 499) (Sat.Literal.pos 498) (Sat.Literal.pos 49) (Sat.Literal.pos 50) (positive_of_descriptor s 499 (.lex permutation0 49) (by rfl)) (lex_0_49_prefix s) (positive_select s 49) (lex_0_49_image s)

theorem lex_0_49_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 498), (Sat.Literal.pos 49), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation0 49 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 498) (Sat.Literal.pos 49) (Sat.Literal.pos 50) (lex_0_49_prefix s) (positive_select s 49) (lex_0_49_image s)

theorem lex_0_49_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 499), (Sat.Literal.pos 498)] :=
  (lex_0_49_gate s).prop _ (List.Mem.head _)

theorem lex_0_49_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 499), (Sat.Literal.neg 49), (Sat.Literal.pos 50)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_49_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 499), (Sat.Literal.pos 49), (Sat.Literal.neg 50)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_49_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 498), (Sat.Literal.neg 49), (Sat.Literal.neg 50), (Sat.Literal.pos 499)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_49_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 498), (Sat.Literal.pos 49), (Sat.Literal.pos 50), (Sat.Literal.pos 499)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 499) = lexBefore s permutation0 46 := by
  exact (positive_lex_of_descriptor s 499 permutation0 49 (by rfl)).trans ((lex_skipped s permutation0 46 49 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 47 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation0 46) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation0 46 by rw [image0_eq]; rfl))

theorem lex_0_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 500) (Sat.Literal.pos 499) (Sat.Literal.pos 46) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation0 46 (assignment s)
    (Sat.Literal.pos 500) (Sat.Literal.pos 499) (Sat.Literal.pos 46) (Sat.Literal.pos 45) (positive_of_descriptor s 500 (.lex permutation0 46) (by rfl)) (lex_0_46_prefix s) (positive_select s 46) (lex_0_46_image s)

theorem lex_0_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 499), (Sat.Literal.pos 46), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation0 46 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 499) (Sat.Literal.pos 46) (Sat.Literal.pos 45) (lex_0_46_prefix s) (positive_select s 46) (lex_0_46_image s)

theorem lex_0_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 500), (Sat.Literal.pos 499)] :=
  (lex_0_46_gate s).prop _ (List.Mem.head _)

theorem lex_0_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 500), (Sat.Literal.neg 46), (Sat.Literal.pos 45)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 500), (Sat.Literal.pos 46), (Sat.Literal.neg 45)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 499), (Sat.Literal.neg 46), (Sat.Literal.neg 45), (Sat.Literal.pos 500)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 499), (Sat.Literal.pos 46), (Sat.Literal.pos 45), (Sat.Literal.pos 500)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 500) = lexBefore s permutation0 45 := by
  exact (positive_lex_of_descriptor s 500 permutation0 46 (by rfl)).trans ((lex_skipped s permutation0 45 46 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation0 45) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation0 45 by rw [image0_eq]; rfl))

theorem lex_0_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 501) (Sat.Literal.pos 500) (Sat.Literal.pos 45) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation0 45 (assignment s)
    (Sat.Literal.pos 501) (Sat.Literal.pos 500) (Sat.Literal.pos 45) (Sat.Literal.pos 46) (positive_of_descriptor s 501 (.lex permutation0 45) (by rfl)) (lex_0_45_prefix s) (positive_select s 45) (lex_0_45_image s)

theorem lex_0_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 500), (Sat.Literal.pos 45), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation0 45 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 500) (Sat.Literal.pos 45) (Sat.Literal.pos 46) (lex_0_45_prefix s) (positive_select s 45) (lex_0_45_image s)

theorem lex_0_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 501), (Sat.Literal.pos 500)] :=
  (lex_0_45_gate s).prop _ (List.Mem.head _)

theorem lex_0_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 501), (Sat.Literal.neg 45), (Sat.Literal.pos 46)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 501), (Sat.Literal.pos 45), (Sat.Literal.neg 46)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 500), (Sat.Literal.neg 45), (Sat.Literal.neg 46), (Sat.Literal.pos 501)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 500), (Sat.Literal.pos 45), (Sat.Literal.pos 46), (Sat.Literal.pos 501)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 501) = lexBefore s permutation0 42 := by
  exact (positive_lex_of_descriptor s 501 permutation0 45 (by rfl)).trans ((lex_skipped s permutation0 42 45 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 43 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation0 42) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation0 42 by rw [image0_eq]; rfl))

theorem lex_0_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 502) (Sat.Literal.pos 501) (Sat.Literal.pos 42) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation0 42 (assignment s)
    (Sat.Literal.pos 502) (Sat.Literal.pos 501) (Sat.Literal.pos 42) (Sat.Literal.pos 41) (positive_of_descriptor s 502 (.lex permutation0 42) (by rfl)) (lex_0_42_prefix s) (positive_select s 42) (lex_0_42_image s)

theorem lex_0_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 501), (Sat.Literal.pos 42), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation0 42 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 501) (Sat.Literal.pos 42) (Sat.Literal.pos 41) (lex_0_42_prefix s) (positive_select s 42) (lex_0_42_image s)

theorem lex_0_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 502), (Sat.Literal.pos 501)] :=
  (lex_0_42_gate s).prop _ (List.Mem.head _)

theorem lex_0_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 502), (Sat.Literal.neg 42), (Sat.Literal.pos 41)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 502), (Sat.Literal.pos 42), (Sat.Literal.neg 41)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 501), (Sat.Literal.neg 42), (Sat.Literal.neg 41), (Sat.Literal.pos 502)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 501), (Sat.Literal.pos 42), (Sat.Literal.pos 41), (Sat.Literal.pos 502)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 502) = lexBefore s permutation0 41 := by
  exact (positive_lex_of_descriptor s 502 permutation0 42 (by rfl)).trans ((lex_skipped s permutation0 41 42 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation0 41) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation0 41 by rw [image0_eq]; rfl))

theorem lex_0_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 503) (Sat.Literal.pos 502) (Sat.Literal.pos 41) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation0 41 (assignment s)
    (Sat.Literal.pos 503) (Sat.Literal.pos 502) (Sat.Literal.pos 41) (Sat.Literal.pos 42) (positive_of_descriptor s 503 (.lex permutation0 41) (by rfl)) (lex_0_41_prefix s) (positive_select s 41) (lex_0_41_image s)

theorem lex_0_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 502), (Sat.Literal.pos 41), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation0 41 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 502) (Sat.Literal.pos 41) (Sat.Literal.pos 42) (lex_0_41_prefix s) (positive_select s 41) (lex_0_41_image s)

theorem lex_0_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 503), (Sat.Literal.pos 502)] :=
  (lex_0_41_gate s).prop _ (List.Mem.head _)

theorem lex_0_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 503), (Sat.Literal.neg 41), (Sat.Literal.pos 42)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 503), (Sat.Literal.pos 41), (Sat.Literal.neg 42)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 502), (Sat.Literal.neg 41), (Sat.Literal.neg 42), (Sat.Literal.pos 503)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 502), (Sat.Literal.pos 41), (Sat.Literal.pos 42), (Sat.Literal.pos 503)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 503) = lexBefore s permutation0 38 := by
  exact (positive_lex_of_descriptor s 503 permutation0 41 (by rfl)).trans ((lex_skipped s permutation0 38 41 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 39 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation0 38) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation0 38 by rw [image0_eq]; rfl))

theorem lex_0_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 504) (Sat.Literal.pos 503) (Sat.Literal.pos 38) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation0 38 (assignment s)
    (Sat.Literal.pos 504) (Sat.Literal.pos 503) (Sat.Literal.pos 38) (Sat.Literal.pos 37) (positive_of_descriptor s 504 (.lex permutation0 38) (by rfl)) (lex_0_38_prefix s) (positive_select s 38) (lex_0_38_image s)

theorem lex_0_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 503), (Sat.Literal.pos 38), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation0 38 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 503) (Sat.Literal.pos 38) (Sat.Literal.pos 37) (lex_0_38_prefix s) (positive_select s 38) (lex_0_38_image s)

theorem lex_0_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 504), (Sat.Literal.pos 503)] :=
  (lex_0_38_gate s).prop _ (List.Mem.head _)

theorem lex_0_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 504), (Sat.Literal.neg 38), (Sat.Literal.pos 37)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 504), (Sat.Literal.pos 38), (Sat.Literal.neg 37)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 503), (Sat.Literal.neg 38), (Sat.Literal.neg 37), (Sat.Literal.pos 504)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 503), (Sat.Literal.pos 38), (Sat.Literal.pos 37), (Sat.Literal.pos 504)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 504) = lexBefore s permutation0 37 := by
  exact (positive_lex_of_descriptor s 504 permutation0 38 (by rfl)).trans ((lex_skipped s permutation0 37 38 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation0 37) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation0 37 by rw [image0_eq]; rfl))

theorem lex_0_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 505) (Sat.Literal.pos 504) (Sat.Literal.pos 37) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation0 37 (assignment s)
    (Sat.Literal.pos 505) (Sat.Literal.pos 504) (Sat.Literal.pos 37) (Sat.Literal.pos 38) (positive_of_descriptor s 505 (.lex permutation0 37) (by rfl)) (lex_0_37_prefix s) (positive_select s 37) (lex_0_37_image s)

theorem lex_0_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 504), (Sat.Literal.pos 37), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation0 37 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 504) (Sat.Literal.pos 37) (Sat.Literal.pos 38) (lex_0_37_prefix s) (positive_select s 37) (lex_0_37_image s)

theorem lex_0_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 505), (Sat.Literal.pos 504)] :=
  (lex_0_37_gate s).prop _ (List.Mem.head _)

theorem lex_0_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 505), (Sat.Literal.neg 37), (Sat.Literal.pos 38)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 505), (Sat.Literal.pos 37), (Sat.Literal.neg 38)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 504), (Sat.Literal.neg 37), (Sat.Literal.neg 38), (Sat.Literal.pos 505)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 504), (Sat.Literal.pos 37), (Sat.Literal.pos 38), (Sat.Literal.pos 505)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 505) = lexBefore s permutation0 34 := by
  exact (positive_lex_of_descriptor s 505 permutation0 37 (by rfl)).trans ((lex_skipped s permutation0 34 37 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 35 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation0 34) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 64) = permuteMask permutation0 34 by rw [image0_eq]; rfl))

theorem lex_0_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 506) (Sat.Literal.pos 505) (Sat.Literal.pos 34) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation0 34 (assignment s)
    (Sat.Literal.pos 506) (Sat.Literal.pos 505) (Sat.Literal.pos 34) (Sat.Literal.pos 33) (positive_of_descriptor s 506 (.lex permutation0 34) (by rfl)) (lex_0_34_prefix s) (positive_select s 34) (lex_0_34_image s)

theorem lex_0_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 505), (Sat.Literal.pos 34), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation0 34 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 505) (Sat.Literal.pos 34) (Sat.Literal.pos 33) (lex_0_34_prefix s) (positive_select s 34) (lex_0_34_image s)

theorem lex_0_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 506), (Sat.Literal.pos 505)] :=
  (lex_0_34_gate s).prop _ (List.Mem.head _)

theorem lex_0_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 506), (Sat.Literal.neg 34), (Sat.Literal.pos 33)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 506), (Sat.Literal.pos 34), (Sat.Literal.neg 33)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 505), (Sat.Literal.neg 34), (Sat.Literal.neg 33), (Sat.Literal.pos 506)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 505), (Sat.Literal.pos 34), (Sat.Literal.pos 33), (Sat.Literal.pos 506)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_33_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 506) = lexBefore s permutation0 33 := by
  exact (positive_lex_of_descriptor s 506 permutation0 34 (by rfl)).trans ((lex_skipped s permutation0 33 34 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_33_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation0 33) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation0 33 by rw [image0_eq]; rfl))

theorem lex_0_33_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 507) (Sat.Literal.pos 506) (Sat.Literal.pos 33) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation0 33 (assignment s)
    (Sat.Literal.pos 507) (Sat.Literal.pos 506) (Sat.Literal.pos 33) (Sat.Literal.pos 34) (positive_of_descriptor s 507 (.lex permutation0 33) (by rfl)) (lex_0_33_prefix s) (positive_select s 33) (lex_0_33_image s)

theorem lex_0_33_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 506), (Sat.Literal.pos 33), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation0 33 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 506) (Sat.Literal.pos 33) (Sat.Literal.pos 34) (lex_0_33_prefix s) (positive_select s 33) (lex_0_33_image s)

theorem lex_0_33_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 507), (Sat.Literal.pos 506)] :=
  (lex_0_33_gate s).prop _ (List.Mem.head _)

theorem lex_0_33_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 507), (Sat.Literal.neg 33), (Sat.Literal.pos 34)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_33_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 507), (Sat.Literal.pos 33), (Sat.Literal.neg 34)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_33_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 506), (Sat.Literal.neg 33), (Sat.Literal.neg 34), (Sat.Literal.pos 507)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_33_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 506), (Sat.Literal.pos 33), (Sat.Literal.pos 34), (Sat.Literal.pos 507)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_30_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 507) = lexBefore s permutation0 30 := by
  exact (positive_lex_of_descriptor s 507 permutation0 33 (by rfl)).trans ((lex_skipped s permutation0 30 33 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 31 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_30_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation0 30) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation0 30 by rw [image0_eq]; rfl))

theorem lex_0_30_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 508) (Sat.Literal.pos 507) (Sat.Literal.pos 30) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation0 30 (assignment s)
    (Sat.Literal.pos 508) (Sat.Literal.pos 507) (Sat.Literal.pos 30) (Sat.Literal.pos 29) (positive_of_descriptor s 508 (.lex permutation0 30) (by rfl)) (lex_0_30_prefix s) (positive_select s 30) (lex_0_30_image s)

theorem lex_0_30_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 507), (Sat.Literal.pos 30), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation0 30 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 507) (Sat.Literal.pos 30) (Sat.Literal.pos 29) (lex_0_30_prefix s) (positive_select s 30) (lex_0_30_image s)

theorem lex_0_30_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 508), (Sat.Literal.pos 507)] :=
  (lex_0_30_gate s).prop _ (List.Mem.head _)

theorem lex_0_30_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 508), (Sat.Literal.neg 30), (Sat.Literal.pos 29)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_30_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 508), (Sat.Literal.pos 30), (Sat.Literal.neg 29)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_30_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 507), (Sat.Literal.neg 30), (Sat.Literal.neg 29), (Sat.Literal.pos 508)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_30_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 507), (Sat.Literal.pos 30), (Sat.Literal.pos 29), (Sat.Literal.pos 508)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 508) = lexBefore s permutation0 29 := by
  exact (positive_lex_of_descriptor s 508 permutation0 30 (by rfl)).trans ((lex_skipped s permutation0 29 30 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation0 29) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 64) = permuteMask permutation0 29 by rw [image0_eq]; rfl))

theorem lex_0_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 509) (Sat.Literal.pos 508) (Sat.Literal.pos 29) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation0 29 (assignment s)
    (Sat.Literal.pos 509) (Sat.Literal.pos 508) (Sat.Literal.pos 29) (Sat.Literal.pos 30) (positive_of_descriptor s 509 (.lex permutation0 29) (by rfl)) (lex_0_29_prefix s) (positive_select s 29) (lex_0_29_image s)

theorem lex_0_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 508), (Sat.Literal.pos 29), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation0 29 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 508) (Sat.Literal.pos 29) (Sat.Literal.pos 30) (lex_0_29_prefix s) (positive_select s 29) (lex_0_29_image s)

theorem lex_0_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 509), (Sat.Literal.pos 508)] :=
  (lex_0_29_gate s).prop _ (List.Mem.head _)

theorem lex_0_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 509), (Sat.Literal.neg 29), (Sat.Literal.pos 30)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 509), (Sat.Literal.pos 29), (Sat.Literal.neg 30)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 508), (Sat.Literal.neg 29), (Sat.Literal.neg 30), (Sat.Literal.pos 509)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 508), (Sat.Literal.pos 29), (Sat.Literal.pos 30), (Sat.Literal.pos 509)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 509) = lexBefore s permutation0 26 := by
  exact (positive_lex_of_descriptor s 509 permutation0 29 (by rfl)).trans ((lex_skipped s permutation0 26 29 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 27 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation0 26) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation0 26 by rw [image0_eq]; rfl))

theorem lex_0_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 510) (Sat.Literal.pos 509) (Sat.Literal.pos 26) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation0 26 (assignment s)
    (Sat.Literal.pos 510) (Sat.Literal.pos 509) (Sat.Literal.pos 26) (Sat.Literal.pos 25) (positive_of_descriptor s 510 (.lex permutation0 26) (by rfl)) (lex_0_26_prefix s) (positive_select s 26) (lex_0_26_image s)

theorem lex_0_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 509), (Sat.Literal.pos 26), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation0 26 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 509) (Sat.Literal.pos 26) (Sat.Literal.pos 25) (lex_0_26_prefix s) (positive_select s 26) (lex_0_26_image s)

theorem lex_0_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 510), (Sat.Literal.pos 509)] :=
  (lex_0_26_gate s).prop _ (List.Mem.head _)

theorem lex_0_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 510), (Sat.Literal.neg 26), (Sat.Literal.pos 25)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 510), (Sat.Literal.pos 26), (Sat.Literal.neg 25)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 509), (Sat.Literal.neg 26), (Sat.Literal.neg 25), (Sat.Literal.pos 510)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 509), (Sat.Literal.pos 26), (Sat.Literal.pos 25), (Sat.Literal.pos 510)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 510) = lexBefore s permutation0 25 := by
  exact (positive_lex_of_descriptor s 510 permutation0 26 (by rfl)).trans ((lex_skipped s permutation0 25 26 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation0 25) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation0 25 by rw [image0_eq]; rfl))

theorem lex_0_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 511) (Sat.Literal.pos 510) (Sat.Literal.pos 25) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation0 25 (assignment s)
    (Sat.Literal.pos 511) (Sat.Literal.pos 510) (Sat.Literal.pos 25) (Sat.Literal.pos 26) (positive_of_descriptor s 511 (.lex permutation0 25) (by rfl)) (lex_0_25_prefix s) (positive_select s 25) (lex_0_25_image s)

theorem lex_0_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 510), (Sat.Literal.pos 25), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation0 25 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 510) (Sat.Literal.pos 25) (Sat.Literal.pos 26) (lex_0_25_prefix s) (positive_select s 25) (lex_0_25_image s)

theorem lex_0_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 511), (Sat.Literal.pos 510)] :=
  (lex_0_25_gate s).prop _ (List.Mem.head _)

theorem lex_0_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 511), (Sat.Literal.neg 25), (Sat.Literal.pos 26)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 511), (Sat.Literal.pos 25), (Sat.Literal.neg 26)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 510), (Sat.Literal.neg 25), (Sat.Literal.neg 26), (Sat.Literal.pos 511)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 510), (Sat.Literal.pos 25), (Sat.Literal.pos 26), (Sat.Literal.pos 511)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 511) = lexBefore s permutation0 22 := by
  exact (positive_lex_of_descriptor s 511 permutation0 25 (by rfl)).trans ((lex_skipped s permutation0 22 25 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 23 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation0 22) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation0 22 by rw [image0_eq]; rfl))

theorem lex_0_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 512) (Sat.Literal.pos 511) (Sat.Literal.pos 22) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation0 22 (assignment s)
    (Sat.Literal.pos 512) (Sat.Literal.pos 511) (Sat.Literal.pos 22) (Sat.Literal.pos 21) (positive_of_descriptor s 512 (.lex permutation0 22) (by rfl)) (lex_0_22_prefix s) (positive_select s 22) (lex_0_22_image s)

theorem lex_0_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 511), (Sat.Literal.pos 22), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation0 22 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 511) (Sat.Literal.pos 22) (Sat.Literal.pos 21) (lex_0_22_prefix s) (positive_select s 22) (lex_0_22_image s)

theorem lex_0_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 512), (Sat.Literal.pos 511)] :=
  (lex_0_22_gate s).prop _ (List.Mem.head _)

theorem lex_0_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 512), (Sat.Literal.neg 22), (Sat.Literal.pos 21)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 512), (Sat.Literal.pos 22), (Sat.Literal.neg 21)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 511), (Sat.Literal.neg 22), (Sat.Literal.neg 21), (Sat.Literal.pos 512)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 511), (Sat.Literal.pos 22), (Sat.Literal.pos 21), (Sat.Literal.pos 512)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 512) = lexBefore s permutation0 21 := by
  exact (positive_lex_of_descriptor s 512 permutation0 22 (by rfl)).trans ((lex_skipped s permutation0 21 22 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation0 21) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation0 21 by rw [image0_eq]; rfl))

theorem lex_0_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 513) (Sat.Literal.pos 512) (Sat.Literal.pos 21) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation0 21 (assignment s)
    (Sat.Literal.pos 513) (Sat.Literal.pos 512) (Sat.Literal.pos 21) (Sat.Literal.pos 22) (positive_of_descriptor s 513 (.lex permutation0 21) (by rfl)) (lex_0_21_prefix s) (positive_select s 21) (lex_0_21_image s)

theorem lex_0_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 512), (Sat.Literal.pos 21), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation0 21 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 512) (Sat.Literal.pos 21) (Sat.Literal.pos 22) (lex_0_21_prefix s) (positive_select s 21) (lex_0_21_image s)

theorem lex_0_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 513), (Sat.Literal.pos 512)] :=
  (lex_0_21_gate s).prop _ (List.Mem.head _)

theorem lex_0_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 513), (Sat.Literal.neg 21), (Sat.Literal.pos 22)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 513), (Sat.Literal.pos 21), (Sat.Literal.neg 22)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 512), (Sat.Literal.neg 21), (Sat.Literal.neg 22), (Sat.Literal.pos 513)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 512), (Sat.Literal.pos 21), (Sat.Literal.pos 22), (Sat.Literal.pos 513)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 513) = lexBefore s permutation0 18 := by
  exact (positive_lex_of_descriptor s 513 permutation0 21 (by rfl)).trans ((lex_skipped s permutation0 18 21 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 19 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation0 18) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation0 18 by rw [image0_eq]; rfl))

theorem lex_0_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 514) (Sat.Literal.pos 513) (Sat.Literal.pos 18) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation0 18 (assignment s)
    (Sat.Literal.pos 514) (Sat.Literal.pos 513) (Sat.Literal.pos 18) (Sat.Literal.pos 17) (positive_of_descriptor s 514 (.lex permutation0 18) (by rfl)) (lex_0_18_prefix s) (positive_select s 18) (lex_0_18_image s)

theorem lex_0_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 513), (Sat.Literal.pos 18), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation0 18 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 513) (Sat.Literal.pos 18) (Sat.Literal.pos 17) (lex_0_18_prefix s) (positive_select s 18) (lex_0_18_image s)

theorem lex_0_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 514), (Sat.Literal.pos 513)] :=
  (lex_0_18_gate s).prop _ (List.Mem.head _)

theorem lex_0_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 514), (Sat.Literal.neg 18), (Sat.Literal.pos 17)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 514), (Sat.Literal.pos 18), (Sat.Literal.neg 17)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 513), (Sat.Literal.neg 18), (Sat.Literal.neg 17), (Sat.Literal.pos 514)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 513), (Sat.Literal.pos 18), (Sat.Literal.pos 17), (Sat.Literal.pos 514)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 514) = lexBefore s permutation0 17 := by
  exact (positive_lex_of_descriptor s 514 permutation0 18 (by rfl)).trans ((lex_skipped s permutation0 17 18 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation0 17) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation0 17 by rw [image0_eq]; rfl))

theorem lex_0_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 515) (Sat.Literal.pos 514) (Sat.Literal.pos 17) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation0 17 (assignment s)
    (Sat.Literal.pos 515) (Sat.Literal.pos 514) (Sat.Literal.pos 17) (Sat.Literal.pos 18) (positive_of_descriptor s 515 (.lex permutation0 17) (by rfl)) (lex_0_17_prefix s) (positive_select s 17) (lex_0_17_image s)

theorem lex_0_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 514), (Sat.Literal.pos 17), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation0 17 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 514) (Sat.Literal.pos 17) (Sat.Literal.pos 18) (lex_0_17_prefix s) (positive_select s 17) (lex_0_17_image s)

theorem lex_0_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 515), (Sat.Literal.pos 514)] :=
  (lex_0_17_gate s).prop _ (List.Mem.head _)

theorem lex_0_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 515), (Sat.Literal.neg 17), (Sat.Literal.pos 18)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 515), (Sat.Literal.pos 17), (Sat.Literal.neg 18)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 514), (Sat.Literal.neg 17), (Sat.Literal.neg 18), (Sat.Literal.pos 515)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 514), (Sat.Literal.pos 17), (Sat.Literal.pos 18), (Sat.Literal.pos 515)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_14_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 515) = lexBefore s permutation0 14 := by
  exact (positive_lex_of_descriptor s 515 permutation0 17 (by rfl)).trans ((lex_skipped s permutation0 14 17 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 15 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_14_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation0 14) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation0 14 by rw [image0_eq]; rfl))

theorem lex_0_14_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 516) (Sat.Literal.pos 515) (Sat.Literal.pos 14) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation0 14 (assignment s)
    (Sat.Literal.pos 516) (Sat.Literal.pos 515) (Sat.Literal.pos 14) (Sat.Literal.pos 13) (positive_of_descriptor s 516 (.lex permutation0 14) (by rfl)) (lex_0_14_prefix s) (positive_select s 14) (lex_0_14_image s)

theorem lex_0_14_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 515), (Sat.Literal.pos 14), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation0 14 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 515) (Sat.Literal.pos 14) (Sat.Literal.pos 13) (lex_0_14_prefix s) (positive_select s 14) (lex_0_14_image s)

theorem lex_0_14_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 516), (Sat.Literal.pos 515)] :=
  (lex_0_14_gate s).prop _ (List.Mem.head _)

theorem lex_0_14_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 516), (Sat.Literal.neg 14), (Sat.Literal.pos 13)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_14_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 516), (Sat.Literal.pos 14), (Sat.Literal.neg 13)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_14_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 515), (Sat.Literal.neg 14), (Sat.Literal.neg 13), (Sat.Literal.pos 516)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_14_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 515), (Sat.Literal.pos 14), (Sat.Literal.pos 13), (Sat.Literal.pos 516)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 516) = lexBefore s permutation0 13 := by
  exact (positive_lex_of_descriptor s 516 permutation0 14 (by rfl)).trans ((lex_skipped s permutation0 13 14 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation0 13) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 64) = permuteMask permutation0 13 by rw [image0_eq]; rfl))

theorem lex_0_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 517) (Sat.Literal.pos 516) (Sat.Literal.pos 13) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation0 13 (assignment s)
    (Sat.Literal.pos 517) (Sat.Literal.pos 516) (Sat.Literal.pos 13) (Sat.Literal.pos 14) (positive_of_descriptor s 517 (.lex permutation0 13) (by rfl)) (lex_0_13_prefix s) (positive_select s 13) (lex_0_13_image s)

theorem lex_0_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 516), (Sat.Literal.pos 13), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation0 13 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 516) (Sat.Literal.pos 13) (Sat.Literal.pos 14) (lex_0_13_prefix s) (positive_select s 13) (lex_0_13_image s)

theorem lex_0_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 517), (Sat.Literal.pos 516)] :=
  (lex_0_13_gate s).prop _ (List.Mem.head _)

theorem lex_0_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 517), (Sat.Literal.neg 13), (Sat.Literal.pos 14)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 517), (Sat.Literal.pos 13), (Sat.Literal.neg 14)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 516), (Sat.Literal.neg 13), (Sat.Literal.neg 14), (Sat.Literal.pos 517)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 516), (Sat.Literal.pos 13), (Sat.Literal.pos 14), (Sat.Literal.pos 517)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 517) = lexBefore s permutation0 10 := by
  exact (positive_lex_of_descriptor s 517 permutation0 13 (by rfl)).trans ((lex_skipped s permutation0 10 13 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 11 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation0 10) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 64) = permuteMask permutation0 10 by rw [image0_eq]; rfl))

theorem lex_0_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 518) (Sat.Literal.pos 517) (Sat.Literal.pos 10) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation0 10 (assignment s)
    (Sat.Literal.pos 518) (Sat.Literal.pos 517) (Sat.Literal.pos 10) (Sat.Literal.pos 9) (positive_of_descriptor s 518 (.lex permutation0 10) (by rfl)) (lex_0_10_prefix s) (positive_select s 10) (lex_0_10_image s)

theorem lex_0_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 517), (Sat.Literal.pos 10), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation0 10 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 517) (Sat.Literal.pos 10) (Sat.Literal.pos 9) (lex_0_10_prefix s) (positive_select s 10) (lex_0_10_image s)

theorem lex_0_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 518), (Sat.Literal.pos 517)] :=
  (lex_0_10_gate s).prop _ (List.Mem.head _)

theorem lex_0_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 518), (Sat.Literal.neg 10), (Sat.Literal.pos 9)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 518), (Sat.Literal.pos 10), (Sat.Literal.neg 9)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 517), (Sat.Literal.neg 10), (Sat.Literal.neg 9), (Sat.Literal.pos 518)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 517), (Sat.Literal.pos 10), (Sat.Literal.pos 9), (Sat.Literal.pos 518)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_9_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 518) = lexBefore s permutation0 9 := by
  exact (positive_lex_of_descriptor s 518 permutation0 10 (by rfl)).trans ((lex_skipped s permutation0 9 10 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_9_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation0 9) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation0 9 by rw [image0_eq]; rfl))

theorem lex_0_9_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 519) (Sat.Literal.pos 518) (Sat.Literal.pos 9) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation0 9 (assignment s)
    (Sat.Literal.pos 519) (Sat.Literal.pos 518) (Sat.Literal.pos 9) (Sat.Literal.pos 10) (positive_of_descriptor s 519 (.lex permutation0 9) (by rfl)) (lex_0_9_prefix s) (positive_select s 9) (lex_0_9_image s)

theorem lex_0_9_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 518), (Sat.Literal.pos 9), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation0 9 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 518) (Sat.Literal.pos 9) (Sat.Literal.pos 10) (lex_0_9_prefix s) (positive_select s 9) (lex_0_9_image s)

theorem lex_0_9_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 519), (Sat.Literal.pos 518)] :=
  (lex_0_9_gate s).prop _ (List.Mem.head _)

theorem lex_0_9_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 519), (Sat.Literal.neg 9), (Sat.Literal.pos 10)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_9_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 519), (Sat.Literal.pos 9), (Sat.Literal.neg 10)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_9_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 518), (Sat.Literal.neg 9), (Sat.Literal.neg 10), (Sat.Literal.pos 519)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_9_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 518), (Sat.Literal.pos 9), (Sat.Literal.pos 10), (Sat.Literal.pos 519)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_6_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 519) = lexBefore s permutation0 6 := by
  exact (positive_lex_of_descriptor s 519 permutation0 9 (by rfl)).trans ((lex_skipped s permutation0 6 9 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 7 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_6_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation0 6) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation0 6 by rw [image0_eq]; rfl))

theorem lex_0_6_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 520) (Sat.Literal.pos 519) (Sat.Literal.pos 6) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation0 6 (assignment s)
    (Sat.Literal.pos 520) (Sat.Literal.pos 519) (Sat.Literal.pos 6) (Sat.Literal.pos 5) (positive_of_descriptor s 520 (.lex permutation0 6) (by rfl)) (lex_0_6_prefix s) (positive_select s 6) (lex_0_6_image s)

theorem lex_0_6_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 519), (Sat.Literal.pos 6), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation0 6 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 519) (Sat.Literal.pos 6) (Sat.Literal.pos 5) (lex_0_6_prefix s) (positive_select s 6) (lex_0_6_image s)

theorem lex_0_6_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 520), (Sat.Literal.pos 519)] :=
  (lex_0_6_gate s).prop _ (List.Mem.head _)

theorem lex_0_6_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 520), (Sat.Literal.neg 6), (Sat.Literal.pos 5)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_6_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 520), (Sat.Literal.pos 6), (Sat.Literal.neg 5)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_6_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 519), (Sat.Literal.neg 6), (Sat.Literal.neg 5), (Sat.Literal.pos 520)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_6_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 519), (Sat.Literal.pos 6), (Sat.Literal.pos 5), (Sat.Literal.pos 520)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 520) = lexBefore s permutation0 5 := by
  exact (positive_lex_of_descriptor s 520 permutation0 6 (by rfl)).trans ((lex_skipped s permutation0 5 6 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation0 5) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 64) = permuteMask permutation0 5 by rw [image0_eq]; rfl))

theorem lex_0_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 521) (Sat.Literal.pos 520) (Sat.Literal.pos 5) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation0 5 (assignment s)
    (Sat.Literal.pos 521) (Sat.Literal.pos 520) (Sat.Literal.pos 5) (Sat.Literal.pos 6) (positive_of_descriptor s 521 (.lex permutation0 5) (by rfl)) (lex_0_5_prefix s) (positive_select s 5) (lex_0_5_image s)

theorem lex_0_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 520), (Sat.Literal.pos 5), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation0 5 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 520) (Sat.Literal.pos 5) (Sat.Literal.pos 6) (lex_0_5_prefix s) (positive_select s 5) (lex_0_5_image s)

theorem lex_0_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 521), (Sat.Literal.pos 520)] :=
  (lex_0_5_gate s).prop _ (List.Mem.head _)

theorem lex_0_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 521), (Sat.Literal.neg 5), (Sat.Literal.pos 6)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 521), (Sat.Literal.pos 5), (Sat.Literal.neg 6)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 520), (Sat.Literal.neg 5), (Sat.Literal.neg 6), (Sat.Literal.pos 521)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 520), (Sat.Literal.pos 5), (Sat.Literal.pos 6), (Sat.Literal.pos 521)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_2_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 521) = lexBefore s permutation0 2 := by
  exact (positive_lex_of_descriptor s 521 permutation0 5 (by rfl)).trans ((lex_skipped s permutation0 2 5 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 3 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_2_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation0 2) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 64) = permuteMask permutation0 2 by rw [image0_eq]; rfl))

theorem lex_0_2_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 522) (Sat.Literal.pos 521) (Sat.Literal.pos 2) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation0 2 (assignment s)
    (Sat.Literal.pos 522) (Sat.Literal.pos 521) (Sat.Literal.pos 2) (Sat.Literal.pos 1) (positive_of_descriptor s 522 (.lex permutation0 2) (by rfl)) (lex_0_2_prefix s) (positive_select s 2) (lex_0_2_image s)

theorem lex_0_2_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 521), (Sat.Literal.pos 2), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation0 2 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 521) (Sat.Literal.pos 2) (Sat.Literal.pos 1) (lex_0_2_prefix s) (positive_select s 2) (lex_0_2_image s)

theorem lex_0_2_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 522), (Sat.Literal.pos 521)] :=
  (lex_0_2_gate s).prop _ (List.Mem.head _)

theorem lex_0_2_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 522), (Sat.Literal.neg 2), (Sat.Literal.pos 1)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_2_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 522), (Sat.Literal.pos 2), (Sat.Literal.neg 1)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_2_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 521), (Sat.Literal.neg 2), (Sat.Literal.neg 1), (Sat.Literal.pos 522)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_2_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 521), (Sat.Literal.pos 2), (Sat.Literal.pos 1), (Sat.Literal.pos 522)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_1_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 522) = lexBefore s permutation0 1 := by
  exact (positive_lex_of_descriptor s 522 permutation0 2 (by rfl)).trans ((lex_skipped s permutation0 1 2 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_1_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation0 1) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 64) = permuteMask permutation0 1 by rw [image0_eq]; rfl))

theorem lex_0_1_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 523) (Sat.Literal.pos 522) (Sat.Literal.pos 1) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation0 1 (assignment s)
    (Sat.Literal.pos 523) (Sat.Literal.pos 522) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (positive_of_descriptor s 523 (.lex permutation0 1) (by rfl)) (lex_0_1_prefix s) (positive_select s 1) (lex_0_1_image s)

theorem lex_0_1_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 522), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation0 1 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 522) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (lex_0_1_prefix s) (positive_select s 1) (lex_0_1_image s)

theorem lex_0_1_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 523), (Sat.Literal.pos 522)] :=
  (lex_0_1_gate s).prop _ (List.Mem.head _)

theorem lex_0_1_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 523), (Sat.Literal.neg 1), (Sat.Literal.pos 2)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_1_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 523), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_1_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 522), (Sat.Literal.neg 1), (Sat.Literal.neg 2), (Sat.Literal.pos 523)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_1_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 522), (Sat.Literal.pos 1), (Sat.Literal.pos 2), (Sat.Literal.pos 523)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation1 61 := by
  exact (negative_falsum s).trans ((lex_first s permutation1 61 (by intro j hj; rw [image1_eq]; exact fixedOnRange_spec image1 62 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_1_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation1 61) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 64) = permuteMask permutation1 61 by rw [image1_eq]; rfl))

theorem lex_1_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 524) (Sat.Literal.neg 64) (Sat.Literal.pos 61) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation1 61 (assignment s)
    (Sat.Literal.pos 524) (Sat.Literal.neg 64) (Sat.Literal.pos 61) (Sat.Literal.pos 59) (positive_of_descriptor s 524 (.lex permutation1 61) (by rfl)) (lex_1_61_prefix s) (positive_select s 61) (lex_1_61_image s)

theorem lex_1_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 61), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation1 61 (hmax permutation1) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 61) (Sat.Literal.pos 59) (lex_1_61_prefix s) (positive_select s 61) (lex_1_61_image s)

theorem lex_1_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 524), (Sat.Literal.neg 64)] :=
  (lex_1_61_gate s).prop _ (List.Mem.head _)

theorem lex_1_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 524), (Sat.Literal.neg 61), (Sat.Literal.pos 59)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 524), (Sat.Literal.pos 61), (Sat.Literal.neg 59)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 61), (Sat.Literal.neg 59), (Sat.Literal.pos 524)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 61), (Sat.Literal.pos 59), (Sat.Literal.pos 524)] :=
  (lex_1_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_60_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 524) = lexBefore s permutation1 60 := by
  exact (positive_lex_of_descriptor s 524 permutation1 61 (by rfl)).trans ((lex_skipped s permutation1 60 61 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_60_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation1 60) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation1 60 by rw [image1_eq]; rfl))

theorem lex_1_60_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 525) (Sat.Literal.pos 524) (Sat.Literal.pos 60) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation1 60 (assignment s)
    (Sat.Literal.pos 525) (Sat.Literal.pos 524) (Sat.Literal.pos 60) (Sat.Literal.pos 58) (positive_of_descriptor s 525 (.lex permutation1 60) (by rfl)) (lex_1_60_prefix s) (positive_select s 60) (lex_1_60_image s)

theorem lex_1_60_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 524), (Sat.Literal.pos 60), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation1 60 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 524) (Sat.Literal.pos 60) (Sat.Literal.pos 58) (lex_1_60_prefix s) (positive_select s 60) (lex_1_60_image s)

theorem lex_1_60_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 525), (Sat.Literal.pos 524)] :=
  (lex_1_60_gate s).prop _ (List.Mem.head _)

theorem lex_1_60_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 525), (Sat.Literal.neg 60), (Sat.Literal.pos 58)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_60_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 525), (Sat.Literal.pos 60), (Sat.Literal.neg 58)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_60_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 524), (Sat.Literal.neg 60), (Sat.Literal.neg 58), (Sat.Literal.pos 525)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_60_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 524), (Sat.Literal.pos 60), (Sat.Literal.pos 58), (Sat.Literal.pos 525)] :=
  (lex_1_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_59_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 525) = lexBefore s permutation1 59 := by
  exact (positive_lex_of_descriptor s 525 permutation1 60 (by rfl)).trans ((lex_skipped s permutation1 59 60 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_59_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation1 59) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 64) = permuteMask permutation1 59 by rw [image1_eq]; rfl))

theorem lex_1_59_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 526) (Sat.Literal.pos 525) (Sat.Literal.pos 59) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation1 59 (assignment s)
    (Sat.Literal.pos 526) (Sat.Literal.pos 525) (Sat.Literal.pos 59) (Sat.Literal.pos 61) (positive_of_descriptor s 526 (.lex permutation1 59) (by rfl)) (lex_1_59_prefix s) (positive_select s 59) (lex_1_59_image s)

theorem lex_1_59_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 525), (Sat.Literal.pos 59), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation1 59 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 525) (Sat.Literal.pos 59) (Sat.Literal.pos 61) (lex_1_59_prefix s) (positive_select s 59) (lex_1_59_image s)

theorem lex_1_59_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 526), (Sat.Literal.pos 525)] :=
  (lex_1_59_gate s).prop _ (List.Mem.head _)

theorem lex_1_59_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 526), (Sat.Literal.neg 59), (Sat.Literal.pos 61)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_59_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 526), (Sat.Literal.pos 59), (Sat.Literal.neg 61)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_59_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 525), (Sat.Literal.neg 59), (Sat.Literal.neg 61), (Sat.Literal.pos 526)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_59_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 525), (Sat.Literal.pos 59), (Sat.Literal.pos 61), (Sat.Literal.pos 526)] :=
  (lex_1_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 526) = lexBefore s permutation1 58 := by
  exact (positive_lex_of_descriptor s 526 permutation1 59 (by rfl)).trans ((lex_skipped s permutation1 58 59 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation1 58) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 64) = permuteMask permutation1 58 by rw [image1_eq]; rfl))

theorem lex_1_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 527) (Sat.Literal.pos 526) (Sat.Literal.pos 58) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation1 58 (assignment s)
    (Sat.Literal.pos 527) (Sat.Literal.pos 526) (Sat.Literal.pos 58) (Sat.Literal.pos 60) (positive_of_descriptor s 527 (.lex permutation1 58) (by rfl)) (lex_1_58_prefix s) (positive_select s 58) (lex_1_58_image s)

theorem lex_1_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 526), (Sat.Literal.pos 58), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation1 58 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 526) (Sat.Literal.pos 58) (Sat.Literal.pos 60) (lex_1_58_prefix s) (positive_select s 58) (lex_1_58_image s)

theorem lex_1_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 527), (Sat.Literal.pos 526)] :=
  (lex_1_58_gate s).prop _ (List.Mem.head _)

theorem lex_1_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 527), (Sat.Literal.neg 58), (Sat.Literal.pos 60)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 527), (Sat.Literal.pos 58), (Sat.Literal.neg 60)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 526), (Sat.Literal.neg 58), (Sat.Literal.neg 60), (Sat.Literal.pos 527)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 526), (Sat.Literal.pos 58), (Sat.Literal.pos 60), (Sat.Literal.pos 527)] :=
  (lex_1_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 527) = lexBefore s permutation1 53 := by
  exact (positive_lex_of_descriptor s 527 permutation1 58 (by rfl)).trans ((lex_skipped s permutation1 53 58 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 54 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation1 53) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 64) = permuteMask permutation1 53 by rw [image1_eq]; rfl))

theorem lex_1_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 528) (Sat.Literal.pos 527) (Sat.Literal.pos 53) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation1 53 (assignment s)
    (Sat.Literal.pos 528) (Sat.Literal.pos 527) (Sat.Literal.pos 53) (Sat.Literal.pos 51) (positive_of_descriptor s 528 (.lex permutation1 53) (by rfl)) (lex_1_53_prefix s) (positive_select s 53) (lex_1_53_image s)

theorem lex_1_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 527), (Sat.Literal.pos 53), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation1 53 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 527) (Sat.Literal.pos 53) (Sat.Literal.pos 51) (lex_1_53_prefix s) (positive_select s 53) (lex_1_53_image s)

theorem lex_1_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 528), (Sat.Literal.pos 527)] :=
  (lex_1_53_gate s).prop _ (List.Mem.head _)

theorem lex_1_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 528), (Sat.Literal.neg 53), (Sat.Literal.pos 51)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 528), (Sat.Literal.pos 53), (Sat.Literal.neg 51)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 527), (Sat.Literal.neg 53), (Sat.Literal.neg 51), (Sat.Literal.pos 528)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 527), (Sat.Literal.pos 53), (Sat.Literal.pos 51), (Sat.Literal.pos 528)] :=
  (lex_1_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 528) = lexBefore s permutation1 52 := by
  exact (positive_lex_of_descriptor s 528 permutation1 53 (by rfl)).trans ((lex_skipped s permutation1 52 53 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation1 52) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation1 52 by rw [image1_eq]; rfl))

theorem lex_1_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 529) (Sat.Literal.pos 528) (Sat.Literal.pos 52) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation1 52 (assignment s)
    (Sat.Literal.pos 529) (Sat.Literal.pos 528) (Sat.Literal.pos 52) (Sat.Literal.pos 50) (positive_of_descriptor s 529 (.lex permutation1 52) (by rfl)) (lex_1_52_prefix s) (positive_select s 52) (lex_1_52_image s)

theorem lex_1_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 528), (Sat.Literal.pos 52), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation1 52 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 528) (Sat.Literal.pos 52) (Sat.Literal.pos 50) (lex_1_52_prefix s) (positive_select s 52) (lex_1_52_image s)

theorem lex_1_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 529), (Sat.Literal.pos 528)] :=
  (lex_1_52_gate s).prop _ (List.Mem.head _)

theorem lex_1_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 529), (Sat.Literal.neg 52), (Sat.Literal.pos 50)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 529), (Sat.Literal.pos 52), (Sat.Literal.neg 50)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 528), (Sat.Literal.neg 52), (Sat.Literal.neg 50), (Sat.Literal.pos 529)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 528), (Sat.Literal.pos 52), (Sat.Literal.pos 50), (Sat.Literal.pos 529)] :=
  (lex_1_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_51_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 529) = lexBefore s permutation1 51 := by
  exact (positive_lex_of_descriptor s 529 permutation1 52 (by rfl)).trans ((lex_skipped s permutation1 51 52 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_51_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation1 51) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation1 51 by rw [image1_eq]; rfl))

theorem lex_1_51_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 530) (Sat.Literal.pos 529) (Sat.Literal.pos 51) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation1 51 (assignment s)
    (Sat.Literal.pos 530) (Sat.Literal.pos 529) (Sat.Literal.pos 51) (Sat.Literal.pos 53) (positive_of_descriptor s 530 (.lex permutation1 51) (by rfl)) (lex_1_51_prefix s) (positive_select s 51) (lex_1_51_image s)

theorem lex_1_51_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 529), (Sat.Literal.pos 51), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation1 51 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 529) (Sat.Literal.pos 51) (Sat.Literal.pos 53) (lex_1_51_prefix s) (positive_select s 51) (lex_1_51_image s)

theorem lex_1_51_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 530), (Sat.Literal.pos 529)] :=
  (lex_1_51_gate s).prop _ (List.Mem.head _)

theorem lex_1_51_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 530), (Sat.Literal.neg 51), (Sat.Literal.pos 53)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_51_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 530), (Sat.Literal.pos 51), (Sat.Literal.neg 53)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_51_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 529), (Sat.Literal.neg 51), (Sat.Literal.neg 53), (Sat.Literal.pos 530)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_51_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 529), (Sat.Literal.pos 51), (Sat.Literal.pos 53), (Sat.Literal.pos 530)] :=
  (lex_1_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 530) = lexBefore s permutation1 50 := by
  exact (positive_lex_of_descriptor s 530 permutation1 51 (by rfl)).trans ((lex_skipped s permutation1 50 51 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation1 50) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation1 50 by rw [image1_eq]; rfl))

theorem lex_1_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 531) (Sat.Literal.pos 530) (Sat.Literal.pos 50) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation1 50 (assignment s)
    (Sat.Literal.pos 531) (Sat.Literal.pos 530) (Sat.Literal.pos 50) (Sat.Literal.pos 52) (positive_of_descriptor s 531 (.lex permutation1 50) (by rfl)) (lex_1_50_prefix s) (positive_select s 50) (lex_1_50_image s)

theorem lex_1_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 530), (Sat.Literal.pos 50), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation1 50 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 530) (Sat.Literal.pos 50) (Sat.Literal.pos 52) (lex_1_50_prefix s) (positive_select s 50) (lex_1_50_image s)

theorem lex_1_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 531), (Sat.Literal.pos 530)] :=
  (lex_1_50_gate s).prop _ (List.Mem.head _)

theorem lex_1_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 531), (Sat.Literal.neg 50), (Sat.Literal.pos 52)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 531), (Sat.Literal.pos 50), (Sat.Literal.neg 52)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 530), (Sat.Literal.neg 50), (Sat.Literal.neg 52), (Sat.Literal.pos 531)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 530), (Sat.Literal.pos 50), (Sat.Literal.pos 52), (Sat.Literal.pos 531)] :=
  (lex_1_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 531) = lexBefore s permutation1 45 := by
  exact (positive_lex_of_descriptor s 531 permutation1 50 (by rfl)).trans ((lex_skipped s permutation1 45 50 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 46 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation1 45) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation1 45 by rw [image1_eq]; rfl))

theorem lex_1_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 532) (Sat.Literal.pos 531) (Sat.Literal.pos 45) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation1 45 (assignment s)
    (Sat.Literal.pos 532) (Sat.Literal.pos 531) (Sat.Literal.pos 45) (Sat.Literal.pos 43) (positive_of_descriptor s 532 (.lex permutation1 45) (by rfl)) (lex_1_45_prefix s) (positive_select s 45) (lex_1_45_image s)

theorem lex_1_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 531), (Sat.Literal.pos 45), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation1 45 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 531) (Sat.Literal.pos 45) (Sat.Literal.pos 43) (lex_1_45_prefix s) (positive_select s 45) (lex_1_45_image s)

theorem lex_1_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 532), (Sat.Literal.pos 531)] :=
  (lex_1_45_gate s).prop _ (List.Mem.head _)

theorem lex_1_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 532), (Sat.Literal.neg 45), (Sat.Literal.pos 43)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 532), (Sat.Literal.pos 45), (Sat.Literal.neg 43)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 531), (Sat.Literal.neg 45), (Sat.Literal.neg 43), (Sat.Literal.pos 532)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 531), (Sat.Literal.pos 45), (Sat.Literal.pos 43), (Sat.Literal.pos 532)] :=
  (lex_1_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 532) = lexBefore s permutation1 44 := by
  exact (positive_lex_of_descriptor s 532 permutation1 45 (by rfl)).trans ((lex_skipped s permutation1 44 45 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation1 44) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation1 44 by rw [image1_eq]; rfl))

theorem lex_1_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 533) (Sat.Literal.pos 532) (Sat.Literal.pos 44) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation1 44 (assignment s)
    (Sat.Literal.pos 533) (Sat.Literal.pos 532) (Sat.Literal.pos 44) (Sat.Literal.pos 42) (positive_of_descriptor s 533 (.lex permutation1 44) (by rfl)) (lex_1_44_prefix s) (positive_select s 44) (lex_1_44_image s)

theorem lex_1_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 532), (Sat.Literal.pos 44), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation1 44 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 532) (Sat.Literal.pos 44) (Sat.Literal.pos 42) (lex_1_44_prefix s) (positive_select s 44) (lex_1_44_image s)

theorem lex_1_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 533), (Sat.Literal.pos 532)] :=
  (lex_1_44_gate s).prop _ (List.Mem.head _)

theorem lex_1_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 533), (Sat.Literal.neg 44), (Sat.Literal.pos 42)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 533), (Sat.Literal.pos 44), (Sat.Literal.neg 42)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 532), (Sat.Literal.neg 44), (Sat.Literal.neg 42), (Sat.Literal.pos 533)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 532), (Sat.Literal.pos 44), (Sat.Literal.pos 42), (Sat.Literal.pos 533)] :=
  (lex_1_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 533) = lexBefore s permutation1 43 := by
  exact (positive_lex_of_descriptor s 533 permutation1 44 (by rfl)).trans ((lex_skipped s permutation1 43 44 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation1 43) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation1 43 by rw [image1_eq]; rfl))

theorem lex_1_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 534) (Sat.Literal.pos 533) (Sat.Literal.pos 43) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation1 43 (assignment s)
    (Sat.Literal.pos 534) (Sat.Literal.pos 533) (Sat.Literal.pos 43) (Sat.Literal.pos 45) (positive_of_descriptor s 534 (.lex permutation1 43) (by rfl)) (lex_1_43_prefix s) (positive_select s 43) (lex_1_43_image s)

theorem lex_1_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 533), (Sat.Literal.pos 43), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation1 43 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 533) (Sat.Literal.pos 43) (Sat.Literal.pos 45) (lex_1_43_prefix s) (positive_select s 43) (lex_1_43_image s)

theorem lex_1_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 534), (Sat.Literal.pos 533)] :=
  (lex_1_43_gate s).prop _ (List.Mem.head _)

theorem lex_1_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 534), (Sat.Literal.neg 43), (Sat.Literal.pos 45)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 534), (Sat.Literal.pos 43), (Sat.Literal.neg 45)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 533), (Sat.Literal.neg 43), (Sat.Literal.neg 45), (Sat.Literal.pos 534)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 533), (Sat.Literal.pos 43), (Sat.Literal.pos 45), (Sat.Literal.pos 534)] :=
  (lex_1_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 534) = lexBefore s permutation1 42 := by
  exact (positive_lex_of_descriptor s 534 permutation1 43 (by rfl)).trans ((lex_skipped s permutation1 42 43 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation1 42) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation1 42 by rw [image1_eq]; rfl))

theorem lex_1_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 535) (Sat.Literal.pos 534) (Sat.Literal.pos 42) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation1 42 (assignment s)
    (Sat.Literal.pos 535) (Sat.Literal.pos 534) (Sat.Literal.pos 42) (Sat.Literal.pos 44) (positive_of_descriptor s 535 (.lex permutation1 42) (by rfl)) (lex_1_42_prefix s) (positive_select s 42) (lex_1_42_image s)

theorem lex_1_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 534), (Sat.Literal.pos 42), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation1 42 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 534) (Sat.Literal.pos 42) (Sat.Literal.pos 44) (lex_1_42_prefix s) (positive_select s 42) (lex_1_42_image s)

theorem lex_1_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 535), (Sat.Literal.pos 534)] :=
  (lex_1_42_gate s).prop _ (List.Mem.head _)

theorem lex_1_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 535), (Sat.Literal.neg 42), (Sat.Literal.pos 44)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 535), (Sat.Literal.pos 42), (Sat.Literal.neg 44)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 534), (Sat.Literal.neg 42), (Sat.Literal.neg 44), (Sat.Literal.pos 535)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 534), (Sat.Literal.pos 42), (Sat.Literal.pos 44), (Sat.Literal.pos 535)] :=
  (lex_1_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 535) = lexBefore s permutation1 37 := by
  exact (positive_lex_of_descriptor s 535 permutation1 42 (by rfl)).trans ((lex_skipped s permutation1 37 42 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 38 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation1 37) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 64) = permuteMask permutation1 37 by rw [image1_eq]; rfl))

theorem lex_1_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 536) (Sat.Literal.pos 535) (Sat.Literal.pos 37) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation1 37 (assignment s)
    (Sat.Literal.pos 536) (Sat.Literal.pos 535) (Sat.Literal.pos 37) (Sat.Literal.pos 35) (positive_of_descriptor s 536 (.lex permutation1 37) (by rfl)) (lex_1_37_prefix s) (positive_select s 37) (lex_1_37_image s)

theorem lex_1_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 535), (Sat.Literal.pos 37), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation1 37 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 535) (Sat.Literal.pos 37) (Sat.Literal.pos 35) (lex_1_37_prefix s) (positive_select s 37) (lex_1_37_image s)

theorem lex_1_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 536), (Sat.Literal.pos 535)] :=
  (lex_1_37_gate s).prop _ (List.Mem.head _)

theorem lex_1_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 536), (Sat.Literal.neg 37), (Sat.Literal.pos 35)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 536), (Sat.Literal.pos 37), (Sat.Literal.neg 35)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 535), (Sat.Literal.neg 37), (Sat.Literal.neg 35), (Sat.Literal.pos 536)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 535), (Sat.Literal.pos 37), (Sat.Literal.pos 35), (Sat.Literal.pos 536)] :=
  (lex_1_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_36_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 536) = lexBefore s permutation1 36 := by
  exact (positive_lex_of_descriptor s 536 permutation1 37 (by rfl)).trans ((lex_skipped s permutation1 36 37 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_36_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation1 36) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation1 36 by rw [image1_eq]; rfl))

theorem lex_1_36_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 537) (Sat.Literal.pos 536) (Sat.Literal.pos 36) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation1 36 (assignment s)
    (Sat.Literal.pos 537) (Sat.Literal.pos 536) (Sat.Literal.pos 36) (Sat.Literal.pos 34) (positive_of_descriptor s 537 (.lex permutation1 36) (by rfl)) (lex_1_36_prefix s) (positive_select s 36) (lex_1_36_image s)

theorem lex_1_36_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 536), (Sat.Literal.pos 36), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation1 36 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 536) (Sat.Literal.pos 36) (Sat.Literal.pos 34) (lex_1_36_prefix s) (positive_select s 36) (lex_1_36_image s)

theorem lex_1_36_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 537), (Sat.Literal.pos 536)] :=
  (lex_1_36_gate s).prop _ (List.Mem.head _)

theorem lex_1_36_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 537), (Sat.Literal.neg 36), (Sat.Literal.pos 34)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_36_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 537), (Sat.Literal.pos 36), (Sat.Literal.neg 34)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_36_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 536), (Sat.Literal.neg 36), (Sat.Literal.neg 34), (Sat.Literal.pos 537)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_36_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 536), (Sat.Literal.pos 36), (Sat.Literal.pos 34), (Sat.Literal.pos 537)] :=
  (lex_1_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_35_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 537) = lexBefore s permutation1 35 := by
  exact (positive_lex_of_descriptor s 537 permutation1 36 (by rfl)).trans ((lex_skipped s permutation1 35 36 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_35_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation1 35) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation1 35 by rw [image1_eq]; rfl))

theorem lex_1_35_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 538) (Sat.Literal.pos 537) (Sat.Literal.pos 35) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation1 35 (assignment s)
    (Sat.Literal.pos 538) (Sat.Literal.pos 537) (Sat.Literal.pos 35) (Sat.Literal.pos 37) (positive_of_descriptor s 538 (.lex permutation1 35) (by rfl)) (lex_1_35_prefix s) (positive_select s 35) (lex_1_35_image s)

theorem lex_1_35_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 537), (Sat.Literal.pos 35), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation1 35 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 537) (Sat.Literal.pos 35) (Sat.Literal.pos 37) (lex_1_35_prefix s) (positive_select s 35) (lex_1_35_image s)

theorem lex_1_35_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 538), (Sat.Literal.pos 537)] :=
  (lex_1_35_gate s).prop _ (List.Mem.head _)

theorem lex_1_35_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 538), (Sat.Literal.neg 35), (Sat.Literal.pos 37)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_35_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 538), (Sat.Literal.pos 35), (Sat.Literal.neg 37)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_35_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 537), (Sat.Literal.neg 35), (Sat.Literal.neg 37), (Sat.Literal.pos 538)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_35_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 537), (Sat.Literal.pos 35), (Sat.Literal.pos 37), (Sat.Literal.pos 538)] :=
  (lex_1_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 538) = lexBefore s permutation1 34 := by
  exact (positive_lex_of_descriptor s 538 permutation1 35 (by rfl)).trans ((lex_skipped s permutation1 34 35 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation1 34) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 64) = permuteMask permutation1 34 by rw [image1_eq]; rfl))

theorem lex_1_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 539) (Sat.Literal.pos 538) (Sat.Literal.pos 34) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation1 34 (assignment s)
    (Sat.Literal.pos 539) (Sat.Literal.pos 538) (Sat.Literal.pos 34) (Sat.Literal.pos 36) (positive_of_descriptor s 539 (.lex permutation1 34) (by rfl)) (lex_1_34_prefix s) (positive_select s 34) (lex_1_34_image s)

theorem lex_1_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 538), (Sat.Literal.pos 34), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation1 34 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 538) (Sat.Literal.pos 34) (Sat.Literal.pos 36) (lex_1_34_prefix s) (positive_select s 34) (lex_1_34_image s)

theorem lex_1_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 539), (Sat.Literal.pos 538)] :=
  (lex_1_34_gate s).prop _ (List.Mem.head _)

theorem lex_1_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 539), (Sat.Literal.neg 34), (Sat.Literal.pos 36)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 539), (Sat.Literal.pos 34), (Sat.Literal.neg 36)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 538), (Sat.Literal.neg 34), (Sat.Literal.neg 36), (Sat.Literal.pos 539)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 538), (Sat.Literal.pos 34), (Sat.Literal.pos 36), (Sat.Literal.pos 539)] :=
  (lex_1_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 539) = lexBefore s permutation1 29 := by
  exact (positive_lex_of_descriptor s 539 permutation1 34 (by rfl)).trans ((lex_skipped s permutation1 29 34 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 30 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation1 29) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 64) = permuteMask permutation1 29 by rw [image1_eq]; rfl))

theorem lex_1_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 540) (Sat.Literal.pos 539) (Sat.Literal.pos 29) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation1 29 (assignment s)
    (Sat.Literal.pos 540) (Sat.Literal.pos 539) (Sat.Literal.pos 29) (Sat.Literal.pos 27) (positive_of_descriptor s 540 (.lex permutation1 29) (by rfl)) (lex_1_29_prefix s) (positive_select s 29) (lex_1_29_image s)

theorem lex_1_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 539), (Sat.Literal.pos 29), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation1 29 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 539) (Sat.Literal.pos 29) (Sat.Literal.pos 27) (lex_1_29_prefix s) (positive_select s 29) (lex_1_29_image s)

theorem lex_1_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 540), (Sat.Literal.pos 539)] :=
  (lex_1_29_gate s).prop _ (List.Mem.head _)

theorem lex_1_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 540), (Sat.Literal.neg 29), (Sat.Literal.pos 27)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 540), (Sat.Literal.pos 29), (Sat.Literal.neg 27)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 539), (Sat.Literal.neg 29), (Sat.Literal.neg 27), (Sat.Literal.pos 540)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 539), (Sat.Literal.pos 29), (Sat.Literal.pos 27), (Sat.Literal.pos 540)] :=
  (lex_1_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_28_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 540) = lexBefore s permutation1 28 := by
  exact (positive_lex_of_descriptor s 540 permutation1 29 (by rfl)).trans ((lex_skipped s permutation1 28 29 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_28_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation1 28) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation1 28 by rw [image1_eq]; rfl))

theorem lex_1_28_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 541) (Sat.Literal.pos 540) (Sat.Literal.pos 28) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation1 28 (assignment s)
    (Sat.Literal.pos 541) (Sat.Literal.pos 540) (Sat.Literal.pos 28) (Sat.Literal.pos 26) (positive_of_descriptor s 541 (.lex permutation1 28) (by rfl)) (lex_1_28_prefix s) (positive_select s 28) (lex_1_28_image s)

theorem lex_1_28_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 540), (Sat.Literal.pos 28), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation1 28 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 540) (Sat.Literal.pos 28) (Sat.Literal.pos 26) (lex_1_28_prefix s) (positive_select s 28) (lex_1_28_image s)

theorem lex_1_28_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 541), (Sat.Literal.pos 540)] :=
  (lex_1_28_gate s).prop _ (List.Mem.head _)

theorem lex_1_28_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 541), (Sat.Literal.neg 28), (Sat.Literal.pos 26)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_28_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 541), (Sat.Literal.pos 28), (Sat.Literal.neg 26)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_28_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 540), (Sat.Literal.neg 28), (Sat.Literal.neg 26), (Sat.Literal.pos 541)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_28_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 540), (Sat.Literal.pos 28), (Sat.Literal.pos 26), (Sat.Literal.pos 541)] :=
  (lex_1_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_27_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 541) = lexBefore s permutation1 27 := by
  exact (positive_lex_of_descriptor s 541 permutation1 28 (by rfl)).trans ((lex_skipped s permutation1 27 28 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_27_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation1 27) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation1 27 by rw [image1_eq]; rfl))

theorem lex_1_27_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 542) (Sat.Literal.pos 541) (Sat.Literal.pos 27) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation1 27 (assignment s)
    (Sat.Literal.pos 542) (Sat.Literal.pos 541) (Sat.Literal.pos 27) (Sat.Literal.pos 29) (positive_of_descriptor s 542 (.lex permutation1 27) (by rfl)) (lex_1_27_prefix s) (positive_select s 27) (lex_1_27_image s)

theorem lex_1_27_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 541), (Sat.Literal.pos 27), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation1 27 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 541) (Sat.Literal.pos 27) (Sat.Literal.pos 29) (lex_1_27_prefix s) (positive_select s 27) (lex_1_27_image s)

theorem lex_1_27_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 542), (Sat.Literal.pos 541)] :=
  (lex_1_27_gate s).prop _ (List.Mem.head _)

theorem lex_1_27_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 542), (Sat.Literal.neg 27), (Sat.Literal.pos 29)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_27_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 542), (Sat.Literal.pos 27), (Sat.Literal.neg 29)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_27_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 541), (Sat.Literal.neg 27), (Sat.Literal.neg 29), (Sat.Literal.pos 542)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_27_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 541), (Sat.Literal.pos 27), (Sat.Literal.pos 29), (Sat.Literal.pos 542)] :=
  (lex_1_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 542) = lexBefore s permutation1 26 := by
  exact (positive_lex_of_descriptor s 542 permutation1 27 (by rfl)).trans ((lex_skipped s permutation1 26 27 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation1 26) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 64) = permuteMask permutation1 26 by rw [image1_eq]; rfl))

theorem lex_1_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 543) (Sat.Literal.pos 542) (Sat.Literal.pos 26) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation1 26 (assignment s)
    (Sat.Literal.pos 543) (Sat.Literal.pos 542) (Sat.Literal.pos 26) (Sat.Literal.pos 28) (positive_of_descriptor s 543 (.lex permutation1 26) (by rfl)) (lex_1_26_prefix s) (positive_select s 26) (lex_1_26_image s)

theorem lex_1_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 542), (Sat.Literal.pos 26), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation1 26 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 542) (Sat.Literal.pos 26) (Sat.Literal.pos 28) (lex_1_26_prefix s) (positive_select s 26) (lex_1_26_image s)

theorem lex_1_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 543), (Sat.Literal.pos 542)] :=
  (lex_1_26_gate s).prop _ (List.Mem.head _)

theorem lex_1_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 543), (Sat.Literal.neg 26), (Sat.Literal.pos 28)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 543), (Sat.Literal.pos 26), (Sat.Literal.neg 28)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 542), (Sat.Literal.neg 26), (Sat.Literal.neg 28), (Sat.Literal.pos 543)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 542), (Sat.Literal.pos 26), (Sat.Literal.pos 28), (Sat.Literal.pos 543)] :=
  (lex_1_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 543) = lexBefore s permutation1 21 := by
  exact (positive_lex_of_descriptor s 543 permutation1 26 (by rfl)).trans ((lex_skipped s permutation1 21 26 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 22 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation1 21) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation1 21 by rw [image1_eq]; rfl))

theorem lex_1_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 544) (Sat.Literal.pos 543) (Sat.Literal.pos 21) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation1 21 (assignment s)
    (Sat.Literal.pos 544) (Sat.Literal.pos 543) (Sat.Literal.pos 21) (Sat.Literal.pos 19) (positive_of_descriptor s 544 (.lex permutation1 21) (by rfl)) (lex_1_21_prefix s) (positive_select s 21) (lex_1_21_image s)

theorem lex_1_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 543), (Sat.Literal.pos 21), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation1 21 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 543) (Sat.Literal.pos 21) (Sat.Literal.pos 19) (lex_1_21_prefix s) (positive_select s 21) (lex_1_21_image s)

theorem lex_1_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 544), (Sat.Literal.pos 543)] :=
  (lex_1_21_gate s).prop _ (List.Mem.head _)

theorem lex_1_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 544), (Sat.Literal.neg 21), (Sat.Literal.pos 19)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 544), (Sat.Literal.pos 21), (Sat.Literal.neg 19)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 543), (Sat.Literal.neg 21), (Sat.Literal.neg 19), (Sat.Literal.pos 544)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 543), (Sat.Literal.pos 21), (Sat.Literal.pos 19), (Sat.Literal.pos 544)] :=
  (lex_1_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 544) = lexBefore s permutation1 20 := by
  exact (positive_lex_of_descriptor s 544 permutation1 21 (by rfl)).trans ((lex_skipped s permutation1 20 21 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation1 20) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation1 20 by rw [image1_eq]; rfl))

theorem lex_1_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 545) (Sat.Literal.pos 544) (Sat.Literal.pos 20) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation1 20 (assignment s)
    (Sat.Literal.pos 545) (Sat.Literal.pos 544) (Sat.Literal.pos 20) (Sat.Literal.pos 18) (positive_of_descriptor s 545 (.lex permutation1 20) (by rfl)) (lex_1_20_prefix s) (positive_select s 20) (lex_1_20_image s)

theorem lex_1_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 544), (Sat.Literal.pos 20), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation1 20 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 544) (Sat.Literal.pos 20) (Sat.Literal.pos 18) (lex_1_20_prefix s) (positive_select s 20) (lex_1_20_image s)

theorem lex_1_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 545), (Sat.Literal.pos 544)] :=
  (lex_1_20_gate s).prop _ (List.Mem.head _)

theorem lex_1_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 545), (Sat.Literal.neg 20), (Sat.Literal.pos 18)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 545), (Sat.Literal.pos 20), (Sat.Literal.neg 18)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 544), (Sat.Literal.neg 20), (Sat.Literal.neg 18), (Sat.Literal.pos 545)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 544), (Sat.Literal.pos 20), (Sat.Literal.pos 18), (Sat.Literal.pos 545)] :=
  (lex_1_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 545) = lexBefore s permutation1 19 := by
  exact (positive_lex_of_descriptor s 545 permutation1 20 (by rfl)).trans ((lex_skipped s permutation1 19 20 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation1 19) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation1 19 by rw [image1_eq]; rfl))

theorem lex_1_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 546) (Sat.Literal.pos 545) (Sat.Literal.pos 19) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation1 19 (assignment s)
    (Sat.Literal.pos 546) (Sat.Literal.pos 545) (Sat.Literal.pos 19) (Sat.Literal.pos 21) (positive_of_descriptor s 546 (.lex permutation1 19) (by rfl)) (lex_1_19_prefix s) (positive_select s 19) (lex_1_19_image s)

theorem lex_1_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 545), (Sat.Literal.pos 19), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation1 19 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 545) (Sat.Literal.pos 19) (Sat.Literal.pos 21) (lex_1_19_prefix s) (positive_select s 19) (lex_1_19_image s)

theorem lex_1_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 546), (Sat.Literal.pos 545)] :=
  (lex_1_19_gate s).prop _ (List.Mem.head _)

theorem lex_1_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 546), (Sat.Literal.neg 19), (Sat.Literal.pos 21)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 546), (Sat.Literal.pos 19), (Sat.Literal.neg 21)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 545), (Sat.Literal.neg 19), (Sat.Literal.neg 21), (Sat.Literal.pos 546)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 545), (Sat.Literal.pos 19), (Sat.Literal.pos 21), (Sat.Literal.pos 546)] :=
  (lex_1_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 546) = lexBefore s permutation1 18 := by
  exact (positive_lex_of_descriptor s 546 permutation1 19 (by rfl)).trans ((lex_skipped s permutation1 18 19 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation1 18) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation1 18 by rw [image1_eq]; rfl))

theorem lex_1_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 547) (Sat.Literal.pos 546) (Sat.Literal.pos 18) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation1 18 (assignment s)
    (Sat.Literal.pos 547) (Sat.Literal.pos 546) (Sat.Literal.pos 18) (Sat.Literal.pos 20) (positive_of_descriptor s 547 (.lex permutation1 18) (by rfl)) (lex_1_18_prefix s) (positive_select s 18) (lex_1_18_image s)

theorem lex_1_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 546), (Sat.Literal.pos 18), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation1 18 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 546) (Sat.Literal.pos 18) (Sat.Literal.pos 20) (lex_1_18_prefix s) (positive_select s 18) (lex_1_18_image s)

theorem lex_1_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 547), (Sat.Literal.pos 546)] :=
  (lex_1_18_gate s).prop _ (List.Mem.head _)

theorem lex_1_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 547), (Sat.Literal.neg 18), (Sat.Literal.pos 20)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 547), (Sat.Literal.pos 18), (Sat.Literal.neg 20)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 546), (Sat.Literal.neg 18), (Sat.Literal.neg 20), (Sat.Literal.pos 547)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 546), (Sat.Literal.pos 18), (Sat.Literal.pos 20), (Sat.Literal.pos 547)] :=
  (lex_1_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 547) = lexBefore s permutation1 13 := by
  exact (positive_lex_of_descriptor s 547 permutation1 18 (by rfl)).trans ((lex_skipped s permutation1 13 18 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 14 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation1 13) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation1 13 by rw [image1_eq]; rfl))

theorem lex_1_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 548) (Sat.Literal.pos 547) (Sat.Literal.pos 13) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation1 13 (assignment s)
    (Sat.Literal.pos 548) (Sat.Literal.pos 547) (Sat.Literal.pos 13) (Sat.Literal.pos 11) (positive_of_descriptor s 548 (.lex permutation1 13) (by rfl)) (lex_1_13_prefix s) (positive_select s 13) (lex_1_13_image s)

theorem lex_1_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 547), (Sat.Literal.pos 13), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation1 13 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 547) (Sat.Literal.pos 13) (Sat.Literal.pos 11) (lex_1_13_prefix s) (positive_select s 13) (lex_1_13_image s)

theorem lex_1_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 548), (Sat.Literal.pos 547)] :=
  (lex_1_13_gate s).prop _ (List.Mem.head _)

theorem lex_1_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 548), (Sat.Literal.neg 13), (Sat.Literal.pos 11)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 548), (Sat.Literal.pos 13), (Sat.Literal.neg 11)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 547), (Sat.Literal.neg 13), (Sat.Literal.neg 11), (Sat.Literal.pos 548)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 547), (Sat.Literal.pos 13), (Sat.Literal.pos 11), (Sat.Literal.pos 548)] :=
  (lex_1_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_12_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 548) = lexBefore s permutation1 12 := by
  exact (positive_lex_of_descriptor s 548 permutation1 13 (by rfl)).trans ((lex_skipped s permutation1 12 13 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_12_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation1 12) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation1 12 by rw [image1_eq]; rfl))

theorem lex_1_12_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 549) (Sat.Literal.pos 548) (Sat.Literal.pos 12) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation1 12 (assignment s)
    (Sat.Literal.pos 549) (Sat.Literal.pos 548) (Sat.Literal.pos 12) (Sat.Literal.pos 10) (positive_of_descriptor s 549 (.lex permutation1 12) (by rfl)) (lex_1_12_prefix s) (positive_select s 12) (lex_1_12_image s)

theorem lex_1_12_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 548), (Sat.Literal.pos 12), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation1 12 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 548) (Sat.Literal.pos 12) (Sat.Literal.pos 10) (lex_1_12_prefix s) (positive_select s 12) (lex_1_12_image s)

theorem lex_1_12_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 549), (Sat.Literal.pos 548)] :=
  (lex_1_12_gate s).prop _ (List.Mem.head _)

theorem lex_1_12_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 549), (Sat.Literal.neg 12), (Sat.Literal.pos 10)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_12_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 549), (Sat.Literal.pos 12), (Sat.Literal.neg 10)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_12_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 548), (Sat.Literal.neg 12), (Sat.Literal.neg 10), (Sat.Literal.pos 549)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_12_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 548), (Sat.Literal.pos 12), (Sat.Literal.pos 10), (Sat.Literal.pos 549)] :=
  (lex_1_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 549) = lexBefore s permutation1 11 := by
  exact (positive_lex_of_descriptor s 549 permutation1 12 (by rfl)).trans ((lex_skipped s permutation1 11 12 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation1 11) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation1 11 by rw [image1_eq]; rfl))

theorem lex_1_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 550) (Sat.Literal.pos 549) (Sat.Literal.pos 11) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation1 11 (assignment s)
    (Sat.Literal.pos 550) (Sat.Literal.pos 549) (Sat.Literal.pos 11) (Sat.Literal.pos 13) (positive_of_descriptor s 550 (.lex permutation1 11) (by rfl)) (lex_1_11_prefix s) (positive_select s 11) (lex_1_11_image s)

theorem lex_1_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 549), (Sat.Literal.pos 11), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation1 11 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 549) (Sat.Literal.pos 11) (Sat.Literal.pos 13) (lex_1_11_prefix s) (positive_select s 11) (lex_1_11_image s)

theorem lex_1_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 550), (Sat.Literal.pos 549)] :=
  (lex_1_11_gate s).prop _ (List.Mem.head _)

theorem lex_1_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 550), (Sat.Literal.neg 11), (Sat.Literal.pos 13)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 550), (Sat.Literal.pos 11), (Sat.Literal.neg 13)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 549), (Sat.Literal.neg 11), (Sat.Literal.neg 13), (Sat.Literal.pos 550)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 549), (Sat.Literal.pos 11), (Sat.Literal.pos 13), (Sat.Literal.pos 550)] :=
  (lex_1_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 550) = lexBefore s permutation1 10 := by
  exact (positive_lex_of_descriptor s 550 permutation1 11 (by rfl)).trans ((lex_skipped s permutation1 10 11 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation1 10) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 64) = permuteMask permutation1 10 by rw [image1_eq]; rfl))

theorem lex_1_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 551) (Sat.Literal.pos 550) (Sat.Literal.pos 10) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation1 10 (assignment s)
    (Sat.Literal.pos 551) (Sat.Literal.pos 550) (Sat.Literal.pos 10) (Sat.Literal.pos 12) (positive_of_descriptor s 551 (.lex permutation1 10) (by rfl)) (lex_1_10_prefix s) (positive_select s 10) (lex_1_10_image s)

theorem lex_1_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 550), (Sat.Literal.pos 10), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation1 10 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 550) (Sat.Literal.pos 10) (Sat.Literal.pos 12) (lex_1_10_prefix s) (positive_select s 10) (lex_1_10_image s)

theorem lex_1_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 551), (Sat.Literal.pos 550)] :=
  (lex_1_10_gate s).prop _ (List.Mem.head _)

theorem lex_1_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 551), (Sat.Literal.neg 10), (Sat.Literal.pos 12)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 551), (Sat.Literal.pos 10), (Sat.Literal.neg 12)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 550), (Sat.Literal.neg 10), (Sat.Literal.neg 12), (Sat.Literal.pos 551)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 550), (Sat.Literal.pos 10), (Sat.Literal.pos 12), (Sat.Literal.pos 551)] :=
  (lex_1_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 551) = lexBefore s permutation1 5 := by
  exact (positive_lex_of_descriptor s 551 permutation1 10 (by rfl)).trans ((lex_skipped s permutation1 5 10 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 6 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation1 5) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 64) = permuteMask permutation1 5 by rw [image1_eq]; rfl))

theorem lex_1_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 552) (Sat.Literal.pos 551) (Sat.Literal.pos 5) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation1 5 (assignment s)
    (Sat.Literal.pos 552) (Sat.Literal.pos 551) (Sat.Literal.pos 5) (Sat.Literal.pos 3) (positive_of_descriptor s 552 (.lex permutation1 5) (by rfl)) (lex_1_5_prefix s) (positive_select s 5) (lex_1_5_image s)

theorem lex_1_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 551), (Sat.Literal.pos 5), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation1 5 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 551) (Sat.Literal.pos 5) (Sat.Literal.pos 3) (lex_1_5_prefix s) (positive_select s 5) (lex_1_5_image s)

theorem lex_1_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 552), (Sat.Literal.pos 551)] :=
  (lex_1_5_gate s).prop _ (List.Mem.head _)

theorem lex_1_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 552), (Sat.Literal.neg 5), (Sat.Literal.pos 3)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 552), (Sat.Literal.pos 5), (Sat.Literal.neg 3)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 551), (Sat.Literal.neg 5), (Sat.Literal.neg 3), (Sat.Literal.pos 552)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 551), (Sat.Literal.pos 5), (Sat.Literal.pos 3), (Sat.Literal.pos 552)] :=
  (lex_1_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_4_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 552) = lexBefore s permutation1 4 := by
  exact (positive_lex_of_descriptor s 552 permutation1 5 (by rfl)).trans ((lex_skipped s permutation1 4 5 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_4_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation1 4) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 64) = permuteMask permutation1 4 by rw [image1_eq]; rfl))

theorem lex_1_4_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 553) (Sat.Literal.pos 552) (Sat.Literal.pos 4) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation1 4 (assignment s)
    (Sat.Literal.pos 553) (Sat.Literal.pos 552) (Sat.Literal.pos 4) (Sat.Literal.pos 2) (positive_of_descriptor s 553 (.lex permutation1 4) (by rfl)) (lex_1_4_prefix s) (positive_select s 4) (lex_1_4_image s)

theorem lex_1_4_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 552), (Sat.Literal.pos 4), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation1 4 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 552) (Sat.Literal.pos 4) (Sat.Literal.pos 2) (lex_1_4_prefix s) (positive_select s 4) (lex_1_4_image s)

theorem lex_1_4_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 553), (Sat.Literal.pos 552)] :=
  (lex_1_4_gate s).prop _ (List.Mem.head _)

theorem lex_1_4_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 553), (Sat.Literal.neg 4), (Sat.Literal.pos 2)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_4_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 553), (Sat.Literal.pos 4), (Sat.Literal.neg 2)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_4_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 552), (Sat.Literal.neg 4), (Sat.Literal.neg 2), (Sat.Literal.pos 553)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_4_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 552), (Sat.Literal.pos 4), (Sat.Literal.pos 2), (Sat.Literal.pos 553)] :=
  (lex_1_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_3_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 553) = lexBefore s permutation1 3 := by
  exact (positive_lex_of_descriptor s 553 permutation1 4 (by rfl)).trans ((lex_skipped s permutation1 3 4 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_3_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation1 3) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation1 3 by rw [image1_eq]; rfl))

theorem lex_1_3_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 554) (Sat.Literal.pos 553) (Sat.Literal.pos 3) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation1 3 (assignment s)
    (Sat.Literal.pos 554) (Sat.Literal.pos 553) (Sat.Literal.pos 3) (Sat.Literal.pos 5) (positive_of_descriptor s 554 (.lex permutation1 3) (by rfl)) (lex_1_3_prefix s) (positive_select s 3) (lex_1_3_image s)

theorem lex_1_3_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 553), (Sat.Literal.pos 3), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation1 3 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 553) (Sat.Literal.pos 3) (Sat.Literal.pos 5) (lex_1_3_prefix s) (positive_select s 3) (lex_1_3_image s)

theorem lex_1_3_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 554), (Sat.Literal.pos 553)] :=
  (lex_1_3_gate s).prop _ (List.Mem.head _)

theorem lex_1_3_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 554), (Sat.Literal.neg 3), (Sat.Literal.pos 5)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_3_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 554), (Sat.Literal.pos 3), (Sat.Literal.neg 5)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_3_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 553), (Sat.Literal.neg 3), (Sat.Literal.neg 5), (Sat.Literal.pos 554)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_3_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 553), (Sat.Literal.pos 3), (Sat.Literal.pos 5), (Sat.Literal.pos 554)] :=
  (lex_1_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_2_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 554) = lexBefore s permutation1 2 := by
  exact (positive_lex_of_descriptor s 554 permutation1 3 (by rfl)).trans ((lex_skipped s permutation1 2 3 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_2_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation1 2) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 64) = permuteMask permutation1 2 by rw [image1_eq]; rfl))

theorem lex_1_2_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 555) (Sat.Literal.pos 554) (Sat.Literal.pos 2) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation1 2 (assignment s)
    (Sat.Literal.pos 555) (Sat.Literal.pos 554) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (positive_of_descriptor s 555 (.lex permutation1 2) (by rfl)) (lex_1_2_prefix s) (positive_select s 2) (lex_1_2_image s)

theorem lex_1_2_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 554), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation1 2 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 554) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (lex_1_2_prefix s) (positive_select s 2) (lex_1_2_image s)

theorem lex_1_2_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 555), (Sat.Literal.pos 554)] :=
  (lex_1_2_gate s).prop _ (List.Mem.head _)

theorem lex_1_2_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 555), (Sat.Literal.neg 2), (Sat.Literal.pos 4)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_2_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 555), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_2_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 554), (Sat.Literal.neg 2), (Sat.Literal.neg 4), (Sat.Literal.pos 555)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_2_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 554), (Sat.Literal.pos 2), (Sat.Literal.pos 4), (Sat.Literal.pos 555)] :=
  (lex_1_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_59_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation2 59 := by
  exact (negative_falsum s).trans ((lex_first s permutation2 59 (by intro j hj; rw [image2_eq]; exact fixedOnRange_spec image2 60 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_2_59_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation2 59) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 64) = permuteMask permutation2 59 by rw [image2_eq]; rfl))

theorem lex_2_59_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 556) (Sat.Literal.neg 64) (Sat.Literal.pos 59) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation2 59 (assignment s)
    (Sat.Literal.pos 556) (Sat.Literal.neg 64) (Sat.Literal.pos 59) (Sat.Literal.pos 55) (positive_of_descriptor s 556 (.lex permutation2 59) (by rfl)) (lex_2_59_prefix s) (positive_select s 59) (lex_2_59_image s)

theorem lex_2_59_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 59), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation2 59 (hmax permutation2) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 59) (Sat.Literal.pos 55) (lex_2_59_prefix s) (positive_select s 59) (lex_2_59_image s)

theorem lex_2_59_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 556), (Sat.Literal.neg 64)] :=
  (lex_2_59_gate s).prop _ (List.Mem.head _)

theorem lex_2_59_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 556), (Sat.Literal.neg 59), (Sat.Literal.pos 55)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_59_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 556), (Sat.Literal.pos 59), (Sat.Literal.neg 55)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_59_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 59), (Sat.Literal.neg 55), (Sat.Literal.pos 556)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_59_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 59), (Sat.Literal.pos 55), (Sat.Literal.pos 556)] :=
  (lex_2_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 556) = lexBefore s permutation2 58 := by
  exact (positive_lex_of_descriptor s 556 permutation2 59 (by rfl)).trans ((lex_skipped s permutation2 58 59 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation2 58) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 64) = permuteMask permutation2 58 by rw [image2_eq]; rfl))

theorem lex_2_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 557) (Sat.Literal.pos 556) (Sat.Literal.pos 58) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation2 58 (assignment s)
    (Sat.Literal.pos 557) (Sat.Literal.pos 556) (Sat.Literal.pos 58) (Sat.Literal.pos 54) (positive_of_descriptor s 557 (.lex permutation2 58) (by rfl)) (lex_2_58_prefix s) (positive_select s 58) (lex_2_58_image s)

theorem lex_2_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 556), (Sat.Literal.pos 58), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation2 58 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 556) (Sat.Literal.pos 58) (Sat.Literal.pos 54) (lex_2_58_prefix s) (positive_select s 58) (lex_2_58_image s)

theorem lex_2_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 557), (Sat.Literal.pos 556)] :=
  (lex_2_58_gate s).prop _ (List.Mem.head _)

theorem lex_2_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 557), (Sat.Literal.neg 58), (Sat.Literal.pos 54)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 557), (Sat.Literal.pos 58), (Sat.Literal.neg 54)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 556), (Sat.Literal.neg 58), (Sat.Literal.neg 54), (Sat.Literal.pos 557)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 556), (Sat.Literal.pos 58), (Sat.Literal.pos 54), (Sat.Literal.pos 557)] :=
  (lex_2_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_57_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 557) = lexBefore s permutation2 57 := by
  exact (positive_lex_of_descriptor s 557 permutation2 58 (by rfl)).trans ((lex_skipped s permutation2 57 58 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_57_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation2 57) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation2 57 by rw [image2_eq]; rfl))

theorem lex_2_57_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 558) (Sat.Literal.pos 557) (Sat.Literal.pos 57) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation2 57 (assignment s)
    (Sat.Literal.pos 558) (Sat.Literal.pos 557) (Sat.Literal.pos 57) (Sat.Literal.pos 53) (positive_of_descriptor s 558 (.lex permutation2 57) (by rfl)) (lex_2_57_prefix s) (positive_select s 57) (lex_2_57_image s)

theorem lex_2_57_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 557), (Sat.Literal.pos 57), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation2 57 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 557) (Sat.Literal.pos 57) (Sat.Literal.pos 53) (lex_2_57_prefix s) (positive_select s 57) (lex_2_57_image s)

theorem lex_2_57_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 558), (Sat.Literal.pos 557)] :=
  (lex_2_57_gate s).prop _ (List.Mem.head _)

theorem lex_2_57_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 558), (Sat.Literal.neg 57), (Sat.Literal.pos 53)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_57_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 558), (Sat.Literal.pos 57), (Sat.Literal.neg 53)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_57_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 557), (Sat.Literal.neg 57), (Sat.Literal.neg 53), (Sat.Literal.pos 558)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_57_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 557), (Sat.Literal.pos 57), (Sat.Literal.pos 53), (Sat.Literal.pos 558)] :=
  (lex_2_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_56_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 558) = lexBefore s permutation2 56 := by
  exact (positive_lex_of_descriptor s 558 permutation2 57 (by rfl)).trans ((lex_skipped s permutation2 56 57 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_56_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation2 56) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation2 56 by rw [image2_eq]; rfl))

theorem lex_2_56_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 559) (Sat.Literal.pos 558) (Sat.Literal.pos 56) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation2 56 (assignment s)
    (Sat.Literal.pos 559) (Sat.Literal.pos 558) (Sat.Literal.pos 56) (Sat.Literal.pos 52) (positive_of_descriptor s 559 (.lex permutation2 56) (by rfl)) (lex_2_56_prefix s) (positive_select s 56) (lex_2_56_image s)

theorem lex_2_56_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 558), (Sat.Literal.pos 56), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation2 56 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 558) (Sat.Literal.pos 56) (Sat.Literal.pos 52) (lex_2_56_prefix s) (positive_select s 56) (lex_2_56_image s)

theorem lex_2_56_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 559), (Sat.Literal.pos 558)] :=
  (lex_2_56_gate s).prop _ (List.Mem.head _)

theorem lex_2_56_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 559), (Sat.Literal.neg 56), (Sat.Literal.pos 52)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_56_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 559), (Sat.Literal.pos 56), (Sat.Literal.neg 52)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_56_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 558), (Sat.Literal.neg 56), (Sat.Literal.neg 52), (Sat.Literal.pos 559)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_56_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 558), (Sat.Literal.pos 56), (Sat.Literal.pos 52), (Sat.Literal.pos 559)] :=
  (lex_2_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_55_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 559) = lexBefore s permutation2 55 := by
  exact (positive_lex_of_descriptor s 559 permutation2 56 (by rfl)).trans ((lex_skipped s permutation2 55 56 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_55_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation2 55) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 64) = permuteMask permutation2 55 by rw [image2_eq]; rfl))

theorem lex_2_55_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 560) (Sat.Literal.pos 559) (Sat.Literal.pos 55) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation2 55 (assignment s)
    (Sat.Literal.pos 560) (Sat.Literal.pos 559) (Sat.Literal.pos 55) (Sat.Literal.pos 59) (positive_of_descriptor s 560 (.lex permutation2 55) (by rfl)) (lex_2_55_prefix s) (positive_select s 55) (lex_2_55_image s)

theorem lex_2_55_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 559), (Sat.Literal.pos 55), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation2 55 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 559) (Sat.Literal.pos 55) (Sat.Literal.pos 59) (lex_2_55_prefix s) (positive_select s 55) (lex_2_55_image s)

theorem lex_2_55_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 560), (Sat.Literal.pos 559)] :=
  (lex_2_55_gate s).prop _ (List.Mem.head _)

theorem lex_2_55_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 560), (Sat.Literal.neg 55), (Sat.Literal.pos 59)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_55_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 560), (Sat.Literal.pos 55), (Sat.Literal.neg 59)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_55_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 559), (Sat.Literal.neg 55), (Sat.Literal.neg 59), (Sat.Literal.pos 560)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_55_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 559), (Sat.Literal.pos 55), (Sat.Literal.pos 59), (Sat.Literal.pos 560)] :=
  (lex_2_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_54_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 560) = lexBefore s permutation2 54 := by
  exact (positive_lex_of_descriptor s 560 permutation2 55 (by rfl)).trans ((lex_skipped s permutation2 54 55 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_54_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation2 54) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation2 54 by rw [image2_eq]; rfl))

theorem lex_2_54_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 561) (Sat.Literal.pos 560) (Sat.Literal.pos 54) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation2 54 (assignment s)
    (Sat.Literal.pos 561) (Sat.Literal.pos 560) (Sat.Literal.pos 54) (Sat.Literal.pos 58) (positive_of_descriptor s 561 (.lex permutation2 54) (by rfl)) (lex_2_54_prefix s) (positive_select s 54) (lex_2_54_image s)

theorem lex_2_54_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 560), (Sat.Literal.pos 54), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation2 54 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 560) (Sat.Literal.pos 54) (Sat.Literal.pos 58) (lex_2_54_prefix s) (positive_select s 54) (lex_2_54_image s)

theorem lex_2_54_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 561), (Sat.Literal.pos 560)] :=
  (lex_2_54_gate s).prop _ (List.Mem.head _)

theorem lex_2_54_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 561), (Sat.Literal.neg 54), (Sat.Literal.pos 58)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_54_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 561), (Sat.Literal.pos 54), (Sat.Literal.neg 58)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_54_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 560), (Sat.Literal.neg 54), (Sat.Literal.neg 58), (Sat.Literal.pos 561)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_54_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 560), (Sat.Literal.pos 54), (Sat.Literal.pos 58), (Sat.Literal.pos 561)] :=
  (lex_2_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 561) = lexBefore s permutation2 53 := by
  exact (positive_lex_of_descriptor s 561 permutation2 54 (by rfl)).trans ((lex_skipped s permutation2 53 54 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation2 53) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 64) = permuteMask permutation2 53 by rw [image2_eq]; rfl))

theorem lex_2_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 562) (Sat.Literal.pos 561) (Sat.Literal.pos 53) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation2 53 (assignment s)
    (Sat.Literal.pos 562) (Sat.Literal.pos 561) (Sat.Literal.pos 53) (Sat.Literal.pos 57) (positive_of_descriptor s 562 (.lex permutation2 53) (by rfl)) (lex_2_53_prefix s) (positive_select s 53) (lex_2_53_image s)

theorem lex_2_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 561), (Sat.Literal.pos 53), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation2 53 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 561) (Sat.Literal.pos 53) (Sat.Literal.pos 57) (lex_2_53_prefix s) (positive_select s 53) (lex_2_53_image s)

theorem lex_2_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 562), (Sat.Literal.pos 561)] :=
  (lex_2_53_gate s).prop _ (List.Mem.head _)

theorem lex_2_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 562), (Sat.Literal.neg 53), (Sat.Literal.pos 57)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 562), (Sat.Literal.pos 53), (Sat.Literal.neg 57)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 561), (Sat.Literal.neg 53), (Sat.Literal.neg 57), (Sat.Literal.pos 562)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 561), (Sat.Literal.pos 53), (Sat.Literal.pos 57), (Sat.Literal.pos 562)] :=
  (lex_2_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 562) = lexBefore s permutation2 52 := by
  exact (positive_lex_of_descriptor s 562 permutation2 53 (by rfl)).trans ((lex_skipped s permutation2 52 53 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation2 52) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 64) = permuteMask permutation2 52 by rw [image2_eq]; rfl))

theorem lex_2_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 563) (Sat.Literal.pos 562) (Sat.Literal.pos 52) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation2 52 (assignment s)
    (Sat.Literal.pos 563) (Sat.Literal.pos 562) (Sat.Literal.pos 52) (Sat.Literal.pos 56) (positive_of_descriptor s 563 (.lex permutation2 52) (by rfl)) (lex_2_52_prefix s) (positive_select s 52) (lex_2_52_image s)

theorem lex_2_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 562), (Sat.Literal.pos 52), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation2 52 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 562) (Sat.Literal.pos 52) (Sat.Literal.pos 56) (lex_2_52_prefix s) (positive_select s 52) (lex_2_52_image s)

theorem lex_2_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 563), (Sat.Literal.pos 562)] :=
  (lex_2_52_gate s).prop _ (List.Mem.head _)

theorem lex_2_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 563), (Sat.Literal.neg 52), (Sat.Literal.pos 56)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 563), (Sat.Literal.pos 52), (Sat.Literal.neg 56)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 562), (Sat.Literal.neg 52), (Sat.Literal.neg 56), (Sat.Literal.pos 563)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 562), (Sat.Literal.pos 52), (Sat.Literal.pos 56), (Sat.Literal.pos 563)] :=
  (lex_2_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 563) = lexBefore s permutation2 43 := by
  exact (positive_lex_of_descriptor s 563 permutation2 52 (by rfl)).trans ((lex_skipped s permutation2 43 52 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 44 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation2 43) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 64) = permuteMask permutation2 43 by rw [image2_eq]; rfl))

theorem lex_2_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 564) (Sat.Literal.pos 563) (Sat.Literal.pos 43) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation2 43 (assignment s)
    (Sat.Literal.pos 564) (Sat.Literal.pos 563) (Sat.Literal.pos 43) (Sat.Literal.pos 39) (positive_of_descriptor s 564 (.lex permutation2 43) (by rfl)) (lex_2_43_prefix s) (positive_select s 43) (lex_2_43_image s)

theorem lex_2_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 563), (Sat.Literal.pos 43), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation2 43 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 563) (Sat.Literal.pos 43) (Sat.Literal.pos 39) (lex_2_43_prefix s) (positive_select s 43) (lex_2_43_image s)

theorem lex_2_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 564), (Sat.Literal.pos 563)] :=
  (lex_2_43_gate s).prop _ (List.Mem.head _)

theorem lex_2_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 564), (Sat.Literal.neg 43), (Sat.Literal.pos 39)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 564), (Sat.Literal.pos 43), (Sat.Literal.neg 39)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 563), (Sat.Literal.neg 43), (Sat.Literal.neg 39), (Sat.Literal.pos 564)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 563), (Sat.Literal.pos 43), (Sat.Literal.pos 39), (Sat.Literal.pos 564)] :=
  (lex_2_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 564) = lexBefore s permutation2 42 := by
  exact (positive_lex_of_descriptor s 564 permutation2 43 (by rfl)).trans ((lex_skipped s permutation2 42 43 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation2 42) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation2 42 by rw [image2_eq]; rfl))

theorem lex_2_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 565) (Sat.Literal.pos 564) (Sat.Literal.pos 42) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation2 42 (assignment s)
    (Sat.Literal.pos 565) (Sat.Literal.pos 564) (Sat.Literal.pos 42) (Sat.Literal.pos 38) (positive_of_descriptor s 565 (.lex permutation2 42) (by rfl)) (lex_2_42_prefix s) (positive_select s 42) (lex_2_42_image s)

theorem lex_2_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 564), (Sat.Literal.pos 42), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation2 42 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 564) (Sat.Literal.pos 42) (Sat.Literal.pos 38) (lex_2_42_prefix s) (positive_select s 42) (lex_2_42_image s)

theorem lex_2_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 565), (Sat.Literal.pos 564)] :=
  (lex_2_42_gate s).prop _ (List.Mem.head _)

theorem lex_2_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 565), (Sat.Literal.neg 42), (Sat.Literal.pos 38)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 565), (Sat.Literal.pos 42), (Sat.Literal.neg 38)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 564), (Sat.Literal.neg 42), (Sat.Literal.neg 38), (Sat.Literal.pos 565)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 564), (Sat.Literal.pos 42), (Sat.Literal.pos 38), (Sat.Literal.pos 565)] :=
  (lex_2_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 565) = lexBefore s permutation2 41 := by
  exact (positive_lex_of_descriptor s 565 permutation2 42 (by rfl)).trans ((lex_skipped s permutation2 41 42 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation2 41) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation2 41 by rw [image2_eq]; rfl))

theorem lex_2_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 566) (Sat.Literal.pos 565) (Sat.Literal.pos 41) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation2 41 (assignment s)
    (Sat.Literal.pos 566) (Sat.Literal.pos 565) (Sat.Literal.pos 41) (Sat.Literal.pos 37) (positive_of_descriptor s 566 (.lex permutation2 41) (by rfl)) (lex_2_41_prefix s) (positive_select s 41) (lex_2_41_image s)

theorem lex_2_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 565), (Sat.Literal.pos 41), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation2 41 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 565) (Sat.Literal.pos 41) (Sat.Literal.pos 37) (lex_2_41_prefix s) (positive_select s 41) (lex_2_41_image s)

theorem lex_2_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 566), (Sat.Literal.pos 565)] :=
  (lex_2_41_gate s).prop _ (List.Mem.head _)

theorem lex_2_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 566), (Sat.Literal.neg 41), (Sat.Literal.pos 37)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 566), (Sat.Literal.pos 41), (Sat.Literal.neg 37)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 565), (Sat.Literal.neg 41), (Sat.Literal.neg 37), (Sat.Literal.pos 566)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 565), (Sat.Literal.pos 41), (Sat.Literal.pos 37), (Sat.Literal.pos 566)] :=
  (lex_2_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 566) = lexBefore s permutation2 40 := by
  exact (positive_lex_of_descriptor s 566 permutation2 41 (by rfl)).trans ((lex_skipped s permutation2 40 41 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation2 40) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 64) = permuteMask permutation2 40 by rw [image2_eq]; rfl))

theorem lex_2_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 567) (Sat.Literal.pos 566) (Sat.Literal.pos 40) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation2 40 (assignment s)
    (Sat.Literal.pos 567) (Sat.Literal.pos 566) (Sat.Literal.pos 40) (Sat.Literal.pos 36) (positive_of_descriptor s 567 (.lex permutation2 40) (by rfl)) (lex_2_40_prefix s) (positive_select s 40) (lex_2_40_image s)

theorem lex_2_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 566), (Sat.Literal.pos 40), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation2 40 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 566) (Sat.Literal.pos 40) (Sat.Literal.pos 36) (lex_2_40_prefix s) (positive_select s 40) (lex_2_40_image s)

theorem lex_2_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 567), (Sat.Literal.pos 566)] :=
  (lex_2_40_gate s).prop _ (List.Mem.head _)

theorem lex_2_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 567), (Sat.Literal.neg 40), (Sat.Literal.pos 36)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 567), (Sat.Literal.pos 40), (Sat.Literal.neg 36)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 566), (Sat.Literal.neg 40), (Sat.Literal.neg 36), (Sat.Literal.pos 567)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 566), (Sat.Literal.pos 40), (Sat.Literal.pos 36), (Sat.Literal.pos 567)] :=
  (lex_2_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_39_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 567) = lexBefore s permutation2 39 := by
  exact (positive_lex_of_descriptor s 567 permutation2 40 (by rfl)).trans ((lex_skipped s permutation2 39 40 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_39_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation2 39) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation2 39 by rw [image2_eq]; rfl))

theorem lex_2_39_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 568) (Sat.Literal.pos 567) (Sat.Literal.pos 39) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation2 39 (assignment s)
    (Sat.Literal.pos 568) (Sat.Literal.pos 567) (Sat.Literal.pos 39) (Sat.Literal.pos 43) (positive_of_descriptor s 568 (.lex permutation2 39) (by rfl)) (lex_2_39_prefix s) (positive_select s 39) (lex_2_39_image s)

theorem lex_2_39_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 567), (Sat.Literal.pos 39), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation2 39 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 567) (Sat.Literal.pos 39) (Sat.Literal.pos 43) (lex_2_39_prefix s) (positive_select s 39) (lex_2_39_image s)

theorem lex_2_39_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 568), (Sat.Literal.pos 567)] :=
  (lex_2_39_gate s).prop _ (List.Mem.head _)

theorem lex_2_39_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 568), (Sat.Literal.neg 39), (Sat.Literal.pos 43)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_39_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 568), (Sat.Literal.pos 39), (Sat.Literal.neg 43)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_39_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 567), (Sat.Literal.neg 39), (Sat.Literal.neg 43), (Sat.Literal.pos 568)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_39_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 567), (Sat.Literal.pos 39), (Sat.Literal.pos 43), (Sat.Literal.pos 568)] :=
  (lex_2_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 568) = lexBefore s permutation2 38 := by
  exact (positive_lex_of_descriptor s 568 permutation2 39 (by rfl)).trans ((lex_skipped s permutation2 38 39 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation2 38) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation2 38 by rw [image2_eq]; rfl))

theorem lex_2_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 569) (Sat.Literal.pos 568) (Sat.Literal.pos 38) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation2 38 (assignment s)
    (Sat.Literal.pos 569) (Sat.Literal.pos 568) (Sat.Literal.pos 38) (Sat.Literal.pos 42) (positive_of_descriptor s 569 (.lex permutation2 38) (by rfl)) (lex_2_38_prefix s) (positive_select s 38) (lex_2_38_image s)

theorem lex_2_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 568), (Sat.Literal.pos 38), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation2 38 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 568) (Sat.Literal.pos 38) (Sat.Literal.pos 42) (lex_2_38_prefix s) (positive_select s 38) (lex_2_38_image s)

theorem lex_2_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 569), (Sat.Literal.pos 568)] :=
  (lex_2_38_gate s).prop _ (List.Mem.head _)

theorem lex_2_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 569), (Sat.Literal.neg 38), (Sat.Literal.pos 42)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 569), (Sat.Literal.pos 38), (Sat.Literal.neg 42)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 568), (Sat.Literal.neg 38), (Sat.Literal.neg 42), (Sat.Literal.pos 569)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 568), (Sat.Literal.pos 38), (Sat.Literal.pos 42), (Sat.Literal.pos 569)] :=
  (lex_2_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 569) = lexBefore s permutation2 37 := by
  exact (positive_lex_of_descriptor s 569 permutation2 38 (by rfl)).trans ((lex_skipped s permutation2 37 38 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation2 37) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation2 37 by rw [image2_eq]; rfl))

theorem lex_2_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 570) (Sat.Literal.pos 569) (Sat.Literal.pos 37) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation2 37 (assignment s)
    (Sat.Literal.pos 570) (Sat.Literal.pos 569) (Sat.Literal.pos 37) (Sat.Literal.pos 41) (positive_of_descriptor s 570 (.lex permutation2 37) (by rfl)) (lex_2_37_prefix s) (positive_select s 37) (lex_2_37_image s)

theorem lex_2_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 569), (Sat.Literal.pos 37), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation2 37 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 569) (Sat.Literal.pos 37) (Sat.Literal.pos 41) (lex_2_37_prefix s) (positive_select s 37) (lex_2_37_image s)

theorem lex_2_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 570), (Sat.Literal.pos 569)] :=
  (lex_2_37_gate s).prop _ (List.Mem.head _)

theorem lex_2_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 570), (Sat.Literal.neg 37), (Sat.Literal.pos 41)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 570), (Sat.Literal.pos 37), (Sat.Literal.neg 41)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 569), (Sat.Literal.neg 37), (Sat.Literal.neg 41), (Sat.Literal.pos 570)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 569), (Sat.Literal.pos 37), (Sat.Literal.pos 41), (Sat.Literal.pos 570)] :=
  (lex_2_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_36_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 570) = lexBefore s permutation2 36 := by
  exact (positive_lex_of_descriptor s 570 permutation2 37 (by rfl)).trans ((lex_skipped s permutation2 36 37 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_36_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation2 36) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation2 36 by rw [image2_eq]; rfl))

theorem lex_2_36_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 571) (Sat.Literal.pos 570) (Sat.Literal.pos 36) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation2 36 (assignment s)
    (Sat.Literal.pos 571) (Sat.Literal.pos 570) (Sat.Literal.pos 36) (Sat.Literal.pos 40) (positive_of_descriptor s 571 (.lex permutation2 36) (by rfl)) (lex_2_36_prefix s) (positive_select s 36) (lex_2_36_image s)

theorem lex_2_36_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 570), (Sat.Literal.pos 36), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation2 36 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 570) (Sat.Literal.pos 36) (Sat.Literal.pos 40) (lex_2_36_prefix s) (positive_select s 36) (lex_2_36_image s)

theorem lex_2_36_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 571), (Sat.Literal.pos 570)] :=
  (lex_2_36_gate s).prop _ (List.Mem.head _)

theorem lex_2_36_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 571), (Sat.Literal.neg 36), (Sat.Literal.pos 40)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_36_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 571), (Sat.Literal.pos 36), (Sat.Literal.neg 40)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_36_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 570), (Sat.Literal.neg 36), (Sat.Literal.neg 40), (Sat.Literal.pos 571)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_36_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 570), (Sat.Literal.pos 36), (Sat.Literal.pos 40), (Sat.Literal.pos 571)] :=
  (lex_2_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_27_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 571) = lexBefore s permutation2 27 := by
  exact (positive_lex_of_descriptor s 571 permutation2 36 (by rfl)).trans ((lex_skipped s permutation2 27 36 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 28 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_27_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation2 27) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation2 27 by rw [image2_eq]; rfl))

theorem lex_2_27_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 572) (Sat.Literal.pos 571) (Sat.Literal.pos 27) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation2 27 (assignment s)
    (Sat.Literal.pos 572) (Sat.Literal.pos 571) (Sat.Literal.pos 27) (Sat.Literal.pos 23) (positive_of_descriptor s 572 (.lex permutation2 27) (by rfl)) (lex_2_27_prefix s) (positive_select s 27) (lex_2_27_image s)

theorem lex_2_27_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 571), (Sat.Literal.pos 27), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation2 27 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 571) (Sat.Literal.pos 27) (Sat.Literal.pos 23) (lex_2_27_prefix s) (positive_select s 27) (lex_2_27_image s)

theorem lex_2_27_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 572), (Sat.Literal.pos 571)] :=
  (lex_2_27_gate s).prop _ (List.Mem.head _)

theorem lex_2_27_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 572), (Sat.Literal.neg 27), (Sat.Literal.pos 23)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_27_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 572), (Sat.Literal.pos 27), (Sat.Literal.neg 23)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_27_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 571), (Sat.Literal.neg 27), (Sat.Literal.neg 23), (Sat.Literal.pos 572)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_27_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 571), (Sat.Literal.pos 27), (Sat.Literal.pos 23), (Sat.Literal.pos 572)] :=
  (lex_2_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 572) = lexBefore s permutation2 26 := by
  exact (positive_lex_of_descriptor s 572 permutation2 27 (by rfl)).trans ((lex_skipped s permutation2 26 27 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation2 26) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation2 26 by rw [image2_eq]; rfl))

theorem lex_2_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 573) (Sat.Literal.pos 572) (Sat.Literal.pos 26) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation2 26 (assignment s)
    (Sat.Literal.pos 573) (Sat.Literal.pos 572) (Sat.Literal.pos 26) (Sat.Literal.pos 22) (positive_of_descriptor s 573 (.lex permutation2 26) (by rfl)) (lex_2_26_prefix s) (positive_select s 26) (lex_2_26_image s)

theorem lex_2_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 572), (Sat.Literal.pos 26), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation2 26 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 572) (Sat.Literal.pos 26) (Sat.Literal.pos 22) (lex_2_26_prefix s) (positive_select s 26) (lex_2_26_image s)

theorem lex_2_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 573), (Sat.Literal.pos 572)] :=
  (lex_2_26_gate s).prop _ (List.Mem.head _)

theorem lex_2_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 573), (Sat.Literal.neg 26), (Sat.Literal.pos 22)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 573), (Sat.Literal.pos 26), (Sat.Literal.neg 22)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 572), (Sat.Literal.neg 26), (Sat.Literal.neg 22), (Sat.Literal.pos 573)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 572), (Sat.Literal.pos 26), (Sat.Literal.pos 22), (Sat.Literal.pos 573)] :=
  (lex_2_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 573) = lexBefore s permutation2 25 := by
  exact (positive_lex_of_descriptor s 573 permutation2 26 (by rfl)).trans ((lex_skipped s permutation2 25 26 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation2 25) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation2 25 by rw [image2_eq]; rfl))

theorem lex_2_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 574) (Sat.Literal.pos 573) (Sat.Literal.pos 25) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation2 25 (assignment s)
    (Sat.Literal.pos 574) (Sat.Literal.pos 573) (Sat.Literal.pos 25) (Sat.Literal.pos 21) (positive_of_descriptor s 574 (.lex permutation2 25) (by rfl)) (lex_2_25_prefix s) (positive_select s 25) (lex_2_25_image s)

theorem lex_2_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 573), (Sat.Literal.pos 25), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation2 25 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 573) (Sat.Literal.pos 25) (Sat.Literal.pos 21) (lex_2_25_prefix s) (positive_select s 25) (lex_2_25_image s)

theorem lex_2_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 574), (Sat.Literal.pos 573)] :=
  (lex_2_25_gate s).prop _ (List.Mem.head _)

theorem lex_2_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 574), (Sat.Literal.neg 25), (Sat.Literal.pos 21)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 574), (Sat.Literal.pos 25), (Sat.Literal.neg 21)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 573), (Sat.Literal.neg 25), (Sat.Literal.neg 21), (Sat.Literal.pos 574)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 573), (Sat.Literal.pos 25), (Sat.Literal.pos 21), (Sat.Literal.pos 574)] :=
  (lex_2_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_24_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 574) = lexBefore s permutation2 24 := by
  exact (positive_lex_of_descriptor s 574 permutation2 25 (by rfl)).trans ((lex_skipped s permutation2 24 25 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_24_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation2 24) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation2 24 by rw [image2_eq]; rfl))

theorem lex_2_24_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 575) (Sat.Literal.pos 574) (Sat.Literal.pos 24) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation2 24 (assignment s)
    (Sat.Literal.pos 575) (Sat.Literal.pos 574) (Sat.Literal.pos 24) (Sat.Literal.pos 20) (positive_of_descriptor s 575 (.lex permutation2 24) (by rfl)) (lex_2_24_prefix s) (positive_select s 24) (lex_2_24_image s)

theorem lex_2_24_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 574), (Sat.Literal.pos 24), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation2 24 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 574) (Sat.Literal.pos 24) (Sat.Literal.pos 20) (lex_2_24_prefix s) (positive_select s 24) (lex_2_24_image s)

theorem lex_2_24_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 575), (Sat.Literal.pos 574)] :=
  (lex_2_24_gate s).prop _ (List.Mem.head _)

theorem lex_2_24_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 575), (Sat.Literal.neg 24), (Sat.Literal.pos 20)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_24_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 575), (Sat.Literal.pos 24), (Sat.Literal.neg 20)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_24_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 574), (Sat.Literal.neg 24), (Sat.Literal.neg 20), (Sat.Literal.pos 575)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_24_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 574), (Sat.Literal.pos 24), (Sat.Literal.pos 20), (Sat.Literal.pos 575)] :=
  (lex_2_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 575) = lexBefore s permutation2 23 := by
  exact (positive_lex_of_descriptor s 575 permutation2 24 (by rfl)).trans ((lex_skipped s permutation2 23 24 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation2 23) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 64) = permuteMask permutation2 23 by rw [image2_eq]; rfl))

theorem lex_2_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 576) (Sat.Literal.pos 575) (Sat.Literal.pos 23) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation2 23 (assignment s)
    (Sat.Literal.pos 576) (Sat.Literal.pos 575) (Sat.Literal.pos 23) (Sat.Literal.pos 27) (positive_of_descriptor s 576 (.lex permutation2 23) (by rfl)) (lex_2_23_prefix s) (positive_select s 23) (lex_2_23_image s)

theorem lex_2_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 575), (Sat.Literal.pos 23), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation2 23 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 575) (Sat.Literal.pos 23) (Sat.Literal.pos 27) (lex_2_23_prefix s) (positive_select s 23) (lex_2_23_image s)

theorem lex_2_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 576), (Sat.Literal.pos 575)] :=
  (lex_2_23_gate s).prop _ (List.Mem.head _)

theorem lex_2_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 576), (Sat.Literal.neg 23), (Sat.Literal.pos 27)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 576), (Sat.Literal.pos 23), (Sat.Literal.neg 27)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 575), (Sat.Literal.neg 23), (Sat.Literal.neg 27), (Sat.Literal.pos 576)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 575), (Sat.Literal.pos 23), (Sat.Literal.pos 27), (Sat.Literal.pos 576)] :=
  (lex_2_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 576) = lexBefore s permutation2 22 := by
  exact (positive_lex_of_descriptor s 576 permutation2 23 (by rfl)).trans ((lex_skipped s permutation2 22 23 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation2 22) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation2 22 by rw [image2_eq]; rfl))

theorem lex_2_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 577) (Sat.Literal.pos 576) (Sat.Literal.pos 22) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation2 22 (assignment s)
    (Sat.Literal.pos 577) (Sat.Literal.pos 576) (Sat.Literal.pos 22) (Sat.Literal.pos 26) (positive_of_descriptor s 577 (.lex permutation2 22) (by rfl)) (lex_2_22_prefix s) (positive_select s 22) (lex_2_22_image s)

theorem lex_2_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 576), (Sat.Literal.pos 22), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation2 22 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 576) (Sat.Literal.pos 22) (Sat.Literal.pos 26) (lex_2_22_prefix s) (positive_select s 22) (lex_2_22_image s)

theorem lex_2_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 577), (Sat.Literal.pos 576)] :=
  (lex_2_22_gate s).prop _ (List.Mem.head _)

theorem lex_2_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 577), (Sat.Literal.neg 22), (Sat.Literal.pos 26)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 577), (Sat.Literal.pos 22), (Sat.Literal.neg 26)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 576), (Sat.Literal.neg 22), (Sat.Literal.neg 26), (Sat.Literal.pos 577)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 576), (Sat.Literal.pos 22), (Sat.Literal.pos 26), (Sat.Literal.pos 577)] :=
  (lex_2_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 577) = lexBefore s permutation2 21 := by
  exact (positive_lex_of_descriptor s 577 permutation2 22 (by rfl)).trans ((lex_skipped s permutation2 21 22 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation2 21) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation2 21 by rw [image2_eq]; rfl))

theorem lex_2_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 578) (Sat.Literal.pos 577) (Sat.Literal.pos 21) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation2 21 (assignment s)
    (Sat.Literal.pos 578) (Sat.Literal.pos 577) (Sat.Literal.pos 21) (Sat.Literal.pos 25) (positive_of_descriptor s 578 (.lex permutation2 21) (by rfl)) (lex_2_21_prefix s) (positive_select s 21) (lex_2_21_image s)

theorem lex_2_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 577), (Sat.Literal.pos 21), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation2 21 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 577) (Sat.Literal.pos 21) (Sat.Literal.pos 25) (lex_2_21_prefix s) (positive_select s 21) (lex_2_21_image s)

theorem lex_2_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 578), (Sat.Literal.pos 577)] :=
  (lex_2_21_gate s).prop _ (List.Mem.head _)

theorem lex_2_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 578), (Sat.Literal.neg 21), (Sat.Literal.pos 25)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 578), (Sat.Literal.pos 21), (Sat.Literal.neg 25)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 577), (Sat.Literal.neg 21), (Sat.Literal.neg 25), (Sat.Literal.pos 578)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 577), (Sat.Literal.pos 21), (Sat.Literal.pos 25), (Sat.Literal.pos 578)] :=
  (lex_2_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 578) = lexBefore s permutation2 20 := by
  exact (positive_lex_of_descriptor s 578 permutation2 21 (by rfl)).trans ((lex_skipped s permutation2 20 21 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation2 20) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 64) = permuteMask permutation2 20 by rw [image2_eq]; rfl))

theorem lex_2_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 579) (Sat.Literal.pos 578) (Sat.Literal.pos 20) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation2 20 (assignment s)
    (Sat.Literal.pos 579) (Sat.Literal.pos 578) (Sat.Literal.pos 20) (Sat.Literal.pos 24) (positive_of_descriptor s 579 (.lex permutation2 20) (by rfl)) (lex_2_20_prefix s) (positive_select s 20) (lex_2_20_image s)

theorem lex_2_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 578), (Sat.Literal.pos 20), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation2 20 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 578) (Sat.Literal.pos 20) (Sat.Literal.pos 24) (lex_2_20_prefix s) (positive_select s 20) (lex_2_20_image s)

theorem lex_2_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 579), (Sat.Literal.pos 578)] :=
  (lex_2_20_gate s).prop _ (List.Mem.head _)

theorem lex_2_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 579), (Sat.Literal.neg 20), (Sat.Literal.pos 24)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 579), (Sat.Literal.pos 20), (Sat.Literal.neg 24)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 578), (Sat.Literal.neg 20), (Sat.Literal.neg 24), (Sat.Literal.pos 579)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 578), (Sat.Literal.pos 20), (Sat.Literal.pos 24), (Sat.Literal.pos 579)] :=
  (lex_2_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 579) = lexBefore s permutation2 11 := by
  exact (positive_lex_of_descriptor s 579 permutation2 20 (by rfl)).trans ((lex_skipped s permutation2 11 20 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 12 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation2 11) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 64) = permuteMask permutation2 11 by rw [image2_eq]; rfl))

theorem lex_2_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 580) (Sat.Literal.pos 579) (Sat.Literal.pos 11) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation2 11 (assignment s)
    (Sat.Literal.pos 580) (Sat.Literal.pos 579) (Sat.Literal.pos 11) (Sat.Literal.pos 7) (positive_of_descriptor s 580 (.lex permutation2 11) (by rfl)) (lex_2_11_prefix s) (positive_select s 11) (lex_2_11_image s)

theorem lex_2_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 579), (Sat.Literal.pos 11), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation2 11 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 579) (Sat.Literal.pos 11) (Sat.Literal.pos 7) (lex_2_11_prefix s) (positive_select s 11) (lex_2_11_image s)

theorem lex_2_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 580), (Sat.Literal.pos 579)] :=
  (lex_2_11_gate s).prop _ (List.Mem.head _)

theorem lex_2_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 580), (Sat.Literal.neg 11), (Sat.Literal.pos 7)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 580), (Sat.Literal.pos 11), (Sat.Literal.neg 7)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 579), (Sat.Literal.neg 11), (Sat.Literal.neg 7), (Sat.Literal.pos 580)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 579), (Sat.Literal.pos 11), (Sat.Literal.pos 7), (Sat.Literal.pos 580)] :=
  (lex_2_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 580) = lexBefore s permutation2 10 := by
  exact (positive_lex_of_descriptor s 580 permutation2 11 (by rfl)).trans ((lex_skipped s permutation2 10 11 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation2 10) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 64) = permuteMask permutation2 10 by rw [image2_eq]; rfl))

theorem lex_2_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 581) (Sat.Literal.pos 580) (Sat.Literal.pos 10) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation2 10 (assignment s)
    (Sat.Literal.pos 581) (Sat.Literal.pos 580) (Sat.Literal.pos 10) (Sat.Literal.pos 6) (positive_of_descriptor s 581 (.lex permutation2 10) (by rfl)) (lex_2_10_prefix s) (positive_select s 10) (lex_2_10_image s)

theorem lex_2_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 580), (Sat.Literal.pos 10), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation2 10 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 580) (Sat.Literal.pos 10) (Sat.Literal.pos 6) (lex_2_10_prefix s) (positive_select s 10) (lex_2_10_image s)

theorem lex_2_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 581), (Sat.Literal.pos 580)] :=
  (lex_2_10_gate s).prop _ (List.Mem.head _)

theorem lex_2_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 581), (Sat.Literal.neg 10), (Sat.Literal.pos 6)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 581), (Sat.Literal.pos 10), (Sat.Literal.neg 6)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 580), (Sat.Literal.neg 10), (Sat.Literal.neg 6), (Sat.Literal.pos 581)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 580), (Sat.Literal.pos 10), (Sat.Literal.pos 6), (Sat.Literal.pos 581)] :=
  (lex_2_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_9_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 581) = lexBefore s permutation2 9 := by
  exact (positive_lex_of_descriptor s 581 permutation2 10 (by rfl)).trans ((lex_skipped s permutation2 9 10 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_9_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation2 9) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation2 9 by rw [image2_eq]; rfl))

theorem lex_2_9_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 582) (Sat.Literal.pos 581) (Sat.Literal.pos 9) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation2 9 (assignment s)
    (Sat.Literal.pos 582) (Sat.Literal.pos 581) (Sat.Literal.pos 9) (Sat.Literal.pos 5) (positive_of_descriptor s 582 (.lex permutation2 9) (by rfl)) (lex_2_9_prefix s) (positive_select s 9) (lex_2_9_image s)

theorem lex_2_9_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 581), (Sat.Literal.pos 9), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation2 9 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 581) (Sat.Literal.pos 9) (Sat.Literal.pos 5) (lex_2_9_prefix s) (positive_select s 9) (lex_2_9_image s)

theorem lex_2_9_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 582), (Sat.Literal.pos 581)] :=
  (lex_2_9_gate s).prop _ (List.Mem.head _)

theorem lex_2_9_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 582), (Sat.Literal.neg 9), (Sat.Literal.pos 5)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_9_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 582), (Sat.Literal.pos 9), (Sat.Literal.neg 5)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_9_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 581), (Sat.Literal.neg 9), (Sat.Literal.neg 5), (Sat.Literal.pos 582)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_9_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 581), (Sat.Literal.pos 9), (Sat.Literal.pos 5), (Sat.Literal.pos 582)] :=
  (lex_2_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_8_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 582) = lexBefore s permutation2 8 := by
  exact (positive_lex_of_descriptor s 582 permutation2 9 (by rfl)).trans ((lex_skipped s permutation2 8 9 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_8_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation2 8) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 64) = permuteMask permutation2 8 by rw [image2_eq]; rfl))

theorem lex_2_8_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 583) (Sat.Literal.pos 582) (Sat.Literal.pos 8) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation2 8 (assignment s)
    (Sat.Literal.pos 583) (Sat.Literal.pos 582) (Sat.Literal.pos 8) (Sat.Literal.pos 4) (positive_of_descriptor s 583 (.lex permutation2 8) (by rfl)) (lex_2_8_prefix s) (positive_select s 8) (lex_2_8_image s)

theorem lex_2_8_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 582), (Sat.Literal.pos 8), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation2 8 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 582) (Sat.Literal.pos 8) (Sat.Literal.pos 4) (lex_2_8_prefix s) (positive_select s 8) (lex_2_8_image s)

theorem lex_2_8_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 583), (Sat.Literal.pos 582)] :=
  (lex_2_8_gate s).prop _ (List.Mem.head _)

theorem lex_2_8_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 583), (Sat.Literal.neg 8), (Sat.Literal.pos 4)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_8_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 583), (Sat.Literal.pos 8), (Sat.Literal.neg 4)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_8_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 582), (Sat.Literal.neg 8), (Sat.Literal.neg 4), (Sat.Literal.pos 583)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_8_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 582), (Sat.Literal.pos 8), (Sat.Literal.pos 4), (Sat.Literal.pos 583)] :=
  (lex_2_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_7_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 583) = lexBefore s permutation2 7 := by
  exact (positive_lex_of_descriptor s 583 permutation2 8 (by rfl)).trans ((lex_skipped s permutation2 7 8 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_7_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation2 7) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation2 7 by rw [image2_eq]; rfl))

theorem lex_2_7_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 584) (Sat.Literal.pos 583) (Sat.Literal.pos 7) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation2 7 (assignment s)
    (Sat.Literal.pos 584) (Sat.Literal.pos 583) (Sat.Literal.pos 7) (Sat.Literal.pos 11) (positive_of_descriptor s 584 (.lex permutation2 7) (by rfl)) (lex_2_7_prefix s) (positive_select s 7) (lex_2_7_image s)

theorem lex_2_7_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 583), (Sat.Literal.pos 7), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation2 7 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 583) (Sat.Literal.pos 7) (Sat.Literal.pos 11) (lex_2_7_prefix s) (positive_select s 7) (lex_2_7_image s)

theorem lex_2_7_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 584), (Sat.Literal.pos 583)] :=
  (lex_2_7_gate s).prop _ (List.Mem.head _)

theorem lex_2_7_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 584), (Sat.Literal.neg 7), (Sat.Literal.pos 11)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_7_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 584), (Sat.Literal.pos 7), (Sat.Literal.neg 11)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_7_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 583), (Sat.Literal.neg 7), (Sat.Literal.neg 11), (Sat.Literal.pos 584)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_7_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 583), (Sat.Literal.pos 7), (Sat.Literal.pos 11), (Sat.Literal.pos 584)] :=
  (lex_2_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_6_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 584) = lexBefore s permutation2 6 := by
  exact (positive_lex_of_descriptor s 584 permutation2 7 (by rfl)).trans ((lex_skipped s permutation2 6 7 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_6_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation2 6) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation2 6 by rw [image2_eq]; rfl))

theorem lex_2_6_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 585) (Sat.Literal.pos 584) (Sat.Literal.pos 6) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation2 6 (assignment s)
    (Sat.Literal.pos 585) (Sat.Literal.pos 584) (Sat.Literal.pos 6) (Sat.Literal.pos 10) (positive_of_descriptor s 585 (.lex permutation2 6) (by rfl)) (lex_2_6_prefix s) (positive_select s 6) (lex_2_6_image s)

theorem lex_2_6_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 584), (Sat.Literal.pos 6), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation2 6 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 584) (Sat.Literal.pos 6) (Sat.Literal.pos 10) (lex_2_6_prefix s) (positive_select s 6) (lex_2_6_image s)

theorem lex_2_6_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 585), (Sat.Literal.pos 584)] :=
  (lex_2_6_gate s).prop _ (List.Mem.head _)

theorem lex_2_6_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 585), (Sat.Literal.neg 6), (Sat.Literal.pos 10)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_6_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 585), (Sat.Literal.pos 6), (Sat.Literal.neg 10)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_6_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 584), (Sat.Literal.neg 6), (Sat.Literal.neg 10), (Sat.Literal.pos 585)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_6_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 584), (Sat.Literal.pos 6), (Sat.Literal.pos 10), (Sat.Literal.pos 585)] :=
  (lex_2_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_5_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 585) = lexBefore s permutation2 5 := by
  exact (positive_lex_of_descriptor s 585 permutation2 6 (by rfl)).trans ((lex_skipped s permutation2 5 6 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_5_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation2 5) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 64) = permuteMask permutation2 5 by rw [image2_eq]; rfl))

theorem lex_2_5_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 586) (Sat.Literal.pos 585) (Sat.Literal.pos 5) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation2 5 (assignment s)
    (Sat.Literal.pos 586) (Sat.Literal.pos 585) (Sat.Literal.pos 5) (Sat.Literal.pos 9) (positive_of_descriptor s 586 (.lex permutation2 5) (by rfl)) (lex_2_5_prefix s) (positive_select s 5) (lex_2_5_image s)

theorem lex_2_5_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 585), (Sat.Literal.pos 5), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation2 5 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 585) (Sat.Literal.pos 5) (Sat.Literal.pos 9) (lex_2_5_prefix s) (positive_select s 5) (lex_2_5_image s)

theorem lex_2_5_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 586), (Sat.Literal.pos 585)] :=
  (lex_2_5_gate s).prop _ (List.Mem.head _)

theorem lex_2_5_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 586), (Sat.Literal.neg 5), (Sat.Literal.pos 9)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_5_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 586), (Sat.Literal.pos 5), (Sat.Literal.neg 9)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_5_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 585), (Sat.Literal.neg 5), (Sat.Literal.neg 9), (Sat.Literal.pos 586)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_5_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 585), (Sat.Literal.pos 5), (Sat.Literal.pos 9), (Sat.Literal.pos 586)] :=
  (lex_2_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_2_4_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 586) = lexBefore s permutation2 4 := by
  exact (positive_lex_of_descriptor s 586 permutation2 5 (by rfl)).trans ((lex_skipped s permutation2 4 5 (by decide) (by intro j hj hp; rw [image2_eq]; exact fixedOnRange_spec image2 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_2_4_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation2 4) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 64) = permuteMask permutation2 4 by rw [image2_eq]; rfl))

theorem lex_2_4_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 587) (Sat.Literal.pos 586) (Sat.Literal.pos 4) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation2 4 (assignment s)
    (Sat.Literal.pos 587) (Sat.Literal.pos 586) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (positive_of_descriptor s 587 (.lex permutation2 4) (by rfl)) (lex_2_4_prefix s) (positive_select s 4) (lex_2_4_image s)

theorem lex_2_4_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 586), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation2 4 (hmax permutation2) (assignment s)
    (Sat.Literal.pos 586) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (lex_2_4_prefix s) (positive_select s 4) (lex_2_4_image s)

theorem lex_2_4_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 587), (Sat.Literal.pos 586)] :=
  (lex_2_4_gate s).prop _ (List.Mem.head _)

theorem lex_2_4_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 587), (Sat.Literal.neg 4), (Sat.Literal.pos 8)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_2_4_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 587), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_2_4_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 586), (Sat.Literal.neg 4), (Sat.Literal.neg 8), (Sat.Literal.pos 587)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_2_4_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 586), (Sat.Literal.pos 4), (Sat.Literal.pos 8), (Sat.Literal.pos 587)] :=
  (lex_2_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_55_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation3 55 := by
  exact (negative_falsum s).trans ((lex_first s permutation3 55 (by intro j hj; rw [image3_eq]; exact fixedOnRange_spec image3 56 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_3_55_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation3 55) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 64) = permuteMask permutation3 55 by rw [image3_eq]; rfl))

theorem lex_3_55_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 588) (Sat.Literal.neg 64) (Sat.Literal.pos 55) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation3 55 (assignment s)
    (Sat.Literal.pos 588) (Sat.Literal.neg 64) (Sat.Literal.pos 55) (Sat.Literal.pos 47) (positive_of_descriptor s 588 (.lex permutation3 55) (by rfl)) (lex_3_55_prefix s) (positive_select s 55) (lex_3_55_image s)

theorem lex_3_55_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 55), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation3 55 (hmax permutation3) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 55) (Sat.Literal.pos 47) (lex_3_55_prefix s) (positive_select s 55) (lex_3_55_image s)

theorem lex_3_55_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 588), (Sat.Literal.neg 64)] :=
  (lex_3_55_gate s).prop _ (List.Mem.head _)

theorem lex_3_55_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 588), (Sat.Literal.neg 55), (Sat.Literal.pos 47)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_55_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 588), (Sat.Literal.pos 55), (Sat.Literal.neg 47)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_55_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 55), (Sat.Literal.neg 47), (Sat.Literal.pos 588)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_55_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 55), (Sat.Literal.pos 47), (Sat.Literal.pos 588)] :=
  (lex_3_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_54_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 588) = lexBefore s permutation3 54 := by
  exact (positive_lex_of_descriptor s 588 permutation3 55 (by rfl)).trans ((lex_skipped s permutation3 54 55 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_54_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation3 54) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation3 54 by rw [image3_eq]; rfl))

theorem lex_3_54_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 589) (Sat.Literal.pos 588) (Sat.Literal.pos 54) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation3 54 (assignment s)
    (Sat.Literal.pos 589) (Sat.Literal.pos 588) (Sat.Literal.pos 54) (Sat.Literal.pos 46) (positive_of_descriptor s 589 (.lex permutation3 54) (by rfl)) (lex_3_54_prefix s) (positive_select s 54) (lex_3_54_image s)

theorem lex_3_54_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 588), (Sat.Literal.pos 54), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation3 54 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 588) (Sat.Literal.pos 54) (Sat.Literal.pos 46) (lex_3_54_prefix s) (positive_select s 54) (lex_3_54_image s)

theorem lex_3_54_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 589), (Sat.Literal.pos 588)] :=
  (lex_3_54_gate s).prop _ (List.Mem.head _)

theorem lex_3_54_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 589), (Sat.Literal.neg 54), (Sat.Literal.pos 46)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_54_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 589), (Sat.Literal.pos 54), (Sat.Literal.neg 46)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_54_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 588), (Sat.Literal.neg 54), (Sat.Literal.neg 46), (Sat.Literal.pos 589)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_54_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 588), (Sat.Literal.pos 54), (Sat.Literal.pos 46), (Sat.Literal.pos 589)] :=
  (lex_3_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 589) = lexBefore s permutation3 53 := by
  exact (positive_lex_of_descriptor s 589 permutation3 54 (by rfl)).trans ((lex_skipped s permutation3 53 54 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation3 53) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation3 53 by rw [image3_eq]; rfl))

theorem lex_3_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 590) (Sat.Literal.pos 589) (Sat.Literal.pos 53) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation3 53 (assignment s)
    (Sat.Literal.pos 590) (Sat.Literal.pos 589) (Sat.Literal.pos 53) (Sat.Literal.pos 45) (positive_of_descriptor s 590 (.lex permutation3 53) (by rfl)) (lex_3_53_prefix s) (positive_select s 53) (lex_3_53_image s)

theorem lex_3_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 589), (Sat.Literal.pos 53), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation3 53 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 589) (Sat.Literal.pos 53) (Sat.Literal.pos 45) (lex_3_53_prefix s) (positive_select s 53) (lex_3_53_image s)

theorem lex_3_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 590), (Sat.Literal.pos 589)] :=
  (lex_3_53_gate s).prop _ (List.Mem.head _)

theorem lex_3_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 590), (Sat.Literal.neg 53), (Sat.Literal.pos 45)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 590), (Sat.Literal.pos 53), (Sat.Literal.neg 45)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 589), (Sat.Literal.neg 53), (Sat.Literal.neg 45), (Sat.Literal.pos 590)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 589), (Sat.Literal.pos 53), (Sat.Literal.pos 45), (Sat.Literal.pos 590)] :=
  (lex_3_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 590) = lexBefore s permutation3 52 := by
  exact (positive_lex_of_descriptor s 590 permutation3 53 (by rfl)).trans ((lex_skipped s permutation3 52 53 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation3 52) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation3 52 by rw [image3_eq]; rfl))

theorem lex_3_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 591) (Sat.Literal.pos 590) (Sat.Literal.pos 52) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation3 52 (assignment s)
    (Sat.Literal.pos 591) (Sat.Literal.pos 590) (Sat.Literal.pos 52) (Sat.Literal.pos 44) (positive_of_descriptor s 591 (.lex permutation3 52) (by rfl)) (lex_3_52_prefix s) (positive_select s 52) (lex_3_52_image s)

theorem lex_3_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 590), (Sat.Literal.pos 52), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation3 52 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 590) (Sat.Literal.pos 52) (Sat.Literal.pos 44) (lex_3_52_prefix s) (positive_select s 52) (lex_3_52_image s)

theorem lex_3_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 591), (Sat.Literal.pos 590)] :=
  (lex_3_52_gate s).prop _ (List.Mem.head _)

theorem lex_3_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 591), (Sat.Literal.neg 52), (Sat.Literal.pos 44)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 591), (Sat.Literal.pos 52), (Sat.Literal.neg 44)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 590), (Sat.Literal.neg 52), (Sat.Literal.neg 44), (Sat.Literal.pos 591)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 590), (Sat.Literal.pos 52), (Sat.Literal.pos 44), (Sat.Literal.pos 591)] :=
  (lex_3_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_0_62_gate

end Crown.CertificateSixData
