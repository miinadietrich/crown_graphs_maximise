import Crown.CertificateSixLexLookup
import Crown.CertificateSixRanges

namespace Crown.CertificateSixData
open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation Crown.CertificateAssembly Crown.CertificateSixAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_3_51_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 591) = lexBefore s permutation3 51 := by
  exact (positive_lex_of_descriptor s 591 permutation3 52 (by rfl)).trans ((lex_skipped s permutation3 51 52 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_51_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation3 51) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation3 51 by rw [image3_eq]; rfl))

theorem lex_3_51_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 592) (Sat.Literal.pos 591) (Sat.Literal.pos 51) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation3 51 (assignment s)
    (Sat.Literal.pos 592) (Sat.Literal.pos 591) (Sat.Literal.pos 51) (Sat.Literal.pos 43) (positive_of_descriptor s 592 (.lex permutation3 51) (by rfl)) (lex_3_51_prefix s) (positive_select s 51) (lex_3_51_image s)

theorem lex_3_51_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 591), (Sat.Literal.pos 51), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation3 51 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 591) (Sat.Literal.pos 51) (Sat.Literal.pos 43) (lex_3_51_prefix s) (positive_select s 51) (lex_3_51_image s)

theorem lex_3_51_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 592), (Sat.Literal.pos 591)] :=
  (lex_3_51_gate s).prop _ (List.Mem.head _)

theorem lex_3_51_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 592), (Sat.Literal.neg 51), (Sat.Literal.pos 43)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_51_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 592), (Sat.Literal.pos 51), (Sat.Literal.neg 43)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_51_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 591), (Sat.Literal.neg 51), (Sat.Literal.neg 43), (Sat.Literal.pos 592)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_51_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 591), (Sat.Literal.pos 51), (Sat.Literal.pos 43), (Sat.Literal.pos 592)] :=
  (lex_3_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 592) = lexBefore s permutation3 50 := by
  exact (positive_lex_of_descriptor s 592 permutation3 51 (by rfl)).trans ((lex_skipped s permutation3 50 51 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation3 50) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation3 50 by rw [image3_eq]; rfl))

theorem lex_3_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 593) (Sat.Literal.pos 592) (Sat.Literal.pos 50) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation3 50 (assignment s)
    (Sat.Literal.pos 593) (Sat.Literal.pos 592) (Sat.Literal.pos 50) (Sat.Literal.pos 42) (positive_of_descriptor s 593 (.lex permutation3 50) (by rfl)) (lex_3_50_prefix s) (positive_select s 50) (lex_3_50_image s)

theorem lex_3_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 592), (Sat.Literal.pos 50), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation3 50 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 592) (Sat.Literal.pos 50) (Sat.Literal.pos 42) (lex_3_50_prefix s) (positive_select s 50) (lex_3_50_image s)

theorem lex_3_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 593), (Sat.Literal.pos 592)] :=
  (lex_3_50_gate s).prop _ (List.Mem.head _)

theorem lex_3_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 593), (Sat.Literal.neg 50), (Sat.Literal.pos 42)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 593), (Sat.Literal.pos 50), (Sat.Literal.neg 42)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 592), (Sat.Literal.neg 50), (Sat.Literal.neg 42), (Sat.Literal.pos 593)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 592), (Sat.Literal.pos 50), (Sat.Literal.pos 42), (Sat.Literal.pos 593)] :=
  (lex_3_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_49_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 593) = lexBefore s permutation3 49 := by
  exact (positive_lex_of_descriptor s 593 permutation3 50 (by rfl)).trans ((lex_skipped s permutation3 49 50 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_49_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation3 49) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation3 49 by rw [image3_eq]; rfl))

theorem lex_3_49_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 594) (Sat.Literal.pos 593) (Sat.Literal.pos 49) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation3 49 (assignment s)
    (Sat.Literal.pos 594) (Sat.Literal.pos 593) (Sat.Literal.pos 49) (Sat.Literal.pos 41) (positive_of_descriptor s 594 (.lex permutation3 49) (by rfl)) (lex_3_49_prefix s) (positive_select s 49) (lex_3_49_image s)

theorem lex_3_49_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 593), (Sat.Literal.pos 49), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation3 49 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 593) (Sat.Literal.pos 49) (Sat.Literal.pos 41) (lex_3_49_prefix s) (positive_select s 49) (lex_3_49_image s)

theorem lex_3_49_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 594), (Sat.Literal.pos 593)] :=
  (lex_3_49_gate s).prop _ (List.Mem.head _)

theorem lex_3_49_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 594), (Sat.Literal.neg 49), (Sat.Literal.pos 41)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_49_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 594), (Sat.Literal.pos 49), (Sat.Literal.neg 41)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_49_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 593), (Sat.Literal.neg 49), (Sat.Literal.neg 41), (Sat.Literal.pos 594)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_49_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 593), (Sat.Literal.pos 49), (Sat.Literal.pos 41), (Sat.Literal.pos 594)] :=
  (lex_3_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_48_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 594) = lexBefore s permutation3 48 := by
  exact (positive_lex_of_descriptor s 594 permutation3 49 (by rfl)).trans ((lex_skipped s permutation3 48 49 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_48_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation3 48) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation3 48 by rw [image3_eq]; rfl))

theorem lex_3_48_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 595) (Sat.Literal.pos 594) (Sat.Literal.pos 48) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation3 48 (assignment s)
    (Sat.Literal.pos 595) (Sat.Literal.pos 594) (Sat.Literal.pos 48) (Sat.Literal.pos 40) (positive_of_descriptor s 595 (.lex permutation3 48) (by rfl)) (lex_3_48_prefix s) (positive_select s 48) (lex_3_48_image s)

theorem lex_3_48_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 594), (Sat.Literal.pos 48), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation3 48 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 594) (Sat.Literal.pos 48) (Sat.Literal.pos 40) (lex_3_48_prefix s) (positive_select s 48) (lex_3_48_image s)

theorem lex_3_48_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 595), (Sat.Literal.pos 594)] :=
  (lex_3_48_gate s).prop _ (List.Mem.head _)

theorem lex_3_48_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 595), (Sat.Literal.neg 48), (Sat.Literal.pos 40)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_48_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 595), (Sat.Literal.pos 48), (Sat.Literal.neg 40)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_48_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 594), (Sat.Literal.neg 48), (Sat.Literal.neg 40), (Sat.Literal.pos 595)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_48_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 594), (Sat.Literal.pos 48), (Sat.Literal.pos 40), (Sat.Literal.pos 595)] :=
  (lex_3_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_47_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 595) = lexBefore s permutation3 47 := by
  exact (positive_lex_of_descriptor s 595 permutation3 48 (by rfl)).trans ((lex_skipped s permutation3 47 48 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_47_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation3 47) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 64) = permuteMask permutation3 47 by rw [image3_eq]; rfl))

theorem lex_3_47_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 596) (Sat.Literal.pos 595) (Sat.Literal.pos 47) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation3 47 (assignment s)
    (Sat.Literal.pos 596) (Sat.Literal.pos 595) (Sat.Literal.pos 47) (Sat.Literal.pos 55) (positive_of_descriptor s 596 (.lex permutation3 47) (by rfl)) (lex_3_47_prefix s) (positive_select s 47) (lex_3_47_image s)

theorem lex_3_47_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 595), (Sat.Literal.pos 47), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation3 47 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 595) (Sat.Literal.pos 47) (Sat.Literal.pos 55) (lex_3_47_prefix s) (positive_select s 47) (lex_3_47_image s)

theorem lex_3_47_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 596), (Sat.Literal.pos 595)] :=
  (lex_3_47_gate s).prop _ (List.Mem.head _)

theorem lex_3_47_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 596), (Sat.Literal.neg 47), (Sat.Literal.pos 55)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_47_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 596), (Sat.Literal.pos 47), (Sat.Literal.neg 55)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_47_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 595), (Sat.Literal.neg 47), (Sat.Literal.neg 55), (Sat.Literal.pos 596)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_47_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 595), (Sat.Literal.pos 47), (Sat.Literal.pos 55), (Sat.Literal.pos 596)] :=
  (lex_3_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 596) = lexBefore s permutation3 46 := by
  exact (positive_lex_of_descriptor s 596 permutation3 47 (by rfl)).trans ((lex_skipped s permutation3 46 47 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation3 46) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 64) = permuteMask permutation3 46 by rw [image3_eq]; rfl))

theorem lex_3_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 597) (Sat.Literal.pos 596) (Sat.Literal.pos 46) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation3 46 (assignment s)
    (Sat.Literal.pos 597) (Sat.Literal.pos 596) (Sat.Literal.pos 46) (Sat.Literal.pos 54) (positive_of_descriptor s 597 (.lex permutation3 46) (by rfl)) (lex_3_46_prefix s) (positive_select s 46) (lex_3_46_image s)

theorem lex_3_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 596), (Sat.Literal.pos 46), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation3 46 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 596) (Sat.Literal.pos 46) (Sat.Literal.pos 54) (lex_3_46_prefix s) (positive_select s 46) (lex_3_46_image s)

theorem lex_3_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 597), (Sat.Literal.pos 596)] :=
  (lex_3_46_gate s).prop _ (List.Mem.head _)

theorem lex_3_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 597), (Sat.Literal.neg 46), (Sat.Literal.pos 54)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 597), (Sat.Literal.pos 46), (Sat.Literal.neg 54)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 596), (Sat.Literal.neg 46), (Sat.Literal.neg 54), (Sat.Literal.pos 597)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 596), (Sat.Literal.pos 46), (Sat.Literal.pos 54), (Sat.Literal.pos 597)] :=
  (lex_3_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 597) = lexBefore s permutation3 45 := by
  exact (positive_lex_of_descriptor s 597 permutation3 46 (by rfl)).trans ((lex_skipped s permutation3 45 46 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation3 45) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation3 45 by rw [image3_eq]; rfl))

theorem lex_3_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 598) (Sat.Literal.pos 597) (Sat.Literal.pos 45) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation3 45 (assignment s)
    (Sat.Literal.pos 598) (Sat.Literal.pos 597) (Sat.Literal.pos 45) (Sat.Literal.pos 53) (positive_of_descriptor s 598 (.lex permutation3 45) (by rfl)) (lex_3_45_prefix s) (positive_select s 45) (lex_3_45_image s)

theorem lex_3_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 597), (Sat.Literal.pos 45), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation3 45 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 597) (Sat.Literal.pos 45) (Sat.Literal.pos 53) (lex_3_45_prefix s) (positive_select s 45) (lex_3_45_image s)

theorem lex_3_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 598), (Sat.Literal.pos 597)] :=
  (lex_3_45_gate s).prop _ (List.Mem.head _)

theorem lex_3_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 598), (Sat.Literal.neg 45), (Sat.Literal.pos 53)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 598), (Sat.Literal.pos 45), (Sat.Literal.neg 53)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 597), (Sat.Literal.neg 45), (Sat.Literal.neg 53), (Sat.Literal.pos 598)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 597), (Sat.Literal.pos 45), (Sat.Literal.pos 53), (Sat.Literal.pos 598)] :=
  (lex_3_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 598) = lexBefore s permutation3 44 := by
  exact (positive_lex_of_descriptor s 598 permutation3 45 (by rfl)).trans ((lex_skipped s permutation3 44 45 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation3 44) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation3 44 by rw [image3_eq]; rfl))

theorem lex_3_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 599) (Sat.Literal.pos 598) (Sat.Literal.pos 44) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation3 44 (assignment s)
    (Sat.Literal.pos 599) (Sat.Literal.pos 598) (Sat.Literal.pos 44) (Sat.Literal.pos 52) (positive_of_descriptor s 599 (.lex permutation3 44) (by rfl)) (lex_3_44_prefix s) (positive_select s 44) (lex_3_44_image s)

theorem lex_3_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 598), (Sat.Literal.pos 44), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation3 44 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 598) (Sat.Literal.pos 44) (Sat.Literal.pos 52) (lex_3_44_prefix s) (positive_select s 44) (lex_3_44_image s)

theorem lex_3_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 599), (Sat.Literal.pos 598)] :=
  (lex_3_44_gate s).prop _ (List.Mem.head _)

theorem lex_3_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 599), (Sat.Literal.neg 44), (Sat.Literal.pos 52)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 599), (Sat.Literal.pos 44), (Sat.Literal.neg 52)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 598), (Sat.Literal.neg 44), (Sat.Literal.neg 52), (Sat.Literal.pos 599)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 598), (Sat.Literal.pos 44), (Sat.Literal.pos 52), (Sat.Literal.pos 599)] :=
  (lex_3_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 599) = lexBefore s permutation3 43 := by
  exact (positive_lex_of_descriptor s 599 permutation3 44 (by rfl)).trans ((lex_skipped s permutation3 43 44 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation3 43) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 64) = permuteMask permutation3 43 by rw [image3_eq]; rfl))

theorem lex_3_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 600) (Sat.Literal.pos 599) (Sat.Literal.pos 43) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation3 43 (assignment s)
    (Sat.Literal.pos 600) (Sat.Literal.pos 599) (Sat.Literal.pos 43) (Sat.Literal.pos 51) (positive_of_descriptor s 600 (.lex permutation3 43) (by rfl)) (lex_3_43_prefix s) (positive_select s 43) (lex_3_43_image s)

theorem lex_3_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 599), (Sat.Literal.pos 43), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation3 43 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 599) (Sat.Literal.pos 43) (Sat.Literal.pos 51) (lex_3_43_prefix s) (positive_select s 43) (lex_3_43_image s)

theorem lex_3_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 600), (Sat.Literal.pos 599)] :=
  (lex_3_43_gate s).prop _ (List.Mem.head _)

theorem lex_3_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 600), (Sat.Literal.neg 43), (Sat.Literal.pos 51)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 600), (Sat.Literal.pos 43), (Sat.Literal.neg 51)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 599), (Sat.Literal.neg 43), (Sat.Literal.neg 51), (Sat.Literal.pos 600)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 599), (Sat.Literal.pos 43), (Sat.Literal.pos 51), (Sat.Literal.pos 600)] :=
  (lex_3_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 600) = lexBefore s permutation3 42 := by
  exact (positive_lex_of_descriptor s 600 permutation3 43 (by rfl)).trans ((lex_skipped s permutation3 42 43 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation3 42) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation3 42 by rw [image3_eq]; rfl))

theorem lex_3_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 601) (Sat.Literal.pos 600) (Sat.Literal.pos 42) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation3 42 (assignment s)
    (Sat.Literal.pos 601) (Sat.Literal.pos 600) (Sat.Literal.pos 42) (Sat.Literal.pos 50) (positive_of_descriptor s 601 (.lex permutation3 42) (by rfl)) (lex_3_42_prefix s) (positive_select s 42) (lex_3_42_image s)

theorem lex_3_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 600), (Sat.Literal.pos 42), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation3 42 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 600) (Sat.Literal.pos 42) (Sat.Literal.pos 50) (lex_3_42_prefix s) (positive_select s 42) (lex_3_42_image s)

theorem lex_3_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 601), (Sat.Literal.pos 600)] :=
  (lex_3_42_gate s).prop _ (List.Mem.head _)

theorem lex_3_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 601), (Sat.Literal.neg 42), (Sat.Literal.pos 50)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 601), (Sat.Literal.pos 42), (Sat.Literal.neg 50)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 600), (Sat.Literal.neg 42), (Sat.Literal.neg 50), (Sat.Literal.pos 601)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 600), (Sat.Literal.pos 42), (Sat.Literal.pos 50), (Sat.Literal.pos 601)] :=
  (lex_3_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 601) = lexBefore s permutation3 41 := by
  exact (positive_lex_of_descriptor s 601 permutation3 42 (by rfl)).trans ((lex_skipped s permutation3 41 42 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation3 41) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 64) = permuteMask permutation3 41 by rw [image3_eq]; rfl))

theorem lex_3_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 602) (Sat.Literal.pos 601) (Sat.Literal.pos 41) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation3 41 (assignment s)
    (Sat.Literal.pos 602) (Sat.Literal.pos 601) (Sat.Literal.pos 41) (Sat.Literal.pos 49) (positive_of_descriptor s 602 (.lex permutation3 41) (by rfl)) (lex_3_41_prefix s) (positive_select s 41) (lex_3_41_image s)

theorem lex_3_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 601), (Sat.Literal.pos 41), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation3 41 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 601) (Sat.Literal.pos 41) (Sat.Literal.pos 49) (lex_3_41_prefix s) (positive_select s 41) (lex_3_41_image s)

theorem lex_3_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 602), (Sat.Literal.pos 601)] :=
  (lex_3_41_gate s).prop _ (List.Mem.head _)

theorem lex_3_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 602), (Sat.Literal.neg 41), (Sat.Literal.pos 49)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 602), (Sat.Literal.pos 41), (Sat.Literal.neg 49)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 601), (Sat.Literal.neg 41), (Sat.Literal.neg 49), (Sat.Literal.pos 602)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 601), (Sat.Literal.pos 41), (Sat.Literal.pos 49), (Sat.Literal.pos 602)] :=
  (lex_3_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 602) = lexBefore s permutation3 40 := by
  exact (positive_lex_of_descriptor s 602 permutation3 41 (by rfl)).trans ((lex_skipped s permutation3 40 41 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation3 40) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 64) = permuteMask permutation3 40 by rw [image3_eq]; rfl))

theorem lex_3_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 603) (Sat.Literal.pos 602) (Sat.Literal.pos 40) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation3 40 (assignment s)
    (Sat.Literal.pos 603) (Sat.Literal.pos 602) (Sat.Literal.pos 40) (Sat.Literal.pos 48) (positive_of_descriptor s 603 (.lex permutation3 40) (by rfl)) (lex_3_40_prefix s) (positive_select s 40) (lex_3_40_image s)

theorem lex_3_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 602), (Sat.Literal.pos 40), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation3 40 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 602) (Sat.Literal.pos 40) (Sat.Literal.pos 48) (lex_3_40_prefix s) (positive_select s 40) (lex_3_40_image s)

theorem lex_3_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 603), (Sat.Literal.pos 602)] :=
  (lex_3_40_gate s).prop _ (List.Mem.head _)

theorem lex_3_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 603), (Sat.Literal.neg 40), (Sat.Literal.pos 48)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 603), (Sat.Literal.pos 40), (Sat.Literal.neg 48)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 602), (Sat.Literal.neg 40), (Sat.Literal.neg 48), (Sat.Literal.pos 603)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 602), (Sat.Literal.pos 40), (Sat.Literal.pos 48), (Sat.Literal.pos 603)] :=
  (lex_3_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 603) = lexBefore s permutation3 23 := by
  exact (positive_lex_of_descriptor s 603 permutation3 40 (by rfl)).trans ((lex_skipped s permutation3 23 40 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 24 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation3 23) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 64) = permuteMask permutation3 23 by rw [image3_eq]; rfl))

theorem lex_3_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 604) (Sat.Literal.pos 603) (Sat.Literal.pos 23) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation3 23 (assignment s)
    (Sat.Literal.pos 604) (Sat.Literal.pos 603) (Sat.Literal.pos 23) (Sat.Literal.pos 15) (positive_of_descriptor s 604 (.lex permutation3 23) (by rfl)) (lex_3_23_prefix s) (positive_select s 23) (lex_3_23_image s)

theorem lex_3_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 603), (Sat.Literal.pos 23), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation3 23 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 603) (Sat.Literal.pos 23) (Sat.Literal.pos 15) (lex_3_23_prefix s) (positive_select s 23) (lex_3_23_image s)

theorem lex_3_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 604), (Sat.Literal.pos 603)] :=
  (lex_3_23_gate s).prop _ (List.Mem.head _)

theorem lex_3_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 604), (Sat.Literal.neg 23), (Sat.Literal.pos 15)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 604), (Sat.Literal.pos 23), (Sat.Literal.neg 15)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 603), (Sat.Literal.neg 23), (Sat.Literal.neg 15), (Sat.Literal.pos 604)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 603), (Sat.Literal.pos 23), (Sat.Literal.pos 15), (Sat.Literal.pos 604)] :=
  (lex_3_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 604) = lexBefore s permutation3 22 := by
  exact (positive_lex_of_descriptor s 604 permutation3 23 (by rfl)).trans ((lex_skipped s permutation3 22 23 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation3 22) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 64) = permuteMask permutation3 22 by rw [image3_eq]; rfl))

theorem lex_3_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 605) (Sat.Literal.pos 604) (Sat.Literal.pos 22) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation3 22 (assignment s)
    (Sat.Literal.pos 605) (Sat.Literal.pos 604) (Sat.Literal.pos 22) (Sat.Literal.pos 14) (positive_of_descriptor s 605 (.lex permutation3 22) (by rfl)) (lex_3_22_prefix s) (positive_select s 22) (lex_3_22_image s)

theorem lex_3_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 604), (Sat.Literal.pos 22), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation3 22 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 604) (Sat.Literal.pos 22) (Sat.Literal.pos 14) (lex_3_22_prefix s) (positive_select s 22) (lex_3_22_image s)

theorem lex_3_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 605), (Sat.Literal.pos 604)] :=
  (lex_3_22_gate s).prop _ (List.Mem.head _)

theorem lex_3_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 605), (Sat.Literal.neg 22), (Sat.Literal.pos 14)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 605), (Sat.Literal.pos 22), (Sat.Literal.neg 14)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 604), (Sat.Literal.neg 22), (Sat.Literal.neg 14), (Sat.Literal.pos 605)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 604), (Sat.Literal.pos 22), (Sat.Literal.pos 14), (Sat.Literal.pos 605)] :=
  (lex_3_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 605) = lexBefore s permutation3 21 := by
  exact (positive_lex_of_descriptor s 605 permutation3 22 (by rfl)).trans ((lex_skipped s permutation3 21 22 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation3 21) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation3 21 by rw [image3_eq]; rfl))

theorem lex_3_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 606) (Sat.Literal.pos 605) (Sat.Literal.pos 21) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation3 21 (assignment s)
    (Sat.Literal.pos 606) (Sat.Literal.pos 605) (Sat.Literal.pos 21) (Sat.Literal.pos 13) (positive_of_descriptor s 606 (.lex permutation3 21) (by rfl)) (lex_3_21_prefix s) (positive_select s 21) (lex_3_21_image s)

theorem lex_3_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 605), (Sat.Literal.pos 21), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation3 21 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 605) (Sat.Literal.pos 21) (Sat.Literal.pos 13) (lex_3_21_prefix s) (positive_select s 21) (lex_3_21_image s)

theorem lex_3_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 606), (Sat.Literal.pos 605)] :=
  (lex_3_21_gate s).prop _ (List.Mem.head _)

theorem lex_3_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 606), (Sat.Literal.neg 21), (Sat.Literal.pos 13)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 606), (Sat.Literal.pos 21), (Sat.Literal.neg 13)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 605), (Sat.Literal.neg 21), (Sat.Literal.neg 13), (Sat.Literal.pos 606)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 605), (Sat.Literal.pos 21), (Sat.Literal.pos 13), (Sat.Literal.pos 606)] :=
  (lex_3_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 606) = lexBefore s permutation3 20 := by
  exact (positive_lex_of_descriptor s 606 permutation3 21 (by rfl)).trans ((lex_skipped s permutation3 20 21 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation3 20) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 64) = permuteMask permutation3 20 by rw [image3_eq]; rfl))

theorem lex_3_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 607) (Sat.Literal.pos 606) (Sat.Literal.pos 20) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation3 20 (assignment s)
    (Sat.Literal.pos 607) (Sat.Literal.pos 606) (Sat.Literal.pos 20) (Sat.Literal.pos 12) (positive_of_descriptor s 607 (.lex permutation3 20) (by rfl)) (lex_3_20_prefix s) (positive_select s 20) (lex_3_20_image s)

theorem lex_3_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 606), (Sat.Literal.pos 20), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation3 20 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 606) (Sat.Literal.pos 20) (Sat.Literal.pos 12) (lex_3_20_prefix s) (positive_select s 20) (lex_3_20_image s)

theorem lex_3_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 607), (Sat.Literal.pos 606)] :=
  (lex_3_20_gate s).prop _ (List.Mem.head _)

theorem lex_3_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 607), (Sat.Literal.neg 20), (Sat.Literal.pos 12)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 607), (Sat.Literal.pos 20), (Sat.Literal.neg 12)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 606), (Sat.Literal.neg 20), (Sat.Literal.neg 12), (Sat.Literal.pos 607)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 606), (Sat.Literal.pos 20), (Sat.Literal.pos 12), (Sat.Literal.pos 607)] :=
  (lex_3_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 607) = lexBefore s permutation3 19 := by
  exact (positive_lex_of_descriptor s 607 permutation3 20 (by rfl)).trans ((lex_skipped s permutation3 19 20 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation3 19) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation3 19 by rw [image3_eq]; rfl))

theorem lex_3_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 608) (Sat.Literal.pos 607) (Sat.Literal.pos 19) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation3 19 (assignment s)
    (Sat.Literal.pos 608) (Sat.Literal.pos 607) (Sat.Literal.pos 19) (Sat.Literal.pos 11) (positive_of_descriptor s 608 (.lex permutation3 19) (by rfl)) (lex_3_19_prefix s) (positive_select s 19) (lex_3_19_image s)

theorem lex_3_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 607), (Sat.Literal.pos 19), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation3 19 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 607) (Sat.Literal.pos 19) (Sat.Literal.pos 11) (lex_3_19_prefix s) (positive_select s 19) (lex_3_19_image s)

theorem lex_3_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 608), (Sat.Literal.pos 607)] :=
  (lex_3_19_gate s).prop _ (List.Mem.head _)

theorem lex_3_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 608), (Sat.Literal.neg 19), (Sat.Literal.pos 11)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 608), (Sat.Literal.pos 19), (Sat.Literal.neg 11)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 607), (Sat.Literal.neg 19), (Sat.Literal.neg 11), (Sat.Literal.pos 608)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 607), (Sat.Literal.pos 19), (Sat.Literal.pos 11), (Sat.Literal.pos 608)] :=
  (lex_3_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 608) = lexBefore s permutation3 18 := by
  exact (positive_lex_of_descriptor s 608 permutation3 19 (by rfl)).trans ((lex_skipped s permutation3 18 19 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation3 18) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 64) = permuteMask permutation3 18 by rw [image3_eq]; rfl))

theorem lex_3_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 609) (Sat.Literal.pos 608) (Sat.Literal.pos 18) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation3 18 (assignment s)
    (Sat.Literal.pos 609) (Sat.Literal.pos 608) (Sat.Literal.pos 18) (Sat.Literal.pos 10) (positive_of_descriptor s 609 (.lex permutation3 18) (by rfl)) (lex_3_18_prefix s) (positive_select s 18) (lex_3_18_image s)

theorem lex_3_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 608), (Sat.Literal.pos 18), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation3 18 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 608) (Sat.Literal.pos 18) (Sat.Literal.pos 10) (lex_3_18_prefix s) (positive_select s 18) (lex_3_18_image s)

theorem lex_3_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 609), (Sat.Literal.pos 608)] :=
  (lex_3_18_gate s).prop _ (List.Mem.head _)

theorem lex_3_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 609), (Sat.Literal.neg 18), (Sat.Literal.pos 10)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 609), (Sat.Literal.pos 18), (Sat.Literal.neg 10)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 608), (Sat.Literal.neg 18), (Sat.Literal.neg 10), (Sat.Literal.pos 609)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 608), (Sat.Literal.pos 18), (Sat.Literal.pos 10), (Sat.Literal.pos 609)] :=
  (lex_3_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 609) = lexBefore s permutation3 17 := by
  exact (positive_lex_of_descriptor s 609 permutation3 18 (by rfl)).trans ((lex_skipped s permutation3 17 18 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation3 17) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 64) = permuteMask permutation3 17 by rw [image3_eq]; rfl))

theorem lex_3_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 610) (Sat.Literal.pos 609) (Sat.Literal.pos 17) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation3 17 (assignment s)
    (Sat.Literal.pos 610) (Sat.Literal.pos 609) (Sat.Literal.pos 17) (Sat.Literal.pos 9) (positive_of_descriptor s 610 (.lex permutation3 17) (by rfl)) (lex_3_17_prefix s) (positive_select s 17) (lex_3_17_image s)

theorem lex_3_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 609), (Sat.Literal.pos 17), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation3 17 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 609) (Sat.Literal.pos 17) (Sat.Literal.pos 9) (lex_3_17_prefix s) (positive_select s 17) (lex_3_17_image s)

theorem lex_3_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 610), (Sat.Literal.pos 609)] :=
  (lex_3_17_gate s).prop _ (List.Mem.head _)

theorem lex_3_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 610), (Sat.Literal.neg 17), (Sat.Literal.pos 9)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 610), (Sat.Literal.pos 17), (Sat.Literal.neg 9)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 609), (Sat.Literal.neg 17), (Sat.Literal.neg 9), (Sat.Literal.pos 610)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 609), (Sat.Literal.pos 17), (Sat.Literal.pos 9), (Sat.Literal.pos 610)] :=
  (lex_3_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_16_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 610) = lexBefore s permutation3 16 := by
  exact (positive_lex_of_descriptor s 610 permutation3 17 (by rfl)).trans ((lex_skipped s permutation3 16 17 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_16_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation3 16) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 64) = permuteMask permutation3 16 by rw [image3_eq]; rfl))

theorem lex_3_16_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 611) (Sat.Literal.pos 610) (Sat.Literal.pos 16) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation3 16 (assignment s)
    (Sat.Literal.pos 611) (Sat.Literal.pos 610) (Sat.Literal.pos 16) (Sat.Literal.pos 8) (positive_of_descriptor s 611 (.lex permutation3 16) (by rfl)) (lex_3_16_prefix s) (positive_select s 16) (lex_3_16_image s)

theorem lex_3_16_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 610), (Sat.Literal.pos 16), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation3 16 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 610) (Sat.Literal.pos 16) (Sat.Literal.pos 8) (lex_3_16_prefix s) (positive_select s 16) (lex_3_16_image s)

theorem lex_3_16_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 611), (Sat.Literal.pos 610)] :=
  (lex_3_16_gate s).prop _ (List.Mem.head _)

theorem lex_3_16_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 611), (Sat.Literal.neg 16), (Sat.Literal.pos 8)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_16_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 611), (Sat.Literal.pos 16), (Sat.Literal.neg 8)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_16_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 610), (Sat.Literal.neg 16), (Sat.Literal.neg 8), (Sat.Literal.pos 611)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_16_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 610), (Sat.Literal.pos 16), (Sat.Literal.pos 8), (Sat.Literal.pos 611)] :=
  (lex_3_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_15_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 611) = lexBefore s permutation3 15 := by
  exact (positive_lex_of_descriptor s 611 permutation3 16 (by rfl)).trans ((lex_skipped s permutation3 15 16 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_15_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation3 15) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation3 15 by rw [image3_eq]; rfl))

theorem lex_3_15_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 612) (Sat.Literal.pos 611) (Sat.Literal.pos 15) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation3 15 (assignment s)
    (Sat.Literal.pos 612) (Sat.Literal.pos 611) (Sat.Literal.pos 15) (Sat.Literal.pos 23) (positive_of_descriptor s 612 (.lex permutation3 15) (by rfl)) (lex_3_15_prefix s) (positive_select s 15) (lex_3_15_image s)

theorem lex_3_15_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 611), (Sat.Literal.pos 15), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation3 15 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 611) (Sat.Literal.pos 15) (Sat.Literal.pos 23) (lex_3_15_prefix s) (positive_select s 15) (lex_3_15_image s)

theorem lex_3_15_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 612), (Sat.Literal.pos 611)] :=
  (lex_3_15_gate s).prop _ (List.Mem.head _)

theorem lex_3_15_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 612), (Sat.Literal.neg 15), (Sat.Literal.pos 23)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_15_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 612), (Sat.Literal.pos 15), (Sat.Literal.neg 23)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_15_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 611), (Sat.Literal.neg 15), (Sat.Literal.neg 23), (Sat.Literal.pos 612)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_15_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 611), (Sat.Literal.pos 15), (Sat.Literal.pos 23), (Sat.Literal.pos 612)] :=
  (lex_3_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_14_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 612) = lexBefore s permutation3 14 := by
  exact (positive_lex_of_descriptor s 612 permutation3 15 (by rfl)).trans ((lex_skipped s permutation3 14 15 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_14_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation3 14) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation3 14 by rw [image3_eq]; rfl))

theorem lex_3_14_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 613) (Sat.Literal.pos 612) (Sat.Literal.pos 14) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation3 14 (assignment s)
    (Sat.Literal.pos 613) (Sat.Literal.pos 612) (Sat.Literal.pos 14) (Sat.Literal.pos 22) (positive_of_descriptor s 613 (.lex permutation3 14) (by rfl)) (lex_3_14_prefix s) (positive_select s 14) (lex_3_14_image s)

theorem lex_3_14_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 612), (Sat.Literal.pos 14), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation3 14 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 612) (Sat.Literal.pos 14) (Sat.Literal.pos 22) (lex_3_14_prefix s) (positive_select s 14) (lex_3_14_image s)

theorem lex_3_14_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 613), (Sat.Literal.pos 612)] :=
  (lex_3_14_gate s).prop _ (List.Mem.head _)

theorem lex_3_14_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 613), (Sat.Literal.neg 14), (Sat.Literal.pos 22)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_14_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 613), (Sat.Literal.pos 14), (Sat.Literal.neg 22)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_14_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 612), (Sat.Literal.neg 14), (Sat.Literal.neg 22), (Sat.Literal.pos 613)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_14_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 612), (Sat.Literal.pos 14), (Sat.Literal.pos 22), (Sat.Literal.pos 613)] :=
  (lex_3_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_13_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 613) = lexBefore s permutation3 13 := by
  exact (positive_lex_of_descriptor s 613 permutation3 14 (by rfl)).trans ((lex_skipped s permutation3 13 14 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_13_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation3 13) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation3 13 by rw [image3_eq]; rfl))

theorem lex_3_13_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 614) (Sat.Literal.pos 613) (Sat.Literal.pos 13) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation3 13 (assignment s)
    (Sat.Literal.pos 614) (Sat.Literal.pos 613) (Sat.Literal.pos 13) (Sat.Literal.pos 21) (positive_of_descriptor s 614 (.lex permutation3 13) (by rfl)) (lex_3_13_prefix s) (positive_select s 13) (lex_3_13_image s)

theorem lex_3_13_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 613), (Sat.Literal.pos 13), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation3 13 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 613) (Sat.Literal.pos 13) (Sat.Literal.pos 21) (lex_3_13_prefix s) (positive_select s 13) (lex_3_13_image s)

theorem lex_3_13_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 614), (Sat.Literal.pos 613)] :=
  (lex_3_13_gate s).prop _ (List.Mem.head _)

theorem lex_3_13_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 614), (Sat.Literal.neg 13), (Sat.Literal.pos 21)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_13_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 614), (Sat.Literal.pos 13), (Sat.Literal.neg 21)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_13_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 613), (Sat.Literal.neg 13), (Sat.Literal.neg 21), (Sat.Literal.pos 614)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_13_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 613), (Sat.Literal.pos 13), (Sat.Literal.pos 21), (Sat.Literal.pos 614)] :=
  (lex_3_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_12_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 614) = lexBefore s permutation3 12 := by
  exact (positive_lex_of_descriptor s 614 permutation3 13 (by rfl)).trans ((lex_skipped s permutation3 12 13 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_12_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation3 12) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation3 12 by rw [image3_eq]; rfl))

theorem lex_3_12_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 615) (Sat.Literal.pos 614) (Sat.Literal.pos 12) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation3 12 (assignment s)
    (Sat.Literal.pos 615) (Sat.Literal.pos 614) (Sat.Literal.pos 12) (Sat.Literal.pos 20) (positive_of_descriptor s 615 (.lex permutation3 12) (by rfl)) (lex_3_12_prefix s) (positive_select s 12) (lex_3_12_image s)

theorem lex_3_12_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 614), (Sat.Literal.pos 12), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation3 12 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 614) (Sat.Literal.pos 12) (Sat.Literal.pos 20) (lex_3_12_prefix s) (positive_select s 12) (lex_3_12_image s)

theorem lex_3_12_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 615), (Sat.Literal.pos 614)] :=
  (lex_3_12_gate s).prop _ (List.Mem.head _)

theorem lex_3_12_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 615), (Sat.Literal.neg 12), (Sat.Literal.pos 20)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_12_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 615), (Sat.Literal.pos 12), (Sat.Literal.neg 20)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_12_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 614), (Sat.Literal.neg 12), (Sat.Literal.neg 20), (Sat.Literal.pos 615)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_12_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 614), (Sat.Literal.pos 12), (Sat.Literal.pos 20), (Sat.Literal.pos 615)] :=
  (lex_3_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_11_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 615) = lexBefore s permutation3 11 := by
  exact (positive_lex_of_descriptor s 615 permutation3 12 (by rfl)).trans ((lex_skipped s permutation3 11 12 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_11_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation3 11) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation3 11 by rw [image3_eq]; rfl))

theorem lex_3_11_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 616) (Sat.Literal.pos 615) (Sat.Literal.pos 11) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation3 11 (assignment s)
    (Sat.Literal.pos 616) (Sat.Literal.pos 615) (Sat.Literal.pos 11) (Sat.Literal.pos 19) (positive_of_descriptor s 616 (.lex permutation3 11) (by rfl)) (lex_3_11_prefix s) (positive_select s 11) (lex_3_11_image s)

theorem lex_3_11_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 615), (Sat.Literal.pos 11), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation3 11 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 615) (Sat.Literal.pos 11) (Sat.Literal.pos 19) (lex_3_11_prefix s) (positive_select s 11) (lex_3_11_image s)

theorem lex_3_11_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 616), (Sat.Literal.pos 615)] :=
  (lex_3_11_gate s).prop _ (List.Mem.head _)

theorem lex_3_11_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 616), (Sat.Literal.neg 11), (Sat.Literal.pos 19)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_11_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 616), (Sat.Literal.pos 11), (Sat.Literal.neg 19)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_11_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 615), (Sat.Literal.neg 11), (Sat.Literal.neg 19), (Sat.Literal.pos 616)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_11_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 615), (Sat.Literal.pos 11), (Sat.Literal.pos 19), (Sat.Literal.pos 616)] :=
  (lex_3_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_10_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 616) = lexBefore s permutation3 10 := by
  exact (positive_lex_of_descriptor s 616 permutation3 11 (by rfl)).trans ((lex_skipped s permutation3 10 11 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_10_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation3 10) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation3 10 by rw [image3_eq]; rfl))

theorem lex_3_10_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 617) (Sat.Literal.pos 616) (Sat.Literal.pos 10) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation3 10 (assignment s)
    (Sat.Literal.pos 617) (Sat.Literal.pos 616) (Sat.Literal.pos 10) (Sat.Literal.pos 18) (positive_of_descriptor s 617 (.lex permutation3 10) (by rfl)) (lex_3_10_prefix s) (positive_select s 10) (lex_3_10_image s)

theorem lex_3_10_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 616), (Sat.Literal.pos 10), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation3 10 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 616) (Sat.Literal.pos 10) (Sat.Literal.pos 18) (lex_3_10_prefix s) (positive_select s 10) (lex_3_10_image s)

theorem lex_3_10_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 617), (Sat.Literal.pos 616)] :=
  (lex_3_10_gate s).prop _ (List.Mem.head _)

theorem lex_3_10_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 617), (Sat.Literal.neg 10), (Sat.Literal.pos 18)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_10_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 617), (Sat.Literal.pos 10), (Sat.Literal.neg 18)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_10_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 616), (Sat.Literal.neg 10), (Sat.Literal.neg 18), (Sat.Literal.pos 617)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_10_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 616), (Sat.Literal.pos 10), (Sat.Literal.pos 18), (Sat.Literal.pos 617)] :=
  (lex_3_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_9_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 617) = lexBefore s permutation3 9 := by
  exact (positive_lex_of_descriptor s 617 permutation3 10 (by rfl)).trans ((lex_skipped s permutation3 9 10 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_9_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation3 9) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation3 9 by rw [image3_eq]; rfl))

theorem lex_3_9_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 618) (Sat.Literal.pos 617) (Sat.Literal.pos 9) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation3 9 (assignment s)
    (Sat.Literal.pos 618) (Sat.Literal.pos 617) (Sat.Literal.pos 9) (Sat.Literal.pos 17) (positive_of_descriptor s 618 (.lex permutation3 9) (by rfl)) (lex_3_9_prefix s) (positive_select s 9) (lex_3_9_image s)

theorem lex_3_9_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 617), (Sat.Literal.pos 9), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation3 9 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 617) (Sat.Literal.pos 9) (Sat.Literal.pos 17) (lex_3_9_prefix s) (positive_select s 9) (lex_3_9_image s)

theorem lex_3_9_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 618), (Sat.Literal.pos 617)] :=
  (lex_3_9_gate s).prop _ (List.Mem.head _)

theorem lex_3_9_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 618), (Sat.Literal.neg 9), (Sat.Literal.pos 17)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_9_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 618), (Sat.Literal.pos 9), (Sat.Literal.neg 17)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_9_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 617), (Sat.Literal.neg 9), (Sat.Literal.neg 17), (Sat.Literal.pos 618)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_9_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 617), (Sat.Literal.pos 9), (Sat.Literal.pos 17), (Sat.Literal.pos 618)] :=
  (lex_3_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_3_8_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 618) = lexBefore s permutation3 8 := by
  exact (positive_lex_of_descriptor s 618 permutation3 9 (by rfl)).trans ((lex_skipped s permutation3 8 9 (by decide) (by intro j hj hp; rw [image3_eq]; exact fixedOnRange_spec image3 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_3_8_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation3 8) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 64) = permuteMask permutation3 8 by rw [image3_eq]; rfl))

theorem lex_3_8_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 619) (Sat.Literal.pos 618) (Sat.Literal.pos 8) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation3 8 (assignment s)
    (Sat.Literal.pos 619) (Sat.Literal.pos 618) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (positive_of_descriptor s 619 (.lex permutation3 8) (by rfl)) (lex_3_8_prefix s) (positive_select s 8) (lex_3_8_image s)

theorem lex_3_8_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 618), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation3 8 (hmax permutation3) (assignment s)
    (Sat.Literal.pos 618) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (lex_3_8_prefix s) (positive_select s 8) (lex_3_8_image s)

theorem lex_3_8_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 619), (Sat.Literal.pos 618)] :=
  (lex_3_8_gate s).prop _ (List.Mem.head _)

theorem lex_3_8_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 619), (Sat.Literal.neg 8), (Sat.Literal.pos 16)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_3_8_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 619), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_3_8_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 618), (Sat.Literal.neg 8), (Sat.Literal.neg 16), (Sat.Literal.pos 619)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_3_8_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 618), (Sat.Literal.pos 8), (Sat.Literal.pos 16), (Sat.Literal.pos 619)] :=
  (lex_3_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_47_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation4 47 := by
  exact (negative_falsum s).trans ((lex_first s permutation4 47 (by intro j hj; rw [image4_eq]; exact fixedOnRange_spec image4 48 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_4_47_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation4 47) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 64) = permuteMask permutation4 47 by rw [image4_eq]; rfl))

theorem lex_4_47_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 620) (Sat.Literal.neg 64) (Sat.Literal.pos 47) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation4 47 (assignment s)
    (Sat.Literal.pos 620) (Sat.Literal.neg 64) (Sat.Literal.pos 47) (Sat.Literal.pos 31) (positive_of_descriptor s 620 (.lex permutation4 47) (by rfl)) (lex_4_47_prefix s) (positive_select s 47) (lex_4_47_image s)

theorem lex_4_47_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 47), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation4 47 (hmax permutation4) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 47) (Sat.Literal.pos 31) (lex_4_47_prefix s) (positive_select s 47) (lex_4_47_image s)

theorem lex_4_47_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 620), (Sat.Literal.neg 64)] :=
  (lex_4_47_gate s).prop _ (List.Mem.head _)

theorem lex_4_47_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 620), (Sat.Literal.neg 47), (Sat.Literal.pos 31)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_47_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 620), (Sat.Literal.pos 47), (Sat.Literal.neg 31)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_47_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 47), (Sat.Literal.neg 31), (Sat.Literal.pos 620)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_47_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 47), (Sat.Literal.pos 31), (Sat.Literal.pos 620)] :=
  (lex_4_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 620) = lexBefore s permutation4 46 := by
  exact (positive_lex_of_descriptor s 620 permutation4 47 (by rfl)).trans ((lex_skipped s permutation4 46 47 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation4 46) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 64) = permuteMask permutation4 46 by rw [image4_eq]; rfl))

theorem lex_4_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 621) (Sat.Literal.pos 620) (Sat.Literal.pos 46) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation4 46 (assignment s)
    (Sat.Literal.pos 621) (Sat.Literal.pos 620) (Sat.Literal.pos 46) (Sat.Literal.pos 30) (positive_of_descriptor s 621 (.lex permutation4 46) (by rfl)) (lex_4_46_prefix s) (positive_select s 46) (lex_4_46_image s)

theorem lex_4_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 620), (Sat.Literal.pos 46), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation4 46 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 620) (Sat.Literal.pos 46) (Sat.Literal.pos 30) (lex_4_46_prefix s) (positive_select s 46) (lex_4_46_image s)

theorem lex_4_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 621), (Sat.Literal.pos 620)] :=
  (lex_4_46_gate s).prop _ (List.Mem.head _)

theorem lex_4_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 621), (Sat.Literal.neg 46), (Sat.Literal.pos 30)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 621), (Sat.Literal.pos 46), (Sat.Literal.neg 30)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 620), (Sat.Literal.neg 46), (Sat.Literal.neg 30), (Sat.Literal.pos 621)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 620), (Sat.Literal.pos 46), (Sat.Literal.pos 30), (Sat.Literal.pos 621)] :=
  (lex_4_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 621) = lexBefore s permutation4 45 := by
  exact (positive_lex_of_descriptor s 621 permutation4 46 (by rfl)).trans ((lex_skipped s permutation4 45 46 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation4 45) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation4 45 by rw [image4_eq]; rfl))

theorem lex_4_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 622) (Sat.Literal.pos 621) (Sat.Literal.pos 45) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation4 45 (assignment s)
    (Sat.Literal.pos 622) (Sat.Literal.pos 621) (Sat.Literal.pos 45) (Sat.Literal.pos 29) (positive_of_descriptor s 622 (.lex permutation4 45) (by rfl)) (lex_4_45_prefix s) (positive_select s 45) (lex_4_45_image s)

theorem lex_4_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 621), (Sat.Literal.pos 45), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation4 45 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 621) (Sat.Literal.pos 45) (Sat.Literal.pos 29) (lex_4_45_prefix s) (positive_select s 45) (lex_4_45_image s)

theorem lex_4_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 622), (Sat.Literal.pos 621)] :=
  (lex_4_45_gate s).prop _ (List.Mem.head _)

theorem lex_4_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 622), (Sat.Literal.neg 45), (Sat.Literal.pos 29)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 622), (Sat.Literal.pos 45), (Sat.Literal.neg 29)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 621), (Sat.Literal.neg 45), (Sat.Literal.neg 29), (Sat.Literal.pos 622)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 621), (Sat.Literal.pos 45), (Sat.Literal.pos 29), (Sat.Literal.pos 622)] :=
  (lex_4_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 622) = lexBefore s permutation4 44 := by
  exact (positive_lex_of_descriptor s 622 permutation4 45 (by rfl)).trans ((lex_skipped s permutation4 44 45 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation4 44) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 64) = permuteMask permutation4 44 by rw [image4_eq]; rfl))

theorem lex_4_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 623) (Sat.Literal.pos 622) (Sat.Literal.pos 44) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation4 44 (assignment s)
    (Sat.Literal.pos 623) (Sat.Literal.pos 622) (Sat.Literal.pos 44) (Sat.Literal.pos 28) (positive_of_descriptor s 623 (.lex permutation4 44) (by rfl)) (lex_4_44_prefix s) (positive_select s 44) (lex_4_44_image s)

theorem lex_4_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 622), (Sat.Literal.pos 44), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation4 44 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 622) (Sat.Literal.pos 44) (Sat.Literal.pos 28) (lex_4_44_prefix s) (positive_select s 44) (lex_4_44_image s)

theorem lex_4_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 623), (Sat.Literal.pos 622)] :=
  (lex_4_44_gate s).prop _ (List.Mem.head _)

theorem lex_4_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 623), (Sat.Literal.neg 44), (Sat.Literal.pos 28)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 623), (Sat.Literal.pos 44), (Sat.Literal.neg 28)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 622), (Sat.Literal.neg 44), (Sat.Literal.neg 28), (Sat.Literal.pos 623)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 622), (Sat.Literal.pos 44), (Sat.Literal.pos 28), (Sat.Literal.pos 623)] :=
  (lex_4_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 623) = lexBefore s permutation4 43 := by
  exact (positive_lex_of_descriptor s 623 permutation4 44 (by rfl)).trans ((lex_skipped s permutation4 43 44 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation4 43) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 64) = permuteMask permutation4 43 by rw [image4_eq]; rfl))

theorem lex_4_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 624) (Sat.Literal.pos 623) (Sat.Literal.pos 43) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation4 43 (assignment s)
    (Sat.Literal.pos 624) (Sat.Literal.pos 623) (Sat.Literal.pos 43) (Sat.Literal.pos 27) (positive_of_descriptor s 624 (.lex permutation4 43) (by rfl)) (lex_4_43_prefix s) (positive_select s 43) (lex_4_43_image s)

theorem lex_4_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 623), (Sat.Literal.pos 43), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation4 43 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 623) (Sat.Literal.pos 43) (Sat.Literal.pos 27) (lex_4_43_prefix s) (positive_select s 43) (lex_4_43_image s)

theorem lex_4_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 624), (Sat.Literal.pos 623)] :=
  (lex_4_43_gate s).prop _ (List.Mem.head _)

theorem lex_4_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 624), (Sat.Literal.neg 43), (Sat.Literal.pos 27)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 624), (Sat.Literal.pos 43), (Sat.Literal.neg 27)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 623), (Sat.Literal.neg 43), (Sat.Literal.neg 27), (Sat.Literal.pos 624)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 623), (Sat.Literal.pos 43), (Sat.Literal.pos 27), (Sat.Literal.pos 624)] :=
  (lex_4_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 624) = lexBefore s permutation4 42 := by
  exact (positive_lex_of_descriptor s 624 permutation4 43 (by rfl)).trans ((lex_skipped s permutation4 42 43 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation4 42) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 64) = permuteMask permutation4 42 by rw [image4_eq]; rfl))

theorem lex_4_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 625) (Sat.Literal.pos 624) (Sat.Literal.pos 42) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation4 42 (assignment s)
    (Sat.Literal.pos 625) (Sat.Literal.pos 624) (Sat.Literal.pos 42) (Sat.Literal.pos 26) (positive_of_descriptor s 625 (.lex permutation4 42) (by rfl)) (lex_4_42_prefix s) (positive_select s 42) (lex_4_42_image s)

theorem lex_4_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 624), (Sat.Literal.pos 42), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation4 42 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 624) (Sat.Literal.pos 42) (Sat.Literal.pos 26) (lex_4_42_prefix s) (positive_select s 42) (lex_4_42_image s)

theorem lex_4_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 625), (Sat.Literal.pos 624)] :=
  (lex_4_42_gate s).prop _ (List.Mem.head _)

theorem lex_4_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 625), (Sat.Literal.neg 42), (Sat.Literal.pos 26)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 625), (Sat.Literal.pos 42), (Sat.Literal.neg 26)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 624), (Sat.Literal.neg 42), (Sat.Literal.neg 26), (Sat.Literal.pos 625)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 624), (Sat.Literal.pos 42), (Sat.Literal.pos 26), (Sat.Literal.pos 625)] :=
  (lex_4_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 625) = lexBefore s permutation4 41 := by
  exact (positive_lex_of_descriptor s 625 permutation4 42 (by rfl)).trans ((lex_skipped s permutation4 41 42 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation4 41) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation4 41 by rw [image4_eq]; rfl))

theorem lex_4_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 626) (Sat.Literal.pos 625) (Sat.Literal.pos 41) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation4 41 (assignment s)
    (Sat.Literal.pos 626) (Sat.Literal.pos 625) (Sat.Literal.pos 41) (Sat.Literal.pos 25) (positive_of_descriptor s 626 (.lex permutation4 41) (by rfl)) (lex_4_41_prefix s) (positive_select s 41) (lex_4_41_image s)

theorem lex_4_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 625), (Sat.Literal.pos 41), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation4 41 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 625) (Sat.Literal.pos 41) (Sat.Literal.pos 25) (lex_4_41_prefix s) (positive_select s 41) (lex_4_41_image s)

theorem lex_4_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 626), (Sat.Literal.pos 625)] :=
  (lex_4_41_gate s).prop _ (List.Mem.head _)

theorem lex_4_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 626), (Sat.Literal.neg 41), (Sat.Literal.pos 25)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 626), (Sat.Literal.pos 41), (Sat.Literal.neg 25)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 625), (Sat.Literal.neg 41), (Sat.Literal.neg 25), (Sat.Literal.pos 626)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 625), (Sat.Literal.pos 41), (Sat.Literal.pos 25), (Sat.Literal.pos 626)] :=
  (lex_4_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 626) = lexBefore s permutation4 40 := by
  exact (positive_lex_of_descriptor s 626 permutation4 41 (by rfl)).trans ((lex_skipped s permutation4 40 41 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation4 40) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 64) = permuteMask permutation4 40 by rw [image4_eq]; rfl))

theorem lex_4_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 627) (Sat.Literal.pos 626) (Sat.Literal.pos 40) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation4 40 (assignment s)
    (Sat.Literal.pos 627) (Sat.Literal.pos 626) (Sat.Literal.pos 40) (Sat.Literal.pos 24) (positive_of_descriptor s 627 (.lex permutation4 40) (by rfl)) (lex_4_40_prefix s) (positive_select s 40) (lex_4_40_image s)

theorem lex_4_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 626), (Sat.Literal.pos 40), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation4 40 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 626) (Sat.Literal.pos 40) (Sat.Literal.pos 24) (lex_4_40_prefix s) (positive_select s 40) (lex_4_40_image s)

theorem lex_4_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 627), (Sat.Literal.pos 626)] :=
  (lex_4_40_gate s).prop _ (List.Mem.head _)

theorem lex_4_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 627), (Sat.Literal.neg 40), (Sat.Literal.pos 24)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 627), (Sat.Literal.pos 40), (Sat.Literal.neg 24)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 626), (Sat.Literal.neg 40), (Sat.Literal.neg 24), (Sat.Literal.pos 627)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 626), (Sat.Literal.pos 40), (Sat.Literal.pos 24), (Sat.Literal.pos 627)] :=
  (lex_4_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_39_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 627) = lexBefore s permutation4 39 := by
  exact (positive_lex_of_descriptor s 627 permutation4 40 (by rfl)).trans ((lex_skipped s permutation4 39 40 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_39_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation4 39) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation4 39 by rw [image4_eq]; rfl))

theorem lex_4_39_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 628) (Sat.Literal.pos 627) (Sat.Literal.pos 39) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation4 39 (assignment s)
    (Sat.Literal.pos 628) (Sat.Literal.pos 627) (Sat.Literal.pos 39) (Sat.Literal.pos 23) (positive_of_descriptor s 628 (.lex permutation4 39) (by rfl)) (lex_4_39_prefix s) (positive_select s 39) (lex_4_39_image s)

theorem lex_4_39_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 627), (Sat.Literal.pos 39), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation4 39 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 627) (Sat.Literal.pos 39) (Sat.Literal.pos 23) (lex_4_39_prefix s) (positive_select s 39) (lex_4_39_image s)

theorem lex_4_39_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 628), (Sat.Literal.pos 627)] :=
  (lex_4_39_gate s).prop _ (List.Mem.head _)

theorem lex_4_39_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 628), (Sat.Literal.neg 39), (Sat.Literal.pos 23)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_39_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 628), (Sat.Literal.pos 39), (Sat.Literal.neg 23)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_39_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 627), (Sat.Literal.neg 39), (Sat.Literal.neg 23), (Sat.Literal.pos 628)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_39_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 627), (Sat.Literal.pos 39), (Sat.Literal.pos 23), (Sat.Literal.pos 628)] :=
  (lex_4_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 628) = lexBefore s permutation4 38 := by
  exact (positive_lex_of_descriptor s 628 permutation4 39 (by rfl)).trans ((lex_skipped s permutation4 38 39 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation4 38) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 64) = permuteMask permutation4 38 by rw [image4_eq]; rfl))

theorem lex_4_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 629) (Sat.Literal.pos 628) (Sat.Literal.pos 38) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation4 38 (assignment s)
    (Sat.Literal.pos 629) (Sat.Literal.pos 628) (Sat.Literal.pos 38) (Sat.Literal.pos 22) (positive_of_descriptor s 629 (.lex permutation4 38) (by rfl)) (lex_4_38_prefix s) (positive_select s 38) (lex_4_38_image s)

theorem lex_4_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 628), (Sat.Literal.pos 38), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation4 38 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 628) (Sat.Literal.pos 38) (Sat.Literal.pos 22) (lex_4_38_prefix s) (positive_select s 38) (lex_4_38_image s)

theorem lex_4_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 629), (Sat.Literal.pos 628)] :=
  (lex_4_38_gate s).prop _ (List.Mem.head _)

theorem lex_4_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 629), (Sat.Literal.neg 38), (Sat.Literal.pos 22)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 629), (Sat.Literal.pos 38), (Sat.Literal.neg 22)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 628), (Sat.Literal.neg 38), (Sat.Literal.neg 22), (Sat.Literal.pos 629)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 628), (Sat.Literal.pos 38), (Sat.Literal.pos 22), (Sat.Literal.pos 629)] :=
  (lex_4_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 629) = lexBefore s permutation4 37 := by
  exact (positive_lex_of_descriptor s 629 permutation4 38 (by rfl)).trans ((lex_skipped s permutation4 37 38 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation4 37) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation4 37 by rw [image4_eq]; rfl))

theorem lex_4_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 630) (Sat.Literal.pos 629) (Sat.Literal.pos 37) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation4 37 (assignment s)
    (Sat.Literal.pos 630) (Sat.Literal.pos 629) (Sat.Literal.pos 37) (Sat.Literal.pos 21) (positive_of_descriptor s 630 (.lex permutation4 37) (by rfl)) (lex_4_37_prefix s) (positive_select s 37) (lex_4_37_image s)

theorem lex_4_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 629), (Sat.Literal.pos 37), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation4 37 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 629) (Sat.Literal.pos 37) (Sat.Literal.pos 21) (lex_4_37_prefix s) (positive_select s 37) (lex_4_37_image s)

theorem lex_4_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 630), (Sat.Literal.pos 629)] :=
  (lex_4_37_gate s).prop _ (List.Mem.head _)

theorem lex_4_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 630), (Sat.Literal.neg 37), (Sat.Literal.pos 21)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 630), (Sat.Literal.pos 37), (Sat.Literal.neg 21)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 629), (Sat.Literal.neg 37), (Sat.Literal.neg 21), (Sat.Literal.pos 630)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 629), (Sat.Literal.pos 37), (Sat.Literal.pos 21), (Sat.Literal.pos 630)] :=
  (lex_4_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_36_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 630) = lexBefore s permutation4 36 := by
  exact (positive_lex_of_descriptor s 630 permutation4 37 (by rfl)).trans ((lex_skipped s permutation4 36 37 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_36_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation4 36) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 64) = permuteMask permutation4 36 by rw [image4_eq]; rfl))

theorem lex_4_36_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 631) (Sat.Literal.pos 630) (Sat.Literal.pos 36) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation4 36 (assignment s)
    (Sat.Literal.pos 631) (Sat.Literal.pos 630) (Sat.Literal.pos 36) (Sat.Literal.pos 20) (positive_of_descriptor s 631 (.lex permutation4 36) (by rfl)) (lex_4_36_prefix s) (positive_select s 36) (lex_4_36_image s)

theorem lex_4_36_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 630), (Sat.Literal.pos 36), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation4 36 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 630) (Sat.Literal.pos 36) (Sat.Literal.pos 20) (lex_4_36_prefix s) (positive_select s 36) (lex_4_36_image s)

theorem lex_4_36_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 631), (Sat.Literal.pos 630)] :=
  (lex_4_36_gate s).prop _ (List.Mem.head _)

theorem lex_4_36_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 631), (Sat.Literal.neg 36), (Sat.Literal.pos 20)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_36_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 631), (Sat.Literal.pos 36), (Sat.Literal.neg 20)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_36_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 630), (Sat.Literal.neg 36), (Sat.Literal.neg 20), (Sat.Literal.pos 631)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_36_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 630), (Sat.Literal.pos 36), (Sat.Literal.pos 20), (Sat.Literal.pos 631)] :=
  (lex_4_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_35_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 631) = lexBefore s permutation4 35 := by
  exact (positive_lex_of_descriptor s 631 permutation4 36 (by rfl)).trans ((lex_skipped s permutation4 35 36 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_35_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation4 35) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation4 35 by rw [image4_eq]; rfl))

theorem lex_4_35_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 632) (Sat.Literal.pos 631) (Sat.Literal.pos 35) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation4 35 (assignment s)
    (Sat.Literal.pos 632) (Sat.Literal.pos 631) (Sat.Literal.pos 35) (Sat.Literal.pos 19) (positive_of_descriptor s 632 (.lex permutation4 35) (by rfl)) (lex_4_35_prefix s) (positive_select s 35) (lex_4_35_image s)

theorem lex_4_35_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 631), (Sat.Literal.pos 35), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation4 35 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 631) (Sat.Literal.pos 35) (Sat.Literal.pos 19) (lex_4_35_prefix s) (positive_select s 35) (lex_4_35_image s)

theorem lex_4_35_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 632), (Sat.Literal.pos 631)] :=
  (lex_4_35_gate s).prop _ (List.Mem.head _)

theorem lex_4_35_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 632), (Sat.Literal.neg 35), (Sat.Literal.pos 19)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_35_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 632), (Sat.Literal.pos 35), (Sat.Literal.neg 19)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_35_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 631), (Sat.Literal.neg 35), (Sat.Literal.neg 19), (Sat.Literal.pos 632)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_35_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 631), (Sat.Literal.pos 35), (Sat.Literal.pos 19), (Sat.Literal.pos 632)] :=
  (lex_4_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 632) = lexBefore s permutation4 34 := by
  exact (positive_lex_of_descriptor s 632 permutation4 35 (by rfl)).trans ((lex_skipped s permutation4 34 35 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation4 34) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 64) = permuteMask permutation4 34 by rw [image4_eq]; rfl))

theorem lex_4_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 633) (Sat.Literal.pos 632) (Sat.Literal.pos 34) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation4 34 (assignment s)
    (Sat.Literal.pos 633) (Sat.Literal.pos 632) (Sat.Literal.pos 34) (Sat.Literal.pos 18) (positive_of_descriptor s 633 (.lex permutation4 34) (by rfl)) (lex_4_34_prefix s) (positive_select s 34) (lex_4_34_image s)

theorem lex_4_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 632), (Sat.Literal.pos 34), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation4 34 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 632) (Sat.Literal.pos 34) (Sat.Literal.pos 18) (lex_4_34_prefix s) (positive_select s 34) (lex_4_34_image s)

theorem lex_4_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 633), (Sat.Literal.pos 632)] :=
  (lex_4_34_gate s).prop _ (List.Mem.head _)

theorem lex_4_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 633), (Sat.Literal.neg 34), (Sat.Literal.pos 18)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 633), (Sat.Literal.pos 34), (Sat.Literal.neg 18)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 632), (Sat.Literal.neg 34), (Sat.Literal.neg 18), (Sat.Literal.pos 633)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 632), (Sat.Literal.pos 34), (Sat.Literal.pos 18), (Sat.Literal.pos 633)] :=
  (lex_4_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_33_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 633) = lexBefore s permutation4 33 := by
  exact (positive_lex_of_descriptor s 633 permutation4 34 (by rfl)).trans ((lex_skipped s permutation4 33 34 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_33_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation4 33) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation4 33 by rw [image4_eq]; rfl))

theorem lex_4_33_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 634) (Sat.Literal.pos 633) (Sat.Literal.pos 33) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation4 33 (assignment s)
    (Sat.Literal.pos 634) (Sat.Literal.pos 633) (Sat.Literal.pos 33) (Sat.Literal.pos 17) (positive_of_descriptor s 634 (.lex permutation4 33) (by rfl)) (lex_4_33_prefix s) (positive_select s 33) (lex_4_33_image s)

theorem lex_4_33_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 633), (Sat.Literal.pos 33), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation4 33 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 633) (Sat.Literal.pos 33) (Sat.Literal.pos 17) (lex_4_33_prefix s) (positive_select s 33) (lex_4_33_image s)

theorem lex_4_33_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 634), (Sat.Literal.pos 633)] :=
  (lex_4_33_gate s).prop _ (List.Mem.head _)

theorem lex_4_33_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 634), (Sat.Literal.neg 33), (Sat.Literal.pos 17)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_33_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 634), (Sat.Literal.pos 33), (Sat.Literal.neg 17)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_33_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 633), (Sat.Literal.neg 33), (Sat.Literal.neg 17), (Sat.Literal.pos 634)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_33_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 633), (Sat.Literal.pos 33), (Sat.Literal.pos 17), (Sat.Literal.pos 634)] :=
  (lex_4_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_32_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 634) = lexBefore s permutation4 32 := by
  exact (positive_lex_of_descriptor s 634 permutation4 33 (by rfl)).trans ((lex_skipped s permutation4 32 33 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_32_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation4 32) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 64) = permuteMask permutation4 32 by rw [image4_eq]; rfl))

theorem lex_4_32_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 635) (Sat.Literal.pos 634) (Sat.Literal.pos 32) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation4 32 (assignment s)
    (Sat.Literal.pos 635) (Sat.Literal.pos 634) (Sat.Literal.pos 32) (Sat.Literal.pos 16) (positive_of_descriptor s 635 (.lex permutation4 32) (by rfl)) (lex_4_32_prefix s) (positive_select s 32) (lex_4_32_image s)

theorem lex_4_32_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 634), (Sat.Literal.pos 32), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation4 32 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 634) (Sat.Literal.pos 32) (Sat.Literal.pos 16) (lex_4_32_prefix s) (positive_select s 32) (lex_4_32_image s)

theorem lex_4_32_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 635), (Sat.Literal.pos 634)] :=
  (lex_4_32_gate s).prop _ (List.Mem.head _)

theorem lex_4_32_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 635), (Sat.Literal.neg 32), (Sat.Literal.pos 16)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_32_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 635), (Sat.Literal.pos 32), (Sat.Literal.neg 16)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_32_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 634), (Sat.Literal.neg 32), (Sat.Literal.neg 16), (Sat.Literal.pos 635)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_32_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 634), (Sat.Literal.pos 32), (Sat.Literal.pos 16), (Sat.Literal.pos 635)] :=
  (lex_4_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_31_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 635) = lexBefore s permutation4 31 := by
  exact (positive_lex_of_descriptor s 635 permutation4 32 (by rfl)).trans ((lex_skipped s permutation4 31 32 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_31_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation4 31) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 64) = permuteMask permutation4 31 by rw [image4_eq]; rfl))

theorem lex_4_31_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 636) (Sat.Literal.pos 635) (Sat.Literal.pos 31) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation4 31 (assignment s)
    (Sat.Literal.pos 636) (Sat.Literal.pos 635) (Sat.Literal.pos 31) (Sat.Literal.pos 47) (positive_of_descriptor s 636 (.lex permutation4 31) (by rfl)) (lex_4_31_prefix s) (positive_select s 31) (lex_4_31_image s)

theorem lex_4_31_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 635), (Sat.Literal.pos 31), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation4 31 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 635) (Sat.Literal.pos 31) (Sat.Literal.pos 47) (lex_4_31_prefix s) (positive_select s 31) (lex_4_31_image s)

theorem lex_4_31_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 636), (Sat.Literal.pos 635)] :=
  (lex_4_31_gate s).prop _ (List.Mem.head _)

theorem lex_4_31_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 636), (Sat.Literal.neg 31), (Sat.Literal.pos 47)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_31_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 636), (Sat.Literal.pos 31), (Sat.Literal.neg 47)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_31_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 635), (Sat.Literal.neg 31), (Sat.Literal.neg 47), (Sat.Literal.pos 636)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_31_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 635), (Sat.Literal.pos 31), (Sat.Literal.pos 47), (Sat.Literal.pos 636)] :=
  (lex_4_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_30_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 636) = lexBefore s permutation4 30 := by
  exact (positive_lex_of_descriptor s 636 permutation4 31 (by rfl)).trans ((lex_skipped s permutation4 30 31 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_30_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation4 30) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation4 30 by rw [image4_eq]; rfl))

theorem lex_4_30_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 637) (Sat.Literal.pos 636) (Sat.Literal.pos 30) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation4 30 (assignment s)
    (Sat.Literal.pos 637) (Sat.Literal.pos 636) (Sat.Literal.pos 30) (Sat.Literal.pos 46) (positive_of_descriptor s 637 (.lex permutation4 30) (by rfl)) (lex_4_30_prefix s) (positive_select s 30) (lex_4_30_image s)

theorem lex_4_30_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 636), (Sat.Literal.pos 30), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation4 30 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 636) (Sat.Literal.pos 30) (Sat.Literal.pos 46) (lex_4_30_prefix s) (positive_select s 30) (lex_4_30_image s)

theorem lex_4_30_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 637), (Sat.Literal.pos 636)] :=
  (lex_4_30_gate s).prop _ (List.Mem.head _)

theorem lex_4_30_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 637), (Sat.Literal.neg 30), (Sat.Literal.pos 46)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_30_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 637), (Sat.Literal.pos 30), (Sat.Literal.neg 46)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_30_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 636), (Sat.Literal.neg 30), (Sat.Literal.neg 46), (Sat.Literal.pos 637)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_30_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 636), (Sat.Literal.pos 30), (Sat.Literal.pos 46), (Sat.Literal.pos 637)] :=
  (lex_4_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 637) = lexBefore s permutation4 29 := by
  exact (positive_lex_of_descriptor s 637 permutation4 30 (by rfl)).trans ((lex_skipped s permutation4 29 30 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation4 29) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation4 29 by rw [image4_eq]; rfl))

theorem lex_4_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 638) (Sat.Literal.pos 637) (Sat.Literal.pos 29) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation4 29 (assignment s)
    (Sat.Literal.pos 638) (Sat.Literal.pos 637) (Sat.Literal.pos 29) (Sat.Literal.pos 45) (positive_of_descriptor s 638 (.lex permutation4 29) (by rfl)) (lex_4_29_prefix s) (positive_select s 29) (lex_4_29_image s)

theorem lex_4_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 637), (Sat.Literal.pos 29), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation4 29 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 637) (Sat.Literal.pos 29) (Sat.Literal.pos 45) (lex_4_29_prefix s) (positive_select s 29) (lex_4_29_image s)

theorem lex_4_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 638), (Sat.Literal.pos 637)] :=
  (lex_4_29_gate s).prop _ (List.Mem.head _)

theorem lex_4_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 638), (Sat.Literal.neg 29), (Sat.Literal.pos 45)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 638), (Sat.Literal.pos 29), (Sat.Literal.neg 45)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 637), (Sat.Literal.neg 29), (Sat.Literal.neg 45), (Sat.Literal.pos 638)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 637), (Sat.Literal.pos 29), (Sat.Literal.pos 45), (Sat.Literal.pos 638)] :=
  (lex_4_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_28_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 638) = lexBefore s permutation4 28 := by
  exact (positive_lex_of_descriptor s 638 permutation4 29 (by rfl)).trans ((lex_skipped s permutation4 28 29 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_28_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation4 28) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 64) = permuteMask permutation4 28 by rw [image4_eq]; rfl))

theorem lex_4_28_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 639) (Sat.Literal.pos 638) (Sat.Literal.pos 28) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation4 28 (assignment s)
    (Sat.Literal.pos 639) (Sat.Literal.pos 638) (Sat.Literal.pos 28) (Sat.Literal.pos 44) (positive_of_descriptor s 639 (.lex permutation4 28) (by rfl)) (lex_4_28_prefix s) (positive_select s 28) (lex_4_28_image s)

theorem lex_4_28_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 638), (Sat.Literal.pos 28), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation4 28 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 638) (Sat.Literal.pos 28) (Sat.Literal.pos 44) (lex_4_28_prefix s) (positive_select s 28) (lex_4_28_image s)

theorem lex_4_28_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 639), (Sat.Literal.pos 638)] :=
  (lex_4_28_gate s).prop _ (List.Mem.head _)

theorem lex_4_28_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 639), (Sat.Literal.neg 28), (Sat.Literal.pos 44)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_28_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 639), (Sat.Literal.pos 28), (Sat.Literal.neg 44)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_28_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 638), (Sat.Literal.neg 28), (Sat.Literal.neg 44), (Sat.Literal.pos 639)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_28_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 638), (Sat.Literal.pos 28), (Sat.Literal.pos 44), (Sat.Literal.pos 639)] :=
  (lex_4_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_27_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 639) = lexBefore s permutation4 27 := by
  exact (positive_lex_of_descriptor s 639 permutation4 28 (by rfl)).trans ((lex_skipped s permutation4 27 28 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_27_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation4 27) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation4 27 by rw [image4_eq]; rfl))

theorem lex_4_27_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 640) (Sat.Literal.pos 639) (Sat.Literal.pos 27) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation4 27 (assignment s)
    (Sat.Literal.pos 640) (Sat.Literal.pos 639) (Sat.Literal.pos 27) (Sat.Literal.pos 43) (positive_of_descriptor s 640 (.lex permutation4 27) (by rfl)) (lex_4_27_prefix s) (positive_select s 27) (lex_4_27_image s)

theorem lex_4_27_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 639), (Sat.Literal.pos 27), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation4 27 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 639) (Sat.Literal.pos 27) (Sat.Literal.pos 43) (lex_4_27_prefix s) (positive_select s 27) (lex_4_27_image s)

theorem lex_4_27_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 640), (Sat.Literal.pos 639)] :=
  (lex_4_27_gate s).prop _ (List.Mem.head _)

theorem lex_4_27_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 640), (Sat.Literal.neg 27), (Sat.Literal.pos 43)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_27_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 640), (Sat.Literal.pos 27), (Sat.Literal.neg 43)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_27_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 639), (Sat.Literal.neg 27), (Sat.Literal.neg 43), (Sat.Literal.pos 640)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_27_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 639), (Sat.Literal.pos 27), (Sat.Literal.pos 43), (Sat.Literal.pos 640)] :=
  (lex_4_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 640) = lexBefore s permutation4 26 := by
  exact (positive_lex_of_descriptor s 640 permutation4 27 (by rfl)).trans ((lex_skipped s permutation4 26 27 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation4 26) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 64) = permuteMask permutation4 26 by rw [image4_eq]; rfl))

theorem lex_4_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 641) (Sat.Literal.pos 640) (Sat.Literal.pos 26) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation4 26 (assignment s)
    (Sat.Literal.pos 641) (Sat.Literal.pos 640) (Sat.Literal.pos 26) (Sat.Literal.pos 42) (positive_of_descriptor s 641 (.lex permutation4 26) (by rfl)) (lex_4_26_prefix s) (positive_select s 26) (lex_4_26_image s)

theorem lex_4_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 640), (Sat.Literal.pos 26), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation4 26 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 640) (Sat.Literal.pos 26) (Sat.Literal.pos 42) (lex_4_26_prefix s) (positive_select s 26) (lex_4_26_image s)

theorem lex_4_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 641), (Sat.Literal.pos 640)] :=
  (lex_4_26_gate s).prop _ (List.Mem.head _)

theorem lex_4_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 641), (Sat.Literal.neg 26), (Sat.Literal.pos 42)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 641), (Sat.Literal.pos 26), (Sat.Literal.neg 42)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 640), (Sat.Literal.neg 26), (Sat.Literal.neg 42), (Sat.Literal.pos 641)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 640), (Sat.Literal.pos 26), (Sat.Literal.pos 42), (Sat.Literal.pos 641)] :=
  (lex_4_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 641) = lexBefore s permutation4 25 := by
  exact (positive_lex_of_descriptor s 641 permutation4 26 (by rfl)).trans ((lex_skipped s permutation4 25 26 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation4 25) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation4 25 by rw [image4_eq]; rfl))

theorem lex_4_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 642) (Sat.Literal.pos 641) (Sat.Literal.pos 25) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation4 25 (assignment s)
    (Sat.Literal.pos 642) (Sat.Literal.pos 641) (Sat.Literal.pos 25) (Sat.Literal.pos 41) (positive_of_descriptor s 642 (.lex permutation4 25) (by rfl)) (lex_4_25_prefix s) (positive_select s 25) (lex_4_25_image s)

theorem lex_4_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 641), (Sat.Literal.pos 25), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation4 25 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 641) (Sat.Literal.pos 25) (Sat.Literal.pos 41) (lex_4_25_prefix s) (positive_select s 25) (lex_4_25_image s)

theorem lex_4_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 642), (Sat.Literal.pos 641)] :=
  (lex_4_25_gate s).prop _ (List.Mem.head _)

theorem lex_4_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 642), (Sat.Literal.neg 25), (Sat.Literal.pos 41)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 642), (Sat.Literal.pos 25), (Sat.Literal.neg 41)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 641), (Sat.Literal.neg 25), (Sat.Literal.neg 41), (Sat.Literal.pos 642)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 641), (Sat.Literal.pos 25), (Sat.Literal.pos 41), (Sat.Literal.pos 642)] :=
  (lex_4_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_24_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 642) = lexBefore s permutation4 24 := by
  exact (positive_lex_of_descriptor s 642 permutation4 25 (by rfl)).trans ((lex_skipped s permutation4 24 25 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_24_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation4 24) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 64) = permuteMask permutation4 24 by rw [image4_eq]; rfl))

theorem lex_4_24_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 643) (Sat.Literal.pos 642) (Sat.Literal.pos 24) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation4 24 (assignment s)
    (Sat.Literal.pos 643) (Sat.Literal.pos 642) (Sat.Literal.pos 24) (Sat.Literal.pos 40) (positive_of_descriptor s 643 (.lex permutation4 24) (by rfl)) (lex_4_24_prefix s) (positive_select s 24) (lex_4_24_image s)

theorem lex_4_24_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 642), (Sat.Literal.pos 24), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation4 24 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 642) (Sat.Literal.pos 24) (Sat.Literal.pos 40) (lex_4_24_prefix s) (positive_select s 24) (lex_4_24_image s)

theorem lex_4_24_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 643), (Sat.Literal.pos 642)] :=
  (lex_4_24_gate s).prop _ (List.Mem.head _)

theorem lex_4_24_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 643), (Sat.Literal.neg 24), (Sat.Literal.pos 40)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_24_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 643), (Sat.Literal.pos 24), (Sat.Literal.neg 40)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_24_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 642), (Sat.Literal.neg 24), (Sat.Literal.neg 40), (Sat.Literal.pos 643)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_24_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 642), (Sat.Literal.pos 24), (Sat.Literal.pos 40), (Sat.Literal.pos 643)] :=
  (lex_4_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 643) = lexBefore s permutation4 23 := by
  exact (positive_lex_of_descriptor s 643 permutation4 24 (by rfl)).trans ((lex_skipped s permutation4 23 24 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation4 23) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 64) = permuteMask permutation4 23 by rw [image4_eq]; rfl))

theorem lex_4_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 644) (Sat.Literal.pos 643) (Sat.Literal.pos 23) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation4 23 (assignment s)
    (Sat.Literal.pos 644) (Sat.Literal.pos 643) (Sat.Literal.pos 23) (Sat.Literal.pos 39) (positive_of_descriptor s 644 (.lex permutation4 23) (by rfl)) (lex_4_23_prefix s) (positive_select s 23) (lex_4_23_image s)

theorem lex_4_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 643), (Sat.Literal.pos 23), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation4 23 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 643) (Sat.Literal.pos 23) (Sat.Literal.pos 39) (lex_4_23_prefix s) (positive_select s 23) (lex_4_23_image s)

theorem lex_4_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 644), (Sat.Literal.pos 643)] :=
  (lex_4_23_gate s).prop _ (List.Mem.head _)

theorem lex_4_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 644), (Sat.Literal.neg 23), (Sat.Literal.pos 39)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 644), (Sat.Literal.pos 23), (Sat.Literal.neg 39)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 643), (Sat.Literal.neg 23), (Sat.Literal.neg 39), (Sat.Literal.pos 644)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 643), (Sat.Literal.pos 23), (Sat.Literal.pos 39), (Sat.Literal.pos 644)] :=
  (lex_4_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_22_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 644) = lexBefore s permutation4 22 := by
  exact (positive_lex_of_descriptor s 644 permutation4 23 (by rfl)).trans ((lex_skipped s permutation4 22 23 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_22_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation4 22) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 64) = permuteMask permutation4 22 by rw [image4_eq]; rfl))

theorem lex_4_22_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 645) (Sat.Literal.pos 644) (Sat.Literal.pos 22) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation4 22 (assignment s)
    (Sat.Literal.pos 645) (Sat.Literal.pos 644) (Sat.Literal.pos 22) (Sat.Literal.pos 38) (positive_of_descriptor s 645 (.lex permutation4 22) (by rfl)) (lex_4_22_prefix s) (positive_select s 22) (lex_4_22_image s)

theorem lex_4_22_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 644), (Sat.Literal.pos 22), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation4 22 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 644) (Sat.Literal.pos 22) (Sat.Literal.pos 38) (lex_4_22_prefix s) (positive_select s 22) (lex_4_22_image s)

theorem lex_4_22_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 645), (Sat.Literal.pos 644)] :=
  (lex_4_22_gate s).prop _ (List.Mem.head _)

theorem lex_4_22_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 645), (Sat.Literal.neg 22), (Sat.Literal.pos 38)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_22_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 645), (Sat.Literal.pos 22), (Sat.Literal.neg 38)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_22_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 644), (Sat.Literal.neg 22), (Sat.Literal.neg 38), (Sat.Literal.pos 645)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_22_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 644), (Sat.Literal.pos 22), (Sat.Literal.pos 38), (Sat.Literal.pos 645)] :=
  (lex_4_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_21_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 645) = lexBefore s permutation4 21 := by
  exact (positive_lex_of_descriptor s 645 permutation4 22 (by rfl)).trans ((lex_skipped s permutation4 21 22 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_21_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation4 21) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation4 21 by rw [image4_eq]; rfl))

theorem lex_4_21_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 646) (Sat.Literal.pos 645) (Sat.Literal.pos 21) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation4 21 (assignment s)
    (Sat.Literal.pos 646) (Sat.Literal.pos 645) (Sat.Literal.pos 21) (Sat.Literal.pos 37) (positive_of_descriptor s 646 (.lex permutation4 21) (by rfl)) (lex_4_21_prefix s) (positive_select s 21) (lex_4_21_image s)

theorem lex_4_21_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 645), (Sat.Literal.pos 21), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation4 21 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 645) (Sat.Literal.pos 21) (Sat.Literal.pos 37) (lex_4_21_prefix s) (positive_select s 21) (lex_4_21_image s)

theorem lex_4_21_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 646), (Sat.Literal.pos 645)] :=
  (lex_4_21_gate s).prop _ (List.Mem.head _)

theorem lex_4_21_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 646), (Sat.Literal.neg 21), (Sat.Literal.pos 37)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_21_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 646), (Sat.Literal.pos 21), (Sat.Literal.neg 37)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_21_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 645), (Sat.Literal.neg 21), (Sat.Literal.neg 37), (Sat.Literal.pos 646)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_21_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 645), (Sat.Literal.pos 21), (Sat.Literal.pos 37), (Sat.Literal.pos 646)] :=
  (lex_4_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_20_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 646) = lexBefore s permutation4 20 := by
  exact (positive_lex_of_descriptor s 646 permutation4 21 (by rfl)).trans ((lex_skipped s permutation4 20 21 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_20_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation4 20) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 64) = permuteMask permutation4 20 by rw [image4_eq]; rfl))

theorem lex_4_20_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 647) (Sat.Literal.pos 646) (Sat.Literal.pos 20) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation4 20 (assignment s)
    (Sat.Literal.pos 647) (Sat.Literal.pos 646) (Sat.Literal.pos 20) (Sat.Literal.pos 36) (positive_of_descriptor s 647 (.lex permutation4 20) (by rfl)) (lex_4_20_prefix s) (positive_select s 20) (lex_4_20_image s)

theorem lex_4_20_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 646), (Sat.Literal.pos 20), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation4 20 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 646) (Sat.Literal.pos 20) (Sat.Literal.pos 36) (lex_4_20_prefix s) (positive_select s 20) (lex_4_20_image s)

theorem lex_4_20_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 647), (Sat.Literal.pos 646)] :=
  (lex_4_20_gate s).prop _ (List.Mem.head _)

theorem lex_4_20_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 647), (Sat.Literal.neg 20), (Sat.Literal.pos 36)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_20_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 647), (Sat.Literal.pos 20), (Sat.Literal.neg 36)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_20_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 646), (Sat.Literal.neg 20), (Sat.Literal.neg 36), (Sat.Literal.pos 647)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_20_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 646), (Sat.Literal.pos 20), (Sat.Literal.pos 36), (Sat.Literal.pos 647)] :=
  (lex_4_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_19_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 647) = lexBefore s permutation4 19 := by
  exact (positive_lex_of_descriptor s 647 permutation4 20 (by rfl)).trans ((lex_skipped s permutation4 19 20 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_19_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation4 19) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 64) = permuteMask permutation4 19 by rw [image4_eq]; rfl))

theorem lex_4_19_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 648) (Sat.Literal.pos 647) (Sat.Literal.pos 19) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation4 19 (assignment s)
    (Sat.Literal.pos 648) (Sat.Literal.pos 647) (Sat.Literal.pos 19) (Sat.Literal.pos 35) (positive_of_descriptor s 648 (.lex permutation4 19) (by rfl)) (lex_4_19_prefix s) (positive_select s 19) (lex_4_19_image s)

theorem lex_4_19_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 647), (Sat.Literal.pos 19), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation4 19 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 647) (Sat.Literal.pos 19) (Sat.Literal.pos 35) (lex_4_19_prefix s) (positive_select s 19) (lex_4_19_image s)

theorem lex_4_19_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 648), (Sat.Literal.pos 647)] :=
  (lex_4_19_gate s).prop _ (List.Mem.head _)

theorem lex_4_19_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 648), (Sat.Literal.neg 19), (Sat.Literal.pos 35)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_19_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 648), (Sat.Literal.pos 19), (Sat.Literal.neg 35)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_19_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 647), (Sat.Literal.neg 19), (Sat.Literal.neg 35), (Sat.Literal.pos 648)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_19_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 647), (Sat.Literal.pos 19), (Sat.Literal.pos 35), (Sat.Literal.pos 648)] :=
  (lex_4_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_18_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 648) = lexBefore s permutation4 18 := by
  exact (positive_lex_of_descriptor s 648 permutation4 19 (by rfl)).trans ((lex_skipped s permutation4 18 19 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_18_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation4 18) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 64) = permuteMask permutation4 18 by rw [image4_eq]; rfl))

theorem lex_4_18_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 649) (Sat.Literal.pos 648) (Sat.Literal.pos 18) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation4 18 (assignment s)
    (Sat.Literal.pos 649) (Sat.Literal.pos 648) (Sat.Literal.pos 18) (Sat.Literal.pos 34) (positive_of_descriptor s 649 (.lex permutation4 18) (by rfl)) (lex_4_18_prefix s) (positive_select s 18) (lex_4_18_image s)

theorem lex_4_18_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 648), (Sat.Literal.pos 18), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation4 18 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 648) (Sat.Literal.pos 18) (Sat.Literal.pos 34) (lex_4_18_prefix s) (positive_select s 18) (lex_4_18_image s)

theorem lex_4_18_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 649), (Sat.Literal.pos 648)] :=
  (lex_4_18_gate s).prop _ (List.Mem.head _)

theorem lex_4_18_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 649), (Sat.Literal.neg 18), (Sat.Literal.pos 34)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_18_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 649), (Sat.Literal.pos 18), (Sat.Literal.neg 34)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_18_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 648), (Sat.Literal.neg 18), (Sat.Literal.neg 34), (Sat.Literal.pos 649)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_18_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 648), (Sat.Literal.pos 18), (Sat.Literal.pos 34), (Sat.Literal.pos 649)] :=
  (lex_4_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_17_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 649) = lexBefore s permutation4 17 := by
  exact (positive_lex_of_descriptor s 649 permutation4 18 (by rfl)).trans ((lex_skipped s permutation4 17 18 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_17_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation4 17) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 64) = permuteMask permutation4 17 by rw [image4_eq]; rfl))

theorem lex_4_17_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 650) (Sat.Literal.pos 649) (Sat.Literal.pos 17) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation4 17 (assignment s)
    (Sat.Literal.pos 650) (Sat.Literal.pos 649) (Sat.Literal.pos 17) (Sat.Literal.pos 33) (positive_of_descriptor s 650 (.lex permutation4 17) (by rfl)) (lex_4_17_prefix s) (positive_select s 17) (lex_4_17_image s)

theorem lex_4_17_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 649), (Sat.Literal.pos 17), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation4 17 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 649) (Sat.Literal.pos 17) (Sat.Literal.pos 33) (lex_4_17_prefix s) (positive_select s 17) (lex_4_17_image s)

theorem lex_4_17_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 650), (Sat.Literal.pos 649)] :=
  (lex_4_17_gate s).prop _ (List.Mem.head _)

theorem lex_4_17_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 650), (Sat.Literal.neg 17), (Sat.Literal.pos 33)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_17_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 650), (Sat.Literal.pos 17), (Sat.Literal.neg 33)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_17_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 649), (Sat.Literal.neg 17), (Sat.Literal.neg 33), (Sat.Literal.pos 650)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_17_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 649), (Sat.Literal.pos 17), (Sat.Literal.pos 33), (Sat.Literal.pos 650)] :=
  (lex_4_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_4_16_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 650) = lexBefore s permutation4 16 := by
  exact (positive_lex_of_descriptor s 650 permutation4 17 (by rfl)).trans ((lex_skipped s permutation4 16 17 (by decide) (by intro j hj hp; rw [image4_eq]; exact fixedOnRange_spec image4 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_4_16_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation4 16) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 64) = permuteMask permutation4 16 by rw [image4_eq]; rfl))

theorem lex_4_16_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 651) (Sat.Literal.pos 650) (Sat.Literal.pos 16) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation4 16 (assignment s)
    (Sat.Literal.pos 651) (Sat.Literal.pos 650) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (positive_of_descriptor s 651 (.lex permutation4 16) (by rfl)) (lex_4_16_prefix s) (positive_select s 16) (lex_4_16_image s)

theorem lex_4_16_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 650), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation4 16 (hmax permutation4) (assignment s)
    (Sat.Literal.pos 650) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (lex_4_16_prefix s) (positive_select s 16) (lex_4_16_image s)

theorem lex_4_16_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 651), (Sat.Literal.pos 650)] :=
  (lex_4_16_gate s).prop _ (List.Mem.head _)

theorem lex_4_16_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 651), (Sat.Literal.neg 16), (Sat.Literal.pos 32)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_4_16_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 651), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_4_16_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 650), (Sat.Literal.neg 16), (Sat.Literal.neg 32), (Sat.Literal.pos 651)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_4_16_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 650), (Sat.Literal.pos 16), (Sat.Literal.pos 32), (Sat.Literal.pos 651)] :=
  (lex_4_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_62_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 64) = lexBefore s permutation5 62 := by
  exact (negative_falsum s).trans ((lex_first s permutation5 62 (by intro j hj; rw [image5_eq]; exact fixedOnRange_spec image5 63 64 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_5_62_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation5 62) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 64) = permuteMask permutation5 62 by rw [image5_eq]; rfl))

theorem lex_5_62_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 652) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation5 62 (assignment s)
    (Sat.Literal.pos 652) (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 61) (positive_of_descriptor s 652 (.lex permutation5 62) (by rfl)) (lex_5_62_prefix s) (positive_select s 62) (lex_5_62_image s)

theorem lex_5_62_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation5 62 (hmax permutation5) (assignment s)
    (Sat.Literal.neg 64) (Sat.Literal.pos 62) (Sat.Literal.pos 61) (lex_5_62_prefix s) (positive_select s 62) (lex_5_62_image s)

theorem lex_5_62_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 652), (Sat.Literal.neg 64)] :=
  (lex_5_62_gate s).prop _ (List.Mem.head _)

theorem lex_5_62_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 652), (Sat.Literal.neg 62), (Sat.Literal.pos 61)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_62_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 652), (Sat.Literal.pos 62), (Sat.Literal.neg 61)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_62_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.neg 62), (Sat.Literal.neg 61), (Sat.Literal.pos 652)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_62_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 64), (Sat.Literal.pos 62), (Sat.Literal.pos 61), (Sat.Literal.pos 652)] :=
  (lex_5_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_61_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 652) = lexBefore s permutation5 61 := by
  exact (positive_lex_of_descriptor s 652 permutation5 62 (by rfl)).trans ((lex_skipped s permutation5 61 62 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_61_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation5 61) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 64) = permuteMask permutation5 61 by rw [image5_eq]; rfl))

theorem lex_5_61_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 653) (Sat.Literal.pos 652) (Sat.Literal.pos 61) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation5 61 (assignment s)
    (Sat.Literal.pos 653) (Sat.Literal.pos 652) (Sat.Literal.pos 61) (Sat.Literal.pos 59) (positive_of_descriptor s 653 (.lex permutation5 61) (by rfl)) (lex_5_61_prefix s) (positive_select s 61) (lex_5_61_image s)

theorem lex_5_61_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 652), (Sat.Literal.pos 61), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation5 61 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 652) (Sat.Literal.pos 61) (Sat.Literal.pos 59) (lex_5_61_prefix s) (positive_select s 61) (lex_5_61_image s)

theorem lex_5_61_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 653), (Sat.Literal.pos 652)] :=
  (lex_5_61_gate s).prop _ (List.Mem.head _)

theorem lex_5_61_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 653), (Sat.Literal.neg 61), (Sat.Literal.pos 59)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_61_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 653), (Sat.Literal.pos 61), (Sat.Literal.neg 59)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_61_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 652), (Sat.Literal.neg 61), (Sat.Literal.neg 59), (Sat.Literal.pos 653)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_61_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 652), (Sat.Literal.pos 61), (Sat.Literal.pos 59), (Sat.Literal.pos 653)] :=
  (lex_5_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_60_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 653) = lexBefore s permutation5 60 := by
  exact (positive_lex_of_descriptor s 653 permutation5 61 (by rfl)).trans ((lex_skipped s permutation5 60 61 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 61 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_60_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation5 60) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 64) = permuteMask permutation5 60 by rw [image5_eq]; rfl))

theorem lex_5_60_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 654) (Sat.Literal.pos 653) (Sat.Literal.pos 60) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation5 60 (assignment s)
    (Sat.Literal.pos 654) (Sat.Literal.pos 653) (Sat.Literal.pos 60) (Sat.Literal.pos 57) (positive_of_descriptor s 654 (.lex permutation5 60) (by rfl)) (lex_5_60_prefix s) (positive_select s 60) (lex_5_60_image s)

theorem lex_5_60_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 653), (Sat.Literal.pos 60), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation5 60 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 653) (Sat.Literal.pos 60) (Sat.Literal.pos 57) (lex_5_60_prefix s) (positive_select s 60) (lex_5_60_image s)

theorem lex_5_60_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 654), (Sat.Literal.pos 653)] :=
  (lex_5_60_gate s).prop _ (List.Mem.head _)

theorem lex_5_60_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 654), (Sat.Literal.neg 60), (Sat.Literal.pos 57)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_60_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 654), (Sat.Literal.pos 60), (Sat.Literal.neg 57)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_60_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 653), (Sat.Literal.neg 60), (Sat.Literal.neg 57), (Sat.Literal.pos 654)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_60_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 653), (Sat.Literal.pos 60), (Sat.Literal.pos 57), (Sat.Literal.pos 654)] :=
  (lex_5_60_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_59_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 654) = lexBefore s permutation5 59 := by
  exact (positive_lex_of_descriptor s 654 permutation5 60 (by rfl)).trans ((lex_skipped s permutation5 59 60 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 60 60 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_59_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation5 59) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 64) = permuteMask permutation5 59 by rw [image5_eq]; rfl))

theorem lex_5_59_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 655) (Sat.Literal.pos 654) (Sat.Literal.pos 59) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation5 59 (assignment s)
    (Sat.Literal.pos 655) (Sat.Literal.pos 654) (Sat.Literal.pos 59) (Sat.Literal.pos 55) (positive_of_descriptor s 655 (.lex permutation5 59) (by rfl)) (lex_5_59_prefix s) (positive_select s 59) (lex_5_59_image s)

theorem lex_5_59_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 654), (Sat.Literal.pos 59), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation5 59 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 654) (Sat.Literal.pos 59) (Sat.Literal.pos 55) (lex_5_59_prefix s) (positive_select s 59) (lex_5_59_image s)

theorem lex_5_59_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 655), (Sat.Literal.pos 654)] :=
  (lex_5_59_gate s).prop _ (List.Mem.head _)

theorem lex_5_59_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 655), (Sat.Literal.neg 59), (Sat.Literal.pos 55)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_59_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 655), (Sat.Literal.pos 59), (Sat.Literal.neg 55)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_59_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 654), (Sat.Literal.neg 59), (Sat.Literal.neg 55), (Sat.Literal.pos 655)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_59_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 654), (Sat.Literal.pos 59), (Sat.Literal.pos 55), (Sat.Literal.pos 655)] :=
  (lex_5_59_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_58_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 655) = lexBefore s permutation5 58 := by
  exact (positive_lex_of_descriptor s 655 permutation5 59 (by rfl)).trans ((lex_skipped s permutation5 58 59 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 59 59 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_58_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation5 58) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 64) = permuteMask permutation5 58 by rw [image5_eq]; rfl))

theorem lex_5_58_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 656) (Sat.Literal.pos 655) (Sat.Literal.pos 58) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation5 58 (assignment s)
    (Sat.Literal.pos 656) (Sat.Literal.pos 655) (Sat.Literal.pos 58) (Sat.Literal.pos 53) (positive_of_descriptor s 656 (.lex permutation5 58) (by rfl)) (lex_5_58_prefix s) (positive_select s 58) (lex_5_58_image s)

theorem lex_5_58_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 655), (Sat.Literal.pos 58), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation5 58 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 655) (Sat.Literal.pos 58) (Sat.Literal.pos 53) (lex_5_58_prefix s) (positive_select s 58) (lex_5_58_image s)

theorem lex_5_58_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 656), (Sat.Literal.pos 655)] :=
  (lex_5_58_gate s).prop _ (List.Mem.head _)

theorem lex_5_58_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 656), (Sat.Literal.neg 58), (Sat.Literal.pos 53)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_58_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 656), (Sat.Literal.pos 58), (Sat.Literal.neg 53)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_58_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 655), (Sat.Literal.neg 58), (Sat.Literal.neg 53), (Sat.Literal.pos 656)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_58_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 655), (Sat.Literal.pos 58), (Sat.Literal.pos 53), (Sat.Literal.pos 656)] :=
  (lex_5_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_57_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 656) = lexBefore s permutation5 57 := by
  exact (positive_lex_of_descriptor s 656 permutation5 58 (by rfl)).trans ((lex_skipped s permutation5 57 58 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_57_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation5 57) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 64) = permuteMask permutation5 57 by rw [image5_eq]; rfl))

theorem lex_5_57_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 657) (Sat.Literal.pos 656) (Sat.Literal.pos 57) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation5 57 (assignment s)
    (Sat.Literal.pos 657) (Sat.Literal.pos 656) (Sat.Literal.pos 57) (Sat.Literal.pos 51) (positive_of_descriptor s 657 (.lex permutation5 57) (by rfl)) (lex_5_57_prefix s) (positive_select s 57) (lex_5_57_image s)

theorem lex_5_57_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 656), (Sat.Literal.pos 57), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation5 57 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 656) (Sat.Literal.pos 57) (Sat.Literal.pos 51) (lex_5_57_prefix s) (positive_select s 57) (lex_5_57_image s)

theorem lex_5_57_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 657), (Sat.Literal.pos 656)] :=
  (lex_5_57_gate s).prop _ (List.Mem.head _)

theorem lex_5_57_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 657), (Sat.Literal.neg 57), (Sat.Literal.pos 51)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_57_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 657), (Sat.Literal.pos 57), (Sat.Literal.neg 51)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_57_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 656), (Sat.Literal.neg 57), (Sat.Literal.neg 51), (Sat.Literal.pos 657)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_57_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 656), (Sat.Literal.pos 57), (Sat.Literal.pos 51), (Sat.Literal.pos 657)] :=
  (lex_5_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_56_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 657) = lexBefore s permutation5 56 := by
  exact (positive_lex_of_descriptor s 657 permutation5 57 (by rfl)).trans ((lex_skipped s permutation5 56 57 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_56_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation5 56) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 64) = permuteMask permutation5 56 by rw [image5_eq]; rfl))

theorem lex_5_56_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 658) (Sat.Literal.pos 657) (Sat.Literal.pos 56) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation5 56 (assignment s)
    (Sat.Literal.pos 658) (Sat.Literal.pos 657) (Sat.Literal.pos 56) (Sat.Literal.pos 49) (positive_of_descriptor s 658 (.lex permutation5 56) (by rfl)) (lex_5_56_prefix s) (positive_select s 56) (lex_5_56_image s)

theorem lex_5_56_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 657), (Sat.Literal.pos 56), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation5 56 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 657) (Sat.Literal.pos 56) (Sat.Literal.pos 49) (lex_5_56_prefix s) (positive_select s 56) (lex_5_56_image s)

theorem lex_5_56_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 658), (Sat.Literal.pos 657)] :=
  (lex_5_56_gate s).prop _ (List.Mem.head _)

theorem lex_5_56_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 658), (Sat.Literal.neg 56), (Sat.Literal.pos 49)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_56_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 658), (Sat.Literal.pos 56), (Sat.Literal.neg 49)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_56_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 657), (Sat.Literal.neg 56), (Sat.Literal.neg 49), (Sat.Literal.pos 658)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_56_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 657), (Sat.Literal.pos 56), (Sat.Literal.pos 49), (Sat.Literal.pos 658)] :=
  (lex_5_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_55_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 658) = lexBefore s permutation5 55 := by
  exact (positive_lex_of_descriptor s 658 permutation5 56 (by rfl)).trans ((lex_skipped s permutation5 55 56 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_55_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation5 55) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 64) = permuteMask permutation5 55 by rw [image5_eq]; rfl))

theorem lex_5_55_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 659) (Sat.Literal.pos 658) (Sat.Literal.pos 55) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation5 55 (assignment s)
    (Sat.Literal.pos 659) (Sat.Literal.pos 658) (Sat.Literal.pos 55) (Sat.Literal.pos 47) (positive_of_descriptor s 659 (.lex permutation5 55) (by rfl)) (lex_5_55_prefix s) (positive_select s 55) (lex_5_55_image s)

theorem lex_5_55_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 658), (Sat.Literal.pos 55), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation5 55 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 658) (Sat.Literal.pos 55) (Sat.Literal.pos 47) (lex_5_55_prefix s) (positive_select s 55) (lex_5_55_image s)

theorem lex_5_55_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 659), (Sat.Literal.pos 658)] :=
  (lex_5_55_gate s).prop _ (List.Mem.head _)

theorem lex_5_55_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 659), (Sat.Literal.neg 55), (Sat.Literal.pos 47)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_55_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 659), (Sat.Literal.pos 55), (Sat.Literal.neg 47)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_55_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 658), (Sat.Literal.neg 55), (Sat.Literal.neg 47), (Sat.Literal.pos 659)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_55_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 658), (Sat.Literal.pos 55), (Sat.Literal.pos 47), (Sat.Literal.pos 659)] :=
  (lex_5_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_54_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 659) = lexBefore s permutation5 54 := by
  exact (positive_lex_of_descriptor s 659 permutation5 55 (by rfl)).trans ((lex_skipped s permutation5 54 55 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_54_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation5 54) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 64) = permuteMask permutation5 54 by rw [image5_eq]; rfl))

theorem lex_5_54_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 660) (Sat.Literal.pos 659) (Sat.Literal.pos 54) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation5 54 (assignment s)
    (Sat.Literal.pos 660) (Sat.Literal.pos 659) (Sat.Literal.pos 54) (Sat.Literal.pos 45) (positive_of_descriptor s 660 (.lex permutation5 54) (by rfl)) (lex_5_54_prefix s) (positive_select s 54) (lex_5_54_image s)

theorem lex_5_54_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 659), (Sat.Literal.pos 54), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation5 54 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 659) (Sat.Literal.pos 54) (Sat.Literal.pos 45) (lex_5_54_prefix s) (positive_select s 54) (lex_5_54_image s)

theorem lex_5_54_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 660), (Sat.Literal.pos 659)] :=
  (lex_5_54_gate s).prop _ (List.Mem.head _)

theorem lex_5_54_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 660), (Sat.Literal.neg 54), (Sat.Literal.pos 45)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_54_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 660), (Sat.Literal.pos 54), (Sat.Literal.neg 45)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_54_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 659), (Sat.Literal.neg 54), (Sat.Literal.neg 45), (Sat.Literal.pos 660)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_54_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 659), (Sat.Literal.pos 54), (Sat.Literal.pos 45), (Sat.Literal.pos 660)] :=
  (lex_5_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_53_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 660) = lexBefore s permutation5 53 := by
  exact (positive_lex_of_descriptor s 660 permutation5 54 (by rfl)).trans ((lex_skipped s permutation5 53 54 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_53_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 43) = s (permuteMask permutation5 53) := by
  exact (positive_select s 43).trans (congrArg s (show (43 : Fin 64) = permuteMask permutation5 53 by rw [image5_eq]; rfl))

theorem lex_5_53_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 661) (Sat.Literal.pos 660) (Sat.Literal.pos 53) (Sat.Literal.pos 43)) := by
  exact equality_gate s permutation5 53 (assignment s)
    (Sat.Literal.pos 661) (Sat.Literal.pos 660) (Sat.Literal.pos 53) (Sat.Literal.pos 43) (positive_of_descriptor s 661 (.lex permutation5 53) (by rfl)) (lex_5_53_prefix s) (positive_select s 53) (lex_5_53_image s)

theorem lex_5_53_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 660), (Sat.Literal.pos 53), (Sat.Literal.neg 43)] := by
  exact comparison_gate s permutation5 53 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 660) (Sat.Literal.pos 53) (Sat.Literal.pos 43) (lex_5_53_prefix s) (positive_select s 53) (lex_5_53_image s)

theorem lex_5_53_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 661), (Sat.Literal.pos 660)] :=
  (lex_5_53_gate s).prop _ (List.Mem.head _)

theorem lex_5_53_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 661), (Sat.Literal.neg 53), (Sat.Literal.pos 43)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_53_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 661), (Sat.Literal.pos 53), (Sat.Literal.neg 43)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_53_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 660), (Sat.Literal.neg 53), (Sat.Literal.neg 43), (Sat.Literal.pos 661)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_53_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 660), (Sat.Literal.pos 53), (Sat.Literal.pos 43), (Sat.Literal.pos 661)] :=
  (lex_5_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_52_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 661) = lexBefore s permutation5 52 := by
  exact (positive_lex_of_descriptor s 661 permutation5 53 (by rfl)).trans ((lex_skipped s permutation5 52 53 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_52_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation5 52) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 64) = permuteMask permutation5 52 by rw [image5_eq]; rfl))

theorem lex_5_52_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 662) (Sat.Literal.pos 661) (Sat.Literal.pos 52) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation5 52 (assignment s)
    (Sat.Literal.pos 662) (Sat.Literal.pos 661) (Sat.Literal.pos 52) (Sat.Literal.pos 41) (positive_of_descriptor s 662 (.lex permutation5 52) (by rfl)) (lex_5_52_prefix s) (positive_select s 52) (lex_5_52_image s)

theorem lex_5_52_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 661), (Sat.Literal.pos 52), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation5 52 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 661) (Sat.Literal.pos 52) (Sat.Literal.pos 41) (lex_5_52_prefix s) (positive_select s 52) (lex_5_52_image s)

theorem lex_5_52_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 662), (Sat.Literal.pos 661)] :=
  (lex_5_52_gate s).prop _ (List.Mem.head _)

theorem lex_5_52_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 662), (Sat.Literal.neg 52), (Sat.Literal.pos 41)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_52_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 662), (Sat.Literal.pos 52), (Sat.Literal.neg 41)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_52_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 661), (Sat.Literal.neg 52), (Sat.Literal.neg 41), (Sat.Literal.pos 662)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_52_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 661), (Sat.Literal.pos 52), (Sat.Literal.pos 41), (Sat.Literal.pos 662)] :=
  (lex_5_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_51_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 662) = lexBefore s permutation5 51 := by
  exact (positive_lex_of_descriptor s 662 permutation5 52 (by rfl)).trans ((lex_skipped s permutation5 51 52 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_51_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation5 51) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 64) = permuteMask permutation5 51 by rw [image5_eq]; rfl))

theorem lex_5_51_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 663) (Sat.Literal.pos 662) (Sat.Literal.pos 51) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation5 51 (assignment s)
    (Sat.Literal.pos 663) (Sat.Literal.pos 662) (Sat.Literal.pos 51) (Sat.Literal.pos 39) (positive_of_descriptor s 663 (.lex permutation5 51) (by rfl)) (lex_5_51_prefix s) (positive_select s 51) (lex_5_51_image s)

theorem lex_5_51_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 662), (Sat.Literal.pos 51), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation5 51 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 662) (Sat.Literal.pos 51) (Sat.Literal.pos 39) (lex_5_51_prefix s) (positive_select s 51) (lex_5_51_image s)

theorem lex_5_51_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 663), (Sat.Literal.pos 662)] :=
  (lex_5_51_gate s).prop _ (List.Mem.head _)

theorem lex_5_51_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 663), (Sat.Literal.neg 51), (Sat.Literal.pos 39)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_51_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 663), (Sat.Literal.pos 51), (Sat.Literal.neg 39)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_51_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 662), (Sat.Literal.neg 51), (Sat.Literal.neg 39), (Sat.Literal.pos 663)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_51_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 662), (Sat.Literal.pos 51), (Sat.Literal.pos 39), (Sat.Literal.pos 663)] :=
  (lex_5_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_50_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 663) = lexBefore s permutation5 50 := by
  exact (positive_lex_of_descriptor s 663 permutation5 51 (by rfl)).trans ((lex_skipped s permutation5 50 51 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_50_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation5 50) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 64) = permuteMask permutation5 50 by rw [image5_eq]; rfl))

theorem lex_5_50_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 664) (Sat.Literal.pos 663) (Sat.Literal.pos 50) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation5 50 (assignment s)
    (Sat.Literal.pos 664) (Sat.Literal.pos 663) (Sat.Literal.pos 50) (Sat.Literal.pos 37) (positive_of_descriptor s 664 (.lex permutation5 50) (by rfl)) (lex_5_50_prefix s) (positive_select s 50) (lex_5_50_image s)

theorem lex_5_50_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 663), (Sat.Literal.pos 50), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation5 50 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 663) (Sat.Literal.pos 50) (Sat.Literal.pos 37) (lex_5_50_prefix s) (positive_select s 50) (lex_5_50_image s)

theorem lex_5_50_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 664), (Sat.Literal.pos 663)] :=
  (lex_5_50_gate s).prop _ (List.Mem.head _)

theorem lex_5_50_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 664), (Sat.Literal.neg 50), (Sat.Literal.pos 37)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_50_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 664), (Sat.Literal.pos 50), (Sat.Literal.neg 37)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_50_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 663), (Sat.Literal.neg 50), (Sat.Literal.neg 37), (Sat.Literal.pos 664)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_50_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 663), (Sat.Literal.pos 50), (Sat.Literal.pos 37), (Sat.Literal.pos 664)] :=
  (lex_5_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_49_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 664) = lexBefore s permutation5 49 := by
  exact (positive_lex_of_descriptor s 664 permutation5 50 (by rfl)).trans ((lex_skipped s permutation5 49 50 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_49_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation5 49) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 64) = permuteMask permutation5 49 by rw [image5_eq]; rfl))

theorem lex_5_49_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 665) (Sat.Literal.pos 664) (Sat.Literal.pos 49) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation5 49 (assignment s)
    (Sat.Literal.pos 665) (Sat.Literal.pos 664) (Sat.Literal.pos 49) (Sat.Literal.pos 35) (positive_of_descriptor s 665 (.lex permutation5 49) (by rfl)) (lex_5_49_prefix s) (positive_select s 49) (lex_5_49_image s)

theorem lex_5_49_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 664), (Sat.Literal.pos 49), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation5 49 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 664) (Sat.Literal.pos 49) (Sat.Literal.pos 35) (lex_5_49_prefix s) (positive_select s 49) (lex_5_49_image s)

theorem lex_5_49_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 665), (Sat.Literal.pos 664)] :=
  (lex_5_49_gate s).prop _ (List.Mem.head _)

theorem lex_5_49_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 665), (Sat.Literal.neg 49), (Sat.Literal.pos 35)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_49_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 665), (Sat.Literal.pos 49), (Sat.Literal.neg 35)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_49_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 664), (Sat.Literal.neg 49), (Sat.Literal.neg 35), (Sat.Literal.pos 665)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_49_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 664), (Sat.Literal.pos 49), (Sat.Literal.pos 35), (Sat.Literal.pos 665)] :=
  (lex_5_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_48_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 665) = lexBefore s permutation5 48 := by
  exact (positive_lex_of_descriptor s 665 permutation5 49 (by rfl)).trans ((lex_skipped s permutation5 48 49 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_48_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation5 48) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 64) = permuteMask permutation5 48 by rw [image5_eq]; rfl))

theorem lex_5_48_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 666) (Sat.Literal.pos 665) (Sat.Literal.pos 48) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation5 48 (assignment s)
    (Sat.Literal.pos 666) (Sat.Literal.pos 665) (Sat.Literal.pos 48) (Sat.Literal.pos 33) (positive_of_descriptor s 666 (.lex permutation5 48) (by rfl)) (lex_5_48_prefix s) (positive_select s 48) (lex_5_48_image s)

theorem lex_5_48_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 665), (Sat.Literal.pos 48), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation5 48 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 665) (Sat.Literal.pos 48) (Sat.Literal.pos 33) (lex_5_48_prefix s) (positive_select s 48) (lex_5_48_image s)

theorem lex_5_48_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 666), (Sat.Literal.pos 665)] :=
  (lex_5_48_gate s).prop _ (List.Mem.head _)

theorem lex_5_48_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 666), (Sat.Literal.neg 48), (Sat.Literal.pos 33)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_48_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 666), (Sat.Literal.pos 48), (Sat.Literal.neg 33)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_48_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 665), (Sat.Literal.neg 48), (Sat.Literal.neg 33), (Sat.Literal.pos 666)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_48_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 665), (Sat.Literal.pos 48), (Sat.Literal.pos 33), (Sat.Literal.pos 666)] :=
  (lex_5_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_47_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 666) = lexBefore s permutation5 47 := by
  exact (positive_lex_of_descriptor s 666 permutation5 48 (by rfl)).trans ((lex_skipped s permutation5 47 48 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_47_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation5 47) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 64) = permuteMask permutation5 47 by rw [image5_eq]; rfl))

theorem lex_5_47_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 667) (Sat.Literal.pos 666) (Sat.Literal.pos 47) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation5 47 (assignment s)
    (Sat.Literal.pos 667) (Sat.Literal.pos 666) (Sat.Literal.pos 47) (Sat.Literal.pos 31) (positive_of_descriptor s 667 (.lex permutation5 47) (by rfl)) (lex_5_47_prefix s) (positive_select s 47) (lex_5_47_image s)

theorem lex_5_47_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 666), (Sat.Literal.pos 47), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation5 47 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 666) (Sat.Literal.pos 47) (Sat.Literal.pos 31) (lex_5_47_prefix s) (positive_select s 47) (lex_5_47_image s)

theorem lex_5_47_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 667), (Sat.Literal.pos 666)] :=
  (lex_5_47_gate s).prop _ (List.Mem.head _)

theorem lex_5_47_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 667), (Sat.Literal.neg 47), (Sat.Literal.pos 31)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_47_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 667), (Sat.Literal.pos 47), (Sat.Literal.neg 31)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_47_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 666), (Sat.Literal.neg 47), (Sat.Literal.neg 31), (Sat.Literal.pos 667)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_47_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 666), (Sat.Literal.pos 47), (Sat.Literal.pos 31), (Sat.Literal.pos 667)] :=
  (lex_5_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_46_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 667) = lexBefore s permutation5 46 := by
  exact (positive_lex_of_descriptor s 667 permutation5 47 (by rfl)).trans ((lex_skipped s permutation5 46 47 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_46_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation5 46) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 64) = permuteMask permutation5 46 by rw [image5_eq]; rfl))

theorem lex_5_46_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 668) (Sat.Literal.pos 667) (Sat.Literal.pos 46) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation5 46 (assignment s)
    (Sat.Literal.pos 668) (Sat.Literal.pos 667) (Sat.Literal.pos 46) (Sat.Literal.pos 29) (positive_of_descriptor s 668 (.lex permutation5 46) (by rfl)) (lex_5_46_prefix s) (positive_select s 46) (lex_5_46_image s)

theorem lex_5_46_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 667), (Sat.Literal.pos 46), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation5 46 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 667) (Sat.Literal.pos 46) (Sat.Literal.pos 29) (lex_5_46_prefix s) (positive_select s 46) (lex_5_46_image s)

theorem lex_5_46_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 668), (Sat.Literal.pos 667)] :=
  (lex_5_46_gate s).prop _ (List.Mem.head _)

theorem lex_5_46_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 668), (Sat.Literal.neg 46), (Sat.Literal.pos 29)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_46_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 668), (Sat.Literal.pos 46), (Sat.Literal.neg 29)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_46_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 667), (Sat.Literal.neg 46), (Sat.Literal.neg 29), (Sat.Literal.pos 668)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_46_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 667), (Sat.Literal.pos 46), (Sat.Literal.pos 29), (Sat.Literal.pos 668)] :=
  (lex_5_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_45_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 668) = lexBefore s permutation5 45 := by
  exact (positive_lex_of_descriptor s 668 permutation5 46 (by rfl)).trans ((lex_skipped s permutation5 45 46 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_45_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation5 45) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 64) = permuteMask permutation5 45 by rw [image5_eq]; rfl))

theorem lex_5_45_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 669) (Sat.Literal.pos 668) (Sat.Literal.pos 45) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation5 45 (assignment s)
    (Sat.Literal.pos 669) (Sat.Literal.pos 668) (Sat.Literal.pos 45) (Sat.Literal.pos 27) (positive_of_descriptor s 669 (.lex permutation5 45) (by rfl)) (lex_5_45_prefix s) (positive_select s 45) (lex_5_45_image s)

theorem lex_5_45_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 668), (Sat.Literal.pos 45), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation5 45 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 668) (Sat.Literal.pos 45) (Sat.Literal.pos 27) (lex_5_45_prefix s) (positive_select s 45) (lex_5_45_image s)

theorem lex_5_45_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 669), (Sat.Literal.pos 668)] :=
  (lex_5_45_gate s).prop _ (List.Mem.head _)

theorem lex_5_45_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 669), (Sat.Literal.neg 45), (Sat.Literal.pos 27)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_45_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 669), (Sat.Literal.pos 45), (Sat.Literal.neg 27)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_45_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 668), (Sat.Literal.neg 45), (Sat.Literal.neg 27), (Sat.Literal.pos 669)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_45_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 668), (Sat.Literal.pos 45), (Sat.Literal.pos 27), (Sat.Literal.pos 669)] :=
  (lex_5_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_44_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 669) = lexBefore s permutation5 44 := by
  exact (positive_lex_of_descriptor s 669 permutation5 45 (by rfl)).trans ((lex_skipped s permutation5 44 45 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_44_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation5 44) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 64) = permuteMask permutation5 44 by rw [image5_eq]; rfl))

theorem lex_5_44_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 670) (Sat.Literal.pos 669) (Sat.Literal.pos 44) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation5 44 (assignment s)
    (Sat.Literal.pos 670) (Sat.Literal.pos 669) (Sat.Literal.pos 44) (Sat.Literal.pos 25) (positive_of_descriptor s 670 (.lex permutation5 44) (by rfl)) (lex_5_44_prefix s) (positive_select s 44) (lex_5_44_image s)

theorem lex_5_44_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 669), (Sat.Literal.pos 44), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation5 44 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 669) (Sat.Literal.pos 44) (Sat.Literal.pos 25) (lex_5_44_prefix s) (positive_select s 44) (lex_5_44_image s)

theorem lex_5_44_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 670), (Sat.Literal.pos 669)] :=
  (lex_5_44_gate s).prop _ (List.Mem.head _)

theorem lex_5_44_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 670), (Sat.Literal.neg 44), (Sat.Literal.pos 25)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_44_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 670), (Sat.Literal.pos 44), (Sat.Literal.neg 25)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_44_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 669), (Sat.Literal.neg 44), (Sat.Literal.neg 25), (Sat.Literal.pos 670)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_44_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 669), (Sat.Literal.pos 44), (Sat.Literal.pos 25), (Sat.Literal.pos 670)] :=
  (lex_5_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_43_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 670) = lexBefore s permutation5 43 := by
  exact (positive_lex_of_descriptor s 670 permutation5 44 (by rfl)).trans ((lex_skipped s permutation5 43 44 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_43_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation5 43) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 64) = permuteMask permutation5 43 by rw [image5_eq]; rfl))

theorem lex_5_43_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 671) (Sat.Literal.pos 670) (Sat.Literal.pos 43) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation5 43 (assignment s)
    (Sat.Literal.pos 671) (Sat.Literal.pos 670) (Sat.Literal.pos 43) (Sat.Literal.pos 23) (positive_of_descriptor s 671 (.lex permutation5 43) (by rfl)) (lex_5_43_prefix s) (positive_select s 43) (lex_5_43_image s)

theorem lex_5_43_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 670), (Sat.Literal.pos 43), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation5 43 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 670) (Sat.Literal.pos 43) (Sat.Literal.pos 23) (lex_5_43_prefix s) (positive_select s 43) (lex_5_43_image s)

theorem lex_5_43_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 671), (Sat.Literal.pos 670)] :=
  (lex_5_43_gate s).prop _ (List.Mem.head _)

theorem lex_5_43_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 671), (Sat.Literal.neg 43), (Sat.Literal.pos 23)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_43_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 671), (Sat.Literal.pos 43), (Sat.Literal.neg 23)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_43_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 670), (Sat.Literal.neg 43), (Sat.Literal.neg 23), (Sat.Literal.pos 671)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_43_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 670), (Sat.Literal.pos 43), (Sat.Literal.pos 23), (Sat.Literal.pos 671)] :=
  (lex_5_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_42_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 671) = lexBefore s permutation5 42 := by
  exact (positive_lex_of_descriptor s 671 permutation5 43 (by rfl)).trans ((lex_skipped s permutation5 42 43 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_42_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation5 42) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 64) = permuteMask permutation5 42 by rw [image5_eq]; rfl))

theorem lex_5_42_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 672) (Sat.Literal.pos 671) (Sat.Literal.pos 42) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation5 42 (assignment s)
    (Sat.Literal.pos 672) (Sat.Literal.pos 671) (Sat.Literal.pos 42) (Sat.Literal.pos 21) (positive_of_descriptor s 672 (.lex permutation5 42) (by rfl)) (lex_5_42_prefix s) (positive_select s 42) (lex_5_42_image s)

theorem lex_5_42_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 671), (Sat.Literal.pos 42), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation5 42 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 671) (Sat.Literal.pos 42) (Sat.Literal.pos 21) (lex_5_42_prefix s) (positive_select s 42) (lex_5_42_image s)

theorem lex_5_42_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 672), (Sat.Literal.pos 671)] :=
  (lex_5_42_gate s).prop _ (List.Mem.head _)

theorem lex_5_42_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 672), (Sat.Literal.neg 42), (Sat.Literal.pos 21)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_42_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 672), (Sat.Literal.pos 42), (Sat.Literal.neg 21)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_42_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 671), (Sat.Literal.neg 42), (Sat.Literal.neg 21), (Sat.Literal.pos 672)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_42_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 671), (Sat.Literal.pos 42), (Sat.Literal.pos 21), (Sat.Literal.pos 672)] :=
  (lex_5_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_41_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 672) = lexBefore s permutation5 41 := by
  exact (positive_lex_of_descriptor s 672 permutation5 42 (by rfl)).trans ((lex_skipped s permutation5 41 42 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_41_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation5 41) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 64) = permuteMask permutation5 41 by rw [image5_eq]; rfl))

theorem lex_5_41_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 673) (Sat.Literal.pos 672) (Sat.Literal.pos 41) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation5 41 (assignment s)
    (Sat.Literal.pos 673) (Sat.Literal.pos 672) (Sat.Literal.pos 41) (Sat.Literal.pos 19) (positive_of_descriptor s 673 (.lex permutation5 41) (by rfl)) (lex_5_41_prefix s) (positive_select s 41) (lex_5_41_image s)

theorem lex_5_41_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 672), (Sat.Literal.pos 41), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation5 41 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 672) (Sat.Literal.pos 41) (Sat.Literal.pos 19) (lex_5_41_prefix s) (positive_select s 41) (lex_5_41_image s)

theorem lex_5_41_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 673), (Sat.Literal.pos 672)] :=
  (lex_5_41_gate s).prop _ (List.Mem.head _)

theorem lex_5_41_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 673), (Sat.Literal.neg 41), (Sat.Literal.pos 19)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_41_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 673), (Sat.Literal.pos 41), (Sat.Literal.neg 19)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_41_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 672), (Sat.Literal.neg 41), (Sat.Literal.neg 19), (Sat.Literal.pos 673)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_41_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 672), (Sat.Literal.pos 41), (Sat.Literal.pos 19), (Sat.Literal.pos 673)] :=
  (lex_5_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_40_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 673) = lexBefore s permutation5 40 := by
  exact (positive_lex_of_descriptor s 673 permutation5 41 (by rfl)).trans ((lex_skipped s permutation5 40 41 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_40_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation5 40) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 64) = permuteMask permutation5 40 by rw [image5_eq]; rfl))

theorem lex_5_40_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 674) (Sat.Literal.pos 673) (Sat.Literal.pos 40) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation5 40 (assignment s)
    (Sat.Literal.pos 674) (Sat.Literal.pos 673) (Sat.Literal.pos 40) (Sat.Literal.pos 17) (positive_of_descriptor s 674 (.lex permutation5 40) (by rfl)) (lex_5_40_prefix s) (positive_select s 40) (lex_5_40_image s)

theorem lex_5_40_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 673), (Sat.Literal.pos 40), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation5 40 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 673) (Sat.Literal.pos 40) (Sat.Literal.pos 17) (lex_5_40_prefix s) (positive_select s 40) (lex_5_40_image s)

theorem lex_5_40_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 674), (Sat.Literal.pos 673)] :=
  (lex_5_40_gate s).prop _ (List.Mem.head _)

theorem lex_5_40_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 674), (Sat.Literal.neg 40), (Sat.Literal.pos 17)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_40_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 674), (Sat.Literal.pos 40), (Sat.Literal.neg 17)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_40_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 673), (Sat.Literal.neg 40), (Sat.Literal.neg 17), (Sat.Literal.pos 674)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_40_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 673), (Sat.Literal.pos 40), (Sat.Literal.pos 17), (Sat.Literal.pos 674)] :=
  (lex_5_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_39_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 674) = lexBefore s permutation5 39 := by
  exact (positive_lex_of_descriptor s 674 permutation5 40 (by rfl)).trans ((lex_skipped s permutation5 39 40 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_39_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation5 39) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 64) = permuteMask permutation5 39 by rw [image5_eq]; rfl))

theorem lex_5_39_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 675) (Sat.Literal.pos 674) (Sat.Literal.pos 39) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation5 39 (assignment s)
    (Sat.Literal.pos 675) (Sat.Literal.pos 674) (Sat.Literal.pos 39) (Sat.Literal.pos 15) (positive_of_descriptor s 675 (.lex permutation5 39) (by rfl)) (lex_5_39_prefix s) (positive_select s 39) (lex_5_39_image s)

theorem lex_5_39_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 674), (Sat.Literal.pos 39), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation5 39 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 674) (Sat.Literal.pos 39) (Sat.Literal.pos 15) (lex_5_39_prefix s) (positive_select s 39) (lex_5_39_image s)

theorem lex_5_39_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 675), (Sat.Literal.pos 674)] :=
  (lex_5_39_gate s).prop _ (List.Mem.head _)

theorem lex_5_39_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 675), (Sat.Literal.neg 39), (Sat.Literal.pos 15)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_39_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 675), (Sat.Literal.pos 39), (Sat.Literal.neg 15)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_39_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 674), (Sat.Literal.neg 39), (Sat.Literal.neg 15), (Sat.Literal.pos 675)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_39_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 674), (Sat.Literal.pos 39), (Sat.Literal.pos 15), (Sat.Literal.pos 675)] :=
  (lex_5_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_38_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 675) = lexBefore s permutation5 38 := by
  exact (positive_lex_of_descriptor s 675 permutation5 39 (by rfl)).trans ((lex_skipped s permutation5 38 39 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_38_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation5 38) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 64) = permuteMask permutation5 38 by rw [image5_eq]; rfl))

theorem lex_5_38_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 676) (Sat.Literal.pos 675) (Sat.Literal.pos 38) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation5 38 (assignment s)
    (Sat.Literal.pos 676) (Sat.Literal.pos 675) (Sat.Literal.pos 38) (Sat.Literal.pos 13) (positive_of_descriptor s 676 (.lex permutation5 38) (by rfl)) (lex_5_38_prefix s) (positive_select s 38) (lex_5_38_image s)

theorem lex_5_38_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 675), (Sat.Literal.pos 38), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation5 38 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 675) (Sat.Literal.pos 38) (Sat.Literal.pos 13) (lex_5_38_prefix s) (positive_select s 38) (lex_5_38_image s)

theorem lex_5_38_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 676), (Sat.Literal.pos 675)] :=
  (lex_5_38_gate s).prop _ (List.Mem.head _)

theorem lex_5_38_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 676), (Sat.Literal.neg 38), (Sat.Literal.pos 13)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_38_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 676), (Sat.Literal.pos 38), (Sat.Literal.neg 13)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_38_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 675), (Sat.Literal.neg 38), (Sat.Literal.neg 13), (Sat.Literal.pos 676)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_38_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 675), (Sat.Literal.pos 38), (Sat.Literal.pos 13), (Sat.Literal.pos 676)] :=
  (lex_5_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_37_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 676) = lexBefore s permutation5 37 := by
  exact (positive_lex_of_descriptor s 676 permutation5 38 (by rfl)).trans ((lex_skipped s permutation5 37 38 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_37_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation5 37) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 64) = permuteMask permutation5 37 by rw [image5_eq]; rfl))

theorem lex_5_37_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 677) (Sat.Literal.pos 676) (Sat.Literal.pos 37) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation5 37 (assignment s)
    (Sat.Literal.pos 677) (Sat.Literal.pos 676) (Sat.Literal.pos 37) (Sat.Literal.pos 11) (positive_of_descriptor s 677 (.lex permutation5 37) (by rfl)) (lex_5_37_prefix s) (positive_select s 37) (lex_5_37_image s)

theorem lex_5_37_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 676), (Sat.Literal.pos 37), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation5 37 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 676) (Sat.Literal.pos 37) (Sat.Literal.pos 11) (lex_5_37_prefix s) (positive_select s 37) (lex_5_37_image s)

theorem lex_5_37_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 677), (Sat.Literal.pos 676)] :=
  (lex_5_37_gate s).prop _ (List.Mem.head _)

theorem lex_5_37_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 677), (Sat.Literal.neg 37), (Sat.Literal.pos 11)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_37_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 677), (Sat.Literal.pos 37), (Sat.Literal.neg 11)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_37_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 676), (Sat.Literal.neg 37), (Sat.Literal.neg 11), (Sat.Literal.pos 677)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_37_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 676), (Sat.Literal.pos 37), (Sat.Literal.pos 11), (Sat.Literal.pos 677)] :=
  (lex_5_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_36_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 677) = lexBefore s permutation5 36 := by
  exact (positive_lex_of_descriptor s 677 permutation5 37 (by rfl)).trans ((lex_skipped s permutation5 36 37 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_36_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation5 36) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 64) = permuteMask permutation5 36 by rw [image5_eq]; rfl))

theorem lex_5_36_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 678) (Sat.Literal.pos 677) (Sat.Literal.pos 36) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation5 36 (assignment s)
    (Sat.Literal.pos 678) (Sat.Literal.pos 677) (Sat.Literal.pos 36) (Sat.Literal.pos 9) (positive_of_descriptor s 678 (.lex permutation5 36) (by rfl)) (lex_5_36_prefix s) (positive_select s 36) (lex_5_36_image s)

theorem lex_5_36_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 677), (Sat.Literal.pos 36), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation5 36 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 677) (Sat.Literal.pos 36) (Sat.Literal.pos 9) (lex_5_36_prefix s) (positive_select s 36) (lex_5_36_image s)

theorem lex_5_36_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 678), (Sat.Literal.pos 677)] :=
  (lex_5_36_gate s).prop _ (List.Mem.head _)

theorem lex_5_36_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 678), (Sat.Literal.neg 36), (Sat.Literal.pos 9)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_36_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 678), (Sat.Literal.pos 36), (Sat.Literal.neg 9)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_36_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 677), (Sat.Literal.neg 36), (Sat.Literal.neg 9), (Sat.Literal.pos 678)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_36_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 677), (Sat.Literal.pos 36), (Sat.Literal.pos 9), (Sat.Literal.pos 678)] :=
  (lex_5_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_35_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 678) = lexBefore s permutation5 35 := by
  exact (positive_lex_of_descriptor s 678 permutation5 36 (by rfl)).trans ((lex_skipped s permutation5 35 36 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_35_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation5 35) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 64) = permuteMask permutation5 35 by rw [image5_eq]; rfl))

theorem lex_5_35_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 679) (Sat.Literal.pos 678) (Sat.Literal.pos 35) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation5 35 (assignment s)
    (Sat.Literal.pos 679) (Sat.Literal.pos 678) (Sat.Literal.pos 35) (Sat.Literal.pos 7) (positive_of_descriptor s 679 (.lex permutation5 35) (by rfl)) (lex_5_35_prefix s) (positive_select s 35) (lex_5_35_image s)

theorem lex_5_35_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 678), (Sat.Literal.pos 35), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation5 35 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 678) (Sat.Literal.pos 35) (Sat.Literal.pos 7) (lex_5_35_prefix s) (positive_select s 35) (lex_5_35_image s)

theorem lex_5_35_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 679), (Sat.Literal.pos 678)] :=
  (lex_5_35_gate s).prop _ (List.Mem.head _)

theorem lex_5_35_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 679), (Sat.Literal.neg 35), (Sat.Literal.pos 7)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_35_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 679), (Sat.Literal.pos 35), (Sat.Literal.neg 7)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_35_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 678), (Sat.Literal.neg 35), (Sat.Literal.neg 7), (Sat.Literal.pos 679)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_35_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 678), (Sat.Literal.pos 35), (Sat.Literal.pos 7), (Sat.Literal.pos 679)] :=
  (lex_5_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_34_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 679) = lexBefore s permutation5 34 := by
  exact (positive_lex_of_descriptor s 679 permutation5 35 (by rfl)).trans ((lex_skipped s permutation5 34 35 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_34_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation5 34) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 64) = permuteMask permutation5 34 by rw [image5_eq]; rfl))

theorem lex_5_34_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 680) (Sat.Literal.pos 679) (Sat.Literal.pos 34) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation5 34 (assignment s)
    (Sat.Literal.pos 680) (Sat.Literal.pos 679) (Sat.Literal.pos 34) (Sat.Literal.pos 5) (positive_of_descriptor s 680 (.lex permutation5 34) (by rfl)) (lex_5_34_prefix s) (positive_select s 34) (lex_5_34_image s)

theorem lex_5_34_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 679), (Sat.Literal.pos 34), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation5 34 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 679) (Sat.Literal.pos 34) (Sat.Literal.pos 5) (lex_5_34_prefix s) (positive_select s 34) (lex_5_34_image s)

theorem lex_5_34_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 680), (Sat.Literal.pos 679)] :=
  (lex_5_34_gate s).prop _ (List.Mem.head _)

theorem lex_5_34_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 680), (Sat.Literal.neg 34), (Sat.Literal.pos 5)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_34_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 680), (Sat.Literal.pos 34), (Sat.Literal.neg 5)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_34_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 679), (Sat.Literal.neg 34), (Sat.Literal.neg 5), (Sat.Literal.pos 680)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_34_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 679), (Sat.Literal.pos 34), (Sat.Literal.pos 5), (Sat.Literal.pos 680)] :=
  (lex_5_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_33_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 680) = lexBefore s permutation5 33 := by
  exact (positive_lex_of_descriptor s 680 permutation5 34 (by rfl)).trans ((lex_skipped s permutation5 33 34 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_33_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation5 33) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 64) = permuteMask permutation5 33 by rw [image5_eq]; rfl))

theorem lex_5_33_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 681) (Sat.Literal.pos 680) (Sat.Literal.pos 33) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation5 33 (assignment s)
    (Sat.Literal.pos 681) (Sat.Literal.pos 680) (Sat.Literal.pos 33) (Sat.Literal.pos 3) (positive_of_descriptor s 681 (.lex permutation5 33) (by rfl)) (lex_5_33_prefix s) (positive_select s 33) (lex_5_33_image s)

theorem lex_5_33_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 680), (Sat.Literal.pos 33), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation5 33 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 680) (Sat.Literal.pos 33) (Sat.Literal.pos 3) (lex_5_33_prefix s) (positive_select s 33) (lex_5_33_image s)

theorem lex_5_33_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 681), (Sat.Literal.pos 680)] :=
  (lex_5_33_gate s).prop _ (List.Mem.head _)

theorem lex_5_33_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 681), (Sat.Literal.neg 33), (Sat.Literal.pos 3)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_33_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 681), (Sat.Literal.pos 33), (Sat.Literal.neg 3)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_33_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 680), (Sat.Literal.neg 33), (Sat.Literal.neg 3), (Sat.Literal.pos 681)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_33_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 680), (Sat.Literal.pos 33), (Sat.Literal.pos 3), (Sat.Literal.pos 681)] :=
  (lex_5_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_32_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 681) = lexBefore s permutation5 32 := by
  exact (positive_lex_of_descriptor s 681 permutation5 33 (by rfl)).trans ((lex_skipped s permutation5 32 33 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_32_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation5 32) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 64) = permuteMask permutation5 32 by rw [image5_eq]; rfl))

theorem lex_5_32_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 682) (Sat.Literal.pos 681) (Sat.Literal.pos 32) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation5 32 (assignment s)
    (Sat.Literal.pos 682) (Sat.Literal.pos 681) (Sat.Literal.pos 32) (Sat.Literal.pos 1) (positive_of_descriptor s 682 (.lex permutation5 32) (by rfl)) (lex_5_32_prefix s) (positive_select s 32) (lex_5_32_image s)

theorem lex_5_32_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 681), (Sat.Literal.pos 32), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation5 32 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 681) (Sat.Literal.pos 32) (Sat.Literal.pos 1) (lex_5_32_prefix s) (positive_select s 32) (lex_5_32_image s)

theorem lex_5_32_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 682), (Sat.Literal.pos 681)] :=
  (lex_5_32_gate s).prop _ (List.Mem.head _)

theorem lex_5_32_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 682), (Sat.Literal.neg 32), (Sat.Literal.pos 1)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_32_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 682), (Sat.Literal.pos 32), (Sat.Literal.neg 1)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_32_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 681), (Sat.Literal.neg 32), (Sat.Literal.neg 1), (Sat.Literal.pos 682)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_32_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 681), (Sat.Literal.pos 32), (Sat.Literal.pos 1), (Sat.Literal.pos 682)] :=
  (lex_5_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_31_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 682) = lexBefore s permutation5 31 := by
  exact (positive_lex_of_descriptor s 682 permutation5 32 (by rfl)).trans ((lex_skipped s permutation5 31 32 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_31_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation5 31) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 64) = permuteMask permutation5 31 by rw [image5_eq]; rfl))

theorem lex_5_31_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 683) (Sat.Literal.pos 682) (Sat.Literal.pos 31) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation5 31 (assignment s)
    (Sat.Literal.pos 683) (Sat.Literal.pos 682) (Sat.Literal.pos 31) (Sat.Literal.pos 62) (positive_of_descriptor s 683 (.lex permutation5 31) (by rfl)) (lex_5_31_prefix s) (positive_select s 31) (lex_5_31_image s)

theorem lex_5_31_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 682), (Sat.Literal.pos 31), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation5 31 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 682) (Sat.Literal.pos 31) (Sat.Literal.pos 62) (lex_5_31_prefix s) (positive_select s 31) (lex_5_31_image s)

theorem lex_5_31_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 683), (Sat.Literal.pos 682)] :=
  (lex_5_31_gate s).prop _ (List.Mem.head _)

theorem lex_5_31_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 683), (Sat.Literal.neg 31), (Sat.Literal.pos 62)] :=
  (lex_5_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_31_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 683), (Sat.Literal.pos 31), (Sat.Literal.neg 62)] :=
  (lex_5_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_31_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 682), (Sat.Literal.neg 31), (Sat.Literal.neg 62), (Sat.Literal.pos 683)] :=
  (lex_5_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_31_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 682), (Sat.Literal.pos 31), (Sat.Literal.pos 62), (Sat.Literal.pos 683)] :=
  (lex_5_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_30_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 683) = lexBefore s permutation5 30 := by
  exact (positive_lex_of_descriptor s 683 permutation5 31 (by rfl)).trans ((lex_skipped s permutation5 30 31 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_30_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation5 30) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 64) = permuteMask permutation5 30 by rw [image5_eq]; rfl))

theorem lex_5_30_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 684) (Sat.Literal.pos 683) (Sat.Literal.pos 30) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation5 30 (assignment s)
    (Sat.Literal.pos 684) (Sat.Literal.pos 683) (Sat.Literal.pos 30) (Sat.Literal.pos 60) (positive_of_descriptor s 684 (.lex permutation5 30) (by rfl)) (lex_5_30_prefix s) (positive_select s 30) (lex_5_30_image s)

theorem lex_5_30_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 683), (Sat.Literal.pos 30), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation5 30 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 683) (Sat.Literal.pos 30) (Sat.Literal.pos 60) (lex_5_30_prefix s) (positive_select s 30) (lex_5_30_image s)

theorem lex_5_30_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 684), (Sat.Literal.pos 683)] :=
  (lex_5_30_gate s).prop _ (List.Mem.head _)

theorem lex_5_30_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 684), (Sat.Literal.neg 30), (Sat.Literal.pos 60)] :=
  (lex_5_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_30_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 684), (Sat.Literal.pos 30), (Sat.Literal.neg 60)] :=
  (lex_5_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_30_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 683), (Sat.Literal.neg 30), (Sat.Literal.neg 60), (Sat.Literal.pos 684)] :=
  (lex_5_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_30_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 683), (Sat.Literal.pos 30), (Sat.Literal.pos 60), (Sat.Literal.pos 684)] :=
  (lex_5_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_29_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 684) = lexBefore s permutation5 29 := by
  exact (positive_lex_of_descriptor s 684 permutation5 30 (by rfl)).trans ((lex_skipped s permutation5 29 30 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_29_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation5 29) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 64) = permuteMask permutation5 29 by rw [image5_eq]; rfl))

theorem lex_5_29_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 685) (Sat.Literal.pos 684) (Sat.Literal.pos 29) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation5 29 (assignment s)
    (Sat.Literal.pos 685) (Sat.Literal.pos 684) (Sat.Literal.pos 29) (Sat.Literal.pos 58) (positive_of_descriptor s 685 (.lex permutation5 29) (by rfl)) (lex_5_29_prefix s) (positive_select s 29) (lex_5_29_image s)

theorem lex_5_29_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 684), (Sat.Literal.pos 29), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation5 29 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 684) (Sat.Literal.pos 29) (Sat.Literal.pos 58) (lex_5_29_prefix s) (positive_select s 29) (lex_5_29_image s)

theorem lex_5_29_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 685), (Sat.Literal.pos 684)] :=
  (lex_5_29_gate s).prop _ (List.Mem.head _)

theorem lex_5_29_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 685), (Sat.Literal.neg 29), (Sat.Literal.pos 58)] :=
  (lex_5_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_29_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 685), (Sat.Literal.pos 29), (Sat.Literal.neg 58)] :=
  (lex_5_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_29_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 684), (Sat.Literal.neg 29), (Sat.Literal.neg 58), (Sat.Literal.pos 685)] :=
  (lex_5_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_29_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 684), (Sat.Literal.pos 29), (Sat.Literal.pos 58), (Sat.Literal.pos 685)] :=
  (lex_5_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_28_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 685) = lexBefore s permutation5 28 := by
  exact (positive_lex_of_descriptor s 685 permutation5 29 (by rfl)).trans ((lex_skipped s permutation5 28 29 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_28_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation5 28) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 64) = permuteMask permutation5 28 by rw [image5_eq]; rfl))

theorem lex_5_28_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 686) (Sat.Literal.pos 685) (Sat.Literal.pos 28) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation5 28 (assignment s)
    (Sat.Literal.pos 686) (Sat.Literal.pos 685) (Sat.Literal.pos 28) (Sat.Literal.pos 56) (positive_of_descriptor s 686 (.lex permutation5 28) (by rfl)) (lex_5_28_prefix s) (positive_select s 28) (lex_5_28_image s)

theorem lex_5_28_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 685), (Sat.Literal.pos 28), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation5 28 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 685) (Sat.Literal.pos 28) (Sat.Literal.pos 56) (lex_5_28_prefix s) (positive_select s 28) (lex_5_28_image s)

theorem lex_5_28_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 686), (Sat.Literal.pos 685)] :=
  (lex_5_28_gate s).prop _ (List.Mem.head _)

theorem lex_5_28_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 686), (Sat.Literal.neg 28), (Sat.Literal.pos 56)] :=
  (lex_5_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_28_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 686), (Sat.Literal.pos 28), (Sat.Literal.neg 56)] :=
  (lex_5_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_28_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 685), (Sat.Literal.neg 28), (Sat.Literal.neg 56), (Sat.Literal.pos 686)] :=
  (lex_5_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_28_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 685), (Sat.Literal.pos 28), (Sat.Literal.pos 56), (Sat.Literal.pos 686)] :=
  (lex_5_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_27_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 686) = lexBefore s permutation5 27 := by
  exact (positive_lex_of_descriptor s 686 permutation5 28 (by rfl)).trans ((lex_skipped s permutation5 27 28 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_27_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation5 27) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 64) = permuteMask permutation5 27 by rw [image5_eq]; rfl))

theorem lex_5_27_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 687) (Sat.Literal.pos 686) (Sat.Literal.pos 27) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation5 27 (assignment s)
    (Sat.Literal.pos 687) (Sat.Literal.pos 686) (Sat.Literal.pos 27) (Sat.Literal.pos 54) (positive_of_descriptor s 687 (.lex permutation5 27) (by rfl)) (lex_5_27_prefix s) (positive_select s 27) (lex_5_27_image s)

theorem lex_5_27_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 686), (Sat.Literal.pos 27), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation5 27 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 686) (Sat.Literal.pos 27) (Sat.Literal.pos 54) (lex_5_27_prefix s) (positive_select s 27) (lex_5_27_image s)

theorem lex_5_27_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 687), (Sat.Literal.pos 686)] :=
  (lex_5_27_gate s).prop _ (List.Mem.head _)

theorem lex_5_27_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 687), (Sat.Literal.neg 27), (Sat.Literal.pos 54)] :=
  (lex_5_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_27_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 687), (Sat.Literal.pos 27), (Sat.Literal.neg 54)] :=
  (lex_5_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_27_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 686), (Sat.Literal.neg 27), (Sat.Literal.neg 54), (Sat.Literal.pos 687)] :=
  (lex_5_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_27_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 686), (Sat.Literal.pos 27), (Sat.Literal.pos 54), (Sat.Literal.pos 687)] :=
  (lex_5_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_26_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 687) = lexBefore s permutation5 26 := by
  exact (positive_lex_of_descriptor s 687 permutation5 27 (by rfl)).trans ((lex_skipped s permutation5 26 27 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_26_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation5 26) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 64) = permuteMask permutation5 26 by rw [image5_eq]; rfl))

theorem lex_5_26_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 688) (Sat.Literal.pos 687) (Sat.Literal.pos 26) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation5 26 (assignment s)
    (Sat.Literal.pos 688) (Sat.Literal.pos 687) (Sat.Literal.pos 26) (Sat.Literal.pos 52) (positive_of_descriptor s 688 (.lex permutation5 26) (by rfl)) (lex_5_26_prefix s) (positive_select s 26) (lex_5_26_image s)

theorem lex_5_26_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 687), (Sat.Literal.pos 26), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation5 26 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 687) (Sat.Literal.pos 26) (Sat.Literal.pos 52) (lex_5_26_prefix s) (positive_select s 26) (lex_5_26_image s)

theorem lex_5_26_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 688), (Sat.Literal.pos 687)] :=
  (lex_5_26_gate s).prop _ (List.Mem.head _)

theorem lex_5_26_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 688), (Sat.Literal.neg 26), (Sat.Literal.pos 52)] :=
  (lex_5_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_26_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 688), (Sat.Literal.pos 26), (Sat.Literal.neg 52)] :=
  (lex_5_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_26_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 687), (Sat.Literal.neg 26), (Sat.Literal.neg 52), (Sat.Literal.pos 688)] :=
  (lex_5_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_26_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 687), (Sat.Literal.pos 26), (Sat.Literal.pos 52), (Sat.Literal.pos 688)] :=
  (lex_5_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_25_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 688) = lexBefore s permutation5 25 := by
  exact (positive_lex_of_descriptor s 688 permutation5 26 (by rfl)).trans ((lex_skipped s permutation5 25 26 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_25_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation5 25) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 64) = permuteMask permutation5 25 by rw [image5_eq]; rfl))

theorem lex_5_25_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 689) (Sat.Literal.pos 688) (Sat.Literal.pos 25) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation5 25 (assignment s)
    (Sat.Literal.pos 689) (Sat.Literal.pos 688) (Sat.Literal.pos 25) (Sat.Literal.pos 50) (positive_of_descriptor s 689 (.lex permutation5 25) (by rfl)) (lex_5_25_prefix s) (positive_select s 25) (lex_5_25_image s)

theorem lex_5_25_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 688), (Sat.Literal.pos 25), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation5 25 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 688) (Sat.Literal.pos 25) (Sat.Literal.pos 50) (lex_5_25_prefix s) (positive_select s 25) (lex_5_25_image s)

theorem lex_5_25_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 689), (Sat.Literal.pos 688)] :=
  (lex_5_25_gate s).prop _ (List.Mem.head _)

theorem lex_5_25_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 689), (Sat.Literal.neg 25), (Sat.Literal.pos 50)] :=
  (lex_5_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_25_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 689), (Sat.Literal.pos 25), (Sat.Literal.neg 50)] :=
  (lex_5_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_25_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 688), (Sat.Literal.neg 25), (Sat.Literal.neg 50), (Sat.Literal.pos 689)] :=
  (lex_5_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_25_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 688), (Sat.Literal.pos 25), (Sat.Literal.pos 50), (Sat.Literal.pos 689)] :=
  (lex_5_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_24_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 689) = lexBefore s permutation5 24 := by
  exact (positive_lex_of_descriptor s 689 permutation5 25 (by rfl)).trans ((lex_skipped s permutation5 24 25 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_24_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation5 24) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 64) = permuteMask permutation5 24 by rw [image5_eq]; rfl))

theorem lex_5_24_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 690) (Sat.Literal.pos 689) (Sat.Literal.pos 24) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation5 24 (assignment s)
    (Sat.Literal.pos 690) (Sat.Literal.pos 689) (Sat.Literal.pos 24) (Sat.Literal.pos 48) (positive_of_descriptor s 690 (.lex permutation5 24) (by rfl)) (lex_5_24_prefix s) (positive_select s 24) (lex_5_24_image s)

theorem lex_5_24_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 689), (Sat.Literal.pos 24), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation5 24 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 689) (Sat.Literal.pos 24) (Sat.Literal.pos 48) (lex_5_24_prefix s) (positive_select s 24) (lex_5_24_image s)

theorem lex_5_24_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 690), (Sat.Literal.pos 689)] :=
  (lex_5_24_gate s).prop _ (List.Mem.head _)

theorem lex_5_24_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 690), (Sat.Literal.neg 24), (Sat.Literal.pos 48)] :=
  (lex_5_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_24_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 690), (Sat.Literal.pos 24), (Sat.Literal.neg 48)] :=
  (lex_5_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_24_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 689), (Sat.Literal.neg 24), (Sat.Literal.neg 48), (Sat.Literal.pos 690)] :=
  (lex_5_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_24_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 689), (Sat.Literal.pos 24), (Sat.Literal.pos 48), (Sat.Literal.pos 690)] :=
  (lex_5_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_5_23_prefix (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 690) = lexBefore s permutation5 23 := by
  exact (positive_lex_of_descriptor s 690 permutation5 24 (by rfl)).trans ((lex_skipped s permutation5 23 24 (by decide) (by intro j hj hp; rw [image5_eq]; exact fixedOnRange_spec image5 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_5_23_image (s : Fin 64 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation5 23) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 64) = permuteMask permutation5 23 by rw [image5_eq]; rfl))

theorem lex_5_23_gate (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 691) (Sat.Literal.pos 690) (Sat.Literal.pos 23) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation5 23 (assignment s)
    (Sat.Literal.pos 691) (Sat.Literal.pos 690) (Sat.Literal.pos 23) (Sat.Literal.pos 46) (positive_of_descriptor s 691 (.lex permutation5 23) (by rfl)) (lex_5_23_prefix s) (positive_select s 23) (lex_5_23_image s)

theorem lex_5_23_comparison (s : Fin 64 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 690), (Sat.Literal.pos 23), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation5 23 (hmax permutation5) (assignment s)
    (Sat.Literal.pos 690) (Sat.Literal.pos 23) (Sat.Literal.pos 46) (lex_5_23_prefix s) (positive_select s 23) (lex_5_23_image s)

theorem lex_5_23_clause0 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 691), (Sat.Literal.pos 690)] :=
  (lex_5_23_gate s).prop _ (List.Mem.head _)

theorem lex_5_23_clause1 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 691), (Sat.Literal.neg 23), (Sat.Literal.pos 46)] :=
  (lex_5_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_5_23_clause2 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 691), (Sat.Literal.pos 23), (Sat.Literal.neg 46)] :=
  (lex_5_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_5_23_clause3 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 690), (Sat.Literal.neg 23), (Sat.Literal.neg 46), (Sat.Literal.pos 691)] :=
  (lex_5_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_5_23_clause4 (s : Fin 64 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 690), (Sat.Literal.pos 23), (Sat.Literal.pos 46), (Sat.Literal.pos 691)] :=
  (lex_5_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_3_51_gate

end Crown.CertificateSixData
