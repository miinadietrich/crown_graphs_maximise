import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_7_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3624) = lexBefore s permutation7 50 := by
  exact (positive_lex_of_descriptor s 3624 permutation7 51 (by rfl)).trans ((lex_skipped s permutation7 50 51 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation7 50) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation7 50 by rw [image7_eq]; rfl))

theorem lex_7_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3625) (Sat.Literal.pos 3624) (Sat.Literal.pos 50) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation7 50 (assignment s)
    (Sat.Literal.pos 3625) (Sat.Literal.pos 3624) (Sat.Literal.pos 50) (Sat.Literal.pos 100) (positive_of_descriptor s 3625 (.lex permutation7 50) (by rfl)) (lex_7_50_prefix s) (positive_select s 50) (lex_7_50_image s)

theorem lex_7_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3624), (Sat.Literal.pos 50), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation7 50 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3624) (Sat.Literal.pos 50) (Sat.Literal.pos 100) (lex_7_50_prefix s) (positive_select s 50) (lex_7_50_image s)

theorem lex_7_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3625), (Sat.Literal.pos 3624)] :=
  (lex_7_50_gate s).prop _ (List.Mem.head _)

theorem lex_7_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3625), (Sat.Literal.neg 50), (Sat.Literal.pos 100)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3625), (Sat.Literal.pos 50), (Sat.Literal.neg 100)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3624), (Sat.Literal.neg 50), (Sat.Literal.neg 100), (Sat.Literal.pos 3625)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3624), (Sat.Literal.pos 50), (Sat.Literal.pos 100), (Sat.Literal.pos 3625)] :=
  (lex_7_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3625) = lexBefore s permutation7 49 := by
  exact (positive_lex_of_descriptor s 3625 permutation7 50 (by rfl)).trans ((lex_skipped s permutation7 49 50 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation7 49) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation7 49 by rw [image7_eq]; rfl))

theorem lex_7_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3626) (Sat.Literal.pos 3625) (Sat.Literal.pos 49) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation7 49 (assignment s)
    (Sat.Literal.pos 3626) (Sat.Literal.pos 3625) (Sat.Literal.pos 49) (Sat.Literal.pos 98) (positive_of_descriptor s 3626 (.lex permutation7 49) (by rfl)) (lex_7_49_prefix s) (positive_select s 49) (lex_7_49_image s)

theorem lex_7_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3625), (Sat.Literal.pos 49), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation7 49 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3625) (Sat.Literal.pos 49) (Sat.Literal.pos 98) (lex_7_49_prefix s) (positive_select s 49) (lex_7_49_image s)

theorem lex_7_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3626), (Sat.Literal.pos 3625)] :=
  (lex_7_49_gate s).prop _ (List.Mem.head _)

theorem lex_7_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3626), (Sat.Literal.neg 49), (Sat.Literal.pos 98)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3626), (Sat.Literal.pos 49), (Sat.Literal.neg 98)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3625), (Sat.Literal.neg 49), (Sat.Literal.neg 98), (Sat.Literal.pos 3626)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3625), (Sat.Literal.pos 49), (Sat.Literal.pos 98), (Sat.Literal.pos 3626)] :=
  (lex_7_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3626) = lexBefore s permutation7 48 := by
  exact (positive_lex_of_descriptor s 3626 permutation7 49 (by rfl)).trans ((lex_skipped s permutation7 48 49 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation7 48) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation7 48 by rw [image7_eq]; rfl))

theorem lex_7_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3627) (Sat.Literal.pos 3626) (Sat.Literal.pos 48) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation7 48 (assignment s)
    (Sat.Literal.pos 3627) (Sat.Literal.pos 3626) (Sat.Literal.pos 48) (Sat.Literal.pos 96) (positive_of_descriptor s 3627 (.lex permutation7 48) (by rfl)) (lex_7_48_prefix s) (positive_select s 48) (lex_7_48_image s)

theorem lex_7_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3626), (Sat.Literal.pos 48), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation7 48 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3626) (Sat.Literal.pos 48) (Sat.Literal.pos 96) (lex_7_48_prefix s) (positive_select s 48) (lex_7_48_image s)

theorem lex_7_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3627), (Sat.Literal.pos 3626)] :=
  (lex_7_48_gate s).prop _ (List.Mem.head _)

theorem lex_7_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3627), (Sat.Literal.neg 48), (Sat.Literal.pos 96)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3627), (Sat.Literal.pos 48), (Sat.Literal.neg 96)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3626), (Sat.Literal.neg 48), (Sat.Literal.neg 96), (Sat.Literal.pos 3627)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3626), (Sat.Literal.pos 48), (Sat.Literal.pos 96), (Sat.Literal.pos 3627)] :=
  (lex_7_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3627) = lexBefore s permutation7 47 := by
  exact (positive_lex_of_descriptor s 3627 permutation7 48 (by rfl)).trans ((lex_skipped s permutation7 47 48 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation7 47) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation7 47 by rw [image7_eq]; rfl))

theorem lex_7_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3628) (Sat.Literal.pos 3627) (Sat.Literal.pos 47) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation7 47 (assignment s)
    (Sat.Literal.pos 3628) (Sat.Literal.pos 3627) (Sat.Literal.pos 47) (Sat.Literal.pos 94) (positive_of_descriptor s 3628 (.lex permutation7 47) (by rfl)) (lex_7_47_prefix s) (positive_select s 47) (lex_7_47_image s)

theorem lex_7_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3627), (Sat.Literal.pos 47), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation7 47 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3627) (Sat.Literal.pos 47) (Sat.Literal.pos 94) (lex_7_47_prefix s) (positive_select s 47) (lex_7_47_image s)

theorem lex_7_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3628), (Sat.Literal.pos 3627)] :=
  (lex_7_47_gate s).prop _ (List.Mem.head _)

theorem lex_7_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3628), (Sat.Literal.neg 47), (Sat.Literal.pos 94)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3628), (Sat.Literal.pos 47), (Sat.Literal.neg 94)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3627), (Sat.Literal.neg 47), (Sat.Literal.neg 94), (Sat.Literal.pos 3628)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3627), (Sat.Literal.pos 47), (Sat.Literal.pos 94), (Sat.Literal.pos 3628)] :=
  (lex_7_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3628) = lexBefore s permutation7 46 := by
  exact (positive_lex_of_descriptor s 3628 permutation7 47 (by rfl)).trans ((lex_skipped s permutation7 46 47 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation7 46) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation7 46 by rw [image7_eq]; rfl))

theorem lex_7_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3629) (Sat.Literal.pos 3628) (Sat.Literal.pos 46) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation7 46 (assignment s)
    (Sat.Literal.pos 3629) (Sat.Literal.pos 3628) (Sat.Literal.pos 46) (Sat.Literal.pos 92) (positive_of_descriptor s 3629 (.lex permutation7 46) (by rfl)) (lex_7_46_prefix s) (positive_select s 46) (lex_7_46_image s)

theorem lex_7_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3628), (Sat.Literal.pos 46), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation7 46 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3628) (Sat.Literal.pos 46) (Sat.Literal.pos 92) (lex_7_46_prefix s) (positive_select s 46) (lex_7_46_image s)

theorem lex_7_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3629), (Sat.Literal.pos 3628)] :=
  (lex_7_46_gate s).prop _ (List.Mem.head _)

theorem lex_7_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3629), (Sat.Literal.neg 46), (Sat.Literal.pos 92)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3629), (Sat.Literal.pos 46), (Sat.Literal.neg 92)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3628), (Sat.Literal.neg 46), (Sat.Literal.neg 92), (Sat.Literal.pos 3629)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3628), (Sat.Literal.pos 46), (Sat.Literal.pos 92), (Sat.Literal.pos 3629)] :=
  (lex_7_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3629) = lexBefore s permutation7 45 := by
  exact (positive_lex_of_descriptor s 3629 permutation7 46 (by rfl)).trans ((lex_skipped s permutation7 45 46 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation7 45) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation7 45 by rw [image7_eq]; rfl))

theorem lex_7_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3630) (Sat.Literal.pos 3629) (Sat.Literal.pos 45) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation7 45 (assignment s)
    (Sat.Literal.pos 3630) (Sat.Literal.pos 3629) (Sat.Literal.pos 45) (Sat.Literal.pos 90) (positive_of_descriptor s 3630 (.lex permutation7 45) (by rfl)) (lex_7_45_prefix s) (positive_select s 45) (lex_7_45_image s)

theorem lex_7_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3629), (Sat.Literal.pos 45), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation7 45 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3629) (Sat.Literal.pos 45) (Sat.Literal.pos 90) (lex_7_45_prefix s) (positive_select s 45) (lex_7_45_image s)

theorem lex_7_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3630), (Sat.Literal.pos 3629)] :=
  (lex_7_45_gate s).prop _ (List.Mem.head _)

theorem lex_7_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3630), (Sat.Literal.neg 45), (Sat.Literal.pos 90)] :=
  (lex_7_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3630), (Sat.Literal.pos 45), (Sat.Literal.neg 90)] :=
  (lex_7_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3629), (Sat.Literal.neg 45), (Sat.Literal.neg 90), (Sat.Literal.pos 3630)] :=
  (lex_7_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3629), (Sat.Literal.pos 45), (Sat.Literal.pos 90), (Sat.Literal.pos 3630)] :=
  (lex_7_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3630) = lexBefore s permutation7 44 := by
  exact (positive_lex_of_descriptor s 3630 permutation7 45 (by rfl)).trans ((lex_skipped s permutation7 44 45 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation7 44) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation7 44 by rw [image7_eq]; rfl))

theorem lex_7_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3631) (Sat.Literal.pos 3630) (Sat.Literal.pos 44) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation7 44 (assignment s)
    (Sat.Literal.pos 3631) (Sat.Literal.pos 3630) (Sat.Literal.pos 44) (Sat.Literal.pos 88) (positive_of_descriptor s 3631 (.lex permutation7 44) (by rfl)) (lex_7_44_prefix s) (positive_select s 44) (lex_7_44_image s)

theorem lex_7_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3630), (Sat.Literal.pos 44), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation7 44 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3630) (Sat.Literal.pos 44) (Sat.Literal.pos 88) (lex_7_44_prefix s) (positive_select s 44) (lex_7_44_image s)

theorem lex_7_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3631), (Sat.Literal.pos 3630)] :=
  (lex_7_44_gate s).prop _ (List.Mem.head _)

theorem lex_7_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3631), (Sat.Literal.neg 44), (Sat.Literal.pos 88)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3631), (Sat.Literal.pos 44), (Sat.Literal.neg 88)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3630), (Sat.Literal.neg 44), (Sat.Literal.neg 88), (Sat.Literal.pos 3631)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3630), (Sat.Literal.pos 44), (Sat.Literal.pos 88), (Sat.Literal.pos 3631)] :=
  (lex_7_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3631) = lexBefore s permutation7 43 := by
  exact (positive_lex_of_descriptor s 3631 permutation7 44 (by rfl)).trans ((lex_skipped s permutation7 43 44 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation7 43) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation7 43 by rw [image7_eq]; rfl))

theorem lex_7_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3632) (Sat.Literal.pos 3631) (Sat.Literal.pos 43) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation7 43 (assignment s)
    (Sat.Literal.pos 3632) (Sat.Literal.pos 3631) (Sat.Literal.pos 43) (Sat.Literal.pos 86) (positive_of_descriptor s 3632 (.lex permutation7 43) (by rfl)) (lex_7_43_prefix s) (positive_select s 43) (lex_7_43_image s)

theorem lex_7_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3631), (Sat.Literal.pos 43), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation7 43 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3631) (Sat.Literal.pos 43) (Sat.Literal.pos 86) (lex_7_43_prefix s) (positive_select s 43) (lex_7_43_image s)

theorem lex_7_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3632), (Sat.Literal.pos 3631)] :=
  (lex_7_43_gate s).prop _ (List.Mem.head _)

theorem lex_7_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3632), (Sat.Literal.neg 43), (Sat.Literal.pos 86)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3632), (Sat.Literal.pos 43), (Sat.Literal.neg 86)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3631), (Sat.Literal.neg 43), (Sat.Literal.neg 86), (Sat.Literal.pos 3632)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3631), (Sat.Literal.pos 43), (Sat.Literal.pos 86), (Sat.Literal.pos 3632)] :=
  (lex_7_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3632) = lexBefore s permutation7 42 := by
  exact (positive_lex_of_descriptor s 3632 permutation7 43 (by rfl)).trans ((lex_skipped s permutation7 42 43 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation7 42) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation7 42 by rw [image7_eq]; rfl))

theorem lex_7_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3633) (Sat.Literal.pos 3632) (Sat.Literal.pos 42) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation7 42 (assignment s)
    (Sat.Literal.pos 3633) (Sat.Literal.pos 3632) (Sat.Literal.pos 42) (Sat.Literal.pos 84) (positive_of_descriptor s 3633 (.lex permutation7 42) (by rfl)) (lex_7_42_prefix s) (positive_select s 42) (lex_7_42_image s)

theorem lex_7_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3632), (Sat.Literal.pos 42), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation7 42 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3632) (Sat.Literal.pos 42) (Sat.Literal.pos 84) (lex_7_42_prefix s) (positive_select s 42) (lex_7_42_image s)

theorem lex_7_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3633), (Sat.Literal.pos 3632)] :=
  (lex_7_42_gate s).prop _ (List.Mem.head _)

theorem lex_7_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3633), (Sat.Literal.neg 42), (Sat.Literal.pos 84)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3633), (Sat.Literal.pos 42), (Sat.Literal.neg 84)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3632), (Sat.Literal.neg 42), (Sat.Literal.neg 84), (Sat.Literal.pos 3633)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3632), (Sat.Literal.pos 42), (Sat.Literal.pos 84), (Sat.Literal.pos 3633)] :=
  (lex_7_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3633) = lexBefore s permutation7 41 := by
  exact (positive_lex_of_descriptor s 3633 permutation7 42 (by rfl)).trans ((lex_skipped s permutation7 41 42 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation7 41) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation7 41 by rw [image7_eq]; rfl))

theorem lex_7_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3634) (Sat.Literal.pos 3633) (Sat.Literal.pos 41) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation7 41 (assignment s)
    (Sat.Literal.pos 3634) (Sat.Literal.pos 3633) (Sat.Literal.pos 41) (Sat.Literal.pos 82) (positive_of_descriptor s 3634 (.lex permutation7 41) (by rfl)) (lex_7_41_prefix s) (positive_select s 41) (lex_7_41_image s)

theorem lex_7_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3633), (Sat.Literal.pos 41), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation7 41 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3633) (Sat.Literal.pos 41) (Sat.Literal.pos 82) (lex_7_41_prefix s) (positive_select s 41) (lex_7_41_image s)

theorem lex_7_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3634), (Sat.Literal.pos 3633)] :=
  (lex_7_41_gate s).prop _ (List.Mem.head _)

theorem lex_7_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3634), (Sat.Literal.neg 41), (Sat.Literal.pos 82)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3634), (Sat.Literal.pos 41), (Sat.Literal.neg 82)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3633), (Sat.Literal.neg 41), (Sat.Literal.neg 82), (Sat.Literal.pos 3634)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3633), (Sat.Literal.pos 41), (Sat.Literal.pos 82), (Sat.Literal.pos 3634)] :=
  (lex_7_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3634) = lexBefore s permutation7 40 := by
  exact (positive_lex_of_descriptor s 3634 permutation7 41 (by rfl)).trans ((lex_skipped s permutation7 40 41 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation7 40) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation7 40 by rw [image7_eq]; rfl))

theorem lex_7_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3635) (Sat.Literal.pos 3634) (Sat.Literal.pos 40) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation7 40 (assignment s)
    (Sat.Literal.pos 3635) (Sat.Literal.pos 3634) (Sat.Literal.pos 40) (Sat.Literal.pos 80) (positive_of_descriptor s 3635 (.lex permutation7 40) (by rfl)) (lex_7_40_prefix s) (positive_select s 40) (lex_7_40_image s)

theorem lex_7_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3634), (Sat.Literal.pos 40), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation7 40 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3634) (Sat.Literal.pos 40) (Sat.Literal.pos 80) (lex_7_40_prefix s) (positive_select s 40) (lex_7_40_image s)

theorem lex_7_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3635), (Sat.Literal.pos 3634)] :=
  (lex_7_40_gate s).prop _ (List.Mem.head _)

theorem lex_7_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3635), (Sat.Literal.neg 40), (Sat.Literal.pos 80)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3635), (Sat.Literal.pos 40), (Sat.Literal.neg 80)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3634), (Sat.Literal.neg 40), (Sat.Literal.neg 80), (Sat.Literal.pos 3635)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3634), (Sat.Literal.pos 40), (Sat.Literal.pos 80), (Sat.Literal.pos 3635)] :=
  (lex_7_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3635) = lexBefore s permutation7 39 := by
  exact (positive_lex_of_descriptor s 3635 permutation7 40 (by rfl)).trans ((lex_skipped s permutation7 39 40 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation7 39) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation7 39 by rw [image7_eq]; rfl))

theorem lex_7_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3636) (Sat.Literal.pos 3635) (Sat.Literal.pos 39) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation7 39 (assignment s)
    (Sat.Literal.pos 3636) (Sat.Literal.pos 3635) (Sat.Literal.pos 39) (Sat.Literal.pos 78) (positive_of_descriptor s 3636 (.lex permutation7 39) (by rfl)) (lex_7_39_prefix s) (positive_select s 39) (lex_7_39_image s)

theorem lex_7_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3635), (Sat.Literal.pos 39), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation7 39 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3635) (Sat.Literal.pos 39) (Sat.Literal.pos 78) (lex_7_39_prefix s) (positive_select s 39) (lex_7_39_image s)

theorem lex_7_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3636), (Sat.Literal.pos 3635)] :=
  (lex_7_39_gate s).prop _ (List.Mem.head _)

theorem lex_7_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3636), (Sat.Literal.neg 39), (Sat.Literal.pos 78)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3636), (Sat.Literal.pos 39), (Sat.Literal.neg 78)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3635), (Sat.Literal.neg 39), (Sat.Literal.neg 78), (Sat.Literal.pos 3636)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3635), (Sat.Literal.pos 39), (Sat.Literal.pos 78), (Sat.Literal.pos 3636)] :=
  (lex_7_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3636) = lexBefore s permutation7 38 := by
  exact (positive_lex_of_descriptor s 3636 permutation7 39 (by rfl)).trans ((lex_skipped s permutation7 38 39 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation7 38) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation7 38 by rw [image7_eq]; rfl))

theorem lex_7_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3637) (Sat.Literal.pos 3636) (Sat.Literal.pos 38) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation7 38 (assignment s)
    (Sat.Literal.pos 3637) (Sat.Literal.pos 3636) (Sat.Literal.pos 38) (Sat.Literal.pos 76) (positive_of_descriptor s 3637 (.lex permutation7 38) (by rfl)) (lex_7_38_prefix s) (positive_select s 38) (lex_7_38_image s)

theorem lex_7_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3636), (Sat.Literal.pos 38), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation7 38 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3636) (Sat.Literal.pos 38) (Sat.Literal.pos 76) (lex_7_38_prefix s) (positive_select s 38) (lex_7_38_image s)

theorem lex_7_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3637), (Sat.Literal.pos 3636)] :=
  (lex_7_38_gate s).prop _ (List.Mem.head _)

theorem lex_7_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3637), (Sat.Literal.neg 38), (Sat.Literal.pos 76)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3637), (Sat.Literal.pos 38), (Sat.Literal.neg 76)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3636), (Sat.Literal.neg 38), (Sat.Literal.neg 76), (Sat.Literal.pos 3637)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3636), (Sat.Literal.pos 38), (Sat.Literal.pos 76), (Sat.Literal.pos 3637)] :=
  (lex_7_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3637) = lexBefore s permutation7 37 := by
  exact (positive_lex_of_descriptor s 3637 permutation7 38 (by rfl)).trans ((lex_skipped s permutation7 37 38 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation7 37) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation7 37 by rw [image7_eq]; rfl))

theorem lex_7_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3638) (Sat.Literal.pos 3637) (Sat.Literal.pos 37) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation7 37 (assignment s)
    (Sat.Literal.pos 3638) (Sat.Literal.pos 3637) (Sat.Literal.pos 37) (Sat.Literal.pos 74) (positive_of_descriptor s 3638 (.lex permutation7 37) (by rfl)) (lex_7_37_prefix s) (positive_select s 37) (lex_7_37_image s)

theorem lex_7_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3637), (Sat.Literal.pos 37), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation7 37 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3637) (Sat.Literal.pos 37) (Sat.Literal.pos 74) (lex_7_37_prefix s) (positive_select s 37) (lex_7_37_image s)

theorem lex_7_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3638), (Sat.Literal.pos 3637)] :=
  (lex_7_37_gate s).prop _ (List.Mem.head _)

theorem lex_7_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3638), (Sat.Literal.neg 37), (Sat.Literal.pos 74)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3638), (Sat.Literal.pos 37), (Sat.Literal.neg 74)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3637), (Sat.Literal.neg 37), (Sat.Literal.neg 74), (Sat.Literal.pos 3638)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3637), (Sat.Literal.pos 37), (Sat.Literal.pos 74), (Sat.Literal.pos 3638)] :=
  (lex_7_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3638) = lexBefore s permutation7 36 := by
  exact (positive_lex_of_descriptor s 3638 permutation7 37 (by rfl)).trans ((lex_skipped s permutation7 36 37 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation7 36) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation7 36 by rw [image7_eq]; rfl))

theorem lex_7_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3639) (Sat.Literal.pos 3638) (Sat.Literal.pos 36) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation7 36 (assignment s)
    (Sat.Literal.pos 3639) (Sat.Literal.pos 3638) (Sat.Literal.pos 36) (Sat.Literal.pos 72) (positive_of_descriptor s 3639 (.lex permutation7 36) (by rfl)) (lex_7_36_prefix s) (positive_select s 36) (lex_7_36_image s)

theorem lex_7_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3638), (Sat.Literal.pos 36), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation7 36 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3638) (Sat.Literal.pos 36) (Sat.Literal.pos 72) (lex_7_36_prefix s) (positive_select s 36) (lex_7_36_image s)

theorem lex_7_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3639), (Sat.Literal.pos 3638)] :=
  (lex_7_36_gate s).prop _ (List.Mem.head _)

theorem lex_7_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3639), (Sat.Literal.neg 36), (Sat.Literal.pos 72)] :=
  (lex_7_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3639), (Sat.Literal.pos 36), (Sat.Literal.neg 72)] :=
  (lex_7_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3638), (Sat.Literal.neg 36), (Sat.Literal.neg 72), (Sat.Literal.pos 3639)] :=
  (lex_7_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3638), (Sat.Literal.pos 36), (Sat.Literal.pos 72), (Sat.Literal.pos 3639)] :=
  (lex_7_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3639) = lexBefore s permutation7 35 := by
  exact (positive_lex_of_descriptor s 3639 permutation7 36 (by rfl)).trans ((lex_skipped s permutation7 35 36 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation7 35) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation7 35 by rw [image7_eq]; rfl))

theorem lex_7_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3640) (Sat.Literal.pos 3639) (Sat.Literal.pos 35) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation7 35 (assignment s)
    (Sat.Literal.pos 3640) (Sat.Literal.pos 3639) (Sat.Literal.pos 35) (Sat.Literal.pos 70) (positive_of_descriptor s 3640 (.lex permutation7 35) (by rfl)) (lex_7_35_prefix s) (positive_select s 35) (lex_7_35_image s)

theorem lex_7_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3639), (Sat.Literal.pos 35), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation7 35 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3639) (Sat.Literal.pos 35) (Sat.Literal.pos 70) (lex_7_35_prefix s) (positive_select s 35) (lex_7_35_image s)

theorem lex_7_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3640), (Sat.Literal.pos 3639)] :=
  (lex_7_35_gate s).prop _ (List.Mem.head _)

theorem lex_7_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3640), (Sat.Literal.neg 35), (Sat.Literal.pos 70)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3640), (Sat.Literal.pos 35), (Sat.Literal.neg 70)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3639), (Sat.Literal.neg 35), (Sat.Literal.neg 70), (Sat.Literal.pos 3640)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3639), (Sat.Literal.pos 35), (Sat.Literal.pos 70), (Sat.Literal.pos 3640)] :=
  (lex_7_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3640) = lexBefore s permutation7 34 := by
  exact (positive_lex_of_descriptor s 3640 permutation7 35 (by rfl)).trans ((lex_skipped s permutation7 34 35 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation7 34) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation7 34 by rw [image7_eq]; rfl))

theorem lex_7_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3641) (Sat.Literal.pos 3640) (Sat.Literal.pos 34) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation7 34 (assignment s)
    (Sat.Literal.pos 3641) (Sat.Literal.pos 3640) (Sat.Literal.pos 34) (Sat.Literal.pos 68) (positive_of_descriptor s 3641 (.lex permutation7 34) (by rfl)) (lex_7_34_prefix s) (positive_select s 34) (lex_7_34_image s)

theorem lex_7_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3640), (Sat.Literal.pos 34), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation7 34 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3640) (Sat.Literal.pos 34) (Sat.Literal.pos 68) (lex_7_34_prefix s) (positive_select s 34) (lex_7_34_image s)

theorem lex_7_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3641), (Sat.Literal.pos 3640)] :=
  (lex_7_34_gate s).prop _ (List.Mem.head _)

theorem lex_7_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3641), (Sat.Literal.neg 34), (Sat.Literal.pos 68)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3641), (Sat.Literal.pos 34), (Sat.Literal.neg 68)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3640), (Sat.Literal.neg 34), (Sat.Literal.neg 68), (Sat.Literal.pos 3641)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3640), (Sat.Literal.pos 34), (Sat.Literal.pos 68), (Sat.Literal.pos 3641)] :=
  (lex_7_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3641) = lexBefore s permutation7 33 := by
  exact (positive_lex_of_descriptor s 3641 permutation7 34 (by rfl)).trans ((lex_skipped s permutation7 33 34 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation7 33) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation7 33 by rw [image7_eq]; rfl))

theorem lex_7_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3642) (Sat.Literal.pos 3641) (Sat.Literal.pos 33) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation7 33 (assignment s)
    (Sat.Literal.pos 3642) (Sat.Literal.pos 3641) (Sat.Literal.pos 33) (Sat.Literal.pos 66) (positive_of_descriptor s 3642 (.lex permutation7 33) (by rfl)) (lex_7_33_prefix s) (positive_select s 33) (lex_7_33_image s)

theorem lex_7_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3641), (Sat.Literal.pos 33), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation7 33 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3641) (Sat.Literal.pos 33) (Sat.Literal.pos 66) (lex_7_33_prefix s) (positive_select s 33) (lex_7_33_image s)

theorem lex_7_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3642), (Sat.Literal.pos 3641)] :=
  (lex_7_33_gate s).prop _ (List.Mem.head _)

theorem lex_7_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3642), (Sat.Literal.neg 33), (Sat.Literal.pos 66)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3642), (Sat.Literal.pos 33), (Sat.Literal.neg 66)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3641), (Sat.Literal.neg 33), (Sat.Literal.neg 66), (Sat.Literal.pos 3642)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3641), (Sat.Literal.pos 33), (Sat.Literal.pos 66), (Sat.Literal.pos 3642)] :=
  (lex_7_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3642) = lexBefore s permutation7 32 := by
  exact (positive_lex_of_descriptor s 3642 permutation7 33 (by rfl)).trans ((lex_skipped s permutation7 32 33 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation7 32) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation7 32 by rw [image7_eq]; rfl))

theorem lex_7_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3643) (Sat.Literal.pos 3642) (Sat.Literal.pos 32) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation7 32 (assignment s)
    (Sat.Literal.pos 3643) (Sat.Literal.pos 3642) (Sat.Literal.pos 32) (Sat.Literal.pos 64) (positive_of_descriptor s 3643 (.lex permutation7 32) (by rfl)) (lex_7_32_prefix s) (positive_select s 32) (lex_7_32_image s)

theorem lex_7_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3642), (Sat.Literal.pos 32), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation7 32 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3642) (Sat.Literal.pos 32) (Sat.Literal.pos 64) (lex_7_32_prefix s) (positive_select s 32) (lex_7_32_image s)

theorem lex_7_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3643), (Sat.Literal.pos 3642)] :=
  (lex_7_32_gate s).prop _ (List.Mem.head _)

theorem lex_7_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3643), (Sat.Literal.neg 32), (Sat.Literal.pos 64)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3643), (Sat.Literal.pos 32), (Sat.Literal.neg 64)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3642), (Sat.Literal.neg 32), (Sat.Literal.neg 64), (Sat.Literal.pos 3643)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3642), (Sat.Literal.pos 32), (Sat.Literal.pos 64), (Sat.Literal.pos 3643)] :=
  (lex_7_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3643) = lexBefore s permutation7 31 := by
  exact (positive_lex_of_descriptor s 3643 permutation7 32 (by rfl)).trans ((lex_skipped s permutation7 31 32 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation7 31) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation7 31 by rw [image7_eq]; rfl))

theorem lex_7_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3644) (Sat.Literal.pos 3643) (Sat.Literal.pos 31) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation7 31 (assignment s)
    (Sat.Literal.pos 3644) (Sat.Literal.pos 3643) (Sat.Literal.pos 31) (Sat.Literal.pos 62) (positive_of_descriptor s 3644 (.lex permutation7 31) (by rfl)) (lex_7_31_prefix s) (positive_select s 31) (lex_7_31_image s)

theorem lex_7_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3643), (Sat.Literal.pos 31), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation7 31 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3643) (Sat.Literal.pos 31) (Sat.Literal.pos 62) (lex_7_31_prefix s) (positive_select s 31) (lex_7_31_image s)

theorem lex_7_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3644), (Sat.Literal.pos 3643)] :=
  (lex_7_31_gate s).prop _ (List.Mem.head _)

theorem lex_7_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3644), (Sat.Literal.neg 31), (Sat.Literal.pos 62)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3644), (Sat.Literal.pos 31), (Sat.Literal.neg 62)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3643), (Sat.Literal.neg 31), (Sat.Literal.neg 62), (Sat.Literal.pos 3644)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3643), (Sat.Literal.pos 31), (Sat.Literal.pos 62), (Sat.Literal.pos 3644)] :=
  (lex_7_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3644) = lexBefore s permutation7 30 := by
  exact (positive_lex_of_descriptor s 3644 permutation7 31 (by rfl)).trans ((lex_skipped s permutation7 30 31 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation7 30) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation7 30 by rw [image7_eq]; rfl))

theorem lex_7_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3645) (Sat.Literal.pos 3644) (Sat.Literal.pos 30) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation7 30 (assignment s)
    (Sat.Literal.pos 3645) (Sat.Literal.pos 3644) (Sat.Literal.pos 30) (Sat.Literal.pos 60) (positive_of_descriptor s 3645 (.lex permutation7 30) (by rfl)) (lex_7_30_prefix s) (positive_select s 30) (lex_7_30_image s)

theorem lex_7_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3644), (Sat.Literal.pos 30), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation7 30 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3644) (Sat.Literal.pos 30) (Sat.Literal.pos 60) (lex_7_30_prefix s) (positive_select s 30) (lex_7_30_image s)

theorem lex_7_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3645), (Sat.Literal.pos 3644)] :=
  (lex_7_30_gate s).prop _ (List.Mem.head _)

theorem lex_7_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3645), (Sat.Literal.neg 30), (Sat.Literal.pos 60)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3645), (Sat.Literal.pos 30), (Sat.Literal.neg 60)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3644), (Sat.Literal.neg 30), (Sat.Literal.neg 60), (Sat.Literal.pos 3645)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3644), (Sat.Literal.pos 30), (Sat.Literal.pos 60), (Sat.Literal.pos 3645)] :=
  (lex_7_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3645) = lexBefore s permutation7 29 := by
  exact (positive_lex_of_descriptor s 3645 permutation7 30 (by rfl)).trans ((lex_skipped s permutation7 29 30 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation7 29) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation7 29 by rw [image7_eq]; rfl))

theorem lex_7_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3646) (Sat.Literal.pos 3645) (Sat.Literal.pos 29) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation7 29 (assignment s)
    (Sat.Literal.pos 3646) (Sat.Literal.pos 3645) (Sat.Literal.pos 29) (Sat.Literal.pos 58) (positive_of_descriptor s 3646 (.lex permutation7 29) (by rfl)) (lex_7_29_prefix s) (positive_select s 29) (lex_7_29_image s)

theorem lex_7_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3645), (Sat.Literal.pos 29), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation7 29 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3645) (Sat.Literal.pos 29) (Sat.Literal.pos 58) (lex_7_29_prefix s) (positive_select s 29) (lex_7_29_image s)

theorem lex_7_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3646), (Sat.Literal.pos 3645)] :=
  (lex_7_29_gate s).prop _ (List.Mem.head _)

theorem lex_7_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3646), (Sat.Literal.neg 29), (Sat.Literal.pos 58)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3646), (Sat.Literal.pos 29), (Sat.Literal.neg 58)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3645), (Sat.Literal.neg 29), (Sat.Literal.neg 58), (Sat.Literal.pos 3646)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3645), (Sat.Literal.pos 29), (Sat.Literal.pos 58), (Sat.Literal.pos 3646)] :=
  (lex_7_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3646) = lexBefore s permutation7 28 := by
  exact (positive_lex_of_descriptor s 3646 permutation7 29 (by rfl)).trans ((lex_skipped s permutation7 28 29 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation7 28) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation7 28 by rw [image7_eq]; rfl))

theorem lex_7_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3647) (Sat.Literal.pos 3646) (Sat.Literal.pos 28) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation7 28 (assignment s)
    (Sat.Literal.pos 3647) (Sat.Literal.pos 3646) (Sat.Literal.pos 28) (Sat.Literal.pos 56) (positive_of_descriptor s 3647 (.lex permutation7 28) (by rfl)) (lex_7_28_prefix s) (positive_select s 28) (lex_7_28_image s)

theorem lex_7_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3646), (Sat.Literal.pos 28), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation7 28 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3646) (Sat.Literal.pos 28) (Sat.Literal.pos 56) (lex_7_28_prefix s) (positive_select s 28) (lex_7_28_image s)

theorem lex_7_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3647), (Sat.Literal.pos 3646)] :=
  (lex_7_28_gate s).prop _ (List.Mem.head _)

theorem lex_7_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3647), (Sat.Literal.neg 28), (Sat.Literal.pos 56)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3647), (Sat.Literal.pos 28), (Sat.Literal.neg 56)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3646), (Sat.Literal.neg 28), (Sat.Literal.neg 56), (Sat.Literal.pos 3647)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3646), (Sat.Literal.pos 28), (Sat.Literal.pos 56), (Sat.Literal.pos 3647)] :=
  (lex_7_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3647) = lexBefore s permutation7 27 := by
  exact (positive_lex_of_descriptor s 3647 permutation7 28 (by rfl)).trans ((lex_skipped s permutation7 27 28 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation7 27) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation7 27 by rw [image7_eq]; rfl))

theorem lex_7_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3648) (Sat.Literal.pos 3647) (Sat.Literal.pos 27) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation7 27 (assignment s)
    (Sat.Literal.pos 3648) (Sat.Literal.pos 3647) (Sat.Literal.pos 27) (Sat.Literal.pos 54) (positive_of_descriptor s 3648 (.lex permutation7 27) (by rfl)) (lex_7_27_prefix s) (positive_select s 27) (lex_7_27_image s)

theorem lex_7_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3647), (Sat.Literal.pos 27), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation7 27 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3647) (Sat.Literal.pos 27) (Sat.Literal.pos 54) (lex_7_27_prefix s) (positive_select s 27) (lex_7_27_image s)

theorem lex_7_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3648), (Sat.Literal.pos 3647)] :=
  (lex_7_27_gate s).prop _ (List.Mem.head _)

theorem lex_7_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3648), (Sat.Literal.neg 27), (Sat.Literal.pos 54)] :=
  (lex_7_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3648), (Sat.Literal.pos 27), (Sat.Literal.neg 54)] :=
  (lex_7_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3647), (Sat.Literal.neg 27), (Sat.Literal.neg 54), (Sat.Literal.pos 3648)] :=
  (lex_7_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3647), (Sat.Literal.pos 27), (Sat.Literal.pos 54), (Sat.Literal.pos 3648)] :=
  (lex_7_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3648) = lexBefore s permutation7 26 := by
  exact (positive_lex_of_descriptor s 3648 permutation7 27 (by rfl)).trans ((lex_skipped s permutation7 26 27 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation7 26) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation7 26 by rw [image7_eq]; rfl))

theorem lex_7_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3649) (Sat.Literal.pos 3648) (Sat.Literal.pos 26) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation7 26 (assignment s)
    (Sat.Literal.pos 3649) (Sat.Literal.pos 3648) (Sat.Literal.pos 26) (Sat.Literal.pos 52) (positive_of_descriptor s 3649 (.lex permutation7 26) (by rfl)) (lex_7_26_prefix s) (positive_select s 26) (lex_7_26_image s)

theorem lex_7_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3648), (Sat.Literal.pos 26), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation7 26 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3648) (Sat.Literal.pos 26) (Sat.Literal.pos 52) (lex_7_26_prefix s) (positive_select s 26) (lex_7_26_image s)

theorem lex_7_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3649), (Sat.Literal.pos 3648)] :=
  (lex_7_26_gate s).prop _ (List.Mem.head _)

theorem lex_7_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3649), (Sat.Literal.neg 26), (Sat.Literal.pos 52)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3649), (Sat.Literal.pos 26), (Sat.Literal.neg 52)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3648), (Sat.Literal.neg 26), (Sat.Literal.neg 52), (Sat.Literal.pos 3649)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3648), (Sat.Literal.pos 26), (Sat.Literal.pos 52), (Sat.Literal.pos 3649)] :=
  (lex_7_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3649) = lexBefore s permutation7 25 := by
  exact (positive_lex_of_descriptor s 3649 permutation7 26 (by rfl)).trans ((lex_skipped s permutation7 25 26 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation7 25) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation7 25 by rw [image7_eq]; rfl))

theorem lex_7_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3650) (Sat.Literal.pos 3649) (Sat.Literal.pos 25) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation7 25 (assignment s)
    (Sat.Literal.pos 3650) (Sat.Literal.pos 3649) (Sat.Literal.pos 25) (Sat.Literal.pos 50) (positive_of_descriptor s 3650 (.lex permutation7 25) (by rfl)) (lex_7_25_prefix s) (positive_select s 25) (lex_7_25_image s)

theorem lex_7_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3649), (Sat.Literal.pos 25), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation7 25 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3649) (Sat.Literal.pos 25) (Sat.Literal.pos 50) (lex_7_25_prefix s) (positive_select s 25) (lex_7_25_image s)

theorem lex_7_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3650), (Sat.Literal.pos 3649)] :=
  (lex_7_25_gate s).prop _ (List.Mem.head _)

theorem lex_7_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3650), (Sat.Literal.neg 25), (Sat.Literal.pos 50)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3650), (Sat.Literal.pos 25), (Sat.Literal.neg 50)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3649), (Sat.Literal.neg 25), (Sat.Literal.neg 50), (Sat.Literal.pos 3650)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3649), (Sat.Literal.pos 25), (Sat.Literal.pos 50), (Sat.Literal.pos 3650)] :=
  (lex_7_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3650) = lexBefore s permutation7 24 := by
  exact (positive_lex_of_descriptor s 3650 permutation7 25 (by rfl)).trans ((lex_skipped s permutation7 24 25 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation7 24) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation7 24 by rw [image7_eq]; rfl))

theorem lex_7_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3651) (Sat.Literal.pos 3650) (Sat.Literal.pos 24) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation7 24 (assignment s)
    (Sat.Literal.pos 3651) (Sat.Literal.pos 3650) (Sat.Literal.pos 24) (Sat.Literal.pos 48) (positive_of_descriptor s 3651 (.lex permutation7 24) (by rfl)) (lex_7_24_prefix s) (positive_select s 24) (lex_7_24_image s)

theorem lex_7_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3650), (Sat.Literal.pos 24), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation7 24 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3650) (Sat.Literal.pos 24) (Sat.Literal.pos 48) (lex_7_24_prefix s) (positive_select s 24) (lex_7_24_image s)

theorem lex_7_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3651), (Sat.Literal.pos 3650)] :=
  (lex_7_24_gate s).prop _ (List.Mem.head _)

theorem lex_7_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3651), (Sat.Literal.neg 24), (Sat.Literal.pos 48)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3651), (Sat.Literal.pos 24), (Sat.Literal.neg 48)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3650), (Sat.Literal.neg 24), (Sat.Literal.neg 48), (Sat.Literal.pos 3651)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3650), (Sat.Literal.pos 24), (Sat.Literal.pos 48), (Sat.Literal.pos 3651)] :=
  (lex_7_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3651) = lexBefore s permutation7 23 := by
  exact (positive_lex_of_descriptor s 3651 permutation7 24 (by rfl)).trans ((lex_skipped s permutation7 23 24 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation7 23) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation7 23 by rw [image7_eq]; rfl))

theorem lex_7_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3652) (Sat.Literal.pos 3651) (Sat.Literal.pos 23) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation7 23 (assignment s)
    (Sat.Literal.pos 3652) (Sat.Literal.pos 3651) (Sat.Literal.pos 23) (Sat.Literal.pos 46) (positive_of_descriptor s 3652 (.lex permutation7 23) (by rfl)) (lex_7_23_prefix s) (positive_select s 23) (lex_7_23_image s)

theorem lex_7_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3651), (Sat.Literal.pos 23), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation7 23 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3651) (Sat.Literal.pos 23) (Sat.Literal.pos 46) (lex_7_23_prefix s) (positive_select s 23) (lex_7_23_image s)

theorem lex_7_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3652), (Sat.Literal.pos 3651)] :=
  (lex_7_23_gate s).prop _ (List.Mem.head _)

theorem lex_7_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3652), (Sat.Literal.neg 23), (Sat.Literal.pos 46)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3652), (Sat.Literal.pos 23), (Sat.Literal.neg 46)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3651), (Sat.Literal.neg 23), (Sat.Literal.neg 46), (Sat.Literal.pos 3652)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3651), (Sat.Literal.pos 23), (Sat.Literal.pos 46), (Sat.Literal.pos 3652)] :=
  (lex_7_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3652) = lexBefore s permutation7 22 := by
  exact (positive_lex_of_descriptor s 3652 permutation7 23 (by rfl)).trans ((lex_skipped s permutation7 22 23 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 44) = s (permuteMask permutation7 22) := by
  exact (positive_select s 44).trans (congrArg s (show (44 : Fin 256) = permuteMask permutation7 22 by rw [image7_eq]; rfl))

theorem lex_7_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3653) (Sat.Literal.pos 3652) (Sat.Literal.pos 22) (Sat.Literal.pos 44)) := by
  exact equality_gate s permutation7 22 (assignment s)
    (Sat.Literal.pos 3653) (Sat.Literal.pos 3652) (Sat.Literal.pos 22) (Sat.Literal.pos 44) (positive_of_descriptor s 3653 (.lex permutation7 22) (by rfl)) (lex_7_22_prefix s) (positive_select s 22) (lex_7_22_image s)

theorem lex_7_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3652), (Sat.Literal.pos 22), (Sat.Literal.neg 44)] := by
  exact comparison_gate s permutation7 22 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3652) (Sat.Literal.pos 22) (Sat.Literal.pos 44) (lex_7_22_prefix s) (positive_select s 22) (lex_7_22_image s)

theorem lex_7_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3653), (Sat.Literal.pos 3652)] :=
  (lex_7_22_gate s).prop _ (List.Mem.head _)

theorem lex_7_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3653), (Sat.Literal.neg 22), (Sat.Literal.pos 44)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3653), (Sat.Literal.pos 22), (Sat.Literal.neg 44)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3652), (Sat.Literal.neg 22), (Sat.Literal.neg 44), (Sat.Literal.pos 3653)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3652), (Sat.Literal.pos 22), (Sat.Literal.pos 44), (Sat.Literal.pos 3653)] :=
  (lex_7_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3653) = lexBefore s permutation7 21 := by
  exact (positive_lex_of_descriptor s 3653 permutation7 22 (by rfl)).trans ((lex_skipped s permutation7 21 22 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation7 21) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation7 21 by rw [image7_eq]; rfl))

theorem lex_7_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3654) (Sat.Literal.pos 3653) (Sat.Literal.pos 21) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation7 21 (assignment s)
    (Sat.Literal.pos 3654) (Sat.Literal.pos 3653) (Sat.Literal.pos 21) (Sat.Literal.pos 42) (positive_of_descriptor s 3654 (.lex permutation7 21) (by rfl)) (lex_7_21_prefix s) (positive_select s 21) (lex_7_21_image s)

theorem lex_7_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3653), (Sat.Literal.pos 21), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation7 21 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3653) (Sat.Literal.pos 21) (Sat.Literal.pos 42) (lex_7_21_prefix s) (positive_select s 21) (lex_7_21_image s)

theorem lex_7_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3654), (Sat.Literal.pos 3653)] :=
  (lex_7_21_gate s).prop _ (List.Mem.head _)

theorem lex_7_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3654), (Sat.Literal.neg 21), (Sat.Literal.pos 42)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3654), (Sat.Literal.pos 21), (Sat.Literal.neg 42)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3653), (Sat.Literal.neg 21), (Sat.Literal.neg 42), (Sat.Literal.pos 3654)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3653), (Sat.Literal.pos 21), (Sat.Literal.pos 42), (Sat.Literal.pos 3654)] :=
  (lex_7_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3654) = lexBefore s permutation7 20 := by
  exact (positive_lex_of_descriptor s 3654 permutation7 21 (by rfl)).trans ((lex_skipped s permutation7 20 21 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation7 20) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation7 20 by rw [image7_eq]; rfl))

theorem lex_7_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3655) (Sat.Literal.pos 3654) (Sat.Literal.pos 20) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation7 20 (assignment s)
    (Sat.Literal.pos 3655) (Sat.Literal.pos 3654) (Sat.Literal.pos 20) (Sat.Literal.pos 40) (positive_of_descriptor s 3655 (.lex permutation7 20) (by rfl)) (lex_7_20_prefix s) (positive_select s 20) (lex_7_20_image s)

theorem lex_7_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3654), (Sat.Literal.pos 20), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation7 20 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3654) (Sat.Literal.pos 20) (Sat.Literal.pos 40) (lex_7_20_prefix s) (positive_select s 20) (lex_7_20_image s)

theorem lex_7_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3655), (Sat.Literal.pos 3654)] :=
  (lex_7_20_gate s).prop _ (List.Mem.head _)

theorem lex_7_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3655), (Sat.Literal.neg 20), (Sat.Literal.pos 40)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3655), (Sat.Literal.pos 20), (Sat.Literal.neg 40)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3654), (Sat.Literal.neg 20), (Sat.Literal.neg 40), (Sat.Literal.pos 3655)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3654), (Sat.Literal.pos 20), (Sat.Literal.pos 40), (Sat.Literal.pos 3655)] :=
  (lex_7_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3655) = lexBefore s permutation7 19 := by
  exact (positive_lex_of_descriptor s 3655 permutation7 20 (by rfl)).trans ((lex_skipped s permutation7 19 20 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation7 19) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation7 19 by rw [image7_eq]; rfl))

theorem lex_7_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3656) (Sat.Literal.pos 3655) (Sat.Literal.pos 19) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation7 19 (assignment s)
    (Sat.Literal.pos 3656) (Sat.Literal.pos 3655) (Sat.Literal.pos 19) (Sat.Literal.pos 38) (positive_of_descriptor s 3656 (.lex permutation7 19) (by rfl)) (lex_7_19_prefix s) (positive_select s 19) (lex_7_19_image s)

theorem lex_7_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3655), (Sat.Literal.pos 19), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation7 19 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3655) (Sat.Literal.pos 19) (Sat.Literal.pos 38) (lex_7_19_prefix s) (positive_select s 19) (lex_7_19_image s)

theorem lex_7_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3656), (Sat.Literal.pos 3655)] :=
  (lex_7_19_gate s).prop _ (List.Mem.head _)

theorem lex_7_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3656), (Sat.Literal.neg 19), (Sat.Literal.pos 38)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3656), (Sat.Literal.pos 19), (Sat.Literal.neg 38)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3655), (Sat.Literal.neg 19), (Sat.Literal.neg 38), (Sat.Literal.pos 3656)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3655), (Sat.Literal.pos 19), (Sat.Literal.pos 38), (Sat.Literal.pos 3656)] :=
  (lex_7_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3656) = lexBefore s permutation7 18 := by
  exact (positive_lex_of_descriptor s 3656 permutation7 19 (by rfl)).trans ((lex_skipped s permutation7 18 19 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation7 18) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation7 18 by rw [image7_eq]; rfl))

theorem lex_7_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3657) (Sat.Literal.pos 3656) (Sat.Literal.pos 18) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation7 18 (assignment s)
    (Sat.Literal.pos 3657) (Sat.Literal.pos 3656) (Sat.Literal.pos 18) (Sat.Literal.pos 36) (positive_of_descriptor s 3657 (.lex permutation7 18) (by rfl)) (lex_7_18_prefix s) (positive_select s 18) (lex_7_18_image s)

theorem lex_7_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3656), (Sat.Literal.pos 18), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation7 18 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3656) (Sat.Literal.pos 18) (Sat.Literal.pos 36) (lex_7_18_prefix s) (positive_select s 18) (lex_7_18_image s)

theorem lex_7_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3657), (Sat.Literal.pos 3656)] :=
  (lex_7_18_gate s).prop _ (List.Mem.head _)

theorem lex_7_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3657), (Sat.Literal.neg 18), (Sat.Literal.pos 36)] :=
  (lex_7_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3657), (Sat.Literal.pos 18), (Sat.Literal.neg 36)] :=
  (lex_7_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3656), (Sat.Literal.neg 18), (Sat.Literal.neg 36), (Sat.Literal.pos 3657)] :=
  (lex_7_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3656), (Sat.Literal.pos 18), (Sat.Literal.pos 36), (Sat.Literal.pos 3657)] :=
  (lex_7_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3657) = lexBefore s permutation7 17 := by
  exact (positive_lex_of_descriptor s 3657 permutation7 18 (by rfl)).trans ((lex_skipped s permutation7 17 18 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation7 17) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation7 17 by rw [image7_eq]; rfl))

theorem lex_7_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3658) (Sat.Literal.pos 3657) (Sat.Literal.pos 17) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation7 17 (assignment s)
    (Sat.Literal.pos 3658) (Sat.Literal.pos 3657) (Sat.Literal.pos 17) (Sat.Literal.pos 34) (positive_of_descriptor s 3658 (.lex permutation7 17) (by rfl)) (lex_7_17_prefix s) (positive_select s 17) (lex_7_17_image s)

theorem lex_7_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3657), (Sat.Literal.pos 17), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation7 17 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3657) (Sat.Literal.pos 17) (Sat.Literal.pos 34) (lex_7_17_prefix s) (positive_select s 17) (lex_7_17_image s)

theorem lex_7_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3658), (Sat.Literal.pos 3657)] :=
  (lex_7_17_gate s).prop _ (List.Mem.head _)

theorem lex_7_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3658), (Sat.Literal.neg 17), (Sat.Literal.pos 34)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3658), (Sat.Literal.pos 17), (Sat.Literal.neg 34)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3657), (Sat.Literal.neg 17), (Sat.Literal.neg 34), (Sat.Literal.pos 3658)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3657), (Sat.Literal.pos 17), (Sat.Literal.pos 34), (Sat.Literal.pos 3658)] :=
  (lex_7_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3658) = lexBefore s permutation7 16 := by
  exact (positive_lex_of_descriptor s 3658 permutation7 17 (by rfl)).trans ((lex_skipped s permutation7 16 17 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation7 16) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation7 16 by rw [image7_eq]; rfl))

theorem lex_7_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3659) (Sat.Literal.pos 3658) (Sat.Literal.pos 16) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation7 16 (assignment s)
    (Sat.Literal.pos 3659) (Sat.Literal.pos 3658) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (positive_of_descriptor s 3659 (.lex permutation7 16) (by rfl)) (lex_7_16_prefix s) (positive_select s 16) (lex_7_16_image s)

theorem lex_7_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3658), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation7 16 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3658) (Sat.Literal.pos 16) (Sat.Literal.pos 32) (lex_7_16_prefix s) (positive_select s 16) (lex_7_16_image s)

theorem lex_7_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3659), (Sat.Literal.pos 3658)] :=
  (lex_7_16_gate s).prop _ (List.Mem.head _)

theorem lex_7_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3659), (Sat.Literal.neg 16), (Sat.Literal.pos 32)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3659), (Sat.Literal.pos 16), (Sat.Literal.neg 32)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3658), (Sat.Literal.neg 16), (Sat.Literal.neg 32), (Sat.Literal.pos 3659)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3658), (Sat.Literal.pos 16), (Sat.Literal.pos 32), (Sat.Literal.pos 3659)] :=
  (lex_7_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3659) = lexBefore s permutation7 15 := by
  exact (positive_lex_of_descriptor s 3659 permutation7 16 (by rfl)).trans ((lex_skipped s permutation7 15 16 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation7 15) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation7 15 by rw [image7_eq]; rfl))

theorem lex_7_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3660) (Sat.Literal.pos 3659) (Sat.Literal.pos 15) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation7 15 (assignment s)
    (Sat.Literal.pos 3660) (Sat.Literal.pos 3659) (Sat.Literal.pos 15) (Sat.Literal.pos 30) (positive_of_descriptor s 3660 (.lex permutation7 15) (by rfl)) (lex_7_15_prefix s) (positive_select s 15) (lex_7_15_image s)

theorem lex_7_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3659), (Sat.Literal.pos 15), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation7 15 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3659) (Sat.Literal.pos 15) (Sat.Literal.pos 30) (lex_7_15_prefix s) (positive_select s 15) (lex_7_15_image s)

theorem lex_7_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3660), (Sat.Literal.pos 3659)] :=
  (lex_7_15_gate s).prop _ (List.Mem.head _)

theorem lex_7_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3660), (Sat.Literal.neg 15), (Sat.Literal.pos 30)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3660), (Sat.Literal.pos 15), (Sat.Literal.neg 30)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3659), (Sat.Literal.neg 15), (Sat.Literal.neg 30), (Sat.Literal.pos 3660)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3659), (Sat.Literal.pos 15), (Sat.Literal.pos 30), (Sat.Literal.pos 3660)] :=
  (lex_7_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3660) = lexBefore s permutation7 14 := by
  exact (positive_lex_of_descriptor s 3660 permutation7 15 (by rfl)).trans ((lex_skipped s permutation7 14 15 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation7 14) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation7 14 by rw [image7_eq]; rfl))

theorem lex_7_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3661) (Sat.Literal.pos 3660) (Sat.Literal.pos 14) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation7 14 (assignment s)
    (Sat.Literal.pos 3661) (Sat.Literal.pos 3660) (Sat.Literal.pos 14) (Sat.Literal.pos 28) (positive_of_descriptor s 3661 (.lex permutation7 14) (by rfl)) (lex_7_14_prefix s) (positive_select s 14) (lex_7_14_image s)

theorem lex_7_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3660), (Sat.Literal.pos 14), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation7 14 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3660) (Sat.Literal.pos 14) (Sat.Literal.pos 28) (lex_7_14_prefix s) (positive_select s 14) (lex_7_14_image s)

theorem lex_7_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3661), (Sat.Literal.pos 3660)] :=
  (lex_7_14_gate s).prop _ (List.Mem.head _)

theorem lex_7_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3661), (Sat.Literal.neg 14), (Sat.Literal.pos 28)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3661), (Sat.Literal.pos 14), (Sat.Literal.neg 28)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3660), (Sat.Literal.neg 14), (Sat.Literal.neg 28), (Sat.Literal.pos 3661)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3660), (Sat.Literal.pos 14), (Sat.Literal.pos 28), (Sat.Literal.pos 3661)] :=
  (lex_7_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3661) = lexBefore s permutation7 13 := by
  exact (positive_lex_of_descriptor s 3661 permutation7 14 (by rfl)).trans ((lex_skipped s permutation7 13 14 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation7 13) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation7 13 by rw [image7_eq]; rfl))

theorem lex_7_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3662) (Sat.Literal.pos 3661) (Sat.Literal.pos 13) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation7 13 (assignment s)
    (Sat.Literal.pos 3662) (Sat.Literal.pos 3661) (Sat.Literal.pos 13) (Sat.Literal.pos 26) (positive_of_descriptor s 3662 (.lex permutation7 13) (by rfl)) (lex_7_13_prefix s) (positive_select s 13) (lex_7_13_image s)

theorem lex_7_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3661), (Sat.Literal.pos 13), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation7 13 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3661) (Sat.Literal.pos 13) (Sat.Literal.pos 26) (lex_7_13_prefix s) (positive_select s 13) (lex_7_13_image s)

theorem lex_7_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3662), (Sat.Literal.pos 3661)] :=
  (lex_7_13_gate s).prop _ (List.Mem.head _)

theorem lex_7_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3662), (Sat.Literal.neg 13), (Sat.Literal.pos 26)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3662), (Sat.Literal.pos 13), (Sat.Literal.neg 26)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3661), (Sat.Literal.neg 13), (Sat.Literal.neg 26), (Sat.Literal.pos 3662)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3661), (Sat.Literal.pos 13), (Sat.Literal.pos 26), (Sat.Literal.pos 3662)] :=
  (lex_7_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3662) = lexBefore s permutation7 12 := by
  exact (positive_lex_of_descriptor s 3662 permutation7 13 (by rfl)).trans ((lex_skipped s permutation7 12 13 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation7 12) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation7 12 by rw [image7_eq]; rfl))

theorem lex_7_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3663) (Sat.Literal.pos 3662) (Sat.Literal.pos 12) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation7 12 (assignment s)
    (Sat.Literal.pos 3663) (Sat.Literal.pos 3662) (Sat.Literal.pos 12) (Sat.Literal.pos 24) (positive_of_descriptor s 3663 (.lex permutation7 12) (by rfl)) (lex_7_12_prefix s) (positive_select s 12) (lex_7_12_image s)

theorem lex_7_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3662), (Sat.Literal.pos 12), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation7 12 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3662) (Sat.Literal.pos 12) (Sat.Literal.pos 24) (lex_7_12_prefix s) (positive_select s 12) (lex_7_12_image s)

theorem lex_7_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3663), (Sat.Literal.pos 3662)] :=
  (lex_7_12_gate s).prop _ (List.Mem.head _)

theorem lex_7_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3663), (Sat.Literal.neg 12), (Sat.Literal.pos 24)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3663), (Sat.Literal.pos 12), (Sat.Literal.neg 24)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3662), (Sat.Literal.neg 12), (Sat.Literal.neg 24), (Sat.Literal.pos 3663)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3662), (Sat.Literal.pos 12), (Sat.Literal.pos 24), (Sat.Literal.pos 3663)] :=
  (lex_7_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3663) = lexBefore s permutation7 11 := by
  exact (positive_lex_of_descriptor s 3663 permutation7 12 (by rfl)).trans ((lex_skipped s permutation7 11 12 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation7 11) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation7 11 by rw [image7_eq]; rfl))

theorem lex_7_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3664) (Sat.Literal.pos 3663) (Sat.Literal.pos 11) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation7 11 (assignment s)
    (Sat.Literal.pos 3664) (Sat.Literal.pos 3663) (Sat.Literal.pos 11) (Sat.Literal.pos 22) (positive_of_descriptor s 3664 (.lex permutation7 11) (by rfl)) (lex_7_11_prefix s) (positive_select s 11) (lex_7_11_image s)

theorem lex_7_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3663), (Sat.Literal.pos 11), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation7 11 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3663) (Sat.Literal.pos 11) (Sat.Literal.pos 22) (lex_7_11_prefix s) (positive_select s 11) (lex_7_11_image s)

theorem lex_7_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3664), (Sat.Literal.pos 3663)] :=
  (lex_7_11_gate s).prop _ (List.Mem.head _)

theorem lex_7_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3664), (Sat.Literal.neg 11), (Sat.Literal.pos 22)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3664), (Sat.Literal.pos 11), (Sat.Literal.neg 22)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3663), (Sat.Literal.neg 11), (Sat.Literal.neg 22), (Sat.Literal.pos 3664)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3663), (Sat.Literal.pos 11), (Sat.Literal.pos 22), (Sat.Literal.pos 3664)] :=
  (lex_7_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3664) = lexBefore s permutation7 10 := by
  exact (positive_lex_of_descriptor s 3664 permutation7 11 (by rfl)).trans ((lex_skipped s permutation7 10 11 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation7 10) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation7 10 by rw [image7_eq]; rfl))

theorem lex_7_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3665) (Sat.Literal.pos 3664) (Sat.Literal.pos 10) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation7 10 (assignment s)
    (Sat.Literal.pos 3665) (Sat.Literal.pos 3664) (Sat.Literal.pos 10) (Sat.Literal.pos 20) (positive_of_descriptor s 3665 (.lex permutation7 10) (by rfl)) (lex_7_10_prefix s) (positive_select s 10) (lex_7_10_image s)

theorem lex_7_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3664), (Sat.Literal.pos 10), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation7 10 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3664) (Sat.Literal.pos 10) (Sat.Literal.pos 20) (lex_7_10_prefix s) (positive_select s 10) (lex_7_10_image s)

theorem lex_7_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3665), (Sat.Literal.pos 3664)] :=
  (lex_7_10_gate s).prop _ (List.Mem.head _)

theorem lex_7_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3665), (Sat.Literal.neg 10), (Sat.Literal.pos 20)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3665), (Sat.Literal.pos 10), (Sat.Literal.neg 20)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3664), (Sat.Literal.neg 10), (Sat.Literal.neg 20), (Sat.Literal.pos 3665)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3664), (Sat.Literal.pos 10), (Sat.Literal.pos 20), (Sat.Literal.pos 3665)] :=
  (lex_7_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3665) = lexBefore s permutation7 9 := by
  exact (positive_lex_of_descriptor s 3665 permutation7 10 (by rfl)).trans ((lex_skipped s permutation7 9 10 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation7 9) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation7 9 by rw [image7_eq]; rfl))

theorem lex_7_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3666) (Sat.Literal.pos 3665) (Sat.Literal.pos 9) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation7 9 (assignment s)
    (Sat.Literal.pos 3666) (Sat.Literal.pos 3665) (Sat.Literal.pos 9) (Sat.Literal.pos 18) (positive_of_descriptor s 3666 (.lex permutation7 9) (by rfl)) (lex_7_9_prefix s) (positive_select s 9) (lex_7_9_image s)

theorem lex_7_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3665), (Sat.Literal.pos 9), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation7 9 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3665) (Sat.Literal.pos 9) (Sat.Literal.pos 18) (lex_7_9_prefix s) (positive_select s 9) (lex_7_9_image s)

theorem lex_7_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3666), (Sat.Literal.pos 3665)] :=
  (lex_7_9_gate s).prop _ (List.Mem.head _)

theorem lex_7_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3666), (Sat.Literal.neg 9), (Sat.Literal.pos 18)] :=
  (lex_7_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3666), (Sat.Literal.pos 9), (Sat.Literal.neg 18)] :=
  (lex_7_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3665), (Sat.Literal.neg 9), (Sat.Literal.neg 18), (Sat.Literal.pos 3666)] :=
  (lex_7_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3665), (Sat.Literal.pos 9), (Sat.Literal.pos 18), (Sat.Literal.pos 3666)] :=
  (lex_7_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3666) = lexBefore s permutation7 8 := by
  exact (positive_lex_of_descriptor s 3666 permutation7 9 (by rfl)).trans ((lex_skipped s permutation7 8 9 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation7 8) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation7 8 by rw [image7_eq]; rfl))

theorem lex_7_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3667) (Sat.Literal.pos 3666) (Sat.Literal.pos 8) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation7 8 (assignment s)
    (Sat.Literal.pos 3667) (Sat.Literal.pos 3666) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (positive_of_descriptor s 3667 (.lex permutation7 8) (by rfl)) (lex_7_8_prefix s) (positive_select s 8) (lex_7_8_image s)

theorem lex_7_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3666), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation7 8 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3666) (Sat.Literal.pos 8) (Sat.Literal.pos 16) (lex_7_8_prefix s) (positive_select s 8) (lex_7_8_image s)

theorem lex_7_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3667), (Sat.Literal.pos 3666)] :=
  (lex_7_8_gate s).prop _ (List.Mem.head _)

theorem lex_7_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3667), (Sat.Literal.neg 8), (Sat.Literal.pos 16)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3667), (Sat.Literal.pos 8), (Sat.Literal.neg 16)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3666), (Sat.Literal.neg 8), (Sat.Literal.neg 16), (Sat.Literal.pos 3667)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3666), (Sat.Literal.pos 8), (Sat.Literal.pos 16), (Sat.Literal.pos 3667)] :=
  (lex_7_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3667) = lexBefore s permutation7 7 := by
  exact (positive_lex_of_descriptor s 3667 permutation7 8 (by rfl)).trans ((lex_skipped s permutation7 7 8 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation7 7) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation7 7 by rw [image7_eq]; rfl))

theorem lex_7_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3668) (Sat.Literal.pos 3667) (Sat.Literal.pos 7) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation7 7 (assignment s)
    (Sat.Literal.pos 3668) (Sat.Literal.pos 3667) (Sat.Literal.pos 7) (Sat.Literal.pos 14) (positive_of_descriptor s 3668 (.lex permutation7 7) (by rfl)) (lex_7_7_prefix s) (positive_select s 7) (lex_7_7_image s)

theorem lex_7_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3667), (Sat.Literal.pos 7), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation7 7 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3667) (Sat.Literal.pos 7) (Sat.Literal.pos 14) (lex_7_7_prefix s) (positive_select s 7) (lex_7_7_image s)

theorem lex_7_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3668), (Sat.Literal.pos 3667)] :=
  (lex_7_7_gate s).prop _ (List.Mem.head _)

theorem lex_7_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3668), (Sat.Literal.neg 7), (Sat.Literal.pos 14)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3668), (Sat.Literal.pos 7), (Sat.Literal.neg 14)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3667), (Sat.Literal.neg 7), (Sat.Literal.neg 14), (Sat.Literal.pos 3668)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3667), (Sat.Literal.pos 7), (Sat.Literal.pos 14), (Sat.Literal.pos 3668)] :=
  (lex_7_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3668) = lexBefore s permutation7 6 := by
  exact (positive_lex_of_descriptor s 3668 permutation7 7 (by rfl)).trans ((lex_skipped s permutation7 6 7 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation7 6) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation7 6 by rw [image7_eq]; rfl))

theorem lex_7_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3669) (Sat.Literal.pos 3668) (Sat.Literal.pos 6) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation7 6 (assignment s)
    (Sat.Literal.pos 3669) (Sat.Literal.pos 3668) (Sat.Literal.pos 6) (Sat.Literal.pos 12) (positive_of_descriptor s 3669 (.lex permutation7 6) (by rfl)) (lex_7_6_prefix s) (positive_select s 6) (lex_7_6_image s)

theorem lex_7_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3668), (Sat.Literal.pos 6), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation7 6 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3668) (Sat.Literal.pos 6) (Sat.Literal.pos 12) (lex_7_6_prefix s) (positive_select s 6) (lex_7_6_image s)

theorem lex_7_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3669), (Sat.Literal.pos 3668)] :=
  (lex_7_6_gate s).prop _ (List.Mem.head _)

theorem lex_7_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3669), (Sat.Literal.neg 6), (Sat.Literal.pos 12)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3669), (Sat.Literal.pos 6), (Sat.Literal.neg 12)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3668), (Sat.Literal.neg 6), (Sat.Literal.neg 12), (Sat.Literal.pos 3669)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3668), (Sat.Literal.pos 6), (Sat.Literal.pos 12), (Sat.Literal.pos 3669)] :=
  (lex_7_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3669) = lexBefore s permutation7 5 := by
  exact (positive_lex_of_descriptor s 3669 permutation7 6 (by rfl)).trans ((lex_skipped s permutation7 5 6 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation7 5) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation7 5 by rw [image7_eq]; rfl))

theorem lex_7_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3670) (Sat.Literal.pos 3669) (Sat.Literal.pos 5) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation7 5 (assignment s)
    (Sat.Literal.pos 3670) (Sat.Literal.pos 3669) (Sat.Literal.pos 5) (Sat.Literal.pos 10) (positive_of_descriptor s 3670 (.lex permutation7 5) (by rfl)) (lex_7_5_prefix s) (positive_select s 5) (lex_7_5_image s)

theorem lex_7_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3669), (Sat.Literal.pos 5), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation7 5 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3669) (Sat.Literal.pos 5) (Sat.Literal.pos 10) (lex_7_5_prefix s) (positive_select s 5) (lex_7_5_image s)

theorem lex_7_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3670), (Sat.Literal.pos 3669)] :=
  (lex_7_5_gate s).prop _ (List.Mem.head _)

theorem lex_7_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3670), (Sat.Literal.neg 5), (Sat.Literal.pos 10)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3670), (Sat.Literal.pos 5), (Sat.Literal.neg 10)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3669), (Sat.Literal.neg 5), (Sat.Literal.neg 10), (Sat.Literal.pos 3670)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3669), (Sat.Literal.pos 5), (Sat.Literal.pos 10), (Sat.Literal.pos 3670)] :=
  (lex_7_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3670) = lexBefore s permutation7 4 := by
  exact (positive_lex_of_descriptor s 3670 permutation7 5 (by rfl)).trans ((lex_skipped s permutation7 4 5 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation7 4) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation7 4 by rw [image7_eq]; rfl))

theorem lex_7_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3671) (Sat.Literal.pos 3670) (Sat.Literal.pos 4) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation7 4 (assignment s)
    (Sat.Literal.pos 3671) (Sat.Literal.pos 3670) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (positive_of_descriptor s 3671 (.lex permutation7 4) (by rfl)) (lex_7_4_prefix s) (positive_select s 4) (lex_7_4_image s)

theorem lex_7_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3670), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation7 4 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3670) (Sat.Literal.pos 4) (Sat.Literal.pos 8) (lex_7_4_prefix s) (positive_select s 4) (lex_7_4_image s)

theorem lex_7_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3671), (Sat.Literal.pos 3670)] :=
  (lex_7_4_gate s).prop _ (List.Mem.head _)

theorem lex_7_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3671), (Sat.Literal.neg 4), (Sat.Literal.pos 8)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3671), (Sat.Literal.pos 4), (Sat.Literal.neg 8)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3670), (Sat.Literal.neg 4), (Sat.Literal.neg 8), (Sat.Literal.pos 3671)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3670), (Sat.Literal.pos 4), (Sat.Literal.pos 8), (Sat.Literal.pos 3671)] :=
  (lex_7_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3671) = lexBefore s permutation7 3 := by
  exact (positive_lex_of_descriptor s 3671 permutation7 4 (by rfl)).trans ((lex_skipped s permutation7 3 4 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation7 3) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation7 3 by rw [image7_eq]; rfl))

theorem lex_7_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3672) (Sat.Literal.pos 3671) (Sat.Literal.pos 3) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation7 3 (assignment s)
    (Sat.Literal.pos 3672) (Sat.Literal.pos 3671) (Sat.Literal.pos 3) (Sat.Literal.pos 6) (positive_of_descriptor s 3672 (.lex permutation7 3) (by rfl)) (lex_7_3_prefix s) (positive_select s 3) (lex_7_3_image s)

theorem lex_7_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3671), (Sat.Literal.pos 3), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation7 3 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3671) (Sat.Literal.pos 3) (Sat.Literal.pos 6) (lex_7_3_prefix s) (positive_select s 3) (lex_7_3_image s)

theorem lex_7_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3672), (Sat.Literal.pos 3671)] :=
  (lex_7_3_gate s).prop _ (List.Mem.head _)

theorem lex_7_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3672), (Sat.Literal.neg 3), (Sat.Literal.pos 6)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3672), (Sat.Literal.pos 3), (Sat.Literal.neg 6)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3671), (Sat.Literal.neg 3), (Sat.Literal.neg 6), (Sat.Literal.pos 3672)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3671), (Sat.Literal.pos 3), (Sat.Literal.pos 6), (Sat.Literal.pos 3672)] :=
  (lex_7_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3672) = lexBefore s permutation7 2 := by
  exact (positive_lex_of_descriptor s 3672 permutation7 3 (by rfl)).trans ((lex_skipped s permutation7 2 3 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation7 2) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation7 2 by rw [image7_eq]; rfl))

theorem lex_7_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3673) (Sat.Literal.pos 3672) (Sat.Literal.pos 2) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation7 2 (assignment s)
    (Sat.Literal.pos 3673) (Sat.Literal.pos 3672) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (positive_of_descriptor s 3673 (.lex permutation7 2) (by rfl)) (lex_7_2_prefix s) (positive_select s 2) (lex_7_2_image s)

theorem lex_7_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3672), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation7 2 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3672) (Sat.Literal.pos 2) (Sat.Literal.pos 4) (lex_7_2_prefix s) (positive_select s 2) (lex_7_2_image s)

theorem lex_7_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3673), (Sat.Literal.pos 3672)] :=
  (lex_7_2_gate s).prop _ (List.Mem.head _)

theorem lex_7_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3673), (Sat.Literal.neg 2), (Sat.Literal.pos 4)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3673), (Sat.Literal.pos 2), (Sat.Literal.neg 4)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3672), (Sat.Literal.neg 2), (Sat.Literal.neg 4), (Sat.Literal.pos 3673)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3672), (Sat.Literal.pos 2), (Sat.Literal.pos 4), (Sat.Literal.pos 3673)] :=
  (lex_7_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3673) = lexBefore s permutation7 1 := by
  exact (positive_lex_of_descriptor s 3673 permutation7 2 (by rfl)).trans ((lex_skipped s permutation7 1 2 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation7 1) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation7 1 by rw [image7_eq]; rfl))

theorem lex_7_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3674) (Sat.Literal.pos 3673) (Sat.Literal.pos 1) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation7 1 (assignment s)
    (Sat.Literal.pos 3674) (Sat.Literal.pos 3673) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (positive_of_descriptor s 3674 (.lex permutation7 1) (by rfl)) (lex_7_1_prefix s) (positive_select s 1) (lex_7_1_image s)

theorem lex_7_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3673), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation7 1 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3673) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (lex_7_1_prefix s) (positive_select s 1) (lex_7_1_image s)

theorem lex_7_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3674), (Sat.Literal.pos 3673)] :=
  (lex_7_1_gate s).prop _ (List.Mem.head _)

theorem lex_7_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3674), (Sat.Literal.neg 1), (Sat.Literal.pos 2)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3674), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3673), (Sat.Literal.neg 1), (Sat.Literal.neg 2), (Sat.Literal.pos 3674)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3673), (Sat.Literal.pos 1), (Sat.Literal.pos 2), (Sat.Literal.pos 3674)] :=
  (lex_7_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation8 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation8 254 (by intro j hj; rw [image8_eq]; exact fixedOnRange_spec image8 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_8_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation8 254) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation8 254 by rw [image8_eq]; rfl))

theorem lex_8_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3675) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation8 254 (assignment s)
    (Sat.Literal.pos 3675) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 251) (positive_of_descriptor s 3675 (.lex permutation8 254) (by rfl)) (lex_8_254_prefix s) (positive_select s 254) (lex_8_254_image s)

theorem lex_8_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation8 254 (hmax permutation8) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 251) (lex_8_254_prefix s) (positive_select s 254) (lex_8_254_image s)

theorem lex_8_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3675), (Sat.Literal.neg 256)] :=
  (lex_8_254_gate s).prop _ (List.Mem.head _)

theorem lex_8_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3675), (Sat.Literal.neg 254), (Sat.Literal.pos 251)] :=
  (lex_8_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3675), (Sat.Literal.pos 254), (Sat.Literal.neg 251)] :=
  (lex_8_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 251), (Sat.Literal.pos 3675)] :=
  (lex_8_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 251), (Sat.Literal.pos 3675)] :=
  (lex_8_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3675) = lexBefore s permutation8 253 := by
  exact (positive_lex_of_descriptor s 3675 permutation8 254 (by rfl)).trans ((lex_skipped s permutation8 253 254 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation8 253) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation8 253 by rw [image8_eq]; rfl))

theorem lex_8_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3676) (Sat.Literal.pos 3675) (Sat.Literal.pos 253) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation8 253 (assignment s)
    (Sat.Literal.pos 3676) (Sat.Literal.pos 3675) (Sat.Literal.pos 253) (Sat.Literal.pos 247) (positive_of_descriptor s 3676 (.lex permutation8 253) (by rfl)) (lex_8_253_prefix s) (positive_select s 253) (lex_8_253_image s)

theorem lex_8_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3675), (Sat.Literal.pos 253), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation8 253 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3675) (Sat.Literal.pos 253) (Sat.Literal.pos 247) (lex_8_253_prefix s) (positive_select s 253) (lex_8_253_image s)

theorem lex_8_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3676), (Sat.Literal.pos 3675)] :=
  (lex_8_253_gate s).prop _ (List.Mem.head _)

theorem lex_8_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3676), (Sat.Literal.neg 253), (Sat.Literal.pos 247)] :=
  (lex_8_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3676), (Sat.Literal.pos 253), (Sat.Literal.neg 247)] :=
  (lex_8_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3675), (Sat.Literal.neg 253), (Sat.Literal.neg 247), (Sat.Literal.pos 3676)] :=
  (lex_8_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3675), (Sat.Literal.pos 253), (Sat.Literal.pos 247), (Sat.Literal.pos 3676)] :=
  (lex_8_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3676) = lexBefore s permutation8 252 := by
  exact (positive_lex_of_descriptor s 3676 permutation8 253 (by rfl)).trans ((lex_skipped s permutation8 252 253 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation8 252) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation8 252 by rw [image8_eq]; rfl))

theorem lex_8_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3677) (Sat.Literal.pos 3676) (Sat.Literal.pos 252) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation8 252 (assignment s)
    (Sat.Literal.pos 3677) (Sat.Literal.pos 3676) (Sat.Literal.pos 252) (Sat.Literal.pos 243) (positive_of_descriptor s 3677 (.lex permutation8 252) (by rfl)) (lex_8_252_prefix s) (positive_select s 252) (lex_8_252_image s)

theorem lex_8_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3676), (Sat.Literal.pos 252), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation8 252 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3676) (Sat.Literal.pos 252) (Sat.Literal.pos 243) (lex_8_252_prefix s) (positive_select s 252) (lex_8_252_image s)

theorem lex_8_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3677), (Sat.Literal.pos 3676)] :=
  (lex_8_252_gate s).prop _ (List.Mem.head _)

theorem lex_8_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3677), (Sat.Literal.neg 252), (Sat.Literal.pos 243)] :=
  (lex_8_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3677), (Sat.Literal.pos 252), (Sat.Literal.neg 243)] :=
  (lex_8_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3676), (Sat.Literal.neg 252), (Sat.Literal.neg 243), (Sat.Literal.pos 3677)] :=
  (lex_8_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3676), (Sat.Literal.pos 252), (Sat.Literal.pos 243), (Sat.Literal.pos 3677)] :=
  (lex_8_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3677) = lexBefore s permutation8 251 := by
  exact (positive_lex_of_descriptor s 3677 permutation8 252 (by rfl)).trans ((lex_skipped s permutation8 251 252 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation8 251) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation8 251 by rw [image8_eq]; rfl))

theorem lex_8_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3678) (Sat.Literal.pos 3677) (Sat.Literal.pos 251) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation8 251 (assignment s)
    (Sat.Literal.pos 3678) (Sat.Literal.pos 3677) (Sat.Literal.pos 251) (Sat.Literal.pos 239) (positive_of_descriptor s 3678 (.lex permutation8 251) (by rfl)) (lex_8_251_prefix s) (positive_select s 251) (lex_8_251_image s)

theorem lex_8_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3677), (Sat.Literal.pos 251), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation8 251 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3677) (Sat.Literal.pos 251) (Sat.Literal.pos 239) (lex_8_251_prefix s) (positive_select s 251) (lex_8_251_image s)

theorem lex_8_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3678), (Sat.Literal.pos 3677)] :=
  (lex_8_251_gate s).prop _ (List.Mem.head _)

theorem lex_8_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3678), (Sat.Literal.neg 251), (Sat.Literal.pos 239)] :=
  (lex_8_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3678), (Sat.Literal.pos 251), (Sat.Literal.neg 239)] :=
  (lex_8_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3677), (Sat.Literal.neg 251), (Sat.Literal.neg 239), (Sat.Literal.pos 3678)] :=
  (lex_8_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3677), (Sat.Literal.pos 251), (Sat.Literal.pos 239), (Sat.Literal.pos 3678)] :=
  (lex_8_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3678) = lexBefore s permutation8 250 := by
  exact (positive_lex_of_descriptor s 3678 permutation8 251 (by rfl)).trans ((lex_skipped s permutation8 250 251 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation8 250) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation8 250 by rw [image8_eq]; rfl))

theorem lex_8_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3679) (Sat.Literal.pos 3678) (Sat.Literal.pos 250) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation8 250 (assignment s)
    (Sat.Literal.pos 3679) (Sat.Literal.pos 3678) (Sat.Literal.pos 250) (Sat.Literal.pos 235) (positive_of_descriptor s 3679 (.lex permutation8 250) (by rfl)) (lex_8_250_prefix s) (positive_select s 250) (lex_8_250_image s)

theorem lex_8_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3678), (Sat.Literal.pos 250), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation8 250 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3678) (Sat.Literal.pos 250) (Sat.Literal.pos 235) (lex_8_250_prefix s) (positive_select s 250) (lex_8_250_image s)

theorem lex_8_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3679), (Sat.Literal.pos 3678)] :=
  (lex_8_250_gate s).prop _ (List.Mem.head _)

theorem lex_8_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3679), (Sat.Literal.neg 250), (Sat.Literal.pos 235)] :=
  (lex_8_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3679), (Sat.Literal.pos 250), (Sat.Literal.neg 235)] :=
  (lex_8_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3678), (Sat.Literal.neg 250), (Sat.Literal.neg 235), (Sat.Literal.pos 3679)] :=
  (lex_8_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3678), (Sat.Literal.pos 250), (Sat.Literal.pos 235), (Sat.Literal.pos 3679)] :=
  (lex_8_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3679) = lexBefore s permutation8 249 := by
  exact (positive_lex_of_descriptor s 3679 permutation8 250 (by rfl)).trans ((lex_skipped s permutation8 249 250 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation8 249) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation8 249 by rw [image8_eq]; rfl))

theorem lex_8_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3680) (Sat.Literal.pos 3679) (Sat.Literal.pos 249) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation8 249 (assignment s)
    (Sat.Literal.pos 3680) (Sat.Literal.pos 3679) (Sat.Literal.pos 249) (Sat.Literal.pos 231) (positive_of_descriptor s 3680 (.lex permutation8 249) (by rfl)) (lex_8_249_prefix s) (positive_select s 249) (lex_8_249_image s)

theorem lex_8_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3679), (Sat.Literal.pos 249), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation8 249 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3679) (Sat.Literal.pos 249) (Sat.Literal.pos 231) (lex_8_249_prefix s) (positive_select s 249) (lex_8_249_image s)

theorem lex_8_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3680), (Sat.Literal.pos 3679)] :=
  (lex_8_249_gate s).prop _ (List.Mem.head _)

theorem lex_8_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3680), (Sat.Literal.neg 249), (Sat.Literal.pos 231)] :=
  (lex_8_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3680), (Sat.Literal.pos 249), (Sat.Literal.neg 231)] :=
  (lex_8_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3679), (Sat.Literal.neg 249), (Sat.Literal.neg 231), (Sat.Literal.pos 3680)] :=
  (lex_8_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3679), (Sat.Literal.pos 249), (Sat.Literal.pos 231), (Sat.Literal.pos 3680)] :=
  (lex_8_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3680) = lexBefore s permutation8 248 := by
  exact (positive_lex_of_descriptor s 3680 permutation8 249 (by rfl)).trans ((lex_skipped s permutation8 248 249 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation8 248) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation8 248 by rw [image8_eq]; rfl))

theorem lex_8_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3681) (Sat.Literal.pos 3680) (Sat.Literal.pos 248) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation8 248 (assignment s)
    (Sat.Literal.pos 3681) (Sat.Literal.pos 3680) (Sat.Literal.pos 248) (Sat.Literal.pos 227) (positive_of_descriptor s 3681 (.lex permutation8 248) (by rfl)) (lex_8_248_prefix s) (positive_select s 248) (lex_8_248_image s)

theorem lex_8_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3680), (Sat.Literal.pos 248), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation8 248 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3680) (Sat.Literal.pos 248) (Sat.Literal.pos 227) (lex_8_248_prefix s) (positive_select s 248) (lex_8_248_image s)

theorem lex_8_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3681), (Sat.Literal.pos 3680)] :=
  (lex_8_248_gate s).prop _ (List.Mem.head _)

theorem lex_8_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3681), (Sat.Literal.neg 248), (Sat.Literal.pos 227)] :=
  (lex_8_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3681), (Sat.Literal.pos 248), (Sat.Literal.neg 227)] :=
  (lex_8_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3680), (Sat.Literal.neg 248), (Sat.Literal.neg 227), (Sat.Literal.pos 3681)] :=
  (lex_8_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3680), (Sat.Literal.pos 248), (Sat.Literal.pos 227), (Sat.Literal.pos 3681)] :=
  (lex_8_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3681) = lexBefore s permutation8 247 := by
  exact (positive_lex_of_descriptor s 3681 permutation8 248 (by rfl)).trans ((lex_skipped s permutation8 247 248 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation8 247) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation8 247 by rw [image8_eq]; rfl))

theorem lex_8_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3682) (Sat.Literal.pos 3681) (Sat.Literal.pos 247) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation8 247 (assignment s)
    (Sat.Literal.pos 3682) (Sat.Literal.pos 3681) (Sat.Literal.pos 247) (Sat.Literal.pos 223) (positive_of_descriptor s 3682 (.lex permutation8 247) (by rfl)) (lex_8_247_prefix s) (positive_select s 247) (lex_8_247_image s)

theorem lex_8_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3681), (Sat.Literal.pos 247), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation8 247 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3681) (Sat.Literal.pos 247) (Sat.Literal.pos 223) (lex_8_247_prefix s) (positive_select s 247) (lex_8_247_image s)

theorem lex_8_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3682), (Sat.Literal.pos 3681)] :=
  (lex_8_247_gate s).prop _ (List.Mem.head _)

theorem lex_8_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3682), (Sat.Literal.neg 247), (Sat.Literal.pos 223)] :=
  (lex_8_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3682), (Sat.Literal.pos 247), (Sat.Literal.neg 223)] :=
  (lex_8_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3681), (Sat.Literal.neg 247), (Sat.Literal.neg 223), (Sat.Literal.pos 3682)] :=
  (lex_8_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3681), (Sat.Literal.pos 247), (Sat.Literal.pos 223), (Sat.Literal.pos 3682)] :=
  (lex_8_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3682) = lexBefore s permutation8 246 := by
  exact (positive_lex_of_descriptor s 3682 permutation8 247 (by rfl)).trans ((lex_skipped s permutation8 246 247 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation8 246) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation8 246 by rw [image8_eq]; rfl))

theorem lex_8_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3683) (Sat.Literal.pos 3682) (Sat.Literal.pos 246) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation8 246 (assignment s)
    (Sat.Literal.pos 3683) (Sat.Literal.pos 3682) (Sat.Literal.pos 246) (Sat.Literal.pos 219) (positive_of_descriptor s 3683 (.lex permutation8 246) (by rfl)) (lex_8_246_prefix s) (positive_select s 246) (lex_8_246_image s)

theorem lex_8_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3682), (Sat.Literal.pos 246), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation8 246 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3682) (Sat.Literal.pos 246) (Sat.Literal.pos 219) (lex_8_246_prefix s) (positive_select s 246) (lex_8_246_image s)

theorem lex_8_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3683), (Sat.Literal.pos 3682)] :=
  (lex_8_246_gate s).prop _ (List.Mem.head _)

theorem lex_8_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3683), (Sat.Literal.neg 246), (Sat.Literal.pos 219)] :=
  (lex_8_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3683), (Sat.Literal.pos 246), (Sat.Literal.neg 219)] :=
  (lex_8_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3682), (Sat.Literal.neg 246), (Sat.Literal.neg 219), (Sat.Literal.pos 3683)] :=
  (lex_8_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3682), (Sat.Literal.pos 246), (Sat.Literal.pos 219), (Sat.Literal.pos 3683)] :=
  (lex_8_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3683) = lexBefore s permutation8 245 := by
  exact (positive_lex_of_descriptor s 3683 permutation8 246 (by rfl)).trans ((lex_skipped s permutation8 245 246 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation8 245) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation8 245 by rw [image8_eq]; rfl))

theorem lex_8_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3684) (Sat.Literal.pos 3683) (Sat.Literal.pos 245) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation8 245 (assignment s)
    (Sat.Literal.pos 3684) (Sat.Literal.pos 3683) (Sat.Literal.pos 245) (Sat.Literal.pos 215) (positive_of_descriptor s 3684 (.lex permutation8 245) (by rfl)) (lex_8_245_prefix s) (positive_select s 245) (lex_8_245_image s)

theorem lex_8_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3683), (Sat.Literal.pos 245), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation8 245 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3683) (Sat.Literal.pos 245) (Sat.Literal.pos 215) (lex_8_245_prefix s) (positive_select s 245) (lex_8_245_image s)

theorem lex_8_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3684), (Sat.Literal.pos 3683)] :=
  (lex_8_245_gate s).prop _ (List.Mem.head _)

theorem lex_8_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3684), (Sat.Literal.neg 245), (Sat.Literal.pos 215)] :=
  (lex_8_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3684), (Sat.Literal.pos 245), (Sat.Literal.neg 215)] :=
  (lex_8_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3683), (Sat.Literal.neg 245), (Sat.Literal.neg 215), (Sat.Literal.pos 3684)] :=
  (lex_8_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3683), (Sat.Literal.pos 245), (Sat.Literal.pos 215), (Sat.Literal.pos 3684)] :=
  (lex_8_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3684) = lexBefore s permutation8 244 := by
  exact (positive_lex_of_descriptor s 3684 permutation8 245 (by rfl)).trans ((lex_skipped s permutation8 244 245 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation8 244) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation8 244 by rw [image8_eq]; rfl))

theorem lex_8_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3685) (Sat.Literal.pos 3684) (Sat.Literal.pos 244) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation8 244 (assignment s)
    (Sat.Literal.pos 3685) (Sat.Literal.pos 3684) (Sat.Literal.pos 244) (Sat.Literal.pos 211) (positive_of_descriptor s 3685 (.lex permutation8 244) (by rfl)) (lex_8_244_prefix s) (positive_select s 244) (lex_8_244_image s)

theorem lex_8_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3684), (Sat.Literal.pos 244), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation8 244 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3684) (Sat.Literal.pos 244) (Sat.Literal.pos 211) (lex_8_244_prefix s) (positive_select s 244) (lex_8_244_image s)

theorem lex_8_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3685), (Sat.Literal.pos 3684)] :=
  (lex_8_244_gate s).prop _ (List.Mem.head _)

theorem lex_8_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3685), (Sat.Literal.neg 244), (Sat.Literal.pos 211)] :=
  (lex_8_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3685), (Sat.Literal.pos 244), (Sat.Literal.neg 211)] :=
  (lex_8_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3684), (Sat.Literal.neg 244), (Sat.Literal.neg 211), (Sat.Literal.pos 3685)] :=
  (lex_8_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3684), (Sat.Literal.pos 244), (Sat.Literal.pos 211), (Sat.Literal.pos 3685)] :=
  (lex_8_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3685) = lexBefore s permutation8 243 := by
  exact (positive_lex_of_descriptor s 3685 permutation8 244 (by rfl)).trans ((lex_skipped s permutation8 243 244 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation8 243) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation8 243 by rw [image8_eq]; rfl))

theorem lex_8_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3686) (Sat.Literal.pos 3685) (Sat.Literal.pos 243) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation8 243 (assignment s)
    (Sat.Literal.pos 3686) (Sat.Literal.pos 3685) (Sat.Literal.pos 243) (Sat.Literal.pos 207) (positive_of_descriptor s 3686 (.lex permutation8 243) (by rfl)) (lex_8_243_prefix s) (positive_select s 243) (lex_8_243_image s)

theorem lex_8_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3685), (Sat.Literal.pos 243), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation8 243 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3685) (Sat.Literal.pos 243) (Sat.Literal.pos 207) (lex_8_243_prefix s) (positive_select s 243) (lex_8_243_image s)

theorem lex_8_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3686), (Sat.Literal.pos 3685)] :=
  (lex_8_243_gate s).prop _ (List.Mem.head _)

theorem lex_8_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3686), (Sat.Literal.neg 243), (Sat.Literal.pos 207)] :=
  (lex_8_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3686), (Sat.Literal.pos 243), (Sat.Literal.neg 207)] :=
  (lex_8_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3685), (Sat.Literal.neg 243), (Sat.Literal.neg 207), (Sat.Literal.pos 3686)] :=
  (lex_8_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3685), (Sat.Literal.pos 243), (Sat.Literal.pos 207), (Sat.Literal.pos 3686)] :=
  (lex_8_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3686) = lexBefore s permutation8 242 := by
  exact (positive_lex_of_descriptor s 3686 permutation8 243 (by rfl)).trans ((lex_skipped s permutation8 242 243 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation8 242) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation8 242 by rw [image8_eq]; rfl))

theorem lex_8_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3687) (Sat.Literal.pos 3686) (Sat.Literal.pos 242) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation8 242 (assignment s)
    (Sat.Literal.pos 3687) (Sat.Literal.pos 3686) (Sat.Literal.pos 242) (Sat.Literal.pos 203) (positive_of_descriptor s 3687 (.lex permutation8 242) (by rfl)) (lex_8_242_prefix s) (positive_select s 242) (lex_8_242_image s)

theorem lex_8_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3686), (Sat.Literal.pos 242), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation8 242 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3686) (Sat.Literal.pos 242) (Sat.Literal.pos 203) (lex_8_242_prefix s) (positive_select s 242) (lex_8_242_image s)

theorem lex_8_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3687), (Sat.Literal.pos 3686)] :=
  (lex_8_242_gate s).prop _ (List.Mem.head _)

theorem lex_8_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3687), (Sat.Literal.neg 242), (Sat.Literal.pos 203)] :=
  (lex_8_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3687), (Sat.Literal.pos 242), (Sat.Literal.neg 203)] :=
  (lex_8_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3686), (Sat.Literal.neg 242), (Sat.Literal.neg 203), (Sat.Literal.pos 3687)] :=
  (lex_8_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3686), (Sat.Literal.pos 242), (Sat.Literal.pos 203), (Sat.Literal.pos 3687)] :=
  (lex_8_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3687) = lexBefore s permutation8 241 := by
  exact (positive_lex_of_descriptor s 3687 permutation8 242 (by rfl)).trans ((lex_skipped s permutation8 241 242 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation8 241) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation8 241 by rw [image8_eq]; rfl))

theorem lex_8_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3688) (Sat.Literal.pos 3687) (Sat.Literal.pos 241) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation8 241 (assignment s)
    (Sat.Literal.pos 3688) (Sat.Literal.pos 3687) (Sat.Literal.pos 241) (Sat.Literal.pos 199) (positive_of_descriptor s 3688 (.lex permutation8 241) (by rfl)) (lex_8_241_prefix s) (positive_select s 241) (lex_8_241_image s)

theorem lex_8_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3687), (Sat.Literal.pos 241), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation8 241 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3687) (Sat.Literal.pos 241) (Sat.Literal.pos 199) (lex_8_241_prefix s) (positive_select s 241) (lex_8_241_image s)

theorem lex_8_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3688), (Sat.Literal.pos 3687)] :=
  (lex_8_241_gate s).prop _ (List.Mem.head _)

theorem lex_8_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3688), (Sat.Literal.neg 241), (Sat.Literal.pos 199)] :=
  (lex_8_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3688), (Sat.Literal.pos 241), (Sat.Literal.neg 199)] :=
  (lex_8_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3687), (Sat.Literal.neg 241), (Sat.Literal.neg 199), (Sat.Literal.pos 3688)] :=
  (lex_8_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3687), (Sat.Literal.pos 241), (Sat.Literal.pos 199), (Sat.Literal.pos 3688)] :=
  (lex_8_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3688) = lexBefore s permutation8 240 := by
  exact (positive_lex_of_descriptor s 3688 permutation8 241 (by rfl)).trans ((lex_skipped s permutation8 240 241 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation8 240) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation8 240 by rw [image8_eq]; rfl))

theorem lex_8_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3689) (Sat.Literal.pos 3688) (Sat.Literal.pos 240) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation8 240 (assignment s)
    (Sat.Literal.pos 3689) (Sat.Literal.pos 3688) (Sat.Literal.pos 240) (Sat.Literal.pos 195) (positive_of_descriptor s 3689 (.lex permutation8 240) (by rfl)) (lex_8_240_prefix s) (positive_select s 240) (lex_8_240_image s)

theorem lex_8_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3688), (Sat.Literal.pos 240), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation8 240 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3688) (Sat.Literal.pos 240) (Sat.Literal.pos 195) (lex_8_240_prefix s) (positive_select s 240) (lex_8_240_image s)

theorem lex_8_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3689), (Sat.Literal.pos 3688)] :=
  (lex_8_240_gate s).prop _ (List.Mem.head _)

theorem lex_8_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3689), (Sat.Literal.neg 240), (Sat.Literal.pos 195)] :=
  (lex_8_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3689), (Sat.Literal.pos 240), (Sat.Literal.neg 195)] :=
  (lex_8_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3688), (Sat.Literal.neg 240), (Sat.Literal.neg 195), (Sat.Literal.pos 3689)] :=
  (lex_8_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3688), (Sat.Literal.pos 240), (Sat.Literal.pos 195), (Sat.Literal.pos 3689)] :=
  (lex_8_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3689) = lexBefore s permutation8 239 := by
  exact (positive_lex_of_descriptor s 3689 permutation8 240 (by rfl)).trans ((lex_skipped s permutation8 239 240 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation8 239) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation8 239 by rw [image8_eq]; rfl))

theorem lex_8_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3690) (Sat.Literal.pos 3689) (Sat.Literal.pos 239) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation8 239 (assignment s)
    (Sat.Literal.pos 3690) (Sat.Literal.pos 3689) (Sat.Literal.pos 239) (Sat.Literal.pos 191) (positive_of_descriptor s 3690 (.lex permutation8 239) (by rfl)) (lex_8_239_prefix s) (positive_select s 239) (lex_8_239_image s)

theorem lex_8_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3689), (Sat.Literal.pos 239), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation8 239 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3689) (Sat.Literal.pos 239) (Sat.Literal.pos 191) (lex_8_239_prefix s) (positive_select s 239) (lex_8_239_image s)

theorem lex_8_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3690), (Sat.Literal.pos 3689)] :=
  (lex_8_239_gate s).prop _ (List.Mem.head _)

theorem lex_8_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3690), (Sat.Literal.neg 239), (Sat.Literal.pos 191)] :=
  (lex_8_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3690), (Sat.Literal.pos 239), (Sat.Literal.neg 191)] :=
  (lex_8_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3689), (Sat.Literal.neg 239), (Sat.Literal.neg 191), (Sat.Literal.pos 3690)] :=
  (lex_8_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3689), (Sat.Literal.pos 239), (Sat.Literal.pos 191), (Sat.Literal.pos 3690)] :=
  (lex_8_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3690) = lexBefore s permutation8 238 := by
  exact (positive_lex_of_descriptor s 3690 permutation8 239 (by rfl)).trans ((lex_skipped s permutation8 238 239 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation8 238) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation8 238 by rw [image8_eq]; rfl))

theorem lex_8_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3691) (Sat.Literal.pos 3690) (Sat.Literal.pos 238) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation8 238 (assignment s)
    (Sat.Literal.pos 3691) (Sat.Literal.pos 3690) (Sat.Literal.pos 238) (Sat.Literal.pos 187) (positive_of_descriptor s 3691 (.lex permutation8 238) (by rfl)) (lex_8_238_prefix s) (positive_select s 238) (lex_8_238_image s)

theorem lex_8_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3690), (Sat.Literal.pos 238), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation8 238 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3690) (Sat.Literal.pos 238) (Sat.Literal.pos 187) (lex_8_238_prefix s) (positive_select s 238) (lex_8_238_image s)

theorem lex_8_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3691), (Sat.Literal.pos 3690)] :=
  (lex_8_238_gate s).prop _ (List.Mem.head _)

theorem lex_8_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3691), (Sat.Literal.neg 238), (Sat.Literal.pos 187)] :=
  (lex_8_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3691), (Sat.Literal.pos 238), (Sat.Literal.neg 187)] :=
  (lex_8_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3690), (Sat.Literal.neg 238), (Sat.Literal.neg 187), (Sat.Literal.pos 3691)] :=
  (lex_8_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3690), (Sat.Literal.pos 238), (Sat.Literal.pos 187), (Sat.Literal.pos 3691)] :=
  (lex_8_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3691) = lexBefore s permutation8 237 := by
  exact (positive_lex_of_descriptor s 3691 permutation8 238 (by rfl)).trans ((lex_skipped s permutation8 237 238 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation8 237) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation8 237 by rw [image8_eq]; rfl))

theorem lex_8_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3692) (Sat.Literal.pos 3691) (Sat.Literal.pos 237) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation8 237 (assignment s)
    (Sat.Literal.pos 3692) (Sat.Literal.pos 3691) (Sat.Literal.pos 237) (Sat.Literal.pos 183) (positive_of_descriptor s 3692 (.lex permutation8 237) (by rfl)) (lex_8_237_prefix s) (positive_select s 237) (lex_8_237_image s)

theorem lex_8_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3691), (Sat.Literal.pos 237), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation8 237 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3691) (Sat.Literal.pos 237) (Sat.Literal.pos 183) (lex_8_237_prefix s) (positive_select s 237) (lex_8_237_image s)

theorem lex_8_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3692), (Sat.Literal.pos 3691)] :=
  (lex_8_237_gate s).prop _ (List.Mem.head _)

theorem lex_8_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3692), (Sat.Literal.neg 237), (Sat.Literal.pos 183)] :=
  (lex_8_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3692), (Sat.Literal.pos 237), (Sat.Literal.neg 183)] :=
  (lex_8_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3691), (Sat.Literal.neg 237), (Sat.Literal.neg 183), (Sat.Literal.pos 3692)] :=
  (lex_8_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3691), (Sat.Literal.pos 237), (Sat.Literal.pos 183), (Sat.Literal.pos 3692)] :=
  (lex_8_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3692) = lexBefore s permutation8 236 := by
  exact (positive_lex_of_descriptor s 3692 permutation8 237 (by rfl)).trans ((lex_skipped s permutation8 236 237 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation8 236) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation8 236 by rw [image8_eq]; rfl))

theorem lex_8_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3693) (Sat.Literal.pos 3692) (Sat.Literal.pos 236) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation8 236 (assignment s)
    (Sat.Literal.pos 3693) (Sat.Literal.pos 3692) (Sat.Literal.pos 236) (Sat.Literal.pos 179) (positive_of_descriptor s 3693 (.lex permutation8 236) (by rfl)) (lex_8_236_prefix s) (positive_select s 236) (lex_8_236_image s)

theorem lex_8_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3692), (Sat.Literal.pos 236), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation8 236 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3692) (Sat.Literal.pos 236) (Sat.Literal.pos 179) (lex_8_236_prefix s) (positive_select s 236) (lex_8_236_image s)

theorem lex_8_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3693), (Sat.Literal.pos 3692)] :=
  (lex_8_236_gate s).prop _ (List.Mem.head _)

theorem lex_8_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3693), (Sat.Literal.neg 236), (Sat.Literal.pos 179)] :=
  (lex_8_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3693), (Sat.Literal.pos 236), (Sat.Literal.neg 179)] :=
  (lex_8_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3692), (Sat.Literal.neg 236), (Sat.Literal.neg 179), (Sat.Literal.pos 3693)] :=
  (lex_8_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3692), (Sat.Literal.pos 236), (Sat.Literal.pos 179), (Sat.Literal.pos 3693)] :=
  (lex_8_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3693) = lexBefore s permutation8 235 := by
  exact (positive_lex_of_descriptor s 3693 permutation8 236 (by rfl)).trans ((lex_skipped s permutation8 235 236 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation8 235) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation8 235 by rw [image8_eq]; rfl))

theorem lex_8_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3694) (Sat.Literal.pos 3693) (Sat.Literal.pos 235) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation8 235 (assignment s)
    (Sat.Literal.pos 3694) (Sat.Literal.pos 3693) (Sat.Literal.pos 235) (Sat.Literal.pos 175) (positive_of_descriptor s 3694 (.lex permutation8 235) (by rfl)) (lex_8_235_prefix s) (positive_select s 235) (lex_8_235_image s)

theorem lex_8_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3693), (Sat.Literal.pos 235), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation8 235 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3693) (Sat.Literal.pos 235) (Sat.Literal.pos 175) (lex_8_235_prefix s) (positive_select s 235) (lex_8_235_image s)

theorem lex_8_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3694), (Sat.Literal.pos 3693)] :=
  (lex_8_235_gate s).prop _ (List.Mem.head _)

theorem lex_8_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3694), (Sat.Literal.neg 235), (Sat.Literal.pos 175)] :=
  (lex_8_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3694), (Sat.Literal.pos 235), (Sat.Literal.neg 175)] :=
  (lex_8_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3693), (Sat.Literal.neg 235), (Sat.Literal.neg 175), (Sat.Literal.pos 3694)] :=
  (lex_8_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3693), (Sat.Literal.pos 235), (Sat.Literal.pos 175), (Sat.Literal.pos 3694)] :=
  (lex_8_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3694) = lexBefore s permutation8 234 := by
  exact (positive_lex_of_descriptor s 3694 permutation8 235 (by rfl)).trans ((lex_skipped s permutation8 234 235 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation8 234) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation8 234 by rw [image8_eq]; rfl))

theorem lex_8_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3695) (Sat.Literal.pos 3694) (Sat.Literal.pos 234) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation8 234 (assignment s)
    (Sat.Literal.pos 3695) (Sat.Literal.pos 3694) (Sat.Literal.pos 234) (Sat.Literal.pos 171) (positive_of_descriptor s 3695 (.lex permutation8 234) (by rfl)) (lex_8_234_prefix s) (positive_select s 234) (lex_8_234_image s)

theorem lex_8_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3694), (Sat.Literal.pos 234), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation8 234 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3694) (Sat.Literal.pos 234) (Sat.Literal.pos 171) (lex_8_234_prefix s) (positive_select s 234) (lex_8_234_image s)

theorem lex_8_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3695), (Sat.Literal.pos 3694)] :=
  (lex_8_234_gate s).prop _ (List.Mem.head _)

theorem lex_8_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3695), (Sat.Literal.neg 234), (Sat.Literal.pos 171)] :=
  (lex_8_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3695), (Sat.Literal.pos 234), (Sat.Literal.neg 171)] :=
  (lex_8_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3694), (Sat.Literal.neg 234), (Sat.Literal.neg 171), (Sat.Literal.pos 3695)] :=
  (lex_8_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3694), (Sat.Literal.pos 234), (Sat.Literal.pos 171), (Sat.Literal.pos 3695)] :=
  (lex_8_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3695) = lexBefore s permutation8 233 := by
  exact (positive_lex_of_descriptor s 3695 permutation8 234 (by rfl)).trans ((lex_skipped s permutation8 233 234 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation8 233) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation8 233 by rw [image8_eq]; rfl))

theorem lex_8_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3696) (Sat.Literal.pos 3695) (Sat.Literal.pos 233) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation8 233 (assignment s)
    (Sat.Literal.pos 3696) (Sat.Literal.pos 3695) (Sat.Literal.pos 233) (Sat.Literal.pos 167) (positive_of_descriptor s 3696 (.lex permutation8 233) (by rfl)) (lex_8_233_prefix s) (positive_select s 233) (lex_8_233_image s)

theorem lex_8_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3695), (Sat.Literal.pos 233), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation8 233 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3695) (Sat.Literal.pos 233) (Sat.Literal.pos 167) (lex_8_233_prefix s) (positive_select s 233) (lex_8_233_image s)

theorem lex_8_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3696), (Sat.Literal.pos 3695)] :=
  (lex_8_233_gate s).prop _ (List.Mem.head _)

theorem lex_8_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3696), (Sat.Literal.neg 233), (Sat.Literal.pos 167)] :=
  (lex_8_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3696), (Sat.Literal.pos 233), (Sat.Literal.neg 167)] :=
  (lex_8_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3695), (Sat.Literal.neg 233), (Sat.Literal.neg 167), (Sat.Literal.pos 3696)] :=
  (lex_8_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3695), (Sat.Literal.pos 233), (Sat.Literal.pos 167), (Sat.Literal.pos 3696)] :=
  (lex_8_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3696) = lexBefore s permutation8 232 := by
  exact (positive_lex_of_descriptor s 3696 permutation8 233 (by rfl)).trans ((lex_skipped s permutation8 232 233 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation8 232) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation8 232 by rw [image8_eq]; rfl))

theorem lex_8_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3697) (Sat.Literal.pos 3696) (Sat.Literal.pos 232) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation8 232 (assignment s)
    (Sat.Literal.pos 3697) (Sat.Literal.pos 3696) (Sat.Literal.pos 232) (Sat.Literal.pos 163) (positive_of_descriptor s 3697 (.lex permutation8 232) (by rfl)) (lex_8_232_prefix s) (positive_select s 232) (lex_8_232_image s)

theorem lex_8_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3696), (Sat.Literal.pos 232), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation8 232 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3696) (Sat.Literal.pos 232) (Sat.Literal.pos 163) (lex_8_232_prefix s) (positive_select s 232) (lex_8_232_image s)

theorem lex_8_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3697), (Sat.Literal.pos 3696)] :=
  (lex_8_232_gate s).prop _ (List.Mem.head _)

theorem lex_8_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3697), (Sat.Literal.neg 232), (Sat.Literal.pos 163)] :=
  (lex_8_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3697), (Sat.Literal.pos 232), (Sat.Literal.neg 163)] :=
  (lex_8_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3696), (Sat.Literal.neg 232), (Sat.Literal.neg 163), (Sat.Literal.pos 3697)] :=
  (lex_8_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3696), (Sat.Literal.pos 232), (Sat.Literal.pos 163), (Sat.Literal.pos 3697)] :=
  (lex_8_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3697) = lexBefore s permutation8 231 := by
  exact (positive_lex_of_descriptor s 3697 permutation8 232 (by rfl)).trans ((lex_skipped s permutation8 231 232 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation8 231) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation8 231 by rw [image8_eq]; rfl))

theorem lex_8_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3698) (Sat.Literal.pos 3697) (Sat.Literal.pos 231) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation8 231 (assignment s)
    (Sat.Literal.pos 3698) (Sat.Literal.pos 3697) (Sat.Literal.pos 231) (Sat.Literal.pos 159) (positive_of_descriptor s 3698 (.lex permutation8 231) (by rfl)) (lex_8_231_prefix s) (positive_select s 231) (lex_8_231_image s)

theorem lex_8_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3697), (Sat.Literal.pos 231), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation8 231 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3697) (Sat.Literal.pos 231) (Sat.Literal.pos 159) (lex_8_231_prefix s) (positive_select s 231) (lex_8_231_image s)

theorem lex_8_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3698), (Sat.Literal.pos 3697)] :=
  (lex_8_231_gate s).prop _ (List.Mem.head _)

theorem lex_8_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3698), (Sat.Literal.neg 231), (Sat.Literal.pos 159)] :=
  (lex_8_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3698), (Sat.Literal.pos 231), (Sat.Literal.neg 159)] :=
  (lex_8_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3697), (Sat.Literal.neg 231), (Sat.Literal.neg 159), (Sat.Literal.pos 3698)] :=
  (lex_8_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3697), (Sat.Literal.pos 231), (Sat.Literal.pos 159), (Sat.Literal.pos 3698)] :=
  (lex_8_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3698) = lexBefore s permutation8 230 := by
  exact (positive_lex_of_descriptor s 3698 permutation8 231 (by rfl)).trans ((lex_skipped s permutation8 230 231 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation8 230) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation8 230 by rw [image8_eq]; rfl))

theorem lex_8_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3699) (Sat.Literal.pos 3698) (Sat.Literal.pos 230) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation8 230 (assignment s)
    (Sat.Literal.pos 3699) (Sat.Literal.pos 3698) (Sat.Literal.pos 230) (Sat.Literal.pos 155) (positive_of_descriptor s 3699 (.lex permutation8 230) (by rfl)) (lex_8_230_prefix s) (positive_select s 230) (lex_8_230_image s)

theorem lex_8_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3698), (Sat.Literal.pos 230), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation8 230 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3698) (Sat.Literal.pos 230) (Sat.Literal.pos 155) (lex_8_230_prefix s) (positive_select s 230) (lex_8_230_image s)

theorem lex_8_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3699), (Sat.Literal.pos 3698)] :=
  (lex_8_230_gate s).prop _ (List.Mem.head _)

theorem lex_8_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3699), (Sat.Literal.neg 230), (Sat.Literal.pos 155)] :=
  (lex_8_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3699), (Sat.Literal.pos 230), (Sat.Literal.neg 155)] :=
  (lex_8_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3698), (Sat.Literal.neg 230), (Sat.Literal.neg 155), (Sat.Literal.pos 3699)] :=
  (lex_8_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3698), (Sat.Literal.pos 230), (Sat.Literal.pos 155), (Sat.Literal.pos 3699)] :=
  (lex_8_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3699) = lexBefore s permutation8 229 := by
  exact (positive_lex_of_descriptor s 3699 permutation8 230 (by rfl)).trans ((lex_skipped s permutation8 229 230 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation8 229) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation8 229 by rw [image8_eq]; rfl))

theorem lex_8_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3700) (Sat.Literal.pos 3699) (Sat.Literal.pos 229) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation8 229 (assignment s)
    (Sat.Literal.pos 3700) (Sat.Literal.pos 3699) (Sat.Literal.pos 229) (Sat.Literal.pos 151) (positive_of_descriptor s 3700 (.lex permutation8 229) (by rfl)) (lex_8_229_prefix s) (positive_select s 229) (lex_8_229_image s)

theorem lex_8_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3699), (Sat.Literal.pos 229), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation8 229 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3699) (Sat.Literal.pos 229) (Sat.Literal.pos 151) (lex_8_229_prefix s) (positive_select s 229) (lex_8_229_image s)

theorem lex_8_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3700), (Sat.Literal.pos 3699)] :=
  (lex_8_229_gate s).prop _ (List.Mem.head _)

theorem lex_8_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3700), (Sat.Literal.neg 229), (Sat.Literal.pos 151)] :=
  (lex_8_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3700), (Sat.Literal.pos 229), (Sat.Literal.neg 151)] :=
  (lex_8_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3699), (Sat.Literal.neg 229), (Sat.Literal.neg 151), (Sat.Literal.pos 3700)] :=
  (lex_8_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3699), (Sat.Literal.pos 229), (Sat.Literal.pos 151), (Sat.Literal.pos 3700)] :=
  (lex_8_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3700) = lexBefore s permutation8 228 := by
  exact (positive_lex_of_descriptor s 3700 permutation8 229 (by rfl)).trans ((lex_skipped s permutation8 228 229 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation8 228) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation8 228 by rw [image8_eq]; rfl))

theorem lex_8_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3701) (Sat.Literal.pos 3700) (Sat.Literal.pos 228) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation8 228 (assignment s)
    (Sat.Literal.pos 3701) (Sat.Literal.pos 3700) (Sat.Literal.pos 228) (Sat.Literal.pos 147) (positive_of_descriptor s 3701 (.lex permutation8 228) (by rfl)) (lex_8_228_prefix s) (positive_select s 228) (lex_8_228_image s)

theorem lex_8_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3700), (Sat.Literal.pos 228), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation8 228 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3700) (Sat.Literal.pos 228) (Sat.Literal.pos 147) (lex_8_228_prefix s) (positive_select s 228) (lex_8_228_image s)

theorem lex_8_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3701), (Sat.Literal.pos 3700)] :=
  (lex_8_228_gate s).prop _ (List.Mem.head _)

theorem lex_8_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3701), (Sat.Literal.neg 228), (Sat.Literal.pos 147)] :=
  (lex_8_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3701), (Sat.Literal.pos 228), (Sat.Literal.neg 147)] :=
  (lex_8_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3700), (Sat.Literal.neg 228), (Sat.Literal.neg 147), (Sat.Literal.pos 3701)] :=
  (lex_8_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3700), (Sat.Literal.pos 228), (Sat.Literal.pos 147), (Sat.Literal.pos 3701)] :=
  (lex_8_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3701) = lexBefore s permutation8 227 := by
  exact (positive_lex_of_descriptor s 3701 permutation8 228 (by rfl)).trans ((lex_skipped s permutation8 227 228 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation8 227) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation8 227 by rw [image8_eq]; rfl))

theorem lex_8_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3702) (Sat.Literal.pos 3701) (Sat.Literal.pos 227) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation8 227 (assignment s)
    (Sat.Literal.pos 3702) (Sat.Literal.pos 3701) (Sat.Literal.pos 227) (Sat.Literal.pos 143) (positive_of_descriptor s 3702 (.lex permutation8 227) (by rfl)) (lex_8_227_prefix s) (positive_select s 227) (lex_8_227_image s)

theorem lex_8_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3701), (Sat.Literal.pos 227), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation8 227 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3701) (Sat.Literal.pos 227) (Sat.Literal.pos 143) (lex_8_227_prefix s) (positive_select s 227) (lex_8_227_image s)

theorem lex_8_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3702), (Sat.Literal.pos 3701)] :=
  (lex_8_227_gate s).prop _ (List.Mem.head _)

theorem lex_8_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3702), (Sat.Literal.neg 227), (Sat.Literal.pos 143)] :=
  (lex_8_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3702), (Sat.Literal.pos 227), (Sat.Literal.neg 143)] :=
  (lex_8_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3701), (Sat.Literal.neg 227), (Sat.Literal.neg 143), (Sat.Literal.pos 3702)] :=
  (lex_8_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3701), (Sat.Literal.pos 227), (Sat.Literal.pos 143), (Sat.Literal.pos 3702)] :=
  (lex_8_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3702) = lexBefore s permutation8 226 := by
  exact (positive_lex_of_descriptor s 3702 permutation8 227 (by rfl)).trans ((lex_skipped s permutation8 226 227 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation8 226) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation8 226 by rw [image8_eq]; rfl))

theorem lex_8_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3703) (Sat.Literal.pos 3702) (Sat.Literal.pos 226) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation8 226 (assignment s)
    (Sat.Literal.pos 3703) (Sat.Literal.pos 3702) (Sat.Literal.pos 226) (Sat.Literal.pos 139) (positive_of_descriptor s 3703 (.lex permutation8 226) (by rfl)) (lex_8_226_prefix s) (positive_select s 226) (lex_8_226_image s)

theorem lex_8_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3702), (Sat.Literal.pos 226), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation8 226 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3702) (Sat.Literal.pos 226) (Sat.Literal.pos 139) (lex_8_226_prefix s) (positive_select s 226) (lex_8_226_image s)

theorem lex_8_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3703), (Sat.Literal.pos 3702)] :=
  (lex_8_226_gate s).prop _ (List.Mem.head _)

theorem lex_8_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3703), (Sat.Literal.neg 226), (Sat.Literal.pos 139)] :=
  (lex_8_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3703), (Sat.Literal.pos 226), (Sat.Literal.neg 139)] :=
  (lex_8_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3702), (Sat.Literal.neg 226), (Sat.Literal.neg 139), (Sat.Literal.pos 3703)] :=
  (lex_8_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3702), (Sat.Literal.pos 226), (Sat.Literal.pos 139), (Sat.Literal.pos 3703)] :=
  (lex_8_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3703) = lexBefore s permutation8 225 := by
  exact (positive_lex_of_descriptor s 3703 permutation8 226 (by rfl)).trans ((lex_skipped s permutation8 225 226 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation8 225) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation8 225 by rw [image8_eq]; rfl))

theorem lex_8_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3704) (Sat.Literal.pos 3703) (Sat.Literal.pos 225) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation8 225 (assignment s)
    (Sat.Literal.pos 3704) (Sat.Literal.pos 3703) (Sat.Literal.pos 225) (Sat.Literal.pos 135) (positive_of_descriptor s 3704 (.lex permutation8 225) (by rfl)) (lex_8_225_prefix s) (positive_select s 225) (lex_8_225_image s)

theorem lex_8_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3703), (Sat.Literal.pos 225), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation8 225 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3703) (Sat.Literal.pos 225) (Sat.Literal.pos 135) (lex_8_225_prefix s) (positive_select s 225) (lex_8_225_image s)

theorem lex_8_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3704), (Sat.Literal.pos 3703)] :=
  (lex_8_225_gate s).prop _ (List.Mem.head _)

theorem lex_8_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3704), (Sat.Literal.neg 225), (Sat.Literal.pos 135)] :=
  (lex_8_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3704), (Sat.Literal.pos 225), (Sat.Literal.neg 135)] :=
  (lex_8_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3703), (Sat.Literal.neg 225), (Sat.Literal.neg 135), (Sat.Literal.pos 3704)] :=
  (lex_8_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3703), (Sat.Literal.pos 225), (Sat.Literal.pos 135), (Sat.Literal.pos 3704)] :=
  (lex_8_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3704) = lexBefore s permutation8 224 := by
  exact (positive_lex_of_descriptor s 3704 permutation8 225 (by rfl)).trans ((lex_skipped s permutation8 224 225 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation8 224) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation8 224 by rw [image8_eq]; rfl))

theorem lex_8_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3705) (Sat.Literal.pos 3704) (Sat.Literal.pos 224) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation8 224 (assignment s)
    (Sat.Literal.pos 3705) (Sat.Literal.pos 3704) (Sat.Literal.pos 224) (Sat.Literal.pos 131) (positive_of_descriptor s 3705 (.lex permutation8 224) (by rfl)) (lex_8_224_prefix s) (positive_select s 224) (lex_8_224_image s)

theorem lex_8_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3704), (Sat.Literal.pos 224), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation8 224 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3704) (Sat.Literal.pos 224) (Sat.Literal.pos 131) (lex_8_224_prefix s) (positive_select s 224) (lex_8_224_image s)

theorem lex_8_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3705), (Sat.Literal.pos 3704)] :=
  (lex_8_224_gate s).prop _ (List.Mem.head _)

theorem lex_8_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3705), (Sat.Literal.neg 224), (Sat.Literal.pos 131)] :=
  (lex_8_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3705), (Sat.Literal.pos 224), (Sat.Literal.neg 131)] :=
  (lex_8_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3704), (Sat.Literal.neg 224), (Sat.Literal.neg 131), (Sat.Literal.pos 3705)] :=
  (lex_8_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3704), (Sat.Literal.pos 224), (Sat.Literal.pos 131), (Sat.Literal.pos 3705)] :=
  (lex_8_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3705) = lexBefore s permutation8 223 := by
  exact (positive_lex_of_descriptor s 3705 permutation8 224 (by rfl)).trans ((lex_skipped s permutation8 223 224 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation8 223) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation8 223 by rw [image8_eq]; rfl))

theorem lex_8_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3706) (Sat.Literal.pos 3705) (Sat.Literal.pos 223) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation8 223 (assignment s)
    (Sat.Literal.pos 3706) (Sat.Literal.pos 3705) (Sat.Literal.pos 223) (Sat.Literal.pos 127) (positive_of_descriptor s 3706 (.lex permutation8 223) (by rfl)) (lex_8_223_prefix s) (positive_select s 223) (lex_8_223_image s)

theorem lex_8_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3705), (Sat.Literal.pos 223), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation8 223 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3705) (Sat.Literal.pos 223) (Sat.Literal.pos 127) (lex_8_223_prefix s) (positive_select s 223) (lex_8_223_image s)

theorem lex_8_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3706), (Sat.Literal.pos 3705)] :=
  (lex_8_223_gate s).prop _ (List.Mem.head _)

theorem lex_8_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3706), (Sat.Literal.neg 223), (Sat.Literal.pos 127)] :=
  (lex_8_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3706), (Sat.Literal.pos 223), (Sat.Literal.neg 127)] :=
  (lex_8_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3705), (Sat.Literal.neg 223), (Sat.Literal.neg 127), (Sat.Literal.pos 3706)] :=
  (lex_8_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3705), (Sat.Literal.pos 223), (Sat.Literal.pos 127), (Sat.Literal.pos 3706)] :=
  (lex_8_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3706) = lexBefore s permutation8 222 := by
  exact (positive_lex_of_descriptor s 3706 permutation8 223 (by rfl)).trans ((lex_skipped s permutation8 222 223 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation8 222) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation8 222 by rw [image8_eq]; rfl))

theorem lex_8_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3707) (Sat.Literal.pos 3706) (Sat.Literal.pos 222) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation8 222 (assignment s)
    (Sat.Literal.pos 3707) (Sat.Literal.pos 3706) (Sat.Literal.pos 222) (Sat.Literal.pos 123) (positive_of_descriptor s 3707 (.lex permutation8 222) (by rfl)) (lex_8_222_prefix s) (positive_select s 222) (lex_8_222_image s)

theorem lex_8_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3706), (Sat.Literal.pos 222), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation8 222 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3706) (Sat.Literal.pos 222) (Sat.Literal.pos 123) (lex_8_222_prefix s) (positive_select s 222) (lex_8_222_image s)

theorem lex_8_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3707), (Sat.Literal.pos 3706)] :=
  (lex_8_222_gate s).prop _ (List.Mem.head _)

theorem lex_8_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3707), (Sat.Literal.neg 222), (Sat.Literal.pos 123)] :=
  (lex_8_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3707), (Sat.Literal.pos 222), (Sat.Literal.neg 123)] :=
  (lex_8_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3706), (Sat.Literal.neg 222), (Sat.Literal.neg 123), (Sat.Literal.pos 3707)] :=
  (lex_8_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3706), (Sat.Literal.pos 222), (Sat.Literal.pos 123), (Sat.Literal.pos 3707)] :=
  (lex_8_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3707) = lexBefore s permutation8 221 := by
  exact (positive_lex_of_descriptor s 3707 permutation8 222 (by rfl)).trans ((lex_skipped s permutation8 221 222 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation8 221) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation8 221 by rw [image8_eq]; rfl))

theorem lex_8_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3708) (Sat.Literal.pos 3707) (Sat.Literal.pos 221) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation8 221 (assignment s)
    (Sat.Literal.pos 3708) (Sat.Literal.pos 3707) (Sat.Literal.pos 221) (Sat.Literal.pos 119) (positive_of_descriptor s 3708 (.lex permutation8 221) (by rfl)) (lex_8_221_prefix s) (positive_select s 221) (lex_8_221_image s)

theorem lex_8_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3707), (Sat.Literal.pos 221), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation8 221 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3707) (Sat.Literal.pos 221) (Sat.Literal.pos 119) (lex_8_221_prefix s) (positive_select s 221) (lex_8_221_image s)

theorem lex_8_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3708), (Sat.Literal.pos 3707)] :=
  (lex_8_221_gate s).prop _ (List.Mem.head _)

theorem lex_8_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3708), (Sat.Literal.neg 221), (Sat.Literal.pos 119)] :=
  (lex_8_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3708), (Sat.Literal.pos 221), (Sat.Literal.neg 119)] :=
  (lex_8_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3707), (Sat.Literal.neg 221), (Sat.Literal.neg 119), (Sat.Literal.pos 3708)] :=
  (lex_8_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3707), (Sat.Literal.pos 221), (Sat.Literal.pos 119), (Sat.Literal.pos 3708)] :=
  (lex_8_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3708) = lexBefore s permutation8 220 := by
  exact (positive_lex_of_descriptor s 3708 permutation8 221 (by rfl)).trans ((lex_skipped s permutation8 220 221 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation8 220) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation8 220 by rw [image8_eq]; rfl))

theorem lex_8_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3709) (Sat.Literal.pos 3708) (Sat.Literal.pos 220) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation8 220 (assignment s)
    (Sat.Literal.pos 3709) (Sat.Literal.pos 3708) (Sat.Literal.pos 220) (Sat.Literal.pos 115) (positive_of_descriptor s 3709 (.lex permutation8 220) (by rfl)) (lex_8_220_prefix s) (positive_select s 220) (lex_8_220_image s)

theorem lex_8_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3708), (Sat.Literal.pos 220), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation8 220 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3708) (Sat.Literal.pos 220) (Sat.Literal.pos 115) (lex_8_220_prefix s) (positive_select s 220) (lex_8_220_image s)

theorem lex_8_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3709), (Sat.Literal.pos 3708)] :=
  (lex_8_220_gate s).prop _ (List.Mem.head _)

theorem lex_8_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3709), (Sat.Literal.neg 220), (Sat.Literal.pos 115)] :=
  (lex_8_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3709), (Sat.Literal.pos 220), (Sat.Literal.neg 115)] :=
  (lex_8_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3708), (Sat.Literal.neg 220), (Sat.Literal.neg 115), (Sat.Literal.pos 3709)] :=
  (lex_8_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3708), (Sat.Literal.pos 220), (Sat.Literal.pos 115), (Sat.Literal.pos 3709)] :=
  (lex_8_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3709) = lexBefore s permutation8 219 := by
  exact (positive_lex_of_descriptor s 3709 permutation8 220 (by rfl)).trans ((lex_skipped s permutation8 219 220 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation8 219) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation8 219 by rw [image8_eq]; rfl))

theorem lex_8_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3710) (Sat.Literal.pos 3709) (Sat.Literal.pos 219) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation8 219 (assignment s)
    (Sat.Literal.pos 3710) (Sat.Literal.pos 3709) (Sat.Literal.pos 219) (Sat.Literal.pos 111) (positive_of_descriptor s 3710 (.lex permutation8 219) (by rfl)) (lex_8_219_prefix s) (positive_select s 219) (lex_8_219_image s)

theorem lex_8_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3709), (Sat.Literal.pos 219), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation8 219 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3709) (Sat.Literal.pos 219) (Sat.Literal.pos 111) (lex_8_219_prefix s) (positive_select s 219) (lex_8_219_image s)

theorem lex_8_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3710), (Sat.Literal.pos 3709)] :=
  (lex_8_219_gate s).prop _ (List.Mem.head _)

theorem lex_8_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3710), (Sat.Literal.neg 219), (Sat.Literal.pos 111)] :=
  (lex_8_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3710), (Sat.Literal.pos 219), (Sat.Literal.neg 111)] :=
  (lex_8_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3709), (Sat.Literal.neg 219), (Sat.Literal.neg 111), (Sat.Literal.pos 3710)] :=
  (lex_8_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3709), (Sat.Literal.pos 219), (Sat.Literal.pos 111), (Sat.Literal.pos 3710)] :=
  (lex_8_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3710) = lexBefore s permutation8 218 := by
  exact (positive_lex_of_descriptor s 3710 permutation8 219 (by rfl)).trans ((lex_skipped s permutation8 218 219 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation8 218) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation8 218 by rw [image8_eq]; rfl))

theorem lex_8_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3711) (Sat.Literal.pos 3710) (Sat.Literal.pos 218) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation8 218 (assignment s)
    (Sat.Literal.pos 3711) (Sat.Literal.pos 3710) (Sat.Literal.pos 218) (Sat.Literal.pos 107) (positive_of_descriptor s 3711 (.lex permutation8 218) (by rfl)) (lex_8_218_prefix s) (positive_select s 218) (lex_8_218_image s)

theorem lex_8_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3710), (Sat.Literal.pos 218), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation8 218 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3710) (Sat.Literal.pos 218) (Sat.Literal.pos 107) (lex_8_218_prefix s) (positive_select s 218) (lex_8_218_image s)

theorem lex_8_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3711), (Sat.Literal.pos 3710)] :=
  (lex_8_218_gate s).prop _ (List.Mem.head _)

theorem lex_8_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3711), (Sat.Literal.neg 218), (Sat.Literal.pos 107)] :=
  (lex_8_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3711), (Sat.Literal.pos 218), (Sat.Literal.neg 107)] :=
  (lex_8_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3710), (Sat.Literal.neg 218), (Sat.Literal.neg 107), (Sat.Literal.pos 3711)] :=
  (lex_8_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3710), (Sat.Literal.pos 218), (Sat.Literal.pos 107), (Sat.Literal.pos 3711)] :=
  (lex_8_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3711) = lexBefore s permutation8 217 := by
  exact (positive_lex_of_descriptor s 3711 permutation8 218 (by rfl)).trans ((lex_skipped s permutation8 217 218 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation8 217) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation8 217 by rw [image8_eq]; rfl))

theorem lex_8_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3712) (Sat.Literal.pos 3711) (Sat.Literal.pos 217) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation8 217 (assignment s)
    (Sat.Literal.pos 3712) (Sat.Literal.pos 3711) (Sat.Literal.pos 217) (Sat.Literal.pos 103) (positive_of_descriptor s 3712 (.lex permutation8 217) (by rfl)) (lex_8_217_prefix s) (positive_select s 217) (lex_8_217_image s)

theorem lex_8_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3711), (Sat.Literal.pos 217), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation8 217 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3711) (Sat.Literal.pos 217) (Sat.Literal.pos 103) (lex_8_217_prefix s) (positive_select s 217) (lex_8_217_image s)

theorem lex_8_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3712), (Sat.Literal.pos 3711)] :=
  (lex_8_217_gate s).prop _ (List.Mem.head _)

theorem lex_8_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3712), (Sat.Literal.neg 217), (Sat.Literal.pos 103)] :=
  (lex_8_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3712), (Sat.Literal.pos 217), (Sat.Literal.neg 103)] :=
  (lex_8_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3711), (Sat.Literal.neg 217), (Sat.Literal.neg 103), (Sat.Literal.pos 3712)] :=
  (lex_8_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3711), (Sat.Literal.pos 217), (Sat.Literal.pos 103), (Sat.Literal.pos 3712)] :=
  (lex_8_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3712) = lexBefore s permutation8 216 := by
  exact (positive_lex_of_descriptor s 3712 permutation8 217 (by rfl)).trans ((lex_skipped s permutation8 216 217 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation8 216) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation8 216 by rw [image8_eq]; rfl))

theorem lex_8_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3713) (Sat.Literal.pos 3712) (Sat.Literal.pos 216) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation8 216 (assignment s)
    (Sat.Literal.pos 3713) (Sat.Literal.pos 3712) (Sat.Literal.pos 216) (Sat.Literal.pos 99) (positive_of_descriptor s 3713 (.lex permutation8 216) (by rfl)) (lex_8_216_prefix s) (positive_select s 216) (lex_8_216_image s)

theorem lex_8_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3712), (Sat.Literal.pos 216), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation8 216 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3712) (Sat.Literal.pos 216) (Sat.Literal.pos 99) (lex_8_216_prefix s) (positive_select s 216) (lex_8_216_image s)

theorem lex_8_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3713), (Sat.Literal.pos 3712)] :=
  (lex_8_216_gate s).prop _ (List.Mem.head _)

theorem lex_8_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3713), (Sat.Literal.neg 216), (Sat.Literal.pos 99)] :=
  (lex_8_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3713), (Sat.Literal.pos 216), (Sat.Literal.neg 99)] :=
  (lex_8_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3712), (Sat.Literal.neg 216), (Sat.Literal.neg 99), (Sat.Literal.pos 3713)] :=
  (lex_8_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3712), (Sat.Literal.pos 216), (Sat.Literal.pos 99), (Sat.Literal.pos 3713)] :=
  (lex_8_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3713) = lexBefore s permutation8 215 := by
  exact (positive_lex_of_descriptor s 3713 permutation8 216 (by rfl)).trans ((lex_skipped s permutation8 215 216 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation8 215) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation8 215 by rw [image8_eq]; rfl))

theorem lex_8_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3714) (Sat.Literal.pos 3713) (Sat.Literal.pos 215) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation8 215 (assignment s)
    (Sat.Literal.pos 3714) (Sat.Literal.pos 3713) (Sat.Literal.pos 215) (Sat.Literal.pos 95) (positive_of_descriptor s 3714 (.lex permutation8 215) (by rfl)) (lex_8_215_prefix s) (positive_select s 215) (lex_8_215_image s)

theorem lex_8_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3713), (Sat.Literal.pos 215), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation8 215 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3713) (Sat.Literal.pos 215) (Sat.Literal.pos 95) (lex_8_215_prefix s) (positive_select s 215) (lex_8_215_image s)

theorem lex_8_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3714), (Sat.Literal.pos 3713)] :=
  (lex_8_215_gate s).prop _ (List.Mem.head _)

theorem lex_8_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3714), (Sat.Literal.neg 215), (Sat.Literal.pos 95)] :=
  (lex_8_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3714), (Sat.Literal.pos 215), (Sat.Literal.neg 95)] :=
  (lex_8_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3713), (Sat.Literal.neg 215), (Sat.Literal.neg 95), (Sat.Literal.pos 3714)] :=
  (lex_8_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3713), (Sat.Literal.pos 215), (Sat.Literal.pos 95), (Sat.Literal.pos 3714)] :=
  (lex_8_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3714) = lexBefore s permutation8 214 := by
  exact (positive_lex_of_descriptor s 3714 permutation8 215 (by rfl)).trans ((lex_skipped s permutation8 214 215 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation8 214) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation8 214 by rw [image8_eq]; rfl))

theorem lex_8_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3715) (Sat.Literal.pos 3714) (Sat.Literal.pos 214) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation8 214 (assignment s)
    (Sat.Literal.pos 3715) (Sat.Literal.pos 3714) (Sat.Literal.pos 214) (Sat.Literal.pos 91) (positive_of_descriptor s 3715 (.lex permutation8 214) (by rfl)) (lex_8_214_prefix s) (positive_select s 214) (lex_8_214_image s)

theorem lex_8_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3714), (Sat.Literal.pos 214), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation8 214 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3714) (Sat.Literal.pos 214) (Sat.Literal.pos 91) (lex_8_214_prefix s) (positive_select s 214) (lex_8_214_image s)

theorem lex_8_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3715), (Sat.Literal.pos 3714)] :=
  (lex_8_214_gate s).prop _ (List.Mem.head _)

theorem lex_8_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3715), (Sat.Literal.neg 214), (Sat.Literal.pos 91)] :=
  (lex_8_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3715), (Sat.Literal.pos 214), (Sat.Literal.neg 91)] :=
  (lex_8_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3714), (Sat.Literal.neg 214), (Sat.Literal.neg 91), (Sat.Literal.pos 3715)] :=
  (lex_8_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3714), (Sat.Literal.pos 214), (Sat.Literal.pos 91), (Sat.Literal.pos 3715)] :=
  (lex_8_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3715) = lexBefore s permutation8 213 := by
  exact (positive_lex_of_descriptor s 3715 permutation8 214 (by rfl)).trans ((lex_skipped s permutation8 213 214 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation8 213) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation8 213 by rw [image8_eq]; rfl))

theorem lex_8_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3716) (Sat.Literal.pos 3715) (Sat.Literal.pos 213) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation8 213 (assignment s)
    (Sat.Literal.pos 3716) (Sat.Literal.pos 3715) (Sat.Literal.pos 213) (Sat.Literal.pos 87) (positive_of_descriptor s 3716 (.lex permutation8 213) (by rfl)) (lex_8_213_prefix s) (positive_select s 213) (lex_8_213_image s)

theorem lex_8_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3715), (Sat.Literal.pos 213), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation8 213 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3715) (Sat.Literal.pos 213) (Sat.Literal.pos 87) (lex_8_213_prefix s) (positive_select s 213) (lex_8_213_image s)

theorem lex_8_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3716), (Sat.Literal.pos 3715)] :=
  (lex_8_213_gate s).prop _ (List.Mem.head _)

theorem lex_8_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3716), (Sat.Literal.neg 213), (Sat.Literal.pos 87)] :=
  (lex_8_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3716), (Sat.Literal.pos 213), (Sat.Literal.neg 87)] :=
  (lex_8_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3715), (Sat.Literal.neg 213), (Sat.Literal.neg 87), (Sat.Literal.pos 3716)] :=
  (lex_8_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3715), (Sat.Literal.pos 213), (Sat.Literal.pos 87), (Sat.Literal.pos 3716)] :=
  (lex_8_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3716) = lexBefore s permutation8 212 := by
  exact (positive_lex_of_descriptor s 3716 permutation8 213 (by rfl)).trans ((lex_skipped s permutation8 212 213 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation8 212) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation8 212 by rw [image8_eq]; rfl))

theorem lex_8_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3717) (Sat.Literal.pos 3716) (Sat.Literal.pos 212) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation8 212 (assignment s)
    (Sat.Literal.pos 3717) (Sat.Literal.pos 3716) (Sat.Literal.pos 212) (Sat.Literal.pos 83) (positive_of_descriptor s 3717 (.lex permutation8 212) (by rfl)) (lex_8_212_prefix s) (positive_select s 212) (lex_8_212_image s)

theorem lex_8_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3716), (Sat.Literal.pos 212), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation8 212 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3716) (Sat.Literal.pos 212) (Sat.Literal.pos 83) (lex_8_212_prefix s) (positive_select s 212) (lex_8_212_image s)

theorem lex_8_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3717), (Sat.Literal.pos 3716)] :=
  (lex_8_212_gate s).prop _ (List.Mem.head _)

theorem lex_8_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3717), (Sat.Literal.neg 212), (Sat.Literal.pos 83)] :=
  (lex_8_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3717), (Sat.Literal.pos 212), (Sat.Literal.neg 83)] :=
  (lex_8_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3716), (Sat.Literal.neg 212), (Sat.Literal.neg 83), (Sat.Literal.pos 3717)] :=
  (lex_8_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3716), (Sat.Literal.pos 212), (Sat.Literal.pos 83), (Sat.Literal.pos 3717)] :=
  (lex_8_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3717) = lexBefore s permutation8 211 := by
  exact (positive_lex_of_descriptor s 3717 permutation8 212 (by rfl)).trans ((lex_skipped s permutation8 211 212 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation8 211) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation8 211 by rw [image8_eq]; rfl))

theorem lex_8_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3718) (Sat.Literal.pos 3717) (Sat.Literal.pos 211) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation8 211 (assignment s)
    (Sat.Literal.pos 3718) (Sat.Literal.pos 3717) (Sat.Literal.pos 211) (Sat.Literal.pos 79) (positive_of_descriptor s 3718 (.lex permutation8 211) (by rfl)) (lex_8_211_prefix s) (positive_select s 211) (lex_8_211_image s)

theorem lex_8_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3717), (Sat.Literal.pos 211), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation8 211 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3717) (Sat.Literal.pos 211) (Sat.Literal.pos 79) (lex_8_211_prefix s) (positive_select s 211) (lex_8_211_image s)

theorem lex_8_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3718), (Sat.Literal.pos 3717)] :=
  (lex_8_211_gate s).prop _ (List.Mem.head _)

theorem lex_8_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3718), (Sat.Literal.neg 211), (Sat.Literal.pos 79)] :=
  (lex_8_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3718), (Sat.Literal.pos 211), (Sat.Literal.neg 79)] :=
  (lex_8_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3717), (Sat.Literal.neg 211), (Sat.Literal.neg 79), (Sat.Literal.pos 3718)] :=
  (lex_8_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3717), (Sat.Literal.pos 211), (Sat.Literal.pos 79), (Sat.Literal.pos 3718)] :=
  (lex_8_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3718) = lexBefore s permutation8 210 := by
  exact (positive_lex_of_descriptor s 3718 permutation8 211 (by rfl)).trans ((lex_skipped s permutation8 210 211 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation8 210) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation8 210 by rw [image8_eq]; rfl))

theorem lex_8_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3719) (Sat.Literal.pos 3718) (Sat.Literal.pos 210) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation8 210 (assignment s)
    (Sat.Literal.pos 3719) (Sat.Literal.pos 3718) (Sat.Literal.pos 210) (Sat.Literal.pos 75) (positive_of_descriptor s 3719 (.lex permutation8 210) (by rfl)) (lex_8_210_prefix s) (positive_select s 210) (lex_8_210_image s)

theorem lex_8_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3718), (Sat.Literal.pos 210), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation8 210 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3718) (Sat.Literal.pos 210) (Sat.Literal.pos 75) (lex_8_210_prefix s) (positive_select s 210) (lex_8_210_image s)

theorem lex_8_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3719), (Sat.Literal.pos 3718)] :=
  (lex_8_210_gate s).prop _ (List.Mem.head _)

theorem lex_8_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3719), (Sat.Literal.neg 210), (Sat.Literal.pos 75)] :=
  (lex_8_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3719), (Sat.Literal.pos 210), (Sat.Literal.neg 75)] :=
  (lex_8_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3718), (Sat.Literal.neg 210), (Sat.Literal.neg 75), (Sat.Literal.pos 3719)] :=
  (lex_8_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3718), (Sat.Literal.pos 210), (Sat.Literal.pos 75), (Sat.Literal.pos 3719)] :=
  (lex_8_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3719) = lexBefore s permutation8 209 := by
  exact (positive_lex_of_descriptor s 3719 permutation8 210 (by rfl)).trans ((lex_skipped s permutation8 209 210 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation8 209) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation8 209 by rw [image8_eq]; rfl))

theorem lex_8_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3720) (Sat.Literal.pos 3719) (Sat.Literal.pos 209) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation8 209 (assignment s)
    (Sat.Literal.pos 3720) (Sat.Literal.pos 3719) (Sat.Literal.pos 209) (Sat.Literal.pos 71) (positive_of_descriptor s 3720 (.lex permutation8 209) (by rfl)) (lex_8_209_prefix s) (positive_select s 209) (lex_8_209_image s)

theorem lex_8_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3719), (Sat.Literal.pos 209), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation8 209 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3719) (Sat.Literal.pos 209) (Sat.Literal.pos 71) (lex_8_209_prefix s) (positive_select s 209) (lex_8_209_image s)

theorem lex_8_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3720), (Sat.Literal.pos 3719)] :=
  (lex_8_209_gate s).prop _ (List.Mem.head _)

theorem lex_8_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3720), (Sat.Literal.neg 209), (Sat.Literal.pos 71)] :=
  (lex_8_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3720), (Sat.Literal.pos 209), (Sat.Literal.neg 71)] :=
  (lex_8_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3719), (Sat.Literal.neg 209), (Sat.Literal.neg 71), (Sat.Literal.pos 3720)] :=
  (lex_8_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3719), (Sat.Literal.pos 209), (Sat.Literal.pos 71), (Sat.Literal.pos 3720)] :=
  (lex_8_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3720) = lexBefore s permutation8 208 := by
  exact (positive_lex_of_descriptor s 3720 permutation8 209 (by rfl)).trans ((lex_skipped s permutation8 208 209 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation8 208) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation8 208 by rw [image8_eq]; rfl))

theorem lex_8_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3721) (Sat.Literal.pos 3720) (Sat.Literal.pos 208) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation8 208 (assignment s)
    (Sat.Literal.pos 3721) (Sat.Literal.pos 3720) (Sat.Literal.pos 208) (Sat.Literal.pos 67) (positive_of_descriptor s 3721 (.lex permutation8 208) (by rfl)) (lex_8_208_prefix s) (positive_select s 208) (lex_8_208_image s)

theorem lex_8_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3720), (Sat.Literal.pos 208), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation8 208 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3720) (Sat.Literal.pos 208) (Sat.Literal.pos 67) (lex_8_208_prefix s) (positive_select s 208) (lex_8_208_image s)

theorem lex_8_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3721), (Sat.Literal.pos 3720)] :=
  (lex_8_208_gate s).prop _ (List.Mem.head _)

theorem lex_8_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3721), (Sat.Literal.neg 208), (Sat.Literal.pos 67)] :=
  (lex_8_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3721), (Sat.Literal.pos 208), (Sat.Literal.neg 67)] :=
  (lex_8_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3720), (Sat.Literal.neg 208), (Sat.Literal.neg 67), (Sat.Literal.pos 3721)] :=
  (lex_8_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3720), (Sat.Literal.pos 208), (Sat.Literal.pos 67), (Sat.Literal.pos 3721)] :=
  (lex_8_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3721) = lexBefore s permutation8 207 := by
  exact (positive_lex_of_descriptor s 3721 permutation8 208 (by rfl)).trans ((lex_skipped s permutation8 207 208 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation8 207) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation8 207 by rw [image8_eq]; rfl))

theorem lex_8_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3722) (Sat.Literal.pos 3721) (Sat.Literal.pos 207) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation8 207 (assignment s)
    (Sat.Literal.pos 3722) (Sat.Literal.pos 3721) (Sat.Literal.pos 207) (Sat.Literal.pos 63) (positive_of_descriptor s 3722 (.lex permutation8 207) (by rfl)) (lex_8_207_prefix s) (positive_select s 207) (lex_8_207_image s)

theorem lex_8_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3721), (Sat.Literal.pos 207), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation8 207 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3721) (Sat.Literal.pos 207) (Sat.Literal.pos 63) (lex_8_207_prefix s) (positive_select s 207) (lex_8_207_image s)

theorem lex_8_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3722), (Sat.Literal.pos 3721)] :=
  (lex_8_207_gate s).prop _ (List.Mem.head _)

theorem lex_8_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3722), (Sat.Literal.neg 207), (Sat.Literal.pos 63)] :=
  (lex_8_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3722), (Sat.Literal.pos 207), (Sat.Literal.neg 63)] :=
  (lex_8_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3721), (Sat.Literal.neg 207), (Sat.Literal.neg 63), (Sat.Literal.pos 3722)] :=
  (lex_8_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3721), (Sat.Literal.pos 207), (Sat.Literal.pos 63), (Sat.Literal.pos 3722)] :=
  (lex_8_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3722) = lexBefore s permutation8 206 := by
  exact (positive_lex_of_descriptor s 3722 permutation8 207 (by rfl)).trans ((lex_skipped s permutation8 206 207 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation8 206) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation8 206 by rw [image8_eq]; rfl))

theorem lex_8_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3723) (Sat.Literal.pos 3722) (Sat.Literal.pos 206) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation8 206 (assignment s)
    (Sat.Literal.pos 3723) (Sat.Literal.pos 3722) (Sat.Literal.pos 206) (Sat.Literal.pos 59) (positive_of_descriptor s 3723 (.lex permutation8 206) (by rfl)) (lex_8_206_prefix s) (positive_select s 206) (lex_8_206_image s)

theorem lex_8_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3722), (Sat.Literal.pos 206), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation8 206 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3722) (Sat.Literal.pos 206) (Sat.Literal.pos 59) (lex_8_206_prefix s) (positive_select s 206) (lex_8_206_image s)

theorem lex_8_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3723), (Sat.Literal.pos 3722)] :=
  (lex_8_206_gate s).prop _ (List.Mem.head _)

theorem lex_8_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3723), (Sat.Literal.neg 206), (Sat.Literal.pos 59)] :=
  (lex_8_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3723), (Sat.Literal.pos 206), (Sat.Literal.neg 59)] :=
  (lex_8_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3722), (Sat.Literal.neg 206), (Sat.Literal.neg 59), (Sat.Literal.pos 3723)] :=
  (lex_8_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3722), (Sat.Literal.pos 206), (Sat.Literal.pos 59), (Sat.Literal.pos 3723)] :=
  (lex_8_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3723) = lexBefore s permutation8 205 := by
  exact (positive_lex_of_descriptor s 3723 permutation8 206 (by rfl)).trans ((lex_skipped s permutation8 205 206 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation8 205) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation8 205 by rw [image8_eq]; rfl))

theorem lex_8_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3724) (Sat.Literal.pos 3723) (Sat.Literal.pos 205) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation8 205 (assignment s)
    (Sat.Literal.pos 3724) (Sat.Literal.pos 3723) (Sat.Literal.pos 205) (Sat.Literal.pos 55) (positive_of_descriptor s 3724 (.lex permutation8 205) (by rfl)) (lex_8_205_prefix s) (positive_select s 205) (lex_8_205_image s)

theorem lex_8_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3723), (Sat.Literal.pos 205), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation8 205 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3723) (Sat.Literal.pos 205) (Sat.Literal.pos 55) (lex_8_205_prefix s) (positive_select s 205) (lex_8_205_image s)

theorem lex_8_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3724), (Sat.Literal.pos 3723)] :=
  (lex_8_205_gate s).prop _ (List.Mem.head _)

theorem lex_8_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3724), (Sat.Literal.neg 205), (Sat.Literal.pos 55)] :=
  (lex_8_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3724), (Sat.Literal.pos 205), (Sat.Literal.neg 55)] :=
  (lex_8_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3723), (Sat.Literal.neg 205), (Sat.Literal.neg 55), (Sat.Literal.pos 3724)] :=
  (lex_8_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3723), (Sat.Literal.pos 205), (Sat.Literal.pos 55), (Sat.Literal.pos 3724)] :=
  (lex_8_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_7_50_gate

end Crown.CertificateData
