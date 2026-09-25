import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_11_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4624) = lexBefore s permutation11 50 := by
  exact (positive_lex_of_descriptor s 4624 permutation11 51 (by rfl)).trans ((lex_skipped s permutation11 50 51 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation11 50) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation11 50 by rw [image11_eq]; rfl))

theorem lex_11_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4625) (Sat.Literal.pos 4624) (Sat.Literal.pos 50) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation11 50 (assignment s)
    (Sat.Literal.pos 4625) (Sat.Literal.pos 4624) (Sat.Literal.pos 50) (Sat.Literal.pos 70) (positive_of_descriptor s 4625 (.lex permutation11 50) (by rfl)) (lex_11_50_prefix s) (positive_select s 50) (lex_11_50_image s)

theorem lex_11_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4624), (Sat.Literal.pos 50), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation11 50 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4624) (Sat.Literal.pos 50) (Sat.Literal.pos 70) (lex_11_50_prefix s) (positive_select s 50) (lex_11_50_image s)

theorem lex_11_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4625), (Sat.Literal.pos 4624)] :=
  (lex_11_50_gate s).prop _ (List.Mem.head _)

theorem lex_11_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4625), (Sat.Literal.neg 50), (Sat.Literal.pos 70)] :=
  (lex_11_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4625), (Sat.Literal.pos 50), (Sat.Literal.neg 70)] :=
  (lex_11_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4624), (Sat.Literal.neg 50), (Sat.Literal.neg 70), (Sat.Literal.pos 4625)] :=
  (lex_11_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4624), (Sat.Literal.pos 50), (Sat.Literal.pos 70), (Sat.Literal.pos 4625)] :=
  (lex_11_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4625) = lexBefore s permutation11 49 := by
  exact (positive_lex_of_descriptor s 4625 permutation11 50 (by rfl)).trans ((lex_skipped s permutation11 49 50 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation11 49) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation11 49 by rw [image11_eq]; rfl))

theorem lex_11_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4626) (Sat.Literal.pos 4625) (Sat.Literal.pos 49) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation11 49 (assignment s)
    (Sat.Literal.pos 4626) (Sat.Literal.pos 4625) (Sat.Literal.pos 49) (Sat.Literal.pos 38) (positive_of_descriptor s 4626 (.lex permutation11 49) (by rfl)) (lex_11_49_prefix s) (positive_select s 49) (lex_11_49_image s)

theorem lex_11_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4625), (Sat.Literal.pos 49), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation11 49 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4625) (Sat.Literal.pos 49) (Sat.Literal.pos 38) (lex_11_49_prefix s) (positive_select s 49) (lex_11_49_image s)

theorem lex_11_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4626), (Sat.Literal.pos 4625)] :=
  (lex_11_49_gate s).prop _ (List.Mem.head _)

theorem lex_11_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4626), (Sat.Literal.neg 49), (Sat.Literal.pos 38)] :=
  (lex_11_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4626), (Sat.Literal.pos 49), (Sat.Literal.neg 38)] :=
  (lex_11_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4625), (Sat.Literal.neg 49), (Sat.Literal.neg 38), (Sat.Literal.pos 4626)] :=
  (lex_11_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4625), (Sat.Literal.pos 49), (Sat.Literal.pos 38), (Sat.Literal.pos 4626)] :=
  (lex_11_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4626) = lexBefore s permutation11 48 := by
  exact (positive_lex_of_descriptor s 4626 permutation11 49 (by rfl)).trans ((lex_skipped s permutation11 48 49 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation11 48) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation11 48 by rw [image11_eq]; rfl))

theorem lex_11_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4627) (Sat.Literal.pos 4626) (Sat.Literal.pos 48) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation11 48 (assignment s)
    (Sat.Literal.pos 4627) (Sat.Literal.pos 4626) (Sat.Literal.pos 48) (Sat.Literal.pos 6) (positive_of_descriptor s 4627 (.lex permutation11 48) (by rfl)) (lex_11_48_prefix s) (positive_select s 48) (lex_11_48_image s)

theorem lex_11_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4626), (Sat.Literal.pos 48), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation11 48 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4626) (Sat.Literal.pos 48) (Sat.Literal.pos 6) (lex_11_48_prefix s) (positive_select s 48) (lex_11_48_image s)

theorem lex_11_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4627), (Sat.Literal.pos 4626)] :=
  (lex_11_48_gate s).prop _ (List.Mem.head _)

theorem lex_11_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4627), (Sat.Literal.neg 48), (Sat.Literal.pos 6)] :=
  (lex_11_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4627), (Sat.Literal.pos 48), (Sat.Literal.neg 6)] :=
  (lex_11_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4626), (Sat.Literal.neg 48), (Sat.Literal.neg 6), (Sat.Literal.pos 4627)] :=
  (lex_11_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4626), (Sat.Literal.pos 48), (Sat.Literal.pos 6), (Sat.Literal.pos 4627)] :=
  (lex_11_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4627) = lexBefore s permutation11 47 := by
  exact (positive_lex_of_descriptor s 4627 permutation11 48 (by rfl)).trans ((lex_skipped s permutation11 47 48 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation11 47) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation11 47 by rw [image11_eq]; rfl))

theorem lex_11_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4628) (Sat.Literal.pos 4627) (Sat.Literal.pos 47) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation11 47 (assignment s)
    (Sat.Literal.pos 4628) (Sat.Literal.pos 4627) (Sat.Literal.pos 47) (Sat.Literal.pos 229) (positive_of_descriptor s 4628 (.lex permutation11 47) (by rfl)) (lex_11_47_prefix s) (positive_select s 47) (lex_11_47_image s)

theorem lex_11_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4627), (Sat.Literal.pos 47), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation11 47 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4627) (Sat.Literal.pos 47) (Sat.Literal.pos 229) (lex_11_47_prefix s) (positive_select s 47) (lex_11_47_image s)

theorem lex_11_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4628), (Sat.Literal.pos 4627)] :=
  (lex_11_47_gate s).prop _ (List.Mem.head _)

theorem lex_11_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4628), (Sat.Literal.neg 47), (Sat.Literal.pos 229)] :=
  (lex_11_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4628), (Sat.Literal.pos 47), (Sat.Literal.neg 229)] :=
  (lex_11_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4627), (Sat.Literal.neg 47), (Sat.Literal.neg 229), (Sat.Literal.pos 4628)] :=
  (lex_11_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4627), (Sat.Literal.pos 47), (Sat.Literal.pos 229), (Sat.Literal.pos 4628)] :=
  (lex_11_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4628) = lexBefore s permutation11 46 := by
  exact (positive_lex_of_descriptor s 4628 permutation11 47 (by rfl)).trans ((lex_skipped s permutation11 46 47 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation11 46) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation11 46 by rw [image11_eq]; rfl))

theorem lex_11_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4629) (Sat.Literal.pos 4628) (Sat.Literal.pos 46) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation11 46 (assignment s)
    (Sat.Literal.pos 4629) (Sat.Literal.pos 4628) (Sat.Literal.pos 46) (Sat.Literal.pos 197) (positive_of_descriptor s 4629 (.lex permutation11 46) (by rfl)) (lex_11_46_prefix s) (positive_select s 46) (lex_11_46_image s)

theorem lex_11_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4628), (Sat.Literal.pos 46), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation11 46 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4628) (Sat.Literal.pos 46) (Sat.Literal.pos 197) (lex_11_46_prefix s) (positive_select s 46) (lex_11_46_image s)

theorem lex_11_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4629), (Sat.Literal.pos 4628)] :=
  (lex_11_46_gate s).prop _ (List.Mem.head _)

theorem lex_11_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4629), (Sat.Literal.neg 46), (Sat.Literal.pos 197)] :=
  (lex_11_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4629), (Sat.Literal.pos 46), (Sat.Literal.neg 197)] :=
  (lex_11_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4628), (Sat.Literal.neg 46), (Sat.Literal.neg 197), (Sat.Literal.pos 4629)] :=
  (lex_11_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4628), (Sat.Literal.pos 46), (Sat.Literal.pos 197), (Sat.Literal.pos 4629)] :=
  (lex_11_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4629) = lexBefore s permutation11 45 := by
  exact (positive_lex_of_descriptor s 4629 permutation11 46 (by rfl)).trans ((lex_skipped s permutation11 45 46 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation11 45) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation11 45 by rw [image11_eq]; rfl))

theorem lex_11_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4630) (Sat.Literal.pos 4629) (Sat.Literal.pos 45) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation11 45 (assignment s)
    (Sat.Literal.pos 4630) (Sat.Literal.pos 4629) (Sat.Literal.pos 45) (Sat.Literal.pos 165) (positive_of_descriptor s 4630 (.lex permutation11 45) (by rfl)) (lex_11_45_prefix s) (positive_select s 45) (lex_11_45_image s)

theorem lex_11_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4629), (Sat.Literal.pos 45), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation11 45 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4629) (Sat.Literal.pos 45) (Sat.Literal.pos 165) (lex_11_45_prefix s) (positive_select s 45) (lex_11_45_image s)

theorem lex_11_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4630), (Sat.Literal.pos 4629)] :=
  (lex_11_45_gate s).prop _ (List.Mem.head _)

theorem lex_11_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4630), (Sat.Literal.neg 45), (Sat.Literal.pos 165)] :=
  (lex_11_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4630), (Sat.Literal.pos 45), (Sat.Literal.neg 165)] :=
  (lex_11_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4629), (Sat.Literal.neg 45), (Sat.Literal.neg 165), (Sat.Literal.pos 4630)] :=
  (lex_11_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4629), (Sat.Literal.pos 45), (Sat.Literal.pos 165), (Sat.Literal.pos 4630)] :=
  (lex_11_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4630) = lexBefore s permutation11 44 := by
  exact (positive_lex_of_descriptor s 4630 permutation11 45 (by rfl)).trans ((lex_skipped s permutation11 44 45 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation11 44) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation11 44 by rw [image11_eq]; rfl))

theorem lex_11_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4631) (Sat.Literal.pos 4630) (Sat.Literal.pos 44) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation11 44 (assignment s)
    (Sat.Literal.pos 4631) (Sat.Literal.pos 4630) (Sat.Literal.pos 44) (Sat.Literal.pos 133) (positive_of_descriptor s 4631 (.lex permutation11 44) (by rfl)) (lex_11_44_prefix s) (positive_select s 44) (lex_11_44_image s)

theorem lex_11_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4630), (Sat.Literal.pos 44), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation11 44 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4630) (Sat.Literal.pos 44) (Sat.Literal.pos 133) (lex_11_44_prefix s) (positive_select s 44) (lex_11_44_image s)

theorem lex_11_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4631), (Sat.Literal.pos 4630)] :=
  (lex_11_44_gate s).prop _ (List.Mem.head _)

theorem lex_11_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4631), (Sat.Literal.neg 44), (Sat.Literal.pos 133)] :=
  (lex_11_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4631), (Sat.Literal.pos 44), (Sat.Literal.neg 133)] :=
  (lex_11_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4630), (Sat.Literal.neg 44), (Sat.Literal.neg 133), (Sat.Literal.pos 4631)] :=
  (lex_11_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4630), (Sat.Literal.pos 44), (Sat.Literal.pos 133), (Sat.Literal.pos 4631)] :=
  (lex_11_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4631) = lexBefore s permutation11 43 := by
  exact (positive_lex_of_descriptor s 4631 permutation11 44 (by rfl)).trans ((lex_skipped s permutation11 43 44 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation11 43) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation11 43 by rw [image11_eq]; rfl))

theorem lex_11_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4632) (Sat.Literal.pos 4631) (Sat.Literal.pos 43) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation11 43 (assignment s)
    (Sat.Literal.pos 4632) (Sat.Literal.pos 4631) (Sat.Literal.pos 43) (Sat.Literal.pos 101) (positive_of_descriptor s 4632 (.lex permutation11 43) (by rfl)) (lex_11_43_prefix s) (positive_select s 43) (lex_11_43_image s)

theorem lex_11_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4631), (Sat.Literal.pos 43), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation11 43 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4631) (Sat.Literal.pos 43) (Sat.Literal.pos 101) (lex_11_43_prefix s) (positive_select s 43) (lex_11_43_image s)

theorem lex_11_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4632), (Sat.Literal.pos 4631)] :=
  (lex_11_43_gate s).prop _ (List.Mem.head _)

theorem lex_11_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4632), (Sat.Literal.neg 43), (Sat.Literal.pos 101)] :=
  (lex_11_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4632), (Sat.Literal.pos 43), (Sat.Literal.neg 101)] :=
  (lex_11_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4631), (Sat.Literal.neg 43), (Sat.Literal.neg 101), (Sat.Literal.pos 4632)] :=
  (lex_11_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4631), (Sat.Literal.pos 43), (Sat.Literal.pos 101), (Sat.Literal.pos 4632)] :=
  (lex_11_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4632) = lexBefore s permutation11 42 := by
  exact (positive_lex_of_descriptor s 4632 permutation11 43 (by rfl)).trans ((lex_skipped s permutation11 42 43 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation11 42) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation11 42 by rw [image11_eq]; rfl))

theorem lex_11_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4633) (Sat.Literal.pos 4632) (Sat.Literal.pos 42) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation11 42 (assignment s)
    (Sat.Literal.pos 4633) (Sat.Literal.pos 4632) (Sat.Literal.pos 42) (Sat.Literal.pos 69) (positive_of_descriptor s 4633 (.lex permutation11 42) (by rfl)) (lex_11_42_prefix s) (positive_select s 42) (lex_11_42_image s)

theorem lex_11_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4632), (Sat.Literal.pos 42), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation11 42 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4632) (Sat.Literal.pos 42) (Sat.Literal.pos 69) (lex_11_42_prefix s) (positive_select s 42) (lex_11_42_image s)

theorem lex_11_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4633), (Sat.Literal.pos 4632)] :=
  (lex_11_42_gate s).prop _ (List.Mem.head _)

theorem lex_11_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4633), (Sat.Literal.neg 42), (Sat.Literal.pos 69)] :=
  (lex_11_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4633), (Sat.Literal.pos 42), (Sat.Literal.neg 69)] :=
  (lex_11_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4632), (Sat.Literal.neg 42), (Sat.Literal.neg 69), (Sat.Literal.pos 4633)] :=
  (lex_11_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4632), (Sat.Literal.pos 42), (Sat.Literal.pos 69), (Sat.Literal.pos 4633)] :=
  (lex_11_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4633) = lexBefore s permutation11 41 := by
  exact (positive_lex_of_descriptor s 4633 permutation11 42 (by rfl)).trans ((lex_skipped s permutation11 41 42 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation11 41) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation11 41 by rw [image11_eq]; rfl))

theorem lex_11_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4634) (Sat.Literal.pos 4633) (Sat.Literal.pos 41) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation11 41 (assignment s)
    (Sat.Literal.pos 4634) (Sat.Literal.pos 4633) (Sat.Literal.pos 41) (Sat.Literal.pos 37) (positive_of_descriptor s 4634 (.lex permutation11 41) (by rfl)) (lex_11_41_prefix s) (positive_select s 41) (lex_11_41_image s)

theorem lex_11_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4633), (Sat.Literal.pos 41), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation11 41 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4633) (Sat.Literal.pos 41) (Sat.Literal.pos 37) (lex_11_41_prefix s) (positive_select s 41) (lex_11_41_image s)

theorem lex_11_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4634), (Sat.Literal.pos 4633)] :=
  (lex_11_41_gate s).prop _ (List.Mem.head _)

theorem lex_11_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4634), (Sat.Literal.neg 41), (Sat.Literal.pos 37)] :=
  (lex_11_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4634), (Sat.Literal.pos 41), (Sat.Literal.neg 37)] :=
  (lex_11_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4633), (Sat.Literal.neg 41), (Sat.Literal.neg 37), (Sat.Literal.pos 4634)] :=
  (lex_11_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4633), (Sat.Literal.pos 41), (Sat.Literal.pos 37), (Sat.Literal.pos 4634)] :=
  (lex_11_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4634) = lexBefore s permutation11 40 := by
  exact (positive_lex_of_descriptor s 4634 permutation11 41 (by rfl)).trans ((lex_skipped s permutation11 40 41 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation11 40) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation11 40 by rw [image11_eq]; rfl))

theorem lex_11_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4635) (Sat.Literal.pos 4634) (Sat.Literal.pos 40) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation11 40 (assignment s)
    (Sat.Literal.pos 4635) (Sat.Literal.pos 4634) (Sat.Literal.pos 40) (Sat.Literal.pos 5) (positive_of_descriptor s 4635 (.lex permutation11 40) (by rfl)) (lex_11_40_prefix s) (positive_select s 40) (lex_11_40_image s)

theorem lex_11_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4634), (Sat.Literal.pos 40), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation11 40 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4634) (Sat.Literal.pos 40) (Sat.Literal.pos 5) (lex_11_40_prefix s) (positive_select s 40) (lex_11_40_image s)

theorem lex_11_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4635), (Sat.Literal.pos 4634)] :=
  (lex_11_40_gate s).prop _ (List.Mem.head _)

theorem lex_11_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4635), (Sat.Literal.neg 40), (Sat.Literal.pos 5)] :=
  (lex_11_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4635), (Sat.Literal.pos 40), (Sat.Literal.neg 5)] :=
  (lex_11_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4634), (Sat.Literal.neg 40), (Sat.Literal.neg 5), (Sat.Literal.pos 4635)] :=
  (lex_11_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4634), (Sat.Literal.pos 40), (Sat.Literal.pos 5), (Sat.Literal.pos 4635)] :=
  (lex_11_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4635) = lexBefore s permutation11 39 := by
  exact (positive_lex_of_descriptor s 4635 permutation11 40 (by rfl)).trans ((lex_skipped s permutation11 39 40 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation11 39) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation11 39 by rw [image11_eq]; rfl))

theorem lex_11_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4636) (Sat.Literal.pos 4635) (Sat.Literal.pos 39) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation11 39 (assignment s)
    (Sat.Literal.pos 4636) (Sat.Literal.pos 4635) (Sat.Literal.pos 39) (Sat.Literal.pos 228) (positive_of_descriptor s 4636 (.lex permutation11 39) (by rfl)) (lex_11_39_prefix s) (positive_select s 39) (lex_11_39_image s)

theorem lex_11_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4635), (Sat.Literal.pos 39), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation11 39 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4635) (Sat.Literal.pos 39) (Sat.Literal.pos 228) (lex_11_39_prefix s) (positive_select s 39) (lex_11_39_image s)

theorem lex_11_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4636), (Sat.Literal.pos 4635)] :=
  (lex_11_39_gate s).prop _ (List.Mem.head _)

theorem lex_11_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4636), (Sat.Literal.neg 39), (Sat.Literal.pos 228)] :=
  (lex_11_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4636), (Sat.Literal.pos 39), (Sat.Literal.neg 228)] :=
  (lex_11_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4635), (Sat.Literal.neg 39), (Sat.Literal.neg 228), (Sat.Literal.pos 4636)] :=
  (lex_11_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4635), (Sat.Literal.pos 39), (Sat.Literal.pos 228), (Sat.Literal.pos 4636)] :=
  (lex_11_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4636) = lexBefore s permutation11 38 := by
  exact (positive_lex_of_descriptor s 4636 permutation11 39 (by rfl)).trans ((lex_skipped s permutation11 38 39 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation11 38) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation11 38 by rw [image11_eq]; rfl))

theorem lex_11_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4637) (Sat.Literal.pos 4636) (Sat.Literal.pos 38) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation11 38 (assignment s)
    (Sat.Literal.pos 4637) (Sat.Literal.pos 4636) (Sat.Literal.pos 38) (Sat.Literal.pos 196) (positive_of_descriptor s 4637 (.lex permutation11 38) (by rfl)) (lex_11_38_prefix s) (positive_select s 38) (lex_11_38_image s)

theorem lex_11_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4636), (Sat.Literal.pos 38), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation11 38 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4636) (Sat.Literal.pos 38) (Sat.Literal.pos 196) (lex_11_38_prefix s) (positive_select s 38) (lex_11_38_image s)

theorem lex_11_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4637), (Sat.Literal.pos 4636)] :=
  (lex_11_38_gate s).prop _ (List.Mem.head _)

theorem lex_11_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4637), (Sat.Literal.neg 38), (Sat.Literal.pos 196)] :=
  (lex_11_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4637), (Sat.Literal.pos 38), (Sat.Literal.neg 196)] :=
  (lex_11_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4636), (Sat.Literal.neg 38), (Sat.Literal.neg 196), (Sat.Literal.pos 4637)] :=
  (lex_11_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4636), (Sat.Literal.pos 38), (Sat.Literal.pos 196), (Sat.Literal.pos 4637)] :=
  (lex_11_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4637) = lexBefore s permutation11 37 := by
  exact (positive_lex_of_descriptor s 4637 permutation11 38 (by rfl)).trans ((lex_skipped s permutation11 37 38 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation11 37) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation11 37 by rw [image11_eq]; rfl))

theorem lex_11_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4638) (Sat.Literal.pos 4637) (Sat.Literal.pos 37) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation11 37 (assignment s)
    (Sat.Literal.pos 4638) (Sat.Literal.pos 4637) (Sat.Literal.pos 37) (Sat.Literal.pos 164) (positive_of_descriptor s 4638 (.lex permutation11 37) (by rfl)) (lex_11_37_prefix s) (positive_select s 37) (lex_11_37_image s)

theorem lex_11_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4637), (Sat.Literal.pos 37), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation11 37 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4637) (Sat.Literal.pos 37) (Sat.Literal.pos 164) (lex_11_37_prefix s) (positive_select s 37) (lex_11_37_image s)

theorem lex_11_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4638), (Sat.Literal.pos 4637)] :=
  (lex_11_37_gate s).prop _ (List.Mem.head _)

theorem lex_11_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4638), (Sat.Literal.neg 37), (Sat.Literal.pos 164)] :=
  (lex_11_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4638), (Sat.Literal.pos 37), (Sat.Literal.neg 164)] :=
  (lex_11_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4637), (Sat.Literal.neg 37), (Sat.Literal.neg 164), (Sat.Literal.pos 4638)] :=
  (lex_11_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4637), (Sat.Literal.pos 37), (Sat.Literal.pos 164), (Sat.Literal.pos 4638)] :=
  (lex_11_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4638) = lexBefore s permutation11 36 := by
  exact (positive_lex_of_descriptor s 4638 permutation11 37 (by rfl)).trans ((lex_skipped s permutation11 36 37 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation11 36) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation11 36 by rw [image11_eq]; rfl))

theorem lex_11_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4639) (Sat.Literal.pos 4638) (Sat.Literal.pos 36) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation11 36 (assignment s)
    (Sat.Literal.pos 4639) (Sat.Literal.pos 4638) (Sat.Literal.pos 36) (Sat.Literal.pos 132) (positive_of_descriptor s 4639 (.lex permutation11 36) (by rfl)) (lex_11_36_prefix s) (positive_select s 36) (lex_11_36_image s)

theorem lex_11_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4638), (Sat.Literal.pos 36), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation11 36 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4638) (Sat.Literal.pos 36) (Sat.Literal.pos 132) (lex_11_36_prefix s) (positive_select s 36) (lex_11_36_image s)

theorem lex_11_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4639), (Sat.Literal.pos 4638)] :=
  (lex_11_36_gate s).prop _ (List.Mem.head _)

theorem lex_11_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4639), (Sat.Literal.neg 36), (Sat.Literal.pos 132)] :=
  (lex_11_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4639), (Sat.Literal.pos 36), (Sat.Literal.neg 132)] :=
  (lex_11_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4638), (Sat.Literal.neg 36), (Sat.Literal.neg 132), (Sat.Literal.pos 4639)] :=
  (lex_11_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4638), (Sat.Literal.pos 36), (Sat.Literal.pos 132), (Sat.Literal.pos 4639)] :=
  (lex_11_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4639) = lexBefore s permutation11 35 := by
  exact (positive_lex_of_descriptor s 4639 permutation11 36 (by rfl)).trans ((lex_skipped s permutation11 35 36 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation11 35) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation11 35 by rw [image11_eq]; rfl))

theorem lex_11_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4640) (Sat.Literal.pos 4639) (Sat.Literal.pos 35) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation11 35 (assignment s)
    (Sat.Literal.pos 4640) (Sat.Literal.pos 4639) (Sat.Literal.pos 35) (Sat.Literal.pos 100) (positive_of_descriptor s 4640 (.lex permutation11 35) (by rfl)) (lex_11_35_prefix s) (positive_select s 35) (lex_11_35_image s)

theorem lex_11_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4639), (Sat.Literal.pos 35), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation11 35 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4639) (Sat.Literal.pos 35) (Sat.Literal.pos 100) (lex_11_35_prefix s) (positive_select s 35) (lex_11_35_image s)

theorem lex_11_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4640), (Sat.Literal.pos 4639)] :=
  (lex_11_35_gate s).prop _ (List.Mem.head _)

theorem lex_11_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4640), (Sat.Literal.neg 35), (Sat.Literal.pos 100)] :=
  (lex_11_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4640), (Sat.Literal.pos 35), (Sat.Literal.neg 100)] :=
  (lex_11_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4639), (Sat.Literal.neg 35), (Sat.Literal.neg 100), (Sat.Literal.pos 4640)] :=
  (lex_11_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4639), (Sat.Literal.pos 35), (Sat.Literal.pos 100), (Sat.Literal.pos 4640)] :=
  (lex_11_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4640) = lexBefore s permutation11 34 := by
  exact (positive_lex_of_descriptor s 4640 permutation11 35 (by rfl)).trans ((lex_skipped s permutation11 34 35 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation11 34) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation11 34 by rw [image11_eq]; rfl))

theorem lex_11_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4641) (Sat.Literal.pos 4640) (Sat.Literal.pos 34) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation11 34 (assignment s)
    (Sat.Literal.pos 4641) (Sat.Literal.pos 4640) (Sat.Literal.pos 34) (Sat.Literal.pos 68) (positive_of_descriptor s 4641 (.lex permutation11 34) (by rfl)) (lex_11_34_prefix s) (positive_select s 34) (lex_11_34_image s)

theorem lex_11_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4640), (Sat.Literal.pos 34), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation11 34 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4640) (Sat.Literal.pos 34) (Sat.Literal.pos 68) (lex_11_34_prefix s) (positive_select s 34) (lex_11_34_image s)

theorem lex_11_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4641), (Sat.Literal.pos 4640)] :=
  (lex_11_34_gate s).prop _ (List.Mem.head _)

theorem lex_11_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4641), (Sat.Literal.neg 34), (Sat.Literal.pos 68)] :=
  (lex_11_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4641), (Sat.Literal.pos 34), (Sat.Literal.neg 68)] :=
  (lex_11_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4640), (Sat.Literal.neg 34), (Sat.Literal.neg 68), (Sat.Literal.pos 4641)] :=
  (lex_11_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4640), (Sat.Literal.pos 34), (Sat.Literal.pos 68), (Sat.Literal.pos 4641)] :=
  (lex_11_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4641) = lexBefore s permutation11 33 := by
  exact (positive_lex_of_descriptor s 4641 permutation11 34 (by rfl)).trans ((lex_skipped s permutation11 33 34 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 36) = s (permuteMask permutation11 33) := by
  exact (positive_select s 36).trans (congrArg s (show (36 : Fin 256) = permuteMask permutation11 33 by rw [image11_eq]; rfl))

theorem lex_11_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4642) (Sat.Literal.pos 4641) (Sat.Literal.pos 33) (Sat.Literal.pos 36)) := by
  exact equality_gate s permutation11 33 (assignment s)
    (Sat.Literal.pos 4642) (Sat.Literal.pos 4641) (Sat.Literal.pos 33) (Sat.Literal.pos 36) (positive_of_descriptor s 4642 (.lex permutation11 33) (by rfl)) (lex_11_33_prefix s) (positive_select s 33) (lex_11_33_image s)

theorem lex_11_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4641), (Sat.Literal.pos 33), (Sat.Literal.neg 36)] := by
  exact comparison_gate s permutation11 33 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4641) (Sat.Literal.pos 33) (Sat.Literal.pos 36) (lex_11_33_prefix s) (positive_select s 33) (lex_11_33_image s)

theorem lex_11_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4642), (Sat.Literal.pos 4641)] :=
  (lex_11_33_gate s).prop _ (List.Mem.head _)

theorem lex_11_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4642), (Sat.Literal.neg 33), (Sat.Literal.pos 36)] :=
  (lex_11_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4642), (Sat.Literal.pos 33), (Sat.Literal.neg 36)] :=
  (lex_11_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4641), (Sat.Literal.neg 33), (Sat.Literal.neg 36), (Sat.Literal.pos 4642)] :=
  (lex_11_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4641), (Sat.Literal.pos 33), (Sat.Literal.pos 36), (Sat.Literal.pos 4642)] :=
  (lex_11_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4642) = lexBefore s permutation11 32 := by
  exact (positive_lex_of_descriptor s 4642 permutation11 33 (by rfl)).trans ((lex_skipped s permutation11 32 33 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation11 32) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation11 32 by rw [image11_eq]; rfl))

theorem lex_11_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4643) (Sat.Literal.pos 4642) (Sat.Literal.pos 32) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation11 32 (assignment s)
    (Sat.Literal.pos 4643) (Sat.Literal.pos 4642) (Sat.Literal.pos 32) (Sat.Literal.pos 4) (positive_of_descriptor s 4643 (.lex permutation11 32) (by rfl)) (lex_11_32_prefix s) (positive_select s 32) (lex_11_32_image s)

theorem lex_11_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4642), (Sat.Literal.pos 32), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation11 32 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4642) (Sat.Literal.pos 32) (Sat.Literal.pos 4) (lex_11_32_prefix s) (positive_select s 32) (lex_11_32_image s)

theorem lex_11_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4643), (Sat.Literal.pos 4642)] :=
  (lex_11_32_gate s).prop _ (List.Mem.head _)

theorem lex_11_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4643), (Sat.Literal.neg 32), (Sat.Literal.pos 4)] :=
  (lex_11_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4643), (Sat.Literal.pos 32), (Sat.Literal.neg 4)] :=
  (lex_11_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4642), (Sat.Literal.neg 32), (Sat.Literal.neg 4), (Sat.Literal.pos 4643)] :=
  (lex_11_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4642), (Sat.Literal.pos 32), (Sat.Literal.pos 4), (Sat.Literal.pos 4643)] :=
  (lex_11_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4643) = lexBefore s permutation11 31 := by
  exact (positive_lex_of_descriptor s 4643 permutation11 32 (by rfl)).trans ((lex_skipped s permutation11 31 32 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation11 31) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation11 31 by rw [image11_eq]; rfl))

theorem lex_11_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4644) (Sat.Literal.pos 4643) (Sat.Literal.pos 31) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation11 31 (assignment s)
    (Sat.Literal.pos 4644) (Sat.Literal.pos 4643) (Sat.Literal.pos 31) (Sat.Literal.pos 227) (positive_of_descriptor s 4644 (.lex permutation11 31) (by rfl)) (lex_11_31_prefix s) (positive_select s 31) (lex_11_31_image s)

theorem lex_11_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4643), (Sat.Literal.pos 31), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation11 31 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4643) (Sat.Literal.pos 31) (Sat.Literal.pos 227) (lex_11_31_prefix s) (positive_select s 31) (lex_11_31_image s)

theorem lex_11_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4644), (Sat.Literal.pos 4643)] :=
  (lex_11_31_gate s).prop _ (List.Mem.head _)

theorem lex_11_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4644), (Sat.Literal.neg 31), (Sat.Literal.pos 227)] :=
  (lex_11_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4644), (Sat.Literal.pos 31), (Sat.Literal.neg 227)] :=
  (lex_11_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4643), (Sat.Literal.neg 31), (Sat.Literal.neg 227), (Sat.Literal.pos 4644)] :=
  (lex_11_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4643), (Sat.Literal.pos 31), (Sat.Literal.pos 227), (Sat.Literal.pos 4644)] :=
  (lex_11_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4644) = lexBefore s permutation11 30 := by
  exact (positive_lex_of_descriptor s 4644 permutation11 31 (by rfl)).trans ((lex_skipped s permutation11 30 31 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation11 30) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation11 30 by rw [image11_eq]; rfl))

theorem lex_11_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4645) (Sat.Literal.pos 4644) (Sat.Literal.pos 30) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation11 30 (assignment s)
    (Sat.Literal.pos 4645) (Sat.Literal.pos 4644) (Sat.Literal.pos 30) (Sat.Literal.pos 195) (positive_of_descriptor s 4645 (.lex permutation11 30) (by rfl)) (lex_11_30_prefix s) (positive_select s 30) (lex_11_30_image s)

theorem lex_11_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4644), (Sat.Literal.pos 30), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation11 30 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4644) (Sat.Literal.pos 30) (Sat.Literal.pos 195) (lex_11_30_prefix s) (positive_select s 30) (lex_11_30_image s)

theorem lex_11_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4645), (Sat.Literal.pos 4644)] :=
  (lex_11_30_gate s).prop _ (List.Mem.head _)

theorem lex_11_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4645), (Sat.Literal.neg 30), (Sat.Literal.pos 195)] :=
  (lex_11_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4645), (Sat.Literal.pos 30), (Sat.Literal.neg 195)] :=
  (lex_11_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4644), (Sat.Literal.neg 30), (Sat.Literal.neg 195), (Sat.Literal.pos 4645)] :=
  (lex_11_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4644), (Sat.Literal.pos 30), (Sat.Literal.pos 195), (Sat.Literal.pos 4645)] :=
  (lex_11_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4645) = lexBefore s permutation11 29 := by
  exact (positive_lex_of_descriptor s 4645 permutation11 30 (by rfl)).trans ((lex_skipped s permutation11 29 30 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation11 29) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation11 29 by rw [image11_eq]; rfl))

theorem lex_11_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4646) (Sat.Literal.pos 4645) (Sat.Literal.pos 29) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation11 29 (assignment s)
    (Sat.Literal.pos 4646) (Sat.Literal.pos 4645) (Sat.Literal.pos 29) (Sat.Literal.pos 163) (positive_of_descriptor s 4646 (.lex permutation11 29) (by rfl)) (lex_11_29_prefix s) (positive_select s 29) (lex_11_29_image s)

theorem lex_11_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4645), (Sat.Literal.pos 29), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation11 29 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4645) (Sat.Literal.pos 29) (Sat.Literal.pos 163) (lex_11_29_prefix s) (positive_select s 29) (lex_11_29_image s)

theorem lex_11_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4646), (Sat.Literal.pos 4645)] :=
  (lex_11_29_gate s).prop _ (List.Mem.head _)

theorem lex_11_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4646), (Sat.Literal.neg 29), (Sat.Literal.pos 163)] :=
  (lex_11_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4646), (Sat.Literal.pos 29), (Sat.Literal.neg 163)] :=
  (lex_11_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4645), (Sat.Literal.neg 29), (Sat.Literal.neg 163), (Sat.Literal.pos 4646)] :=
  (lex_11_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4645), (Sat.Literal.pos 29), (Sat.Literal.pos 163), (Sat.Literal.pos 4646)] :=
  (lex_11_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4646) = lexBefore s permutation11 28 := by
  exact (positive_lex_of_descriptor s 4646 permutation11 29 (by rfl)).trans ((lex_skipped s permutation11 28 29 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation11 28) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation11 28 by rw [image11_eq]; rfl))

theorem lex_11_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4647) (Sat.Literal.pos 4646) (Sat.Literal.pos 28) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation11 28 (assignment s)
    (Sat.Literal.pos 4647) (Sat.Literal.pos 4646) (Sat.Literal.pos 28) (Sat.Literal.pos 131) (positive_of_descriptor s 4647 (.lex permutation11 28) (by rfl)) (lex_11_28_prefix s) (positive_select s 28) (lex_11_28_image s)

theorem lex_11_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4646), (Sat.Literal.pos 28), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation11 28 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4646) (Sat.Literal.pos 28) (Sat.Literal.pos 131) (lex_11_28_prefix s) (positive_select s 28) (lex_11_28_image s)

theorem lex_11_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4647), (Sat.Literal.pos 4646)] :=
  (lex_11_28_gate s).prop _ (List.Mem.head _)

theorem lex_11_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4647), (Sat.Literal.neg 28), (Sat.Literal.pos 131)] :=
  (lex_11_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4647), (Sat.Literal.pos 28), (Sat.Literal.neg 131)] :=
  (lex_11_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4646), (Sat.Literal.neg 28), (Sat.Literal.neg 131), (Sat.Literal.pos 4647)] :=
  (lex_11_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4646), (Sat.Literal.pos 28), (Sat.Literal.pos 131), (Sat.Literal.pos 4647)] :=
  (lex_11_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4647) = lexBefore s permutation11 27 := by
  exact (positive_lex_of_descriptor s 4647 permutation11 28 (by rfl)).trans ((lex_skipped s permutation11 27 28 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation11 27) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation11 27 by rw [image11_eq]; rfl))

theorem lex_11_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4648) (Sat.Literal.pos 4647) (Sat.Literal.pos 27) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation11 27 (assignment s)
    (Sat.Literal.pos 4648) (Sat.Literal.pos 4647) (Sat.Literal.pos 27) (Sat.Literal.pos 99) (positive_of_descriptor s 4648 (.lex permutation11 27) (by rfl)) (lex_11_27_prefix s) (positive_select s 27) (lex_11_27_image s)

theorem lex_11_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4647), (Sat.Literal.pos 27), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation11 27 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4647) (Sat.Literal.pos 27) (Sat.Literal.pos 99) (lex_11_27_prefix s) (positive_select s 27) (lex_11_27_image s)

theorem lex_11_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4648), (Sat.Literal.pos 4647)] :=
  (lex_11_27_gate s).prop _ (List.Mem.head _)

theorem lex_11_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4648), (Sat.Literal.neg 27), (Sat.Literal.pos 99)] :=
  (lex_11_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4648), (Sat.Literal.pos 27), (Sat.Literal.neg 99)] :=
  (lex_11_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4647), (Sat.Literal.neg 27), (Sat.Literal.neg 99), (Sat.Literal.pos 4648)] :=
  (lex_11_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4647), (Sat.Literal.pos 27), (Sat.Literal.pos 99), (Sat.Literal.pos 4648)] :=
  (lex_11_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4648) = lexBefore s permutation11 26 := by
  exact (positive_lex_of_descriptor s 4648 permutation11 27 (by rfl)).trans ((lex_skipped s permutation11 26 27 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation11 26) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation11 26 by rw [image11_eq]; rfl))

theorem lex_11_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4649) (Sat.Literal.pos 4648) (Sat.Literal.pos 26) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation11 26 (assignment s)
    (Sat.Literal.pos 4649) (Sat.Literal.pos 4648) (Sat.Literal.pos 26) (Sat.Literal.pos 67) (positive_of_descriptor s 4649 (.lex permutation11 26) (by rfl)) (lex_11_26_prefix s) (positive_select s 26) (lex_11_26_image s)

theorem lex_11_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4648), (Sat.Literal.pos 26), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation11 26 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4648) (Sat.Literal.pos 26) (Sat.Literal.pos 67) (lex_11_26_prefix s) (positive_select s 26) (lex_11_26_image s)

theorem lex_11_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4649), (Sat.Literal.pos 4648)] :=
  (lex_11_26_gate s).prop _ (List.Mem.head _)

theorem lex_11_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4649), (Sat.Literal.neg 26), (Sat.Literal.pos 67)] :=
  (lex_11_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4649), (Sat.Literal.pos 26), (Sat.Literal.neg 67)] :=
  (lex_11_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4648), (Sat.Literal.neg 26), (Sat.Literal.neg 67), (Sat.Literal.pos 4649)] :=
  (lex_11_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4648), (Sat.Literal.pos 26), (Sat.Literal.pos 67), (Sat.Literal.pos 4649)] :=
  (lex_11_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4649) = lexBefore s permutation11 25 := by
  exact (positive_lex_of_descriptor s 4649 permutation11 26 (by rfl)).trans ((lex_skipped s permutation11 25 26 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 35) = s (permuteMask permutation11 25) := by
  exact (positive_select s 35).trans (congrArg s (show (35 : Fin 256) = permuteMask permutation11 25 by rw [image11_eq]; rfl))

theorem lex_11_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4650) (Sat.Literal.pos 4649) (Sat.Literal.pos 25) (Sat.Literal.pos 35)) := by
  exact equality_gate s permutation11 25 (assignment s)
    (Sat.Literal.pos 4650) (Sat.Literal.pos 4649) (Sat.Literal.pos 25) (Sat.Literal.pos 35) (positive_of_descriptor s 4650 (.lex permutation11 25) (by rfl)) (lex_11_25_prefix s) (positive_select s 25) (lex_11_25_image s)

theorem lex_11_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4649), (Sat.Literal.pos 25), (Sat.Literal.neg 35)] := by
  exact comparison_gate s permutation11 25 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4649) (Sat.Literal.pos 25) (Sat.Literal.pos 35) (lex_11_25_prefix s) (positive_select s 25) (lex_11_25_image s)

theorem lex_11_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4650), (Sat.Literal.pos 4649)] :=
  (lex_11_25_gate s).prop _ (List.Mem.head _)

theorem lex_11_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4650), (Sat.Literal.neg 25), (Sat.Literal.pos 35)] :=
  (lex_11_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4650), (Sat.Literal.pos 25), (Sat.Literal.neg 35)] :=
  (lex_11_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4649), (Sat.Literal.neg 25), (Sat.Literal.neg 35), (Sat.Literal.pos 4650)] :=
  (lex_11_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4649), (Sat.Literal.pos 25), (Sat.Literal.pos 35), (Sat.Literal.pos 4650)] :=
  (lex_11_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4650) = lexBefore s permutation11 24 := by
  exact (positive_lex_of_descriptor s 4650 permutation11 25 (by rfl)).trans ((lex_skipped s permutation11 24 25 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation11 24) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation11 24 by rw [image11_eq]; rfl))

theorem lex_11_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4651) (Sat.Literal.pos 4650) (Sat.Literal.pos 24) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation11 24 (assignment s)
    (Sat.Literal.pos 4651) (Sat.Literal.pos 4650) (Sat.Literal.pos 24) (Sat.Literal.pos 3) (positive_of_descriptor s 4651 (.lex permutation11 24) (by rfl)) (lex_11_24_prefix s) (positive_select s 24) (lex_11_24_image s)

theorem lex_11_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4650), (Sat.Literal.pos 24), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation11 24 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4650) (Sat.Literal.pos 24) (Sat.Literal.pos 3) (lex_11_24_prefix s) (positive_select s 24) (lex_11_24_image s)

theorem lex_11_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4651), (Sat.Literal.pos 4650)] :=
  (lex_11_24_gate s).prop _ (List.Mem.head _)

theorem lex_11_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4651), (Sat.Literal.neg 24), (Sat.Literal.pos 3)] :=
  (lex_11_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4651), (Sat.Literal.pos 24), (Sat.Literal.neg 3)] :=
  (lex_11_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4650), (Sat.Literal.neg 24), (Sat.Literal.neg 3), (Sat.Literal.pos 4651)] :=
  (lex_11_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4650), (Sat.Literal.pos 24), (Sat.Literal.pos 3), (Sat.Literal.pos 4651)] :=
  (lex_11_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4651) = lexBefore s permutation11 23 := by
  exact (positive_lex_of_descriptor s 4651 permutation11 24 (by rfl)).trans ((lex_skipped s permutation11 23 24 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation11 23) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation11 23 by rw [image11_eq]; rfl))

theorem lex_11_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4652) (Sat.Literal.pos 4651) (Sat.Literal.pos 23) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation11 23 (assignment s)
    (Sat.Literal.pos 4652) (Sat.Literal.pos 4651) (Sat.Literal.pos 23) (Sat.Literal.pos 226) (positive_of_descriptor s 4652 (.lex permutation11 23) (by rfl)) (lex_11_23_prefix s) (positive_select s 23) (lex_11_23_image s)

theorem lex_11_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4651), (Sat.Literal.pos 23), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation11 23 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4651) (Sat.Literal.pos 23) (Sat.Literal.pos 226) (lex_11_23_prefix s) (positive_select s 23) (lex_11_23_image s)

theorem lex_11_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4652), (Sat.Literal.pos 4651)] :=
  (lex_11_23_gate s).prop _ (List.Mem.head _)

theorem lex_11_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4652), (Sat.Literal.neg 23), (Sat.Literal.pos 226)] :=
  (lex_11_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4652), (Sat.Literal.pos 23), (Sat.Literal.neg 226)] :=
  (lex_11_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4651), (Sat.Literal.neg 23), (Sat.Literal.neg 226), (Sat.Literal.pos 4652)] :=
  (lex_11_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4651), (Sat.Literal.pos 23), (Sat.Literal.pos 226), (Sat.Literal.pos 4652)] :=
  (lex_11_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4652) = lexBefore s permutation11 22 := by
  exact (positive_lex_of_descriptor s 4652 permutation11 23 (by rfl)).trans ((lex_skipped s permutation11 22 23 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation11 22) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation11 22 by rw [image11_eq]; rfl))

theorem lex_11_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4653) (Sat.Literal.pos 4652) (Sat.Literal.pos 22) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation11 22 (assignment s)
    (Sat.Literal.pos 4653) (Sat.Literal.pos 4652) (Sat.Literal.pos 22) (Sat.Literal.pos 194) (positive_of_descriptor s 4653 (.lex permutation11 22) (by rfl)) (lex_11_22_prefix s) (positive_select s 22) (lex_11_22_image s)

theorem lex_11_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4652), (Sat.Literal.pos 22), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation11 22 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4652) (Sat.Literal.pos 22) (Sat.Literal.pos 194) (lex_11_22_prefix s) (positive_select s 22) (lex_11_22_image s)

theorem lex_11_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4653), (Sat.Literal.pos 4652)] :=
  (lex_11_22_gate s).prop _ (List.Mem.head _)

theorem lex_11_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4653), (Sat.Literal.neg 22), (Sat.Literal.pos 194)] :=
  (lex_11_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4653), (Sat.Literal.pos 22), (Sat.Literal.neg 194)] :=
  (lex_11_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4652), (Sat.Literal.neg 22), (Sat.Literal.neg 194), (Sat.Literal.pos 4653)] :=
  (lex_11_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4652), (Sat.Literal.pos 22), (Sat.Literal.pos 194), (Sat.Literal.pos 4653)] :=
  (lex_11_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4653) = lexBefore s permutation11 21 := by
  exact (positive_lex_of_descriptor s 4653 permutation11 22 (by rfl)).trans ((lex_skipped s permutation11 21 22 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation11 21) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation11 21 by rw [image11_eq]; rfl))

theorem lex_11_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4654) (Sat.Literal.pos 4653) (Sat.Literal.pos 21) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation11 21 (assignment s)
    (Sat.Literal.pos 4654) (Sat.Literal.pos 4653) (Sat.Literal.pos 21) (Sat.Literal.pos 162) (positive_of_descriptor s 4654 (.lex permutation11 21) (by rfl)) (lex_11_21_prefix s) (positive_select s 21) (lex_11_21_image s)

theorem lex_11_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4653), (Sat.Literal.pos 21), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation11 21 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4653) (Sat.Literal.pos 21) (Sat.Literal.pos 162) (lex_11_21_prefix s) (positive_select s 21) (lex_11_21_image s)

theorem lex_11_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4654), (Sat.Literal.pos 4653)] :=
  (lex_11_21_gate s).prop _ (List.Mem.head _)

theorem lex_11_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4654), (Sat.Literal.neg 21), (Sat.Literal.pos 162)] :=
  (lex_11_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4654), (Sat.Literal.pos 21), (Sat.Literal.neg 162)] :=
  (lex_11_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4653), (Sat.Literal.neg 21), (Sat.Literal.neg 162), (Sat.Literal.pos 4654)] :=
  (lex_11_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4653), (Sat.Literal.pos 21), (Sat.Literal.pos 162), (Sat.Literal.pos 4654)] :=
  (lex_11_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4654) = lexBefore s permutation11 20 := by
  exact (positive_lex_of_descriptor s 4654 permutation11 21 (by rfl)).trans ((lex_skipped s permutation11 20 21 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation11 20) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation11 20 by rw [image11_eq]; rfl))

theorem lex_11_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4655) (Sat.Literal.pos 4654) (Sat.Literal.pos 20) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation11 20 (assignment s)
    (Sat.Literal.pos 4655) (Sat.Literal.pos 4654) (Sat.Literal.pos 20) (Sat.Literal.pos 130) (positive_of_descriptor s 4655 (.lex permutation11 20) (by rfl)) (lex_11_20_prefix s) (positive_select s 20) (lex_11_20_image s)

theorem lex_11_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4654), (Sat.Literal.pos 20), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation11 20 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4654) (Sat.Literal.pos 20) (Sat.Literal.pos 130) (lex_11_20_prefix s) (positive_select s 20) (lex_11_20_image s)

theorem lex_11_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4655), (Sat.Literal.pos 4654)] :=
  (lex_11_20_gate s).prop _ (List.Mem.head _)

theorem lex_11_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4655), (Sat.Literal.neg 20), (Sat.Literal.pos 130)] :=
  (lex_11_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4655), (Sat.Literal.pos 20), (Sat.Literal.neg 130)] :=
  (lex_11_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4654), (Sat.Literal.neg 20), (Sat.Literal.neg 130), (Sat.Literal.pos 4655)] :=
  (lex_11_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4654), (Sat.Literal.pos 20), (Sat.Literal.pos 130), (Sat.Literal.pos 4655)] :=
  (lex_11_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4655) = lexBefore s permutation11 19 := by
  exact (positive_lex_of_descriptor s 4655 permutation11 20 (by rfl)).trans ((lex_skipped s permutation11 19 20 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation11 19) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation11 19 by rw [image11_eq]; rfl))

theorem lex_11_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4656) (Sat.Literal.pos 4655) (Sat.Literal.pos 19) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation11 19 (assignment s)
    (Sat.Literal.pos 4656) (Sat.Literal.pos 4655) (Sat.Literal.pos 19) (Sat.Literal.pos 98) (positive_of_descriptor s 4656 (.lex permutation11 19) (by rfl)) (lex_11_19_prefix s) (positive_select s 19) (lex_11_19_image s)

theorem lex_11_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4655), (Sat.Literal.pos 19), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation11 19 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4655) (Sat.Literal.pos 19) (Sat.Literal.pos 98) (lex_11_19_prefix s) (positive_select s 19) (lex_11_19_image s)

theorem lex_11_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4656), (Sat.Literal.pos 4655)] :=
  (lex_11_19_gate s).prop _ (List.Mem.head _)

theorem lex_11_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4656), (Sat.Literal.neg 19), (Sat.Literal.pos 98)] :=
  (lex_11_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4656), (Sat.Literal.pos 19), (Sat.Literal.neg 98)] :=
  (lex_11_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4655), (Sat.Literal.neg 19), (Sat.Literal.neg 98), (Sat.Literal.pos 4656)] :=
  (lex_11_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4655), (Sat.Literal.pos 19), (Sat.Literal.pos 98), (Sat.Literal.pos 4656)] :=
  (lex_11_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4656) = lexBefore s permutation11 18 := by
  exact (positive_lex_of_descriptor s 4656 permutation11 19 (by rfl)).trans ((lex_skipped s permutation11 18 19 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation11 18) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation11 18 by rw [image11_eq]; rfl))

theorem lex_11_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4657) (Sat.Literal.pos 4656) (Sat.Literal.pos 18) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation11 18 (assignment s)
    (Sat.Literal.pos 4657) (Sat.Literal.pos 4656) (Sat.Literal.pos 18) (Sat.Literal.pos 66) (positive_of_descriptor s 4657 (.lex permutation11 18) (by rfl)) (lex_11_18_prefix s) (positive_select s 18) (lex_11_18_image s)

theorem lex_11_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4656), (Sat.Literal.pos 18), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation11 18 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4656) (Sat.Literal.pos 18) (Sat.Literal.pos 66) (lex_11_18_prefix s) (positive_select s 18) (lex_11_18_image s)

theorem lex_11_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4657), (Sat.Literal.pos 4656)] :=
  (lex_11_18_gate s).prop _ (List.Mem.head _)

theorem lex_11_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4657), (Sat.Literal.neg 18), (Sat.Literal.pos 66)] :=
  (lex_11_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4657), (Sat.Literal.pos 18), (Sat.Literal.neg 66)] :=
  (lex_11_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4656), (Sat.Literal.neg 18), (Sat.Literal.neg 66), (Sat.Literal.pos 4657)] :=
  (lex_11_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4656), (Sat.Literal.pos 18), (Sat.Literal.pos 66), (Sat.Literal.pos 4657)] :=
  (lex_11_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4657) = lexBefore s permutation11 17 := by
  exact (positive_lex_of_descriptor s 4657 permutation11 18 (by rfl)).trans ((lex_skipped s permutation11 17 18 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation11 17) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation11 17 by rw [image11_eq]; rfl))

theorem lex_11_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4658) (Sat.Literal.pos 4657) (Sat.Literal.pos 17) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation11 17 (assignment s)
    (Sat.Literal.pos 4658) (Sat.Literal.pos 4657) (Sat.Literal.pos 17) (Sat.Literal.pos 34) (positive_of_descriptor s 4658 (.lex permutation11 17) (by rfl)) (lex_11_17_prefix s) (positive_select s 17) (lex_11_17_image s)

theorem lex_11_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4657), (Sat.Literal.pos 17), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation11 17 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4657) (Sat.Literal.pos 17) (Sat.Literal.pos 34) (lex_11_17_prefix s) (positive_select s 17) (lex_11_17_image s)

theorem lex_11_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4658), (Sat.Literal.pos 4657)] :=
  (lex_11_17_gate s).prop _ (List.Mem.head _)

theorem lex_11_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4658), (Sat.Literal.neg 17), (Sat.Literal.pos 34)] :=
  (lex_11_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4658), (Sat.Literal.pos 17), (Sat.Literal.neg 34)] :=
  (lex_11_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4657), (Sat.Literal.neg 17), (Sat.Literal.neg 34), (Sat.Literal.pos 4658)] :=
  (lex_11_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4657), (Sat.Literal.pos 17), (Sat.Literal.pos 34), (Sat.Literal.pos 4658)] :=
  (lex_11_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4658) = lexBefore s permutation11 16 := by
  exact (positive_lex_of_descriptor s 4658 permutation11 17 (by rfl)).trans ((lex_skipped s permutation11 16 17 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation11 16) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation11 16 by rw [image11_eq]; rfl))

theorem lex_11_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4659) (Sat.Literal.pos 4658) (Sat.Literal.pos 16) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation11 16 (assignment s)
    (Sat.Literal.pos 4659) (Sat.Literal.pos 4658) (Sat.Literal.pos 16) (Sat.Literal.pos 2) (positive_of_descriptor s 4659 (.lex permutation11 16) (by rfl)) (lex_11_16_prefix s) (positive_select s 16) (lex_11_16_image s)

theorem lex_11_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4658), (Sat.Literal.pos 16), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation11 16 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4658) (Sat.Literal.pos 16) (Sat.Literal.pos 2) (lex_11_16_prefix s) (positive_select s 16) (lex_11_16_image s)

theorem lex_11_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4659), (Sat.Literal.pos 4658)] :=
  (lex_11_16_gate s).prop _ (List.Mem.head _)

theorem lex_11_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4659), (Sat.Literal.neg 16), (Sat.Literal.pos 2)] :=
  (lex_11_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4659), (Sat.Literal.pos 16), (Sat.Literal.neg 2)] :=
  (lex_11_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4658), (Sat.Literal.neg 16), (Sat.Literal.neg 2), (Sat.Literal.pos 4659)] :=
  (lex_11_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4658), (Sat.Literal.pos 16), (Sat.Literal.pos 2), (Sat.Literal.pos 4659)] :=
  (lex_11_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4659) = lexBefore s permutation11 15 := by
  exact (positive_lex_of_descriptor s 4659 permutation11 16 (by rfl)).trans ((lex_skipped s permutation11 15 16 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation11 15) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation11 15 by rw [image11_eq]; rfl))

theorem lex_11_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4660) (Sat.Literal.pos 4659) (Sat.Literal.pos 15) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation11 15 (assignment s)
    (Sat.Literal.pos 4660) (Sat.Literal.pos 4659) (Sat.Literal.pos 15) (Sat.Literal.pos 225) (positive_of_descriptor s 4660 (.lex permutation11 15) (by rfl)) (lex_11_15_prefix s) (positive_select s 15) (lex_11_15_image s)

theorem lex_11_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4659), (Sat.Literal.pos 15), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation11 15 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4659) (Sat.Literal.pos 15) (Sat.Literal.pos 225) (lex_11_15_prefix s) (positive_select s 15) (lex_11_15_image s)

theorem lex_11_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4660), (Sat.Literal.pos 4659)] :=
  (lex_11_15_gate s).prop _ (List.Mem.head _)

theorem lex_11_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4660), (Sat.Literal.neg 15), (Sat.Literal.pos 225)] :=
  (lex_11_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4660), (Sat.Literal.pos 15), (Sat.Literal.neg 225)] :=
  (lex_11_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4659), (Sat.Literal.neg 15), (Sat.Literal.neg 225), (Sat.Literal.pos 4660)] :=
  (lex_11_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4659), (Sat.Literal.pos 15), (Sat.Literal.pos 225), (Sat.Literal.pos 4660)] :=
  (lex_11_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4660) = lexBefore s permutation11 14 := by
  exact (positive_lex_of_descriptor s 4660 permutation11 15 (by rfl)).trans ((lex_skipped s permutation11 14 15 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation11 14) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation11 14 by rw [image11_eq]; rfl))

theorem lex_11_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4661) (Sat.Literal.pos 4660) (Sat.Literal.pos 14) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation11 14 (assignment s)
    (Sat.Literal.pos 4661) (Sat.Literal.pos 4660) (Sat.Literal.pos 14) (Sat.Literal.pos 193) (positive_of_descriptor s 4661 (.lex permutation11 14) (by rfl)) (lex_11_14_prefix s) (positive_select s 14) (lex_11_14_image s)

theorem lex_11_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4660), (Sat.Literal.pos 14), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation11 14 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4660) (Sat.Literal.pos 14) (Sat.Literal.pos 193) (lex_11_14_prefix s) (positive_select s 14) (lex_11_14_image s)

theorem lex_11_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4661), (Sat.Literal.pos 4660)] :=
  (lex_11_14_gate s).prop _ (List.Mem.head _)

theorem lex_11_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4661), (Sat.Literal.neg 14), (Sat.Literal.pos 193)] :=
  (lex_11_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4661), (Sat.Literal.pos 14), (Sat.Literal.neg 193)] :=
  (lex_11_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4660), (Sat.Literal.neg 14), (Sat.Literal.neg 193), (Sat.Literal.pos 4661)] :=
  (lex_11_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4660), (Sat.Literal.pos 14), (Sat.Literal.pos 193), (Sat.Literal.pos 4661)] :=
  (lex_11_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4661) = lexBefore s permutation11 13 := by
  exact (positive_lex_of_descriptor s 4661 permutation11 14 (by rfl)).trans ((lex_skipped s permutation11 13 14 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation11 13) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation11 13 by rw [image11_eq]; rfl))

theorem lex_11_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4662) (Sat.Literal.pos 4661) (Sat.Literal.pos 13) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation11 13 (assignment s)
    (Sat.Literal.pos 4662) (Sat.Literal.pos 4661) (Sat.Literal.pos 13) (Sat.Literal.pos 161) (positive_of_descriptor s 4662 (.lex permutation11 13) (by rfl)) (lex_11_13_prefix s) (positive_select s 13) (lex_11_13_image s)

theorem lex_11_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4661), (Sat.Literal.pos 13), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation11 13 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4661) (Sat.Literal.pos 13) (Sat.Literal.pos 161) (lex_11_13_prefix s) (positive_select s 13) (lex_11_13_image s)

theorem lex_11_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4662), (Sat.Literal.pos 4661)] :=
  (lex_11_13_gate s).prop _ (List.Mem.head _)

theorem lex_11_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4662), (Sat.Literal.neg 13), (Sat.Literal.pos 161)] :=
  (lex_11_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4662), (Sat.Literal.pos 13), (Sat.Literal.neg 161)] :=
  (lex_11_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4661), (Sat.Literal.neg 13), (Sat.Literal.neg 161), (Sat.Literal.pos 4662)] :=
  (lex_11_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4661), (Sat.Literal.pos 13), (Sat.Literal.pos 161), (Sat.Literal.pos 4662)] :=
  (lex_11_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4662) = lexBefore s permutation11 12 := by
  exact (positive_lex_of_descriptor s 4662 permutation11 13 (by rfl)).trans ((lex_skipped s permutation11 12 13 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation11 12) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation11 12 by rw [image11_eq]; rfl))

theorem lex_11_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4663) (Sat.Literal.pos 4662) (Sat.Literal.pos 12) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation11 12 (assignment s)
    (Sat.Literal.pos 4663) (Sat.Literal.pos 4662) (Sat.Literal.pos 12) (Sat.Literal.pos 129) (positive_of_descriptor s 4663 (.lex permutation11 12) (by rfl)) (lex_11_12_prefix s) (positive_select s 12) (lex_11_12_image s)

theorem lex_11_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4662), (Sat.Literal.pos 12), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation11 12 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4662) (Sat.Literal.pos 12) (Sat.Literal.pos 129) (lex_11_12_prefix s) (positive_select s 12) (lex_11_12_image s)

theorem lex_11_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4663), (Sat.Literal.pos 4662)] :=
  (lex_11_12_gate s).prop _ (List.Mem.head _)

theorem lex_11_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4663), (Sat.Literal.neg 12), (Sat.Literal.pos 129)] :=
  (lex_11_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4663), (Sat.Literal.pos 12), (Sat.Literal.neg 129)] :=
  (lex_11_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4662), (Sat.Literal.neg 12), (Sat.Literal.neg 129), (Sat.Literal.pos 4663)] :=
  (lex_11_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4662), (Sat.Literal.pos 12), (Sat.Literal.pos 129), (Sat.Literal.pos 4663)] :=
  (lex_11_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4663) = lexBefore s permutation11 11 := by
  exact (positive_lex_of_descriptor s 4663 permutation11 12 (by rfl)).trans ((lex_skipped s permutation11 11 12 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation11 11) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation11 11 by rw [image11_eq]; rfl))

theorem lex_11_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4664) (Sat.Literal.pos 4663) (Sat.Literal.pos 11) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation11 11 (assignment s)
    (Sat.Literal.pos 4664) (Sat.Literal.pos 4663) (Sat.Literal.pos 11) (Sat.Literal.pos 97) (positive_of_descriptor s 4664 (.lex permutation11 11) (by rfl)) (lex_11_11_prefix s) (positive_select s 11) (lex_11_11_image s)

theorem lex_11_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4663), (Sat.Literal.pos 11), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation11 11 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4663) (Sat.Literal.pos 11) (Sat.Literal.pos 97) (lex_11_11_prefix s) (positive_select s 11) (lex_11_11_image s)

theorem lex_11_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4664), (Sat.Literal.pos 4663)] :=
  (lex_11_11_gate s).prop _ (List.Mem.head _)

theorem lex_11_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4664), (Sat.Literal.neg 11), (Sat.Literal.pos 97)] :=
  (lex_11_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4664), (Sat.Literal.pos 11), (Sat.Literal.neg 97)] :=
  (lex_11_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4663), (Sat.Literal.neg 11), (Sat.Literal.neg 97), (Sat.Literal.pos 4664)] :=
  (lex_11_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4663), (Sat.Literal.pos 11), (Sat.Literal.pos 97), (Sat.Literal.pos 4664)] :=
  (lex_11_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4664) = lexBefore s permutation11 10 := by
  exact (positive_lex_of_descriptor s 4664 permutation11 11 (by rfl)).trans ((lex_skipped s permutation11 10 11 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation11 10) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation11 10 by rw [image11_eq]; rfl))

theorem lex_11_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4665) (Sat.Literal.pos 4664) (Sat.Literal.pos 10) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation11 10 (assignment s)
    (Sat.Literal.pos 4665) (Sat.Literal.pos 4664) (Sat.Literal.pos 10) (Sat.Literal.pos 65) (positive_of_descriptor s 4665 (.lex permutation11 10) (by rfl)) (lex_11_10_prefix s) (positive_select s 10) (lex_11_10_image s)

theorem lex_11_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4664), (Sat.Literal.pos 10), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation11 10 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4664) (Sat.Literal.pos 10) (Sat.Literal.pos 65) (lex_11_10_prefix s) (positive_select s 10) (lex_11_10_image s)

theorem lex_11_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4665), (Sat.Literal.pos 4664)] :=
  (lex_11_10_gate s).prop _ (List.Mem.head _)

theorem lex_11_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4665), (Sat.Literal.neg 10), (Sat.Literal.pos 65)] :=
  (lex_11_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4665), (Sat.Literal.pos 10), (Sat.Literal.neg 65)] :=
  (lex_11_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4664), (Sat.Literal.neg 10), (Sat.Literal.neg 65), (Sat.Literal.pos 4665)] :=
  (lex_11_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4664), (Sat.Literal.pos 10), (Sat.Literal.pos 65), (Sat.Literal.pos 4665)] :=
  (lex_11_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4665) = lexBefore s permutation11 9 := by
  exact (positive_lex_of_descriptor s 4665 permutation11 10 (by rfl)).trans ((lex_skipped s permutation11 9 10 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation11 9) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation11 9 by rw [image11_eq]; rfl))

theorem lex_11_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4666) (Sat.Literal.pos 4665) (Sat.Literal.pos 9) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation11 9 (assignment s)
    (Sat.Literal.pos 4666) (Sat.Literal.pos 4665) (Sat.Literal.pos 9) (Sat.Literal.pos 33) (positive_of_descriptor s 4666 (.lex permutation11 9) (by rfl)) (lex_11_9_prefix s) (positive_select s 9) (lex_11_9_image s)

theorem lex_11_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4665), (Sat.Literal.pos 9), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation11 9 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4665) (Sat.Literal.pos 9) (Sat.Literal.pos 33) (lex_11_9_prefix s) (positive_select s 9) (lex_11_9_image s)

theorem lex_11_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4666), (Sat.Literal.pos 4665)] :=
  (lex_11_9_gate s).prop _ (List.Mem.head _)

theorem lex_11_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4666), (Sat.Literal.neg 9), (Sat.Literal.pos 33)] :=
  (lex_11_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4666), (Sat.Literal.pos 9), (Sat.Literal.neg 33)] :=
  (lex_11_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4665), (Sat.Literal.neg 9), (Sat.Literal.neg 33), (Sat.Literal.pos 4666)] :=
  (lex_11_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4665), (Sat.Literal.pos 9), (Sat.Literal.pos 33), (Sat.Literal.pos 4666)] :=
  (lex_11_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4666) = lexBefore s permutation11 8 := by
  exact (positive_lex_of_descriptor s 4666 permutation11 9 (by rfl)).trans ((lex_skipped s permutation11 8 9 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation11 8) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation11 8 by rw [image11_eq]; rfl))

theorem lex_11_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4667) (Sat.Literal.pos 4666) (Sat.Literal.pos 8) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation11 8 (assignment s)
    (Sat.Literal.pos 4667) (Sat.Literal.pos 4666) (Sat.Literal.pos 8) (Sat.Literal.pos 1) (positive_of_descriptor s 4667 (.lex permutation11 8) (by rfl)) (lex_11_8_prefix s) (positive_select s 8) (lex_11_8_image s)

theorem lex_11_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4666), (Sat.Literal.pos 8), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation11 8 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4666) (Sat.Literal.pos 8) (Sat.Literal.pos 1) (lex_11_8_prefix s) (positive_select s 8) (lex_11_8_image s)

theorem lex_11_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4667), (Sat.Literal.pos 4666)] :=
  (lex_11_8_gate s).prop _ (List.Mem.head _)

theorem lex_11_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4667), (Sat.Literal.neg 8), (Sat.Literal.pos 1)] :=
  (lex_11_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4667), (Sat.Literal.pos 8), (Sat.Literal.neg 1)] :=
  (lex_11_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4666), (Sat.Literal.neg 8), (Sat.Literal.neg 1), (Sat.Literal.pos 4667)] :=
  (lex_11_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4666), (Sat.Literal.pos 8), (Sat.Literal.pos 1), (Sat.Literal.pos 4667)] :=
  (lex_11_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4667) = lexBefore s permutation11 7 := by
  exact (positive_lex_of_descriptor s 4667 permutation11 8 (by rfl)).trans ((lex_skipped s permutation11 7 8 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation11 7) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation11 7 by rw [image11_eq]; rfl))

theorem lex_11_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4668) (Sat.Literal.pos 4667) (Sat.Literal.pos 7) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation11 7 (assignment s)
    (Sat.Literal.pos 4668) (Sat.Literal.pos 4667) (Sat.Literal.pos 7) (Sat.Literal.pos 224) (positive_of_descriptor s 4668 (.lex permutation11 7) (by rfl)) (lex_11_7_prefix s) (positive_select s 7) (lex_11_7_image s)

theorem lex_11_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4667), (Sat.Literal.pos 7), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation11 7 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4667) (Sat.Literal.pos 7) (Sat.Literal.pos 224) (lex_11_7_prefix s) (positive_select s 7) (lex_11_7_image s)

theorem lex_11_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4668), (Sat.Literal.pos 4667)] :=
  (lex_11_7_gate s).prop _ (List.Mem.head _)

theorem lex_11_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4668), (Sat.Literal.neg 7), (Sat.Literal.pos 224)] :=
  (lex_11_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4668), (Sat.Literal.pos 7), (Sat.Literal.neg 224)] :=
  (lex_11_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4667), (Sat.Literal.neg 7), (Sat.Literal.neg 224), (Sat.Literal.pos 4668)] :=
  (lex_11_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4667), (Sat.Literal.pos 7), (Sat.Literal.pos 224), (Sat.Literal.pos 4668)] :=
  (lex_11_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4668) = lexBefore s permutation11 6 := by
  exact (positive_lex_of_descriptor s 4668 permutation11 7 (by rfl)).trans ((lex_skipped s permutation11 6 7 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation11 6) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation11 6 by rw [image11_eq]; rfl))

theorem lex_11_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4669) (Sat.Literal.pos 4668) (Sat.Literal.pos 6) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation11 6 (assignment s)
    (Sat.Literal.pos 4669) (Sat.Literal.pos 4668) (Sat.Literal.pos 6) (Sat.Literal.pos 192) (positive_of_descriptor s 4669 (.lex permutation11 6) (by rfl)) (lex_11_6_prefix s) (positive_select s 6) (lex_11_6_image s)

theorem lex_11_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4668), (Sat.Literal.pos 6), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation11 6 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4668) (Sat.Literal.pos 6) (Sat.Literal.pos 192) (lex_11_6_prefix s) (positive_select s 6) (lex_11_6_image s)

theorem lex_11_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4669), (Sat.Literal.pos 4668)] :=
  (lex_11_6_gate s).prop _ (List.Mem.head _)

theorem lex_11_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4669), (Sat.Literal.neg 6), (Sat.Literal.pos 192)] :=
  (lex_11_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4669), (Sat.Literal.pos 6), (Sat.Literal.neg 192)] :=
  (lex_11_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4668), (Sat.Literal.neg 6), (Sat.Literal.neg 192), (Sat.Literal.pos 4669)] :=
  (lex_11_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4668), (Sat.Literal.pos 6), (Sat.Literal.pos 192), (Sat.Literal.pos 4669)] :=
  (lex_11_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4669) = lexBefore s permutation11 5 := by
  exact (positive_lex_of_descriptor s 4669 permutation11 6 (by rfl)).trans ((lex_skipped s permutation11 5 6 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation11 5) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation11 5 by rw [image11_eq]; rfl))

theorem lex_11_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4670) (Sat.Literal.pos 4669) (Sat.Literal.pos 5) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation11 5 (assignment s)
    (Sat.Literal.pos 4670) (Sat.Literal.pos 4669) (Sat.Literal.pos 5) (Sat.Literal.pos 160) (positive_of_descriptor s 4670 (.lex permutation11 5) (by rfl)) (lex_11_5_prefix s) (positive_select s 5) (lex_11_5_image s)

theorem lex_11_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4669), (Sat.Literal.pos 5), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation11 5 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4669) (Sat.Literal.pos 5) (Sat.Literal.pos 160) (lex_11_5_prefix s) (positive_select s 5) (lex_11_5_image s)

theorem lex_11_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4670), (Sat.Literal.pos 4669)] :=
  (lex_11_5_gate s).prop _ (List.Mem.head _)

theorem lex_11_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4670), (Sat.Literal.neg 5), (Sat.Literal.pos 160)] :=
  (lex_11_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4670), (Sat.Literal.pos 5), (Sat.Literal.neg 160)] :=
  (lex_11_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4669), (Sat.Literal.neg 5), (Sat.Literal.neg 160), (Sat.Literal.pos 4670)] :=
  (lex_11_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4669), (Sat.Literal.pos 5), (Sat.Literal.pos 160), (Sat.Literal.pos 4670)] :=
  (lex_11_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4670) = lexBefore s permutation11 4 := by
  exact (positive_lex_of_descriptor s 4670 permutation11 5 (by rfl)).trans ((lex_skipped s permutation11 4 5 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation11 4) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation11 4 by rw [image11_eq]; rfl))

theorem lex_11_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4671) (Sat.Literal.pos 4670) (Sat.Literal.pos 4) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation11 4 (assignment s)
    (Sat.Literal.pos 4671) (Sat.Literal.pos 4670) (Sat.Literal.pos 4) (Sat.Literal.pos 128) (positive_of_descriptor s 4671 (.lex permutation11 4) (by rfl)) (lex_11_4_prefix s) (positive_select s 4) (lex_11_4_image s)

theorem lex_11_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4670), (Sat.Literal.pos 4), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation11 4 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4670) (Sat.Literal.pos 4) (Sat.Literal.pos 128) (lex_11_4_prefix s) (positive_select s 4) (lex_11_4_image s)

theorem lex_11_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4671), (Sat.Literal.pos 4670)] :=
  (lex_11_4_gate s).prop _ (List.Mem.head _)

theorem lex_11_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4671), (Sat.Literal.neg 4), (Sat.Literal.pos 128)] :=
  (lex_11_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4671), (Sat.Literal.pos 4), (Sat.Literal.neg 128)] :=
  (lex_11_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4670), (Sat.Literal.neg 4), (Sat.Literal.neg 128), (Sat.Literal.pos 4671)] :=
  (lex_11_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4670), (Sat.Literal.pos 4), (Sat.Literal.pos 128), (Sat.Literal.pos 4671)] :=
  (lex_11_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4671) = lexBefore s permutation11 3 := by
  exact (positive_lex_of_descriptor s 4671 permutation11 4 (by rfl)).trans ((lex_skipped s permutation11 3 4 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation11 3) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation11 3 by rw [image11_eq]; rfl))

theorem lex_11_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4672) (Sat.Literal.pos 4671) (Sat.Literal.pos 3) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation11 3 (assignment s)
    (Sat.Literal.pos 4672) (Sat.Literal.pos 4671) (Sat.Literal.pos 3) (Sat.Literal.pos 96) (positive_of_descriptor s 4672 (.lex permutation11 3) (by rfl)) (lex_11_3_prefix s) (positive_select s 3) (lex_11_3_image s)

theorem lex_11_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4671), (Sat.Literal.pos 3), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation11 3 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4671) (Sat.Literal.pos 3) (Sat.Literal.pos 96) (lex_11_3_prefix s) (positive_select s 3) (lex_11_3_image s)

theorem lex_11_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4672), (Sat.Literal.pos 4671)] :=
  (lex_11_3_gate s).prop _ (List.Mem.head _)

theorem lex_11_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4672), (Sat.Literal.neg 3), (Sat.Literal.pos 96)] :=
  (lex_11_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4672), (Sat.Literal.pos 3), (Sat.Literal.neg 96)] :=
  (lex_11_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4671), (Sat.Literal.neg 3), (Sat.Literal.neg 96), (Sat.Literal.pos 4672)] :=
  (lex_11_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4671), (Sat.Literal.pos 3), (Sat.Literal.pos 96), (Sat.Literal.pos 4672)] :=
  (lex_11_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4672) = lexBefore s permutation11 2 := by
  exact (positive_lex_of_descriptor s 4672 permutation11 3 (by rfl)).trans ((lex_skipped s permutation11 2 3 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation11 2) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation11 2 by rw [image11_eq]; rfl))

theorem lex_11_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4673) (Sat.Literal.pos 4672) (Sat.Literal.pos 2) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation11 2 (assignment s)
    (Sat.Literal.pos 4673) (Sat.Literal.pos 4672) (Sat.Literal.pos 2) (Sat.Literal.pos 64) (positive_of_descriptor s 4673 (.lex permutation11 2) (by rfl)) (lex_11_2_prefix s) (positive_select s 2) (lex_11_2_image s)

theorem lex_11_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4672), (Sat.Literal.pos 2), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation11 2 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4672) (Sat.Literal.pos 2) (Sat.Literal.pos 64) (lex_11_2_prefix s) (positive_select s 2) (lex_11_2_image s)

theorem lex_11_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4673), (Sat.Literal.pos 4672)] :=
  (lex_11_2_gate s).prop _ (List.Mem.head _)

theorem lex_11_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4673), (Sat.Literal.neg 2), (Sat.Literal.pos 64)] :=
  (lex_11_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4673), (Sat.Literal.pos 2), (Sat.Literal.neg 64)] :=
  (lex_11_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4672), (Sat.Literal.neg 2), (Sat.Literal.neg 64), (Sat.Literal.pos 4673)] :=
  (lex_11_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4672), (Sat.Literal.pos 2), (Sat.Literal.pos 64), (Sat.Literal.pos 4673)] :=
  (lex_11_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4673) = lexBefore s permutation11 1 := by
  exact (positive_lex_of_descriptor s 4673 permutation11 2 (by rfl)).trans ((lex_skipped s permutation11 1 2 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation11 1) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation11 1 by rw [image11_eq]; rfl))

theorem lex_11_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4674) (Sat.Literal.pos 4673) (Sat.Literal.pos 1) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation11 1 (assignment s)
    (Sat.Literal.pos 4674) (Sat.Literal.pos 4673) (Sat.Literal.pos 1) (Sat.Literal.pos 32) (positive_of_descriptor s 4674 (.lex permutation11 1) (by rfl)) (lex_11_1_prefix s) (positive_select s 1) (lex_11_1_image s)

theorem lex_11_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4673), (Sat.Literal.pos 1), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation11 1 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4673) (Sat.Literal.pos 1) (Sat.Literal.pos 32) (lex_11_1_prefix s) (positive_select s 1) (lex_11_1_image s)

theorem lex_11_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4674), (Sat.Literal.pos 4673)] :=
  (lex_11_1_gate s).prop _ (List.Mem.head _)

theorem lex_11_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4674), (Sat.Literal.neg 1), (Sat.Literal.pos 32)] :=
  (lex_11_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4674), (Sat.Literal.pos 1), (Sat.Literal.neg 32)] :=
  (lex_11_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4673), (Sat.Literal.neg 1), (Sat.Literal.neg 32), (Sat.Literal.pos 4674)] :=
  (lex_11_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4673), (Sat.Literal.pos 1), (Sat.Literal.pos 32), (Sat.Literal.pos 4674)] :=
  (lex_11_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation12 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation12 254 (by intro j hj; rw [image12_eq]; exact fixedOnRange_spec image12 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_12_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation12 254) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation12 254 by rw [image12_eq]; rfl))

theorem lex_12_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4675) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation12 254 (assignment s)
    (Sat.Literal.pos 4675) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 191) (positive_of_descriptor s 4675 (.lex permutation12 254) (by rfl)) (lex_12_254_prefix s) (positive_select s 254) (lex_12_254_image s)

theorem lex_12_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation12 254 (hmax permutation12) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 191) (lex_12_254_prefix s) (positive_select s 254) (lex_12_254_image s)

theorem lex_12_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4675), (Sat.Literal.neg 256)] :=
  (lex_12_254_gate s).prop _ (List.Mem.head _)

theorem lex_12_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4675), (Sat.Literal.neg 254), (Sat.Literal.pos 191)] :=
  (lex_12_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4675), (Sat.Literal.pos 254), (Sat.Literal.neg 191)] :=
  (lex_12_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 191), (Sat.Literal.pos 4675)] :=
  (lex_12_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 191), (Sat.Literal.pos 4675)] :=
  (lex_12_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4675) = lexBefore s permutation12 253 := by
  exact (positive_lex_of_descriptor s 4675 permutation12 254 (by rfl)).trans ((lex_skipped s permutation12 253 254 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation12 253) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation12 253 by rw [image12_eq]; rfl))

theorem lex_12_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4676) (Sat.Literal.pos 4675) (Sat.Literal.pos 253) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation12 253 (assignment s)
    (Sat.Literal.pos 4676) (Sat.Literal.pos 4675) (Sat.Literal.pos 253) (Sat.Literal.pos 127) (positive_of_descriptor s 4676 (.lex permutation12 253) (by rfl)) (lex_12_253_prefix s) (positive_select s 253) (lex_12_253_image s)

theorem lex_12_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4675), (Sat.Literal.pos 253), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation12 253 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4675) (Sat.Literal.pos 253) (Sat.Literal.pos 127) (lex_12_253_prefix s) (positive_select s 253) (lex_12_253_image s)

theorem lex_12_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4676), (Sat.Literal.pos 4675)] :=
  (lex_12_253_gate s).prop _ (List.Mem.head _)

theorem lex_12_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4676), (Sat.Literal.neg 253), (Sat.Literal.pos 127)] :=
  (lex_12_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4676), (Sat.Literal.pos 253), (Sat.Literal.neg 127)] :=
  (lex_12_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4675), (Sat.Literal.neg 253), (Sat.Literal.neg 127), (Sat.Literal.pos 4676)] :=
  (lex_12_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4675), (Sat.Literal.pos 253), (Sat.Literal.pos 127), (Sat.Literal.pos 4676)] :=
  (lex_12_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4676) = lexBefore s permutation12 252 := by
  exact (positive_lex_of_descriptor s 4676 permutation12 253 (by rfl)).trans ((lex_skipped s permutation12 252 253 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation12 252) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation12 252 by rw [image12_eq]; rfl))

theorem lex_12_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4677) (Sat.Literal.pos 4676) (Sat.Literal.pos 252) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation12 252 (assignment s)
    (Sat.Literal.pos 4677) (Sat.Literal.pos 4676) (Sat.Literal.pos 252) (Sat.Literal.pos 63) (positive_of_descriptor s 4677 (.lex permutation12 252) (by rfl)) (lex_12_252_prefix s) (positive_select s 252) (lex_12_252_image s)

theorem lex_12_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4676), (Sat.Literal.pos 252), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation12 252 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4676) (Sat.Literal.pos 252) (Sat.Literal.pos 63) (lex_12_252_prefix s) (positive_select s 252) (lex_12_252_image s)

theorem lex_12_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4677), (Sat.Literal.pos 4676)] :=
  (lex_12_252_gate s).prop _ (List.Mem.head _)

theorem lex_12_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4677), (Sat.Literal.neg 252), (Sat.Literal.pos 63)] :=
  (lex_12_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4677), (Sat.Literal.pos 252), (Sat.Literal.neg 63)] :=
  (lex_12_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4676), (Sat.Literal.neg 252), (Sat.Literal.neg 63), (Sat.Literal.pos 4677)] :=
  (lex_12_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4676), (Sat.Literal.pos 252), (Sat.Literal.pos 63), (Sat.Literal.pos 4677)] :=
  (lex_12_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4677) = lexBefore s permutation12 251 := by
  exact (positive_lex_of_descriptor s 4677 permutation12 252 (by rfl)).trans ((lex_skipped s permutation12 251 252 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation12 251) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation12 251 by rw [image12_eq]; rfl))

theorem lex_12_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4678) (Sat.Literal.pos 4677) (Sat.Literal.pos 251) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation12 251 (assignment s)
    (Sat.Literal.pos 4678) (Sat.Literal.pos 4677) (Sat.Literal.pos 251) (Sat.Literal.pos 254) (positive_of_descriptor s 4678 (.lex permutation12 251) (by rfl)) (lex_12_251_prefix s) (positive_select s 251) (lex_12_251_image s)

theorem lex_12_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4677), (Sat.Literal.pos 251), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation12 251 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4677) (Sat.Literal.pos 251) (Sat.Literal.pos 254) (lex_12_251_prefix s) (positive_select s 251) (lex_12_251_image s)

theorem lex_12_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4678), (Sat.Literal.pos 4677)] :=
  (lex_12_251_gate s).prop _ (List.Mem.head _)

theorem lex_12_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4678), (Sat.Literal.neg 251), (Sat.Literal.pos 254)] :=
  (lex_12_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4678), (Sat.Literal.pos 251), (Sat.Literal.neg 254)] :=
  (lex_12_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4677), (Sat.Literal.neg 251), (Sat.Literal.neg 254), (Sat.Literal.pos 4678)] :=
  (lex_12_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4677), (Sat.Literal.pos 251), (Sat.Literal.pos 254), (Sat.Literal.pos 4678)] :=
  (lex_12_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4678) = lexBefore s permutation12 250 := by
  exact (positive_lex_of_descriptor s 4678 permutation12 251 (by rfl)).trans ((lex_skipped s permutation12 250 251 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation12 250) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation12 250 by rw [image12_eq]; rfl))

theorem lex_12_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4679) (Sat.Literal.pos 4678) (Sat.Literal.pos 250) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation12 250 (assignment s)
    (Sat.Literal.pos 4679) (Sat.Literal.pos 4678) (Sat.Literal.pos 250) (Sat.Literal.pos 190) (positive_of_descriptor s 4679 (.lex permutation12 250) (by rfl)) (lex_12_250_prefix s) (positive_select s 250) (lex_12_250_image s)

theorem lex_12_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4678), (Sat.Literal.pos 250), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation12 250 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4678) (Sat.Literal.pos 250) (Sat.Literal.pos 190) (lex_12_250_prefix s) (positive_select s 250) (lex_12_250_image s)

theorem lex_12_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4679), (Sat.Literal.pos 4678)] :=
  (lex_12_250_gate s).prop _ (List.Mem.head _)

theorem lex_12_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4679), (Sat.Literal.neg 250), (Sat.Literal.pos 190)] :=
  (lex_12_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4679), (Sat.Literal.pos 250), (Sat.Literal.neg 190)] :=
  (lex_12_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4678), (Sat.Literal.neg 250), (Sat.Literal.neg 190), (Sat.Literal.pos 4679)] :=
  (lex_12_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4678), (Sat.Literal.pos 250), (Sat.Literal.pos 190), (Sat.Literal.pos 4679)] :=
  (lex_12_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4679) = lexBefore s permutation12 249 := by
  exact (positive_lex_of_descriptor s 4679 permutation12 250 (by rfl)).trans ((lex_skipped s permutation12 249 250 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation12 249) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation12 249 by rw [image12_eq]; rfl))

theorem lex_12_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4680) (Sat.Literal.pos 4679) (Sat.Literal.pos 249) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation12 249 (assignment s)
    (Sat.Literal.pos 4680) (Sat.Literal.pos 4679) (Sat.Literal.pos 249) (Sat.Literal.pos 126) (positive_of_descriptor s 4680 (.lex permutation12 249) (by rfl)) (lex_12_249_prefix s) (positive_select s 249) (lex_12_249_image s)

theorem lex_12_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4679), (Sat.Literal.pos 249), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation12 249 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4679) (Sat.Literal.pos 249) (Sat.Literal.pos 126) (lex_12_249_prefix s) (positive_select s 249) (lex_12_249_image s)

theorem lex_12_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4680), (Sat.Literal.pos 4679)] :=
  (lex_12_249_gate s).prop _ (List.Mem.head _)

theorem lex_12_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4680), (Sat.Literal.neg 249), (Sat.Literal.pos 126)] :=
  (lex_12_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4680), (Sat.Literal.pos 249), (Sat.Literal.neg 126)] :=
  (lex_12_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4679), (Sat.Literal.neg 249), (Sat.Literal.neg 126), (Sat.Literal.pos 4680)] :=
  (lex_12_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4679), (Sat.Literal.pos 249), (Sat.Literal.pos 126), (Sat.Literal.pos 4680)] :=
  (lex_12_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4680) = lexBefore s permutation12 248 := by
  exact (positive_lex_of_descriptor s 4680 permutation12 249 (by rfl)).trans ((lex_skipped s permutation12 248 249 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation12 248) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation12 248 by rw [image12_eq]; rfl))

theorem lex_12_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4681) (Sat.Literal.pos 4680) (Sat.Literal.pos 248) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation12 248 (assignment s)
    (Sat.Literal.pos 4681) (Sat.Literal.pos 4680) (Sat.Literal.pos 248) (Sat.Literal.pos 62) (positive_of_descriptor s 4681 (.lex permutation12 248) (by rfl)) (lex_12_248_prefix s) (positive_select s 248) (lex_12_248_image s)

theorem lex_12_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4680), (Sat.Literal.pos 248), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation12 248 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4680) (Sat.Literal.pos 248) (Sat.Literal.pos 62) (lex_12_248_prefix s) (positive_select s 248) (lex_12_248_image s)

theorem lex_12_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4681), (Sat.Literal.pos 4680)] :=
  (lex_12_248_gate s).prop _ (List.Mem.head _)

theorem lex_12_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4681), (Sat.Literal.neg 248), (Sat.Literal.pos 62)] :=
  (lex_12_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4681), (Sat.Literal.pos 248), (Sat.Literal.neg 62)] :=
  (lex_12_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4680), (Sat.Literal.neg 248), (Sat.Literal.neg 62), (Sat.Literal.pos 4681)] :=
  (lex_12_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4680), (Sat.Literal.pos 248), (Sat.Literal.pos 62), (Sat.Literal.pos 4681)] :=
  (lex_12_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4681) = lexBefore s permutation12 247 := by
  exact (positive_lex_of_descriptor s 4681 permutation12 248 (by rfl)).trans ((lex_skipped s permutation12 247 248 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation12 247) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation12 247 by rw [image12_eq]; rfl))

theorem lex_12_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4682) (Sat.Literal.pos 4681) (Sat.Literal.pos 247) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation12 247 (assignment s)
    (Sat.Literal.pos 4682) (Sat.Literal.pos 4681) (Sat.Literal.pos 247) (Sat.Literal.pos 253) (positive_of_descriptor s 4682 (.lex permutation12 247) (by rfl)) (lex_12_247_prefix s) (positive_select s 247) (lex_12_247_image s)

theorem lex_12_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4681), (Sat.Literal.pos 247), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation12 247 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4681) (Sat.Literal.pos 247) (Sat.Literal.pos 253) (lex_12_247_prefix s) (positive_select s 247) (lex_12_247_image s)

theorem lex_12_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4682), (Sat.Literal.pos 4681)] :=
  (lex_12_247_gate s).prop _ (List.Mem.head _)

theorem lex_12_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4682), (Sat.Literal.neg 247), (Sat.Literal.pos 253)] :=
  (lex_12_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4682), (Sat.Literal.pos 247), (Sat.Literal.neg 253)] :=
  (lex_12_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4681), (Sat.Literal.neg 247), (Sat.Literal.neg 253), (Sat.Literal.pos 4682)] :=
  (lex_12_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4681), (Sat.Literal.pos 247), (Sat.Literal.pos 253), (Sat.Literal.pos 4682)] :=
  (lex_12_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4682) = lexBefore s permutation12 246 := by
  exact (positive_lex_of_descriptor s 4682 permutation12 247 (by rfl)).trans ((lex_skipped s permutation12 246 247 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation12 246) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation12 246 by rw [image12_eq]; rfl))

theorem lex_12_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4683) (Sat.Literal.pos 4682) (Sat.Literal.pos 246) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation12 246 (assignment s)
    (Sat.Literal.pos 4683) (Sat.Literal.pos 4682) (Sat.Literal.pos 246) (Sat.Literal.pos 189) (positive_of_descriptor s 4683 (.lex permutation12 246) (by rfl)) (lex_12_246_prefix s) (positive_select s 246) (lex_12_246_image s)

theorem lex_12_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4682), (Sat.Literal.pos 246), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation12 246 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4682) (Sat.Literal.pos 246) (Sat.Literal.pos 189) (lex_12_246_prefix s) (positive_select s 246) (lex_12_246_image s)

theorem lex_12_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4683), (Sat.Literal.pos 4682)] :=
  (lex_12_246_gate s).prop _ (List.Mem.head _)

theorem lex_12_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4683), (Sat.Literal.neg 246), (Sat.Literal.pos 189)] :=
  (lex_12_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4683), (Sat.Literal.pos 246), (Sat.Literal.neg 189)] :=
  (lex_12_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4682), (Sat.Literal.neg 246), (Sat.Literal.neg 189), (Sat.Literal.pos 4683)] :=
  (lex_12_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4682), (Sat.Literal.pos 246), (Sat.Literal.pos 189), (Sat.Literal.pos 4683)] :=
  (lex_12_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4683) = lexBefore s permutation12 245 := by
  exact (positive_lex_of_descriptor s 4683 permutation12 246 (by rfl)).trans ((lex_skipped s permutation12 245 246 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation12 245) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation12 245 by rw [image12_eq]; rfl))

theorem lex_12_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4684) (Sat.Literal.pos 4683) (Sat.Literal.pos 245) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation12 245 (assignment s)
    (Sat.Literal.pos 4684) (Sat.Literal.pos 4683) (Sat.Literal.pos 245) (Sat.Literal.pos 125) (positive_of_descriptor s 4684 (.lex permutation12 245) (by rfl)) (lex_12_245_prefix s) (positive_select s 245) (lex_12_245_image s)

theorem lex_12_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4683), (Sat.Literal.pos 245), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation12 245 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4683) (Sat.Literal.pos 245) (Sat.Literal.pos 125) (lex_12_245_prefix s) (positive_select s 245) (lex_12_245_image s)

theorem lex_12_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4684), (Sat.Literal.pos 4683)] :=
  (lex_12_245_gate s).prop _ (List.Mem.head _)

theorem lex_12_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4684), (Sat.Literal.neg 245), (Sat.Literal.pos 125)] :=
  (lex_12_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4684), (Sat.Literal.pos 245), (Sat.Literal.neg 125)] :=
  (lex_12_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4683), (Sat.Literal.neg 245), (Sat.Literal.neg 125), (Sat.Literal.pos 4684)] :=
  (lex_12_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4683), (Sat.Literal.pos 245), (Sat.Literal.pos 125), (Sat.Literal.pos 4684)] :=
  (lex_12_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4684) = lexBefore s permutation12 244 := by
  exact (positive_lex_of_descriptor s 4684 permutation12 245 (by rfl)).trans ((lex_skipped s permutation12 244 245 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation12 244) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation12 244 by rw [image12_eq]; rfl))

theorem lex_12_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4685) (Sat.Literal.pos 4684) (Sat.Literal.pos 244) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation12 244 (assignment s)
    (Sat.Literal.pos 4685) (Sat.Literal.pos 4684) (Sat.Literal.pos 244) (Sat.Literal.pos 61) (positive_of_descriptor s 4685 (.lex permutation12 244) (by rfl)) (lex_12_244_prefix s) (positive_select s 244) (lex_12_244_image s)

theorem lex_12_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4684), (Sat.Literal.pos 244), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation12 244 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4684) (Sat.Literal.pos 244) (Sat.Literal.pos 61) (lex_12_244_prefix s) (positive_select s 244) (lex_12_244_image s)

theorem lex_12_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4685), (Sat.Literal.pos 4684)] :=
  (lex_12_244_gate s).prop _ (List.Mem.head _)

theorem lex_12_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4685), (Sat.Literal.neg 244), (Sat.Literal.pos 61)] :=
  (lex_12_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4685), (Sat.Literal.pos 244), (Sat.Literal.neg 61)] :=
  (lex_12_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4684), (Sat.Literal.neg 244), (Sat.Literal.neg 61), (Sat.Literal.pos 4685)] :=
  (lex_12_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4684), (Sat.Literal.pos 244), (Sat.Literal.pos 61), (Sat.Literal.pos 4685)] :=
  (lex_12_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4685) = lexBefore s permutation12 243 := by
  exact (positive_lex_of_descriptor s 4685 permutation12 244 (by rfl)).trans ((lex_skipped s permutation12 243 244 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation12 243) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation12 243 by rw [image12_eq]; rfl))

theorem lex_12_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4686) (Sat.Literal.pos 4685) (Sat.Literal.pos 243) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation12 243 (assignment s)
    (Sat.Literal.pos 4686) (Sat.Literal.pos 4685) (Sat.Literal.pos 243) (Sat.Literal.pos 252) (positive_of_descriptor s 4686 (.lex permutation12 243) (by rfl)) (lex_12_243_prefix s) (positive_select s 243) (lex_12_243_image s)

theorem lex_12_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4685), (Sat.Literal.pos 243), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation12 243 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4685) (Sat.Literal.pos 243) (Sat.Literal.pos 252) (lex_12_243_prefix s) (positive_select s 243) (lex_12_243_image s)

theorem lex_12_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4686), (Sat.Literal.pos 4685)] :=
  (lex_12_243_gate s).prop _ (List.Mem.head _)

theorem lex_12_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4686), (Sat.Literal.neg 243), (Sat.Literal.pos 252)] :=
  (lex_12_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4686), (Sat.Literal.pos 243), (Sat.Literal.neg 252)] :=
  (lex_12_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4685), (Sat.Literal.neg 243), (Sat.Literal.neg 252), (Sat.Literal.pos 4686)] :=
  (lex_12_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4685), (Sat.Literal.pos 243), (Sat.Literal.pos 252), (Sat.Literal.pos 4686)] :=
  (lex_12_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4686) = lexBefore s permutation12 242 := by
  exact (positive_lex_of_descriptor s 4686 permutation12 243 (by rfl)).trans ((lex_skipped s permutation12 242 243 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation12 242) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation12 242 by rw [image12_eq]; rfl))

theorem lex_12_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4687) (Sat.Literal.pos 4686) (Sat.Literal.pos 242) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation12 242 (assignment s)
    (Sat.Literal.pos 4687) (Sat.Literal.pos 4686) (Sat.Literal.pos 242) (Sat.Literal.pos 188) (positive_of_descriptor s 4687 (.lex permutation12 242) (by rfl)) (lex_12_242_prefix s) (positive_select s 242) (lex_12_242_image s)

theorem lex_12_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4686), (Sat.Literal.pos 242), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation12 242 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4686) (Sat.Literal.pos 242) (Sat.Literal.pos 188) (lex_12_242_prefix s) (positive_select s 242) (lex_12_242_image s)

theorem lex_12_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4687), (Sat.Literal.pos 4686)] :=
  (lex_12_242_gate s).prop _ (List.Mem.head _)

theorem lex_12_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4687), (Sat.Literal.neg 242), (Sat.Literal.pos 188)] :=
  (lex_12_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4687), (Sat.Literal.pos 242), (Sat.Literal.neg 188)] :=
  (lex_12_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4686), (Sat.Literal.neg 242), (Sat.Literal.neg 188), (Sat.Literal.pos 4687)] :=
  (lex_12_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4686), (Sat.Literal.pos 242), (Sat.Literal.pos 188), (Sat.Literal.pos 4687)] :=
  (lex_12_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4687) = lexBefore s permutation12 241 := by
  exact (positive_lex_of_descriptor s 4687 permutation12 242 (by rfl)).trans ((lex_skipped s permutation12 241 242 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation12 241) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation12 241 by rw [image12_eq]; rfl))

theorem lex_12_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4688) (Sat.Literal.pos 4687) (Sat.Literal.pos 241) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation12 241 (assignment s)
    (Sat.Literal.pos 4688) (Sat.Literal.pos 4687) (Sat.Literal.pos 241) (Sat.Literal.pos 124) (positive_of_descriptor s 4688 (.lex permutation12 241) (by rfl)) (lex_12_241_prefix s) (positive_select s 241) (lex_12_241_image s)

theorem lex_12_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4687), (Sat.Literal.pos 241), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation12 241 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4687) (Sat.Literal.pos 241) (Sat.Literal.pos 124) (lex_12_241_prefix s) (positive_select s 241) (lex_12_241_image s)

theorem lex_12_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4688), (Sat.Literal.pos 4687)] :=
  (lex_12_241_gate s).prop _ (List.Mem.head _)

theorem lex_12_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4688), (Sat.Literal.neg 241), (Sat.Literal.pos 124)] :=
  (lex_12_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4688), (Sat.Literal.pos 241), (Sat.Literal.neg 124)] :=
  (lex_12_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4687), (Sat.Literal.neg 241), (Sat.Literal.neg 124), (Sat.Literal.pos 4688)] :=
  (lex_12_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4687), (Sat.Literal.pos 241), (Sat.Literal.pos 124), (Sat.Literal.pos 4688)] :=
  (lex_12_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4688) = lexBefore s permutation12 240 := by
  exact (positive_lex_of_descriptor s 4688 permutation12 241 (by rfl)).trans ((lex_skipped s permutation12 240 241 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation12 240) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation12 240 by rw [image12_eq]; rfl))

theorem lex_12_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4689) (Sat.Literal.pos 4688) (Sat.Literal.pos 240) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation12 240 (assignment s)
    (Sat.Literal.pos 4689) (Sat.Literal.pos 4688) (Sat.Literal.pos 240) (Sat.Literal.pos 60) (positive_of_descriptor s 4689 (.lex permutation12 240) (by rfl)) (lex_12_240_prefix s) (positive_select s 240) (lex_12_240_image s)

theorem lex_12_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4688), (Sat.Literal.pos 240), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation12 240 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4688) (Sat.Literal.pos 240) (Sat.Literal.pos 60) (lex_12_240_prefix s) (positive_select s 240) (lex_12_240_image s)

theorem lex_12_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4689), (Sat.Literal.pos 4688)] :=
  (lex_12_240_gate s).prop _ (List.Mem.head _)

theorem lex_12_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4689), (Sat.Literal.neg 240), (Sat.Literal.pos 60)] :=
  (lex_12_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4689), (Sat.Literal.pos 240), (Sat.Literal.neg 60)] :=
  (lex_12_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4688), (Sat.Literal.neg 240), (Sat.Literal.neg 60), (Sat.Literal.pos 4689)] :=
  (lex_12_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4688), (Sat.Literal.pos 240), (Sat.Literal.pos 60), (Sat.Literal.pos 4689)] :=
  (lex_12_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4689) = lexBefore s permutation12 239 := by
  exact (positive_lex_of_descriptor s 4689 permutation12 240 (by rfl)).trans ((lex_skipped s permutation12 239 240 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation12 239) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation12 239 by rw [image12_eq]; rfl))

theorem lex_12_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4690) (Sat.Literal.pos 4689) (Sat.Literal.pos 239) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation12 239 (assignment s)
    (Sat.Literal.pos 4690) (Sat.Literal.pos 4689) (Sat.Literal.pos 239) (Sat.Literal.pos 251) (positive_of_descriptor s 4690 (.lex permutation12 239) (by rfl)) (lex_12_239_prefix s) (positive_select s 239) (lex_12_239_image s)

theorem lex_12_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4689), (Sat.Literal.pos 239), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation12 239 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4689) (Sat.Literal.pos 239) (Sat.Literal.pos 251) (lex_12_239_prefix s) (positive_select s 239) (lex_12_239_image s)

theorem lex_12_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4690), (Sat.Literal.pos 4689)] :=
  (lex_12_239_gate s).prop _ (List.Mem.head _)

theorem lex_12_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4690), (Sat.Literal.neg 239), (Sat.Literal.pos 251)] :=
  (lex_12_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4690), (Sat.Literal.pos 239), (Sat.Literal.neg 251)] :=
  (lex_12_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4689), (Sat.Literal.neg 239), (Sat.Literal.neg 251), (Sat.Literal.pos 4690)] :=
  (lex_12_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4689), (Sat.Literal.pos 239), (Sat.Literal.pos 251), (Sat.Literal.pos 4690)] :=
  (lex_12_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4690) = lexBefore s permutation12 238 := by
  exact (positive_lex_of_descriptor s 4690 permutation12 239 (by rfl)).trans ((lex_skipped s permutation12 238 239 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation12 238) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation12 238 by rw [image12_eq]; rfl))

theorem lex_12_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4691) (Sat.Literal.pos 4690) (Sat.Literal.pos 238) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation12 238 (assignment s)
    (Sat.Literal.pos 4691) (Sat.Literal.pos 4690) (Sat.Literal.pos 238) (Sat.Literal.pos 187) (positive_of_descriptor s 4691 (.lex permutation12 238) (by rfl)) (lex_12_238_prefix s) (positive_select s 238) (lex_12_238_image s)

theorem lex_12_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4690), (Sat.Literal.pos 238), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation12 238 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4690) (Sat.Literal.pos 238) (Sat.Literal.pos 187) (lex_12_238_prefix s) (positive_select s 238) (lex_12_238_image s)

theorem lex_12_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4691), (Sat.Literal.pos 4690)] :=
  (lex_12_238_gate s).prop _ (List.Mem.head _)

theorem lex_12_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4691), (Sat.Literal.neg 238), (Sat.Literal.pos 187)] :=
  (lex_12_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4691), (Sat.Literal.pos 238), (Sat.Literal.neg 187)] :=
  (lex_12_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4690), (Sat.Literal.neg 238), (Sat.Literal.neg 187), (Sat.Literal.pos 4691)] :=
  (lex_12_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4690), (Sat.Literal.pos 238), (Sat.Literal.pos 187), (Sat.Literal.pos 4691)] :=
  (lex_12_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4691) = lexBefore s permutation12 237 := by
  exact (positive_lex_of_descriptor s 4691 permutation12 238 (by rfl)).trans ((lex_skipped s permutation12 237 238 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation12 237) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation12 237 by rw [image12_eq]; rfl))

theorem lex_12_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4692) (Sat.Literal.pos 4691) (Sat.Literal.pos 237) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation12 237 (assignment s)
    (Sat.Literal.pos 4692) (Sat.Literal.pos 4691) (Sat.Literal.pos 237) (Sat.Literal.pos 123) (positive_of_descriptor s 4692 (.lex permutation12 237) (by rfl)) (lex_12_237_prefix s) (positive_select s 237) (lex_12_237_image s)

theorem lex_12_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4691), (Sat.Literal.pos 237), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation12 237 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4691) (Sat.Literal.pos 237) (Sat.Literal.pos 123) (lex_12_237_prefix s) (positive_select s 237) (lex_12_237_image s)

theorem lex_12_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4692), (Sat.Literal.pos 4691)] :=
  (lex_12_237_gate s).prop _ (List.Mem.head _)

theorem lex_12_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4692), (Sat.Literal.neg 237), (Sat.Literal.pos 123)] :=
  (lex_12_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4692), (Sat.Literal.pos 237), (Sat.Literal.neg 123)] :=
  (lex_12_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4691), (Sat.Literal.neg 237), (Sat.Literal.neg 123), (Sat.Literal.pos 4692)] :=
  (lex_12_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4691), (Sat.Literal.pos 237), (Sat.Literal.pos 123), (Sat.Literal.pos 4692)] :=
  (lex_12_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4692) = lexBefore s permutation12 236 := by
  exact (positive_lex_of_descriptor s 4692 permutation12 237 (by rfl)).trans ((lex_skipped s permutation12 236 237 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation12 236) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation12 236 by rw [image12_eq]; rfl))

theorem lex_12_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4693) (Sat.Literal.pos 4692) (Sat.Literal.pos 236) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation12 236 (assignment s)
    (Sat.Literal.pos 4693) (Sat.Literal.pos 4692) (Sat.Literal.pos 236) (Sat.Literal.pos 59) (positive_of_descriptor s 4693 (.lex permutation12 236) (by rfl)) (lex_12_236_prefix s) (positive_select s 236) (lex_12_236_image s)

theorem lex_12_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4692), (Sat.Literal.pos 236), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation12 236 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4692) (Sat.Literal.pos 236) (Sat.Literal.pos 59) (lex_12_236_prefix s) (positive_select s 236) (lex_12_236_image s)

theorem lex_12_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4693), (Sat.Literal.pos 4692)] :=
  (lex_12_236_gate s).prop _ (List.Mem.head _)

theorem lex_12_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4693), (Sat.Literal.neg 236), (Sat.Literal.pos 59)] :=
  (lex_12_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4693), (Sat.Literal.pos 236), (Sat.Literal.neg 59)] :=
  (lex_12_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4692), (Sat.Literal.neg 236), (Sat.Literal.neg 59), (Sat.Literal.pos 4693)] :=
  (lex_12_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4692), (Sat.Literal.pos 236), (Sat.Literal.pos 59), (Sat.Literal.pos 4693)] :=
  (lex_12_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4693) = lexBefore s permutation12 235 := by
  exact (positive_lex_of_descriptor s 4693 permutation12 236 (by rfl)).trans ((lex_skipped s permutation12 235 236 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation12 235) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation12 235 by rw [image12_eq]; rfl))

theorem lex_12_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4694) (Sat.Literal.pos 4693) (Sat.Literal.pos 235) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation12 235 (assignment s)
    (Sat.Literal.pos 4694) (Sat.Literal.pos 4693) (Sat.Literal.pos 235) (Sat.Literal.pos 250) (positive_of_descriptor s 4694 (.lex permutation12 235) (by rfl)) (lex_12_235_prefix s) (positive_select s 235) (lex_12_235_image s)

theorem lex_12_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4693), (Sat.Literal.pos 235), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation12 235 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4693) (Sat.Literal.pos 235) (Sat.Literal.pos 250) (lex_12_235_prefix s) (positive_select s 235) (lex_12_235_image s)

theorem lex_12_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4694), (Sat.Literal.pos 4693)] :=
  (lex_12_235_gate s).prop _ (List.Mem.head _)

theorem lex_12_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4694), (Sat.Literal.neg 235), (Sat.Literal.pos 250)] :=
  (lex_12_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4694), (Sat.Literal.pos 235), (Sat.Literal.neg 250)] :=
  (lex_12_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4693), (Sat.Literal.neg 235), (Sat.Literal.neg 250), (Sat.Literal.pos 4694)] :=
  (lex_12_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4693), (Sat.Literal.pos 235), (Sat.Literal.pos 250), (Sat.Literal.pos 4694)] :=
  (lex_12_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4694) = lexBefore s permutation12 234 := by
  exact (positive_lex_of_descriptor s 4694 permutation12 235 (by rfl)).trans ((lex_skipped s permutation12 234 235 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation12 234) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation12 234 by rw [image12_eq]; rfl))

theorem lex_12_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4695) (Sat.Literal.pos 4694) (Sat.Literal.pos 234) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation12 234 (assignment s)
    (Sat.Literal.pos 4695) (Sat.Literal.pos 4694) (Sat.Literal.pos 234) (Sat.Literal.pos 186) (positive_of_descriptor s 4695 (.lex permutation12 234) (by rfl)) (lex_12_234_prefix s) (positive_select s 234) (lex_12_234_image s)

theorem lex_12_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4694), (Sat.Literal.pos 234), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation12 234 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4694) (Sat.Literal.pos 234) (Sat.Literal.pos 186) (lex_12_234_prefix s) (positive_select s 234) (lex_12_234_image s)

theorem lex_12_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4695), (Sat.Literal.pos 4694)] :=
  (lex_12_234_gate s).prop _ (List.Mem.head _)

theorem lex_12_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4695), (Sat.Literal.neg 234), (Sat.Literal.pos 186)] :=
  (lex_12_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4695), (Sat.Literal.pos 234), (Sat.Literal.neg 186)] :=
  (lex_12_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4694), (Sat.Literal.neg 234), (Sat.Literal.neg 186), (Sat.Literal.pos 4695)] :=
  (lex_12_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4694), (Sat.Literal.pos 234), (Sat.Literal.pos 186), (Sat.Literal.pos 4695)] :=
  (lex_12_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4695) = lexBefore s permutation12 233 := by
  exact (positive_lex_of_descriptor s 4695 permutation12 234 (by rfl)).trans ((lex_skipped s permutation12 233 234 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation12 233) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation12 233 by rw [image12_eq]; rfl))

theorem lex_12_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4696) (Sat.Literal.pos 4695) (Sat.Literal.pos 233) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation12 233 (assignment s)
    (Sat.Literal.pos 4696) (Sat.Literal.pos 4695) (Sat.Literal.pos 233) (Sat.Literal.pos 122) (positive_of_descriptor s 4696 (.lex permutation12 233) (by rfl)) (lex_12_233_prefix s) (positive_select s 233) (lex_12_233_image s)

theorem lex_12_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4695), (Sat.Literal.pos 233), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation12 233 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4695) (Sat.Literal.pos 233) (Sat.Literal.pos 122) (lex_12_233_prefix s) (positive_select s 233) (lex_12_233_image s)

theorem lex_12_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4696), (Sat.Literal.pos 4695)] :=
  (lex_12_233_gate s).prop _ (List.Mem.head _)

theorem lex_12_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4696), (Sat.Literal.neg 233), (Sat.Literal.pos 122)] :=
  (lex_12_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4696), (Sat.Literal.pos 233), (Sat.Literal.neg 122)] :=
  (lex_12_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4695), (Sat.Literal.neg 233), (Sat.Literal.neg 122), (Sat.Literal.pos 4696)] :=
  (lex_12_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4695), (Sat.Literal.pos 233), (Sat.Literal.pos 122), (Sat.Literal.pos 4696)] :=
  (lex_12_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4696) = lexBefore s permutation12 232 := by
  exact (positive_lex_of_descriptor s 4696 permutation12 233 (by rfl)).trans ((lex_skipped s permutation12 232 233 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation12 232) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation12 232 by rw [image12_eq]; rfl))

theorem lex_12_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4697) (Sat.Literal.pos 4696) (Sat.Literal.pos 232) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation12 232 (assignment s)
    (Sat.Literal.pos 4697) (Sat.Literal.pos 4696) (Sat.Literal.pos 232) (Sat.Literal.pos 58) (positive_of_descriptor s 4697 (.lex permutation12 232) (by rfl)) (lex_12_232_prefix s) (positive_select s 232) (lex_12_232_image s)

theorem lex_12_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4696), (Sat.Literal.pos 232), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation12 232 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4696) (Sat.Literal.pos 232) (Sat.Literal.pos 58) (lex_12_232_prefix s) (positive_select s 232) (lex_12_232_image s)

theorem lex_12_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4697), (Sat.Literal.pos 4696)] :=
  (lex_12_232_gate s).prop _ (List.Mem.head _)

theorem lex_12_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4697), (Sat.Literal.neg 232), (Sat.Literal.pos 58)] :=
  (lex_12_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4697), (Sat.Literal.pos 232), (Sat.Literal.neg 58)] :=
  (lex_12_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4696), (Sat.Literal.neg 232), (Sat.Literal.neg 58), (Sat.Literal.pos 4697)] :=
  (lex_12_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4696), (Sat.Literal.pos 232), (Sat.Literal.pos 58), (Sat.Literal.pos 4697)] :=
  (lex_12_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4697) = lexBefore s permutation12 231 := by
  exact (positive_lex_of_descriptor s 4697 permutation12 232 (by rfl)).trans ((lex_skipped s permutation12 231 232 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation12 231) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation12 231 by rw [image12_eq]; rfl))

theorem lex_12_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4698) (Sat.Literal.pos 4697) (Sat.Literal.pos 231) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation12 231 (assignment s)
    (Sat.Literal.pos 4698) (Sat.Literal.pos 4697) (Sat.Literal.pos 231) (Sat.Literal.pos 249) (positive_of_descriptor s 4698 (.lex permutation12 231) (by rfl)) (lex_12_231_prefix s) (positive_select s 231) (lex_12_231_image s)

theorem lex_12_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4697), (Sat.Literal.pos 231), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation12 231 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4697) (Sat.Literal.pos 231) (Sat.Literal.pos 249) (lex_12_231_prefix s) (positive_select s 231) (lex_12_231_image s)

theorem lex_12_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4698), (Sat.Literal.pos 4697)] :=
  (lex_12_231_gate s).prop _ (List.Mem.head _)

theorem lex_12_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4698), (Sat.Literal.neg 231), (Sat.Literal.pos 249)] :=
  (lex_12_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4698), (Sat.Literal.pos 231), (Sat.Literal.neg 249)] :=
  (lex_12_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4697), (Sat.Literal.neg 231), (Sat.Literal.neg 249), (Sat.Literal.pos 4698)] :=
  (lex_12_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4697), (Sat.Literal.pos 231), (Sat.Literal.pos 249), (Sat.Literal.pos 4698)] :=
  (lex_12_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4698) = lexBefore s permutation12 230 := by
  exact (positive_lex_of_descriptor s 4698 permutation12 231 (by rfl)).trans ((lex_skipped s permutation12 230 231 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation12 230) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation12 230 by rw [image12_eq]; rfl))

theorem lex_12_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4699) (Sat.Literal.pos 4698) (Sat.Literal.pos 230) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation12 230 (assignment s)
    (Sat.Literal.pos 4699) (Sat.Literal.pos 4698) (Sat.Literal.pos 230) (Sat.Literal.pos 185) (positive_of_descriptor s 4699 (.lex permutation12 230) (by rfl)) (lex_12_230_prefix s) (positive_select s 230) (lex_12_230_image s)

theorem lex_12_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4698), (Sat.Literal.pos 230), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation12 230 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4698) (Sat.Literal.pos 230) (Sat.Literal.pos 185) (lex_12_230_prefix s) (positive_select s 230) (lex_12_230_image s)

theorem lex_12_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4699), (Sat.Literal.pos 4698)] :=
  (lex_12_230_gate s).prop _ (List.Mem.head _)

theorem lex_12_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4699), (Sat.Literal.neg 230), (Sat.Literal.pos 185)] :=
  (lex_12_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4699), (Sat.Literal.pos 230), (Sat.Literal.neg 185)] :=
  (lex_12_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4698), (Sat.Literal.neg 230), (Sat.Literal.neg 185), (Sat.Literal.pos 4699)] :=
  (lex_12_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4698), (Sat.Literal.pos 230), (Sat.Literal.pos 185), (Sat.Literal.pos 4699)] :=
  (lex_12_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4699) = lexBefore s permutation12 229 := by
  exact (positive_lex_of_descriptor s 4699 permutation12 230 (by rfl)).trans ((lex_skipped s permutation12 229 230 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation12 229) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation12 229 by rw [image12_eq]; rfl))

theorem lex_12_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4700) (Sat.Literal.pos 4699) (Sat.Literal.pos 229) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation12 229 (assignment s)
    (Sat.Literal.pos 4700) (Sat.Literal.pos 4699) (Sat.Literal.pos 229) (Sat.Literal.pos 121) (positive_of_descriptor s 4700 (.lex permutation12 229) (by rfl)) (lex_12_229_prefix s) (positive_select s 229) (lex_12_229_image s)

theorem lex_12_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4699), (Sat.Literal.pos 229), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation12 229 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4699) (Sat.Literal.pos 229) (Sat.Literal.pos 121) (lex_12_229_prefix s) (positive_select s 229) (lex_12_229_image s)

theorem lex_12_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4700), (Sat.Literal.pos 4699)] :=
  (lex_12_229_gate s).prop _ (List.Mem.head _)

theorem lex_12_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4700), (Sat.Literal.neg 229), (Sat.Literal.pos 121)] :=
  (lex_12_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4700), (Sat.Literal.pos 229), (Sat.Literal.neg 121)] :=
  (lex_12_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4699), (Sat.Literal.neg 229), (Sat.Literal.neg 121), (Sat.Literal.pos 4700)] :=
  (lex_12_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4699), (Sat.Literal.pos 229), (Sat.Literal.pos 121), (Sat.Literal.pos 4700)] :=
  (lex_12_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4700) = lexBefore s permutation12 228 := by
  exact (positive_lex_of_descriptor s 4700 permutation12 229 (by rfl)).trans ((lex_skipped s permutation12 228 229 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation12 228) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation12 228 by rw [image12_eq]; rfl))

theorem lex_12_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4701) (Sat.Literal.pos 4700) (Sat.Literal.pos 228) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation12 228 (assignment s)
    (Sat.Literal.pos 4701) (Sat.Literal.pos 4700) (Sat.Literal.pos 228) (Sat.Literal.pos 57) (positive_of_descriptor s 4701 (.lex permutation12 228) (by rfl)) (lex_12_228_prefix s) (positive_select s 228) (lex_12_228_image s)

theorem lex_12_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4700), (Sat.Literal.pos 228), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation12 228 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4700) (Sat.Literal.pos 228) (Sat.Literal.pos 57) (lex_12_228_prefix s) (positive_select s 228) (lex_12_228_image s)

theorem lex_12_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4701), (Sat.Literal.pos 4700)] :=
  (lex_12_228_gate s).prop _ (List.Mem.head _)

theorem lex_12_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4701), (Sat.Literal.neg 228), (Sat.Literal.pos 57)] :=
  (lex_12_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4701), (Sat.Literal.pos 228), (Sat.Literal.neg 57)] :=
  (lex_12_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4700), (Sat.Literal.neg 228), (Sat.Literal.neg 57), (Sat.Literal.pos 4701)] :=
  (lex_12_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4700), (Sat.Literal.pos 228), (Sat.Literal.pos 57), (Sat.Literal.pos 4701)] :=
  (lex_12_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4701) = lexBefore s permutation12 227 := by
  exact (positive_lex_of_descriptor s 4701 permutation12 228 (by rfl)).trans ((lex_skipped s permutation12 227 228 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation12 227) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation12 227 by rw [image12_eq]; rfl))

theorem lex_12_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4702) (Sat.Literal.pos 4701) (Sat.Literal.pos 227) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation12 227 (assignment s)
    (Sat.Literal.pos 4702) (Sat.Literal.pos 4701) (Sat.Literal.pos 227) (Sat.Literal.pos 248) (positive_of_descriptor s 4702 (.lex permutation12 227) (by rfl)) (lex_12_227_prefix s) (positive_select s 227) (lex_12_227_image s)

theorem lex_12_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4701), (Sat.Literal.pos 227), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation12 227 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4701) (Sat.Literal.pos 227) (Sat.Literal.pos 248) (lex_12_227_prefix s) (positive_select s 227) (lex_12_227_image s)

theorem lex_12_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4702), (Sat.Literal.pos 4701)] :=
  (lex_12_227_gate s).prop _ (List.Mem.head _)

theorem lex_12_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4702), (Sat.Literal.neg 227), (Sat.Literal.pos 248)] :=
  (lex_12_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4702), (Sat.Literal.pos 227), (Sat.Literal.neg 248)] :=
  (lex_12_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4701), (Sat.Literal.neg 227), (Sat.Literal.neg 248), (Sat.Literal.pos 4702)] :=
  (lex_12_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4701), (Sat.Literal.pos 227), (Sat.Literal.pos 248), (Sat.Literal.pos 4702)] :=
  (lex_12_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4702) = lexBefore s permutation12 226 := by
  exact (positive_lex_of_descriptor s 4702 permutation12 227 (by rfl)).trans ((lex_skipped s permutation12 226 227 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation12 226) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation12 226 by rw [image12_eq]; rfl))

theorem lex_12_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4703) (Sat.Literal.pos 4702) (Sat.Literal.pos 226) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation12 226 (assignment s)
    (Sat.Literal.pos 4703) (Sat.Literal.pos 4702) (Sat.Literal.pos 226) (Sat.Literal.pos 184) (positive_of_descriptor s 4703 (.lex permutation12 226) (by rfl)) (lex_12_226_prefix s) (positive_select s 226) (lex_12_226_image s)

theorem lex_12_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4702), (Sat.Literal.pos 226), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation12 226 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4702) (Sat.Literal.pos 226) (Sat.Literal.pos 184) (lex_12_226_prefix s) (positive_select s 226) (lex_12_226_image s)

theorem lex_12_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4703), (Sat.Literal.pos 4702)] :=
  (lex_12_226_gate s).prop _ (List.Mem.head _)

theorem lex_12_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4703), (Sat.Literal.neg 226), (Sat.Literal.pos 184)] :=
  (lex_12_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4703), (Sat.Literal.pos 226), (Sat.Literal.neg 184)] :=
  (lex_12_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4702), (Sat.Literal.neg 226), (Sat.Literal.neg 184), (Sat.Literal.pos 4703)] :=
  (lex_12_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4702), (Sat.Literal.pos 226), (Sat.Literal.pos 184), (Sat.Literal.pos 4703)] :=
  (lex_12_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4703) = lexBefore s permutation12 225 := by
  exact (positive_lex_of_descriptor s 4703 permutation12 226 (by rfl)).trans ((lex_skipped s permutation12 225 226 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation12 225) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation12 225 by rw [image12_eq]; rfl))

theorem lex_12_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4704) (Sat.Literal.pos 4703) (Sat.Literal.pos 225) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation12 225 (assignment s)
    (Sat.Literal.pos 4704) (Sat.Literal.pos 4703) (Sat.Literal.pos 225) (Sat.Literal.pos 120) (positive_of_descriptor s 4704 (.lex permutation12 225) (by rfl)) (lex_12_225_prefix s) (positive_select s 225) (lex_12_225_image s)

theorem lex_12_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4703), (Sat.Literal.pos 225), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation12 225 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4703) (Sat.Literal.pos 225) (Sat.Literal.pos 120) (lex_12_225_prefix s) (positive_select s 225) (lex_12_225_image s)

theorem lex_12_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4704), (Sat.Literal.pos 4703)] :=
  (lex_12_225_gate s).prop _ (List.Mem.head _)

theorem lex_12_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4704), (Sat.Literal.neg 225), (Sat.Literal.pos 120)] :=
  (lex_12_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4704), (Sat.Literal.pos 225), (Sat.Literal.neg 120)] :=
  (lex_12_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4703), (Sat.Literal.neg 225), (Sat.Literal.neg 120), (Sat.Literal.pos 4704)] :=
  (lex_12_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4703), (Sat.Literal.pos 225), (Sat.Literal.pos 120), (Sat.Literal.pos 4704)] :=
  (lex_12_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4704) = lexBefore s permutation12 224 := by
  exact (positive_lex_of_descriptor s 4704 permutation12 225 (by rfl)).trans ((lex_skipped s permutation12 224 225 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation12 224) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation12 224 by rw [image12_eq]; rfl))

theorem lex_12_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4705) (Sat.Literal.pos 4704) (Sat.Literal.pos 224) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation12 224 (assignment s)
    (Sat.Literal.pos 4705) (Sat.Literal.pos 4704) (Sat.Literal.pos 224) (Sat.Literal.pos 56) (positive_of_descriptor s 4705 (.lex permutation12 224) (by rfl)) (lex_12_224_prefix s) (positive_select s 224) (lex_12_224_image s)

theorem lex_12_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4704), (Sat.Literal.pos 224), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation12 224 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4704) (Sat.Literal.pos 224) (Sat.Literal.pos 56) (lex_12_224_prefix s) (positive_select s 224) (lex_12_224_image s)

theorem lex_12_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4705), (Sat.Literal.pos 4704)] :=
  (lex_12_224_gate s).prop _ (List.Mem.head _)

theorem lex_12_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4705), (Sat.Literal.neg 224), (Sat.Literal.pos 56)] :=
  (lex_12_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4705), (Sat.Literal.pos 224), (Sat.Literal.neg 56)] :=
  (lex_12_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4704), (Sat.Literal.neg 224), (Sat.Literal.neg 56), (Sat.Literal.pos 4705)] :=
  (lex_12_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4704), (Sat.Literal.pos 224), (Sat.Literal.pos 56), (Sat.Literal.pos 4705)] :=
  (lex_12_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4705) = lexBefore s permutation12 223 := by
  exact (positive_lex_of_descriptor s 4705 permutation12 224 (by rfl)).trans ((lex_skipped s permutation12 223 224 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation12 223) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation12 223 by rw [image12_eq]; rfl))

theorem lex_12_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4706) (Sat.Literal.pos 4705) (Sat.Literal.pos 223) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation12 223 (assignment s)
    (Sat.Literal.pos 4706) (Sat.Literal.pos 4705) (Sat.Literal.pos 223) (Sat.Literal.pos 247) (positive_of_descriptor s 4706 (.lex permutation12 223) (by rfl)) (lex_12_223_prefix s) (positive_select s 223) (lex_12_223_image s)

theorem lex_12_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4705), (Sat.Literal.pos 223), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation12 223 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4705) (Sat.Literal.pos 223) (Sat.Literal.pos 247) (lex_12_223_prefix s) (positive_select s 223) (lex_12_223_image s)

theorem lex_12_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4706), (Sat.Literal.pos 4705)] :=
  (lex_12_223_gate s).prop _ (List.Mem.head _)

theorem lex_12_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4706), (Sat.Literal.neg 223), (Sat.Literal.pos 247)] :=
  (lex_12_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4706), (Sat.Literal.pos 223), (Sat.Literal.neg 247)] :=
  (lex_12_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4705), (Sat.Literal.neg 223), (Sat.Literal.neg 247), (Sat.Literal.pos 4706)] :=
  (lex_12_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4705), (Sat.Literal.pos 223), (Sat.Literal.pos 247), (Sat.Literal.pos 4706)] :=
  (lex_12_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4706) = lexBefore s permutation12 222 := by
  exact (positive_lex_of_descriptor s 4706 permutation12 223 (by rfl)).trans ((lex_skipped s permutation12 222 223 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation12 222) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation12 222 by rw [image12_eq]; rfl))

theorem lex_12_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4707) (Sat.Literal.pos 4706) (Sat.Literal.pos 222) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation12 222 (assignment s)
    (Sat.Literal.pos 4707) (Sat.Literal.pos 4706) (Sat.Literal.pos 222) (Sat.Literal.pos 183) (positive_of_descriptor s 4707 (.lex permutation12 222) (by rfl)) (lex_12_222_prefix s) (positive_select s 222) (lex_12_222_image s)

theorem lex_12_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4706), (Sat.Literal.pos 222), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation12 222 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4706) (Sat.Literal.pos 222) (Sat.Literal.pos 183) (lex_12_222_prefix s) (positive_select s 222) (lex_12_222_image s)

theorem lex_12_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4707), (Sat.Literal.pos 4706)] :=
  (lex_12_222_gate s).prop _ (List.Mem.head _)

theorem lex_12_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4707), (Sat.Literal.neg 222), (Sat.Literal.pos 183)] :=
  (lex_12_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4707), (Sat.Literal.pos 222), (Sat.Literal.neg 183)] :=
  (lex_12_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4706), (Sat.Literal.neg 222), (Sat.Literal.neg 183), (Sat.Literal.pos 4707)] :=
  (lex_12_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4706), (Sat.Literal.pos 222), (Sat.Literal.pos 183), (Sat.Literal.pos 4707)] :=
  (lex_12_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4707) = lexBefore s permutation12 221 := by
  exact (positive_lex_of_descriptor s 4707 permutation12 222 (by rfl)).trans ((lex_skipped s permutation12 221 222 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation12 221) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation12 221 by rw [image12_eq]; rfl))

theorem lex_12_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4708) (Sat.Literal.pos 4707) (Sat.Literal.pos 221) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation12 221 (assignment s)
    (Sat.Literal.pos 4708) (Sat.Literal.pos 4707) (Sat.Literal.pos 221) (Sat.Literal.pos 119) (positive_of_descriptor s 4708 (.lex permutation12 221) (by rfl)) (lex_12_221_prefix s) (positive_select s 221) (lex_12_221_image s)

theorem lex_12_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4707), (Sat.Literal.pos 221), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation12 221 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4707) (Sat.Literal.pos 221) (Sat.Literal.pos 119) (lex_12_221_prefix s) (positive_select s 221) (lex_12_221_image s)

theorem lex_12_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4708), (Sat.Literal.pos 4707)] :=
  (lex_12_221_gate s).prop _ (List.Mem.head _)

theorem lex_12_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4708), (Sat.Literal.neg 221), (Sat.Literal.pos 119)] :=
  (lex_12_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4708), (Sat.Literal.pos 221), (Sat.Literal.neg 119)] :=
  (lex_12_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4707), (Sat.Literal.neg 221), (Sat.Literal.neg 119), (Sat.Literal.pos 4708)] :=
  (lex_12_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4707), (Sat.Literal.pos 221), (Sat.Literal.pos 119), (Sat.Literal.pos 4708)] :=
  (lex_12_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4708) = lexBefore s permutation12 220 := by
  exact (positive_lex_of_descriptor s 4708 permutation12 221 (by rfl)).trans ((lex_skipped s permutation12 220 221 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation12 220) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation12 220 by rw [image12_eq]; rfl))

theorem lex_12_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4709) (Sat.Literal.pos 4708) (Sat.Literal.pos 220) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation12 220 (assignment s)
    (Sat.Literal.pos 4709) (Sat.Literal.pos 4708) (Sat.Literal.pos 220) (Sat.Literal.pos 55) (positive_of_descriptor s 4709 (.lex permutation12 220) (by rfl)) (lex_12_220_prefix s) (positive_select s 220) (lex_12_220_image s)

theorem lex_12_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4708), (Sat.Literal.pos 220), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation12 220 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4708) (Sat.Literal.pos 220) (Sat.Literal.pos 55) (lex_12_220_prefix s) (positive_select s 220) (lex_12_220_image s)

theorem lex_12_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4709), (Sat.Literal.pos 4708)] :=
  (lex_12_220_gate s).prop _ (List.Mem.head _)

theorem lex_12_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4709), (Sat.Literal.neg 220), (Sat.Literal.pos 55)] :=
  (lex_12_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4709), (Sat.Literal.pos 220), (Sat.Literal.neg 55)] :=
  (lex_12_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4708), (Sat.Literal.neg 220), (Sat.Literal.neg 55), (Sat.Literal.pos 4709)] :=
  (lex_12_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4708), (Sat.Literal.pos 220), (Sat.Literal.pos 55), (Sat.Literal.pos 4709)] :=
  (lex_12_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4709) = lexBefore s permutation12 219 := by
  exact (positive_lex_of_descriptor s 4709 permutation12 220 (by rfl)).trans ((lex_skipped s permutation12 219 220 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation12 219) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation12 219 by rw [image12_eq]; rfl))

theorem lex_12_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4710) (Sat.Literal.pos 4709) (Sat.Literal.pos 219) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation12 219 (assignment s)
    (Sat.Literal.pos 4710) (Sat.Literal.pos 4709) (Sat.Literal.pos 219) (Sat.Literal.pos 246) (positive_of_descriptor s 4710 (.lex permutation12 219) (by rfl)) (lex_12_219_prefix s) (positive_select s 219) (lex_12_219_image s)

theorem lex_12_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4709), (Sat.Literal.pos 219), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation12 219 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4709) (Sat.Literal.pos 219) (Sat.Literal.pos 246) (lex_12_219_prefix s) (positive_select s 219) (lex_12_219_image s)

theorem lex_12_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4710), (Sat.Literal.pos 4709)] :=
  (lex_12_219_gate s).prop _ (List.Mem.head _)

theorem lex_12_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4710), (Sat.Literal.neg 219), (Sat.Literal.pos 246)] :=
  (lex_12_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4710), (Sat.Literal.pos 219), (Sat.Literal.neg 246)] :=
  (lex_12_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4709), (Sat.Literal.neg 219), (Sat.Literal.neg 246), (Sat.Literal.pos 4710)] :=
  (lex_12_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4709), (Sat.Literal.pos 219), (Sat.Literal.pos 246), (Sat.Literal.pos 4710)] :=
  (lex_12_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4710) = lexBefore s permutation12 218 := by
  exact (positive_lex_of_descriptor s 4710 permutation12 219 (by rfl)).trans ((lex_skipped s permutation12 218 219 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation12 218) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation12 218 by rw [image12_eq]; rfl))

theorem lex_12_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4711) (Sat.Literal.pos 4710) (Sat.Literal.pos 218) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation12 218 (assignment s)
    (Sat.Literal.pos 4711) (Sat.Literal.pos 4710) (Sat.Literal.pos 218) (Sat.Literal.pos 182) (positive_of_descriptor s 4711 (.lex permutation12 218) (by rfl)) (lex_12_218_prefix s) (positive_select s 218) (lex_12_218_image s)

theorem lex_12_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4710), (Sat.Literal.pos 218), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation12 218 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4710) (Sat.Literal.pos 218) (Sat.Literal.pos 182) (lex_12_218_prefix s) (positive_select s 218) (lex_12_218_image s)

theorem lex_12_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4711), (Sat.Literal.pos 4710)] :=
  (lex_12_218_gate s).prop _ (List.Mem.head _)

theorem lex_12_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4711), (Sat.Literal.neg 218), (Sat.Literal.pos 182)] :=
  (lex_12_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4711), (Sat.Literal.pos 218), (Sat.Literal.neg 182)] :=
  (lex_12_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4710), (Sat.Literal.neg 218), (Sat.Literal.neg 182), (Sat.Literal.pos 4711)] :=
  (lex_12_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4710), (Sat.Literal.pos 218), (Sat.Literal.pos 182), (Sat.Literal.pos 4711)] :=
  (lex_12_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4711) = lexBefore s permutation12 217 := by
  exact (positive_lex_of_descriptor s 4711 permutation12 218 (by rfl)).trans ((lex_skipped s permutation12 217 218 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation12 217) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation12 217 by rw [image12_eq]; rfl))

theorem lex_12_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4712) (Sat.Literal.pos 4711) (Sat.Literal.pos 217) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation12 217 (assignment s)
    (Sat.Literal.pos 4712) (Sat.Literal.pos 4711) (Sat.Literal.pos 217) (Sat.Literal.pos 118) (positive_of_descriptor s 4712 (.lex permutation12 217) (by rfl)) (lex_12_217_prefix s) (positive_select s 217) (lex_12_217_image s)

theorem lex_12_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4711), (Sat.Literal.pos 217), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation12 217 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4711) (Sat.Literal.pos 217) (Sat.Literal.pos 118) (lex_12_217_prefix s) (positive_select s 217) (lex_12_217_image s)

theorem lex_12_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4712), (Sat.Literal.pos 4711)] :=
  (lex_12_217_gate s).prop _ (List.Mem.head _)

theorem lex_12_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4712), (Sat.Literal.neg 217), (Sat.Literal.pos 118)] :=
  (lex_12_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4712), (Sat.Literal.pos 217), (Sat.Literal.neg 118)] :=
  (lex_12_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4711), (Sat.Literal.neg 217), (Sat.Literal.neg 118), (Sat.Literal.pos 4712)] :=
  (lex_12_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4711), (Sat.Literal.pos 217), (Sat.Literal.pos 118), (Sat.Literal.pos 4712)] :=
  (lex_12_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4712) = lexBefore s permutation12 216 := by
  exact (positive_lex_of_descriptor s 4712 permutation12 217 (by rfl)).trans ((lex_skipped s permutation12 216 217 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation12 216) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation12 216 by rw [image12_eq]; rfl))

theorem lex_12_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4713) (Sat.Literal.pos 4712) (Sat.Literal.pos 216) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation12 216 (assignment s)
    (Sat.Literal.pos 4713) (Sat.Literal.pos 4712) (Sat.Literal.pos 216) (Sat.Literal.pos 54) (positive_of_descriptor s 4713 (.lex permutation12 216) (by rfl)) (lex_12_216_prefix s) (positive_select s 216) (lex_12_216_image s)

theorem lex_12_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4712), (Sat.Literal.pos 216), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation12 216 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4712) (Sat.Literal.pos 216) (Sat.Literal.pos 54) (lex_12_216_prefix s) (positive_select s 216) (lex_12_216_image s)

theorem lex_12_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4713), (Sat.Literal.pos 4712)] :=
  (lex_12_216_gate s).prop _ (List.Mem.head _)

theorem lex_12_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4713), (Sat.Literal.neg 216), (Sat.Literal.pos 54)] :=
  (lex_12_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4713), (Sat.Literal.pos 216), (Sat.Literal.neg 54)] :=
  (lex_12_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4712), (Sat.Literal.neg 216), (Sat.Literal.neg 54), (Sat.Literal.pos 4713)] :=
  (lex_12_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4712), (Sat.Literal.pos 216), (Sat.Literal.pos 54), (Sat.Literal.pos 4713)] :=
  (lex_12_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4713) = lexBefore s permutation12 215 := by
  exact (positive_lex_of_descriptor s 4713 permutation12 216 (by rfl)).trans ((lex_skipped s permutation12 215 216 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation12 215) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation12 215 by rw [image12_eq]; rfl))

theorem lex_12_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4714) (Sat.Literal.pos 4713) (Sat.Literal.pos 215) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation12 215 (assignment s)
    (Sat.Literal.pos 4714) (Sat.Literal.pos 4713) (Sat.Literal.pos 215) (Sat.Literal.pos 245) (positive_of_descriptor s 4714 (.lex permutation12 215) (by rfl)) (lex_12_215_prefix s) (positive_select s 215) (lex_12_215_image s)

theorem lex_12_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4713), (Sat.Literal.pos 215), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation12 215 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4713) (Sat.Literal.pos 215) (Sat.Literal.pos 245) (lex_12_215_prefix s) (positive_select s 215) (lex_12_215_image s)

theorem lex_12_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4714), (Sat.Literal.pos 4713)] :=
  (lex_12_215_gate s).prop _ (List.Mem.head _)

theorem lex_12_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4714), (Sat.Literal.neg 215), (Sat.Literal.pos 245)] :=
  (lex_12_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4714), (Sat.Literal.pos 215), (Sat.Literal.neg 245)] :=
  (lex_12_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4713), (Sat.Literal.neg 215), (Sat.Literal.neg 245), (Sat.Literal.pos 4714)] :=
  (lex_12_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4713), (Sat.Literal.pos 215), (Sat.Literal.pos 245), (Sat.Literal.pos 4714)] :=
  (lex_12_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4714) = lexBefore s permutation12 214 := by
  exact (positive_lex_of_descriptor s 4714 permutation12 215 (by rfl)).trans ((lex_skipped s permutation12 214 215 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation12 214) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation12 214 by rw [image12_eq]; rfl))

theorem lex_12_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4715) (Sat.Literal.pos 4714) (Sat.Literal.pos 214) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation12 214 (assignment s)
    (Sat.Literal.pos 4715) (Sat.Literal.pos 4714) (Sat.Literal.pos 214) (Sat.Literal.pos 181) (positive_of_descriptor s 4715 (.lex permutation12 214) (by rfl)) (lex_12_214_prefix s) (positive_select s 214) (lex_12_214_image s)

theorem lex_12_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4714), (Sat.Literal.pos 214), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation12 214 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4714) (Sat.Literal.pos 214) (Sat.Literal.pos 181) (lex_12_214_prefix s) (positive_select s 214) (lex_12_214_image s)

theorem lex_12_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4715), (Sat.Literal.pos 4714)] :=
  (lex_12_214_gate s).prop _ (List.Mem.head _)

theorem lex_12_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4715), (Sat.Literal.neg 214), (Sat.Literal.pos 181)] :=
  (lex_12_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4715), (Sat.Literal.pos 214), (Sat.Literal.neg 181)] :=
  (lex_12_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4714), (Sat.Literal.neg 214), (Sat.Literal.neg 181), (Sat.Literal.pos 4715)] :=
  (lex_12_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4714), (Sat.Literal.pos 214), (Sat.Literal.pos 181), (Sat.Literal.pos 4715)] :=
  (lex_12_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4715) = lexBefore s permutation12 213 := by
  exact (positive_lex_of_descriptor s 4715 permutation12 214 (by rfl)).trans ((lex_skipped s permutation12 213 214 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation12 213) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation12 213 by rw [image12_eq]; rfl))

theorem lex_12_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4716) (Sat.Literal.pos 4715) (Sat.Literal.pos 213) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation12 213 (assignment s)
    (Sat.Literal.pos 4716) (Sat.Literal.pos 4715) (Sat.Literal.pos 213) (Sat.Literal.pos 117) (positive_of_descriptor s 4716 (.lex permutation12 213) (by rfl)) (lex_12_213_prefix s) (positive_select s 213) (lex_12_213_image s)

theorem lex_12_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4715), (Sat.Literal.pos 213), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation12 213 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4715) (Sat.Literal.pos 213) (Sat.Literal.pos 117) (lex_12_213_prefix s) (positive_select s 213) (lex_12_213_image s)

theorem lex_12_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4716), (Sat.Literal.pos 4715)] :=
  (lex_12_213_gate s).prop _ (List.Mem.head _)

theorem lex_12_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4716), (Sat.Literal.neg 213), (Sat.Literal.pos 117)] :=
  (lex_12_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4716), (Sat.Literal.pos 213), (Sat.Literal.neg 117)] :=
  (lex_12_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4715), (Sat.Literal.neg 213), (Sat.Literal.neg 117), (Sat.Literal.pos 4716)] :=
  (lex_12_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4715), (Sat.Literal.pos 213), (Sat.Literal.pos 117), (Sat.Literal.pos 4716)] :=
  (lex_12_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4716) = lexBefore s permutation12 212 := by
  exact (positive_lex_of_descriptor s 4716 permutation12 213 (by rfl)).trans ((lex_skipped s permutation12 212 213 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation12 212) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation12 212 by rw [image12_eq]; rfl))

theorem lex_12_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4717) (Sat.Literal.pos 4716) (Sat.Literal.pos 212) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation12 212 (assignment s)
    (Sat.Literal.pos 4717) (Sat.Literal.pos 4716) (Sat.Literal.pos 212) (Sat.Literal.pos 53) (positive_of_descriptor s 4717 (.lex permutation12 212) (by rfl)) (lex_12_212_prefix s) (positive_select s 212) (lex_12_212_image s)

theorem lex_12_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4716), (Sat.Literal.pos 212), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation12 212 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4716) (Sat.Literal.pos 212) (Sat.Literal.pos 53) (lex_12_212_prefix s) (positive_select s 212) (lex_12_212_image s)

theorem lex_12_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4717), (Sat.Literal.pos 4716)] :=
  (lex_12_212_gate s).prop _ (List.Mem.head _)

theorem lex_12_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4717), (Sat.Literal.neg 212), (Sat.Literal.pos 53)] :=
  (lex_12_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4717), (Sat.Literal.pos 212), (Sat.Literal.neg 53)] :=
  (lex_12_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4716), (Sat.Literal.neg 212), (Sat.Literal.neg 53), (Sat.Literal.pos 4717)] :=
  (lex_12_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4716), (Sat.Literal.pos 212), (Sat.Literal.pos 53), (Sat.Literal.pos 4717)] :=
  (lex_12_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4717) = lexBefore s permutation12 211 := by
  exact (positive_lex_of_descriptor s 4717 permutation12 212 (by rfl)).trans ((lex_skipped s permutation12 211 212 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation12 211) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation12 211 by rw [image12_eq]; rfl))

theorem lex_12_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4718) (Sat.Literal.pos 4717) (Sat.Literal.pos 211) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation12 211 (assignment s)
    (Sat.Literal.pos 4718) (Sat.Literal.pos 4717) (Sat.Literal.pos 211) (Sat.Literal.pos 244) (positive_of_descriptor s 4718 (.lex permutation12 211) (by rfl)) (lex_12_211_prefix s) (positive_select s 211) (lex_12_211_image s)

theorem lex_12_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4717), (Sat.Literal.pos 211), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation12 211 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4717) (Sat.Literal.pos 211) (Sat.Literal.pos 244) (lex_12_211_prefix s) (positive_select s 211) (lex_12_211_image s)

theorem lex_12_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4718), (Sat.Literal.pos 4717)] :=
  (lex_12_211_gate s).prop _ (List.Mem.head _)

theorem lex_12_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4718), (Sat.Literal.neg 211), (Sat.Literal.pos 244)] :=
  (lex_12_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4718), (Sat.Literal.pos 211), (Sat.Literal.neg 244)] :=
  (lex_12_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4717), (Sat.Literal.neg 211), (Sat.Literal.neg 244), (Sat.Literal.pos 4718)] :=
  (lex_12_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4717), (Sat.Literal.pos 211), (Sat.Literal.pos 244), (Sat.Literal.pos 4718)] :=
  (lex_12_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4718) = lexBefore s permutation12 210 := by
  exact (positive_lex_of_descriptor s 4718 permutation12 211 (by rfl)).trans ((lex_skipped s permutation12 210 211 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation12 210) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation12 210 by rw [image12_eq]; rfl))

theorem lex_12_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4719) (Sat.Literal.pos 4718) (Sat.Literal.pos 210) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation12 210 (assignment s)
    (Sat.Literal.pos 4719) (Sat.Literal.pos 4718) (Sat.Literal.pos 210) (Sat.Literal.pos 180) (positive_of_descriptor s 4719 (.lex permutation12 210) (by rfl)) (lex_12_210_prefix s) (positive_select s 210) (lex_12_210_image s)

theorem lex_12_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4718), (Sat.Literal.pos 210), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation12 210 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4718) (Sat.Literal.pos 210) (Sat.Literal.pos 180) (lex_12_210_prefix s) (positive_select s 210) (lex_12_210_image s)

theorem lex_12_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4719), (Sat.Literal.pos 4718)] :=
  (lex_12_210_gate s).prop _ (List.Mem.head _)

theorem lex_12_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4719), (Sat.Literal.neg 210), (Sat.Literal.pos 180)] :=
  (lex_12_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4719), (Sat.Literal.pos 210), (Sat.Literal.neg 180)] :=
  (lex_12_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4718), (Sat.Literal.neg 210), (Sat.Literal.neg 180), (Sat.Literal.pos 4719)] :=
  (lex_12_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4718), (Sat.Literal.pos 210), (Sat.Literal.pos 180), (Sat.Literal.pos 4719)] :=
  (lex_12_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4719) = lexBefore s permutation12 209 := by
  exact (positive_lex_of_descriptor s 4719 permutation12 210 (by rfl)).trans ((lex_skipped s permutation12 209 210 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation12 209) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation12 209 by rw [image12_eq]; rfl))

theorem lex_12_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4720) (Sat.Literal.pos 4719) (Sat.Literal.pos 209) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation12 209 (assignment s)
    (Sat.Literal.pos 4720) (Sat.Literal.pos 4719) (Sat.Literal.pos 209) (Sat.Literal.pos 116) (positive_of_descriptor s 4720 (.lex permutation12 209) (by rfl)) (lex_12_209_prefix s) (positive_select s 209) (lex_12_209_image s)

theorem lex_12_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4719), (Sat.Literal.pos 209), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation12 209 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4719) (Sat.Literal.pos 209) (Sat.Literal.pos 116) (lex_12_209_prefix s) (positive_select s 209) (lex_12_209_image s)

theorem lex_12_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4720), (Sat.Literal.pos 4719)] :=
  (lex_12_209_gate s).prop _ (List.Mem.head _)

theorem lex_12_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4720), (Sat.Literal.neg 209), (Sat.Literal.pos 116)] :=
  (lex_12_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4720), (Sat.Literal.pos 209), (Sat.Literal.neg 116)] :=
  (lex_12_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4719), (Sat.Literal.neg 209), (Sat.Literal.neg 116), (Sat.Literal.pos 4720)] :=
  (lex_12_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4719), (Sat.Literal.pos 209), (Sat.Literal.pos 116), (Sat.Literal.pos 4720)] :=
  (lex_12_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4720) = lexBefore s permutation12 208 := by
  exact (positive_lex_of_descriptor s 4720 permutation12 209 (by rfl)).trans ((lex_skipped s permutation12 208 209 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation12 208) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation12 208 by rw [image12_eq]; rfl))

theorem lex_12_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4721) (Sat.Literal.pos 4720) (Sat.Literal.pos 208) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation12 208 (assignment s)
    (Sat.Literal.pos 4721) (Sat.Literal.pos 4720) (Sat.Literal.pos 208) (Sat.Literal.pos 52) (positive_of_descriptor s 4721 (.lex permutation12 208) (by rfl)) (lex_12_208_prefix s) (positive_select s 208) (lex_12_208_image s)

theorem lex_12_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4720), (Sat.Literal.pos 208), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation12 208 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4720) (Sat.Literal.pos 208) (Sat.Literal.pos 52) (lex_12_208_prefix s) (positive_select s 208) (lex_12_208_image s)

theorem lex_12_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4721), (Sat.Literal.pos 4720)] :=
  (lex_12_208_gate s).prop _ (List.Mem.head _)

theorem lex_12_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4721), (Sat.Literal.neg 208), (Sat.Literal.pos 52)] :=
  (lex_12_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4721), (Sat.Literal.pos 208), (Sat.Literal.neg 52)] :=
  (lex_12_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4720), (Sat.Literal.neg 208), (Sat.Literal.neg 52), (Sat.Literal.pos 4721)] :=
  (lex_12_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4720), (Sat.Literal.pos 208), (Sat.Literal.pos 52), (Sat.Literal.pos 4721)] :=
  (lex_12_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4721) = lexBefore s permutation12 207 := by
  exact (positive_lex_of_descriptor s 4721 permutation12 208 (by rfl)).trans ((lex_skipped s permutation12 207 208 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation12 207) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation12 207 by rw [image12_eq]; rfl))

theorem lex_12_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4722) (Sat.Literal.pos 4721) (Sat.Literal.pos 207) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation12 207 (assignment s)
    (Sat.Literal.pos 4722) (Sat.Literal.pos 4721) (Sat.Literal.pos 207) (Sat.Literal.pos 243) (positive_of_descriptor s 4722 (.lex permutation12 207) (by rfl)) (lex_12_207_prefix s) (positive_select s 207) (lex_12_207_image s)

theorem lex_12_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4721), (Sat.Literal.pos 207), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation12 207 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4721) (Sat.Literal.pos 207) (Sat.Literal.pos 243) (lex_12_207_prefix s) (positive_select s 207) (lex_12_207_image s)

theorem lex_12_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4722), (Sat.Literal.pos 4721)] :=
  (lex_12_207_gate s).prop _ (List.Mem.head _)

theorem lex_12_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4722), (Sat.Literal.neg 207), (Sat.Literal.pos 243)] :=
  (lex_12_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4722), (Sat.Literal.pos 207), (Sat.Literal.neg 243)] :=
  (lex_12_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4721), (Sat.Literal.neg 207), (Sat.Literal.neg 243), (Sat.Literal.pos 4722)] :=
  (lex_12_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4721), (Sat.Literal.pos 207), (Sat.Literal.pos 243), (Sat.Literal.pos 4722)] :=
  (lex_12_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4722) = lexBefore s permutation12 206 := by
  exact (positive_lex_of_descriptor s 4722 permutation12 207 (by rfl)).trans ((lex_skipped s permutation12 206 207 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation12 206) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation12 206 by rw [image12_eq]; rfl))

theorem lex_12_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4723) (Sat.Literal.pos 4722) (Sat.Literal.pos 206) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation12 206 (assignment s)
    (Sat.Literal.pos 4723) (Sat.Literal.pos 4722) (Sat.Literal.pos 206) (Sat.Literal.pos 179) (positive_of_descriptor s 4723 (.lex permutation12 206) (by rfl)) (lex_12_206_prefix s) (positive_select s 206) (lex_12_206_image s)

theorem lex_12_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4722), (Sat.Literal.pos 206), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation12 206 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4722) (Sat.Literal.pos 206) (Sat.Literal.pos 179) (lex_12_206_prefix s) (positive_select s 206) (lex_12_206_image s)

theorem lex_12_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4723), (Sat.Literal.pos 4722)] :=
  (lex_12_206_gate s).prop _ (List.Mem.head _)

theorem lex_12_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4723), (Sat.Literal.neg 206), (Sat.Literal.pos 179)] :=
  (lex_12_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4723), (Sat.Literal.pos 206), (Sat.Literal.neg 179)] :=
  (lex_12_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4722), (Sat.Literal.neg 206), (Sat.Literal.neg 179), (Sat.Literal.pos 4723)] :=
  (lex_12_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4722), (Sat.Literal.pos 206), (Sat.Literal.pos 179), (Sat.Literal.pos 4723)] :=
  (lex_12_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4723) = lexBefore s permutation12 205 := by
  exact (positive_lex_of_descriptor s 4723 permutation12 206 (by rfl)).trans ((lex_skipped s permutation12 205 206 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation12 205) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation12 205 by rw [image12_eq]; rfl))

theorem lex_12_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4724) (Sat.Literal.pos 4723) (Sat.Literal.pos 205) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation12 205 (assignment s)
    (Sat.Literal.pos 4724) (Sat.Literal.pos 4723) (Sat.Literal.pos 205) (Sat.Literal.pos 115) (positive_of_descriptor s 4724 (.lex permutation12 205) (by rfl)) (lex_12_205_prefix s) (positive_select s 205) (lex_12_205_image s)

theorem lex_12_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4723), (Sat.Literal.pos 205), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation12 205 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4723) (Sat.Literal.pos 205) (Sat.Literal.pos 115) (lex_12_205_prefix s) (positive_select s 205) (lex_12_205_image s)

theorem lex_12_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4724), (Sat.Literal.pos 4723)] :=
  (lex_12_205_gate s).prop _ (List.Mem.head _)

theorem lex_12_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4724), (Sat.Literal.neg 205), (Sat.Literal.pos 115)] :=
  (lex_12_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4724), (Sat.Literal.pos 205), (Sat.Literal.neg 115)] :=
  (lex_12_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4723), (Sat.Literal.neg 205), (Sat.Literal.neg 115), (Sat.Literal.pos 4724)] :=
  (lex_12_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4723), (Sat.Literal.pos 205), (Sat.Literal.pos 115), (Sat.Literal.pos 4724)] :=
  (lex_12_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_11_50_gate

end Crown.CertificateData
