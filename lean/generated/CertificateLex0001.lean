import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_0_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2624) = lexBefore s permutation0 54 := by
  exact (positive_lex_of_descriptor s 2624 permutation0 57 (by rfl)).trans ((lex_skipped s permutation0 54 57 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 55 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation0 54) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation0 54 by rw [image0_eq]; rfl))

theorem lex_0_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2625) (Sat.Literal.pos 2624) (Sat.Literal.pos 54) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation0 54 (assignment s)
    (Sat.Literal.pos 2625) (Sat.Literal.pos 2624) (Sat.Literal.pos 54) (Sat.Literal.pos 53) (positive_of_descriptor s 2625 (.lex permutation0 54) (by rfl)) (lex_0_54_prefix s) (positive_select s 54) (lex_0_54_image s)

theorem lex_0_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2624), (Sat.Literal.pos 54), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation0 54 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2624) (Sat.Literal.pos 54) (Sat.Literal.pos 53) (lex_0_54_prefix s) (positive_select s 54) (lex_0_54_image s)

theorem lex_0_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2625), (Sat.Literal.pos 2624)] :=
  (lex_0_54_gate s).prop _ (List.Mem.head _)

theorem lex_0_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2625), (Sat.Literal.neg 54), (Sat.Literal.pos 53)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2625), (Sat.Literal.pos 54), (Sat.Literal.neg 53)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2624), (Sat.Literal.neg 54), (Sat.Literal.neg 53), (Sat.Literal.pos 2625)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2624), (Sat.Literal.pos 54), (Sat.Literal.pos 53), (Sat.Literal.pos 2625)] :=
  (lex_0_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2625) = lexBefore s permutation0 53 := by
  exact (positive_lex_of_descriptor s 2625 permutation0 54 (by rfl)).trans ((lex_skipped s permutation0 53 54 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation0 53) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation0 53 by rw [image0_eq]; rfl))

theorem lex_0_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2626) (Sat.Literal.pos 2625) (Sat.Literal.pos 53) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation0 53 (assignment s)
    (Sat.Literal.pos 2626) (Sat.Literal.pos 2625) (Sat.Literal.pos 53) (Sat.Literal.pos 54) (positive_of_descriptor s 2626 (.lex permutation0 53) (by rfl)) (lex_0_53_prefix s) (positive_select s 53) (lex_0_53_image s)

theorem lex_0_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2625), (Sat.Literal.pos 53), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation0 53 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2625) (Sat.Literal.pos 53) (Sat.Literal.pos 54) (lex_0_53_prefix s) (positive_select s 53) (lex_0_53_image s)

theorem lex_0_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2626), (Sat.Literal.pos 2625)] :=
  (lex_0_53_gate s).prop _ (List.Mem.head _)

theorem lex_0_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2626), (Sat.Literal.neg 53), (Sat.Literal.pos 54)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2626), (Sat.Literal.pos 53), (Sat.Literal.neg 54)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2625), (Sat.Literal.neg 53), (Sat.Literal.neg 54), (Sat.Literal.pos 2626)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2625), (Sat.Literal.pos 53), (Sat.Literal.pos 54), (Sat.Literal.pos 2626)] :=
  (lex_0_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2626) = lexBefore s permutation0 50 := by
  exact (positive_lex_of_descriptor s 2626 permutation0 53 (by rfl)).trans ((lex_skipped s permutation0 50 53 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 51 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation0 50) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation0 50 by rw [image0_eq]; rfl))

theorem lex_0_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2627) (Sat.Literal.pos 2626) (Sat.Literal.pos 50) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation0 50 (assignment s)
    (Sat.Literal.pos 2627) (Sat.Literal.pos 2626) (Sat.Literal.pos 50) (Sat.Literal.pos 49) (positive_of_descriptor s 2627 (.lex permutation0 50) (by rfl)) (lex_0_50_prefix s) (positive_select s 50) (lex_0_50_image s)

theorem lex_0_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2626), (Sat.Literal.pos 50), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation0 50 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2626) (Sat.Literal.pos 50) (Sat.Literal.pos 49) (lex_0_50_prefix s) (positive_select s 50) (lex_0_50_image s)

theorem lex_0_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2627), (Sat.Literal.pos 2626)] :=
  (lex_0_50_gate s).prop _ (List.Mem.head _)

theorem lex_0_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2627), (Sat.Literal.neg 50), (Sat.Literal.pos 49)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2627), (Sat.Literal.pos 50), (Sat.Literal.neg 49)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2626), (Sat.Literal.neg 50), (Sat.Literal.neg 49), (Sat.Literal.pos 2627)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2626), (Sat.Literal.pos 50), (Sat.Literal.pos 49), (Sat.Literal.pos 2627)] :=
  (lex_0_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2627) = lexBefore s permutation0 49 := by
  exact (positive_lex_of_descriptor s 2627 permutation0 50 (by rfl)).trans ((lex_skipped s permutation0 49 50 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 50) = s (permuteMask permutation0 49) := by
  exact (positive_select s 50).trans (congrArg s (show (50 : Fin 256) = permuteMask permutation0 49 by rw [image0_eq]; rfl))

theorem lex_0_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2628) (Sat.Literal.pos 2627) (Sat.Literal.pos 49) (Sat.Literal.pos 50)) := by
  exact equality_gate s permutation0 49 (assignment s)
    (Sat.Literal.pos 2628) (Sat.Literal.pos 2627) (Sat.Literal.pos 49) (Sat.Literal.pos 50) (positive_of_descriptor s 2628 (.lex permutation0 49) (by rfl)) (lex_0_49_prefix s) (positive_select s 49) (lex_0_49_image s)

theorem lex_0_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2627), (Sat.Literal.pos 49), (Sat.Literal.neg 50)] := by
  exact comparison_gate s permutation0 49 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2627) (Sat.Literal.pos 49) (Sat.Literal.pos 50) (lex_0_49_prefix s) (positive_select s 49) (lex_0_49_image s)

theorem lex_0_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2628), (Sat.Literal.pos 2627)] :=
  (lex_0_49_gate s).prop _ (List.Mem.head _)

theorem lex_0_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2628), (Sat.Literal.neg 49), (Sat.Literal.pos 50)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2628), (Sat.Literal.pos 49), (Sat.Literal.neg 50)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2627), (Sat.Literal.neg 49), (Sat.Literal.neg 50), (Sat.Literal.pos 2628)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2627), (Sat.Literal.pos 49), (Sat.Literal.pos 50), (Sat.Literal.pos 2628)] :=
  (lex_0_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2628) = lexBefore s permutation0 46 := by
  exact (positive_lex_of_descriptor s 2628 permutation0 49 (by rfl)).trans ((lex_skipped s permutation0 46 49 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 47 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation0 46) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation0 46 by rw [image0_eq]; rfl))

theorem lex_0_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2629) (Sat.Literal.pos 2628) (Sat.Literal.pos 46) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation0 46 (assignment s)
    (Sat.Literal.pos 2629) (Sat.Literal.pos 2628) (Sat.Literal.pos 46) (Sat.Literal.pos 45) (positive_of_descriptor s 2629 (.lex permutation0 46) (by rfl)) (lex_0_46_prefix s) (positive_select s 46) (lex_0_46_image s)

theorem lex_0_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2628), (Sat.Literal.pos 46), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation0 46 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2628) (Sat.Literal.pos 46) (Sat.Literal.pos 45) (lex_0_46_prefix s) (positive_select s 46) (lex_0_46_image s)

theorem lex_0_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2629), (Sat.Literal.pos 2628)] :=
  (lex_0_46_gate s).prop _ (List.Mem.head _)

theorem lex_0_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2629), (Sat.Literal.neg 46), (Sat.Literal.pos 45)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2629), (Sat.Literal.pos 46), (Sat.Literal.neg 45)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2628), (Sat.Literal.neg 46), (Sat.Literal.neg 45), (Sat.Literal.pos 2629)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2628), (Sat.Literal.pos 46), (Sat.Literal.pos 45), (Sat.Literal.pos 2629)] :=
  (lex_0_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2629) = lexBefore s permutation0 45 := by
  exact (positive_lex_of_descriptor s 2629 permutation0 46 (by rfl)).trans ((lex_skipped s permutation0 45 46 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation0 45) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation0 45 by rw [image0_eq]; rfl))

theorem lex_0_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2630) (Sat.Literal.pos 2629) (Sat.Literal.pos 45) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation0 45 (assignment s)
    (Sat.Literal.pos 2630) (Sat.Literal.pos 2629) (Sat.Literal.pos 45) (Sat.Literal.pos 46) (positive_of_descriptor s 2630 (.lex permutation0 45) (by rfl)) (lex_0_45_prefix s) (positive_select s 45) (lex_0_45_image s)

theorem lex_0_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2629), (Sat.Literal.pos 45), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation0 45 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2629) (Sat.Literal.pos 45) (Sat.Literal.pos 46) (lex_0_45_prefix s) (positive_select s 45) (lex_0_45_image s)

theorem lex_0_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2630), (Sat.Literal.pos 2629)] :=
  (lex_0_45_gate s).prop _ (List.Mem.head _)

theorem lex_0_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2630), (Sat.Literal.neg 45), (Sat.Literal.pos 46)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2630), (Sat.Literal.pos 45), (Sat.Literal.neg 46)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2629), (Sat.Literal.neg 45), (Sat.Literal.neg 46), (Sat.Literal.pos 2630)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2629), (Sat.Literal.pos 45), (Sat.Literal.pos 46), (Sat.Literal.pos 2630)] :=
  (lex_0_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2630) = lexBefore s permutation0 42 := by
  exact (positive_lex_of_descriptor s 2630 permutation0 45 (by rfl)).trans ((lex_skipped s permutation0 42 45 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 43 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation0 42) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation0 42 by rw [image0_eq]; rfl))

theorem lex_0_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2631) (Sat.Literal.pos 2630) (Sat.Literal.pos 42) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation0 42 (assignment s)
    (Sat.Literal.pos 2631) (Sat.Literal.pos 2630) (Sat.Literal.pos 42) (Sat.Literal.pos 41) (positive_of_descriptor s 2631 (.lex permutation0 42) (by rfl)) (lex_0_42_prefix s) (positive_select s 42) (lex_0_42_image s)

theorem lex_0_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2630), (Sat.Literal.pos 42), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation0 42 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2630) (Sat.Literal.pos 42) (Sat.Literal.pos 41) (lex_0_42_prefix s) (positive_select s 42) (lex_0_42_image s)

theorem lex_0_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2631), (Sat.Literal.pos 2630)] :=
  (lex_0_42_gate s).prop _ (List.Mem.head _)

theorem lex_0_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2631), (Sat.Literal.neg 42), (Sat.Literal.pos 41)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2631), (Sat.Literal.pos 42), (Sat.Literal.neg 41)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2630), (Sat.Literal.neg 42), (Sat.Literal.neg 41), (Sat.Literal.pos 2631)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2630), (Sat.Literal.pos 42), (Sat.Literal.pos 41), (Sat.Literal.pos 2631)] :=
  (lex_0_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2631) = lexBefore s permutation0 41 := by
  exact (positive_lex_of_descriptor s 2631 permutation0 42 (by rfl)).trans ((lex_skipped s permutation0 41 42 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 42) = s (permuteMask permutation0 41) := by
  exact (positive_select s 42).trans (congrArg s (show (42 : Fin 256) = permuteMask permutation0 41 by rw [image0_eq]; rfl))

theorem lex_0_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2632) (Sat.Literal.pos 2631) (Sat.Literal.pos 41) (Sat.Literal.pos 42)) := by
  exact equality_gate s permutation0 41 (assignment s)
    (Sat.Literal.pos 2632) (Sat.Literal.pos 2631) (Sat.Literal.pos 41) (Sat.Literal.pos 42) (positive_of_descriptor s 2632 (.lex permutation0 41) (by rfl)) (lex_0_41_prefix s) (positive_select s 41) (lex_0_41_image s)

theorem lex_0_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2631), (Sat.Literal.pos 41), (Sat.Literal.neg 42)] := by
  exact comparison_gate s permutation0 41 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2631) (Sat.Literal.pos 41) (Sat.Literal.pos 42) (lex_0_41_prefix s) (positive_select s 41) (lex_0_41_image s)

theorem lex_0_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2632), (Sat.Literal.pos 2631)] :=
  (lex_0_41_gate s).prop _ (List.Mem.head _)

theorem lex_0_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2632), (Sat.Literal.neg 41), (Sat.Literal.pos 42)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2632), (Sat.Literal.pos 41), (Sat.Literal.neg 42)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2631), (Sat.Literal.neg 41), (Sat.Literal.neg 42), (Sat.Literal.pos 2632)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2631), (Sat.Literal.pos 41), (Sat.Literal.pos 42), (Sat.Literal.pos 2632)] :=
  (lex_0_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2632) = lexBefore s permutation0 38 := by
  exact (positive_lex_of_descriptor s 2632 permutation0 41 (by rfl)).trans ((lex_skipped s permutation0 38 41 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 39 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation0 38) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation0 38 by rw [image0_eq]; rfl))

theorem lex_0_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2633) (Sat.Literal.pos 2632) (Sat.Literal.pos 38) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation0 38 (assignment s)
    (Sat.Literal.pos 2633) (Sat.Literal.pos 2632) (Sat.Literal.pos 38) (Sat.Literal.pos 37) (positive_of_descriptor s 2633 (.lex permutation0 38) (by rfl)) (lex_0_38_prefix s) (positive_select s 38) (lex_0_38_image s)

theorem lex_0_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2632), (Sat.Literal.pos 38), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation0 38 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2632) (Sat.Literal.pos 38) (Sat.Literal.pos 37) (lex_0_38_prefix s) (positive_select s 38) (lex_0_38_image s)

theorem lex_0_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2633), (Sat.Literal.pos 2632)] :=
  (lex_0_38_gate s).prop _ (List.Mem.head _)

theorem lex_0_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2633), (Sat.Literal.neg 38), (Sat.Literal.pos 37)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2633), (Sat.Literal.pos 38), (Sat.Literal.neg 37)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2632), (Sat.Literal.neg 38), (Sat.Literal.neg 37), (Sat.Literal.pos 2633)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2632), (Sat.Literal.pos 38), (Sat.Literal.pos 37), (Sat.Literal.pos 2633)] :=
  (lex_0_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2633) = lexBefore s permutation0 37 := by
  exact (positive_lex_of_descriptor s 2633 permutation0 38 (by rfl)).trans ((lex_skipped s permutation0 37 38 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation0 37) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation0 37 by rw [image0_eq]; rfl))

theorem lex_0_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2634) (Sat.Literal.pos 2633) (Sat.Literal.pos 37) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation0 37 (assignment s)
    (Sat.Literal.pos 2634) (Sat.Literal.pos 2633) (Sat.Literal.pos 37) (Sat.Literal.pos 38) (positive_of_descriptor s 2634 (.lex permutation0 37) (by rfl)) (lex_0_37_prefix s) (positive_select s 37) (lex_0_37_image s)

theorem lex_0_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2633), (Sat.Literal.pos 37), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation0 37 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2633) (Sat.Literal.pos 37) (Sat.Literal.pos 38) (lex_0_37_prefix s) (positive_select s 37) (lex_0_37_image s)

theorem lex_0_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2634), (Sat.Literal.pos 2633)] :=
  (lex_0_37_gate s).prop _ (List.Mem.head _)

theorem lex_0_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2634), (Sat.Literal.neg 37), (Sat.Literal.pos 38)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2634), (Sat.Literal.pos 37), (Sat.Literal.neg 38)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2633), (Sat.Literal.neg 37), (Sat.Literal.neg 38), (Sat.Literal.pos 2634)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2633), (Sat.Literal.pos 37), (Sat.Literal.pos 38), (Sat.Literal.pos 2634)] :=
  (lex_0_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2634) = lexBefore s permutation0 34 := by
  exact (positive_lex_of_descriptor s 2634 permutation0 37 (by rfl)).trans ((lex_skipped s permutation0 34 37 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 35 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation0 34) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation0 34 by rw [image0_eq]; rfl))

theorem lex_0_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2635) (Sat.Literal.pos 2634) (Sat.Literal.pos 34) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation0 34 (assignment s)
    (Sat.Literal.pos 2635) (Sat.Literal.pos 2634) (Sat.Literal.pos 34) (Sat.Literal.pos 33) (positive_of_descriptor s 2635 (.lex permutation0 34) (by rfl)) (lex_0_34_prefix s) (positive_select s 34) (lex_0_34_image s)

theorem lex_0_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2634), (Sat.Literal.pos 34), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation0 34 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2634) (Sat.Literal.pos 34) (Sat.Literal.pos 33) (lex_0_34_prefix s) (positive_select s 34) (lex_0_34_image s)

theorem lex_0_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2635), (Sat.Literal.pos 2634)] :=
  (lex_0_34_gate s).prop _ (List.Mem.head _)

theorem lex_0_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2635), (Sat.Literal.neg 34), (Sat.Literal.pos 33)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2635), (Sat.Literal.pos 34), (Sat.Literal.neg 33)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2634), (Sat.Literal.neg 34), (Sat.Literal.neg 33), (Sat.Literal.pos 2635)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2634), (Sat.Literal.pos 34), (Sat.Literal.pos 33), (Sat.Literal.pos 2635)] :=
  (lex_0_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2635) = lexBefore s permutation0 33 := by
  exact (positive_lex_of_descriptor s 2635 permutation0 34 (by rfl)).trans ((lex_skipped s permutation0 33 34 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 34) = s (permuteMask permutation0 33) := by
  exact (positive_select s 34).trans (congrArg s (show (34 : Fin 256) = permuteMask permutation0 33 by rw [image0_eq]; rfl))

theorem lex_0_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2636) (Sat.Literal.pos 2635) (Sat.Literal.pos 33) (Sat.Literal.pos 34)) := by
  exact equality_gate s permutation0 33 (assignment s)
    (Sat.Literal.pos 2636) (Sat.Literal.pos 2635) (Sat.Literal.pos 33) (Sat.Literal.pos 34) (positive_of_descriptor s 2636 (.lex permutation0 33) (by rfl)) (lex_0_33_prefix s) (positive_select s 33) (lex_0_33_image s)

theorem lex_0_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2635), (Sat.Literal.pos 33), (Sat.Literal.neg 34)] := by
  exact comparison_gate s permutation0 33 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2635) (Sat.Literal.pos 33) (Sat.Literal.pos 34) (lex_0_33_prefix s) (positive_select s 33) (lex_0_33_image s)

theorem lex_0_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2636), (Sat.Literal.pos 2635)] :=
  (lex_0_33_gate s).prop _ (List.Mem.head _)

theorem lex_0_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2636), (Sat.Literal.neg 33), (Sat.Literal.pos 34)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2636), (Sat.Literal.pos 33), (Sat.Literal.neg 34)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2635), (Sat.Literal.neg 33), (Sat.Literal.neg 34), (Sat.Literal.pos 2636)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2635), (Sat.Literal.pos 33), (Sat.Literal.pos 34), (Sat.Literal.pos 2636)] :=
  (lex_0_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2636) = lexBefore s permutation0 30 := by
  exact (positive_lex_of_descriptor s 2636 permutation0 33 (by rfl)).trans ((lex_skipped s permutation0 30 33 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 31 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation0 30) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation0 30 by rw [image0_eq]; rfl))

theorem lex_0_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2637) (Sat.Literal.pos 2636) (Sat.Literal.pos 30) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation0 30 (assignment s)
    (Sat.Literal.pos 2637) (Sat.Literal.pos 2636) (Sat.Literal.pos 30) (Sat.Literal.pos 29) (positive_of_descriptor s 2637 (.lex permutation0 30) (by rfl)) (lex_0_30_prefix s) (positive_select s 30) (lex_0_30_image s)

theorem lex_0_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2636), (Sat.Literal.pos 30), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation0 30 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2636) (Sat.Literal.pos 30) (Sat.Literal.pos 29) (lex_0_30_prefix s) (positive_select s 30) (lex_0_30_image s)

theorem lex_0_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2637), (Sat.Literal.pos 2636)] :=
  (lex_0_30_gate s).prop _ (List.Mem.head _)

theorem lex_0_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2637), (Sat.Literal.neg 30), (Sat.Literal.pos 29)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2637), (Sat.Literal.pos 30), (Sat.Literal.neg 29)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2636), (Sat.Literal.neg 30), (Sat.Literal.neg 29), (Sat.Literal.pos 2637)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2636), (Sat.Literal.pos 30), (Sat.Literal.pos 29), (Sat.Literal.pos 2637)] :=
  (lex_0_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2637) = lexBefore s permutation0 29 := by
  exact (positive_lex_of_descriptor s 2637 permutation0 30 (by rfl)).trans ((lex_skipped s permutation0 29 30 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation0 29) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation0 29 by rw [image0_eq]; rfl))

theorem lex_0_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2638) (Sat.Literal.pos 2637) (Sat.Literal.pos 29) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation0 29 (assignment s)
    (Sat.Literal.pos 2638) (Sat.Literal.pos 2637) (Sat.Literal.pos 29) (Sat.Literal.pos 30) (positive_of_descriptor s 2638 (.lex permutation0 29) (by rfl)) (lex_0_29_prefix s) (positive_select s 29) (lex_0_29_image s)

theorem lex_0_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2637), (Sat.Literal.pos 29), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation0 29 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2637) (Sat.Literal.pos 29) (Sat.Literal.pos 30) (lex_0_29_prefix s) (positive_select s 29) (lex_0_29_image s)

theorem lex_0_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2638), (Sat.Literal.pos 2637)] :=
  (lex_0_29_gate s).prop _ (List.Mem.head _)

theorem lex_0_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2638), (Sat.Literal.neg 29), (Sat.Literal.pos 30)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2638), (Sat.Literal.pos 29), (Sat.Literal.neg 30)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2637), (Sat.Literal.neg 29), (Sat.Literal.neg 30), (Sat.Literal.pos 2638)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2637), (Sat.Literal.pos 29), (Sat.Literal.pos 30), (Sat.Literal.pos 2638)] :=
  (lex_0_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2638) = lexBefore s permutation0 26 := by
  exact (positive_lex_of_descriptor s 2638 permutation0 29 (by rfl)).trans ((lex_skipped s permutation0 26 29 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 27 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation0 26) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation0 26 by rw [image0_eq]; rfl))

theorem lex_0_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2639) (Sat.Literal.pos 2638) (Sat.Literal.pos 26) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation0 26 (assignment s)
    (Sat.Literal.pos 2639) (Sat.Literal.pos 2638) (Sat.Literal.pos 26) (Sat.Literal.pos 25) (positive_of_descriptor s 2639 (.lex permutation0 26) (by rfl)) (lex_0_26_prefix s) (positive_select s 26) (lex_0_26_image s)

theorem lex_0_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2638), (Sat.Literal.pos 26), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation0 26 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2638) (Sat.Literal.pos 26) (Sat.Literal.pos 25) (lex_0_26_prefix s) (positive_select s 26) (lex_0_26_image s)

theorem lex_0_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2639), (Sat.Literal.pos 2638)] :=
  (lex_0_26_gate s).prop _ (List.Mem.head _)

theorem lex_0_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2639), (Sat.Literal.neg 26), (Sat.Literal.pos 25)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2639), (Sat.Literal.pos 26), (Sat.Literal.neg 25)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2638), (Sat.Literal.neg 26), (Sat.Literal.neg 25), (Sat.Literal.pos 2639)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2638), (Sat.Literal.pos 26), (Sat.Literal.pos 25), (Sat.Literal.pos 2639)] :=
  (lex_0_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2639) = lexBefore s permutation0 25 := by
  exact (positive_lex_of_descriptor s 2639 permutation0 26 (by rfl)).trans ((lex_skipped s permutation0 25 26 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation0 25) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation0 25 by rw [image0_eq]; rfl))

theorem lex_0_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2640) (Sat.Literal.pos 2639) (Sat.Literal.pos 25) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation0 25 (assignment s)
    (Sat.Literal.pos 2640) (Sat.Literal.pos 2639) (Sat.Literal.pos 25) (Sat.Literal.pos 26) (positive_of_descriptor s 2640 (.lex permutation0 25) (by rfl)) (lex_0_25_prefix s) (positive_select s 25) (lex_0_25_image s)

theorem lex_0_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2639), (Sat.Literal.pos 25), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation0 25 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2639) (Sat.Literal.pos 25) (Sat.Literal.pos 26) (lex_0_25_prefix s) (positive_select s 25) (lex_0_25_image s)

theorem lex_0_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2640), (Sat.Literal.pos 2639)] :=
  (lex_0_25_gate s).prop _ (List.Mem.head _)

theorem lex_0_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2640), (Sat.Literal.neg 25), (Sat.Literal.pos 26)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2640), (Sat.Literal.pos 25), (Sat.Literal.neg 26)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2639), (Sat.Literal.neg 25), (Sat.Literal.neg 26), (Sat.Literal.pos 2640)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2639), (Sat.Literal.pos 25), (Sat.Literal.pos 26), (Sat.Literal.pos 2640)] :=
  (lex_0_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2640) = lexBefore s permutation0 22 := by
  exact (positive_lex_of_descriptor s 2640 permutation0 25 (by rfl)).trans ((lex_skipped s permutation0 22 25 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 23 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation0 22) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation0 22 by rw [image0_eq]; rfl))

theorem lex_0_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2641) (Sat.Literal.pos 2640) (Sat.Literal.pos 22) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation0 22 (assignment s)
    (Sat.Literal.pos 2641) (Sat.Literal.pos 2640) (Sat.Literal.pos 22) (Sat.Literal.pos 21) (positive_of_descriptor s 2641 (.lex permutation0 22) (by rfl)) (lex_0_22_prefix s) (positive_select s 22) (lex_0_22_image s)

theorem lex_0_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2640), (Sat.Literal.pos 22), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation0 22 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2640) (Sat.Literal.pos 22) (Sat.Literal.pos 21) (lex_0_22_prefix s) (positive_select s 22) (lex_0_22_image s)

theorem lex_0_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2641), (Sat.Literal.pos 2640)] :=
  (lex_0_22_gate s).prop _ (List.Mem.head _)

theorem lex_0_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2641), (Sat.Literal.neg 22), (Sat.Literal.pos 21)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2641), (Sat.Literal.pos 22), (Sat.Literal.neg 21)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2640), (Sat.Literal.neg 22), (Sat.Literal.neg 21), (Sat.Literal.pos 2641)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2640), (Sat.Literal.pos 22), (Sat.Literal.pos 21), (Sat.Literal.pos 2641)] :=
  (lex_0_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2641) = lexBefore s permutation0 21 := by
  exact (positive_lex_of_descriptor s 2641 permutation0 22 (by rfl)).trans ((lex_skipped s permutation0 21 22 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation0 21) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation0 21 by rw [image0_eq]; rfl))

theorem lex_0_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2642) (Sat.Literal.pos 2641) (Sat.Literal.pos 21) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation0 21 (assignment s)
    (Sat.Literal.pos 2642) (Sat.Literal.pos 2641) (Sat.Literal.pos 21) (Sat.Literal.pos 22) (positive_of_descriptor s 2642 (.lex permutation0 21) (by rfl)) (lex_0_21_prefix s) (positive_select s 21) (lex_0_21_image s)

theorem lex_0_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2641), (Sat.Literal.pos 21), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation0 21 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2641) (Sat.Literal.pos 21) (Sat.Literal.pos 22) (lex_0_21_prefix s) (positive_select s 21) (lex_0_21_image s)

theorem lex_0_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2642), (Sat.Literal.pos 2641)] :=
  (lex_0_21_gate s).prop _ (List.Mem.head _)

theorem lex_0_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2642), (Sat.Literal.neg 21), (Sat.Literal.pos 22)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2642), (Sat.Literal.pos 21), (Sat.Literal.neg 22)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2641), (Sat.Literal.neg 21), (Sat.Literal.neg 22), (Sat.Literal.pos 2642)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2641), (Sat.Literal.pos 21), (Sat.Literal.pos 22), (Sat.Literal.pos 2642)] :=
  (lex_0_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2642) = lexBefore s permutation0 18 := by
  exact (positive_lex_of_descriptor s 2642 permutation0 21 (by rfl)).trans ((lex_skipped s permutation0 18 21 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 19 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation0 18) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation0 18 by rw [image0_eq]; rfl))

theorem lex_0_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2643) (Sat.Literal.pos 2642) (Sat.Literal.pos 18) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation0 18 (assignment s)
    (Sat.Literal.pos 2643) (Sat.Literal.pos 2642) (Sat.Literal.pos 18) (Sat.Literal.pos 17) (positive_of_descriptor s 2643 (.lex permutation0 18) (by rfl)) (lex_0_18_prefix s) (positive_select s 18) (lex_0_18_image s)

theorem lex_0_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2642), (Sat.Literal.pos 18), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation0 18 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2642) (Sat.Literal.pos 18) (Sat.Literal.pos 17) (lex_0_18_prefix s) (positive_select s 18) (lex_0_18_image s)

theorem lex_0_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2643), (Sat.Literal.pos 2642)] :=
  (lex_0_18_gate s).prop _ (List.Mem.head _)

theorem lex_0_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2643), (Sat.Literal.neg 18), (Sat.Literal.pos 17)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2643), (Sat.Literal.pos 18), (Sat.Literal.neg 17)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2642), (Sat.Literal.neg 18), (Sat.Literal.neg 17), (Sat.Literal.pos 2643)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2642), (Sat.Literal.pos 18), (Sat.Literal.pos 17), (Sat.Literal.pos 2643)] :=
  (lex_0_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2643) = lexBefore s permutation0 17 := by
  exact (positive_lex_of_descriptor s 2643 permutation0 18 (by rfl)).trans ((lex_skipped s permutation0 17 18 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation0 17) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation0 17 by rw [image0_eq]; rfl))

theorem lex_0_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2644) (Sat.Literal.pos 2643) (Sat.Literal.pos 17) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation0 17 (assignment s)
    (Sat.Literal.pos 2644) (Sat.Literal.pos 2643) (Sat.Literal.pos 17) (Sat.Literal.pos 18) (positive_of_descriptor s 2644 (.lex permutation0 17) (by rfl)) (lex_0_17_prefix s) (positive_select s 17) (lex_0_17_image s)

theorem lex_0_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2643), (Sat.Literal.pos 17), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation0 17 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2643) (Sat.Literal.pos 17) (Sat.Literal.pos 18) (lex_0_17_prefix s) (positive_select s 17) (lex_0_17_image s)

theorem lex_0_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2644), (Sat.Literal.pos 2643)] :=
  (lex_0_17_gate s).prop _ (List.Mem.head _)

theorem lex_0_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2644), (Sat.Literal.neg 17), (Sat.Literal.pos 18)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2644), (Sat.Literal.pos 17), (Sat.Literal.neg 18)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2643), (Sat.Literal.neg 17), (Sat.Literal.neg 18), (Sat.Literal.pos 2644)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2643), (Sat.Literal.pos 17), (Sat.Literal.pos 18), (Sat.Literal.pos 2644)] :=
  (lex_0_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2644) = lexBefore s permutation0 14 := by
  exact (positive_lex_of_descriptor s 2644 permutation0 17 (by rfl)).trans ((lex_skipped s permutation0 14 17 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 15 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation0 14) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation0 14 by rw [image0_eq]; rfl))

theorem lex_0_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2645) (Sat.Literal.pos 2644) (Sat.Literal.pos 14) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation0 14 (assignment s)
    (Sat.Literal.pos 2645) (Sat.Literal.pos 2644) (Sat.Literal.pos 14) (Sat.Literal.pos 13) (positive_of_descriptor s 2645 (.lex permutation0 14) (by rfl)) (lex_0_14_prefix s) (positive_select s 14) (lex_0_14_image s)

theorem lex_0_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2644), (Sat.Literal.pos 14), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation0 14 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2644) (Sat.Literal.pos 14) (Sat.Literal.pos 13) (lex_0_14_prefix s) (positive_select s 14) (lex_0_14_image s)

theorem lex_0_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2645), (Sat.Literal.pos 2644)] :=
  (lex_0_14_gate s).prop _ (List.Mem.head _)

theorem lex_0_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2645), (Sat.Literal.neg 14), (Sat.Literal.pos 13)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2645), (Sat.Literal.pos 14), (Sat.Literal.neg 13)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2644), (Sat.Literal.neg 14), (Sat.Literal.neg 13), (Sat.Literal.pos 2645)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2644), (Sat.Literal.pos 14), (Sat.Literal.pos 13), (Sat.Literal.pos 2645)] :=
  (lex_0_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2645) = lexBefore s permutation0 13 := by
  exact (positive_lex_of_descriptor s 2645 permutation0 14 (by rfl)).trans ((lex_skipped s permutation0 13 14 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation0 13) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation0 13 by rw [image0_eq]; rfl))

theorem lex_0_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2646) (Sat.Literal.pos 2645) (Sat.Literal.pos 13) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation0 13 (assignment s)
    (Sat.Literal.pos 2646) (Sat.Literal.pos 2645) (Sat.Literal.pos 13) (Sat.Literal.pos 14) (positive_of_descriptor s 2646 (.lex permutation0 13) (by rfl)) (lex_0_13_prefix s) (positive_select s 13) (lex_0_13_image s)

theorem lex_0_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2645), (Sat.Literal.pos 13), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation0 13 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2645) (Sat.Literal.pos 13) (Sat.Literal.pos 14) (lex_0_13_prefix s) (positive_select s 13) (lex_0_13_image s)

theorem lex_0_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2646), (Sat.Literal.pos 2645)] :=
  (lex_0_13_gate s).prop _ (List.Mem.head _)

theorem lex_0_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2646), (Sat.Literal.neg 13), (Sat.Literal.pos 14)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2646), (Sat.Literal.pos 13), (Sat.Literal.neg 14)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2645), (Sat.Literal.neg 13), (Sat.Literal.neg 14), (Sat.Literal.pos 2646)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2645), (Sat.Literal.pos 13), (Sat.Literal.pos 14), (Sat.Literal.pos 2646)] :=
  (lex_0_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2646) = lexBefore s permutation0 10 := by
  exact (positive_lex_of_descriptor s 2646 permutation0 13 (by rfl)).trans ((lex_skipped s permutation0 10 13 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 11 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation0 10) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation0 10 by rw [image0_eq]; rfl))

theorem lex_0_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2647) (Sat.Literal.pos 2646) (Sat.Literal.pos 10) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation0 10 (assignment s)
    (Sat.Literal.pos 2647) (Sat.Literal.pos 2646) (Sat.Literal.pos 10) (Sat.Literal.pos 9) (positive_of_descriptor s 2647 (.lex permutation0 10) (by rfl)) (lex_0_10_prefix s) (positive_select s 10) (lex_0_10_image s)

theorem lex_0_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2646), (Sat.Literal.pos 10), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation0 10 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2646) (Sat.Literal.pos 10) (Sat.Literal.pos 9) (lex_0_10_prefix s) (positive_select s 10) (lex_0_10_image s)

theorem lex_0_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2647), (Sat.Literal.pos 2646)] :=
  (lex_0_10_gate s).prop _ (List.Mem.head _)

theorem lex_0_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2647), (Sat.Literal.neg 10), (Sat.Literal.pos 9)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2647), (Sat.Literal.pos 10), (Sat.Literal.neg 9)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2646), (Sat.Literal.neg 10), (Sat.Literal.neg 9), (Sat.Literal.pos 2647)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2646), (Sat.Literal.pos 10), (Sat.Literal.pos 9), (Sat.Literal.pos 2647)] :=
  (lex_0_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2647) = lexBefore s permutation0 9 := by
  exact (positive_lex_of_descriptor s 2647 permutation0 10 (by rfl)).trans ((lex_skipped s permutation0 9 10 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation0 9) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation0 9 by rw [image0_eq]; rfl))

theorem lex_0_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2648) (Sat.Literal.pos 2647) (Sat.Literal.pos 9) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation0 9 (assignment s)
    (Sat.Literal.pos 2648) (Sat.Literal.pos 2647) (Sat.Literal.pos 9) (Sat.Literal.pos 10) (positive_of_descriptor s 2648 (.lex permutation0 9) (by rfl)) (lex_0_9_prefix s) (positive_select s 9) (lex_0_9_image s)

theorem lex_0_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2647), (Sat.Literal.pos 9), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation0 9 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2647) (Sat.Literal.pos 9) (Sat.Literal.pos 10) (lex_0_9_prefix s) (positive_select s 9) (lex_0_9_image s)

theorem lex_0_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2648), (Sat.Literal.pos 2647)] :=
  (lex_0_9_gate s).prop _ (List.Mem.head _)

theorem lex_0_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2648), (Sat.Literal.neg 9), (Sat.Literal.pos 10)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2648), (Sat.Literal.pos 9), (Sat.Literal.neg 10)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2647), (Sat.Literal.neg 9), (Sat.Literal.neg 10), (Sat.Literal.pos 2648)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2647), (Sat.Literal.pos 9), (Sat.Literal.pos 10), (Sat.Literal.pos 2648)] :=
  (lex_0_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2648) = lexBefore s permutation0 6 := by
  exact (positive_lex_of_descriptor s 2648 permutation0 9 (by rfl)).trans ((lex_skipped s permutation0 6 9 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 7 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation0 6) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation0 6 by rw [image0_eq]; rfl))

theorem lex_0_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2649) (Sat.Literal.pos 2648) (Sat.Literal.pos 6) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation0 6 (assignment s)
    (Sat.Literal.pos 2649) (Sat.Literal.pos 2648) (Sat.Literal.pos 6) (Sat.Literal.pos 5) (positive_of_descriptor s 2649 (.lex permutation0 6) (by rfl)) (lex_0_6_prefix s) (positive_select s 6) (lex_0_6_image s)

theorem lex_0_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2648), (Sat.Literal.pos 6), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation0 6 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2648) (Sat.Literal.pos 6) (Sat.Literal.pos 5) (lex_0_6_prefix s) (positive_select s 6) (lex_0_6_image s)

theorem lex_0_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2649), (Sat.Literal.pos 2648)] :=
  (lex_0_6_gate s).prop _ (List.Mem.head _)

theorem lex_0_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2649), (Sat.Literal.neg 6), (Sat.Literal.pos 5)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2649), (Sat.Literal.pos 6), (Sat.Literal.neg 5)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2648), (Sat.Literal.neg 6), (Sat.Literal.neg 5), (Sat.Literal.pos 2649)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2648), (Sat.Literal.pos 6), (Sat.Literal.pos 5), (Sat.Literal.pos 2649)] :=
  (lex_0_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2649) = lexBefore s permutation0 5 := by
  exact (positive_lex_of_descriptor s 2649 permutation0 6 (by rfl)).trans ((lex_skipped s permutation0 5 6 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation0 5) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation0 5 by rw [image0_eq]; rfl))

theorem lex_0_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2650) (Sat.Literal.pos 2649) (Sat.Literal.pos 5) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation0 5 (assignment s)
    (Sat.Literal.pos 2650) (Sat.Literal.pos 2649) (Sat.Literal.pos 5) (Sat.Literal.pos 6) (positive_of_descriptor s 2650 (.lex permutation0 5) (by rfl)) (lex_0_5_prefix s) (positive_select s 5) (lex_0_5_image s)

theorem lex_0_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2649), (Sat.Literal.pos 5), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation0 5 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2649) (Sat.Literal.pos 5) (Sat.Literal.pos 6) (lex_0_5_prefix s) (positive_select s 5) (lex_0_5_image s)

theorem lex_0_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2650), (Sat.Literal.pos 2649)] :=
  (lex_0_5_gate s).prop _ (List.Mem.head _)

theorem lex_0_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2650), (Sat.Literal.neg 5), (Sat.Literal.pos 6)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2650), (Sat.Literal.pos 5), (Sat.Literal.neg 6)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2649), (Sat.Literal.neg 5), (Sat.Literal.neg 6), (Sat.Literal.pos 2650)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2649), (Sat.Literal.pos 5), (Sat.Literal.pos 6), (Sat.Literal.pos 2650)] :=
  (lex_0_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2650) = lexBefore s permutation0 2 := by
  exact (positive_lex_of_descriptor s 2650 permutation0 5 (by rfl)).trans ((lex_skipped s permutation0 2 5 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 3 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation0 2) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation0 2 by rw [image0_eq]; rfl))

theorem lex_0_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2651) (Sat.Literal.pos 2650) (Sat.Literal.pos 2) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation0 2 (assignment s)
    (Sat.Literal.pos 2651) (Sat.Literal.pos 2650) (Sat.Literal.pos 2) (Sat.Literal.pos 1) (positive_of_descriptor s 2651 (.lex permutation0 2) (by rfl)) (lex_0_2_prefix s) (positive_select s 2) (lex_0_2_image s)

theorem lex_0_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2650), (Sat.Literal.pos 2), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation0 2 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2650) (Sat.Literal.pos 2) (Sat.Literal.pos 1) (lex_0_2_prefix s) (positive_select s 2) (lex_0_2_image s)

theorem lex_0_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2651), (Sat.Literal.pos 2650)] :=
  (lex_0_2_gate s).prop _ (List.Mem.head _)

theorem lex_0_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2651), (Sat.Literal.neg 2), (Sat.Literal.pos 1)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2651), (Sat.Literal.pos 2), (Sat.Literal.neg 1)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2650), (Sat.Literal.neg 2), (Sat.Literal.neg 1), (Sat.Literal.pos 2651)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2650), (Sat.Literal.pos 2), (Sat.Literal.pos 1), (Sat.Literal.pos 2651)] :=
  (lex_0_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2651) = lexBefore s permutation0 1 := by
  exact (positive_lex_of_descriptor s 2651 permutation0 2 (by rfl)).trans ((lex_skipped s permutation0 1 2 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation0 1) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation0 1 by rw [image0_eq]; rfl))

theorem lex_0_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2652) (Sat.Literal.pos 2651) (Sat.Literal.pos 1) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation0 1 (assignment s)
    (Sat.Literal.pos 2652) (Sat.Literal.pos 2651) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (positive_of_descriptor s 2652 (.lex permutation0 1) (by rfl)) (lex_0_1_prefix s) (positive_select s 1) (lex_0_1_image s)

theorem lex_0_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2651), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation0 1 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2651) (Sat.Literal.pos 1) (Sat.Literal.pos 2) (lex_0_1_prefix s) (positive_select s 1) (lex_0_1_image s)

theorem lex_0_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2652), (Sat.Literal.pos 2651)] :=
  (lex_0_1_gate s).prop _ (List.Mem.head _)

theorem lex_0_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2652), (Sat.Literal.neg 1), (Sat.Literal.pos 2)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2652), (Sat.Literal.pos 1), (Sat.Literal.neg 2)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2651), (Sat.Literal.neg 1), (Sat.Literal.neg 2), (Sat.Literal.pos 2652)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2651), (Sat.Literal.pos 1), (Sat.Literal.pos 2), (Sat.Literal.pos 2652)] :=
  (lex_0_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation1 253 := by
  exact (negative_falsum s).trans ((lex_first s permutation1 253 (by intro j hj; rw [image1_eq]; exact fixedOnRange_spec image1 254 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_1_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation1 253) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation1 253 by rw [image1_eq]; rfl))

theorem lex_1_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2653) (Sat.Literal.neg 256) (Sat.Literal.pos 253) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation1 253 (assignment s)
    (Sat.Literal.pos 2653) (Sat.Literal.neg 256) (Sat.Literal.pos 253) (Sat.Literal.pos 251) (positive_of_descriptor s 2653 (.lex permutation1 253) (by rfl)) (lex_1_253_prefix s) (positive_select s 253) (lex_1_253_image s)

theorem lex_1_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 253), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation1 253 (hmax permutation1) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 253) (Sat.Literal.pos 251) (lex_1_253_prefix s) (positive_select s 253) (lex_1_253_image s)

theorem lex_1_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2653), (Sat.Literal.neg 256)] :=
  (lex_1_253_gate s).prop _ (List.Mem.head _)

theorem lex_1_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2653), (Sat.Literal.neg 253), (Sat.Literal.pos 251)] :=
  (lex_1_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2653), (Sat.Literal.pos 253), (Sat.Literal.neg 251)] :=
  (lex_1_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 253), (Sat.Literal.neg 251), (Sat.Literal.pos 2653)] :=
  (lex_1_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 253), (Sat.Literal.pos 251), (Sat.Literal.pos 2653)] :=
  (lex_1_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2653) = lexBefore s permutation1 252 := by
  exact (positive_lex_of_descriptor s 2653 permutation1 253 (by rfl)).trans ((lex_skipped s permutation1 252 253 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation1 252) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation1 252 by rw [image1_eq]; rfl))

theorem lex_1_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2654) (Sat.Literal.pos 2653) (Sat.Literal.pos 252) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation1 252 (assignment s)
    (Sat.Literal.pos 2654) (Sat.Literal.pos 2653) (Sat.Literal.pos 252) (Sat.Literal.pos 250) (positive_of_descriptor s 2654 (.lex permutation1 252) (by rfl)) (lex_1_252_prefix s) (positive_select s 252) (lex_1_252_image s)

theorem lex_1_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2653), (Sat.Literal.pos 252), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation1 252 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2653) (Sat.Literal.pos 252) (Sat.Literal.pos 250) (lex_1_252_prefix s) (positive_select s 252) (lex_1_252_image s)

theorem lex_1_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2654), (Sat.Literal.pos 2653)] :=
  (lex_1_252_gate s).prop _ (List.Mem.head _)

theorem lex_1_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2654), (Sat.Literal.neg 252), (Sat.Literal.pos 250)] :=
  (lex_1_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2654), (Sat.Literal.pos 252), (Sat.Literal.neg 250)] :=
  (lex_1_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2653), (Sat.Literal.neg 252), (Sat.Literal.neg 250), (Sat.Literal.pos 2654)] :=
  (lex_1_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2653), (Sat.Literal.pos 252), (Sat.Literal.pos 250), (Sat.Literal.pos 2654)] :=
  (lex_1_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2654) = lexBefore s permutation1 251 := by
  exact (positive_lex_of_descriptor s 2654 permutation1 252 (by rfl)).trans ((lex_skipped s permutation1 251 252 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation1 251) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation1 251 by rw [image1_eq]; rfl))

theorem lex_1_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2655) (Sat.Literal.pos 2654) (Sat.Literal.pos 251) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation1 251 (assignment s)
    (Sat.Literal.pos 2655) (Sat.Literal.pos 2654) (Sat.Literal.pos 251) (Sat.Literal.pos 253) (positive_of_descriptor s 2655 (.lex permutation1 251) (by rfl)) (lex_1_251_prefix s) (positive_select s 251) (lex_1_251_image s)

theorem lex_1_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2654), (Sat.Literal.pos 251), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation1 251 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2654) (Sat.Literal.pos 251) (Sat.Literal.pos 253) (lex_1_251_prefix s) (positive_select s 251) (lex_1_251_image s)

theorem lex_1_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2655), (Sat.Literal.pos 2654)] :=
  (lex_1_251_gate s).prop _ (List.Mem.head _)

theorem lex_1_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2655), (Sat.Literal.neg 251), (Sat.Literal.pos 253)] :=
  (lex_1_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2655), (Sat.Literal.pos 251), (Sat.Literal.neg 253)] :=
  (lex_1_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2654), (Sat.Literal.neg 251), (Sat.Literal.neg 253), (Sat.Literal.pos 2655)] :=
  (lex_1_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2654), (Sat.Literal.pos 251), (Sat.Literal.pos 253), (Sat.Literal.pos 2655)] :=
  (lex_1_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2655) = lexBefore s permutation1 250 := by
  exact (positive_lex_of_descriptor s 2655 permutation1 251 (by rfl)).trans ((lex_skipped s permutation1 250 251 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation1 250) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation1 250 by rw [image1_eq]; rfl))

theorem lex_1_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2656) (Sat.Literal.pos 2655) (Sat.Literal.pos 250) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation1 250 (assignment s)
    (Sat.Literal.pos 2656) (Sat.Literal.pos 2655) (Sat.Literal.pos 250) (Sat.Literal.pos 252) (positive_of_descriptor s 2656 (.lex permutation1 250) (by rfl)) (lex_1_250_prefix s) (positive_select s 250) (lex_1_250_image s)

theorem lex_1_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2655), (Sat.Literal.pos 250), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation1 250 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2655) (Sat.Literal.pos 250) (Sat.Literal.pos 252) (lex_1_250_prefix s) (positive_select s 250) (lex_1_250_image s)

theorem lex_1_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2656), (Sat.Literal.pos 2655)] :=
  (lex_1_250_gate s).prop _ (List.Mem.head _)

theorem lex_1_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2656), (Sat.Literal.neg 250), (Sat.Literal.pos 252)] :=
  (lex_1_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2656), (Sat.Literal.pos 250), (Sat.Literal.neg 252)] :=
  (lex_1_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2655), (Sat.Literal.neg 250), (Sat.Literal.neg 252), (Sat.Literal.pos 2656)] :=
  (lex_1_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2655), (Sat.Literal.pos 250), (Sat.Literal.pos 252), (Sat.Literal.pos 2656)] :=
  (lex_1_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2656) = lexBefore s permutation1 245 := by
  exact (positive_lex_of_descriptor s 2656 permutation1 250 (by rfl)).trans ((lex_skipped s permutation1 245 250 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 246 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation1 245) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation1 245 by rw [image1_eq]; rfl))

theorem lex_1_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2657) (Sat.Literal.pos 2656) (Sat.Literal.pos 245) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation1 245 (assignment s)
    (Sat.Literal.pos 2657) (Sat.Literal.pos 2656) (Sat.Literal.pos 245) (Sat.Literal.pos 243) (positive_of_descriptor s 2657 (.lex permutation1 245) (by rfl)) (lex_1_245_prefix s) (positive_select s 245) (lex_1_245_image s)

theorem lex_1_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2656), (Sat.Literal.pos 245), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation1 245 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2656) (Sat.Literal.pos 245) (Sat.Literal.pos 243) (lex_1_245_prefix s) (positive_select s 245) (lex_1_245_image s)

theorem lex_1_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2657), (Sat.Literal.pos 2656)] :=
  (lex_1_245_gate s).prop _ (List.Mem.head _)

theorem lex_1_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2657), (Sat.Literal.neg 245), (Sat.Literal.pos 243)] :=
  (lex_1_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2657), (Sat.Literal.pos 245), (Sat.Literal.neg 243)] :=
  (lex_1_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2656), (Sat.Literal.neg 245), (Sat.Literal.neg 243), (Sat.Literal.pos 2657)] :=
  (lex_1_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2656), (Sat.Literal.pos 245), (Sat.Literal.pos 243), (Sat.Literal.pos 2657)] :=
  (lex_1_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2657) = lexBefore s permutation1 244 := by
  exact (positive_lex_of_descriptor s 2657 permutation1 245 (by rfl)).trans ((lex_skipped s permutation1 244 245 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation1 244) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation1 244 by rw [image1_eq]; rfl))

theorem lex_1_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2658) (Sat.Literal.pos 2657) (Sat.Literal.pos 244) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation1 244 (assignment s)
    (Sat.Literal.pos 2658) (Sat.Literal.pos 2657) (Sat.Literal.pos 244) (Sat.Literal.pos 242) (positive_of_descriptor s 2658 (.lex permutation1 244) (by rfl)) (lex_1_244_prefix s) (positive_select s 244) (lex_1_244_image s)

theorem lex_1_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2657), (Sat.Literal.pos 244), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation1 244 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2657) (Sat.Literal.pos 244) (Sat.Literal.pos 242) (lex_1_244_prefix s) (positive_select s 244) (lex_1_244_image s)

theorem lex_1_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2658), (Sat.Literal.pos 2657)] :=
  (lex_1_244_gate s).prop _ (List.Mem.head _)

theorem lex_1_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2658), (Sat.Literal.neg 244), (Sat.Literal.pos 242)] :=
  (lex_1_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2658), (Sat.Literal.pos 244), (Sat.Literal.neg 242)] :=
  (lex_1_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2657), (Sat.Literal.neg 244), (Sat.Literal.neg 242), (Sat.Literal.pos 2658)] :=
  (lex_1_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2657), (Sat.Literal.pos 244), (Sat.Literal.pos 242), (Sat.Literal.pos 2658)] :=
  (lex_1_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2658) = lexBefore s permutation1 243 := by
  exact (positive_lex_of_descriptor s 2658 permutation1 244 (by rfl)).trans ((lex_skipped s permutation1 243 244 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation1 243) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation1 243 by rw [image1_eq]; rfl))

theorem lex_1_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2659) (Sat.Literal.pos 2658) (Sat.Literal.pos 243) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation1 243 (assignment s)
    (Sat.Literal.pos 2659) (Sat.Literal.pos 2658) (Sat.Literal.pos 243) (Sat.Literal.pos 245) (positive_of_descriptor s 2659 (.lex permutation1 243) (by rfl)) (lex_1_243_prefix s) (positive_select s 243) (lex_1_243_image s)

theorem lex_1_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2658), (Sat.Literal.pos 243), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation1 243 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2658) (Sat.Literal.pos 243) (Sat.Literal.pos 245) (lex_1_243_prefix s) (positive_select s 243) (lex_1_243_image s)

theorem lex_1_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2659), (Sat.Literal.pos 2658)] :=
  (lex_1_243_gate s).prop _ (List.Mem.head _)

theorem lex_1_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2659), (Sat.Literal.neg 243), (Sat.Literal.pos 245)] :=
  (lex_1_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2659), (Sat.Literal.pos 243), (Sat.Literal.neg 245)] :=
  (lex_1_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2658), (Sat.Literal.neg 243), (Sat.Literal.neg 245), (Sat.Literal.pos 2659)] :=
  (lex_1_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2658), (Sat.Literal.pos 243), (Sat.Literal.pos 245), (Sat.Literal.pos 2659)] :=
  (lex_1_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2659) = lexBefore s permutation1 242 := by
  exact (positive_lex_of_descriptor s 2659 permutation1 243 (by rfl)).trans ((lex_skipped s permutation1 242 243 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation1 242) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation1 242 by rw [image1_eq]; rfl))

theorem lex_1_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2660) (Sat.Literal.pos 2659) (Sat.Literal.pos 242) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation1 242 (assignment s)
    (Sat.Literal.pos 2660) (Sat.Literal.pos 2659) (Sat.Literal.pos 242) (Sat.Literal.pos 244) (positive_of_descriptor s 2660 (.lex permutation1 242) (by rfl)) (lex_1_242_prefix s) (positive_select s 242) (lex_1_242_image s)

theorem lex_1_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2659), (Sat.Literal.pos 242), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation1 242 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2659) (Sat.Literal.pos 242) (Sat.Literal.pos 244) (lex_1_242_prefix s) (positive_select s 242) (lex_1_242_image s)

theorem lex_1_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2660), (Sat.Literal.pos 2659)] :=
  (lex_1_242_gate s).prop _ (List.Mem.head _)

theorem lex_1_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2660), (Sat.Literal.neg 242), (Sat.Literal.pos 244)] :=
  (lex_1_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2660), (Sat.Literal.pos 242), (Sat.Literal.neg 244)] :=
  (lex_1_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2659), (Sat.Literal.neg 242), (Sat.Literal.neg 244), (Sat.Literal.pos 2660)] :=
  (lex_1_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2659), (Sat.Literal.pos 242), (Sat.Literal.pos 244), (Sat.Literal.pos 2660)] :=
  (lex_1_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2660) = lexBefore s permutation1 237 := by
  exact (positive_lex_of_descriptor s 2660 permutation1 242 (by rfl)).trans ((lex_skipped s permutation1 237 242 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 238 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation1 237) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation1 237 by rw [image1_eq]; rfl))

theorem lex_1_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2661) (Sat.Literal.pos 2660) (Sat.Literal.pos 237) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation1 237 (assignment s)
    (Sat.Literal.pos 2661) (Sat.Literal.pos 2660) (Sat.Literal.pos 237) (Sat.Literal.pos 235) (positive_of_descriptor s 2661 (.lex permutation1 237) (by rfl)) (lex_1_237_prefix s) (positive_select s 237) (lex_1_237_image s)

theorem lex_1_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2660), (Sat.Literal.pos 237), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation1 237 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2660) (Sat.Literal.pos 237) (Sat.Literal.pos 235) (lex_1_237_prefix s) (positive_select s 237) (lex_1_237_image s)

theorem lex_1_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2661), (Sat.Literal.pos 2660)] :=
  (lex_1_237_gate s).prop _ (List.Mem.head _)

theorem lex_1_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2661), (Sat.Literal.neg 237), (Sat.Literal.pos 235)] :=
  (lex_1_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2661), (Sat.Literal.pos 237), (Sat.Literal.neg 235)] :=
  (lex_1_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2660), (Sat.Literal.neg 237), (Sat.Literal.neg 235), (Sat.Literal.pos 2661)] :=
  (lex_1_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2660), (Sat.Literal.pos 237), (Sat.Literal.pos 235), (Sat.Literal.pos 2661)] :=
  (lex_1_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2661) = lexBefore s permutation1 236 := by
  exact (positive_lex_of_descriptor s 2661 permutation1 237 (by rfl)).trans ((lex_skipped s permutation1 236 237 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation1 236) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation1 236 by rw [image1_eq]; rfl))

theorem lex_1_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2662) (Sat.Literal.pos 2661) (Sat.Literal.pos 236) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation1 236 (assignment s)
    (Sat.Literal.pos 2662) (Sat.Literal.pos 2661) (Sat.Literal.pos 236) (Sat.Literal.pos 234) (positive_of_descriptor s 2662 (.lex permutation1 236) (by rfl)) (lex_1_236_prefix s) (positive_select s 236) (lex_1_236_image s)

theorem lex_1_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2661), (Sat.Literal.pos 236), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation1 236 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2661) (Sat.Literal.pos 236) (Sat.Literal.pos 234) (lex_1_236_prefix s) (positive_select s 236) (lex_1_236_image s)

theorem lex_1_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2662), (Sat.Literal.pos 2661)] :=
  (lex_1_236_gate s).prop _ (List.Mem.head _)

theorem lex_1_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2662), (Sat.Literal.neg 236), (Sat.Literal.pos 234)] :=
  (lex_1_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2662), (Sat.Literal.pos 236), (Sat.Literal.neg 234)] :=
  (lex_1_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2661), (Sat.Literal.neg 236), (Sat.Literal.neg 234), (Sat.Literal.pos 2662)] :=
  (lex_1_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2661), (Sat.Literal.pos 236), (Sat.Literal.pos 234), (Sat.Literal.pos 2662)] :=
  (lex_1_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2662) = lexBefore s permutation1 235 := by
  exact (positive_lex_of_descriptor s 2662 permutation1 236 (by rfl)).trans ((lex_skipped s permutation1 235 236 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation1 235) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation1 235 by rw [image1_eq]; rfl))

theorem lex_1_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2663) (Sat.Literal.pos 2662) (Sat.Literal.pos 235) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation1 235 (assignment s)
    (Sat.Literal.pos 2663) (Sat.Literal.pos 2662) (Sat.Literal.pos 235) (Sat.Literal.pos 237) (positive_of_descriptor s 2663 (.lex permutation1 235) (by rfl)) (lex_1_235_prefix s) (positive_select s 235) (lex_1_235_image s)

theorem lex_1_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2662), (Sat.Literal.pos 235), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation1 235 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2662) (Sat.Literal.pos 235) (Sat.Literal.pos 237) (lex_1_235_prefix s) (positive_select s 235) (lex_1_235_image s)

theorem lex_1_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2663), (Sat.Literal.pos 2662)] :=
  (lex_1_235_gate s).prop _ (List.Mem.head _)

theorem lex_1_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2663), (Sat.Literal.neg 235), (Sat.Literal.pos 237)] :=
  (lex_1_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2663), (Sat.Literal.pos 235), (Sat.Literal.neg 237)] :=
  (lex_1_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2662), (Sat.Literal.neg 235), (Sat.Literal.neg 237), (Sat.Literal.pos 2663)] :=
  (lex_1_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2662), (Sat.Literal.pos 235), (Sat.Literal.pos 237), (Sat.Literal.pos 2663)] :=
  (lex_1_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2663) = lexBefore s permutation1 234 := by
  exact (positive_lex_of_descriptor s 2663 permutation1 235 (by rfl)).trans ((lex_skipped s permutation1 234 235 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation1 234) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation1 234 by rw [image1_eq]; rfl))

theorem lex_1_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2664) (Sat.Literal.pos 2663) (Sat.Literal.pos 234) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation1 234 (assignment s)
    (Sat.Literal.pos 2664) (Sat.Literal.pos 2663) (Sat.Literal.pos 234) (Sat.Literal.pos 236) (positive_of_descriptor s 2664 (.lex permutation1 234) (by rfl)) (lex_1_234_prefix s) (positive_select s 234) (lex_1_234_image s)

theorem lex_1_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2663), (Sat.Literal.pos 234), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation1 234 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2663) (Sat.Literal.pos 234) (Sat.Literal.pos 236) (lex_1_234_prefix s) (positive_select s 234) (lex_1_234_image s)

theorem lex_1_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2664), (Sat.Literal.pos 2663)] :=
  (lex_1_234_gate s).prop _ (List.Mem.head _)

theorem lex_1_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2664), (Sat.Literal.neg 234), (Sat.Literal.pos 236)] :=
  (lex_1_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2664), (Sat.Literal.pos 234), (Sat.Literal.neg 236)] :=
  (lex_1_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2663), (Sat.Literal.neg 234), (Sat.Literal.neg 236), (Sat.Literal.pos 2664)] :=
  (lex_1_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2663), (Sat.Literal.pos 234), (Sat.Literal.pos 236), (Sat.Literal.pos 2664)] :=
  (lex_1_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2664) = lexBefore s permutation1 229 := by
  exact (positive_lex_of_descriptor s 2664 permutation1 234 (by rfl)).trans ((lex_skipped s permutation1 229 234 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 230 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation1 229) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation1 229 by rw [image1_eq]; rfl))

theorem lex_1_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2665) (Sat.Literal.pos 2664) (Sat.Literal.pos 229) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation1 229 (assignment s)
    (Sat.Literal.pos 2665) (Sat.Literal.pos 2664) (Sat.Literal.pos 229) (Sat.Literal.pos 227) (positive_of_descriptor s 2665 (.lex permutation1 229) (by rfl)) (lex_1_229_prefix s) (positive_select s 229) (lex_1_229_image s)

theorem lex_1_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2664), (Sat.Literal.pos 229), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation1 229 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2664) (Sat.Literal.pos 229) (Sat.Literal.pos 227) (lex_1_229_prefix s) (positive_select s 229) (lex_1_229_image s)

theorem lex_1_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2665), (Sat.Literal.pos 2664)] :=
  (lex_1_229_gate s).prop _ (List.Mem.head _)

theorem lex_1_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2665), (Sat.Literal.neg 229), (Sat.Literal.pos 227)] :=
  (lex_1_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2665), (Sat.Literal.pos 229), (Sat.Literal.neg 227)] :=
  (lex_1_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2664), (Sat.Literal.neg 229), (Sat.Literal.neg 227), (Sat.Literal.pos 2665)] :=
  (lex_1_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2664), (Sat.Literal.pos 229), (Sat.Literal.pos 227), (Sat.Literal.pos 2665)] :=
  (lex_1_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2665) = lexBefore s permutation1 228 := by
  exact (positive_lex_of_descriptor s 2665 permutation1 229 (by rfl)).trans ((lex_skipped s permutation1 228 229 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation1 228) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation1 228 by rw [image1_eq]; rfl))

theorem lex_1_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2666) (Sat.Literal.pos 2665) (Sat.Literal.pos 228) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation1 228 (assignment s)
    (Sat.Literal.pos 2666) (Sat.Literal.pos 2665) (Sat.Literal.pos 228) (Sat.Literal.pos 226) (positive_of_descriptor s 2666 (.lex permutation1 228) (by rfl)) (lex_1_228_prefix s) (positive_select s 228) (lex_1_228_image s)

theorem lex_1_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2665), (Sat.Literal.pos 228), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation1 228 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2665) (Sat.Literal.pos 228) (Sat.Literal.pos 226) (lex_1_228_prefix s) (positive_select s 228) (lex_1_228_image s)

theorem lex_1_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2666), (Sat.Literal.pos 2665)] :=
  (lex_1_228_gate s).prop _ (List.Mem.head _)

theorem lex_1_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2666), (Sat.Literal.neg 228), (Sat.Literal.pos 226)] :=
  (lex_1_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2666), (Sat.Literal.pos 228), (Sat.Literal.neg 226)] :=
  (lex_1_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2665), (Sat.Literal.neg 228), (Sat.Literal.neg 226), (Sat.Literal.pos 2666)] :=
  (lex_1_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2665), (Sat.Literal.pos 228), (Sat.Literal.pos 226), (Sat.Literal.pos 2666)] :=
  (lex_1_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2666) = lexBefore s permutation1 227 := by
  exact (positive_lex_of_descriptor s 2666 permutation1 228 (by rfl)).trans ((lex_skipped s permutation1 227 228 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation1 227) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation1 227 by rw [image1_eq]; rfl))

theorem lex_1_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2667) (Sat.Literal.pos 2666) (Sat.Literal.pos 227) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation1 227 (assignment s)
    (Sat.Literal.pos 2667) (Sat.Literal.pos 2666) (Sat.Literal.pos 227) (Sat.Literal.pos 229) (positive_of_descriptor s 2667 (.lex permutation1 227) (by rfl)) (lex_1_227_prefix s) (positive_select s 227) (lex_1_227_image s)

theorem lex_1_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2666), (Sat.Literal.pos 227), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation1 227 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2666) (Sat.Literal.pos 227) (Sat.Literal.pos 229) (lex_1_227_prefix s) (positive_select s 227) (lex_1_227_image s)

theorem lex_1_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2667), (Sat.Literal.pos 2666)] :=
  (lex_1_227_gate s).prop _ (List.Mem.head _)

theorem lex_1_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2667), (Sat.Literal.neg 227), (Sat.Literal.pos 229)] :=
  (lex_1_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2667), (Sat.Literal.pos 227), (Sat.Literal.neg 229)] :=
  (lex_1_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2666), (Sat.Literal.neg 227), (Sat.Literal.neg 229), (Sat.Literal.pos 2667)] :=
  (lex_1_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2666), (Sat.Literal.pos 227), (Sat.Literal.pos 229), (Sat.Literal.pos 2667)] :=
  (lex_1_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2667) = lexBefore s permutation1 226 := by
  exact (positive_lex_of_descriptor s 2667 permutation1 227 (by rfl)).trans ((lex_skipped s permutation1 226 227 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation1 226) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation1 226 by rw [image1_eq]; rfl))

theorem lex_1_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2668) (Sat.Literal.pos 2667) (Sat.Literal.pos 226) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation1 226 (assignment s)
    (Sat.Literal.pos 2668) (Sat.Literal.pos 2667) (Sat.Literal.pos 226) (Sat.Literal.pos 228) (positive_of_descriptor s 2668 (.lex permutation1 226) (by rfl)) (lex_1_226_prefix s) (positive_select s 226) (lex_1_226_image s)

theorem lex_1_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2667), (Sat.Literal.pos 226), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation1 226 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2667) (Sat.Literal.pos 226) (Sat.Literal.pos 228) (lex_1_226_prefix s) (positive_select s 226) (lex_1_226_image s)

theorem lex_1_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2668), (Sat.Literal.pos 2667)] :=
  (lex_1_226_gate s).prop _ (List.Mem.head _)

theorem lex_1_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2668), (Sat.Literal.neg 226), (Sat.Literal.pos 228)] :=
  (lex_1_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2668), (Sat.Literal.pos 226), (Sat.Literal.neg 228)] :=
  (lex_1_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2667), (Sat.Literal.neg 226), (Sat.Literal.neg 228), (Sat.Literal.pos 2668)] :=
  (lex_1_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2667), (Sat.Literal.pos 226), (Sat.Literal.pos 228), (Sat.Literal.pos 2668)] :=
  (lex_1_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2668) = lexBefore s permutation1 221 := by
  exact (positive_lex_of_descriptor s 2668 permutation1 226 (by rfl)).trans ((lex_skipped s permutation1 221 226 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 222 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation1 221) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation1 221 by rw [image1_eq]; rfl))

theorem lex_1_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2669) (Sat.Literal.pos 2668) (Sat.Literal.pos 221) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation1 221 (assignment s)
    (Sat.Literal.pos 2669) (Sat.Literal.pos 2668) (Sat.Literal.pos 221) (Sat.Literal.pos 219) (positive_of_descriptor s 2669 (.lex permutation1 221) (by rfl)) (lex_1_221_prefix s) (positive_select s 221) (lex_1_221_image s)

theorem lex_1_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2668), (Sat.Literal.pos 221), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation1 221 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2668) (Sat.Literal.pos 221) (Sat.Literal.pos 219) (lex_1_221_prefix s) (positive_select s 221) (lex_1_221_image s)

theorem lex_1_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2669), (Sat.Literal.pos 2668)] :=
  (lex_1_221_gate s).prop _ (List.Mem.head _)

theorem lex_1_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2669), (Sat.Literal.neg 221), (Sat.Literal.pos 219)] :=
  (lex_1_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2669), (Sat.Literal.pos 221), (Sat.Literal.neg 219)] :=
  (lex_1_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2668), (Sat.Literal.neg 221), (Sat.Literal.neg 219), (Sat.Literal.pos 2669)] :=
  (lex_1_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2668), (Sat.Literal.pos 221), (Sat.Literal.pos 219), (Sat.Literal.pos 2669)] :=
  (lex_1_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2669) = lexBefore s permutation1 220 := by
  exact (positive_lex_of_descriptor s 2669 permutation1 221 (by rfl)).trans ((lex_skipped s permutation1 220 221 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation1 220) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation1 220 by rw [image1_eq]; rfl))

theorem lex_1_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2670) (Sat.Literal.pos 2669) (Sat.Literal.pos 220) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation1 220 (assignment s)
    (Sat.Literal.pos 2670) (Sat.Literal.pos 2669) (Sat.Literal.pos 220) (Sat.Literal.pos 218) (positive_of_descriptor s 2670 (.lex permutation1 220) (by rfl)) (lex_1_220_prefix s) (positive_select s 220) (lex_1_220_image s)

theorem lex_1_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2669), (Sat.Literal.pos 220), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation1 220 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2669) (Sat.Literal.pos 220) (Sat.Literal.pos 218) (lex_1_220_prefix s) (positive_select s 220) (lex_1_220_image s)

theorem lex_1_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2670), (Sat.Literal.pos 2669)] :=
  (lex_1_220_gate s).prop _ (List.Mem.head _)

theorem lex_1_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2670), (Sat.Literal.neg 220), (Sat.Literal.pos 218)] :=
  (lex_1_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2670), (Sat.Literal.pos 220), (Sat.Literal.neg 218)] :=
  (lex_1_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2669), (Sat.Literal.neg 220), (Sat.Literal.neg 218), (Sat.Literal.pos 2670)] :=
  (lex_1_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2669), (Sat.Literal.pos 220), (Sat.Literal.pos 218), (Sat.Literal.pos 2670)] :=
  (lex_1_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2670) = lexBefore s permutation1 219 := by
  exact (positive_lex_of_descriptor s 2670 permutation1 220 (by rfl)).trans ((lex_skipped s permutation1 219 220 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation1 219) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation1 219 by rw [image1_eq]; rfl))

theorem lex_1_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2671) (Sat.Literal.pos 2670) (Sat.Literal.pos 219) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation1 219 (assignment s)
    (Sat.Literal.pos 2671) (Sat.Literal.pos 2670) (Sat.Literal.pos 219) (Sat.Literal.pos 221) (positive_of_descriptor s 2671 (.lex permutation1 219) (by rfl)) (lex_1_219_prefix s) (positive_select s 219) (lex_1_219_image s)

theorem lex_1_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2670), (Sat.Literal.pos 219), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation1 219 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2670) (Sat.Literal.pos 219) (Sat.Literal.pos 221) (lex_1_219_prefix s) (positive_select s 219) (lex_1_219_image s)

theorem lex_1_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2671), (Sat.Literal.pos 2670)] :=
  (lex_1_219_gate s).prop _ (List.Mem.head _)

theorem lex_1_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2671), (Sat.Literal.neg 219), (Sat.Literal.pos 221)] :=
  (lex_1_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2671), (Sat.Literal.pos 219), (Sat.Literal.neg 221)] :=
  (lex_1_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2670), (Sat.Literal.neg 219), (Sat.Literal.neg 221), (Sat.Literal.pos 2671)] :=
  (lex_1_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2670), (Sat.Literal.pos 219), (Sat.Literal.pos 221), (Sat.Literal.pos 2671)] :=
  (lex_1_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2671) = lexBefore s permutation1 218 := by
  exact (positive_lex_of_descriptor s 2671 permutation1 219 (by rfl)).trans ((lex_skipped s permutation1 218 219 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation1 218) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation1 218 by rw [image1_eq]; rfl))

theorem lex_1_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2672) (Sat.Literal.pos 2671) (Sat.Literal.pos 218) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation1 218 (assignment s)
    (Sat.Literal.pos 2672) (Sat.Literal.pos 2671) (Sat.Literal.pos 218) (Sat.Literal.pos 220) (positive_of_descriptor s 2672 (.lex permutation1 218) (by rfl)) (lex_1_218_prefix s) (positive_select s 218) (lex_1_218_image s)

theorem lex_1_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2671), (Sat.Literal.pos 218), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation1 218 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2671) (Sat.Literal.pos 218) (Sat.Literal.pos 220) (lex_1_218_prefix s) (positive_select s 218) (lex_1_218_image s)

theorem lex_1_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2672), (Sat.Literal.pos 2671)] :=
  (lex_1_218_gate s).prop _ (List.Mem.head _)

theorem lex_1_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2672), (Sat.Literal.neg 218), (Sat.Literal.pos 220)] :=
  (lex_1_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2672), (Sat.Literal.pos 218), (Sat.Literal.neg 220)] :=
  (lex_1_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2671), (Sat.Literal.neg 218), (Sat.Literal.neg 220), (Sat.Literal.pos 2672)] :=
  (lex_1_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2671), (Sat.Literal.pos 218), (Sat.Literal.pos 220), (Sat.Literal.pos 2672)] :=
  (lex_1_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2672) = lexBefore s permutation1 213 := by
  exact (positive_lex_of_descriptor s 2672 permutation1 218 (by rfl)).trans ((lex_skipped s permutation1 213 218 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 214 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation1 213) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation1 213 by rw [image1_eq]; rfl))

theorem lex_1_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2673) (Sat.Literal.pos 2672) (Sat.Literal.pos 213) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation1 213 (assignment s)
    (Sat.Literal.pos 2673) (Sat.Literal.pos 2672) (Sat.Literal.pos 213) (Sat.Literal.pos 211) (positive_of_descriptor s 2673 (.lex permutation1 213) (by rfl)) (lex_1_213_prefix s) (positive_select s 213) (lex_1_213_image s)

theorem lex_1_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2672), (Sat.Literal.pos 213), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation1 213 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2672) (Sat.Literal.pos 213) (Sat.Literal.pos 211) (lex_1_213_prefix s) (positive_select s 213) (lex_1_213_image s)

theorem lex_1_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2673), (Sat.Literal.pos 2672)] :=
  (lex_1_213_gate s).prop _ (List.Mem.head _)

theorem lex_1_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2673), (Sat.Literal.neg 213), (Sat.Literal.pos 211)] :=
  (lex_1_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2673), (Sat.Literal.pos 213), (Sat.Literal.neg 211)] :=
  (lex_1_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2672), (Sat.Literal.neg 213), (Sat.Literal.neg 211), (Sat.Literal.pos 2673)] :=
  (lex_1_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2672), (Sat.Literal.pos 213), (Sat.Literal.pos 211), (Sat.Literal.pos 2673)] :=
  (lex_1_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2673) = lexBefore s permutation1 212 := by
  exact (positive_lex_of_descriptor s 2673 permutation1 213 (by rfl)).trans ((lex_skipped s permutation1 212 213 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation1 212) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation1 212 by rw [image1_eq]; rfl))

theorem lex_1_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2674) (Sat.Literal.pos 2673) (Sat.Literal.pos 212) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation1 212 (assignment s)
    (Sat.Literal.pos 2674) (Sat.Literal.pos 2673) (Sat.Literal.pos 212) (Sat.Literal.pos 210) (positive_of_descriptor s 2674 (.lex permutation1 212) (by rfl)) (lex_1_212_prefix s) (positive_select s 212) (lex_1_212_image s)

theorem lex_1_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2673), (Sat.Literal.pos 212), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation1 212 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2673) (Sat.Literal.pos 212) (Sat.Literal.pos 210) (lex_1_212_prefix s) (positive_select s 212) (lex_1_212_image s)

theorem lex_1_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2674), (Sat.Literal.pos 2673)] :=
  (lex_1_212_gate s).prop _ (List.Mem.head _)

theorem lex_1_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2674), (Sat.Literal.neg 212), (Sat.Literal.pos 210)] :=
  (lex_1_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2674), (Sat.Literal.pos 212), (Sat.Literal.neg 210)] :=
  (lex_1_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2673), (Sat.Literal.neg 212), (Sat.Literal.neg 210), (Sat.Literal.pos 2674)] :=
  (lex_1_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2673), (Sat.Literal.pos 212), (Sat.Literal.pos 210), (Sat.Literal.pos 2674)] :=
  (lex_1_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2674) = lexBefore s permutation1 211 := by
  exact (positive_lex_of_descriptor s 2674 permutation1 212 (by rfl)).trans ((lex_skipped s permutation1 211 212 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation1 211) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation1 211 by rw [image1_eq]; rfl))

theorem lex_1_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2675) (Sat.Literal.pos 2674) (Sat.Literal.pos 211) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation1 211 (assignment s)
    (Sat.Literal.pos 2675) (Sat.Literal.pos 2674) (Sat.Literal.pos 211) (Sat.Literal.pos 213) (positive_of_descriptor s 2675 (.lex permutation1 211) (by rfl)) (lex_1_211_prefix s) (positive_select s 211) (lex_1_211_image s)

theorem lex_1_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2674), (Sat.Literal.pos 211), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation1 211 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2674) (Sat.Literal.pos 211) (Sat.Literal.pos 213) (lex_1_211_prefix s) (positive_select s 211) (lex_1_211_image s)

theorem lex_1_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2675), (Sat.Literal.pos 2674)] :=
  (lex_1_211_gate s).prop _ (List.Mem.head _)

theorem lex_1_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2675), (Sat.Literal.neg 211), (Sat.Literal.pos 213)] :=
  (lex_1_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2675), (Sat.Literal.pos 211), (Sat.Literal.neg 213)] :=
  (lex_1_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2674), (Sat.Literal.neg 211), (Sat.Literal.neg 213), (Sat.Literal.pos 2675)] :=
  (lex_1_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2674), (Sat.Literal.pos 211), (Sat.Literal.pos 213), (Sat.Literal.pos 2675)] :=
  (lex_1_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2675) = lexBefore s permutation1 210 := by
  exact (positive_lex_of_descriptor s 2675 permutation1 211 (by rfl)).trans ((lex_skipped s permutation1 210 211 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation1 210) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation1 210 by rw [image1_eq]; rfl))

theorem lex_1_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2676) (Sat.Literal.pos 2675) (Sat.Literal.pos 210) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation1 210 (assignment s)
    (Sat.Literal.pos 2676) (Sat.Literal.pos 2675) (Sat.Literal.pos 210) (Sat.Literal.pos 212) (positive_of_descriptor s 2676 (.lex permutation1 210) (by rfl)) (lex_1_210_prefix s) (positive_select s 210) (lex_1_210_image s)

theorem lex_1_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2675), (Sat.Literal.pos 210), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation1 210 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2675) (Sat.Literal.pos 210) (Sat.Literal.pos 212) (lex_1_210_prefix s) (positive_select s 210) (lex_1_210_image s)

theorem lex_1_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2676), (Sat.Literal.pos 2675)] :=
  (lex_1_210_gate s).prop _ (List.Mem.head _)

theorem lex_1_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2676), (Sat.Literal.neg 210), (Sat.Literal.pos 212)] :=
  (lex_1_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2676), (Sat.Literal.pos 210), (Sat.Literal.neg 212)] :=
  (lex_1_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2675), (Sat.Literal.neg 210), (Sat.Literal.neg 212), (Sat.Literal.pos 2676)] :=
  (lex_1_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2675), (Sat.Literal.pos 210), (Sat.Literal.pos 212), (Sat.Literal.pos 2676)] :=
  (lex_1_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2676) = lexBefore s permutation1 205 := by
  exact (positive_lex_of_descriptor s 2676 permutation1 210 (by rfl)).trans ((lex_skipped s permutation1 205 210 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 206 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation1 205) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation1 205 by rw [image1_eq]; rfl))

theorem lex_1_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2677) (Sat.Literal.pos 2676) (Sat.Literal.pos 205) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation1 205 (assignment s)
    (Sat.Literal.pos 2677) (Sat.Literal.pos 2676) (Sat.Literal.pos 205) (Sat.Literal.pos 203) (positive_of_descriptor s 2677 (.lex permutation1 205) (by rfl)) (lex_1_205_prefix s) (positive_select s 205) (lex_1_205_image s)

theorem lex_1_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2676), (Sat.Literal.pos 205), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation1 205 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2676) (Sat.Literal.pos 205) (Sat.Literal.pos 203) (lex_1_205_prefix s) (positive_select s 205) (lex_1_205_image s)

theorem lex_1_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2677), (Sat.Literal.pos 2676)] :=
  (lex_1_205_gate s).prop _ (List.Mem.head _)

theorem lex_1_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2677), (Sat.Literal.neg 205), (Sat.Literal.pos 203)] :=
  (lex_1_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2677), (Sat.Literal.pos 205), (Sat.Literal.neg 203)] :=
  (lex_1_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2676), (Sat.Literal.neg 205), (Sat.Literal.neg 203), (Sat.Literal.pos 2677)] :=
  (lex_1_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2676), (Sat.Literal.pos 205), (Sat.Literal.pos 203), (Sat.Literal.pos 2677)] :=
  (lex_1_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2677) = lexBefore s permutation1 204 := by
  exact (positive_lex_of_descriptor s 2677 permutation1 205 (by rfl)).trans ((lex_skipped s permutation1 204 205 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation1 204) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation1 204 by rw [image1_eq]; rfl))

theorem lex_1_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2678) (Sat.Literal.pos 2677) (Sat.Literal.pos 204) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation1 204 (assignment s)
    (Sat.Literal.pos 2678) (Sat.Literal.pos 2677) (Sat.Literal.pos 204) (Sat.Literal.pos 202) (positive_of_descriptor s 2678 (.lex permutation1 204) (by rfl)) (lex_1_204_prefix s) (positive_select s 204) (lex_1_204_image s)

theorem lex_1_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2677), (Sat.Literal.pos 204), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation1 204 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2677) (Sat.Literal.pos 204) (Sat.Literal.pos 202) (lex_1_204_prefix s) (positive_select s 204) (lex_1_204_image s)

theorem lex_1_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2678), (Sat.Literal.pos 2677)] :=
  (lex_1_204_gate s).prop _ (List.Mem.head _)

theorem lex_1_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2678), (Sat.Literal.neg 204), (Sat.Literal.pos 202)] :=
  (lex_1_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2678), (Sat.Literal.pos 204), (Sat.Literal.neg 202)] :=
  (lex_1_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2677), (Sat.Literal.neg 204), (Sat.Literal.neg 202), (Sat.Literal.pos 2678)] :=
  (lex_1_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2677), (Sat.Literal.pos 204), (Sat.Literal.pos 202), (Sat.Literal.pos 2678)] :=
  (lex_1_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2678) = lexBefore s permutation1 203 := by
  exact (positive_lex_of_descriptor s 2678 permutation1 204 (by rfl)).trans ((lex_skipped s permutation1 203 204 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation1 203) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation1 203 by rw [image1_eq]; rfl))

theorem lex_1_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2679) (Sat.Literal.pos 2678) (Sat.Literal.pos 203) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation1 203 (assignment s)
    (Sat.Literal.pos 2679) (Sat.Literal.pos 2678) (Sat.Literal.pos 203) (Sat.Literal.pos 205) (positive_of_descriptor s 2679 (.lex permutation1 203) (by rfl)) (lex_1_203_prefix s) (positive_select s 203) (lex_1_203_image s)

theorem lex_1_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2678), (Sat.Literal.pos 203), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation1 203 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2678) (Sat.Literal.pos 203) (Sat.Literal.pos 205) (lex_1_203_prefix s) (positive_select s 203) (lex_1_203_image s)

theorem lex_1_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2679), (Sat.Literal.pos 2678)] :=
  (lex_1_203_gate s).prop _ (List.Mem.head _)

theorem lex_1_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2679), (Sat.Literal.neg 203), (Sat.Literal.pos 205)] :=
  (lex_1_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2679), (Sat.Literal.pos 203), (Sat.Literal.neg 205)] :=
  (lex_1_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2678), (Sat.Literal.neg 203), (Sat.Literal.neg 205), (Sat.Literal.pos 2679)] :=
  (lex_1_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2678), (Sat.Literal.pos 203), (Sat.Literal.pos 205), (Sat.Literal.pos 2679)] :=
  (lex_1_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2679) = lexBefore s permutation1 202 := by
  exact (positive_lex_of_descriptor s 2679 permutation1 203 (by rfl)).trans ((lex_skipped s permutation1 202 203 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 204) = s (permuteMask permutation1 202) := by
  exact (positive_select s 204).trans (congrArg s (show (204 : Fin 256) = permuteMask permutation1 202 by rw [image1_eq]; rfl))

theorem lex_1_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2680) (Sat.Literal.pos 2679) (Sat.Literal.pos 202) (Sat.Literal.pos 204)) := by
  exact equality_gate s permutation1 202 (assignment s)
    (Sat.Literal.pos 2680) (Sat.Literal.pos 2679) (Sat.Literal.pos 202) (Sat.Literal.pos 204) (positive_of_descriptor s 2680 (.lex permutation1 202) (by rfl)) (lex_1_202_prefix s) (positive_select s 202) (lex_1_202_image s)

theorem lex_1_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2679), (Sat.Literal.pos 202), (Sat.Literal.neg 204)] := by
  exact comparison_gate s permutation1 202 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2679) (Sat.Literal.pos 202) (Sat.Literal.pos 204) (lex_1_202_prefix s) (positive_select s 202) (lex_1_202_image s)

theorem lex_1_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2680), (Sat.Literal.pos 2679)] :=
  (lex_1_202_gate s).prop _ (List.Mem.head _)

theorem lex_1_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2680), (Sat.Literal.neg 202), (Sat.Literal.pos 204)] :=
  (lex_1_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2680), (Sat.Literal.pos 202), (Sat.Literal.neg 204)] :=
  (lex_1_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2679), (Sat.Literal.neg 202), (Sat.Literal.neg 204), (Sat.Literal.pos 2680)] :=
  (lex_1_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2679), (Sat.Literal.pos 202), (Sat.Literal.pos 204), (Sat.Literal.pos 2680)] :=
  (lex_1_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2680) = lexBefore s permutation1 197 := by
  exact (positive_lex_of_descriptor s 2680 permutation1 202 (by rfl)).trans ((lex_skipped s permutation1 197 202 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 198 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation1 197) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation1 197 by rw [image1_eq]; rfl))

theorem lex_1_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2681) (Sat.Literal.pos 2680) (Sat.Literal.pos 197) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation1 197 (assignment s)
    (Sat.Literal.pos 2681) (Sat.Literal.pos 2680) (Sat.Literal.pos 197) (Sat.Literal.pos 195) (positive_of_descriptor s 2681 (.lex permutation1 197) (by rfl)) (lex_1_197_prefix s) (positive_select s 197) (lex_1_197_image s)

theorem lex_1_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2680), (Sat.Literal.pos 197), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation1 197 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2680) (Sat.Literal.pos 197) (Sat.Literal.pos 195) (lex_1_197_prefix s) (positive_select s 197) (lex_1_197_image s)

theorem lex_1_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2681), (Sat.Literal.pos 2680)] :=
  (lex_1_197_gate s).prop _ (List.Mem.head _)

theorem lex_1_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2681), (Sat.Literal.neg 197), (Sat.Literal.pos 195)] :=
  (lex_1_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2681), (Sat.Literal.pos 197), (Sat.Literal.neg 195)] :=
  (lex_1_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2680), (Sat.Literal.neg 197), (Sat.Literal.neg 195), (Sat.Literal.pos 2681)] :=
  (lex_1_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2680), (Sat.Literal.pos 197), (Sat.Literal.pos 195), (Sat.Literal.pos 2681)] :=
  (lex_1_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2681) = lexBefore s permutation1 196 := by
  exact (positive_lex_of_descriptor s 2681 permutation1 197 (by rfl)).trans ((lex_skipped s permutation1 196 197 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation1 196) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation1 196 by rw [image1_eq]; rfl))

theorem lex_1_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2682) (Sat.Literal.pos 2681) (Sat.Literal.pos 196) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation1 196 (assignment s)
    (Sat.Literal.pos 2682) (Sat.Literal.pos 2681) (Sat.Literal.pos 196) (Sat.Literal.pos 194) (positive_of_descriptor s 2682 (.lex permutation1 196) (by rfl)) (lex_1_196_prefix s) (positive_select s 196) (lex_1_196_image s)

theorem lex_1_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2681), (Sat.Literal.pos 196), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation1 196 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2681) (Sat.Literal.pos 196) (Sat.Literal.pos 194) (lex_1_196_prefix s) (positive_select s 196) (lex_1_196_image s)

theorem lex_1_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2682), (Sat.Literal.pos 2681)] :=
  (lex_1_196_gate s).prop _ (List.Mem.head _)

theorem lex_1_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2682), (Sat.Literal.neg 196), (Sat.Literal.pos 194)] :=
  (lex_1_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2682), (Sat.Literal.pos 196), (Sat.Literal.neg 194)] :=
  (lex_1_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2681), (Sat.Literal.neg 196), (Sat.Literal.neg 194), (Sat.Literal.pos 2682)] :=
  (lex_1_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2681), (Sat.Literal.pos 196), (Sat.Literal.pos 194), (Sat.Literal.pos 2682)] :=
  (lex_1_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2682) = lexBefore s permutation1 195 := by
  exact (positive_lex_of_descriptor s 2682 permutation1 196 (by rfl)).trans ((lex_skipped s permutation1 195 196 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation1 195) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation1 195 by rw [image1_eq]; rfl))

theorem lex_1_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2683) (Sat.Literal.pos 2682) (Sat.Literal.pos 195) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation1 195 (assignment s)
    (Sat.Literal.pos 2683) (Sat.Literal.pos 2682) (Sat.Literal.pos 195) (Sat.Literal.pos 197) (positive_of_descriptor s 2683 (.lex permutation1 195) (by rfl)) (lex_1_195_prefix s) (positive_select s 195) (lex_1_195_image s)

theorem lex_1_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2682), (Sat.Literal.pos 195), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation1 195 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2682) (Sat.Literal.pos 195) (Sat.Literal.pos 197) (lex_1_195_prefix s) (positive_select s 195) (lex_1_195_image s)

theorem lex_1_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2683), (Sat.Literal.pos 2682)] :=
  (lex_1_195_gate s).prop _ (List.Mem.head _)

theorem lex_1_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2683), (Sat.Literal.neg 195), (Sat.Literal.pos 197)] :=
  (lex_1_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2683), (Sat.Literal.pos 195), (Sat.Literal.neg 197)] :=
  (lex_1_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2682), (Sat.Literal.neg 195), (Sat.Literal.neg 197), (Sat.Literal.pos 2683)] :=
  (lex_1_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2682), (Sat.Literal.pos 195), (Sat.Literal.pos 197), (Sat.Literal.pos 2683)] :=
  (lex_1_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2683) = lexBefore s permutation1 194 := by
  exact (positive_lex_of_descriptor s 2683 permutation1 195 (by rfl)).trans ((lex_skipped s permutation1 194 195 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 196) = s (permuteMask permutation1 194) := by
  exact (positive_select s 196).trans (congrArg s (show (196 : Fin 256) = permuteMask permutation1 194 by rw [image1_eq]; rfl))

theorem lex_1_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2684) (Sat.Literal.pos 2683) (Sat.Literal.pos 194) (Sat.Literal.pos 196)) := by
  exact equality_gate s permutation1 194 (assignment s)
    (Sat.Literal.pos 2684) (Sat.Literal.pos 2683) (Sat.Literal.pos 194) (Sat.Literal.pos 196) (positive_of_descriptor s 2684 (.lex permutation1 194) (by rfl)) (lex_1_194_prefix s) (positive_select s 194) (lex_1_194_image s)

theorem lex_1_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2683), (Sat.Literal.pos 194), (Sat.Literal.neg 196)] := by
  exact comparison_gate s permutation1 194 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2683) (Sat.Literal.pos 194) (Sat.Literal.pos 196) (lex_1_194_prefix s) (positive_select s 194) (lex_1_194_image s)

theorem lex_1_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2684), (Sat.Literal.pos 2683)] :=
  (lex_1_194_gate s).prop _ (List.Mem.head _)

theorem lex_1_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2684), (Sat.Literal.neg 194), (Sat.Literal.pos 196)] :=
  (lex_1_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2684), (Sat.Literal.pos 194), (Sat.Literal.neg 196)] :=
  (lex_1_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2683), (Sat.Literal.neg 194), (Sat.Literal.neg 196), (Sat.Literal.pos 2684)] :=
  (lex_1_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2683), (Sat.Literal.pos 194), (Sat.Literal.pos 196), (Sat.Literal.pos 2684)] :=
  (lex_1_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2684) = lexBefore s permutation1 189 := by
  exact (positive_lex_of_descriptor s 2684 permutation1 194 (by rfl)).trans ((lex_skipped s permutation1 189 194 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 190 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation1 189) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation1 189 by rw [image1_eq]; rfl))

theorem lex_1_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2685) (Sat.Literal.pos 2684) (Sat.Literal.pos 189) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation1 189 (assignment s)
    (Sat.Literal.pos 2685) (Sat.Literal.pos 2684) (Sat.Literal.pos 189) (Sat.Literal.pos 187) (positive_of_descriptor s 2685 (.lex permutation1 189) (by rfl)) (lex_1_189_prefix s) (positive_select s 189) (lex_1_189_image s)

theorem lex_1_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2684), (Sat.Literal.pos 189), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation1 189 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2684) (Sat.Literal.pos 189) (Sat.Literal.pos 187) (lex_1_189_prefix s) (positive_select s 189) (lex_1_189_image s)

theorem lex_1_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2685), (Sat.Literal.pos 2684)] :=
  (lex_1_189_gate s).prop _ (List.Mem.head _)

theorem lex_1_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2685), (Sat.Literal.neg 189), (Sat.Literal.pos 187)] :=
  (lex_1_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2685), (Sat.Literal.pos 189), (Sat.Literal.neg 187)] :=
  (lex_1_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2684), (Sat.Literal.neg 189), (Sat.Literal.neg 187), (Sat.Literal.pos 2685)] :=
  (lex_1_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2684), (Sat.Literal.pos 189), (Sat.Literal.pos 187), (Sat.Literal.pos 2685)] :=
  (lex_1_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2685) = lexBefore s permutation1 188 := by
  exact (positive_lex_of_descriptor s 2685 permutation1 189 (by rfl)).trans ((lex_skipped s permutation1 188 189 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation1 188) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation1 188 by rw [image1_eq]; rfl))

theorem lex_1_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2686) (Sat.Literal.pos 2685) (Sat.Literal.pos 188) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation1 188 (assignment s)
    (Sat.Literal.pos 2686) (Sat.Literal.pos 2685) (Sat.Literal.pos 188) (Sat.Literal.pos 186) (positive_of_descriptor s 2686 (.lex permutation1 188) (by rfl)) (lex_1_188_prefix s) (positive_select s 188) (lex_1_188_image s)

theorem lex_1_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2685), (Sat.Literal.pos 188), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation1 188 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2685) (Sat.Literal.pos 188) (Sat.Literal.pos 186) (lex_1_188_prefix s) (positive_select s 188) (lex_1_188_image s)

theorem lex_1_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2686), (Sat.Literal.pos 2685)] :=
  (lex_1_188_gate s).prop _ (List.Mem.head _)

theorem lex_1_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2686), (Sat.Literal.neg 188), (Sat.Literal.pos 186)] :=
  (lex_1_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2686), (Sat.Literal.pos 188), (Sat.Literal.neg 186)] :=
  (lex_1_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2685), (Sat.Literal.neg 188), (Sat.Literal.neg 186), (Sat.Literal.pos 2686)] :=
  (lex_1_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2685), (Sat.Literal.pos 188), (Sat.Literal.pos 186), (Sat.Literal.pos 2686)] :=
  (lex_1_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2686) = lexBefore s permutation1 187 := by
  exact (positive_lex_of_descriptor s 2686 permutation1 188 (by rfl)).trans ((lex_skipped s permutation1 187 188 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation1 187) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation1 187 by rw [image1_eq]; rfl))

theorem lex_1_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2687) (Sat.Literal.pos 2686) (Sat.Literal.pos 187) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation1 187 (assignment s)
    (Sat.Literal.pos 2687) (Sat.Literal.pos 2686) (Sat.Literal.pos 187) (Sat.Literal.pos 189) (positive_of_descriptor s 2687 (.lex permutation1 187) (by rfl)) (lex_1_187_prefix s) (positive_select s 187) (lex_1_187_image s)

theorem lex_1_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2686), (Sat.Literal.pos 187), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation1 187 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2686) (Sat.Literal.pos 187) (Sat.Literal.pos 189) (lex_1_187_prefix s) (positive_select s 187) (lex_1_187_image s)

theorem lex_1_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2687), (Sat.Literal.pos 2686)] :=
  (lex_1_187_gate s).prop _ (List.Mem.head _)

theorem lex_1_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2687), (Sat.Literal.neg 187), (Sat.Literal.pos 189)] :=
  (lex_1_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2687), (Sat.Literal.pos 187), (Sat.Literal.neg 189)] :=
  (lex_1_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2686), (Sat.Literal.neg 187), (Sat.Literal.neg 189), (Sat.Literal.pos 2687)] :=
  (lex_1_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2686), (Sat.Literal.pos 187), (Sat.Literal.pos 189), (Sat.Literal.pos 2687)] :=
  (lex_1_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2687) = lexBefore s permutation1 186 := by
  exact (positive_lex_of_descriptor s 2687 permutation1 187 (by rfl)).trans ((lex_skipped s permutation1 186 187 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation1 186) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation1 186 by rw [image1_eq]; rfl))

theorem lex_1_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2688) (Sat.Literal.pos 2687) (Sat.Literal.pos 186) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation1 186 (assignment s)
    (Sat.Literal.pos 2688) (Sat.Literal.pos 2687) (Sat.Literal.pos 186) (Sat.Literal.pos 188) (positive_of_descriptor s 2688 (.lex permutation1 186) (by rfl)) (lex_1_186_prefix s) (positive_select s 186) (lex_1_186_image s)

theorem lex_1_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2687), (Sat.Literal.pos 186), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation1 186 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2687) (Sat.Literal.pos 186) (Sat.Literal.pos 188) (lex_1_186_prefix s) (positive_select s 186) (lex_1_186_image s)

theorem lex_1_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2688), (Sat.Literal.pos 2687)] :=
  (lex_1_186_gate s).prop _ (List.Mem.head _)

theorem lex_1_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2688), (Sat.Literal.neg 186), (Sat.Literal.pos 188)] :=
  (lex_1_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2688), (Sat.Literal.pos 186), (Sat.Literal.neg 188)] :=
  (lex_1_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2687), (Sat.Literal.neg 186), (Sat.Literal.neg 188), (Sat.Literal.pos 2688)] :=
  (lex_1_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2687), (Sat.Literal.pos 186), (Sat.Literal.pos 188), (Sat.Literal.pos 2688)] :=
  (lex_1_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2688) = lexBefore s permutation1 181 := by
  exact (positive_lex_of_descriptor s 2688 permutation1 186 (by rfl)).trans ((lex_skipped s permutation1 181 186 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 182 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation1 181) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation1 181 by rw [image1_eq]; rfl))

theorem lex_1_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2689) (Sat.Literal.pos 2688) (Sat.Literal.pos 181) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation1 181 (assignment s)
    (Sat.Literal.pos 2689) (Sat.Literal.pos 2688) (Sat.Literal.pos 181) (Sat.Literal.pos 179) (positive_of_descriptor s 2689 (.lex permutation1 181) (by rfl)) (lex_1_181_prefix s) (positive_select s 181) (lex_1_181_image s)

theorem lex_1_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2688), (Sat.Literal.pos 181), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation1 181 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2688) (Sat.Literal.pos 181) (Sat.Literal.pos 179) (lex_1_181_prefix s) (positive_select s 181) (lex_1_181_image s)

theorem lex_1_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2689), (Sat.Literal.pos 2688)] :=
  (lex_1_181_gate s).prop _ (List.Mem.head _)

theorem lex_1_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2689), (Sat.Literal.neg 181), (Sat.Literal.pos 179)] :=
  (lex_1_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2689), (Sat.Literal.pos 181), (Sat.Literal.neg 179)] :=
  (lex_1_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2688), (Sat.Literal.neg 181), (Sat.Literal.neg 179), (Sat.Literal.pos 2689)] :=
  (lex_1_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2688), (Sat.Literal.pos 181), (Sat.Literal.pos 179), (Sat.Literal.pos 2689)] :=
  (lex_1_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2689) = lexBefore s permutation1 180 := by
  exact (positive_lex_of_descriptor s 2689 permutation1 181 (by rfl)).trans ((lex_skipped s permutation1 180 181 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation1 180) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation1 180 by rw [image1_eq]; rfl))

theorem lex_1_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2690) (Sat.Literal.pos 2689) (Sat.Literal.pos 180) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation1 180 (assignment s)
    (Sat.Literal.pos 2690) (Sat.Literal.pos 2689) (Sat.Literal.pos 180) (Sat.Literal.pos 178) (positive_of_descriptor s 2690 (.lex permutation1 180) (by rfl)) (lex_1_180_prefix s) (positive_select s 180) (lex_1_180_image s)

theorem lex_1_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2689), (Sat.Literal.pos 180), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation1 180 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2689) (Sat.Literal.pos 180) (Sat.Literal.pos 178) (lex_1_180_prefix s) (positive_select s 180) (lex_1_180_image s)

theorem lex_1_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2690), (Sat.Literal.pos 2689)] :=
  (lex_1_180_gate s).prop _ (List.Mem.head _)

theorem lex_1_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2690), (Sat.Literal.neg 180), (Sat.Literal.pos 178)] :=
  (lex_1_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2690), (Sat.Literal.pos 180), (Sat.Literal.neg 178)] :=
  (lex_1_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2689), (Sat.Literal.neg 180), (Sat.Literal.neg 178), (Sat.Literal.pos 2690)] :=
  (lex_1_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2689), (Sat.Literal.pos 180), (Sat.Literal.pos 178), (Sat.Literal.pos 2690)] :=
  (lex_1_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2690) = lexBefore s permutation1 179 := by
  exact (positive_lex_of_descriptor s 2690 permutation1 180 (by rfl)).trans ((lex_skipped s permutation1 179 180 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation1 179) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation1 179 by rw [image1_eq]; rfl))

theorem lex_1_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2691) (Sat.Literal.pos 2690) (Sat.Literal.pos 179) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation1 179 (assignment s)
    (Sat.Literal.pos 2691) (Sat.Literal.pos 2690) (Sat.Literal.pos 179) (Sat.Literal.pos 181) (positive_of_descriptor s 2691 (.lex permutation1 179) (by rfl)) (lex_1_179_prefix s) (positive_select s 179) (lex_1_179_image s)

theorem lex_1_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2690), (Sat.Literal.pos 179), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation1 179 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2690) (Sat.Literal.pos 179) (Sat.Literal.pos 181) (lex_1_179_prefix s) (positive_select s 179) (lex_1_179_image s)

theorem lex_1_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2691), (Sat.Literal.pos 2690)] :=
  (lex_1_179_gate s).prop _ (List.Mem.head _)

theorem lex_1_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2691), (Sat.Literal.neg 179), (Sat.Literal.pos 181)] :=
  (lex_1_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2691), (Sat.Literal.pos 179), (Sat.Literal.neg 181)] :=
  (lex_1_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2690), (Sat.Literal.neg 179), (Sat.Literal.neg 181), (Sat.Literal.pos 2691)] :=
  (lex_1_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2690), (Sat.Literal.pos 179), (Sat.Literal.pos 181), (Sat.Literal.pos 2691)] :=
  (lex_1_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2691) = lexBefore s permutation1 178 := by
  exact (positive_lex_of_descriptor s 2691 permutation1 179 (by rfl)).trans ((lex_skipped s permutation1 178 179 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation1 178) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation1 178 by rw [image1_eq]; rfl))

theorem lex_1_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2692) (Sat.Literal.pos 2691) (Sat.Literal.pos 178) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation1 178 (assignment s)
    (Sat.Literal.pos 2692) (Sat.Literal.pos 2691) (Sat.Literal.pos 178) (Sat.Literal.pos 180) (positive_of_descriptor s 2692 (.lex permutation1 178) (by rfl)) (lex_1_178_prefix s) (positive_select s 178) (lex_1_178_image s)

theorem lex_1_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2691), (Sat.Literal.pos 178), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation1 178 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2691) (Sat.Literal.pos 178) (Sat.Literal.pos 180) (lex_1_178_prefix s) (positive_select s 178) (lex_1_178_image s)

theorem lex_1_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2692), (Sat.Literal.pos 2691)] :=
  (lex_1_178_gate s).prop _ (List.Mem.head _)

theorem lex_1_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2692), (Sat.Literal.neg 178), (Sat.Literal.pos 180)] :=
  (lex_1_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2692), (Sat.Literal.pos 178), (Sat.Literal.neg 180)] :=
  (lex_1_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2691), (Sat.Literal.neg 178), (Sat.Literal.neg 180), (Sat.Literal.pos 2692)] :=
  (lex_1_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2691), (Sat.Literal.pos 178), (Sat.Literal.pos 180), (Sat.Literal.pos 2692)] :=
  (lex_1_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2692) = lexBefore s permutation1 173 := by
  exact (positive_lex_of_descriptor s 2692 permutation1 178 (by rfl)).trans ((lex_skipped s permutation1 173 178 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 174 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation1 173) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation1 173 by rw [image1_eq]; rfl))

theorem lex_1_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2693) (Sat.Literal.pos 2692) (Sat.Literal.pos 173) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation1 173 (assignment s)
    (Sat.Literal.pos 2693) (Sat.Literal.pos 2692) (Sat.Literal.pos 173) (Sat.Literal.pos 171) (positive_of_descriptor s 2693 (.lex permutation1 173) (by rfl)) (lex_1_173_prefix s) (positive_select s 173) (lex_1_173_image s)

theorem lex_1_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2692), (Sat.Literal.pos 173), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation1 173 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2692) (Sat.Literal.pos 173) (Sat.Literal.pos 171) (lex_1_173_prefix s) (positive_select s 173) (lex_1_173_image s)

theorem lex_1_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2693), (Sat.Literal.pos 2692)] :=
  (lex_1_173_gate s).prop _ (List.Mem.head _)

theorem lex_1_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2693), (Sat.Literal.neg 173), (Sat.Literal.pos 171)] :=
  (lex_1_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2693), (Sat.Literal.pos 173), (Sat.Literal.neg 171)] :=
  (lex_1_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2692), (Sat.Literal.neg 173), (Sat.Literal.neg 171), (Sat.Literal.pos 2693)] :=
  (lex_1_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2692), (Sat.Literal.pos 173), (Sat.Literal.pos 171), (Sat.Literal.pos 2693)] :=
  (lex_1_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2693) = lexBefore s permutation1 172 := by
  exact (positive_lex_of_descriptor s 2693 permutation1 173 (by rfl)).trans ((lex_skipped s permutation1 172 173 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation1 172) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation1 172 by rw [image1_eq]; rfl))

theorem lex_1_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2694) (Sat.Literal.pos 2693) (Sat.Literal.pos 172) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation1 172 (assignment s)
    (Sat.Literal.pos 2694) (Sat.Literal.pos 2693) (Sat.Literal.pos 172) (Sat.Literal.pos 170) (positive_of_descriptor s 2694 (.lex permutation1 172) (by rfl)) (lex_1_172_prefix s) (positive_select s 172) (lex_1_172_image s)

theorem lex_1_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2693), (Sat.Literal.pos 172), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation1 172 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2693) (Sat.Literal.pos 172) (Sat.Literal.pos 170) (lex_1_172_prefix s) (positive_select s 172) (lex_1_172_image s)

theorem lex_1_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2694), (Sat.Literal.pos 2693)] :=
  (lex_1_172_gate s).prop _ (List.Mem.head _)

theorem lex_1_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2694), (Sat.Literal.neg 172), (Sat.Literal.pos 170)] :=
  (lex_1_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2694), (Sat.Literal.pos 172), (Sat.Literal.neg 170)] :=
  (lex_1_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2693), (Sat.Literal.neg 172), (Sat.Literal.neg 170), (Sat.Literal.pos 2694)] :=
  (lex_1_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2693), (Sat.Literal.pos 172), (Sat.Literal.pos 170), (Sat.Literal.pos 2694)] :=
  (lex_1_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2694) = lexBefore s permutation1 171 := by
  exact (positive_lex_of_descriptor s 2694 permutation1 172 (by rfl)).trans ((lex_skipped s permutation1 171 172 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation1 171) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation1 171 by rw [image1_eq]; rfl))

theorem lex_1_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2695) (Sat.Literal.pos 2694) (Sat.Literal.pos 171) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation1 171 (assignment s)
    (Sat.Literal.pos 2695) (Sat.Literal.pos 2694) (Sat.Literal.pos 171) (Sat.Literal.pos 173) (positive_of_descriptor s 2695 (.lex permutation1 171) (by rfl)) (lex_1_171_prefix s) (positive_select s 171) (lex_1_171_image s)

theorem lex_1_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2694), (Sat.Literal.pos 171), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation1 171 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2694) (Sat.Literal.pos 171) (Sat.Literal.pos 173) (lex_1_171_prefix s) (positive_select s 171) (lex_1_171_image s)

theorem lex_1_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2695), (Sat.Literal.pos 2694)] :=
  (lex_1_171_gate s).prop _ (List.Mem.head _)

theorem lex_1_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2695), (Sat.Literal.neg 171), (Sat.Literal.pos 173)] :=
  (lex_1_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2695), (Sat.Literal.pos 171), (Sat.Literal.neg 173)] :=
  (lex_1_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2694), (Sat.Literal.neg 171), (Sat.Literal.neg 173), (Sat.Literal.pos 2695)] :=
  (lex_1_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2694), (Sat.Literal.pos 171), (Sat.Literal.pos 173), (Sat.Literal.pos 2695)] :=
  (lex_1_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2695) = lexBefore s permutation1 170 := by
  exact (positive_lex_of_descriptor s 2695 permutation1 171 (by rfl)).trans ((lex_skipped s permutation1 170 171 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation1 170) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation1 170 by rw [image1_eq]; rfl))

theorem lex_1_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2696) (Sat.Literal.pos 2695) (Sat.Literal.pos 170) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation1 170 (assignment s)
    (Sat.Literal.pos 2696) (Sat.Literal.pos 2695) (Sat.Literal.pos 170) (Sat.Literal.pos 172) (positive_of_descriptor s 2696 (.lex permutation1 170) (by rfl)) (lex_1_170_prefix s) (positive_select s 170) (lex_1_170_image s)

theorem lex_1_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2695), (Sat.Literal.pos 170), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation1 170 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2695) (Sat.Literal.pos 170) (Sat.Literal.pos 172) (lex_1_170_prefix s) (positive_select s 170) (lex_1_170_image s)

theorem lex_1_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2696), (Sat.Literal.pos 2695)] :=
  (lex_1_170_gate s).prop _ (List.Mem.head _)

theorem lex_1_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2696), (Sat.Literal.neg 170), (Sat.Literal.pos 172)] :=
  (lex_1_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2696), (Sat.Literal.pos 170), (Sat.Literal.neg 172)] :=
  (lex_1_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2695), (Sat.Literal.neg 170), (Sat.Literal.neg 172), (Sat.Literal.pos 2696)] :=
  (lex_1_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2695), (Sat.Literal.pos 170), (Sat.Literal.pos 172), (Sat.Literal.pos 2696)] :=
  (lex_1_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2696) = lexBefore s permutation1 165 := by
  exact (positive_lex_of_descriptor s 2696 permutation1 170 (by rfl)).trans ((lex_skipped s permutation1 165 170 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 166 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation1 165) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation1 165 by rw [image1_eq]; rfl))

theorem lex_1_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2697) (Sat.Literal.pos 2696) (Sat.Literal.pos 165) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation1 165 (assignment s)
    (Sat.Literal.pos 2697) (Sat.Literal.pos 2696) (Sat.Literal.pos 165) (Sat.Literal.pos 163) (positive_of_descriptor s 2697 (.lex permutation1 165) (by rfl)) (lex_1_165_prefix s) (positive_select s 165) (lex_1_165_image s)

theorem lex_1_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2696), (Sat.Literal.pos 165), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation1 165 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2696) (Sat.Literal.pos 165) (Sat.Literal.pos 163) (lex_1_165_prefix s) (positive_select s 165) (lex_1_165_image s)

theorem lex_1_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2697), (Sat.Literal.pos 2696)] :=
  (lex_1_165_gate s).prop _ (List.Mem.head _)

theorem lex_1_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2697), (Sat.Literal.neg 165), (Sat.Literal.pos 163)] :=
  (lex_1_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2697), (Sat.Literal.pos 165), (Sat.Literal.neg 163)] :=
  (lex_1_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2696), (Sat.Literal.neg 165), (Sat.Literal.neg 163), (Sat.Literal.pos 2697)] :=
  (lex_1_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2696), (Sat.Literal.pos 165), (Sat.Literal.pos 163), (Sat.Literal.pos 2697)] :=
  (lex_1_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2697) = lexBefore s permutation1 164 := by
  exact (positive_lex_of_descriptor s 2697 permutation1 165 (by rfl)).trans ((lex_skipped s permutation1 164 165 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation1 164) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation1 164 by rw [image1_eq]; rfl))

theorem lex_1_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2698) (Sat.Literal.pos 2697) (Sat.Literal.pos 164) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation1 164 (assignment s)
    (Sat.Literal.pos 2698) (Sat.Literal.pos 2697) (Sat.Literal.pos 164) (Sat.Literal.pos 162) (positive_of_descriptor s 2698 (.lex permutation1 164) (by rfl)) (lex_1_164_prefix s) (positive_select s 164) (lex_1_164_image s)

theorem lex_1_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2697), (Sat.Literal.pos 164), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation1 164 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2697) (Sat.Literal.pos 164) (Sat.Literal.pos 162) (lex_1_164_prefix s) (positive_select s 164) (lex_1_164_image s)

theorem lex_1_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2698), (Sat.Literal.pos 2697)] :=
  (lex_1_164_gate s).prop _ (List.Mem.head _)

theorem lex_1_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2698), (Sat.Literal.neg 164), (Sat.Literal.pos 162)] :=
  (lex_1_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2698), (Sat.Literal.pos 164), (Sat.Literal.neg 162)] :=
  (lex_1_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2697), (Sat.Literal.neg 164), (Sat.Literal.neg 162), (Sat.Literal.pos 2698)] :=
  (lex_1_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2697), (Sat.Literal.pos 164), (Sat.Literal.pos 162), (Sat.Literal.pos 2698)] :=
  (lex_1_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2698) = lexBefore s permutation1 163 := by
  exact (positive_lex_of_descriptor s 2698 permutation1 164 (by rfl)).trans ((lex_skipped s permutation1 163 164 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation1 163) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation1 163 by rw [image1_eq]; rfl))

theorem lex_1_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2699) (Sat.Literal.pos 2698) (Sat.Literal.pos 163) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation1 163 (assignment s)
    (Sat.Literal.pos 2699) (Sat.Literal.pos 2698) (Sat.Literal.pos 163) (Sat.Literal.pos 165) (positive_of_descriptor s 2699 (.lex permutation1 163) (by rfl)) (lex_1_163_prefix s) (positive_select s 163) (lex_1_163_image s)

theorem lex_1_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2698), (Sat.Literal.pos 163), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation1 163 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2698) (Sat.Literal.pos 163) (Sat.Literal.pos 165) (lex_1_163_prefix s) (positive_select s 163) (lex_1_163_image s)

theorem lex_1_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2699), (Sat.Literal.pos 2698)] :=
  (lex_1_163_gate s).prop _ (List.Mem.head _)

theorem lex_1_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2699), (Sat.Literal.neg 163), (Sat.Literal.pos 165)] :=
  (lex_1_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2699), (Sat.Literal.pos 163), (Sat.Literal.neg 165)] :=
  (lex_1_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2698), (Sat.Literal.neg 163), (Sat.Literal.neg 165), (Sat.Literal.pos 2699)] :=
  (lex_1_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2698), (Sat.Literal.pos 163), (Sat.Literal.pos 165), (Sat.Literal.pos 2699)] :=
  (lex_1_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2699) = lexBefore s permutation1 162 := by
  exact (positive_lex_of_descriptor s 2699 permutation1 163 (by rfl)).trans ((lex_skipped s permutation1 162 163 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation1 162) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation1 162 by rw [image1_eq]; rfl))

theorem lex_1_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2700) (Sat.Literal.pos 2699) (Sat.Literal.pos 162) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation1 162 (assignment s)
    (Sat.Literal.pos 2700) (Sat.Literal.pos 2699) (Sat.Literal.pos 162) (Sat.Literal.pos 164) (positive_of_descriptor s 2700 (.lex permutation1 162) (by rfl)) (lex_1_162_prefix s) (positive_select s 162) (lex_1_162_image s)

theorem lex_1_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2699), (Sat.Literal.pos 162), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation1 162 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2699) (Sat.Literal.pos 162) (Sat.Literal.pos 164) (lex_1_162_prefix s) (positive_select s 162) (lex_1_162_image s)

theorem lex_1_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2700), (Sat.Literal.pos 2699)] :=
  (lex_1_162_gate s).prop _ (List.Mem.head _)

theorem lex_1_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2700), (Sat.Literal.neg 162), (Sat.Literal.pos 164)] :=
  (lex_1_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2700), (Sat.Literal.pos 162), (Sat.Literal.neg 164)] :=
  (lex_1_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2699), (Sat.Literal.neg 162), (Sat.Literal.neg 164), (Sat.Literal.pos 2700)] :=
  (lex_1_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2699), (Sat.Literal.pos 162), (Sat.Literal.pos 164), (Sat.Literal.pos 2700)] :=
  (lex_1_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2700) = lexBefore s permutation1 157 := by
  exact (positive_lex_of_descriptor s 2700 permutation1 162 (by rfl)).trans ((lex_skipped s permutation1 157 162 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 158 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation1 157) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation1 157 by rw [image1_eq]; rfl))

theorem lex_1_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2701) (Sat.Literal.pos 2700) (Sat.Literal.pos 157) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation1 157 (assignment s)
    (Sat.Literal.pos 2701) (Sat.Literal.pos 2700) (Sat.Literal.pos 157) (Sat.Literal.pos 155) (positive_of_descriptor s 2701 (.lex permutation1 157) (by rfl)) (lex_1_157_prefix s) (positive_select s 157) (lex_1_157_image s)

theorem lex_1_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2700), (Sat.Literal.pos 157), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation1 157 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2700) (Sat.Literal.pos 157) (Sat.Literal.pos 155) (lex_1_157_prefix s) (positive_select s 157) (lex_1_157_image s)

theorem lex_1_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2701), (Sat.Literal.pos 2700)] :=
  (lex_1_157_gate s).prop _ (List.Mem.head _)

theorem lex_1_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2701), (Sat.Literal.neg 157), (Sat.Literal.pos 155)] :=
  (lex_1_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2701), (Sat.Literal.pos 157), (Sat.Literal.neg 155)] :=
  (lex_1_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2700), (Sat.Literal.neg 157), (Sat.Literal.neg 155), (Sat.Literal.pos 2701)] :=
  (lex_1_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2700), (Sat.Literal.pos 157), (Sat.Literal.pos 155), (Sat.Literal.pos 2701)] :=
  (lex_1_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2701) = lexBefore s permutation1 156 := by
  exact (positive_lex_of_descriptor s 2701 permutation1 157 (by rfl)).trans ((lex_skipped s permutation1 156 157 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation1 156) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation1 156 by rw [image1_eq]; rfl))

theorem lex_1_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2702) (Sat.Literal.pos 2701) (Sat.Literal.pos 156) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation1 156 (assignment s)
    (Sat.Literal.pos 2702) (Sat.Literal.pos 2701) (Sat.Literal.pos 156) (Sat.Literal.pos 154) (positive_of_descriptor s 2702 (.lex permutation1 156) (by rfl)) (lex_1_156_prefix s) (positive_select s 156) (lex_1_156_image s)

theorem lex_1_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2701), (Sat.Literal.pos 156), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation1 156 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2701) (Sat.Literal.pos 156) (Sat.Literal.pos 154) (lex_1_156_prefix s) (positive_select s 156) (lex_1_156_image s)

theorem lex_1_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2702), (Sat.Literal.pos 2701)] :=
  (lex_1_156_gate s).prop _ (List.Mem.head _)

theorem lex_1_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2702), (Sat.Literal.neg 156), (Sat.Literal.pos 154)] :=
  (lex_1_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2702), (Sat.Literal.pos 156), (Sat.Literal.neg 154)] :=
  (lex_1_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2701), (Sat.Literal.neg 156), (Sat.Literal.neg 154), (Sat.Literal.pos 2702)] :=
  (lex_1_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2701), (Sat.Literal.pos 156), (Sat.Literal.pos 154), (Sat.Literal.pos 2702)] :=
  (lex_1_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2702) = lexBefore s permutation1 155 := by
  exact (positive_lex_of_descriptor s 2702 permutation1 156 (by rfl)).trans ((lex_skipped s permutation1 155 156 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation1 155) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation1 155 by rw [image1_eq]; rfl))

theorem lex_1_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2703) (Sat.Literal.pos 2702) (Sat.Literal.pos 155) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation1 155 (assignment s)
    (Sat.Literal.pos 2703) (Sat.Literal.pos 2702) (Sat.Literal.pos 155) (Sat.Literal.pos 157) (positive_of_descriptor s 2703 (.lex permutation1 155) (by rfl)) (lex_1_155_prefix s) (positive_select s 155) (lex_1_155_image s)

theorem lex_1_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2702), (Sat.Literal.pos 155), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation1 155 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2702) (Sat.Literal.pos 155) (Sat.Literal.pos 157) (lex_1_155_prefix s) (positive_select s 155) (lex_1_155_image s)

theorem lex_1_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2703), (Sat.Literal.pos 2702)] :=
  (lex_1_155_gate s).prop _ (List.Mem.head _)

theorem lex_1_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2703), (Sat.Literal.neg 155), (Sat.Literal.pos 157)] :=
  (lex_1_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2703), (Sat.Literal.pos 155), (Sat.Literal.neg 157)] :=
  (lex_1_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2702), (Sat.Literal.neg 155), (Sat.Literal.neg 157), (Sat.Literal.pos 2703)] :=
  (lex_1_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2702), (Sat.Literal.pos 155), (Sat.Literal.pos 157), (Sat.Literal.pos 2703)] :=
  (lex_1_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2703) = lexBefore s permutation1 154 := by
  exact (positive_lex_of_descriptor s 2703 permutation1 155 (by rfl)).trans ((lex_skipped s permutation1 154 155 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation1 154) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation1 154 by rw [image1_eq]; rfl))

theorem lex_1_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2704) (Sat.Literal.pos 2703) (Sat.Literal.pos 154) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation1 154 (assignment s)
    (Sat.Literal.pos 2704) (Sat.Literal.pos 2703) (Sat.Literal.pos 154) (Sat.Literal.pos 156) (positive_of_descriptor s 2704 (.lex permutation1 154) (by rfl)) (lex_1_154_prefix s) (positive_select s 154) (lex_1_154_image s)

theorem lex_1_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2703), (Sat.Literal.pos 154), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation1 154 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2703) (Sat.Literal.pos 154) (Sat.Literal.pos 156) (lex_1_154_prefix s) (positive_select s 154) (lex_1_154_image s)

theorem lex_1_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2704), (Sat.Literal.pos 2703)] :=
  (lex_1_154_gate s).prop _ (List.Mem.head _)

theorem lex_1_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2704), (Sat.Literal.neg 154), (Sat.Literal.pos 156)] :=
  (lex_1_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2704), (Sat.Literal.pos 154), (Sat.Literal.neg 156)] :=
  (lex_1_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2703), (Sat.Literal.neg 154), (Sat.Literal.neg 156), (Sat.Literal.pos 2704)] :=
  (lex_1_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2703), (Sat.Literal.pos 154), (Sat.Literal.pos 156), (Sat.Literal.pos 2704)] :=
  (lex_1_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2704) = lexBefore s permutation1 149 := by
  exact (positive_lex_of_descriptor s 2704 permutation1 154 (by rfl)).trans ((lex_skipped s permutation1 149 154 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 150 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation1 149) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation1 149 by rw [image1_eq]; rfl))

theorem lex_1_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2705) (Sat.Literal.pos 2704) (Sat.Literal.pos 149) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation1 149 (assignment s)
    (Sat.Literal.pos 2705) (Sat.Literal.pos 2704) (Sat.Literal.pos 149) (Sat.Literal.pos 147) (positive_of_descriptor s 2705 (.lex permutation1 149) (by rfl)) (lex_1_149_prefix s) (positive_select s 149) (lex_1_149_image s)

theorem lex_1_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2704), (Sat.Literal.pos 149), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation1 149 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2704) (Sat.Literal.pos 149) (Sat.Literal.pos 147) (lex_1_149_prefix s) (positive_select s 149) (lex_1_149_image s)

theorem lex_1_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2705), (Sat.Literal.pos 2704)] :=
  (lex_1_149_gate s).prop _ (List.Mem.head _)

theorem lex_1_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2705), (Sat.Literal.neg 149), (Sat.Literal.pos 147)] :=
  (lex_1_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2705), (Sat.Literal.pos 149), (Sat.Literal.neg 147)] :=
  (lex_1_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2704), (Sat.Literal.neg 149), (Sat.Literal.neg 147), (Sat.Literal.pos 2705)] :=
  (lex_1_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2704), (Sat.Literal.pos 149), (Sat.Literal.pos 147), (Sat.Literal.pos 2705)] :=
  (lex_1_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2705) = lexBefore s permutation1 148 := by
  exact (positive_lex_of_descriptor s 2705 permutation1 149 (by rfl)).trans ((lex_skipped s permutation1 148 149 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation1 148) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation1 148 by rw [image1_eq]; rfl))

theorem lex_1_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2706) (Sat.Literal.pos 2705) (Sat.Literal.pos 148) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation1 148 (assignment s)
    (Sat.Literal.pos 2706) (Sat.Literal.pos 2705) (Sat.Literal.pos 148) (Sat.Literal.pos 146) (positive_of_descriptor s 2706 (.lex permutation1 148) (by rfl)) (lex_1_148_prefix s) (positive_select s 148) (lex_1_148_image s)

theorem lex_1_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2705), (Sat.Literal.pos 148), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation1 148 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2705) (Sat.Literal.pos 148) (Sat.Literal.pos 146) (lex_1_148_prefix s) (positive_select s 148) (lex_1_148_image s)

theorem lex_1_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2706), (Sat.Literal.pos 2705)] :=
  (lex_1_148_gate s).prop _ (List.Mem.head _)

theorem lex_1_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2706), (Sat.Literal.neg 148), (Sat.Literal.pos 146)] :=
  (lex_1_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2706), (Sat.Literal.pos 148), (Sat.Literal.neg 146)] :=
  (lex_1_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2705), (Sat.Literal.neg 148), (Sat.Literal.neg 146), (Sat.Literal.pos 2706)] :=
  (lex_1_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2705), (Sat.Literal.pos 148), (Sat.Literal.pos 146), (Sat.Literal.pos 2706)] :=
  (lex_1_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2706) = lexBefore s permutation1 147 := by
  exact (positive_lex_of_descriptor s 2706 permutation1 148 (by rfl)).trans ((lex_skipped s permutation1 147 148 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation1 147) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation1 147 by rw [image1_eq]; rfl))

theorem lex_1_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2707) (Sat.Literal.pos 2706) (Sat.Literal.pos 147) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation1 147 (assignment s)
    (Sat.Literal.pos 2707) (Sat.Literal.pos 2706) (Sat.Literal.pos 147) (Sat.Literal.pos 149) (positive_of_descriptor s 2707 (.lex permutation1 147) (by rfl)) (lex_1_147_prefix s) (positive_select s 147) (lex_1_147_image s)

theorem lex_1_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2706), (Sat.Literal.pos 147), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation1 147 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2706) (Sat.Literal.pos 147) (Sat.Literal.pos 149) (lex_1_147_prefix s) (positive_select s 147) (lex_1_147_image s)

theorem lex_1_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2707), (Sat.Literal.pos 2706)] :=
  (lex_1_147_gate s).prop _ (List.Mem.head _)

theorem lex_1_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2707), (Sat.Literal.neg 147), (Sat.Literal.pos 149)] :=
  (lex_1_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2707), (Sat.Literal.pos 147), (Sat.Literal.neg 149)] :=
  (lex_1_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2706), (Sat.Literal.neg 147), (Sat.Literal.neg 149), (Sat.Literal.pos 2707)] :=
  (lex_1_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2706), (Sat.Literal.pos 147), (Sat.Literal.pos 149), (Sat.Literal.pos 2707)] :=
  (lex_1_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2707) = lexBefore s permutation1 146 := by
  exact (positive_lex_of_descriptor s 2707 permutation1 147 (by rfl)).trans ((lex_skipped s permutation1 146 147 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation1 146) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation1 146 by rw [image1_eq]; rfl))

theorem lex_1_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2708) (Sat.Literal.pos 2707) (Sat.Literal.pos 146) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation1 146 (assignment s)
    (Sat.Literal.pos 2708) (Sat.Literal.pos 2707) (Sat.Literal.pos 146) (Sat.Literal.pos 148) (positive_of_descriptor s 2708 (.lex permutation1 146) (by rfl)) (lex_1_146_prefix s) (positive_select s 146) (lex_1_146_image s)

theorem lex_1_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2707), (Sat.Literal.pos 146), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation1 146 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2707) (Sat.Literal.pos 146) (Sat.Literal.pos 148) (lex_1_146_prefix s) (positive_select s 146) (lex_1_146_image s)

theorem lex_1_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2708), (Sat.Literal.pos 2707)] :=
  (lex_1_146_gate s).prop _ (List.Mem.head _)

theorem lex_1_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2708), (Sat.Literal.neg 146), (Sat.Literal.pos 148)] :=
  (lex_1_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2708), (Sat.Literal.pos 146), (Sat.Literal.neg 148)] :=
  (lex_1_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2707), (Sat.Literal.neg 146), (Sat.Literal.neg 148), (Sat.Literal.pos 2708)] :=
  (lex_1_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2707), (Sat.Literal.pos 146), (Sat.Literal.pos 148), (Sat.Literal.pos 2708)] :=
  (lex_1_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2708) = lexBefore s permutation1 141 := by
  exact (positive_lex_of_descriptor s 2708 permutation1 146 (by rfl)).trans ((lex_skipped s permutation1 141 146 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 142 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation1 141) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation1 141 by rw [image1_eq]; rfl))

theorem lex_1_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2709) (Sat.Literal.pos 2708) (Sat.Literal.pos 141) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation1 141 (assignment s)
    (Sat.Literal.pos 2709) (Sat.Literal.pos 2708) (Sat.Literal.pos 141) (Sat.Literal.pos 139) (positive_of_descriptor s 2709 (.lex permutation1 141) (by rfl)) (lex_1_141_prefix s) (positive_select s 141) (lex_1_141_image s)

theorem lex_1_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2708), (Sat.Literal.pos 141), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation1 141 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2708) (Sat.Literal.pos 141) (Sat.Literal.pos 139) (lex_1_141_prefix s) (positive_select s 141) (lex_1_141_image s)

theorem lex_1_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2709), (Sat.Literal.pos 2708)] :=
  (lex_1_141_gate s).prop _ (List.Mem.head _)

theorem lex_1_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2709), (Sat.Literal.neg 141), (Sat.Literal.pos 139)] :=
  (lex_1_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2709), (Sat.Literal.pos 141), (Sat.Literal.neg 139)] :=
  (lex_1_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2708), (Sat.Literal.neg 141), (Sat.Literal.neg 139), (Sat.Literal.pos 2709)] :=
  (lex_1_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2708), (Sat.Literal.pos 141), (Sat.Literal.pos 139), (Sat.Literal.pos 2709)] :=
  (lex_1_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2709) = lexBefore s permutation1 140 := by
  exact (positive_lex_of_descriptor s 2709 permutation1 141 (by rfl)).trans ((lex_skipped s permutation1 140 141 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation1 140) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation1 140 by rw [image1_eq]; rfl))

theorem lex_1_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2710) (Sat.Literal.pos 2709) (Sat.Literal.pos 140) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation1 140 (assignment s)
    (Sat.Literal.pos 2710) (Sat.Literal.pos 2709) (Sat.Literal.pos 140) (Sat.Literal.pos 138) (positive_of_descriptor s 2710 (.lex permutation1 140) (by rfl)) (lex_1_140_prefix s) (positive_select s 140) (lex_1_140_image s)

theorem lex_1_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2709), (Sat.Literal.pos 140), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation1 140 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2709) (Sat.Literal.pos 140) (Sat.Literal.pos 138) (lex_1_140_prefix s) (positive_select s 140) (lex_1_140_image s)

theorem lex_1_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2710), (Sat.Literal.pos 2709)] :=
  (lex_1_140_gate s).prop _ (List.Mem.head _)

theorem lex_1_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2710), (Sat.Literal.neg 140), (Sat.Literal.pos 138)] :=
  (lex_1_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2710), (Sat.Literal.pos 140), (Sat.Literal.neg 138)] :=
  (lex_1_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2709), (Sat.Literal.neg 140), (Sat.Literal.neg 138), (Sat.Literal.pos 2710)] :=
  (lex_1_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2709), (Sat.Literal.pos 140), (Sat.Literal.pos 138), (Sat.Literal.pos 2710)] :=
  (lex_1_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2710) = lexBefore s permutation1 139 := by
  exact (positive_lex_of_descriptor s 2710 permutation1 140 (by rfl)).trans ((lex_skipped s permutation1 139 140 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation1 139) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation1 139 by rw [image1_eq]; rfl))

theorem lex_1_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2711) (Sat.Literal.pos 2710) (Sat.Literal.pos 139) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation1 139 (assignment s)
    (Sat.Literal.pos 2711) (Sat.Literal.pos 2710) (Sat.Literal.pos 139) (Sat.Literal.pos 141) (positive_of_descriptor s 2711 (.lex permutation1 139) (by rfl)) (lex_1_139_prefix s) (positive_select s 139) (lex_1_139_image s)

theorem lex_1_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2710), (Sat.Literal.pos 139), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation1 139 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2710) (Sat.Literal.pos 139) (Sat.Literal.pos 141) (lex_1_139_prefix s) (positive_select s 139) (lex_1_139_image s)

theorem lex_1_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2711), (Sat.Literal.pos 2710)] :=
  (lex_1_139_gate s).prop _ (List.Mem.head _)

theorem lex_1_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2711), (Sat.Literal.neg 139), (Sat.Literal.pos 141)] :=
  (lex_1_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2711), (Sat.Literal.pos 139), (Sat.Literal.neg 141)] :=
  (lex_1_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2710), (Sat.Literal.neg 139), (Sat.Literal.neg 141), (Sat.Literal.pos 2711)] :=
  (lex_1_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2710), (Sat.Literal.pos 139), (Sat.Literal.pos 141), (Sat.Literal.pos 2711)] :=
  (lex_1_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2711) = lexBefore s permutation1 138 := by
  exact (positive_lex_of_descriptor s 2711 permutation1 139 (by rfl)).trans ((lex_skipped s permutation1 138 139 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation1 138) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation1 138 by rw [image1_eq]; rfl))

theorem lex_1_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2712) (Sat.Literal.pos 2711) (Sat.Literal.pos 138) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation1 138 (assignment s)
    (Sat.Literal.pos 2712) (Sat.Literal.pos 2711) (Sat.Literal.pos 138) (Sat.Literal.pos 140) (positive_of_descriptor s 2712 (.lex permutation1 138) (by rfl)) (lex_1_138_prefix s) (positive_select s 138) (lex_1_138_image s)

theorem lex_1_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2711), (Sat.Literal.pos 138), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation1 138 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2711) (Sat.Literal.pos 138) (Sat.Literal.pos 140) (lex_1_138_prefix s) (positive_select s 138) (lex_1_138_image s)

theorem lex_1_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2712), (Sat.Literal.pos 2711)] :=
  (lex_1_138_gate s).prop _ (List.Mem.head _)

theorem lex_1_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2712), (Sat.Literal.neg 138), (Sat.Literal.pos 140)] :=
  (lex_1_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2712), (Sat.Literal.pos 138), (Sat.Literal.neg 140)] :=
  (lex_1_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2711), (Sat.Literal.neg 138), (Sat.Literal.neg 140), (Sat.Literal.pos 2712)] :=
  (lex_1_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2711), (Sat.Literal.pos 138), (Sat.Literal.pos 140), (Sat.Literal.pos 2712)] :=
  (lex_1_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2712) = lexBefore s permutation1 133 := by
  exact (positive_lex_of_descriptor s 2712 permutation1 138 (by rfl)).trans ((lex_skipped s permutation1 133 138 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 134 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation1 133) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation1 133 by rw [image1_eq]; rfl))

theorem lex_1_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2713) (Sat.Literal.pos 2712) (Sat.Literal.pos 133) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation1 133 (assignment s)
    (Sat.Literal.pos 2713) (Sat.Literal.pos 2712) (Sat.Literal.pos 133) (Sat.Literal.pos 131) (positive_of_descriptor s 2713 (.lex permutation1 133) (by rfl)) (lex_1_133_prefix s) (positive_select s 133) (lex_1_133_image s)

theorem lex_1_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2712), (Sat.Literal.pos 133), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation1 133 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2712) (Sat.Literal.pos 133) (Sat.Literal.pos 131) (lex_1_133_prefix s) (positive_select s 133) (lex_1_133_image s)

theorem lex_1_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2713), (Sat.Literal.pos 2712)] :=
  (lex_1_133_gate s).prop _ (List.Mem.head _)

theorem lex_1_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2713), (Sat.Literal.neg 133), (Sat.Literal.pos 131)] :=
  (lex_1_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2713), (Sat.Literal.pos 133), (Sat.Literal.neg 131)] :=
  (lex_1_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2712), (Sat.Literal.neg 133), (Sat.Literal.neg 131), (Sat.Literal.pos 2713)] :=
  (lex_1_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2712), (Sat.Literal.pos 133), (Sat.Literal.pos 131), (Sat.Literal.pos 2713)] :=
  (lex_1_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2713) = lexBefore s permutation1 132 := by
  exact (positive_lex_of_descriptor s 2713 permutation1 133 (by rfl)).trans ((lex_skipped s permutation1 132 133 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation1 132) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation1 132 by rw [image1_eq]; rfl))

theorem lex_1_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2714) (Sat.Literal.pos 2713) (Sat.Literal.pos 132) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation1 132 (assignment s)
    (Sat.Literal.pos 2714) (Sat.Literal.pos 2713) (Sat.Literal.pos 132) (Sat.Literal.pos 130) (positive_of_descriptor s 2714 (.lex permutation1 132) (by rfl)) (lex_1_132_prefix s) (positive_select s 132) (lex_1_132_image s)

theorem lex_1_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2713), (Sat.Literal.pos 132), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation1 132 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2713) (Sat.Literal.pos 132) (Sat.Literal.pos 130) (lex_1_132_prefix s) (positive_select s 132) (lex_1_132_image s)

theorem lex_1_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2714), (Sat.Literal.pos 2713)] :=
  (lex_1_132_gate s).prop _ (List.Mem.head _)

theorem lex_1_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2714), (Sat.Literal.neg 132), (Sat.Literal.pos 130)] :=
  (lex_1_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2714), (Sat.Literal.pos 132), (Sat.Literal.neg 130)] :=
  (lex_1_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2713), (Sat.Literal.neg 132), (Sat.Literal.neg 130), (Sat.Literal.pos 2714)] :=
  (lex_1_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2713), (Sat.Literal.pos 132), (Sat.Literal.pos 130), (Sat.Literal.pos 2714)] :=
  (lex_1_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2714) = lexBefore s permutation1 131 := by
  exact (positive_lex_of_descriptor s 2714 permutation1 132 (by rfl)).trans ((lex_skipped s permutation1 131 132 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation1 131) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation1 131 by rw [image1_eq]; rfl))

theorem lex_1_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2715) (Sat.Literal.pos 2714) (Sat.Literal.pos 131) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation1 131 (assignment s)
    (Sat.Literal.pos 2715) (Sat.Literal.pos 2714) (Sat.Literal.pos 131) (Sat.Literal.pos 133) (positive_of_descriptor s 2715 (.lex permutation1 131) (by rfl)) (lex_1_131_prefix s) (positive_select s 131) (lex_1_131_image s)

theorem lex_1_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2714), (Sat.Literal.pos 131), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation1 131 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2714) (Sat.Literal.pos 131) (Sat.Literal.pos 133) (lex_1_131_prefix s) (positive_select s 131) (lex_1_131_image s)

theorem lex_1_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2715), (Sat.Literal.pos 2714)] :=
  (lex_1_131_gate s).prop _ (List.Mem.head _)

theorem lex_1_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2715), (Sat.Literal.neg 131), (Sat.Literal.pos 133)] :=
  (lex_1_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2715), (Sat.Literal.pos 131), (Sat.Literal.neg 133)] :=
  (lex_1_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2714), (Sat.Literal.neg 131), (Sat.Literal.neg 133), (Sat.Literal.pos 2715)] :=
  (lex_1_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2714), (Sat.Literal.pos 131), (Sat.Literal.pos 133), (Sat.Literal.pos 2715)] :=
  (lex_1_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2715) = lexBefore s permutation1 130 := by
  exact (positive_lex_of_descriptor s 2715 permutation1 131 (by rfl)).trans ((lex_skipped s permutation1 130 131 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation1 130) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation1 130 by rw [image1_eq]; rfl))

theorem lex_1_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2716) (Sat.Literal.pos 2715) (Sat.Literal.pos 130) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation1 130 (assignment s)
    (Sat.Literal.pos 2716) (Sat.Literal.pos 2715) (Sat.Literal.pos 130) (Sat.Literal.pos 132) (positive_of_descriptor s 2716 (.lex permutation1 130) (by rfl)) (lex_1_130_prefix s) (positive_select s 130) (lex_1_130_image s)

theorem lex_1_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2715), (Sat.Literal.pos 130), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation1 130 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2715) (Sat.Literal.pos 130) (Sat.Literal.pos 132) (lex_1_130_prefix s) (positive_select s 130) (lex_1_130_image s)

theorem lex_1_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2716), (Sat.Literal.pos 2715)] :=
  (lex_1_130_gate s).prop _ (List.Mem.head _)

theorem lex_1_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2716), (Sat.Literal.neg 130), (Sat.Literal.pos 132)] :=
  (lex_1_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2716), (Sat.Literal.pos 130), (Sat.Literal.neg 132)] :=
  (lex_1_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2715), (Sat.Literal.neg 130), (Sat.Literal.neg 132), (Sat.Literal.pos 2716)] :=
  (lex_1_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2715), (Sat.Literal.pos 130), (Sat.Literal.pos 132), (Sat.Literal.pos 2716)] :=
  (lex_1_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2716) = lexBefore s permutation1 125 := by
  exact (positive_lex_of_descriptor s 2716 permutation1 130 (by rfl)).trans ((lex_skipped s permutation1 125 130 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 126 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation1 125) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation1 125 by rw [image1_eq]; rfl))

theorem lex_1_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2717) (Sat.Literal.pos 2716) (Sat.Literal.pos 125) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation1 125 (assignment s)
    (Sat.Literal.pos 2717) (Sat.Literal.pos 2716) (Sat.Literal.pos 125) (Sat.Literal.pos 123) (positive_of_descriptor s 2717 (.lex permutation1 125) (by rfl)) (lex_1_125_prefix s) (positive_select s 125) (lex_1_125_image s)

theorem lex_1_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2716), (Sat.Literal.pos 125), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation1 125 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2716) (Sat.Literal.pos 125) (Sat.Literal.pos 123) (lex_1_125_prefix s) (positive_select s 125) (lex_1_125_image s)

theorem lex_1_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2717), (Sat.Literal.pos 2716)] :=
  (lex_1_125_gate s).prop _ (List.Mem.head _)

theorem lex_1_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2717), (Sat.Literal.neg 125), (Sat.Literal.pos 123)] :=
  (lex_1_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2717), (Sat.Literal.pos 125), (Sat.Literal.neg 123)] :=
  (lex_1_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2716), (Sat.Literal.neg 125), (Sat.Literal.neg 123), (Sat.Literal.pos 2717)] :=
  (lex_1_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2716), (Sat.Literal.pos 125), (Sat.Literal.pos 123), (Sat.Literal.pos 2717)] :=
  (lex_1_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2717) = lexBefore s permutation1 124 := by
  exact (positive_lex_of_descriptor s 2717 permutation1 125 (by rfl)).trans ((lex_skipped s permutation1 124 125 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation1 124) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation1 124 by rw [image1_eq]; rfl))

theorem lex_1_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2718) (Sat.Literal.pos 2717) (Sat.Literal.pos 124) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation1 124 (assignment s)
    (Sat.Literal.pos 2718) (Sat.Literal.pos 2717) (Sat.Literal.pos 124) (Sat.Literal.pos 122) (positive_of_descriptor s 2718 (.lex permutation1 124) (by rfl)) (lex_1_124_prefix s) (positive_select s 124) (lex_1_124_image s)

theorem lex_1_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2717), (Sat.Literal.pos 124), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation1 124 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2717) (Sat.Literal.pos 124) (Sat.Literal.pos 122) (lex_1_124_prefix s) (positive_select s 124) (lex_1_124_image s)

theorem lex_1_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2718), (Sat.Literal.pos 2717)] :=
  (lex_1_124_gate s).prop _ (List.Mem.head _)

theorem lex_1_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2718), (Sat.Literal.neg 124), (Sat.Literal.pos 122)] :=
  (lex_1_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2718), (Sat.Literal.pos 124), (Sat.Literal.neg 122)] :=
  (lex_1_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2717), (Sat.Literal.neg 124), (Sat.Literal.neg 122), (Sat.Literal.pos 2718)] :=
  (lex_1_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2717), (Sat.Literal.pos 124), (Sat.Literal.pos 122), (Sat.Literal.pos 2718)] :=
  (lex_1_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2718) = lexBefore s permutation1 123 := by
  exact (positive_lex_of_descriptor s 2718 permutation1 124 (by rfl)).trans ((lex_skipped s permutation1 123 124 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation1 123) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation1 123 by rw [image1_eq]; rfl))

theorem lex_1_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2719) (Sat.Literal.pos 2718) (Sat.Literal.pos 123) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation1 123 (assignment s)
    (Sat.Literal.pos 2719) (Sat.Literal.pos 2718) (Sat.Literal.pos 123) (Sat.Literal.pos 125) (positive_of_descriptor s 2719 (.lex permutation1 123) (by rfl)) (lex_1_123_prefix s) (positive_select s 123) (lex_1_123_image s)

theorem lex_1_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2718), (Sat.Literal.pos 123), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation1 123 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2718) (Sat.Literal.pos 123) (Sat.Literal.pos 125) (lex_1_123_prefix s) (positive_select s 123) (lex_1_123_image s)

theorem lex_1_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2719), (Sat.Literal.pos 2718)] :=
  (lex_1_123_gate s).prop _ (List.Mem.head _)

theorem lex_1_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2719), (Sat.Literal.neg 123), (Sat.Literal.pos 125)] :=
  (lex_1_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2719), (Sat.Literal.pos 123), (Sat.Literal.neg 125)] :=
  (lex_1_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2718), (Sat.Literal.neg 123), (Sat.Literal.neg 125), (Sat.Literal.pos 2719)] :=
  (lex_1_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2718), (Sat.Literal.pos 123), (Sat.Literal.pos 125), (Sat.Literal.pos 2719)] :=
  (lex_1_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2719) = lexBefore s permutation1 122 := by
  exact (positive_lex_of_descriptor s 2719 permutation1 123 (by rfl)).trans ((lex_skipped s permutation1 122 123 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation1 122) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation1 122 by rw [image1_eq]; rfl))

theorem lex_1_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2720) (Sat.Literal.pos 2719) (Sat.Literal.pos 122) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation1 122 (assignment s)
    (Sat.Literal.pos 2720) (Sat.Literal.pos 2719) (Sat.Literal.pos 122) (Sat.Literal.pos 124) (positive_of_descriptor s 2720 (.lex permutation1 122) (by rfl)) (lex_1_122_prefix s) (positive_select s 122) (lex_1_122_image s)

theorem lex_1_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2719), (Sat.Literal.pos 122), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation1 122 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2719) (Sat.Literal.pos 122) (Sat.Literal.pos 124) (lex_1_122_prefix s) (positive_select s 122) (lex_1_122_image s)

theorem lex_1_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2720), (Sat.Literal.pos 2719)] :=
  (lex_1_122_gate s).prop _ (List.Mem.head _)

theorem lex_1_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2720), (Sat.Literal.neg 122), (Sat.Literal.pos 124)] :=
  (lex_1_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2720), (Sat.Literal.pos 122), (Sat.Literal.neg 124)] :=
  (lex_1_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2719), (Sat.Literal.neg 122), (Sat.Literal.neg 124), (Sat.Literal.pos 2720)] :=
  (lex_1_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2719), (Sat.Literal.pos 122), (Sat.Literal.pos 124), (Sat.Literal.pos 2720)] :=
  (lex_1_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2720) = lexBefore s permutation1 117 := by
  exact (positive_lex_of_descriptor s 2720 permutation1 122 (by rfl)).trans ((lex_skipped s permutation1 117 122 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 118 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation1 117) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation1 117 by rw [image1_eq]; rfl))

theorem lex_1_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2721) (Sat.Literal.pos 2720) (Sat.Literal.pos 117) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation1 117 (assignment s)
    (Sat.Literal.pos 2721) (Sat.Literal.pos 2720) (Sat.Literal.pos 117) (Sat.Literal.pos 115) (positive_of_descriptor s 2721 (.lex permutation1 117) (by rfl)) (lex_1_117_prefix s) (positive_select s 117) (lex_1_117_image s)

theorem lex_1_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2720), (Sat.Literal.pos 117), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation1 117 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2720) (Sat.Literal.pos 117) (Sat.Literal.pos 115) (lex_1_117_prefix s) (positive_select s 117) (lex_1_117_image s)

theorem lex_1_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2721), (Sat.Literal.pos 2720)] :=
  (lex_1_117_gate s).prop _ (List.Mem.head _)

theorem lex_1_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2721), (Sat.Literal.neg 117), (Sat.Literal.pos 115)] :=
  (lex_1_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2721), (Sat.Literal.pos 117), (Sat.Literal.neg 115)] :=
  (lex_1_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2720), (Sat.Literal.neg 117), (Sat.Literal.neg 115), (Sat.Literal.pos 2721)] :=
  (lex_1_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2720), (Sat.Literal.pos 117), (Sat.Literal.pos 115), (Sat.Literal.pos 2721)] :=
  (lex_1_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2721) = lexBefore s permutation1 116 := by
  exact (positive_lex_of_descriptor s 2721 permutation1 117 (by rfl)).trans ((lex_skipped s permutation1 116 117 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation1 116) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation1 116 by rw [image1_eq]; rfl))

theorem lex_1_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2722) (Sat.Literal.pos 2721) (Sat.Literal.pos 116) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation1 116 (assignment s)
    (Sat.Literal.pos 2722) (Sat.Literal.pos 2721) (Sat.Literal.pos 116) (Sat.Literal.pos 114) (positive_of_descriptor s 2722 (.lex permutation1 116) (by rfl)) (lex_1_116_prefix s) (positive_select s 116) (lex_1_116_image s)

theorem lex_1_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2721), (Sat.Literal.pos 116), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation1 116 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2721) (Sat.Literal.pos 116) (Sat.Literal.pos 114) (lex_1_116_prefix s) (positive_select s 116) (lex_1_116_image s)

theorem lex_1_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2722), (Sat.Literal.pos 2721)] :=
  (lex_1_116_gate s).prop _ (List.Mem.head _)

theorem lex_1_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2722), (Sat.Literal.neg 116), (Sat.Literal.pos 114)] :=
  (lex_1_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2722), (Sat.Literal.pos 116), (Sat.Literal.neg 114)] :=
  (lex_1_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2721), (Sat.Literal.neg 116), (Sat.Literal.neg 114), (Sat.Literal.pos 2722)] :=
  (lex_1_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2721), (Sat.Literal.pos 116), (Sat.Literal.pos 114), (Sat.Literal.pos 2722)] :=
  (lex_1_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2722) = lexBefore s permutation1 115 := by
  exact (positive_lex_of_descriptor s 2722 permutation1 116 (by rfl)).trans ((lex_skipped s permutation1 115 116 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation1 115) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation1 115 by rw [image1_eq]; rfl))

theorem lex_1_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2723) (Sat.Literal.pos 2722) (Sat.Literal.pos 115) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation1 115 (assignment s)
    (Sat.Literal.pos 2723) (Sat.Literal.pos 2722) (Sat.Literal.pos 115) (Sat.Literal.pos 117) (positive_of_descriptor s 2723 (.lex permutation1 115) (by rfl)) (lex_1_115_prefix s) (positive_select s 115) (lex_1_115_image s)

theorem lex_1_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2722), (Sat.Literal.pos 115), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation1 115 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2722) (Sat.Literal.pos 115) (Sat.Literal.pos 117) (lex_1_115_prefix s) (positive_select s 115) (lex_1_115_image s)

theorem lex_1_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2723), (Sat.Literal.pos 2722)] :=
  (lex_1_115_gate s).prop _ (List.Mem.head _)

theorem lex_1_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2723), (Sat.Literal.neg 115), (Sat.Literal.pos 117)] :=
  (lex_1_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2723), (Sat.Literal.pos 115), (Sat.Literal.neg 117)] :=
  (lex_1_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2722), (Sat.Literal.neg 115), (Sat.Literal.neg 117), (Sat.Literal.pos 2723)] :=
  (lex_1_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2722), (Sat.Literal.pos 115), (Sat.Literal.pos 117), (Sat.Literal.pos 2723)] :=
  (lex_1_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_1_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2723) = lexBefore s permutation1 114 := by
  exact (positive_lex_of_descriptor s 2723 permutation1 115 (by rfl)).trans ((lex_skipped s permutation1 114 115 (by decide) (by intro j hj hp; rw [image1_eq]; exact fixedOnRange_spec image1 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_1_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation1 114) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation1 114 by rw [image1_eq]; rfl))

theorem lex_1_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2724) (Sat.Literal.pos 2723) (Sat.Literal.pos 114) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation1 114 (assignment s)
    (Sat.Literal.pos 2724) (Sat.Literal.pos 2723) (Sat.Literal.pos 114) (Sat.Literal.pos 116) (positive_of_descriptor s 2724 (.lex permutation1 114) (by rfl)) (lex_1_114_prefix s) (positive_select s 114) (lex_1_114_image s)

theorem lex_1_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2723), (Sat.Literal.pos 114), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation1 114 (hmax permutation1) (assignment s)
    (Sat.Literal.pos 2723) (Sat.Literal.pos 114) (Sat.Literal.pos 116) (lex_1_114_prefix s) (positive_select s 114) (lex_1_114_image s)

theorem lex_1_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2724), (Sat.Literal.pos 2723)] :=
  (lex_1_114_gate s).prop _ (List.Mem.head _)

theorem lex_1_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2724), (Sat.Literal.neg 114), (Sat.Literal.pos 116)] :=
  (lex_1_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_1_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2724), (Sat.Literal.pos 114), (Sat.Literal.neg 116)] :=
  (lex_1_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_1_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2723), (Sat.Literal.neg 114), (Sat.Literal.neg 116), (Sat.Literal.pos 2724)] :=
  (lex_1_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_1_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2723), (Sat.Literal.pos 114), (Sat.Literal.pos 116), (Sat.Literal.pos 2724)] :=
  (lex_1_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_0_54_gate

end Crown.CertificateData
