import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_9_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4124) = lexBefore s permutation9 56 := by
  exact (positive_lex_of_descriptor s 4124 permutation9 57 (by rfl)).trans ((lex_skipped s permutation9 56 57 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation9 56) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation9 56 by rw [image9_eq]; rfl))

theorem lex_9_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4125) (Sat.Literal.pos 4124) (Sat.Literal.pos 56) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation9 56 (assignment s)
    (Sat.Literal.pos 4125) (Sat.Literal.pos 4124) (Sat.Literal.pos 56) (Sat.Literal.pos 193) (positive_of_descriptor s 4125 (.lex permutation9 56) (by rfl)) (lex_9_56_prefix s) (positive_select s 56) (lex_9_56_image s)

theorem lex_9_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4124), (Sat.Literal.pos 56), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation9 56 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4124) (Sat.Literal.pos 56) (Sat.Literal.pos 193) (lex_9_56_prefix s) (positive_select s 56) (lex_9_56_image s)

theorem lex_9_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4125), (Sat.Literal.pos 4124)] :=
  (lex_9_56_gate s).prop _ (List.Mem.head _)

theorem lex_9_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4125), (Sat.Literal.neg 56), (Sat.Literal.pos 193)] :=
  (lex_9_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4125), (Sat.Literal.pos 56), (Sat.Literal.neg 193)] :=
  (lex_9_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4124), (Sat.Literal.neg 56), (Sat.Literal.neg 193), (Sat.Literal.pos 4125)] :=
  (lex_9_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4124), (Sat.Literal.pos 56), (Sat.Literal.pos 193), (Sat.Literal.pos 4125)] :=
  (lex_9_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4125) = lexBefore s permutation9 55 := by
  exact (positive_lex_of_descriptor s 4125 permutation9 56 (by rfl)).trans ((lex_skipped s permutation9 55 56 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation9 55) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation9 55 by rw [image9_eq]; rfl))

theorem lex_9_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4126) (Sat.Literal.pos 4125) (Sat.Literal.pos 55) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation9 55 (assignment s)
    (Sat.Literal.pos 4126) (Sat.Literal.pos 4125) (Sat.Literal.pos 55) (Sat.Literal.pos 185) (positive_of_descriptor s 4126 (.lex permutation9 55) (by rfl)) (lex_9_55_prefix s) (positive_select s 55) (lex_9_55_image s)

theorem lex_9_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4125), (Sat.Literal.pos 55), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation9 55 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4125) (Sat.Literal.pos 55) (Sat.Literal.pos 185) (lex_9_55_prefix s) (positive_select s 55) (lex_9_55_image s)

theorem lex_9_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4126), (Sat.Literal.pos 4125)] :=
  (lex_9_55_gate s).prop _ (List.Mem.head _)

theorem lex_9_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4126), (Sat.Literal.neg 55), (Sat.Literal.pos 185)] :=
  (lex_9_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4126), (Sat.Literal.pos 55), (Sat.Literal.neg 185)] :=
  (lex_9_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4125), (Sat.Literal.neg 55), (Sat.Literal.neg 185), (Sat.Literal.pos 4126)] :=
  (lex_9_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4125), (Sat.Literal.pos 55), (Sat.Literal.pos 185), (Sat.Literal.pos 4126)] :=
  (lex_9_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4126) = lexBefore s permutation9 54 := by
  exact (positive_lex_of_descriptor s 4126 permutation9 55 (by rfl)).trans ((lex_skipped s permutation9 54 55 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation9 54) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation9 54 by rw [image9_eq]; rfl))

theorem lex_9_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4127) (Sat.Literal.pos 4126) (Sat.Literal.pos 54) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation9 54 (assignment s)
    (Sat.Literal.pos 4127) (Sat.Literal.pos 4126) (Sat.Literal.pos 54) (Sat.Literal.pos 177) (positive_of_descriptor s 4127 (.lex permutation9 54) (by rfl)) (lex_9_54_prefix s) (positive_select s 54) (lex_9_54_image s)

theorem lex_9_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4126), (Sat.Literal.pos 54), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation9 54 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4126) (Sat.Literal.pos 54) (Sat.Literal.pos 177) (lex_9_54_prefix s) (positive_select s 54) (lex_9_54_image s)

theorem lex_9_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4127), (Sat.Literal.pos 4126)] :=
  (lex_9_54_gate s).prop _ (List.Mem.head _)

theorem lex_9_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4127), (Sat.Literal.neg 54), (Sat.Literal.pos 177)] :=
  (lex_9_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4127), (Sat.Literal.pos 54), (Sat.Literal.neg 177)] :=
  (lex_9_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4126), (Sat.Literal.neg 54), (Sat.Literal.neg 177), (Sat.Literal.pos 4127)] :=
  (lex_9_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4126), (Sat.Literal.pos 54), (Sat.Literal.pos 177), (Sat.Literal.pos 4127)] :=
  (lex_9_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4127) = lexBefore s permutation9 53 := by
  exact (positive_lex_of_descriptor s 4127 permutation9 54 (by rfl)).trans ((lex_skipped s permutation9 53 54 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation9 53) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation9 53 by rw [image9_eq]; rfl))

theorem lex_9_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4128) (Sat.Literal.pos 4127) (Sat.Literal.pos 53) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation9 53 (assignment s)
    (Sat.Literal.pos 4128) (Sat.Literal.pos 4127) (Sat.Literal.pos 53) (Sat.Literal.pos 169) (positive_of_descriptor s 4128 (.lex permutation9 53) (by rfl)) (lex_9_53_prefix s) (positive_select s 53) (lex_9_53_image s)

theorem lex_9_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4127), (Sat.Literal.pos 53), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation9 53 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4127) (Sat.Literal.pos 53) (Sat.Literal.pos 169) (lex_9_53_prefix s) (positive_select s 53) (lex_9_53_image s)

theorem lex_9_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4128), (Sat.Literal.pos 4127)] :=
  (lex_9_53_gate s).prop _ (List.Mem.head _)

theorem lex_9_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4128), (Sat.Literal.neg 53), (Sat.Literal.pos 169)] :=
  (lex_9_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4128), (Sat.Literal.pos 53), (Sat.Literal.neg 169)] :=
  (lex_9_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4127), (Sat.Literal.neg 53), (Sat.Literal.neg 169), (Sat.Literal.pos 4128)] :=
  (lex_9_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4127), (Sat.Literal.pos 53), (Sat.Literal.pos 169), (Sat.Literal.pos 4128)] :=
  (lex_9_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4128) = lexBefore s permutation9 52 := by
  exact (positive_lex_of_descriptor s 4128 permutation9 53 (by rfl)).trans ((lex_skipped s permutation9 52 53 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation9 52) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation9 52 by rw [image9_eq]; rfl))

theorem lex_9_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4129) (Sat.Literal.pos 4128) (Sat.Literal.pos 52) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation9 52 (assignment s)
    (Sat.Literal.pos 4129) (Sat.Literal.pos 4128) (Sat.Literal.pos 52) (Sat.Literal.pos 161) (positive_of_descriptor s 4129 (.lex permutation9 52) (by rfl)) (lex_9_52_prefix s) (positive_select s 52) (lex_9_52_image s)

theorem lex_9_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4128), (Sat.Literal.pos 52), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation9 52 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4128) (Sat.Literal.pos 52) (Sat.Literal.pos 161) (lex_9_52_prefix s) (positive_select s 52) (lex_9_52_image s)

theorem lex_9_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4129), (Sat.Literal.pos 4128)] :=
  (lex_9_52_gate s).prop _ (List.Mem.head _)

theorem lex_9_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4129), (Sat.Literal.neg 52), (Sat.Literal.pos 161)] :=
  (lex_9_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4129), (Sat.Literal.pos 52), (Sat.Literal.neg 161)] :=
  (lex_9_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4128), (Sat.Literal.neg 52), (Sat.Literal.neg 161), (Sat.Literal.pos 4129)] :=
  (lex_9_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4128), (Sat.Literal.pos 52), (Sat.Literal.pos 161), (Sat.Literal.pos 4129)] :=
  (lex_9_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4129) = lexBefore s permutation9 51 := by
  exact (positive_lex_of_descriptor s 4129 permutation9 52 (by rfl)).trans ((lex_skipped s permutation9 51 52 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation9 51) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation9 51 by rw [image9_eq]; rfl))

theorem lex_9_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4130) (Sat.Literal.pos 4129) (Sat.Literal.pos 51) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation9 51 (assignment s)
    (Sat.Literal.pos 4130) (Sat.Literal.pos 4129) (Sat.Literal.pos 51) (Sat.Literal.pos 153) (positive_of_descriptor s 4130 (.lex permutation9 51) (by rfl)) (lex_9_51_prefix s) (positive_select s 51) (lex_9_51_image s)

theorem lex_9_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4129), (Sat.Literal.pos 51), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation9 51 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4129) (Sat.Literal.pos 51) (Sat.Literal.pos 153) (lex_9_51_prefix s) (positive_select s 51) (lex_9_51_image s)

theorem lex_9_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4130), (Sat.Literal.pos 4129)] :=
  (lex_9_51_gate s).prop _ (List.Mem.head _)

theorem lex_9_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4130), (Sat.Literal.neg 51), (Sat.Literal.pos 153)] :=
  (lex_9_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4130), (Sat.Literal.pos 51), (Sat.Literal.neg 153)] :=
  (lex_9_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4129), (Sat.Literal.neg 51), (Sat.Literal.neg 153), (Sat.Literal.pos 4130)] :=
  (lex_9_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4129), (Sat.Literal.pos 51), (Sat.Literal.pos 153), (Sat.Literal.pos 4130)] :=
  (lex_9_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4130) = lexBefore s permutation9 50 := by
  exact (positive_lex_of_descriptor s 4130 permutation9 51 (by rfl)).trans ((lex_skipped s permutation9 50 51 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation9 50) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation9 50 by rw [image9_eq]; rfl))

theorem lex_9_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4131) (Sat.Literal.pos 4130) (Sat.Literal.pos 50) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation9 50 (assignment s)
    (Sat.Literal.pos 4131) (Sat.Literal.pos 4130) (Sat.Literal.pos 50) (Sat.Literal.pos 145) (positive_of_descriptor s 4131 (.lex permutation9 50) (by rfl)) (lex_9_50_prefix s) (positive_select s 50) (lex_9_50_image s)

theorem lex_9_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4130), (Sat.Literal.pos 50), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation9 50 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4130) (Sat.Literal.pos 50) (Sat.Literal.pos 145) (lex_9_50_prefix s) (positive_select s 50) (lex_9_50_image s)

theorem lex_9_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4131), (Sat.Literal.pos 4130)] :=
  (lex_9_50_gate s).prop _ (List.Mem.head _)

theorem lex_9_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4131), (Sat.Literal.neg 50), (Sat.Literal.pos 145)] :=
  (lex_9_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4131), (Sat.Literal.pos 50), (Sat.Literal.neg 145)] :=
  (lex_9_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4130), (Sat.Literal.neg 50), (Sat.Literal.neg 145), (Sat.Literal.pos 4131)] :=
  (lex_9_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4130), (Sat.Literal.pos 50), (Sat.Literal.pos 145), (Sat.Literal.pos 4131)] :=
  (lex_9_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4131) = lexBefore s permutation9 49 := by
  exact (positive_lex_of_descriptor s 4131 permutation9 50 (by rfl)).trans ((lex_skipped s permutation9 49 50 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation9 49) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation9 49 by rw [image9_eq]; rfl))

theorem lex_9_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4132) (Sat.Literal.pos 4131) (Sat.Literal.pos 49) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation9 49 (assignment s)
    (Sat.Literal.pos 4132) (Sat.Literal.pos 4131) (Sat.Literal.pos 49) (Sat.Literal.pos 137) (positive_of_descriptor s 4132 (.lex permutation9 49) (by rfl)) (lex_9_49_prefix s) (positive_select s 49) (lex_9_49_image s)

theorem lex_9_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4131), (Sat.Literal.pos 49), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation9 49 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4131) (Sat.Literal.pos 49) (Sat.Literal.pos 137) (lex_9_49_prefix s) (positive_select s 49) (lex_9_49_image s)

theorem lex_9_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4132), (Sat.Literal.pos 4131)] :=
  (lex_9_49_gate s).prop _ (List.Mem.head _)

theorem lex_9_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4132), (Sat.Literal.neg 49), (Sat.Literal.pos 137)] :=
  (lex_9_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4132), (Sat.Literal.pos 49), (Sat.Literal.neg 137)] :=
  (lex_9_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4131), (Sat.Literal.neg 49), (Sat.Literal.neg 137), (Sat.Literal.pos 4132)] :=
  (lex_9_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4131), (Sat.Literal.pos 49), (Sat.Literal.pos 137), (Sat.Literal.pos 4132)] :=
  (lex_9_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4132) = lexBefore s permutation9 48 := by
  exact (positive_lex_of_descriptor s 4132 permutation9 49 (by rfl)).trans ((lex_skipped s permutation9 48 49 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation9 48) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation9 48 by rw [image9_eq]; rfl))

theorem lex_9_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4133) (Sat.Literal.pos 4132) (Sat.Literal.pos 48) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation9 48 (assignment s)
    (Sat.Literal.pos 4133) (Sat.Literal.pos 4132) (Sat.Literal.pos 48) (Sat.Literal.pos 129) (positive_of_descriptor s 4133 (.lex permutation9 48) (by rfl)) (lex_9_48_prefix s) (positive_select s 48) (lex_9_48_image s)

theorem lex_9_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4132), (Sat.Literal.pos 48), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation9 48 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4132) (Sat.Literal.pos 48) (Sat.Literal.pos 129) (lex_9_48_prefix s) (positive_select s 48) (lex_9_48_image s)

theorem lex_9_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4133), (Sat.Literal.pos 4132)] :=
  (lex_9_48_gate s).prop _ (List.Mem.head _)

theorem lex_9_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4133), (Sat.Literal.neg 48), (Sat.Literal.pos 129)] :=
  (lex_9_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4133), (Sat.Literal.pos 48), (Sat.Literal.neg 129)] :=
  (lex_9_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4132), (Sat.Literal.neg 48), (Sat.Literal.neg 129), (Sat.Literal.pos 4133)] :=
  (lex_9_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4132), (Sat.Literal.pos 48), (Sat.Literal.pos 129), (Sat.Literal.pos 4133)] :=
  (lex_9_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4133) = lexBefore s permutation9 47 := by
  exact (positive_lex_of_descriptor s 4133 permutation9 48 (by rfl)).trans ((lex_skipped s permutation9 47 48 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation9 47) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation9 47 by rw [image9_eq]; rfl))

theorem lex_9_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4134) (Sat.Literal.pos 4133) (Sat.Literal.pos 47) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation9 47 (assignment s)
    (Sat.Literal.pos 4134) (Sat.Literal.pos 4133) (Sat.Literal.pos 47) (Sat.Literal.pos 121) (positive_of_descriptor s 4134 (.lex permutation9 47) (by rfl)) (lex_9_47_prefix s) (positive_select s 47) (lex_9_47_image s)

theorem lex_9_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4133), (Sat.Literal.pos 47), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation9 47 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4133) (Sat.Literal.pos 47) (Sat.Literal.pos 121) (lex_9_47_prefix s) (positive_select s 47) (lex_9_47_image s)

theorem lex_9_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4134), (Sat.Literal.pos 4133)] :=
  (lex_9_47_gate s).prop _ (List.Mem.head _)

theorem lex_9_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4134), (Sat.Literal.neg 47), (Sat.Literal.pos 121)] :=
  (lex_9_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4134), (Sat.Literal.pos 47), (Sat.Literal.neg 121)] :=
  (lex_9_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4133), (Sat.Literal.neg 47), (Sat.Literal.neg 121), (Sat.Literal.pos 4134)] :=
  (lex_9_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4133), (Sat.Literal.pos 47), (Sat.Literal.pos 121), (Sat.Literal.pos 4134)] :=
  (lex_9_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4134) = lexBefore s permutation9 46 := by
  exact (positive_lex_of_descriptor s 4134 permutation9 47 (by rfl)).trans ((lex_skipped s permutation9 46 47 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation9 46) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation9 46 by rw [image9_eq]; rfl))

theorem lex_9_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4135) (Sat.Literal.pos 4134) (Sat.Literal.pos 46) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation9 46 (assignment s)
    (Sat.Literal.pos 4135) (Sat.Literal.pos 4134) (Sat.Literal.pos 46) (Sat.Literal.pos 113) (positive_of_descriptor s 4135 (.lex permutation9 46) (by rfl)) (lex_9_46_prefix s) (positive_select s 46) (lex_9_46_image s)

theorem lex_9_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4134), (Sat.Literal.pos 46), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation9 46 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4134) (Sat.Literal.pos 46) (Sat.Literal.pos 113) (lex_9_46_prefix s) (positive_select s 46) (lex_9_46_image s)

theorem lex_9_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4135), (Sat.Literal.pos 4134)] :=
  (lex_9_46_gate s).prop _ (List.Mem.head _)

theorem lex_9_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4135), (Sat.Literal.neg 46), (Sat.Literal.pos 113)] :=
  (lex_9_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4135), (Sat.Literal.pos 46), (Sat.Literal.neg 113)] :=
  (lex_9_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4134), (Sat.Literal.neg 46), (Sat.Literal.neg 113), (Sat.Literal.pos 4135)] :=
  (lex_9_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4134), (Sat.Literal.pos 46), (Sat.Literal.pos 113), (Sat.Literal.pos 4135)] :=
  (lex_9_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4135) = lexBefore s permutation9 45 := by
  exact (positive_lex_of_descriptor s 4135 permutation9 46 (by rfl)).trans ((lex_skipped s permutation9 45 46 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation9 45) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation9 45 by rw [image9_eq]; rfl))

theorem lex_9_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4136) (Sat.Literal.pos 4135) (Sat.Literal.pos 45) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation9 45 (assignment s)
    (Sat.Literal.pos 4136) (Sat.Literal.pos 4135) (Sat.Literal.pos 45) (Sat.Literal.pos 105) (positive_of_descriptor s 4136 (.lex permutation9 45) (by rfl)) (lex_9_45_prefix s) (positive_select s 45) (lex_9_45_image s)

theorem lex_9_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4135), (Sat.Literal.pos 45), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation9 45 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4135) (Sat.Literal.pos 45) (Sat.Literal.pos 105) (lex_9_45_prefix s) (positive_select s 45) (lex_9_45_image s)

theorem lex_9_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4136), (Sat.Literal.pos 4135)] :=
  (lex_9_45_gate s).prop _ (List.Mem.head _)

theorem lex_9_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4136), (Sat.Literal.neg 45), (Sat.Literal.pos 105)] :=
  (lex_9_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4136), (Sat.Literal.pos 45), (Sat.Literal.neg 105)] :=
  (lex_9_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4135), (Sat.Literal.neg 45), (Sat.Literal.neg 105), (Sat.Literal.pos 4136)] :=
  (lex_9_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4135), (Sat.Literal.pos 45), (Sat.Literal.pos 105), (Sat.Literal.pos 4136)] :=
  (lex_9_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4136) = lexBefore s permutation9 44 := by
  exact (positive_lex_of_descriptor s 4136 permutation9 45 (by rfl)).trans ((lex_skipped s permutation9 44 45 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation9 44) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation9 44 by rw [image9_eq]; rfl))

theorem lex_9_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4137) (Sat.Literal.pos 4136) (Sat.Literal.pos 44) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation9 44 (assignment s)
    (Sat.Literal.pos 4137) (Sat.Literal.pos 4136) (Sat.Literal.pos 44) (Sat.Literal.pos 97) (positive_of_descriptor s 4137 (.lex permutation9 44) (by rfl)) (lex_9_44_prefix s) (positive_select s 44) (lex_9_44_image s)

theorem lex_9_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4136), (Sat.Literal.pos 44), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation9 44 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4136) (Sat.Literal.pos 44) (Sat.Literal.pos 97) (lex_9_44_prefix s) (positive_select s 44) (lex_9_44_image s)

theorem lex_9_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4137), (Sat.Literal.pos 4136)] :=
  (lex_9_44_gate s).prop _ (List.Mem.head _)

theorem lex_9_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4137), (Sat.Literal.neg 44), (Sat.Literal.pos 97)] :=
  (lex_9_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4137), (Sat.Literal.pos 44), (Sat.Literal.neg 97)] :=
  (lex_9_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4136), (Sat.Literal.neg 44), (Sat.Literal.neg 97), (Sat.Literal.pos 4137)] :=
  (lex_9_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4136), (Sat.Literal.pos 44), (Sat.Literal.pos 97), (Sat.Literal.pos 4137)] :=
  (lex_9_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4137) = lexBefore s permutation9 43 := by
  exact (positive_lex_of_descriptor s 4137 permutation9 44 (by rfl)).trans ((lex_skipped s permutation9 43 44 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation9 43) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation9 43 by rw [image9_eq]; rfl))

theorem lex_9_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4138) (Sat.Literal.pos 4137) (Sat.Literal.pos 43) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation9 43 (assignment s)
    (Sat.Literal.pos 4138) (Sat.Literal.pos 4137) (Sat.Literal.pos 43) (Sat.Literal.pos 89) (positive_of_descriptor s 4138 (.lex permutation9 43) (by rfl)) (lex_9_43_prefix s) (positive_select s 43) (lex_9_43_image s)

theorem lex_9_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4137), (Sat.Literal.pos 43), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation9 43 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4137) (Sat.Literal.pos 43) (Sat.Literal.pos 89) (lex_9_43_prefix s) (positive_select s 43) (lex_9_43_image s)

theorem lex_9_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4138), (Sat.Literal.pos 4137)] :=
  (lex_9_43_gate s).prop _ (List.Mem.head _)

theorem lex_9_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4138), (Sat.Literal.neg 43), (Sat.Literal.pos 89)] :=
  (lex_9_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4138), (Sat.Literal.pos 43), (Sat.Literal.neg 89)] :=
  (lex_9_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4137), (Sat.Literal.neg 43), (Sat.Literal.neg 89), (Sat.Literal.pos 4138)] :=
  (lex_9_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4137), (Sat.Literal.pos 43), (Sat.Literal.pos 89), (Sat.Literal.pos 4138)] :=
  (lex_9_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4138) = lexBefore s permutation9 42 := by
  exact (positive_lex_of_descriptor s 4138 permutation9 43 (by rfl)).trans ((lex_skipped s permutation9 42 43 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation9 42) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation9 42 by rw [image9_eq]; rfl))

theorem lex_9_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4139) (Sat.Literal.pos 4138) (Sat.Literal.pos 42) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation9 42 (assignment s)
    (Sat.Literal.pos 4139) (Sat.Literal.pos 4138) (Sat.Literal.pos 42) (Sat.Literal.pos 81) (positive_of_descriptor s 4139 (.lex permutation9 42) (by rfl)) (lex_9_42_prefix s) (positive_select s 42) (lex_9_42_image s)

theorem lex_9_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4138), (Sat.Literal.pos 42), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation9 42 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4138) (Sat.Literal.pos 42) (Sat.Literal.pos 81) (lex_9_42_prefix s) (positive_select s 42) (lex_9_42_image s)

theorem lex_9_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4139), (Sat.Literal.pos 4138)] :=
  (lex_9_42_gate s).prop _ (List.Mem.head _)

theorem lex_9_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4139), (Sat.Literal.neg 42), (Sat.Literal.pos 81)] :=
  (lex_9_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4139), (Sat.Literal.pos 42), (Sat.Literal.neg 81)] :=
  (lex_9_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4138), (Sat.Literal.neg 42), (Sat.Literal.neg 81), (Sat.Literal.pos 4139)] :=
  (lex_9_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4138), (Sat.Literal.pos 42), (Sat.Literal.pos 81), (Sat.Literal.pos 4139)] :=
  (lex_9_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4139) = lexBefore s permutation9 41 := by
  exact (positive_lex_of_descriptor s 4139 permutation9 42 (by rfl)).trans ((lex_skipped s permutation9 41 42 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation9 41) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation9 41 by rw [image9_eq]; rfl))

theorem lex_9_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4140) (Sat.Literal.pos 4139) (Sat.Literal.pos 41) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation9 41 (assignment s)
    (Sat.Literal.pos 4140) (Sat.Literal.pos 4139) (Sat.Literal.pos 41) (Sat.Literal.pos 73) (positive_of_descriptor s 4140 (.lex permutation9 41) (by rfl)) (lex_9_41_prefix s) (positive_select s 41) (lex_9_41_image s)

theorem lex_9_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4139), (Sat.Literal.pos 41), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation9 41 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4139) (Sat.Literal.pos 41) (Sat.Literal.pos 73) (lex_9_41_prefix s) (positive_select s 41) (lex_9_41_image s)

theorem lex_9_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4140), (Sat.Literal.pos 4139)] :=
  (lex_9_41_gate s).prop _ (List.Mem.head _)

theorem lex_9_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4140), (Sat.Literal.neg 41), (Sat.Literal.pos 73)] :=
  (lex_9_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4140), (Sat.Literal.pos 41), (Sat.Literal.neg 73)] :=
  (lex_9_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4139), (Sat.Literal.neg 41), (Sat.Literal.neg 73), (Sat.Literal.pos 4140)] :=
  (lex_9_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4139), (Sat.Literal.pos 41), (Sat.Literal.pos 73), (Sat.Literal.pos 4140)] :=
  (lex_9_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4140) = lexBefore s permutation9 40 := by
  exact (positive_lex_of_descriptor s 4140 permutation9 41 (by rfl)).trans ((lex_skipped s permutation9 40 41 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation9 40) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation9 40 by rw [image9_eq]; rfl))

theorem lex_9_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4141) (Sat.Literal.pos 4140) (Sat.Literal.pos 40) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation9 40 (assignment s)
    (Sat.Literal.pos 4141) (Sat.Literal.pos 4140) (Sat.Literal.pos 40) (Sat.Literal.pos 65) (positive_of_descriptor s 4141 (.lex permutation9 40) (by rfl)) (lex_9_40_prefix s) (positive_select s 40) (lex_9_40_image s)

theorem lex_9_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4140), (Sat.Literal.pos 40), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation9 40 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4140) (Sat.Literal.pos 40) (Sat.Literal.pos 65) (lex_9_40_prefix s) (positive_select s 40) (lex_9_40_image s)

theorem lex_9_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4141), (Sat.Literal.pos 4140)] :=
  (lex_9_40_gate s).prop _ (List.Mem.head _)

theorem lex_9_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4141), (Sat.Literal.neg 40), (Sat.Literal.pos 65)] :=
  (lex_9_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4141), (Sat.Literal.pos 40), (Sat.Literal.neg 65)] :=
  (lex_9_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4140), (Sat.Literal.neg 40), (Sat.Literal.neg 65), (Sat.Literal.pos 4141)] :=
  (lex_9_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4140), (Sat.Literal.pos 40), (Sat.Literal.pos 65), (Sat.Literal.pos 4141)] :=
  (lex_9_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4141) = lexBefore s permutation9 39 := by
  exact (positive_lex_of_descriptor s 4141 permutation9 40 (by rfl)).trans ((lex_skipped s permutation9 39 40 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation9 39) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation9 39 by rw [image9_eq]; rfl))

theorem lex_9_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4142) (Sat.Literal.pos 4141) (Sat.Literal.pos 39) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation9 39 (assignment s)
    (Sat.Literal.pos 4142) (Sat.Literal.pos 4141) (Sat.Literal.pos 39) (Sat.Literal.pos 57) (positive_of_descriptor s 4142 (.lex permutation9 39) (by rfl)) (lex_9_39_prefix s) (positive_select s 39) (lex_9_39_image s)

theorem lex_9_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4141), (Sat.Literal.pos 39), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation9 39 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4141) (Sat.Literal.pos 39) (Sat.Literal.pos 57) (lex_9_39_prefix s) (positive_select s 39) (lex_9_39_image s)

theorem lex_9_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4142), (Sat.Literal.pos 4141)] :=
  (lex_9_39_gate s).prop _ (List.Mem.head _)

theorem lex_9_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4142), (Sat.Literal.neg 39), (Sat.Literal.pos 57)] :=
  (lex_9_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4142), (Sat.Literal.pos 39), (Sat.Literal.neg 57)] :=
  (lex_9_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4141), (Sat.Literal.neg 39), (Sat.Literal.neg 57), (Sat.Literal.pos 4142)] :=
  (lex_9_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4141), (Sat.Literal.pos 39), (Sat.Literal.pos 57), (Sat.Literal.pos 4142)] :=
  (lex_9_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4142) = lexBefore s permutation9 38 := by
  exact (positive_lex_of_descriptor s 4142 permutation9 39 (by rfl)).trans ((lex_skipped s permutation9 38 39 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation9 38) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation9 38 by rw [image9_eq]; rfl))

theorem lex_9_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4143) (Sat.Literal.pos 4142) (Sat.Literal.pos 38) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation9 38 (assignment s)
    (Sat.Literal.pos 4143) (Sat.Literal.pos 4142) (Sat.Literal.pos 38) (Sat.Literal.pos 49) (positive_of_descriptor s 4143 (.lex permutation9 38) (by rfl)) (lex_9_38_prefix s) (positive_select s 38) (lex_9_38_image s)

theorem lex_9_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4142), (Sat.Literal.pos 38), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation9 38 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4142) (Sat.Literal.pos 38) (Sat.Literal.pos 49) (lex_9_38_prefix s) (positive_select s 38) (lex_9_38_image s)

theorem lex_9_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4143), (Sat.Literal.pos 4142)] :=
  (lex_9_38_gate s).prop _ (List.Mem.head _)

theorem lex_9_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4143), (Sat.Literal.neg 38), (Sat.Literal.pos 49)] :=
  (lex_9_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4143), (Sat.Literal.pos 38), (Sat.Literal.neg 49)] :=
  (lex_9_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4142), (Sat.Literal.neg 38), (Sat.Literal.neg 49), (Sat.Literal.pos 4143)] :=
  (lex_9_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4142), (Sat.Literal.pos 38), (Sat.Literal.pos 49), (Sat.Literal.pos 4143)] :=
  (lex_9_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4143) = lexBefore s permutation9 37 := by
  exact (positive_lex_of_descriptor s 4143 permutation9 38 (by rfl)).trans ((lex_skipped s permutation9 37 38 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 41) = s (permuteMask permutation9 37) := by
  exact (positive_select s 41).trans (congrArg s (show (41 : Fin 256) = permuteMask permutation9 37 by rw [image9_eq]; rfl))

theorem lex_9_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4144) (Sat.Literal.pos 4143) (Sat.Literal.pos 37) (Sat.Literal.pos 41)) := by
  exact equality_gate s permutation9 37 (assignment s)
    (Sat.Literal.pos 4144) (Sat.Literal.pos 4143) (Sat.Literal.pos 37) (Sat.Literal.pos 41) (positive_of_descriptor s 4144 (.lex permutation9 37) (by rfl)) (lex_9_37_prefix s) (positive_select s 37) (lex_9_37_image s)

theorem lex_9_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4143), (Sat.Literal.pos 37), (Sat.Literal.neg 41)] := by
  exact comparison_gate s permutation9 37 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4143) (Sat.Literal.pos 37) (Sat.Literal.pos 41) (lex_9_37_prefix s) (positive_select s 37) (lex_9_37_image s)

theorem lex_9_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4144), (Sat.Literal.pos 4143)] :=
  (lex_9_37_gate s).prop _ (List.Mem.head _)

theorem lex_9_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4144), (Sat.Literal.neg 37), (Sat.Literal.pos 41)] :=
  (lex_9_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4144), (Sat.Literal.pos 37), (Sat.Literal.neg 41)] :=
  (lex_9_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4143), (Sat.Literal.neg 37), (Sat.Literal.neg 41), (Sat.Literal.pos 4144)] :=
  (lex_9_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4143), (Sat.Literal.pos 37), (Sat.Literal.pos 41), (Sat.Literal.pos 4144)] :=
  (lex_9_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4144) = lexBefore s permutation9 36 := by
  exact (positive_lex_of_descriptor s 4144 permutation9 37 (by rfl)).trans ((lex_skipped s permutation9 36 37 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 33) = s (permuteMask permutation9 36) := by
  exact (positive_select s 33).trans (congrArg s (show (33 : Fin 256) = permuteMask permutation9 36 by rw [image9_eq]; rfl))

theorem lex_9_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4145) (Sat.Literal.pos 4144) (Sat.Literal.pos 36) (Sat.Literal.pos 33)) := by
  exact equality_gate s permutation9 36 (assignment s)
    (Sat.Literal.pos 4145) (Sat.Literal.pos 4144) (Sat.Literal.pos 36) (Sat.Literal.pos 33) (positive_of_descriptor s 4145 (.lex permutation9 36) (by rfl)) (lex_9_36_prefix s) (positive_select s 36) (lex_9_36_image s)

theorem lex_9_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4144), (Sat.Literal.pos 36), (Sat.Literal.neg 33)] := by
  exact comparison_gate s permutation9 36 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4144) (Sat.Literal.pos 36) (Sat.Literal.pos 33) (lex_9_36_prefix s) (positive_select s 36) (lex_9_36_image s)

theorem lex_9_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4145), (Sat.Literal.pos 4144)] :=
  (lex_9_36_gate s).prop _ (List.Mem.head _)

theorem lex_9_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4145), (Sat.Literal.neg 36), (Sat.Literal.pos 33)] :=
  (lex_9_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4145), (Sat.Literal.pos 36), (Sat.Literal.neg 33)] :=
  (lex_9_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4144), (Sat.Literal.neg 36), (Sat.Literal.neg 33), (Sat.Literal.pos 4145)] :=
  (lex_9_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4144), (Sat.Literal.pos 36), (Sat.Literal.pos 33), (Sat.Literal.pos 4145)] :=
  (lex_9_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4145) = lexBefore s permutation9 35 := by
  exact (positive_lex_of_descriptor s 4145 permutation9 36 (by rfl)).trans ((lex_skipped s permutation9 35 36 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation9 35) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation9 35 by rw [image9_eq]; rfl))

theorem lex_9_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4146) (Sat.Literal.pos 4145) (Sat.Literal.pos 35) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation9 35 (assignment s)
    (Sat.Literal.pos 4146) (Sat.Literal.pos 4145) (Sat.Literal.pos 35) (Sat.Literal.pos 25) (positive_of_descriptor s 4146 (.lex permutation9 35) (by rfl)) (lex_9_35_prefix s) (positive_select s 35) (lex_9_35_image s)

theorem lex_9_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4145), (Sat.Literal.pos 35), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation9 35 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4145) (Sat.Literal.pos 35) (Sat.Literal.pos 25) (lex_9_35_prefix s) (positive_select s 35) (lex_9_35_image s)

theorem lex_9_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4146), (Sat.Literal.pos 4145)] :=
  (lex_9_35_gate s).prop _ (List.Mem.head _)

theorem lex_9_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4146), (Sat.Literal.neg 35), (Sat.Literal.pos 25)] :=
  (lex_9_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4146), (Sat.Literal.pos 35), (Sat.Literal.neg 25)] :=
  (lex_9_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4145), (Sat.Literal.neg 35), (Sat.Literal.neg 25), (Sat.Literal.pos 4146)] :=
  (lex_9_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4145), (Sat.Literal.pos 35), (Sat.Literal.pos 25), (Sat.Literal.pos 4146)] :=
  (lex_9_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4146) = lexBefore s permutation9 34 := by
  exact (positive_lex_of_descriptor s 4146 permutation9 35 (by rfl)).trans ((lex_skipped s permutation9 34 35 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation9 34) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation9 34 by rw [image9_eq]; rfl))

theorem lex_9_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4147) (Sat.Literal.pos 4146) (Sat.Literal.pos 34) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation9 34 (assignment s)
    (Sat.Literal.pos 4147) (Sat.Literal.pos 4146) (Sat.Literal.pos 34) (Sat.Literal.pos 17) (positive_of_descriptor s 4147 (.lex permutation9 34) (by rfl)) (lex_9_34_prefix s) (positive_select s 34) (lex_9_34_image s)

theorem lex_9_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4146), (Sat.Literal.pos 34), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation9 34 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4146) (Sat.Literal.pos 34) (Sat.Literal.pos 17) (lex_9_34_prefix s) (positive_select s 34) (lex_9_34_image s)

theorem lex_9_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4147), (Sat.Literal.pos 4146)] :=
  (lex_9_34_gate s).prop _ (List.Mem.head _)

theorem lex_9_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4147), (Sat.Literal.neg 34), (Sat.Literal.pos 17)] :=
  (lex_9_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4147), (Sat.Literal.pos 34), (Sat.Literal.neg 17)] :=
  (lex_9_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4146), (Sat.Literal.neg 34), (Sat.Literal.neg 17), (Sat.Literal.pos 4147)] :=
  (lex_9_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4146), (Sat.Literal.pos 34), (Sat.Literal.pos 17), (Sat.Literal.pos 4147)] :=
  (lex_9_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4147) = lexBefore s permutation9 33 := by
  exact (positive_lex_of_descriptor s 4147 permutation9 34 (by rfl)).trans ((lex_skipped s permutation9 33 34 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation9 33) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation9 33 by rw [image9_eq]; rfl))

theorem lex_9_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4148) (Sat.Literal.pos 4147) (Sat.Literal.pos 33) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation9 33 (assignment s)
    (Sat.Literal.pos 4148) (Sat.Literal.pos 4147) (Sat.Literal.pos 33) (Sat.Literal.pos 9) (positive_of_descriptor s 4148 (.lex permutation9 33) (by rfl)) (lex_9_33_prefix s) (positive_select s 33) (lex_9_33_image s)

theorem lex_9_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4147), (Sat.Literal.pos 33), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation9 33 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4147) (Sat.Literal.pos 33) (Sat.Literal.pos 9) (lex_9_33_prefix s) (positive_select s 33) (lex_9_33_image s)

theorem lex_9_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4148), (Sat.Literal.pos 4147)] :=
  (lex_9_33_gate s).prop _ (List.Mem.head _)

theorem lex_9_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4148), (Sat.Literal.neg 33), (Sat.Literal.pos 9)] :=
  (lex_9_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4148), (Sat.Literal.pos 33), (Sat.Literal.neg 9)] :=
  (lex_9_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4147), (Sat.Literal.neg 33), (Sat.Literal.neg 9), (Sat.Literal.pos 4148)] :=
  (lex_9_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4147), (Sat.Literal.pos 33), (Sat.Literal.pos 9), (Sat.Literal.pos 4148)] :=
  (lex_9_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4148) = lexBefore s permutation9 32 := by
  exact (positive_lex_of_descriptor s 4148 permutation9 33 (by rfl)).trans ((lex_skipped s permutation9 32 33 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation9 32) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation9 32 by rw [image9_eq]; rfl))

theorem lex_9_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4149) (Sat.Literal.pos 4148) (Sat.Literal.pos 32) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation9 32 (assignment s)
    (Sat.Literal.pos 4149) (Sat.Literal.pos 4148) (Sat.Literal.pos 32) (Sat.Literal.pos 1) (positive_of_descriptor s 4149 (.lex permutation9 32) (by rfl)) (lex_9_32_prefix s) (positive_select s 32) (lex_9_32_image s)

theorem lex_9_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4148), (Sat.Literal.pos 32), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation9 32 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4148) (Sat.Literal.pos 32) (Sat.Literal.pos 1) (lex_9_32_prefix s) (positive_select s 32) (lex_9_32_image s)

theorem lex_9_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4149), (Sat.Literal.pos 4148)] :=
  (lex_9_32_gate s).prop _ (List.Mem.head _)

theorem lex_9_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4149), (Sat.Literal.neg 32), (Sat.Literal.pos 1)] :=
  (lex_9_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4149), (Sat.Literal.pos 32), (Sat.Literal.neg 1)] :=
  (lex_9_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4148), (Sat.Literal.neg 32), (Sat.Literal.neg 1), (Sat.Literal.pos 4149)] :=
  (lex_9_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4148), (Sat.Literal.pos 32), (Sat.Literal.pos 1), (Sat.Literal.pos 4149)] :=
  (lex_9_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4149) = lexBefore s permutation9 31 := by
  exact (positive_lex_of_descriptor s 4149 permutation9 32 (by rfl)).trans ((lex_skipped s permutation9 31 32 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation9 31) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation9 31 by rw [image9_eq]; rfl))

theorem lex_9_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4150) (Sat.Literal.pos 4149) (Sat.Literal.pos 31) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation9 31 (assignment s)
    (Sat.Literal.pos 4150) (Sat.Literal.pos 4149) (Sat.Literal.pos 31) (Sat.Literal.pos 248) (positive_of_descriptor s 4150 (.lex permutation9 31) (by rfl)) (lex_9_31_prefix s) (positive_select s 31) (lex_9_31_image s)

theorem lex_9_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4149), (Sat.Literal.pos 31), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation9 31 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4149) (Sat.Literal.pos 31) (Sat.Literal.pos 248) (lex_9_31_prefix s) (positive_select s 31) (lex_9_31_image s)

theorem lex_9_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4150), (Sat.Literal.pos 4149)] :=
  (lex_9_31_gate s).prop _ (List.Mem.head _)

theorem lex_9_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4150), (Sat.Literal.neg 31), (Sat.Literal.pos 248)] :=
  (lex_9_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4150), (Sat.Literal.pos 31), (Sat.Literal.neg 248)] :=
  (lex_9_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4149), (Sat.Literal.neg 31), (Sat.Literal.neg 248), (Sat.Literal.pos 4150)] :=
  (lex_9_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4149), (Sat.Literal.pos 31), (Sat.Literal.pos 248), (Sat.Literal.pos 4150)] :=
  (lex_9_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4150) = lexBefore s permutation9 30 := by
  exact (positive_lex_of_descriptor s 4150 permutation9 31 (by rfl)).trans ((lex_skipped s permutation9 30 31 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation9 30) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation9 30 by rw [image9_eq]; rfl))

theorem lex_9_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4151) (Sat.Literal.pos 4150) (Sat.Literal.pos 30) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation9 30 (assignment s)
    (Sat.Literal.pos 4151) (Sat.Literal.pos 4150) (Sat.Literal.pos 30) (Sat.Literal.pos 240) (positive_of_descriptor s 4151 (.lex permutation9 30) (by rfl)) (lex_9_30_prefix s) (positive_select s 30) (lex_9_30_image s)

theorem lex_9_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4150), (Sat.Literal.pos 30), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation9 30 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4150) (Sat.Literal.pos 30) (Sat.Literal.pos 240) (lex_9_30_prefix s) (positive_select s 30) (lex_9_30_image s)

theorem lex_9_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4151), (Sat.Literal.pos 4150)] :=
  (lex_9_30_gate s).prop _ (List.Mem.head _)

theorem lex_9_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4151), (Sat.Literal.neg 30), (Sat.Literal.pos 240)] :=
  (lex_9_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4151), (Sat.Literal.pos 30), (Sat.Literal.neg 240)] :=
  (lex_9_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4150), (Sat.Literal.neg 30), (Sat.Literal.neg 240), (Sat.Literal.pos 4151)] :=
  (lex_9_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4150), (Sat.Literal.pos 30), (Sat.Literal.pos 240), (Sat.Literal.pos 4151)] :=
  (lex_9_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4151) = lexBefore s permutation9 29 := by
  exact (positive_lex_of_descriptor s 4151 permutation9 30 (by rfl)).trans ((lex_skipped s permutation9 29 30 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation9 29) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation9 29 by rw [image9_eq]; rfl))

theorem lex_9_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4152) (Sat.Literal.pos 4151) (Sat.Literal.pos 29) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation9 29 (assignment s)
    (Sat.Literal.pos 4152) (Sat.Literal.pos 4151) (Sat.Literal.pos 29) (Sat.Literal.pos 232) (positive_of_descriptor s 4152 (.lex permutation9 29) (by rfl)) (lex_9_29_prefix s) (positive_select s 29) (lex_9_29_image s)

theorem lex_9_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4151), (Sat.Literal.pos 29), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation9 29 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4151) (Sat.Literal.pos 29) (Sat.Literal.pos 232) (lex_9_29_prefix s) (positive_select s 29) (lex_9_29_image s)

theorem lex_9_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4152), (Sat.Literal.pos 4151)] :=
  (lex_9_29_gate s).prop _ (List.Mem.head _)

theorem lex_9_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4152), (Sat.Literal.neg 29), (Sat.Literal.pos 232)] :=
  (lex_9_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4152), (Sat.Literal.pos 29), (Sat.Literal.neg 232)] :=
  (lex_9_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4151), (Sat.Literal.neg 29), (Sat.Literal.neg 232), (Sat.Literal.pos 4152)] :=
  (lex_9_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4151), (Sat.Literal.pos 29), (Sat.Literal.pos 232), (Sat.Literal.pos 4152)] :=
  (lex_9_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4152) = lexBefore s permutation9 28 := by
  exact (positive_lex_of_descriptor s 4152 permutation9 29 (by rfl)).trans ((lex_skipped s permutation9 28 29 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation9 28) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation9 28 by rw [image9_eq]; rfl))

theorem lex_9_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4153) (Sat.Literal.pos 4152) (Sat.Literal.pos 28) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation9 28 (assignment s)
    (Sat.Literal.pos 4153) (Sat.Literal.pos 4152) (Sat.Literal.pos 28) (Sat.Literal.pos 224) (positive_of_descriptor s 4153 (.lex permutation9 28) (by rfl)) (lex_9_28_prefix s) (positive_select s 28) (lex_9_28_image s)

theorem lex_9_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4152), (Sat.Literal.pos 28), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation9 28 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4152) (Sat.Literal.pos 28) (Sat.Literal.pos 224) (lex_9_28_prefix s) (positive_select s 28) (lex_9_28_image s)

theorem lex_9_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4153), (Sat.Literal.pos 4152)] :=
  (lex_9_28_gate s).prop _ (List.Mem.head _)

theorem lex_9_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4153), (Sat.Literal.neg 28), (Sat.Literal.pos 224)] :=
  (lex_9_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4153), (Sat.Literal.pos 28), (Sat.Literal.neg 224)] :=
  (lex_9_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4152), (Sat.Literal.neg 28), (Sat.Literal.neg 224), (Sat.Literal.pos 4153)] :=
  (lex_9_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4152), (Sat.Literal.pos 28), (Sat.Literal.pos 224), (Sat.Literal.pos 4153)] :=
  (lex_9_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4153) = lexBefore s permutation9 27 := by
  exact (positive_lex_of_descriptor s 4153 permutation9 28 (by rfl)).trans ((lex_skipped s permutation9 27 28 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation9 27) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation9 27 by rw [image9_eq]; rfl))

theorem lex_9_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4154) (Sat.Literal.pos 4153) (Sat.Literal.pos 27) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation9 27 (assignment s)
    (Sat.Literal.pos 4154) (Sat.Literal.pos 4153) (Sat.Literal.pos 27) (Sat.Literal.pos 216) (positive_of_descriptor s 4154 (.lex permutation9 27) (by rfl)) (lex_9_27_prefix s) (positive_select s 27) (lex_9_27_image s)

theorem lex_9_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4153), (Sat.Literal.pos 27), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation9 27 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4153) (Sat.Literal.pos 27) (Sat.Literal.pos 216) (lex_9_27_prefix s) (positive_select s 27) (lex_9_27_image s)

theorem lex_9_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4154), (Sat.Literal.pos 4153)] :=
  (lex_9_27_gate s).prop _ (List.Mem.head _)

theorem lex_9_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4154), (Sat.Literal.neg 27), (Sat.Literal.pos 216)] :=
  (lex_9_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4154), (Sat.Literal.pos 27), (Sat.Literal.neg 216)] :=
  (lex_9_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4153), (Sat.Literal.neg 27), (Sat.Literal.neg 216), (Sat.Literal.pos 4154)] :=
  (lex_9_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4153), (Sat.Literal.pos 27), (Sat.Literal.pos 216), (Sat.Literal.pos 4154)] :=
  (lex_9_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4154) = lexBefore s permutation9 26 := by
  exact (positive_lex_of_descriptor s 4154 permutation9 27 (by rfl)).trans ((lex_skipped s permutation9 26 27 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation9 26) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation9 26 by rw [image9_eq]; rfl))

theorem lex_9_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4155) (Sat.Literal.pos 4154) (Sat.Literal.pos 26) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation9 26 (assignment s)
    (Sat.Literal.pos 4155) (Sat.Literal.pos 4154) (Sat.Literal.pos 26) (Sat.Literal.pos 208) (positive_of_descriptor s 4155 (.lex permutation9 26) (by rfl)) (lex_9_26_prefix s) (positive_select s 26) (lex_9_26_image s)

theorem lex_9_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4154), (Sat.Literal.pos 26), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation9 26 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4154) (Sat.Literal.pos 26) (Sat.Literal.pos 208) (lex_9_26_prefix s) (positive_select s 26) (lex_9_26_image s)

theorem lex_9_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4155), (Sat.Literal.pos 4154)] :=
  (lex_9_26_gate s).prop _ (List.Mem.head _)

theorem lex_9_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4155), (Sat.Literal.neg 26), (Sat.Literal.pos 208)] :=
  (lex_9_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4155), (Sat.Literal.pos 26), (Sat.Literal.neg 208)] :=
  (lex_9_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4154), (Sat.Literal.neg 26), (Sat.Literal.neg 208), (Sat.Literal.pos 4155)] :=
  (lex_9_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4154), (Sat.Literal.pos 26), (Sat.Literal.pos 208), (Sat.Literal.pos 4155)] :=
  (lex_9_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4155) = lexBefore s permutation9 25 := by
  exact (positive_lex_of_descriptor s 4155 permutation9 26 (by rfl)).trans ((lex_skipped s permutation9 25 26 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 200) = s (permuteMask permutation9 25) := by
  exact (positive_select s 200).trans (congrArg s (show (200 : Fin 256) = permuteMask permutation9 25 by rw [image9_eq]; rfl))

theorem lex_9_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4156) (Sat.Literal.pos 4155) (Sat.Literal.pos 25) (Sat.Literal.pos 200)) := by
  exact equality_gate s permutation9 25 (assignment s)
    (Sat.Literal.pos 4156) (Sat.Literal.pos 4155) (Sat.Literal.pos 25) (Sat.Literal.pos 200) (positive_of_descriptor s 4156 (.lex permutation9 25) (by rfl)) (lex_9_25_prefix s) (positive_select s 25) (lex_9_25_image s)

theorem lex_9_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4155), (Sat.Literal.pos 25), (Sat.Literal.neg 200)] := by
  exact comparison_gate s permutation9 25 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4155) (Sat.Literal.pos 25) (Sat.Literal.pos 200) (lex_9_25_prefix s) (positive_select s 25) (lex_9_25_image s)

theorem lex_9_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4156), (Sat.Literal.pos 4155)] :=
  (lex_9_25_gate s).prop _ (List.Mem.head _)

theorem lex_9_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4156), (Sat.Literal.neg 25), (Sat.Literal.pos 200)] :=
  (lex_9_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4156), (Sat.Literal.pos 25), (Sat.Literal.neg 200)] :=
  (lex_9_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4155), (Sat.Literal.neg 25), (Sat.Literal.neg 200), (Sat.Literal.pos 4156)] :=
  (lex_9_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4155), (Sat.Literal.pos 25), (Sat.Literal.pos 200), (Sat.Literal.pos 4156)] :=
  (lex_9_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4156) = lexBefore s permutation9 24 := by
  exact (positive_lex_of_descriptor s 4156 permutation9 25 (by rfl)).trans ((lex_skipped s permutation9 24 25 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 192) = s (permuteMask permutation9 24) := by
  exact (positive_select s 192).trans (congrArg s (show (192 : Fin 256) = permuteMask permutation9 24 by rw [image9_eq]; rfl))

theorem lex_9_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4157) (Sat.Literal.pos 4156) (Sat.Literal.pos 24) (Sat.Literal.pos 192)) := by
  exact equality_gate s permutation9 24 (assignment s)
    (Sat.Literal.pos 4157) (Sat.Literal.pos 4156) (Sat.Literal.pos 24) (Sat.Literal.pos 192) (positive_of_descriptor s 4157 (.lex permutation9 24) (by rfl)) (lex_9_24_prefix s) (positive_select s 24) (lex_9_24_image s)

theorem lex_9_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4156), (Sat.Literal.pos 24), (Sat.Literal.neg 192)] := by
  exact comparison_gate s permutation9 24 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4156) (Sat.Literal.pos 24) (Sat.Literal.pos 192) (lex_9_24_prefix s) (positive_select s 24) (lex_9_24_image s)

theorem lex_9_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4157), (Sat.Literal.pos 4156)] :=
  (lex_9_24_gate s).prop _ (List.Mem.head _)

theorem lex_9_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4157), (Sat.Literal.neg 24), (Sat.Literal.pos 192)] :=
  (lex_9_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4157), (Sat.Literal.pos 24), (Sat.Literal.neg 192)] :=
  (lex_9_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4156), (Sat.Literal.neg 24), (Sat.Literal.neg 192), (Sat.Literal.pos 4157)] :=
  (lex_9_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4156), (Sat.Literal.pos 24), (Sat.Literal.pos 192), (Sat.Literal.pos 4157)] :=
  (lex_9_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4157) = lexBefore s permutation9 23 := by
  exact (positive_lex_of_descriptor s 4157 permutation9 24 (by rfl)).trans ((lex_skipped s permutation9 23 24 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation9 23) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation9 23 by rw [image9_eq]; rfl))

theorem lex_9_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4158) (Sat.Literal.pos 4157) (Sat.Literal.pos 23) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation9 23 (assignment s)
    (Sat.Literal.pos 4158) (Sat.Literal.pos 4157) (Sat.Literal.pos 23) (Sat.Literal.pos 184) (positive_of_descriptor s 4158 (.lex permutation9 23) (by rfl)) (lex_9_23_prefix s) (positive_select s 23) (lex_9_23_image s)

theorem lex_9_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4157), (Sat.Literal.pos 23), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation9 23 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4157) (Sat.Literal.pos 23) (Sat.Literal.pos 184) (lex_9_23_prefix s) (positive_select s 23) (lex_9_23_image s)

theorem lex_9_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4158), (Sat.Literal.pos 4157)] :=
  (lex_9_23_gate s).prop _ (List.Mem.head _)

theorem lex_9_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4158), (Sat.Literal.neg 23), (Sat.Literal.pos 184)] :=
  (lex_9_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4158), (Sat.Literal.pos 23), (Sat.Literal.neg 184)] :=
  (lex_9_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4157), (Sat.Literal.neg 23), (Sat.Literal.neg 184), (Sat.Literal.pos 4158)] :=
  (lex_9_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4157), (Sat.Literal.pos 23), (Sat.Literal.pos 184), (Sat.Literal.pos 4158)] :=
  (lex_9_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4158) = lexBefore s permutation9 22 := by
  exact (positive_lex_of_descriptor s 4158 permutation9 23 (by rfl)).trans ((lex_skipped s permutation9 22 23 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation9 22) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation9 22 by rw [image9_eq]; rfl))

theorem lex_9_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4159) (Sat.Literal.pos 4158) (Sat.Literal.pos 22) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation9 22 (assignment s)
    (Sat.Literal.pos 4159) (Sat.Literal.pos 4158) (Sat.Literal.pos 22) (Sat.Literal.pos 176) (positive_of_descriptor s 4159 (.lex permutation9 22) (by rfl)) (lex_9_22_prefix s) (positive_select s 22) (lex_9_22_image s)

theorem lex_9_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4158), (Sat.Literal.pos 22), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation9 22 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4158) (Sat.Literal.pos 22) (Sat.Literal.pos 176) (lex_9_22_prefix s) (positive_select s 22) (lex_9_22_image s)

theorem lex_9_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4159), (Sat.Literal.pos 4158)] :=
  (lex_9_22_gate s).prop _ (List.Mem.head _)

theorem lex_9_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4159), (Sat.Literal.neg 22), (Sat.Literal.pos 176)] :=
  (lex_9_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4159), (Sat.Literal.pos 22), (Sat.Literal.neg 176)] :=
  (lex_9_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4158), (Sat.Literal.neg 22), (Sat.Literal.neg 176), (Sat.Literal.pos 4159)] :=
  (lex_9_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4158), (Sat.Literal.pos 22), (Sat.Literal.pos 176), (Sat.Literal.pos 4159)] :=
  (lex_9_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4159) = lexBefore s permutation9 21 := by
  exact (positive_lex_of_descriptor s 4159 permutation9 22 (by rfl)).trans ((lex_skipped s permutation9 21 22 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation9 21) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation9 21 by rw [image9_eq]; rfl))

theorem lex_9_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4160) (Sat.Literal.pos 4159) (Sat.Literal.pos 21) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation9 21 (assignment s)
    (Sat.Literal.pos 4160) (Sat.Literal.pos 4159) (Sat.Literal.pos 21) (Sat.Literal.pos 168) (positive_of_descriptor s 4160 (.lex permutation9 21) (by rfl)) (lex_9_21_prefix s) (positive_select s 21) (lex_9_21_image s)

theorem lex_9_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4159), (Sat.Literal.pos 21), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation9 21 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4159) (Sat.Literal.pos 21) (Sat.Literal.pos 168) (lex_9_21_prefix s) (positive_select s 21) (lex_9_21_image s)

theorem lex_9_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4160), (Sat.Literal.pos 4159)] :=
  (lex_9_21_gate s).prop _ (List.Mem.head _)

theorem lex_9_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4160), (Sat.Literal.neg 21), (Sat.Literal.pos 168)] :=
  (lex_9_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4160), (Sat.Literal.pos 21), (Sat.Literal.neg 168)] :=
  (lex_9_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4159), (Sat.Literal.neg 21), (Sat.Literal.neg 168), (Sat.Literal.pos 4160)] :=
  (lex_9_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4159), (Sat.Literal.pos 21), (Sat.Literal.pos 168), (Sat.Literal.pos 4160)] :=
  (lex_9_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4160) = lexBefore s permutation9 20 := by
  exact (positive_lex_of_descriptor s 4160 permutation9 21 (by rfl)).trans ((lex_skipped s permutation9 20 21 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation9 20) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation9 20 by rw [image9_eq]; rfl))

theorem lex_9_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4161) (Sat.Literal.pos 4160) (Sat.Literal.pos 20) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation9 20 (assignment s)
    (Sat.Literal.pos 4161) (Sat.Literal.pos 4160) (Sat.Literal.pos 20) (Sat.Literal.pos 160) (positive_of_descriptor s 4161 (.lex permutation9 20) (by rfl)) (lex_9_20_prefix s) (positive_select s 20) (lex_9_20_image s)

theorem lex_9_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4160), (Sat.Literal.pos 20), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation9 20 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4160) (Sat.Literal.pos 20) (Sat.Literal.pos 160) (lex_9_20_prefix s) (positive_select s 20) (lex_9_20_image s)

theorem lex_9_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4161), (Sat.Literal.pos 4160)] :=
  (lex_9_20_gate s).prop _ (List.Mem.head _)

theorem lex_9_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4161), (Sat.Literal.neg 20), (Sat.Literal.pos 160)] :=
  (lex_9_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4161), (Sat.Literal.pos 20), (Sat.Literal.neg 160)] :=
  (lex_9_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4160), (Sat.Literal.neg 20), (Sat.Literal.neg 160), (Sat.Literal.pos 4161)] :=
  (lex_9_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4160), (Sat.Literal.pos 20), (Sat.Literal.pos 160), (Sat.Literal.pos 4161)] :=
  (lex_9_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4161) = lexBefore s permutation9 19 := by
  exact (positive_lex_of_descriptor s 4161 permutation9 20 (by rfl)).trans ((lex_skipped s permutation9 19 20 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation9 19) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation9 19 by rw [image9_eq]; rfl))

theorem lex_9_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4162) (Sat.Literal.pos 4161) (Sat.Literal.pos 19) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation9 19 (assignment s)
    (Sat.Literal.pos 4162) (Sat.Literal.pos 4161) (Sat.Literal.pos 19) (Sat.Literal.pos 152) (positive_of_descriptor s 4162 (.lex permutation9 19) (by rfl)) (lex_9_19_prefix s) (positive_select s 19) (lex_9_19_image s)

theorem lex_9_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4161), (Sat.Literal.pos 19), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation9 19 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4161) (Sat.Literal.pos 19) (Sat.Literal.pos 152) (lex_9_19_prefix s) (positive_select s 19) (lex_9_19_image s)

theorem lex_9_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4162), (Sat.Literal.pos 4161)] :=
  (lex_9_19_gate s).prop _ (List.Mem.head _)

theorem lex_9_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4162), (Sat.Literal.neg 19), (Sat.Literal.pos 152)] :=
  (lex_9_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4162), (Sat.Literal.pos 19), (Sat.Literal.neg 152)] :=
  (lex_9_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4161), (Sat.Literal.neg 19), (Sat.Literal.neg 152), (Sat.Literal.pos 4162)] :=
  (lex_9_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4161), (Sat.Literal.pos 19), (Sat.Literal.pos 152), (Sat.Literal.pos 4162)] :=
  (lex_9_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4162) = lexBefore s permutation9 18 := by
  exact (positive_lex_of_descriptor s 4162 permutation9 19 (by rfl)).trans ((lex_skipped s permutation9 18 19 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation9 18) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation9 18 by rw [image9_eq]; rfl))

theorem lex_9_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4163) (Sat.Literal.pos 4162) (Sat.Literal.pos 18) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation9 18 (assignment s)
    (Sat.Literal.pos 4163) (Sat.Literal.pos 4162) (Sat.Literal.pos 18) (Sat.Literal.pos 144) (positive_of_descriptor s 4163 (.lex permutation9 18) (by rfl)) (lex_9_18_prefix s) (positive_select s 18) (lex_9_18_image s)

theorem lex_9_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4162), (Sat.Literal.pos 18), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation9 18 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4162) (Sat.Literal.pos 18) (Sat.Literal.pos 144) (lex_9_18_prefix s) (positive_select s 18) (lex_9_18_image s)

theorem lex_9_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4163), (Sat.Literal.pos 4162)] :=
  (lex_9_18_gate s).prop _ (List.Mem.head _)

theorem lex_9_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4163), (Sat.Literal.neg 18), (Sat.Literal.pos 144)] :=
  (lex_9_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4163), (Sat.Literal.pos 18), (Sat.Literal.neg 144)] :=
  (lex_9_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4162), (Sat.Literal.neg 18), (Sat.Literal.neg 144), (Sat.Literal.pos 4163)] :=
  (lex_9_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4162), (Sat.Literal.pos 18), (Sat.Literal.pos 144), (Sat.Literal.pos 4163)] :=
  (lex_9_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4163) = lexBefore s permutation9 17 := by
  exact (positive_lex_of_descriptor s 4163 permutation9 18 (by rfl)).trans ((lex_skipped s permutation9 17 18 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation9 17) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation9 17 by rw [image9_eq]; rfl))

theorem lex_9_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4164) (Sat.Literal.pos 4163) (Sat.Literal.pos 17) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation9 17 (assignment s)
    (Sat.Literal.pos 4164) (Sat.Literal.pos 4163) (Sat.Literal.pos 17) (Sat.Literal.pos 136) (positive_of_descriptor s 4164 (.lex permutation9 17) (by rfl)) (lex_9_17_prefix s) (positive_select s 17) (lex_9_17_image s)

theorem lex_9_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4163), (Sat.Literal.pos 17), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation9 17 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4163) (Sat.Literal.pos 17) (Sat.Literal.pos 136) (lex_9_17_prefix s) (positive_select s 17) (lex_9_17_image s)

theorem lex_9_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4164), (Sat.Literal.pos 4163)] :=
  (lex_9_17_gate s).prop _ (List.Mem.head _)

theorem lex_9_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4164), (Sat.Literal.neg 17), (Sat.Literal.pos 136)] :=
  (lex_9_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4164), (Sat.Literal.pos 17), (Sat.Literal.neg 136)] :=
  (lex_9_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4163), (Sat.Literal.neg 17), (Sat.Literal.neg 136), (Sat.Literal.pos 4164)] :=
  (lex_9_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4163), (Sat.Literal.pos 17), (Sat.Literal.pos 136), (Sat.Literal.pos 4164)] :=
  (lex_9_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4164) = lexBefore s permutation9 16 := by
  exact (positive_lex_of_descriptor s 4164 permutation9 17 (by rfl)).trans ((lex_skipped s permutation9 16 17 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation9 16) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation9 16 by rw [image9_eq]; rfl))

theorem lex_9_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4165) (Sat.Literal.pos 4164) (Sat.Literal.pos 16) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation9 16 (assignment s)
    (Sat.Literal.pos 4165) (Sat.Literal.pos 4164) (Sat.Literal.pos 16) (Sat.Literal.pos 128) (positive_of_descriptor s 4165 (.lex permutation9 16) (by rfl)) (lex_9_16_prefix s) (positive_select s 16) (lex_9_16_image s)

theorem lex_9_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4164), (Sat.Literal.pos 16), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation9 16 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4164) (Sat.Literal.pos 16) (Sat.Literal.pos 128) (lex_9_16_prefix s) (positive_select s 16) (lex_9_16_image s)

theorem lex_9_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4165), (Sat.Literal.pos 4164)] :=
  (lex_9_16_gate s).prop _ (List.Mem.head _)

theorem lex_9_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4165), (Sat.Literal.neg 16), (Sat.Literal.pos 128)] :=
  (lex_9_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4165), (Sat.Literal.pos 16), (Sat.Literal.neg 128)] :=
  (lex_9_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4164), (Sat.Literal.neg 16), (Sat.Literal.neg 128), (Sat.Literal.pos 4165)] :=
  (lex_9_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4164), (Sat.Literal.pos 16), (Sat.Literal.pos 128), (Sat.Literal.pos 4165)] :=
  (lex_9_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4165) = lexBefore s permutation9 15 := by
  exact (positive_lex_of_descriptor s 4165 permutation9 16 (by rfl)).trans ((lex_skipped s permutation9 15 16 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation9 15) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation9 15 by rw [image9_eq]; rfl))

theorem lex_9_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4166) (Sat.Literal.pos 4165) (Sat.Literal.pos 15) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation9 15 (assignment s)
    (Sat.Literal.pos 4166) (Sat.Literal.pos 4165) (Sat.Literal.pos 15) (Sat.Literal.pos 120) (positive_of_descriptor s 4166 (.lex permutation9 15) (by rfl)) (lex_9_15_prefix s) (positive_select s 15) (lex_9_15_image s)

theorem lex_9_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4165), (Sat.Literal.pos 15), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation9 15 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4165) (Sat.Literal.pos 15) (Sat.Literal.pos 120) (lex_9_15_prefix s) (positive_select s 15) (lex_9_15_image s)

theorem lex_9_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4166), (Sat.Literal.pos 4165)] :=
  (lex_9_15_gate s).prop _ (List.Mem.head _)

theorem lex_9_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4166), (Sat.Literal.neg 15), (Sat.Literal.pos 120)] :=
  (lex_9_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4166), (Sat.Literal.pos 15), (Sat.Literal.neg 120)] :=
  (lex_9_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4165), (Sat.Literal.neg 15), (Sat.Literal.neg 120), (Sat.Literal.pos 4166)] :=
  (lex_9_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4165), (Sat.Literal.pos 15), (Sat.Literal.pos 120), (Sat.Literal.pos 4166)] :=
  (lex_9_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4166) = lexBefore s permutation9 14 := by
  exact (positive_lex_of_descriptor s 4166 permutation9 15 (by rfl)).trans ((lex_skipped s permutation9 14 15 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation9 14) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation9 14 by rw [image9_eq]; rfl))

theorem lex_9_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4167) (Sat.Literal.pos 4166) (Sat.Literal.pos 14) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation9 14 (assignment s)
    (Sat.Literal.pos 4167) (Sat.Literal.pos 4166) (Sat.Literal.pos 14) (Sat.Literal.pos 112) (positive_of_descriptor s 4167 (.lex permutation9 14) (by rfl)) (lex_9_14_prefix s) (positive_select s 14) (lex_9_14_image s)

theorem lex_9_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4166), (Sat.Literal.pos 14), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation9 14 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4166) (Sat.Literal.pos 14) (Sat.Literal.pos 112) (lex_9_14_prefix s) (positive_select s 14) (lex_9_14_image s)

theorem lex_9_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4167), (Sat.Literal.pos 4166)] :=
  (lex_9_14_gate s).prop _ (List.Mem.head _)

theorem lex_9_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4167), (Sat.Literal.neg 14), (Sat.Literal.pos 112)] :=
  (lex_9_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4167), (Sat.Literal.pos 14), (Sat.Literal.neg 112)] :=
  (lex_9_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4166), (Sat.Literal.neg 14), (Sat.Literal.neg 112), (Sat.Literal.pos 4167)] :=
  (lex_9_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4166), (Sat.Literal.pos 14), (Sat.Literal.pos 112), (Sat.Literal.pos 4167)] :=
  (lex_9_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4167) = lexBefore s permutation9 13 := by
  exact (positive_lex_of_descriptor s 4167 permutation9 14 (by rfl)).trans ((lex_skipped s permutation9 13 14 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation9 13) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation9 13 by rw [image9_eq]; rfl))

theorem lex_9_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4168) (Sat.Literal.pos 4167) (Sat.Literal.pos 13) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation9 13 (assignment s)
    (Sat.Literal.pos 4168) (Sat.Literal.pos 4167) (Sat.Literal.pos 13) (Sat.Literal.pos 104) (positive_of_descriptor s 4168 (.lex permutation9 13) (by rfl)) (lex_9_13_prefix s) (positive_select s 13) (lex_9_13_image s)

theorem lex_9_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4167), (Sat.Literal.pos 13), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation9 13 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4167) (Sat.Literal.pos 13) (Sat.Literal.pos 104) (lex_9_13_prefix s) (positive_select s 13) (lex_9_13_image s)

theorem lex_9_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4168), (Sat.Literal.pos 4167)] :=
  (lex_9_13_gate s).prop _ (List.Mem.head _)

theorem lex_9_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4168), (Sat.Literal.neg 13), (Sat.Literal.pos 104)] :=
  (lex_9_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4168), (Sat.Literal.pos 13), (Sat.Literal.neg 104)] :=
  (lex_9_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4167), (Sat.Literal.neg 13), (Sat.Literal.neg 104), (Sat.Literal.pos 4168)] :=
  (lex_9_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4167), (Sat.Literal.pos 13), (Sat.Literal.pos 104), (Sat.Literal.pos 4168)] :=
  (lex_9_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4168) = lexBefore s permutation9 12 := by
  exact (positive_lex_of_descriptor s 4168 permutation9 13 (by rfl)).trans ((lex_skipped s permutation9 12 13 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation9 12) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation9 12 by rw [image9_eq]; rfl))

theorem lex_9_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4169) (Sat.Literal.pos 4168) (Sat.Literal.pos 12) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation9 12 (assignment s)
    (Sat.Literal.pos 4169) (Sat.Literal.pos 4168) (Sat.Literal.pos 12) (Sat.Literal.pos 96) (positive_of_descriptor s 4169 (.lex permutation9 12) (by rfl)) (lex_9_12_prefix s) (positive_select s 12) (lex_9_12_image s)

theorem lex_9_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4168), (Sat.Literal.pos 12), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation9 12 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4168) (Sat.Literal.pos 12) (Sat.Literal.pos 96) (lex_9_12_prefix s) (positive_select s 12) (lex_9_12_image s)

theorem lex_9_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4169), (Sat.Literal.pos 4168)] :=
  (lex_9_12_gate s).prop _ (List.Mem.head _)

theorem lex_9_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4169), (Sat.Literal.neg 12), (Sat.Literal.pos 96)] :=
  (lex_9_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4169), (Sat.Literal.pos 12), (Sat.Literal.neg 96)] :=
  (lex_9_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4168), (Sat.Literal.neg 12), (Sat.Literal.neg 96), (Sat.Literal.pos 4169)] :=
  (lex_9_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4168), (Sat.Literal.pos 12), (Sat.Literal.pos 96), (Sat.Literal.pos 4169)] :=
  (lex_9_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4169) = lexBefore s permutation9 11 := by
  exact (positive_lex_of_descriptor s 4169 permutation9 12 (by rfl)).trans ((lex_skipped s permutation9 11 12 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation9 11) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation9 11 by rw [image9_eq]; rfl))

theorem lex_9_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4170) (Sat.Literal.pos 4169) (Sat.Literal.pos 11) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation9 11 (assignment s)
    (Sat.Literal.pos 4170) (Sat.Literal.pos 4169) (Sat.Literal.pos 11) (Sat.Literal.pos 88) (positive_of_descriptor s 4170 (.lex permutation9 11) (by rfl)) (lex_9_11_prefix s) (positive_select s 11) (lex_9_11_image s)

theorem lex_9_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4169), (Sat.Literal.pos 11), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation9 11 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4169) (Sat.Literal.pos 11) (Sat.Literal.pos 88) (lex_9_11_prefix s) (positive_select s 11) (lex_9_11_image s)

theorem lex_9_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4170), (Sat.Literal.pos 4169)] :=
  (lex_9_11_gate s).prop _ (List.Mem.head _)

theorem lex_9_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4170), (Sat.Literal.neg 11), (Sat.Literal.pos 88)] :=
  (lex_9_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4170), (Sat.Literal.pos 11), (Sat.Literal.neg 88)] :=
  (lex_9_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4169), (Sat.Literal.neg 11), (Sat.Literal.neg 88), (Sat.Literal.pos 4170)] :=
  (lex_9_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4169), (Sat.Literal.pos 11), (Sat.Literal.pos 88), (Sat.Literal.pos 4170)] :=
  (lex_9_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4170) = lexBefore s permutation9 10 := by
  exact (positive_lex_of_descriptor s 4170 permutation9 11 (by rfl)).trans ((lex_skipped s permutation9 10 11 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation9 10) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation9 10 by rw [image9_eq]; rfl))

theorem lex_9_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4171) (Sat.Literal.pos 4170) (Sat.Literal.pos 10) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation9 10 (assignment s)
    (Sat.Literal.pos 4171) (Sat.Literal.pos 4170) (Sat.Literal.pos 10) (Sat.Literal.pos 80) (positive_of_descriptor s 4171 (.lex permutation9 10) (by rfl)) (lex_9_10_prefix s) (positive_select s 10) (lex_9_10_image s)

theorem lex_9_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4170), (Sat.Literal.pos 10), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation9 10 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4170) (Sat.Literal.pos 10) (Sat.Literal.pos 80) (lex_9_10_prefix s) (positive_select s 10) (lex_9_10_image s)

theorem lex_9_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4171), (Sat.Literal.pos 4170)] :=
  (lex_9_10_gate s).prop _ (List.Mem.head _)

theorem lex_9_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4171), (Sat.Literal.neg 10), (Sat.Literal.pos 80)] :=
  (lex_9_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4171), (Sat.Literal.pos 10), (Sat.Literal.neg 80)] :=
  (lex_9_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4170), (Sat.Literal.neg 10), (Sat.Literal.neg 80), (Sat.Literal.pos 4171)] :=
  (lex_9_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4170), (Sat.Literal.pos 10), (Sat.Literal.pos 80), (Sat.Literal.pos 4171)] :=
  (lex_9_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4171) = lexBefore s permutation9 9 := by
  exact (positive_lex_of_descriptor s 4171 permutation9 10 (by rfl)).trans ((lex_skipped s permutation9 9 10 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation9 9) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation9 9 by rw [image9_eq]; rfl))

theorem lex_9_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4172) (Sat.Literal.pos 4171) (Sat.Literal.pos 9) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation9 9 (assignment s)
    (Sat.Literal.pos 4172) (Sat.Literal.pos 4171) (Sat.Literal.pos 9) (Sat.Literal.pos 72) (positive_of_descriptor s 4172 (.lex permutation9 9) (by rfl)) (lex_9_9_prefix s) (positive_select s 9) (lex_9_9_image s)

theorem lex_9_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4171), (Sat.Literal.pos 9), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation9 9 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4171) (Sat.Literal.pos 9) (Sat.Literal.pos 72) (lex_9_9_prefix s) (positive_select s 9) (lex_9_9_image s)

theorem lex_9_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4172), (Sat.Literal.pos 4171)] :=
  (lex_9_9_gate s).prop _ (List.Mem.head _)

theorem lex_9_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4172), (Sat.Literal.neg 9), (Sat.Literal.pos 72)] :=
  (lex_9_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4172), (Sat.Literal.pos 9), (Sat.Literal.neg 72)] :=
  (lex_9_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4171), (Sat.Literal.neg 9), (Sat.Literal.neg 72), (Sat.Literal.pos 4172)] :=
  (lex_9_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4171), (Sat.Literal.pos 9), (Sat.Literal.pos 72), (Sat.Literal.pos 4172)] :=
  (lex_9_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4172) = lexBefore s permutation9 8 := by
  exact (positive_lex_of_descriptor s 4172 permutation9 9 (by rfl)).trans ((lex_skipped s permutation9 8 9 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation9 8) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation9 8 by rw [image9_eq]; rfl))

theorem lex_9_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4173) (Sat.Literal.pos 4172) (Sat.Literal.pos 8) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation9 8 (assignment s)
    (Sat.Literal.pos 4173) (Sat.Literal.pos 4172) (Sat.Literal.pos 8) (Sat.Literal.pos 64) (positive_of_descriptor s 4173 (.lex permutation9 8) (by rfl)) (lex_9_8_prefix s) (positive_select s 8) (lex_9_8_image s)

theorem lex_9_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4172), (Sat.Literal.pos 8), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation9 8 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4172) (Sat.Literal.pos 8) (Sat.Literal.pos 64) (lex_9_8_prefix s) (positive_select s 8) (lex_9_8_image s)

theorem lex_9_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4173), (Sat.Literal.pos 4172)] :=
  (lex_9_8_gate s).prop _ (List.Mem.head _)

theorem lex_9_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4173), (Sat.Literal.neg 8), (Sat.Literal.pos 64)] :=
  (lex_9_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4173), (Sat.Literal.pos 8), (Sat.Literal.neg 64)] :=
  (lex_9_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4172), (Sat.Literal.neg 8), (Sat.Literal.neg 64), (Sat.Literal.pos 4173)] :=
  (lex_9_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4172), (Sat.Literal.pos 8), (Sat.Literal.pos 64), (Sat.Literal.pos 4173)] :=
  (lex_9_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4173) = lexBefore s permutation9 7 := by
  exact (positive_lex_of_descriptor s 4173 permutation9 8 (by rfl)).trans ((lex_skipped s permutation9 7 8 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation9 7) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation9 7 by rw [image9_eq]; rfl))

theorem lex_9_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4174) (Sat.Literal.pos 4173) (Sat.Literal.pos 7) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation9 7 (assignment s)
    (Sat.Literal.pos 4174) (Sat.Literal.pos 4173) (Sat.Literal.pos 7) (Sat.Literal.pos 56) (positive_of_descriptor s 4174 (.lex permutation9 7) (by rfl)) (lex_9_7_prefix s) (positive_select s 7) (lex_9_7_image s)

theorem lex_9_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4173), (Sat.Literal.pos 7), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation9 7 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4173) (Sat.Literal.pos 7) (Sat.Literal.pos 56) (lex_9_7_prefix s) (positive_select s 7) (lex_9_7_image s)

theorem lex_9_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4174), (Sat.Literal.pos 4173)] :=
  (lex_9_7_gate s).prop _ (List.Mem.head _)

theorem lex_9_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4174), (Sat.Literal.neg 7), (Sat.Literal.pos 56)] :=
  (lex_9_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4174), (Sat.Literal.pos 7), (Sat.Literal.neg 56)] :=
  (lex_9_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4173), (Sat.Literal.neg 7), (Sat.Literal.neg 56), (Sat.Literal.pos 4174)] :=
  (lex_9_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4173), (Sat.Literal.pos 7), (Sat.Literal.pos 56), (Sat.Literal.pos 4174)] :=
  (lex_9_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4174) = lexBefore s permutation9 6 := by
  exact (positive_lex_of_descriptor s 4174 permutation9 7 (by rfl)).trans ((lex_skipped s permutation9 6 7 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 48) = s (permuteMask permutation9 6) := by
  exact (positive_select s 48).trans (congrArg s (show (48 : Fin 256) = permuteMask permutation9 6 by rw [image9_eq]; rfl))

theorem lex_9_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4175) (Sat.Literal.pos 4174) (Sat.Literal.pos 6) (Sat.Literal.pos 48)) := by
  exact equality_gate s permutation9 6 (assignment s)
    (Sat.Literal.pos 4175) (Sat.Literal.pos 4174) (Sat.Literal.pos 6) (Sat.Literal.pos 48) (positive_of_descriptor s 4175 (.lex permutation9 6) (by rfl)) (lex_9_6_prefix s) (positive_select s 6) (lex_9_6_image s)

theorem lex_9_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4174), (Sat.Literal.pos 6), (Sat.Literal.neg 48)] := by
  exact comparison_gate s permutation9 6 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4174) (Sat.Literal.pos 6) (Sat.Literal.pos 48) (lex_9_6_prefix s) (positive_select s 6) (lex_9_6_image s)

theorem lex_9_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4175), (Sat.Literal.pos 4174)] :=
  (lex_9_6_gate s).prop _ (List.Mem.head _)

theorem lex_9_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4175), (Sat.Literal.neg 6), (Sat.Literal.pos 48)] :=
  (lex_9_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4175), (Sat.Literal.pos 6), (Sat.Literal.neg 48)] :=
  (lex_9_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4174), (Sat.Literal.neg 6), (Sat.Literal.neg 48), (Sat.Literal.pos 4175)] :=
  (lex_9_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4174), (Sat.Literal.pos 6), (Sat.Literal.pos 48), (Sat.Literal.pos 4175)] :=
  (lex_9_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4175) = lexBefore s permutation9 5 := by
  exact (positive_lex_of_descriptor s 4175 permutation9 6 (by rfl)).trans ((lex_skipped s permutation9 5 6 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 40) = s (permuteMask permutation9 5) := by
  exact (positive_select s 40).trans (congrArg s (show (40 : Fin 256) = permuteMask permutation9 5 by rw [image9_eq]; rfl))

theorem lex_9_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4176) (Sat.Literal.pos 4175) (Sat.Literal.pos 5) (Sat.Literal.pos 40)) := by
  exact equality_gate s permutation9 5 (assignment s)
    (Sat.Literal.pos 4176) (Sat.Literal.pos 4175) (Sat.Literal.pos 5) (Sat.Literal.pos 40) (positive_of_descriptor s 4176 (.lex permutation9 5) (by rfl)) (lex_9_5_prefix s) (positive_select s 5) (lex_9_5_image s)

theorem lex_9_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4175), (Sat.Literal.pos 5), (Sat.Literal.neg 40)] := by
  exact comparison_gate s permutation9 5 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4175) (Sat.Literal.pos 5) (Sat.Literal.pos 40) (lex_9_5_prefix s) (positive_select s 5) (lex_9_5_image s)

theorem lex_9_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4176), (Sat.Literal.pos 4175)] :=
  (lex_9_5_gate s).prop _ (List.Mem.head _)

theorem lex_9_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4176), (Sat.Literal.neg 5), (Sat.Literal.pos 40)] :=
  (lex_9_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4176), (Sat.Literal.pos 5), (Sat.Literal.neg 40)] :=
  (lex_9_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4175), (Sat.Literal.neg 5), (Sat.Literal.neg 40), (Sat.Literal.pos 4176)] :=
  (lex_9_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4175), (Sat.Literal.pos 5), (Sat.Literal.pos 40), (Sat.Literal.pos 4176)] :=
  (lex_9_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4176) = lexBefore s permutation9 4 := by
  exact (positive_lex_of_descriptor s 4176 permutation9 5 (by rfl)).trans ((lex_skipped s permutation9 4 5 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 32) = s (permuteMask permutation9 4) := by
  exact (positive_select s 32).trans (congrArg s (show (32 : Fin 256) = permuteMask permutation9 4 by rw [image9_eq]; rfl))

theorem lex_9_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4177) (Sat.Literal.pos 4176) (Sat.Literal.pos 4) (Sat.Literal.pos 32)) := by
  exact equality_gate s permutation9 4 (assignment s)
    (Sat.Literal.pos 4177) (Sat.Literal.pos 4176) (Sat.Literal.pos 4) (Sat.Literal.pos 32) (positive_of_descriptor s 4177 (.lex permutation9 4) (by rfl)) (lex_9_4_prefix s) (positive_select s 4) (lex_9_4_image s)

theorem lex_9_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4176), (Sat.Literal.pos 4), (Sat.Literal.neg 32)] := by
  exact comparison_gate s permutation9 4 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4176) (Sat.Literal.pos 4) (Sat.Literal.pos 32) (lex_9_4_prefix s) (positive_select s 4) (lex_9_4_image s)

theorem lex_9_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4177), (Sat.Literal.pos 4176)] :=
  (lex_9_4_gate s).prop _ (List.Mem.head _)

theorem lex_9_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4177), (Sat.Literal.neg 4), (Sat.Literal.pos 32)] :=
  (lex_9_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4177), (Sat.Literal.pos 4), (Sat.Literal.neg 32)] :=
  (lex_9_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4176), (Sat.Literal.neg 4), (Sat.Literal.neg 32), (Sat.Literal.pos 4177)] :=
  (lex_9_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4176), (Sat.Literal.pos 4), (Sat.Literal.pos 32), (Sat.Literal.pos 4177)] :=
  (lex_9_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4177) = lexBefore s permutation9 3 := by
  exact (positive_lex_of_descriptor s 4177 permutation9 4 (by rfl)).trans ((lex_skipped s permutation9 3 4 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation9 3) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation9 3 by rw [image9_eq]; rfl))

theorem lex_9_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4178) (Sat.Literal.pos 4177) (Sat.Literal.pos 3) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation9 3 (assignment s)
    (Sat.Literal.pos 4178) (Sat.Literal.pos 4177) (Sat.Literal.pos 3) (Sat.Literal.pos 24) (positive_of_descriptor s 4178 (.lex permutation9 3) (by rfl)) (lex_9_3_prefix s) (positive_select s 3) (lex_9_3_image s)

theorem lex_9_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4177), (Sat.Literal.pos 3), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation9 3 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4177) (Sat.Literal.pos 3) (Sat.Literal.pos 24) (lex_9_3_prefix s) (positive_select s 3) (lex_9_3_image s)

theorem lex_9_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4178), (Sat.Literal.pos 4177)] :=
  (lex_9_3_gate s).prop _ (List.Mem.head _)

theorem lex_9_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4178), (Sat.Literal.neg 3), (Sat.Literal.pos 24)] :=
  (lex_9_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4178), (Sat.Literal.pos 3), (Sat.Literal.neg 24)] :=
  (lex_9_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4177), (Sat.Literal.neg 3), (Sat.Literal.neg 24), (Sat.Literal.pos 4178)] :=
  (lex_9_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4177), (Sat.Literal.pos 3), (Sat.Literal.pos 24), (Sat.Literal.pos 4178)] :=
  (lex_9_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4178) = lexBefore s permutation9 2 := by
  exact (positive_lex_of_descriptor s 4178 permutation9 3 (by rfl)).trans ((lex_skipped s permutation9 2 3 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation9 2) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation9 2 by rw [image9_eq]; rfl))

theorem lex_9_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4179) (Sat.Literal.pos 4178) (Sat.Literal.pos 2) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation9 2 (assignment s)
    (Sat.Literal.pos 4179) (Sat.Literal.pos 4178) (Sat.Literal.pos 2) (Sat.Literal.pos 16) (positive_of_descriptor s 4179 (.lex permutation9 2) (by rfl)) (lex_9_2_prefix s) (positive_select s 2) (lex_9_2_image s)

theorem lex_9_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4178), (Sat.Literal.pos 2), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation9 2 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4178) (Sat.Literal.pos 2) (Sat.Literal.pos 16) (lex_9_2_prefix s) (positive_select s 2) (lex_9_2_image s)

theorem lex_9_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4179), (Sat.Literal.pos 4178)] :=
  (lex_9_2_gate s).prop _ (List.Mem.head _)

theorem lex_9_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4179), (Sat.Literal.neg 2), (Sat.Literal.pos 16)] :=
  (lex_9_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4179), (Sat.Literal.pos 2), (Sat.Literal.neg 16)] :=
  (lex_9_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4178), (Sat.Literal.neg 2), (Sat.Literal.neg 16), (Sat.Literal.pos 4179)] :=
  (lex_9_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4178), (Sat.Literal.pos 2), (Sat.Literal.pos 16), (Sat.Literal.pos 4179)] :=
  (lex_9_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4179) = lexBefore s permutation9 1 := by
  exact (positive_lex_of_descriptor s 4179 permutation9 2 (by rfl)).trans ((lex_skipped s permutation9 1 2 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation9 1) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation9 1 by rw [image9_eq]; rfl))

theorem lex_9_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4180) (Sat.Literal.pos 4179) (Sat.Literal.pos 1) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation9 1 (assignment s)
    (Sat.Literal.pos 4180) (Sat.Literal.pos 4179) (Sat.Literal.pos 1) (Sat.Literal.pos 8) (positive_of_descriptor s 4180 (.lex permutation9 1) (by rfl)) (lex_9_1_prefix s) (positive_select s 1) (lex_9_1_image s)

theorem lex_9_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4179), (Sat.Literal.pos 1), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation9 1 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4179) (Sat.Literal.pos 1) (Sat.Literal.pos 8) (lex_9_1_prefix s) (positive_select s 1) (lex_9_1_image s)

theorem lex_9_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4180), (Sat.Literal.pos 4179)] :=
  (lex_9_1_gate s).prop _ (List.Mem.head _)

theorem lex_9_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4180), (Sat.Literal.neg 1), (Sat.Literal.pos 8)] :=
  (lex_9_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4180), (Sat.Literal.pos 1), (Sat.Literal.neg 8)] :=
  (lex_9_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4179), (Sat.Literal.neg 1), (Sat.Literal.neg 8), (Sat.Literal.pos 4180)] :=
  (lex_9_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4179), (Sat.Literal.pos 1), (Sat.Literal.pos 8), (Sat.Literal.pos 4180)] :=
  (lex_9_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation10 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation10 254 (by intro j hj; rw [image10_eq]; exact fixedOnRange_spec image10 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_10_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation10 254) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation10 254 by rw [image10_eq]; rfl))

theorem lex_10_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4181) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation10 254 (assignment s)
    (Sat.Literal.pos 4181) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 239) (positive_of_descriptor s 4181 (.lex permutation10 254) (by rfl)) (lex_10_254_prefix s) (positive_select s 254) (lex_10_254_image s)

theorem lex_10_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation10 254 (hmax permutation10) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 239) (lex_10_254_prefix s) (positive_select s 254) (lex_10_254_image s)

theorem lex_10_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4181), (Sat.Literal.neg 256)] :=
  (lex_10_254_gate s).prop _ (List.Mem.head _)

theorem lex_10_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4181), (Sat.Literal.neg 254), (Sat.Literal.pos 239)] :=
  (lex_10_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4181), (Sat.Literal.pos 254), (Sat.Literal.neg 239)] :=
  (lex_10_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 239), (Sat.Literal.pos 4181)] :=
  (lex_10_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 239), (Sat.Literal.pos 4181)] :=
  (lex_10_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4181) = lexBefore s permutation10 253 := by
  exact (positive_lex_of_descriptor s 4181 permutation10 254 (by rfl)).trans ((lex_skipped s permutation10 253 254 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation10 253) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation10 253 by rw [image10_eq]; rfl))

theorem lex_10_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4182) (Sat.Literal.pos 4181) (Sat.Literal.pos 253) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation10 253 (assignment s)
    (Sat.Literal.pos 4182) (Sat.Literal.pos 4181) (Sat.Literal.pos 253) (Sat.Literal.pos 223) (positive_of_descriptor s 4182 (.lex permutation10 253) (by rfl)) (lex_10_253_prefix s) (positive_select s 253) (lex_10_253_image s)

theorem lex_10_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4181), (Sat.Literal.pos 253), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation10 253 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4181) (Sat.Literal.pos 253) (Sat.Literal.pos 223) (lex_10_253_prefix s) (positive_select s 253) (lex_10_253_image s)

theorem lex_10_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4182), (Sat.Literal.pos 4181)] :=
  (lex_10_253_gate s).prop _ (List.Mem.head _)

theorem lex_10_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4182), (Sat.Literal.neg 253), (Sat.Literal.pos 223)] :=
  (lex_10_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4182), (Sat.Literal.pos 253), (Sat.Literal.neg 223)] :=
  (lex_10_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4181), (Sat.Literal.neg 253), (Sat.Literal.neg 223), (Sat.Literal.pos 4182)] :=
  (lex_10_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4181), (Sat.Literal.pos 253), (Sat.Literal.pos 223), (Sat.Literal.pos 4182)] :=
  (lex_10_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4182) = lexBefore s permutation10 252 := by
  exact (positive_lex_of_descriptor s 4182 permutation10 253 (by rfl)).trans ((lex_skipped s permutation10 252 253 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation10 252) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation10 252 by rw [image10_eq]; rfl))

theorem lex_10_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4183) (Sat.Literal.pos 4182) (Sat.Literal.pos 252) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation10 252 (assignment s)
    (Sat.Literal.pos 4183) (Sat.Literal.pos 4182) (Sat.Literal.pos 252) (Sat.Literal.pos 207) (positive_of_descriptor s 4183 (.lex permutation10 252) (by rfl)) (lex_10_252_prefix s) (positive_select s 252) (lex_10_252_image s)

theorem lex_10_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4182), (Sat.Literal.pos 252), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation10 252 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4182) (Sat.Literal.pos 252) (Sat.Literal.pos 207) (lex_10_252_prefix s) (positive_select s 252) (lex_10_252_image s)

theorem lex_10_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4183), (Sat.Literal.pos 4182)] :=
  (lex_10_252_gate s).prop _ (List.Mem.head _)

theorem lex_10_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4183), (Sat.Literal.neg 252), (Sat.Literal.pos 207)] :=
  (lex_10_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4183), (Sat.Literal.pos 252), (Sat.Literal.neg 207)] :=
  (lex_10_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4182), (Sat.Literal.neg 252), (Sat.Literal.neg 207), (Sat.Literal.pos 4183)] :=
  (lex_10_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4182), (Sat.Literal.pos 252), (Sat.Literal.pos 207), (Sat.Literal.pos 4183)] :=
  (lex_10_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4183) = lexBefore s permutation10 251 := by
  exact (positive_lex_of_descriptor s 4183 permutation10 252 (by rfl)).trans ((lex_skipped s permutation10 251 252 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation10 251) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation10 251 by rw [image10_eq]; rfl))

theorem lex_10_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4184) (Sat.Literal.pos 4183) (Sat.Literal.pos 251) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation10 251 (assignment s)
    (Sat.Literal.pos 4184) (Sat.Literal.pos 4183) (Sat.Literal.pos 251) (Sat.Literal.pos 191) (positive_of_descriptor s 4184 (.lex permutation10 251) (by rfl)) (lex_10_251_prefix s) (positive_select s 251) (lex_10_251_image s)

theorem lex_10_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4183), (Sat.Literal.pos 251), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation10 251 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4183) (Sat.Literal.pos 251) (Sat.Literal.pos 191) (lex_10_251_prefix s) (positive_select s 251) (lex_10_251_image s)

theorem lex_10_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4184), (Sat.Literal.pos 4183)] :=
  (lex_10_251_gate s).prop _ (List.Mem.head _)

theorem lex_10_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4184), (Sat.Literal.neg 251), (Sat.Literal.pos 191)] :=
  (lex_10_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4184), (Sat.Literal.pos 251), (Sat.Literal.neg 191)] :=
  (lex_10_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4183), (Sat.Literal.neg 251), (Sat.Literal.neg 191), (Sat.Literal.pos 4184)] :=
  (lex_10_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4183), (Sat.Literal.pos 251), (Sat.Literal.pos 191), (Sat.Literal.pos 4184)] :=
  (lex_10_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4184) = lexBefore s permutation10 250 := by
  exact (positive_lex_of_descriptor s 4184 permutation10 251 (by rfl)).trans ((lex_skipped s permutation10 250 251 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation10 250) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation10 250 by rw [image10_eq]; rfl))

theorem lex_10_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4185) (Sat.Literal.pos 4184) (Sat.Literal.pos 250) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation10 250 (assignment s)
    (Sat.Literal.pos 4185) (Sat.Literal.pos 4184) (Sat.Literal.pos 250) (Sat.Literal.pos 175) (positive_of_descriptor s 4185 (.lex permutation10 250) (by rfl)) (lex_10_250_prefix s) (positive_select s 250) (lex_10_250_image s)

theorem lex_10_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4184), (Sat.Literal.pos 250), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation10 250 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4184) (Sat.Literal.pos 250) (Sat.Literal.pos 175) (lex_10_250_prefix s) (positive_select s 250) (lex_10_250_image s)

theorem lex_10_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4185), (Sat.Literal.pos 4184)] :=
  (lex_10_250_gate s).prop _ (List.Mem.head _)

theorem lex_10_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4185), (Sat.Literal.neg 250), (Sat.Literal.pos 175)] :=
  (lex_10_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4185), (Sat.Literal.pos 250), (Sat.Literal.neg 175)] :=
  (lex_10_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4184), (Sat.Literal.neg 250), (Sat.Literal.neg 175), (Sat.Literal.pos 4185)] :=
  (lex_10_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4184), (Sat.Literal.pos 250), (Sat.Literal.pos 175), (Sat.Literal.pos 4185)] :=
  (lex_10_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4185) = lexBefore s permutation10 249 := by
  exact (positive_lex_of_descriptor s 4185 permutation10 250 (by rfl)).trans ((lex_skipped s permutation10 249 250 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation10 249) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation10 249 by rw [image10_eq]; rfl))

theorem lex_10_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4186) (Sat.Literal.pos 4185) (Sat.Literal.pos 249) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation10 249 (assignment s)
    (Sat.Literal.pos 4186) (Sat.Literal.pos 4185) (Sat.Literal.pos 249) (Sat.Literal.pos 159) (positive_of_descriptor s 4186 (.lex permutation10 249) (by rfl)) (lex_10_249_prefix s) (positive_select s 249) (lex_10_249_image s)

theorem lex_10_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4185), (Sat.Literal.pos 249), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation10 249 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4185) (Sat.Literal.pos 249) (Sat.Literal.pos 159) (lex_10_249_prefix s) (positive_select s 249) (lex_10_249_image s)

theorem lex_10_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4186), (Sat.Literal.pos 4185)] :=
  (lex_10_249_gate s).prop _ (List.Mem.head _)

theorem lex_10_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4186), (Sat.Literal.neg 249), (Sat.Literal.pos 159)] :=
  (lex_10_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4186), (Sat.Literal.pos 249), (Sat.Literal.neg 159)] :=
  (lex_10_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4185), (Sat.Literal.neg 249), (Sat.Literal.neg 159), (Sat.Literal.pos 4186)] :=
  (lex_10_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4185), (Sat.Literal.pos 249), (Sat.Literal.pos 159), (Sat.Literal.pos 4186)] :=
  (lex_10_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4186) = lexBefore s permutation10 248 := by
  exact (positive_lex_of_descriptor s 4186 permutation10 249 (by rfl)).trans ((lex_skipped s permutation10 248 249 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation10 248) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation10 248 by rw [image10_eq]; rfl))

theorem lex_10_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4187) (Sat.Literal.pos 4186) (Sat.Literal.pos 248) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation10 248 (assignment s)
    (Sat.Literal.pos 4187) (Sat.Literal.pos 4186) (Sat.Literal.pos 248) (Sat.Literal.pos 143) (positive_of_descriptor s 4187 (.lex permutation10 248) (by rfl)) (lex_10_248_prefix s) (positive_select s 248) (lex_10_248_image s)

theorem lex_10_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4186), (Sat.Literal.pos 248), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation10 248 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4186) (Sat.Literal.pos 248) (Sat.Literal.pos 143) (lex_10_248_prefix s) (positive_select s 248) (lex_10_248_image s)

theorem lex_10_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4187), (Sat.Literal.pos 4186)] :=
  (lex_10_248_gate s).prop _ (List.Mem.head _)

theorem lex_10_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4187), (Sat.Literal.neg 248), (Sat.Literal.pos 143)] :=
  (lex_10_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4187), (Sat.Literal.pos 248), (Sat.Literal.neg 143)] :=
  (lex_10_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4186), (Sat.Literal.neg 248), (Sat.Literal.neg 143), (Sat.Literal.pos 4187)] :=
  (lex_10_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4186), (Sat.Literal.pos 248), (Sat.Literal.pos 143), (Sat.Literal.pos 4187)] :=
  (lex_10_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4187) = lexBefore s permutation10 247 := by
  exact (positive_lex_of_descriptor s 4187 permutation10 248 (by rfl)).trans ((lex_skipped s permutation10 247 248 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation10 247) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation10 247 by rw [image10_eq]; rfl))

theorem lex_10_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4188) (Sat.Literal.pos 4187) (Sat.Literal.pos 247) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation10 247 (assignment s)
    (Sat.Literal.pos 4188) (Sat.Literal.pos 4187) (Sat.Literal.pos 247) (Sat.Literal.pos 127) (positive_of_descriptor s 4188 (.lex permutation10 247) (by rfl)) (lex_10_247_prefix s) (positive_select s 247) (lex_10_247_image s)

theorem lex_10_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4187), (Sat.Literal.pos 247), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation10 247 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4187) (Sat.Literal.pos 247) (Sat.Literal.pos 127) (lex_10_247_prefix s) (positive_select s 247) (lex_10_247_image s)

theorem lex_10_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4188), (Sat.Literal.pos 4187)] :=
  (lex_10_247_gate s).prop _ (List.Mem.head _)

theorem lex_10_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4188), (Sat.Literal.neg 247), (Sat.Literal.pos 127)] :=
  (lex_10_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4188), (Sat.Literal.pos 247), (Sat.Literal.neg 127)] :=
  (lex_10_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4187), (Sat.Literal.neg 247), (Sat.Literal.neg 127), (Sat.Literal.pos 4188)] :=
  (lex_10_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4187), (Sat.Literal.pos 247), (Sat.Literal.pos 127), (Sat.Literal.pos 4188)] :=
  (lex_10_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4188) = lexBefore s permutation10 246 := by
  exact (positive_lex_of_descriptor s 4188 permutation10 247 (by rfl)).trans ((lex_skipped s permutation10 246 247 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation10 246) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation10 246 by rw [image10_eq]; rfl))

theorem lex_10_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4189) (Sat.Literal.pos 4188) (Sat.Literal.pos 246) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation10 246 (assignment s)
    (Sat.Literal.pos 4189) (Sat.Literal.pos 4188) (Sat.Literal.pos 246) (Sat.Literal.pos 111) (positive_of_descriptor s 4189 (.lex permutation10 246) (by rfl)) (lex_10_246_prefix s) (positive_select s 246) (lex_10_246_image s)

theorem lex_10_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4188), (Sat.Literal.pos 246), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation10 246 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4188) (Sat.Literal.pos 246) (Sat.Literal.pos 111) (lex_10_246_prefix s) (positive_select s 246) (lex_10_246_image s)

theorem lex_10_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4189), (Sat.Literal.pos 4188)] :=
  (lex_10_246_gate s).prop _ (List.Mem.head _)

theorem lex_10_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4189), (Sat.Literal.neg 246), (Sat.Literal.pos 111)] :=
  (lex_10_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4189), (Sat.Literal.pos 246), (Sat.Literal.neg 111)] :=
  (lex_10_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4188), (Sat.Literal.neg 246), (Sat.Literal.neg 111), (Sat.Literal.pos 4189)] :=
  (lex_10_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4188), (Sat.Literal.pos 246), (Sat.Literal.pos 111), (Sat.Literal.pos 4189)] :=
  (lex_10_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4189) = lexBefore s permutation10 245 := by
  exact (positive_lex_of_descriptor s 4189 permutation10 246 (by rfl)).trans ((lex_skipped s permutation10 245 246 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation10 245) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation10 245 by rw [image10_eq]; rfl))

theorem lex_10_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4190) (Sat.Literal.pos 4189) (Sat.Literal.pos 245) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation10 245 (assignment s)
    (Sat.Literal.pos 4190) (Sat.Literal.pos 4189) (Sat.Literal.pos 245) (Sat.Literal.pos 95) (positive_of_descriptor s 4190 (.lex permutation10 245) (by rfl)) (lex_10_245_prefix s) (positive_select s 245) (lex_10_245_image s)

theorem lex_10_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4189), (Sat.Literal.pos 245), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation10 245 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4189) (Sat.Literal.pos 245) (Sat.Literal.pos 95) (lex_10_245_prefix s) (positive_select s 245) (lex_10_245_image s)

theorem lex_10_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4190), (Sat.Literal.pos 4189)] :=
  (lex_10_245_gate s).prop _ (List.Mem.head _)

theorem lex_10_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4190), (Sat.Literal.neg 245), (Sat.Literal.pos 95)] :=
  (lex_10_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4190), (Sat.Literal.pos 245), (Sat.Literal.neg 95)] :=
  (lex_10_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4189), (Sat.Literal.neg 245), (Sat.Literal.neg 95), (Sat.Literal.pos 4190)] :=
  (lex_10_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4189), (Sat.Literal.pos 245), (Sat.Literal.pos 95), (Sat.Literal.pos 4190)] :=
  (lex_10_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4190) = lexBefore s permutation10 244 := by
  exact (positive_lex_of_descriptor s 4190 permutation10 245 (by rfl)).trans ((lex_skipped s permutation10 244 245 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation10 244) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation10 244 by rw [image10_eq]; rfl))

theorem lex_10_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4191) (Sat.Literal.pos 4190) (Sat.Literal.pos 244) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation10 244 (assignment s)
    (Sat.Literal.pos 4191) (Sat.Literal.pos 4190) (Sat.Literal.pos 244) (Sat.Literal.pos 79) (positive_of_descriptor s 4191 (.lex permutation10 244) (by rfl)) (lex_10_244_prefix s) (positive_select s 244) (lex_10_244_image s)

theorem lex_10_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4190), (Sat.Literal.pos 244), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation10 244 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4190) (Sat.Literal.pos 244) (Sat.Literal.pos 79) (lex_10_244_prefix s) (positive_select s 244) (lex_10_244_image s)

theorem lex_10_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4191), (Sat.Literal.pos 4190)] :=
  (lex_10_244_gate s).prop _ (List.Mem.head _)

theorem lex_10_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4191), (Sat.Literal.neg 244), (Sat.Literal.pos 79)] :=
  (lex_10_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4191), (Sat.Literal.pos 244), (Sat.Literal.neg 79)] :=
  (lex_10_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4190), (Sat.Literal.neg 244), (Sat.Literal.neg 79), (Sat.Literal.pos 4191)] :=
  (lex_10_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4190), (Sat.Literal.pos 244), (Sat.Literal.pos 79), (Sat.Literal.pos 4191)] :=
  (lex_10_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4191) = lexBefore s permutation10 243 := by
  exact (positive_lex_of_descriptor s 4191 permutation10 244 (by rfl)).trans ((lex_skipped s permutation10 243 244 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation10 243) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation10 243 by rw [image10_eq]; rfl))

theorem lex_10_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4192) (Sat.Literal.pos 4191) (Sat.Literal.pos 243) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation10 243 (assignment s)
    (Sat.Literal.pos 4192) (Sat.Literal.pos 4191) (Sat.Literal.pos 243) (Sat.Literal.pos 63) (positive_of_descriptor s 4192 (.lex permutation10 243) (by rfl)) (lex_10_243_prefix s) (positive_select s 243) (lex_10_243_image s)

theorem lex_10_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4191), (Sat.Literal.pos 243), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation10 243 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4191) (Sat.Literal.pos 243) (Sat.Literal.pos 63) (lex_10_243_prefix s) (positive_select s 243) (lex_10_243_image s)

theorem lex_10_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4192), (Sat.Literal.pos 4191)] :=
  (lex_10_243_gate s).prop _ (List.Mem.head _)

theorem lex_10_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4192), (Sat.Literal.neg 243), (Sat.Literal.pos 63)] :=
  (lex_10_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4192), (Sat.Literal.pos 243), (Sat.Literal.neg 63)] :=
  (lex_10_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4191), (Sat.Literal.neg 243), (Sat.Literal.neg 63), (Sat.Literal.pos 4192)] :=
  (lex_10_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4191), (Sat.Literal.pos 243), (Sat.Literal.pos 63), (Sat.Literal.pos 4192)] :=
  (lex_10_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4192) = lexBefore s permutation10 242 := by
  exact (positive_lex_of_descriptor s 4192 permutation10 243 (by rfl)).trans ((lex_skipped s permutation10 242 243 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation10 242) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation10 242 by rw [image10_eq]; rfl))

theorem lex_10_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4193) (Sat.Literal.pos 4192) (Sat.Literal.pos 242) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation10 242 (assignment s)
    (Sat.Literal.pos 4193) (Sat.Literal.pos 4192) (Sat.Literal.pos 242) (Sat.Literal.pos 47) (positive_of_descriptor s 4193 (.lex permutation10 242) (by rfl)) (lex_10_242_prefix s) (positive_select s 242) (lex_10_242_image s)

theorem lex_10_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4192), (Sat.Literal.pos 242), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation10 242 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4192) (Sat.Literal.pos 242) (Sat.Literal.pos 47) (lex_10_242_prefix s) (positive_select s 242) (lex_10_242_image s)

theorem lex_10_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4193), (Sat.Literal.pos 4192)] :=
  (lex_10_242_gate s).prop _ (List.Mem.head _)

theorem lex_10_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4193), (Sat.Literal.neg 242), (Sat.Literal.pos 47)] :=
  (lex_10_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4193), (Sat.Literal.pos 242), (Sat.Literal.neg 47)] :=
  (lex_10_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4192), (Sat.Literal.neg 242), (Sat.Literal.neg 47), (Sat.Literal.pos 4193)] :=
  (lex_10_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4192), (Sat.Literal.pos 242), (Sat.Literal.pos 47), (Sat.Literal.pos 4193)] :=
  (lex_10_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4193) = lexBefore s permutation10 241 := by
  exact (positive_lex_of_descriptor s 4193 permutation10 242 (by rfl)).trans ((lex_skipped s permutation10 241 242 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation10 241) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation10 241 by rw [image10_eq]; rfl))

theorem lex_10_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4194) (Sat.Literal.pos 4193) (Sat.Literal.pos 241) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation10 241 (assignment s)
    (Sat.Literal.pos 4194) (Sat.Literal.pos 4193) (Sat.Literal.pos 241) (Sat.Literal.pos 31) (positive_of_descriptor s 4194 (.lex permutation10 241) (by rfl)) (lex_10_241_prefix s) (positive_select s 241) (lex_10_241_image s)

theorem lex_10_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4193), (Sat.Literal.pos 241), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation10 241 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4193) (Sat.Literal.pos 241) (Sat.Literal.pos 31) (lex_10_241_prefix s) (positive_select s 241) (lex_10_241_image s)

theorem lex_10_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4194), (Sat.Literal.pos 4193)] :=
  (lex_10_241_gate s).prop _ (List.Mem.head _)

theorem lex_10_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4194), (Sat.Literal.neg 241), (Sat.Literal.pos 31)] :=
  (lex_10_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4194), (Sat.Literal.pos 241), (Sat.Literal.neg 31)] :=
  (lex_10_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4193), (Sat.Literal.neg 241), (Sat.Literal.neg 31), (Sat.Literal.pos 4194)] :=
  (lex_10_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4193), (Sat.Literal.pos 241), (Sat.Literal.pos 31), (Sat.Literal.pos 4194)] :=
  (lex_10_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4194) = lexBefore s permutation10 240 := by
  exact (positive_lex_of_descriptor s 4194 permutation10 241 (by rfl)).trans ((lex_skipped s permutation10 240 241 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation10 240) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation10 240 by rw [image10_eq]; rfl))

theorem lex_10_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4195) (Sat.Literal.pos 4194) (Sat.Literal.pos 240) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation10 240 (assignment s)
    (Sat.Literal.pos 4195) (Sat.Literal.pos 4194) (Sat.Literal.pos 240) (Sat.Literal.pos 15) (positive_of_descriptor s 4195 (.lex permutation10 240) (by rfl)) (lex_10_240_prefix s) (positive_select s 240) (lex_10_240_image s)

theorem lex_10_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4194), (Sat.Literal.pos 240), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation10 240 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4194) (Sat.Literal.pos 240) (Sat.Literal.pos 15) (lex_10_240_prefix s) (positive_select s 240) (lex_10_240_image s)

theorem lex_10_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4195), (Sat.Literal.pos 4194)] :=
  (lex_10_240_gate s).prop _ (List.Mem.head _)

theorem lex_10_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4195), (Sat.Literal.neg 240), (Sat.Literal.pos 15)] :=
  (lex_10_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4195), (Sat.Literal.pos 240), (Sat.Literal.neg 15)] :=
  (lex_10_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4194), (Sat.Literal.neg 240), (Sat.Literal.neg 15), (Sat.Literal.pos 4195)] :=
  (lex_10_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4194), (Sat.Literal.pos 240), (Sat.Literal.pos 15), (Sat.Literal.pos 4195)] :=
  (lex_10_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4195) = lexBefore s permutation10 239 := by
  exact (positive_lex_of_descriptor s 4195 permutation10 240 (by rfl)).trans ((lex_skipped s permutation10 239 240 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation10 239) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation10 239 by rw [image10_eq]; rfl))

theorem lex_10_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4196) (Sat.Literal.pos 4195) (Sat.Literal.pos 239) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation10 239 (assignment s)
    (Sat.Literal.pos 4196) (Sat.Literal.pos 4195) (Sat.Literal.pos 239) (Sat.Literal.pos 254) (positive_of_descriptor s 4196 (.lex permutation10 239) (by rfl)) (lex_10_239_prefix s) (positive_select s 239) (lex_10_239_image s)

theorem lex_10_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4195), (Sat.Literal.pos 239), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation10 239 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4195) (Sat.Literal.pos 239) (Sat.Literal.pos 254) (lex_10_239_prefix s) (positive_select s 239) (lex_10_239_image s)

theorem lex_10_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4196), (Sat.Literal.pos 4195)] :=
  (lex_10_239_gate s).prop _ (List.Mem.head _)

theorem lex_10_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4196), (Sat.Literal.neg 239), (Sat.Literal.pos 254)] :=
  (lex_10_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4196), (Sat.Literal.pos 239), (Sat.Literal.neg 254)] :=
  (lex_10_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4195), (Sat.Literal.neg 239), (Sat.Literal.neg 254), (Sat.Literal.pos 4196)] :=
  (lex_10_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4195), (Sat.Literal.pos 239), (Sat.Literal.pos 254), (Sat.Literal.pos 4196)] :=
  (lex_10_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4196) = lexBefore s permutation10 237 := by
  exact (positive_lex_of_descriptor s 4196 permutation10 239 (by rfl)).trans ((lex_skipped s permutation10 237 239 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 238 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation10 237) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation10 237 by rw [image10_eq]; rfl))

theorem lex_10_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4197) (Sat.Literal.pos 4196) (Sat.Literal.pos 237) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation10 237 (assignment s)
    (Sat.Literal.pos 4197) (Sat.Literal.pos 4196) (Sat.Literal.pos 237) (Sat.Literal.pos 222) (positive_of_descriptor s 4197 (.lex permutation10 237) (by rfl)) (lex_10_237_prefix s) (positive_select s 237) (lex_10_237_image s)

theorem lex_10_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4196), (Sat.Literal.pos 237), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation10 237 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4196) (Sat.Literal.pos 237) (Sat.Literal.pos 222) (lex_10_237_prefix s) (positive_select s 237) (lex_10_237_image s)

theorem lex_10_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4197), (Sat.Literal.pos 4196)] :=
  (lex_10_237_gate s).prop _ (List.Mem.head _)

theorem lex_10_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4197), (Sat.Literal.neg 237), (Sat.Literal.pos 222)] :=
  (lex_10_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4197), (Sat.Literal.pos 237), (Sat.Literal.neg 222)] :=
  (lex_10_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4196), (Sat.Literal.neg 237), (Sat.Literal.neg 222), (Sat.Literal.pos 4197)] :=
  (lex_10_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4196), (Sat.Literal.pos 237), (Sat.Literal.pos 222), (Sat.Literal.pos 4197)] :=
  (lex_10_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4197) = lexBefore s permutation10 236 := by
  exact (positive_lex_of_descriptor s 4197 permutation10 237 (by rfl)).trans ((lex_skipped s permutation10 236 237 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation10 236) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation10 236 by rw [image10_eq]; rfl))

theorem lex_10_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4198) (Sat.Literal.pos 4197) (Sat.Literal.pos 236) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation10 236 (assignment s)
    (Sat.Literal.pos 4198) (Sat.Literal.pos 4197) (Sat.Literal.pos 236) (Sat.Literal.pos 206) (positive_of_descriptor s 4198 (.lex permutation10 236) (by rfl)) (lex_10_236_prefix s) (positive_select s 236) (lex_10_236_image s)

theorem lex_10_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4197), (Sat.Literal.pos 236), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation10 236 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4197) (Sat.Literal.pos 236) (Sat.Literal.pos 206) (lex_10_236_prefix s) (positive_select s 236) (lex_10_236_image s)

theorem lex_10_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4198), (Sat.Literal.pos 4197)] :=
  (lex_10_236_gate s).prop _ (List.Mem.head _)

theorem lex_10_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4198), (Sat.Literal.neg 236), (Sat.Literal.pos 206)] :=
  (lex_10_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4198), (Sat.Literal.pos 236), (Sat.Literal.neg 206)] :=
  (lex_10_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4197), (Sat.Literal.neg 236), (Sat.Literal.neg 206), (Sat.Literal.pos 4198)] :=
  (lex_10_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4197), (Sat.Literal.pos 236), (Sat.Literal.pos 206), (Sat.Literal.pos 4198)] :=
  (lex_10_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4198) = lexBefore s permutation10 235 := by
  exact (positive_lex_of_descriptor s 4198 permutation10 236 (by rfl)).trans ((lex_skipped s permutation10 235 236 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation10 235) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation10 235 by rw [image10_eq]; rfl))

theorem lex_10_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4199) (Sat.Literal.pos 4198) (Sat.Literal.pos 235) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation10 235 (assignment s)
    (Sat.Literal.pos 4199) (Sat.Literal.pos 4198) (Sat.Literal.pos 235) (Sat.Literal.pos 190) (positive_of_descriptor s 4199 (.lex permutation10 235) (by rfl)) (lex_10_235_prefix s) (positive_select s 235) (lex_10_235_image s)

theorem lex_10_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4198), (Sat.Literal.pos 235), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation10 235 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4198) (Sat.Literal.pos 235) (Sat.Literal.pos 190) (lex_10_235_prefix s) (positive_select s 235) (lex_10_235_image s)

theorem lex_10_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4199), (Sat.Literal.pos 4198)] :=
  (lex_10_235_gate s).prop _ (List.Mem.head _)

theorem lex_10_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4199), (Sat.Literal.neg 235), (Sat.Literal.pos 190)] :=
  (lex_10_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4199), (Sat.Literal.pos 235), (Sat.Literal.neg 190)] :=
  (lex_10_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4198), (Sat.Literal.neg 235), (Sat.Literal.neg 190), (Sat.Literal.pos 4199)] :=
  (lex_10_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4198), (Sat.Literal.pos 235), (Sat.Literal.pos 190), (Sat.Literal.pos 4199)] :=
  (lex_10_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4199) = lexBefore s permutation10 234 := by
  exact (positive_lex_of_descriptor s 4199 permutation10 235 (by rfl)).trans ((lex_skipped s permutation10 234 235 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation10 234) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation10 234 by rw [image10_eq]; rfl))

theorem lex_10_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4200) (Sat.Literal.pos 4199) (Sat.Literal.pos 234) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation10 234 (assignment s)
    (Sat.Literal.pos 4200) (Sat.Literal.pos 4199) (Sat.Literal.pos 234) (Sat.Literal.pos 174) (positive_of_descriptor s 4200 (.lex permutation10 234) (by rfl)) (lex_10_234_prefix s) (positive_select s 234) (lex_10_234_image s)

theorem lex_10_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4199), (Sat.Literal.pos 234), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation10 234 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4199) (Sat.Literal.pos 234) (Sat.Literal.pos 174) (lex_10_234_prefix s) (positive_select s 234) (lex_10_234_image s)

theorem lex_10_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4200), (Sat.Literal.pos 4199)] :=
  (lex_10_234_gate s).prop _ (List.Mem.head _)

theorem lex_10_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4200), (Sat.Literal.neg 234), (Sat.Literal.pos 174)] :=
  (lex_10_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4200), (Sat.Literal.pos 234), (Sat.Literal.neg 174)] :=
  (lex_10_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4199), (Sat.Literal.neg 234), (Sat.Literal.neg 174), (Sat.Literal.pos 4200)] :=
  (lex_10_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4199), (Sat.Literal.pos 234), (Sat.Literal.pos 174), (Sat.Literal.pos 4200)] :=
  (lex_10_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4200) = lexBefore s permutation10 233 := by
  exact (positive_lex_of_descriptor s 4200 permutation10 234 (by rfl)).trans ((lex_skipped s permutation10 233 234 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation10 233) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation10 233 by rw [image10_eq]; rfl))

theorem lex_10_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4201) (Sat.Literal.pos 4200) (Sat.Literal.pos 233) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation10 233 (assignment s)
    (Sat.Literal.pos 4201) (Sat.Literal.pos 4200) (Sat.Literal.pos 233) (Sat.Literal.pos 158) (positive_of_descriptor s 4201 (.lex permutation10 233) (by rfl)) (lex_10_233_prefix s) (positive_select s 233) (lex_10_233_image s)

theorem lex_10_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4200), (Sat.Literal.pos 233), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation10 233 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4200) (Sat.Literal.pos 233) (Sat.Literal.pos 158) (lex_10_233_prefix s) (positive_select s 233) (lex_10_233_image s)

theorem lex_10_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4201), (Sat.Literal.pos 4200)] :=
  (lex_10_233_gate s).prop _ (List.Mem.head _)

theorem lex_10_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4201), (Sat.Literal.neg 233), (Sat.Literal.pos 158)] :=
  (lex_10_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4201), (Sat.Literal.pos 233), (Sat.Literal.neg 158)] :=
  (lex_10_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4200), (Sat.Literal.neg 233), (Sat.Literal.neg 158), (Sat.Literal.pos 4201)] :=
  (lex_10_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4200), (Sat.Literal.pos 233), (Sat.Literal.pos 158), (Sat.Literal.pos 4201)] :=
  (lex_10_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4201) = lexBefore s permutation10 232 := by
  exact (positive_lex_of_descriptor s 4201 permutation10 233 (by rfl)).trans ((lex_skipped s permutation10 232 233 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation10 232) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation10 232 by rw [image10_eq]; rfl))

theorem lex_10_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4202) (Sat.Literal.pos 4201) (Sat.Literal.pos 232) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation10 232 (assignment s)
    (Sat.Literal.pos 4202) (Sat.Literal.pos 4201) (Sat.Literal.pos 232) (Sat.Literal.pos 142) (positive_of_descriptor s 4202 (.lex permutation10 232) (by rfl)) (lex_10_232_prefix s) (positive_select s 232) (lex_10_232_image s)

theorem lex_10_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4201), (Sat.Literal.pos 232), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation10 232 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4201) (Sat.Literal.pos 232) (Sat.Literal.pos 142) (lex_10_232_prefix s) (positive_select s 232) (lex_10_232_image s)

theorem lex_10_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4202), (Sat.Literal.pos 4201)] :=
  (lex_10_232_gate s).prop _ (List.Mem.head _)

theorem lex_10_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4202), (Sat.Literal.neg 232), (Sat.Literal.pos 142)] :=
  (lex_10_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4202), (Sat.Literal.pos 232), (Sat.Literal.neg 142)] :=
  (lex_10_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4201), (Sat.Literal.neg 232), (Sat.Literal.neg 142), (Sat.Literal.pos 4202)] :=
  (lex_10_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4201), (Sat.Literal.pos 232), (Sat.Literal.pos 142), (Sat.Literal.pos 4202)] :=
  (lex_10_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4202) = lexBefore s permutation10 231 := by
  exact (positive_lex_of_descriptor s 4202 permutation10 232 (by rfl)).trans ((lex_skipped s permutation10 231 232 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation10 231) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation10 231 by rw [image10_eq]; rfl))

theorem lex_10_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4203) (Sat.Literal.pos 4202) (Sat.Literal.pos 231) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation10 231 (assignment s)
    (Sat.Literal.pos 4203) (Sat.Literal.pos 4202) (Sat.Literal.pos 231) (Sat.Literal.pos 126) (positive_of_descriptor s 4203 (.lex permutation10 231) (by rfl)) (lex_10_231_prefix s) (positive_select s 231) (lex_10_231_image s)

theorem lex_10_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4202), (Sat.Literal.pos 231), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation10 231 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4202) (Sat.Literal.pos 231) (Sat.Literal.pos 126) (lex_10_231_prefix s) (positive_select s 231) (lex_10_231_image s)

theorem lex_10_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4203), (Sat.Literal.pos 4202)] :=
  (lex_10_231_gate s).prop _ (List.Mem.head _)

theorem lex_10_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4203), (Sat.Literal.neg 231), (Sat.Literal.pos 126)] :=
  (lex_10_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4203), (Sat.Literal.pos 231), (Sat.Literal.neg 126)] :=
  (lex_10_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4202), (Sat.Literal.neg 231), (Sat.Literal.neg 126), (Sat.Literal.pos 4203)] :=
  (lex_10_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4202), (Sat.Literal.pos 231), (Sat.Literal.pos 126), (Sat.Literal.pos 4203)] :=
  (lex_10_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4203) = lexBefore s permutation10 230 := by
  exact (positive_lex_of_descriptor s 4203 permutation10 231 (by rfl)).trans ((lex_skipped s permutation10 230 231 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation10 230) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation10 230 by rw [image10_eq]; rfl))

theorem lex_10_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4204) (Sat.Literal.pos 4203) (Sat.Literal.pos 230) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation10 230 (assignment s)
    (Sat.Literal.pos 4204) (Sat.Literal.pos 4203) (Sat.Literal.pos 230) (Sat.Literal.pos 110) (positive_of_descriptor s 4204 (.lex permutation10 230) (by rfl)) (lex_10_230_prefix s) (positive_select s 230) (lex_10_230_image s)

theorem lex_10_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4203), (Sat.Literal.pos 230), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation10 230 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4203) (Sat.Literal.pos 230) (Sat.Literal.pos 110) (lex_10_230_prefix s) (positive_select s 230) (lex_10_230_image s)

theorem lex_10_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4204), (Sat.Literal.pos 4203)] :=
  (lex_10_230_gate s).prop _ (List.Mem.head _)

theorem lex_10_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4204), (Sat.Literal.neg 230), (Sat.Literal.pos 110)] :=
  (lex_10_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4204), (Sat.Literal.pos 230), (Sat.Literal.neg 110)] :=
  (lex_10_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4203), (Sat.Literal.neg 230), (Sat.Literal.neg 110), (Sat.Literal.pos 4204)] :=
  (lex_10_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4203), (Sat.Literal.pos 230), (Sat.Literal.pos 110), (Sat.Literal.pos 4204)] :=
  (lex_10_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4204) = lexBefore s permutation10 229 := by
  exact (positive_lex_of_descriptor s 4204 permutation10 230 (by rfl)).trans ((lex_skipped s permutation10 229 230 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation10 229) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation10 229 by rw [image10_eq]; rfl))

theorem lex_10_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4205) (Sat.Literal.pos 4204) (Sat.Literal.pos 229) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation10 229 (assignment s)
    (Sat.Literal.pos 4205) (Sat.Literal.pos 4204) (Sat.Literal.pos 229) (Sat.Literal.pos 94) (positive_of_descriptor s 4205 (.lex permutation10 229) (by rfl)) (lex_10_229_prefix s) (positive_select s 229) (lex_10_229_image s)

theorem lex_10_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4204), (Sat.Literal.pos 229), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation10 229 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4204) (Sat.Literal.pos 229) (Sat.Literal.pos 94) (lex_10_229_prefix s) (positive_select s 229) (lex_10_229_image s)

theorem lex_10_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4205), (Sat.Literal.pos 4204)] :=
  (lex_10_229_gate s).prop _ (List.Mem.head _)

theorem lex_10_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4205), (Sat.Literal.neg 229), (Sat.Literal.pos 94)] :=
  (lex_10_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4205), (Sat.Literal.pos 229), (Sat.Literal.neg 94)] :=
  (lex_10_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4204), (Sat.Literal.neg 229), (Sat.Literal.neg 94), (Sat.Literal.pos 4205)] :=
  (lex_10_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4204), (Sat.Literal.pos 229), (Sat.Literal.pos 94), (Sat.Literal.pos 4205)] :=
  (lex_10_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4205) = lexBefore s permutation10 228 := by
  exact (positive_lex_of_descriptor s 4205 permutation10 229 (by rfl)).trans ((lex_skipped s permutation10 228 229 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation10 228) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation10 228 by rw [image10_eq]; rfl))

theorem lex_10_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4206) (Sat.Literal.pos 4205) (Sat.Literal.pos 228) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation10 228 (assignment s)
    (Sat.Literal.pos 4206) (Sat.Literal.pos 4205) (Sat.Literal.pos 228) (Sat.Literal.pos 78) (positive_of_descriptor s 4206 (.lex permutation10 228) (by rfl)) (lex_10_228_prefix s) (positive_select s 228) (lex_10_228_image s)

theorem lex_10_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4205), (Sat.Literal.pos 228), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation10 228 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4205) (Sat.Literal.pos 228) (Sat.Literal.pos 78) (lex_10_228_prefix s) (positive_select s 228) (lex_10_228_image s)

theorem lex_10_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4206), (Sat.Literal.pos 4205)] :=
  (lex_10_228_gate s).prop _ (List.Mem.head _)

theorem lex_10_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4206), (Sat.Literal.neg 228), (Sat.Literal.pos 78)] :=
  (lex_10_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4206), (Sat.Literal.pos 228), (Sat.Literal.neg 78)] :=
  (lex_10_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4205), (Sat.Literal.neg 228), (Sat.Literal.neg 78), (Sat.Literal.pos 4206)] :=
  (lex_10_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4205), (Sat.Literal.pos 228), (Sat.Literal.pos 78), (Sat.Literal.pos 4206)] :=
  (lex_10_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4206) = lexBefore s permutation10 227 := by
  exact (positive_lex_of_descriptor s 4206 permutation10 228 (by rfl)).trans ((lex_skipped s permutation10 227 228 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation10 227) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation10 227 by rw [image10_eq]; rfl))

theorem lex_10_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4207) (Sat.Literal.pos 4206) (Sat.Literal.pos 227) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation10 227 (assignment s)
    (Sat.Literal.pos 4207) (Sat.Literal.pos 4206) (Sat.Literal.pos 227) (Sat.Literal.pos 62) (positive_of_descriptor s 4207 (.lex permutation10 227) (by rfl)) (lex_10_227_prefix s) (positive_select s 227) (lex_10_227_image s)

theorem lex_10_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4206), (Sat.Literal.pos 227), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation10 227 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4206) (Sat.Literal.pos 227) (Sat.Literal.pos 62) (lex_10_227_prefix s) (positive_select s 227) (lex_10_227_image s)

theorem lex_10_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4207), (Sat.Literal.pos 4206)] :=
  (lex_10_227_gate s).prop _ (List.Mem.head _)

theorem lex_10_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4207), (Sat.Literal.neg 227), (Sat.Literal.pos 62)] :=
  (lex_10_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4207), (Sat.Literal.pos 227), (Sat.Literal.neg 62)] :=
  (lex_10_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4206), (Sat.Literal.neg 227), (Sat.Literal.neg 62), (Sat.Literal.pos 4207)] :=
  (lex_10_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4206), (Sat.Literal.pos 227), (Sat.Literal.pos 62), (Sat.Literal.pos 4207)] :=
  (lex_10_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4207) = lexBefore s permutation10 226 := by
  exact (positive_lex_of_descriptor s 4207 permutation10 227 (by rfl)).trans ((lex_skipped s permutation10 226 227 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation10 226) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation10 226 by rw [image10_eq]; rfl))

theorem lex_10_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4208) (Sat.Literal.pos 4207) (Sat.Literal.pos 226) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation10 226 (assignment s)
    (Sat.Literal.pos 4208) (Sat.Literal.pos 4207) (Sat.Literal.pos 226) (Sat.Literal.pos 46) (positive_of_descriptor s 4208 (.lex permutation10 226) (by rfl)) (lex_10_226_prefix s) (positive_select s 226) (lex_10_226_image s)

theorem lex_10_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4207), (Sat.Literal.pos 226), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation10 226 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4207) (Sat.Literal.pos 226) (Sat.Literal.pos 46) (lex_10_226_prefix s) (positive_select s 226) (lex_10_226_image s)

theorem lex_10_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4208), (Sat.Literal.pos 4207)] :=
  (lex_10_226_gate s).prop _ (List.Mem.head _)

theorem lex_10_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4208), (Sat.Literal.neg 226), (Sat.Literal.pos 46)] :=
  (lex_10_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4208), (Sat.Literal.pos 226), (Sat.Literal.neg 46)] :=
  (lex_10_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4207), (Sat.Literal.neg 226), (Sat.Literal.neg 46), (Sat.Literal.pos 4208)] :=
  (lex_10_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4207), (Sat.Literal.pos 226), (Sat.Literal.pos 46), (Sat.Literal.pos 4208)] :=
  (lex_10_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4208) = lexBefore s permutation10 225 := by
  exact (positive_lex_of_descriptor s 4208 permutation10 226 (by rfl)).trans ((lex_skipped s permutation10 225 226 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation10 225) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation10 225 by rw [image10_eq]; rfl))

theorem lex_10_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4209) (Sat.Literal.pos 4208) (Sat.Literal.pos 225) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation10 225 (assignment s)
    (Sat.Literal.pos 4209) (Sat.Literal.pos 4208) (Sat.Literal.pos 225) (Sat.Literal.pos 30) (positive_of_descriptor s 4209 (.lex permutation10 225) (by rfl)) (lex_10_225_prefix s) (positive_select s 225) (lex_10_225_image s)

theorem lex_10_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4208), (Sat.Literal.pos 225), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation10 225 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4208) (Sat.Literal.pos 225) (Sat.Literal.pos 30) (lex_10_225_prefix s) (positive_select s 225) (lex_10_225_image s)

theorem lex_10_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4209), (Sat.Literal.pos 4208)] :=
  (lex_10_225_gate s).prop _ (List.Mem.head _)

theorem lex_10_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4209), (Sat.Literal.neg 225), (Sat.Literal.pos 30)] :=
  (lex_10_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4209), (Sat.Literal.pos 225), (Sat.Literal.neg 30)] :=
  (lex_10_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4208), (Sat.Literal.neg 225), (Sat.Literal.neg 30), (Sat.Literal.pos 4209)] :=
  (lex_10_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4208), (Sat.Literal.pos 225), (Sat.Literal.pos 30), (Sat.Literal.pos 4209)] :=
  (lex_10_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4209) = lexBefore s permutation10 224 := by
  exact (positive_lex_of_descriptor s 4209 permutation10 225 (by rfl)).trans ((lex_skipped s permutation10 224 225 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation10 224) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation10 224 by rw [image10_eq]; rfl))

theorem lex_10_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4210) (Sat.Literal.pos 4209) (Sat.Literal.pos 224) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation10 224 (assignment s)
    (Sat.Literal.pos 4210) (Sat.Literal.pos 4209) (Sat.Literal.pos 224) (Sat.Literal.pos 14) (positive_of_descriptor s 4210 (.lex permutation10 224) (by rfl)) (lex_10_224_prefix s) (positive_select s 224) (lex_10_224_image s)

theorem lex_10_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4209), (Sat.Literal.pos 224), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation10 224 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4209) (Sat.Literal.pos 224) (Sat.Literal.pos 14) (lex_10_224_prefix s) (positive_select s 224) (lex_10_224_image s)

theorem lex_10_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4210), (Sat.Literal.pos 4209)] :=
  (lex_10_224_gate s).prop _ (List.Mem.head _)

theorem lex_10_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4210), (Sat.Literal.neg 224), (Sat.Literal.pos 14)] :=
  (lex_10_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4210), (Sat.Literal.pos 224), (Sat.Literal.neg 14)] :=
  (lex_10_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4209), (Sat.Literal.neg 224), (Sat.Literal.neg 14), (Sat.Literal.pos 4210)] :=
  (lex_10_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4209), (Sat.Literal.pos 224), (Sat.Literal.pos 14), (Sat.Literal.pos 4210)] :=
  (lex_10_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4210) = lexBefore s permutation10 223 := by
  exact (positive_lex_of_descriptor s 4210 permutation10 224 (by rfl)).trans ((lex_skipped s permutation10 223 224 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation10 223) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation10 223 by rw [image10_eq]; rfl))

theorem lex_10_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4211) (Sat.Literal.pos 4210) (Sat.Literal.pos 223) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation10 223 (assignment s)
    (Sat.Literal.pos 4211) (Sat.Literal.pos 4210) (Sat.Literal.pos 223) (Sat.Literal.pos 253) (positive_of_descriptor s 4211 (.lex permutation10 223) (by rfl)) (lex_10_223_prefix s) (positive_select s 223) (lex_10_223_image s)

theorem lex_10_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4210), (Sat.Literal.pos 223), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation10 223 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4210) (Sat.Literal.pos 223) (Sat.Literal.pos 253) (lex_10_223_prefix s) (positive_select s 223) (lex_10_223_image s)

theorem lex_10_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4211), (Sat.Literal.pos 4210)] :=
  (lex_10_223_gate s).prop _ (List.Mem.head _)

theorem lex_10_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4211), (Sat.Literal.neg 223), (Sat.Literal.pos 253)] :=
  (lex_10_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4211), (Sat.Literal.pos 223), (Sat.Literal.neg 253)] :=
  (lex_10_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4210), (Sat.Literal.neg 223), (Sat.Literal.neg 253), (Sat.Literal.pos 4211)] :=
  (lex_10_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4210), (Sat.Literal.pos 223), (Sat.Literal.pos 253), (Sat.Literal.pos 4211)] :=
  (lex_10_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4211) = lexBefore s permutation10 222 := by
  exact (positive_lex_of_descriptor s 4211 permutation10 223 (by rfl)).trans ((lex_skipped s permutation10 222 223 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation10 222) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation10 222 by rw [image10_eq]; rfl))

theorem lex_10_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4212) (Sat.Literal.pos 4211) (Sat.Literal.pos 222) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation10 222 (assignment s)
    (Sat.Literal.pos 4212) (Sat.Literal.pos 4211) (Sat.Literal.pos 222) (Sat.Literal.pos 237) (positive_of_descriptor s 4212 (.lex permutation10 222) (by rfl)) (lex_10_222_prefix s) (positive_select s 222) (lex_10_222_image s)

theorem lex_10_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4211), (Sat.Literal.pos 222), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation10 222 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4211) (Sat.Literal.pos 222) (Sat.Literal.pos 237) (lex_10_222_prefix s) (positive_select s 222) (lex_10_222_image s)

theorem lex_10_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4212), (Sat.Literal.pos 4211)] :=
  (lex_10_222_gate s).prop _ (List.Mem.head _)

theorem lex_10_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4212), (Sat.Literal.neg 222), (Sat.Literal.pos 237)] :=
  (lex_10_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4212), (Sat.Literal.pos 222), (Sat.Literal.neg 237)] :=
  (lex_10_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4211), (Sat.Literal.neg 222), (Sat.Literal.neg 237), (Sat.Literal.pos 4212)] :=
  (lex_10_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4211), (Sat.Literal.pos 222), (Sat.Literal.pos 237), (Sat.Literal.pos 4212)] :=
  (lex_10_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4212) = lexBefore s permutation10 220 := by
  exact (positive_lex_of_descriptor s 4212 permutation10 222 (by rfl)).trans ((lex_skipped s permutation10 220 222 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 221 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation10 220) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation10 220 by rw [image10_eq]; rfl))

theorem lex_10_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4213) (Sat.Literal.pos 4212) (Sat.Literal.pos 220) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation10 220 (assignment s)
    (Sat.Literal.pos 4213) (Sat.Literal.pos 4212) (Sat.Literal.pos 220) (Sat.Literal.pos 205) (positive_of_descriptor s 4213 (.lex permutation10 220) (by rfl)) (lex_10_220_prefix s) (positive_select s 220) (lex_10_220_image s)

theorem lex_10_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4212), (Sat.Literal.pos 220), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation10 220 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4212) (Sat.Literal.pos 220) (Sat.Literal.pos 205) (lex_10_220_prefix s) (positive_select s 220) (lex_10_220_image s)

theorem lex_10_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4213), (Sat.Literal.pos 4212)] :=
  (lex_10_220_gate s).prop _ (List.Mem.head _)

theorem lex_10_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4213), (Sat.Literal.neg 220), (Sat.Literal.pos 205)] :=
  (lex_10_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4213), (Sat.Literal.pos 220), (Sat.Literal.neg 205)] :=
  (lex_10_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4212), (Sat.Literal.neg 220), (Sat.Literal.neg 205), (Sat.Literal.pos 4213)] :=
  (lex_10_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4212), (Sat.Literal.pos 220), (Sat.Literal.pos 205), (Sat.Literal.pos 4213)] :=
  (lex_10_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4213) = lexBefore s permutation10 219 := by
  exact (positive_lex_of_descriptor s 4213 permutation10 220 (by rfl)).trans ((lex_skipped s permutation10 219 220 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation10 219) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation10 219 by rw [image10_eq]; rfl))

theorem lex_10_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4214) (Sat.Literal.pos 4213) (Sat.Literal.pos 219) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation10 219 (assignment s)
    (Sat.Literal.pos 4214) (Sat.Literal.pos 4213) (Sat.Literal.pos 219) (Sat.Literal.pos 189) (positive_of_descriptor s 4214 (.lex permutation10 219) (by rfl)) (lex_10_219_prefix s) (positive_select s 219) (lex_10_219_image s)

theorem lex_10_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4213), (Sat.Literal.pos 219), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation10 219 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4213) (Sat.Literal.pos 219) (Sat.Literal.pos 189) (lex_10_219_prefix s) (positive_select s 219) (lex_10_219_image s)

theorem lex_10_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4214), (Sat.Literal.pos 4213)] :=
  (lex_10_219_gate s).prop _ (List.Mem.head _)

theorem lex_10_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4214), (Sat.Literal.neg 219), (Sat.Literal.pos 189)] :=
  (lex_10_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4214), (Sat.Literal.pos 219), (Sat.Literal.neg 189)] :=
  (lex_10_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4213), (Sat.Literal.neg 219), (Sat.Literal.neg 189), (Sat.Literal.pos 4214)] :=
  (lex_10_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4213), (Sat.Literal.pos 219), (Sat.Literal.pos 189), (Sat.Literal.pos 4214)] :=
  (lex_10_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4214) = lexBefore s permutation10 218 := by
  exact (positive_lex_of_descriptor s 4214 permutation10 219 (by rfl)).trans ((lex_skipped s permutation10 218 219 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation10 218) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation10 218 by rw [image10_eq]; rfl))

theorem lex_10_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4215) (Sat.Literal.pos 4214) (Sat.Literal.pos 218) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation10 218 (assignment s)
    (Sat.Literal.pos 4215) (Sat.Literal.pos 4214) (Sat.Literal.pos 218) (Sat.Literal.pos 173) (positive_of_descriptor s 4215 (.lex permutation10 218) (by rfl)) (lex_10_218_prefix s) (positive_select s 218) (lex_10_218_image s)

theorem lex_10_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4214), (Sat.Literal.pos 218), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation10 218 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4214) (Sat.Literal.pos 218) (Sat.Literal.pos 173) (lex_10_218_prefix s) (positive_select s 218) (lex_10_218_image s)

theorem lex_10_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4215), (Sat.Literal.pos 4214)] :=
  (lex_10_218_gate s).prop _ (List.Mem.head _)

theorem lex_10_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4215), (Sat.Literal.neg 218), (Sat.Literal.pos 173)] :=
  (lex_10_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4215), (Sat.Literal.pos 218), (Sat.Literal.neg 173)] :=
  (lex_10_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4214), (Sat.Literal.neg 218), (Sat.Literal.neg 173), (Sat.Literal.pos 4215)] :=
  (lex_10_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4214), (Sat.Literal.pos 218), (Sat.Literal.pos 173), (Sat.Literal.pos 4215)] :=
  (lex_10_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4215) = lexBefore s permutation10 217 := by
  exact (positive_lex_of_descriptor s 4215 permutation10 218 (by rfl)).trans ((lex_skipped s permutation10 217 218 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation10 217) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation10 217 by rw [image10_eq]; rfl))

theorem lex_10_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4216) (Sat.Literal.pos 4215) (Sat.Literal.pos 217) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation10 217 (assignment s)
    (Sat.Literal.pos 4216) (Sat.Literal.pos 4215) (Sat.Literal.pos 217) (Sat.Literal.pos 157) (positive_of_descriptor s 4216 (.lex permutation10 217) (by rfl)) (lex_10_217_prefix s) (positive_select s 217) (lex_10_217_image s)

theorem lex_10_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4215), (Sat.Literal.pos 217), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation10 217 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4215) (Sat.Literal.pos 217) (Sat.Literal.pos 157) (lex_10_217_prefix s) (positive_select s 217) (lex_10_217_image s)

theorem lex_10_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4216), (Sat.Literal.pos 4215)] :=
  (lex_10_217_gate s).prop _ (List.Mem.head _)

theorem lex_10_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4216), (Sat.Literal.neg 217), (Sat.Literal.pos 157)] :=
  (lex_10_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4216), (Sat.Literal.pos 217), (Sat.Literal.neg 157)] :=
  (lex_10_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4215), (Sat.Literal.neg 217), (Sat.Literal.neg 157), (Sat.Literal.pos 4216)] :=
  (lex_10_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4215), (Sat.Literal.pos 217), (Sat.Literal.pos 157), (Sat.Literal.pos 4216)] :=
  (lex_10_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4216) = lexBefore s permutation10 216 := by
  exact (positive_lex_of_descriptor s 4216 permutation10 217 (by rfl)).trans ((lex_skipped s permutation10 216 217 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation10 216) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation10 216 by rw [image10_eq]; rfl))

theorem lex_10_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4217) (Sat.Literal.pos 4216) (Sat.Literal.pos 216) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation10 216 (assignment s)
    (Sat.Literal.pos 4217) (Sat.Literal.pos 4216) (Sat.Literal.pos 216) (Sat.Literal.pos 141) (positive_of_descriptor s 4217 (.lex permutation10 216) (by rfl)) (lex_10_216_prefix s) (positive_select s 216) (lex_10_216_image s)

theorem lex_10_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4216), (Sat.Literal.pos 216), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation10 216 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4216) (Sat.Literal.pos 216) (Sat.Literal.pos 141) (lex_10_216_prefix s) (positive_select s 216) (lex_10_216_image s)

theorem lex_10_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4217), (Sat.Literal.pos 4216)] :=
  (lex_10_216_gate s).prop _ (List.Mem.head _)

theorem lex_10_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4217), (Sat.Literal.neg 216), (Sat.Literal.pos 141)] :=
  (lex_10_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4217), (Sat.Literal.pos 216), (Sat.Literal.neg 141)] :=
  (lex_10_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4216), (Sat.Literal.neg 216), (Sat.Literal.neg 141), (Sat.Literal.pos 4217)] :=
  (lex_10_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4216), (Sat.Literal.pos 216), (Sat.Literal.pos 141), (Sat.Literal.pos 4217)] :=
  (lex_10_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4217) = lexBefore s permutation10 215 := by
  exact (positive_lex_of_descriptor s 4217 permutation10 216 (by rfl)).trans ((lex_skipped s permutation10 215 216 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation10 215) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation10 215 by rw [image10_eq]; rfl))

theorem lex_10_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4218) (Sat.Literal.pos 4217) (Sat.Literal.pos 215) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation10 215 (assignment s)
    (Sat.Literal.pos 4218) (Sat.Literal.pos 4217) (Sat.Literal.pos 215) (Sat.Literal.pos 125) (positive_of_descriptor s 4218 (.lex permutation10 215) (by rfl)) (lex_10_215_prefix s) (positive_select s 215) (lex_10_215_image s)

theorem lex_10_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4217), (Sat.Literal.pos 215), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation10 215 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4217) (Sat.Literal.pos 215) (Sat.Literal.pos 125) (lex_10_215_prefix s) (positive_select s 215) (lex_10_215_image s)

theorem lex_10_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4218), (Sat.Literal.pos 4217)] :=
  (lex_10_215_gate s).prop _ (List.Mem.head _)

theorem lex_10_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4218), (Sat.Literal.neg 215), (Sat.Literal.pos 125)] :=
  (lex_10_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4218), (Sat.Literal.pos 215), (Sat.Literal.neg 125)] :=
  (lex_10_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4217), (Sat.Literal.neg 215), (Sat.Literal.neg 125), (Sat.Literal.pos 4218)] :=
  (lex_10_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4217), (Sat.Literal.pos 215), (Sat.Literal.pos 125), (Sat.Literal.pos 4218)] :=
  (lex_10_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4218) = lexBefore s permutation10 214 := by
  exact (positive_lex_of_descriptor s 4218 permutation10 215 (by rfl)).trans ((lex_skipped s permutation10 214 215 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation10 214) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation10 214 by rw [image10_eq]; rfl))

theorem lex_10_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4219) (Sat.Literal.pos 4218) (Sat.Literal.pos 214) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation10 214 (assignment s)
    (Sat.Literal.pos 4219) (Sat.Literal.pos 4218) (Sat.Literal.pos 214) (Sat.Literal.pos 109) (positive_of_descriptor s 4219 (.lex permutation10 214) (by rfl)) (lex_10_214_prefix s) (positive_select s 214) (lex_10_214_image s)

theorem lex_10_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4218), (Sat.Literal.pos 214), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation10 214 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4218) (Sat.Literal.pos 214) (Sat.Literal.pos 109) (lex_10_214_prefix s) (positive_select s 214) (lex_10_214_image s)

theorem lex_10_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4219), (Sat.Literal.pos 4218)] :=
  (lex_10_214_gate s).prop _ (List.Mem.head _)

theorem lex_10_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4219), (Sat.Literal.neg 214), (Sat.Literal.pos 109)] :=
  (lex_10_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4219), (Sat.Literal.pos 214), (Sat.Literal.neg 109)] :=
  (lex_10_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4218), (Sat.Literal.neg 214), (Sat.Literal.neg 109), (Sat.Literal.pos 4219)] :=
  (lex_10_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4218), (Sat.Literal.pos 214), (Sat.Literal.pos 109), (Sat.Literal.pos 4219)] :=
  (lex_10_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4219) = lexBefore s permutation10 213 := by
  exact (positive_lex_of_descriptor s 4219 permutation10 214 (by rfl)).trans ((lex_skipped s permutation10 213 214 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation10 213) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation10 213 by rw [image10_eq]; rfl))

theorem lex_10_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4220) (Sat.Literal.pos 4219) (Sat.Literal.pos 213) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation10 213 (assignment s)
    (Sat.Literal.pos 4220) (Sat.Literal.pos 4219) (Sat.Literal.pos 213) (Sat.Literal.pos 93) (positive_of_descriptor s 4220 (.lex permutation10 213) (by rfl)) (lex_10_213_prefix s) (positive_select s 213) (lex_10_213_image s)

theorem lex_10_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4219), (Sat.Literal.pos 213), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation10 213 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4219) (Sat.Literal.pos 213) (Sat.Literal.pos 93) (lex_10_213_prefix s) (positive_select s 213) (lex_10_213_image s)

theorem lex_10_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4220), (Sat.Literal.pos 4219)] :=
  (lex_10_213_gate s).prop _ (List.Mem.head _)

theorem lex_10_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4220), (Sat.Literal.neg 213), (Sat.Literal.pos 93)] :=
  (lex_10_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4220), (Sat.Literal.pos 213), (Sat.Literal.neg 93)] :=
  (lex_10_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4219), (Sat.Literal.neg 213), (Sat.Literal.neg 93), (Sat.Literal.pos 4220)] :=
  (lex_10_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4219), (Sat.Literal.pos 213), (Sat.Literal.pos 93), (Sat.Literal.pos 4220)] :=
  (lex_10_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4220) = lexBefore s permutation10 212 := by
  exact (positive_lex_of_descriptor s 4220 permutation10 213 (by rfl)).trans ((lex_skipped s permutation10 212 213 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation10 212) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation10 212 by rw [image10_eq]; rfl))

theorem lex_10_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4221) (Sat.Literal.pos 4220) (Sat.Literal.pos 212) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation10 212 (assignment s)
    (Sat.Literal.pos 4221) (Sat.Literal.pos 4220) (Sat.Literal.pos 212) (Sat.Literal.pos 77) (positive_of_descriptor s 4221 (.lex permutation10 212) (by rfl)) (lex_10_212_prefix s) (positive_select s 212) (lex_10_212_image s)

theorem lex_10_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4220), (Sat.Literal.pos 212), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation10 212 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4220) (Sat.Literal.pos 212) (Sat.Literal.pos 77) (lex_10_212_prefix s) (positive_select s 212) (lex_10_212_image s)

theorem lex_10_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4221), (Sat.Literal.pos 4220)] :=
  (lex_10_212_gate s).prop _ (List.Mem.head _)

theorem lex_10_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4221), (Sat.Literal.neg 212), (Sat.Literal.pos 77)] :=
  (lex_10_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4221), (Sat.Literal.pos 212), (Sat.Literal.neg 77)] :=
  (lex_10_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4220), (Sat.Literal.neg 212), (Sat.Literal.neg 77), (Sat.Literal.pos 4221)] :=
  (lex_10_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4220), (Sat.Literal.pos 212), (Sat.Literal.pos 77), (Sat.Literal.pos 4221)] :=
  (lex_10_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4221) = lexBefore s permutation10 211 := by
  exact (positive_lex_of_descriptor s 4221 permutation10 212 (by rfl)).trans ((lex_skipped s permutation10 211 212 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation10 211) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation10 211 by rw [image10_eq]; rfl))

theorem lex_10_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4222) (Sat.Literal.pos 4221) (Sat.Literal.pos 211) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation10 211 (assignment s)
    (Sat.Literal.pos 4222) (Sat.Literal.pos 4221) (Sat.Literal.pos 211) (Sat.Literal.pos 61) (positive_of_descriptor s 4222 (.lex permutation10 211) (by rfl)) (lex_10_211_prefix s) (positive_select s 211) (lex_10_211_image s)

theorem lex_10_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4221), (Sat.Literal.pos 211), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation10 211 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4221) (Sat.Literal.pos 211) (Sat.Literal.pos 61) (lex_10_211_prefix s) (positive_select s 211) (lex_10_211_image s)

theorem lex_10_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4222), (Sat.Literal.pos 4221)] :=
  (lex_10_211_gate s).prop _ (List.Mem.head _)

theorem lex_10_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4222), (Sat.Literal.neg 211), (Sat.Literal.pos 61)] :=
  (lex_10_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4222), (Sat.Literal.pos 211), (Sat.Literal.neg 61)] :=
  (lex_10_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4221), (Sat.Literal.neg 211), (Sat.Literal.neg 61), (Sat.Literal.pos 4222)] :=
  (lex_10_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4221), (Sat.Literal.pos 211), (Sat.Literal.pos 61), (Sat.Literal.pos 4222)] :=
  (lex_10_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4222) = lexBefore s permutation10 210 := by
  exact (positive_lex_of_descriptor s 4222 permutation10 211 (by rfl)).trans ((lex_skipped s permutation10 210 211 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation10 210) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation10 210 by rw [image10_eq]; rfl))

theorem lex_10_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4223) (Sat.Literal.pos 4222) (Sat.Literal.pos 210) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation10 210 (assignment s)
    (Sat.Literal.pos 4223) (Sat.Literal.pos 4222) (Sat.Literal.pos 210) (Sat.Literal.pos 45) (positive_of_descriptor s 4223 (.lex permutation10 210) (by rfl)) (lex_10_210_prefix s) (positive_select s 210) (lex_10_210_image s)

theorem lex_10_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4222), (Sat.Literal.pos 210), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation10 210 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4222) (Sat.Literal.pos 210) (Sat.Literal.pos 45) (lex_10_210_prefix s) (positive_select s 210) (lex_10_210_image s)

theorem lex_10_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4223), (Sat.Literal.pos 4222)] :=
  (lex_10_210_gate s).prop _ (List.Mem.head _)

theorem lex_10_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4223), (Sat.Literal.neg 210), (Sat.Literal.pos 45)] :=
  (lex_10_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4223), (Sat.Literal.pos 210), (Sat.Literal.neg 45)] :=
  (lex_10_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4222), (Sat.Literal.neg 210), (Sat.Literal.neg 45), (Sat.Literal.pos 4223)] :=
  (lex_10_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4222), (Sat.Literal.pos 210), (Sat.Literal.pos 45), (Sat.Literal.pos 4223)] :=
  (lex_10_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_10_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4223) = lexBefore s permutation10 209 := by
  exact (positive_lex_of_descriptor s 4223 permutation10 210 (by rfl)).trans ((lex_skipped s permutation10 209 210 (by decide) (by intro j hj hp; rw [image10_eq]; exact fixedOnRange_spec image10 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_10_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation10 209) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation10 209 by rw [image10_eq]; rfl))

theorem lex_10_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4224) (Sat.Literal.pos 4223) (Sat.Literal.pos 209) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation10 209 (assignment s)
    (Sat.Literal.pos 4224) (Sat.Literal.pos 4223) (Sat.Literal.pos 209) (Sat.Literal.pos 29) (positive_of_descriptor s 4224 (.lex permutation10 209) (by rfl)) (lex_10_209_prefix s) (positive_select s 209) (lex_10_209_image s)

theorem lex_10_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4223), (Sat.Literal.pos 209), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation10 209 (hmax permutation10) (assignment s)
    (Sat.Literal.pos 4223) (Sat.Literal.pos 209) (Sat.Literal.pos 29) (lex_10_209_prefix s) (positive_select s 209) (lex_10_209_image s)

theorem lex_10_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4224), (Sat.Literal.pos 4223)] :=
  (lex_10_209_gate s).prop _ (List.Mem.head _)

theorem lex_10_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4224), (Sat.Literal.neg 209), (Sat.Literal.pos 29)] :=
  (lex_10_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_10_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4224), (Sat.Literal.pos 209), (Sat.Literal.neg 29)] :=
  (lex_10_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_10_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4223), (Sat.Literal.neg 209), (Sat.Literal.neg 29), (Sat.Literal.pos 4224)] :=
  (lex_10_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_10_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4223), (Sat.Literal.pos 209), (Sat.Literal.pos 29), (Sat.Literal.pos 4224)] :=
  (lex_10_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_9_56_gate

end Crown.CertificateData
