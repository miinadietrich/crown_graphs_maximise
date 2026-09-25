import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_13_56_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5124) = lexBefore s permutation13 56 := by
  exact (positive_lex_of_descriptor s 5124 permutation13 57 (by rfl)).trans ((lex_skipped s permutation13 56 57 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 57 57 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_56_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation13 56) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation13 56 by rw [image13_eq]; rfl))

theorem lex_13_56_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5125) (Sat.Literal.pos 5124) (Sat.Literal.pos 56) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation13 56 (assignment s)
    (Sat.Literal.pos 5125) (Sat.Literal.pos 5124) (Sat.Literal.pos 56) (Sat.Literal.pos 28) (positive_of_descriptor s 5125 (.lex permutation13 56) (by rfl)) (lex_13_56_prefix s) (positive_select s 56) (lex_13_56_image s)

theorem lex_13_56_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5124), (Sat.Literal.pos 56), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation13 56 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5124) (Sat.Literal.pos 56) (Sat.Literal.pos 28) (lex_13_56_prefix s) (positive_select s 56) (lex_13_56_image s)

theorem lex_13_56_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5125), (Sat.Literal.pos 5124)] :=
  (lex_13_56_gate s).prop _ (List.Mem.head _)

theorem lex_13_56_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5125), (Sat.Literal.neg 56), (Sat.Literal.pos 28)] :=
  (lex_13_56_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_56_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5125), (Sat.Literal.pos 56), (Sat.Literal.neg 28)] :=
  (lex_13_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_56_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5124), (Sat.Literal.neg 56), (Sat.Literal.neg 28), (Sat.Literal.pos 5125)] :=
  (lex_13_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_56_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5124), (Sat.Literal.pos 56), (Sat.Literal.pos 28), (Sat.Literal.pos 5125)] :=
  (lex_13_56_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_55_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5125) = lexBefore s permutation13 55 := by
  exact (positive_lex_of_descriptor s 5125 permutation13 56 (by rfl)).trans ((lex_skipped s permutation13 55 56 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 56 56 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_55_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation13 55) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation13 55 by rw [image13_eq]; rfl))

theorem lex_13_55_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5126) (Sat.Literal.pos 5125) (Sat.Literal.pos 55) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation13 55 (assignment s)
    (Sat.Literal.pos 5126) (Sat.Literal.pos 5125) (Sat.Literal.pos 55) (Sat.Literal.pos 155) (positive_of_descriptor s 5126 (.lex permutation13 55) (by rfl)) (lex_13_55_prefix s) (positive_select s 55) (lex_13_55_image s)

theorem lex_13_55_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5125), (Sat.Literal.pos 55), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation13 55 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5125) (Sat.Literal.pos 55) (Sat.Literal.pos 155) (lex_13_55_prefix s) (positive_select s 55) (lex_13_55_image s)

theorem lex_13_55_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5126), (Sat.Literal.pos 5125)] :=
  (lex_13_55_gate s).prop _ (List.Mem.head _)

theorem lex_13_55_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5126), (Sat.Literal.neg 55), (Sat.Literal.pos 155)] :=
  (lex_13_55_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_55_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5126), (Sat.Literal.pos 55), (Sat.Literal.neg 155)] :=
  (lex_13_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_55_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5125), (Sat.Literal.neg 55), (Sat.Literal.neg 155), (Sat.Literal.pos 5126)] :=
  (lex_13_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_55_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5125), (Sat.Literal.pos 55), (Sat.Literal.pos 155), (Sat.Literal.pos 5126)] :=
  (lex_13_55_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_54_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5126) = lexBefore s permutation13 54 := by
  exact (positive_lex_of_descriptor s 5126 permutation13 55 (by rfl)).trans ((lex_skipped s permutation13 54 55 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 55 55 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_54_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation13 54) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation13 54 by rw [image13_eq]; rfl))

theorem lex_13_54_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5127) (Sat.Literal.pos 5126) (Sat.Literal.pos 54) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation13 54 (assignment s)
    (Sat.Literal.pos 5127) (Sat.Literal.pos 5126) (Sat.Literal.pos 54) (Sat.Literal.pos 27) (positive_of_descriptor s 5127 (.lex permutation13 54) (by rfl)) (lex_13_54_prefix s) (positive_select s 54) (lex_13_54_image s)

theorem lex_13_54_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5126), (Sat.Literal.pos 54), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation13 54 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5126) (Sat.Literal.pos 54) (Sat.Literal.pos 27) (lex_13_54_prefix s) (positive_select s 54) (lex_13_54_image s)

theorem lex_13_54_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5127), (Sat.Literal.pos 5126)] :=
  (lex_13_54_gate s).prop _ (List.Mem.head _)

theorem lex_13_54_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5127), (Sat.Literal.neg 54), (Sat.Literal.pos 27)] :=
  (lex_13_54_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_54_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5127), (Sat.Literal.pos 54), (Sat.Literal.neg 27)] :=
  (lex_13_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_54_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5126), (Sat.Literal.neg 54), (Sat.Literal.neg 27), (Sat.Literal.pos 5127)] :=
  (lex_13_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_54_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5126), (Sat.Literal.pos 54), (Sat.Literal.pos 27), (Sat.Literal.pos 5127)] :=
  (lex_13_54_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_53_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5127) = lexBefore s permutation13 53 := by
  exact (positive_lex_of_descriptor s 5127 permutation13 54 (by rfl)).trans ((lex_skipped s permutation13 53 54 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 54 54 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_53_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation13 53) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation13 53 by rw [image13_eq]; rfl))

theorem lex_13_53_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5128) (Sat.Literal.pos 5127) (Sat.Literal.pos 53) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation13 53 (assignment s)
    (Sat.Literal.pos 5128) (Sat.Literal.pos 5127) (Sat.Literal.pos 53) (Sat.Literal.pos 154) (positive_of_descriptor s 5128 (.lex permutation13 53) (by rfl)) (lex_13_53_prefix s) (positive_select s 53) (lex_13_53_image s)

theorem lex_13_53_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5127), (Sat.Literal.pos 53), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation13 53 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5127) (Sat.Literal.pos 53) (Sat.Literal.pos 154) (lex_13_53_prefix s) (positive_select s 53) (lex_13_53_image s)

theorem lex_13_53_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5128), (Sat.Literal.pos 5127)] :=
  (lex_13_53_gate s).prop _ (List.Mem.head _)

theorem lex_13_53_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5128), (Sat.Literal.neg 53), (Sat.Literal.pos 154)] :=
  (lex_13_53_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_53_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5128), (Sat.Literal.pos 53), (Sat.Literal.neg 154)] :=
  (lex_13_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_53_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5127), (Sat.Literal.neg 53), (Sat.Literal.neg 154), (Sat.Literal.pos 5128)] :=
  (lex_13_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_53_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5127), (Sat.Literal.pos 53), (Sat.Literal.pos 154), (Sat.Literal.pos 5128)] :=
  (lex_13_53_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_52_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5128) = lexBefore s permutation13 52 := by
  exact (positive_lex_of_descriptor s 5128 permutation13 53 (by rfl)).trans ((lex_skipped s permutation13 52 53 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 53 53 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_52_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation13 52) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation13 52 by rw [image13_eq]; rfl))

theorem lex_13_52_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5129) (Sat.Literal.pos 5128) (Sat.Literal.pos 52) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation13 52 (assignment s)
    (Sat.Literal.pos 5129) (Sat.Literal.pos 5128) (Sat.Literal.pos 52) (Sat.Literal.pos 26) (positive_of_descriptor s 5129 (.lex permutation13 52) (by rfl)) (lex_13_52_prefix s) (positive_select s 52) (lex_13_52_image s)

theorem lex_13_52_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5128), (Sat.Literal.pos 52), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation13 52 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5128) (Sat.Literal.pos 52) (Sat.Literal.pos 26) (lex_13_52_prefix s) (positive_select s 52) (lex_13_52_image s)

theorem lex_13_52_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5129), (Sat.Literal.pos 5128)] :=
  (lex_13_52_gate s).prop _ (List.Mem.head _)

theorem lex_13_52_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5129), (Sat.Literal.neg 52), (Sat.Literal.pos 26)] :=
  (lex_13_52_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_52_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5129), (Sat.Literal.pos 52), (Sat.Literal.neg 26)] :=
  (lex_13_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_52_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5128), (Sat.Literal.neg 52), (Sat.Literal.neg 26), (Sat.Literal.pos 5129)] :=
  (lex_13_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_52_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5128), (Sat.Literal.pos 52), (Sat.Literal.pos 26), (Sat.Literal.pos 5129)] :=
  (lex_13_52_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_51_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5129) = lexBefore s permutation13 51 := by
  exact (positive_lex_of_descriptor s 5129 permutation13 52 (by rfl)).trans ((lex_skipped s permutation13 51 52 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 52 52 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_51_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation13 51) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation13 51 by rw [image13_eq]; rfl))

theorem lex_13_51_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5130) (Sat.Literal.pos 5129) (Sat.Literal.pos 51) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation13 51 (assignment s)
    (Sat.Literal.pos 5130) (Sat.Literal.pos 5129) (Sat.Literal.pos 51) (Sat.Literal.pos 153) (positive_of_descriptor s 5130 (.lex permutation13 51) (by rfl)) (lex_13_51_prefix s) (positive_select s 51) (lex_13_51_image s)

theorem lex_13_51_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5129), (Sat.Literal.pos 51), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation13 51 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5129) (Sat.Literal.pos 51) (Sat.Literal.pos 153) (lex_13_51_prefix s) (positive_select s 51) (lex_13_51_image s)

theorem lex_13_51_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5130), (Sat.Literal.pos 5129)] :=
  (lex_13_51_gate s).prop _ (List.Mem.head _)

theorem lex_13_51_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5130), (Sat.Literal.neg 51), (Sat.Literal.pos 153)] :=
  (lex_13_51_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_51_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5130), (Sat.Literal.pos 51), (Sat.Literal.neg 153)] :=
  (lex_13_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_51_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5129), (Sat.Literal.neg 51), (Sat.Literal.neg 153), (Sat.Literal.pos 5130)] :=
  (lex_13_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_51_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5129), (Sat.Literal.pos 51), (Sat.Literal.pos 153), (Sat.Literal.pos 5130)] :=
  (lex_13_51_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_50_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5130) = lexBefore s permutation13 50 := by
  exact (positive_lex_of_descriptor s 5130 permutation13 51 (by rfl)).trans ((lex_skipped s permutation13 50 51 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 51 51 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_50_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation13 50) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation13 50 by rw [image13_eq]; rfl))

theorem lex_13_50_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5131) (Sat.Literal.pos 5130) (Sat.Literal.pos 50) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation13 50 (assignment s)
    (Sat.Literal.pos 5131) (Sat.Literal.pos 5130) (Sat.Literal.pos 50) (Sat.Literal.pos 25) (positive_of_descriptor s 5131 (.lex permutation13 50) (by rfl)) (lex_13_50_prefix s) (positive_select s 50) (lex_13_50_image s)

theorem lex_13_50_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5130), (Sat.Literal.pos 50), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation13 50 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5130) (Sat.Literal.pos 50) (Sat.Literal.pos 25) (lex_13_50_prefix s) (positive_select s 50) (lex_13_50_image s)

theorem lex_13_50_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5131), (Sat.Literal.pos 5130)] :=
  (lex_13_50_gate s).prop _ (List.Mem.head _)

theorem lex_13_50_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5131), (Sat.Literal.neg 50), (Sat.Literal.pos 25)] :=
  (lex_13_50_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_50_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5131), (Sat.Literal.pos 50), (Sat.Literal.neg 25)] :=
  (lex_13_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_50_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5130), (Sat.Literal.neg 50), (Sat.Literal.neg 25), (Sat.Literal.pos 5131)] :=
  (lex_13_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_50_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5130), (Sat.Literal.pos 50), (Sat.Literal.pos 25), (Sat.Literal.pos 5131)] :=
  (lex_13_50_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_49_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5131) = lexBefore s permutation13 49 := by
  exact (positive_lex_of_descriptor s 5131 permutation13 50 (by rfl)).trans ((lex_skipped s permutation13 49 50 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 50 50 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_49_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation13 49) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation13 49 by rw [image13_eq]; rfl))

theorem lex_13_49_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5132) (Sat.Literal.pos 5131) (Sat.Literal.pos 49) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation13 49 (assignment s)
    (Sat.Literal.pos 5132) (Sat.Literal.pos 5131) (Sat.Literal.pos 49) (Sat.Literal.pos 152) (positive_of_descriptor s 5132 (.lex permutation13 49) (by rfl)) (lex_13_49_prefix s) (positive_select s 49) (lex_13_49_image s)

theorem lex_13_49_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5131), (Sat.Literal.pos 49), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation13 49 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5131) (Sat.Literal.pos 49) (Sat.Literal.pos 152) (lex_13_49_prefix s) (positive_select s 49) (lex_13_49_image s)

theorem lex_13_49_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5132), (Sat.Literal.pos 5131)] :=
  (lex_13_49_gate s).prop _ (List.Mem.head _)

theorem lex_13_49_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5132), (Sat.Literal.neg 49), (Sat.Literal.pos 152)] :=
  (lex_13_49_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_49_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5132), (Sat.Literal.pos 49), (Sat.Literal.neg 152)] :=
  (lex_13_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_49_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5131), (Sat.Literal.neg 49), (Sat.Literal.neg 152), (Sat.Literal.pos 5132)] :=
  (lex_13_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_49_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5131), (Sat.Literal.pos 49), (Sat.Literal.pos 152), (Sat.Literal.pos 5132)] :=
  (lex_13_49_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_48_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5132) = lexBefore s permutation13 48 := by
  exact (positive_lex_of_descriptor s 5132 permutation13 49 (by rfl)).trans ((lex_skipped s permutation13 48 49 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 49 49 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_48_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation13 48) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation13 48 by rw [image13_eq]; rfl))

theorem lex_13_48_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5133) (Sat.Literal.pos 5132) (Sat.Literal.pos 48) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation13 48 (assignment s)
    (Sat.Literal.pos 5133) (Sat.Literal.pos 5132) (Sat.Literal.pos 48) (Sat.Literal.pos 24) (positive_of_descriptor s 5133 (.lex permutation13 48) (by rfl)) (lex_13_48_prefix s) (positive_select s 48) (lex_13_48_image s)

theorem lex_13_48_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5132), (Sat.Literal.pos 48), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation13 48 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5132) (Sat.Literal.pos 48) (Sat.Literal.pos 24) (lex_13_48_prefix s) (positive_select s 48) (lex_13_48_image s)

theorem lex_13_48_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5133), (Sat.Literal.pos 5132)] :=
  (lex_13_48_gate s).prop _ (List.Mem.head _)

theorem lex_13_48_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5133), (Sat.Literal.neg 48), (Sat.Literal.pos 24)] :=
  (lex_13_48_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_48_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5133), (Sat.Literal.pos 48), (Sat.Literal.neg 24)] :=
  (lex_13_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_48_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5132), (Sat.Literal.neg 48), (Sat.Literal.neg 24), (Sat.Literal.pos 5133)] :=
  (lex_13_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_48_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5132), (Sat.Literal.pos 48), (Sat.Literal.pos 24), (Sat.Literal.pos 5133)] :=
  (lex_13_48_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_47_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5133) = lexBefore s permutation13 47 := by
  exact (positive_lex_of_descriptor s 5133 permutation13 48 (by rfl)).trans ((lex_skipped s permutation13 47 48 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 48 48 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_47_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation13 47) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation13 47 by rw [image13_eq]; rfl))

theorem lex_13_47_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5134) (Sat.Literal.pos 5133) (Sat.Literal.pos 47) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation13 47 (assignment s)
    (Sat.Literal.pos 5134) (Sat.Literal.pos 5133) (Sat.Literal.pos 47) (Sat.Literal.pos 151) (positive_of_descriptor s 5134 (.lex permutation13 47) (by rfl)) (lex_13_47_prefix s) (positive_select s 47) (lex_13_47_image s)

theorem lex_13_47_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5133), (Sat.Literal.pos 47), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation13 47 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5133) (Sat.Literal.pos 47) (Sat.Literal.pos 151) (lex_13_47_prefix s) (positive_select s 47) (lex_13_47_image s)

theorem lex_13_47_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5134), (Sat.Literal.pos 5133)] :=
  (lex_13_47_gate s).prop _ (List.Mem.head _)

theorem lex_13_47_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5134), (Sat.Literal.neg 47), (Sat.Literal.pos 151)] :=
  (lex_13_47_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_47_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5134), (Sat.Literal.pos 47), (Sat.Literal.neg 151)] :=
  (lex_13_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_47_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5133), (Sat.Literal.neg 47), (Sat.Literal.neg 151), (Sat.Literal.pos 5134)] :=
  (lex_13_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_47_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5133), (Sat.Literal.pos 47), (Sat.Literal.pos 151), (Sat.Literal.pos 5134)] :=
  (lex_13_47_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_46_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5134) = lexBefore s permutation13 46 := by
  exact (positive_lex_of_descriptor s 5134 permutation13 47 (by rfl)).trans ((lex_skipped s permutation13 46 47 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 47 47 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_46_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation13 46) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation13 46 by rw [image13_eq]; rfl))

theorem lex_13_46_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5135) (Sat.Literal.pos 5134) (Sat.Literal.pos 46) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation13 46 (assignment s)
    (Sat.Literal.pos 5135) (Sat.Literal.pos 5134) (Sat.Literal.pos 46) (Sat.Literal.pos 23) (positive_of_descriptor s 5135 (.lex permutation13 46) (by rfl)) (lex_13_46_prefix s) (positive_select s 46) (lex_13_46_image s)

theorem lex_13_46_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5134), (Sat.Literal.pos 46), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation13 46 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5134) (Sat.Literal.pos 46) (Sat.Literal.pos 23) (lex_13_46_prefix s) (positive_select s 46) (lex_13_46_image s)

theorem lex_13_46_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5135), (Sat.Literal.pos 5134)] :=
  (lex_13_46_gate s).prop _ (List.Mem.head _)

theorem lex_13_46_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5135), (Sat.Literal.neg 46), (Sat.Literal.pos 23)] :=
  (lex_13_46_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_46_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5135), (Sat.Literal.pos 46), (Sat.Literal.neg 23)] :=
  (lex_13_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_46_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5134), (Sat.Literal.neg 46), (Sat.Literal.neg 23), (Sat.Literal.pos 5135)] :=
  (lex_13_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_46_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5134), (Sat.Literal.pos 46), (Sat.Literal.pos 23), (Sat.Literal.pos 5135)] :=
  (lex_13_46_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_45_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5135) = lexBefore s permutation13 45 := by
  exact (positive_lex_of_descriptor s 5135 permutation13 46 (by rfl)).trans ((lex_skipped s permutation13 45 46 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 46 46 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_45_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation13 45) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation13 45 by rw [image13_eq]; rfl))

theorem lex_13_45_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5136) (Sat.Literal.pos 5135) (Sat.Literal.pos 45) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation13 45 (assignment s)
    (Sat.Literal.pos 5136) (Sat.Literal.pos 5135) (Sat.Literal.pos 45) (Sat.Literal.pos 150) (positive_of_descriptor s 5136 (.lex permutation13 45) (by rfl)) (lex_13_45_prefix s) (positive_select s 45) (lex_13_45_image s)

theorem lex_13_45_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5135), (Sat.Literal.pos 45), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation13 45 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5135) (Sat.Literal.pos 45) (Sat.Literal.pos 150) (lex_13_45_prefix s) (positive_select s 45) (lex_13_45_image s)

theorem lex_13_45_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5136), (Sat.Literal.pos 5135)] :=
  (lex_13_45_gate s).prop _ (List.Mem.head _)

theorem lex_13_45_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5136), (Sat.Literal.neg 45), (Sat.Literal.pos 150)] :=
  (lex_13_45_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_45_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5136), (Sat.Literal.pos 45), (Sat.Literal.neg 150)] :=
  (lex_13_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_45_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5135), (Sat.Literal.neg 45), (Sat.Literal.neg 150), (Sat.Literal.pos 5136)] :=
  (lex_13_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_45_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5135), (Sat.Literal.pos 45), (Sat.Literal.pos 150), (Sat.Literal.pos 5136)] :=
  (lex_13_45_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_44_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5136) = lexBefore s permutation13 44 := by
  exact (positive_lex_of_descriptor s 5136 permutation13 45 (by rfl)).trans ((lex_skipped s permutation13 44 45 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 45 45 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_44_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation13 44) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation13 44 by rw [image13_eq]; rfl))

theorem lex_13_44_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5137) (Sat.Literal.pos 5136) (Sat.Literal.pos 44) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation13 44 (assignment s)
    (Sat.Literal.pos 5137) (Sat.Literal.pos 5136) (Sat.Literal.pos 44) (Sat.Literal.pos 22) (positive_of_descriptor s 5137 (.lex permutation13 44) (by rfl)) (lex_13_44_prefix s) (positive_select s 44) (lex_13_44_image s)

theorem lex_13_44_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5136), (Sat.Literal.pos 44), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation13 44 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5136) (Sat.Literal.pos 44) (Sat.Literal.pos 22) (lex_13_44_prefix s) (positive_select s 44) (lex_13_44_image s)

theorem lex_13_44_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5137), (Sat.Literal.pos 5136)] :=
  (lex_13_44_gate s).prop _ (List.Mem.head _)

theorem lex_13_44_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5137), (Sat.Literal.neg 44), (Sat.Literal.pos 22)] :=
  (lex_13_44_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_44_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5137), (Sat.Literal.pos 44), (Sat.Literal.neg 22)] :=
  (lex_13_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_44_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5136), (Sat.Literal.neg 44), (Sat.Literal.neg 22), (Sat.Literal.pos 5137)] :=
  (lex_13_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_44_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5136), (Sat.Literal.pos 44), (Sat.Literal.pos 22), (Sat.Literal.pos 5137)] :=
  (lex_13_44_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_43_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5137) = lexBefore s permutation13 43 := by
  exact (positive_lex_of_descriptor s 5137 permutation13 44 (by rfl)).trans ((lex_skipped s permutation13 43 44 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 44 44 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_43_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation13 43) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation13 43 by rw [image13_eq]; rfl))

theorem lex_13_43_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5138) (Sat.Literal.pos 5137) (Sat.Literal.pos 43) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation13 43 (assignment s)
    (Sat.Literal.pos 5138) (Sat.Literal.pos 5137) (Sat.Literal.pos 43) (Sat.Literal.pos 149) (positive_of_descriptor s 5138 (.lex permutation13 43) (by rfl)) (lex_13_43_prefix s) (positive_select s 43) (lex_13_43_image s)

theorem lex_13_43_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5137), (Sat.Literal.pos 43), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation13 43 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5137) (Sat.Literal.pos 43) (Sat.Literal.pos 149) (lex_13_43_prefix s) (positive_select s 43) (lex_13_43_image s)

theorem lex_13_43_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5138), (Sat.Literal.pos 5137)] :=
  (lex_13_43_gate s).prop _ (List.Mem.head _)

theorem lex_13_43_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5138), (Sat.Literal.neg 43), (Sat.Literal.pos 149)] :=
  (lex_13_43_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_43_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5138), (Sat.Literal.pos 43), (Sat.Literal.neg 149)] :=
  (lex_13_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_43_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5137), (Sat.Literal.neg 43), (Sat.Literal.neg 149), (Sat.Literal.pos 5138)] :=
  (lex_13_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_43_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5137), (Sat.Literal.pos 43), (Sat.Literal.pos 149), (Sat.Literal.pos 5138)] :=
  (lex_13_43_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_42_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5138) = lexBefore s permutation13 42 := by
  exact (positive_lex_of_descriptor s 5138 permutation13 43 (by rfl)).trans ((lex_skipped s permutation13 42 43 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 43 43 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_42_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation13 42) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation13 42 by rw [image13_eq]; rfl))

theorem lex_13_42_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5139) (Sat.Literal.pos 5138) (Sat.Literal.pos 42) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation13 42 (assignment s)
    (Sat.Literal.pos 5139) (Sat.Literal.pos 5138) (Sat.Literal.pos 42) (Sat.Literal.pos 21) (positive_of_descriptor s 5139 (.lex permutation13 42) (by rfl)) (lex_13_42_prefix s) (positive_select s 42) (lex_13_42_image s)

theorem lex_13_42_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5138), (Sat.Literal.pos 42), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation13 42 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5138) (Sat.Literal.pos 42) (Sat.Literal.pos 21) (lex_13_42_prefix s) (positive_select s 42) (lex_13_42_image s)

theorem lex_13_42_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5139), (Sat.Literal.pos 5138)] :=
  (lex_13_42_gate s).prop _ (List.Mem.head _)

theorem lex_13_42_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5139), (Sat.Literal.neg 42), (Sat.Literal.pos 21)] :=
  (lex_13_42_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_42_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5139), (Sat.Literal.pos 42), (Sat.Literal.neg 21)] :=
  (lex_13_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_42_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5138), (Sat.Literal.neg 42), (Sat.Literal.neg 21), (Sat.Literal.pos 5139)] :=
  (lex_13_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_42_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5138), (Sat.Literal.pos 42), (Sat.Literal.pos 21), (Sat.Literal.pos 5139)] :=
  (lex_13_42_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_41_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5139) = lexBefore s permutation13 41 := by
  exact (positive_lex_of_descriptor s 5139 permutation13 42 (by rfl)).trans ((lex_skipped s permutation13 41 42 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 42 42 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_41_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation13 41) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation13 41 by rw [image13_eq]; rfl))

theorem lex_13_41_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5140) (Sat.Literal.pos 5139) (Sat.Literal.pos 41) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation13 41 (assignment s)
    (Sat.Literal.pos 5140) (Sat.Literal.pos 5139) (Sat.Literal.pos 41) (Sat.Literal.pos 148) (positive_of_descriptor s 5140 (.lex permutation13 41) (by rfl)) (lex_13_41_prefix s) (positive_select s 41) (lex_13_41_image s)

theorem lex_13_41_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5139), (Sat.Literal.pos 41), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation13 41 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5139) (Sat.Literal.pos 41) (Sat.Literal.pos 148) (lex_13_41_prefix s) (positive_select s 41) (lex_13_41_image s)

theorem lex_13_41_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5140), (Sat.Literal.pos 5139)] :=
  (lex_13_41_gate s).prop _ (List.Mem.head _)

theorem lex_13_41_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5140), (Sat.Literal.neg 41), (Sat.Literal.pos 148)] :=
  (lex_13_41_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_41_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5140), (Sat.Literal.pos 41), (Sat.Literal.neg 148)] :=
  (lex_13_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_41_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5139), (Sat.Literal.neg 41), (Sat.Literal.neg 148), (Sat.Literal.pos 5140)] :=
  (lex_13_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_41_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5139), (Sat.Literal.pos 41), (Sat.Literal.pos 148), (Sat.Literal.pos 5140)] :=
  (lex_13_41_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_40_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5140) = lexBefore s permutation13 40 := by
  exact (positive_lex_of_descriptor s 5140 permutation13 41 (by rfl)).trans ((lex_skipped s permutation13 40 41 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 41 41 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_40_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation13 40) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation13 40 by rw [image13_eq]; rfl))

theorem lex_13_40_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5141) (Sat.Literal.pos 5140) (Sat.Literal.pos 40) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation13 40 (assignment s)
    (Sat.Literal.pos 5141) (Sat.Literal.pos 5140) (Sat.Literal.pos 40) (Sat.Literal.pos 20) (positive_of_descriptor s 5141 (.lex permutation13 40) (by rfl)) (lex_13_40_prefix s) (positive_select s 40) (lex_13_40_image s)

theorem lex_13_40_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5140), (Sat.Literal.pos 40), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation13 40 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5140) (Sat.Literal.pos 40) (Sat.Literal.pos 20) (lex_13_40_prefix s) (positive_select s 40) (lex_13_40_image s)

theorem lex_13_40_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5141), (Sat.Literal.pos 5140)] :=
  (lex_13_40_gate s).prop _ (List.Mem.head _)

theorem lex_13_40_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5141), (Sat.Literal.neg 40), (Sat.Literal.pos 20)] :=
  (lex_13_40_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_40_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5141), (Sat.Literal.pos 40), (Sat.Literal.neg 20)] :=
  (lex_13_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_40_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5140), (Sat.Literal.neg 40), (Sat.Literal.neg 20), (Sat.Literal.pos 5141)] :=
  (lex_13_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_40_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5140), (Sat.Literal.pos 40), (Sat.Literal.pos 20), (Sat.Literal.pos 5141)] :=
  (lex_13_40_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_39_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5141) = lexBefore s permutation13 39 := by
  exact (positive_lex_of_descriptor s 5141 permutation13 40 (by rfl)).trans ((lex_skipped s permutation13 39 40 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 40 40 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_39_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation13 39) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation13 39 by rw [image13_eq]; rfl))

theorem lex_13_39_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5142) (Sat.Literal.pos 5141) (Sat.Literal.pos 39) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation13 39 (assignment s)
    (Sat.Literal.pos 5142) (Sat.Literal.pos 5141) (Sat.Literal.pos 39) (Sat.Literal.pos 147) (positive_of_descriptor s 5142 (.lex permutation13 39) (by rfl)) (lex_13_39_prefix s) (positive_select s 39) (lex_13_39_image s)

theorem lex_13_39_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5141), (Sat.Literal.pos 39), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation13 39 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5141) (Sat.Literal.pos 39) (Sat.Literal.pos 147) (lex_13_39_prefix s) (positive_select s 39) (lex_13_39_image s)

theorem lex_13_39_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5142), (Sat.Literal.pos 5141)] :=
  (lex_13_39_gate s).prop _ (List.Mem.head _)

theorem lex_13_39_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5142), (Sat.Literal.neg 39), (Sat.Literal.pos 147)] :=
  (lex_13_39_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_39_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5142), (Sat.Literal.pos 39), (Sat.Literal.neg 147)] :=
  (lex_13_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_39_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5141), (Sat.Literal.neg 39), (Sat.Literal.neg 147), (Sat.Literal.pos 5142)] :=
  (lex_13_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_39_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5141), (Sat.Literal.pos 39), (Sat.Literal.pos 147), (Sat.Literal.pos 5142)] :=
  (lex_13_39_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_38_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5142) = lexBefore s permutation13 38 := by
  exact (positive_lex_of_descriptor s 5142 permutation13 39 (by rfl)).trans ((lex_skipped s permutation13 38 39 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 39 39 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_38_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation13 38) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation13 38 by rw [image13_eq]; rfl))

theorem lex_13_38_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5143) (Sat.Literal.pos 5142) (Sat.Literal.pos 38) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation13 38 (assignment s)
    (Sat.Literal.pos 5143) (Sat.Literal.pos 5142) (Sat.Literal.pos 38) (Sat.Literal.pos 19) (positive_of_descriptor s 5143 (.lex permutation13 38) (by rfl)) (lex_13_38_prefix s) (positive_select s 38) (lex_13_38_image s)

theorem lex_13_38_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5142), (Sat.Literal.pos 38), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation13 38 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5142) (Sat.Literal.pos 38) (Sat.Literal.pos 19) (lex_13_38_prefix s) (positive_select s 38) (lex_13_38_image s)

theorem lex_13_38_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5143), (Sat.Literal.pos 5142)] :=
  (lex_13_38_gate s).prop _ (List.Mem.head _)

theorem lex_13_38_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5143), (Sat.Literal.neg 38), (Sat.Literal.pos 19)] :=
  (lex_13_38_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_38_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5143), (Sat.Literal.pos 38), (Sat.Literal.neg 19)] :=
  (lex_13_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_38_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5142), (Sat.Literal.neg 38), (Sat.Literal.neg 19), (Sat.Literal.pos 5143)] :=
  (lex_13_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_38_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5142), (Sat.Literal.pos 38), (Sat.Literal.pos 19), (Sat.Literal.pos 5143)] :=
  (lex_13_38_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_37_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5143) = lexBefore s permutation13 37 := by
  exact (positive_lex_of_descriptor s 5143 permutation13 38 (by rfl)).trans ((lex_skipped s permutation13 37 38 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 38 38 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_37_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation13 37) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation13 37 by rw [image13_eq]; rfl))

theorem lex_13_37_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5144) (Sat.Literal.pos 5143) (Sat.Literal.pos 37) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation13 37 (assignment s)
    (Sat.Literal.pos 5144) (Sat.Literal.pos 5143) (Sat.Literal.pos 37) (Sat.Literal.pos 146) (positive_of_descriptor s 5144 (.lex permutation13 37) (by rfl)) (lex_13_37_prefix s) (positive_select s 37) (lex_13_37_image s)

theorem lex_13_37_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5143), (Sat.Literal.pos 37), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation13 37 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5143) (Sat.Literal.pos 37) (Sat.Literal.pos 146) (lex_13_37_prefix s) (positive_select s 37) (lex_13_37_image s)

theorem lex_13_37_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5144), (Sat.Literal.pos 5143)] :=
  (lex_13_37_gate s).prop _ (List.Mem.head _)

theorem lex_13_37_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5144), (Sat.Literal.neg 37), (Sat.Literal.pos 146)] :=
  (lex_13_37_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_37_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5144), (Sat.Literal.pos 37), (Sat.Literal.neg 146)] :=
  (lex_13_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_37_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5143), (Sat.Literal.neg 37), (Sat.Literal.neg 146), (Sat.Literal.pos 5144)] :=
  (lex_13_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_37_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5143), (Sat.Literal.pos 37), (Sat.Literal.pos 146), (Sat.Literal.pos 5144)] :=
  (lex_13_37_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_36_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5144) = lexBefore s permutation13 36 := by
  exact (positive_lex_of_descriptor s 5144 permutation13 37 (by rfl)).trans ((lex_skipped s permutation13 36 37 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 37 37 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_36_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 18) = s (permuteMask permutation13 36) := by
  exact (positive_select s 18).trans (congrArg s (show (18 : Fin 256) = permuteMask permutation13 36 by rw [image13_eq]; rfl))

theorem lex_13_36_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5145) (Sat.Literal.pos 5144) (Sat.Literal.pos 36) (Sat.Literal.pos 18)) := by
  exact equality_gate s permutation13 36 (assignment s)
    (Sat.Literal.pos 5145) (Sat.Literal.pos 5144) (Sat.Literal.pos 36) (Sat.Literal.pos 18) (positive_of_descriptor s 5145 (.lex permutation13 36) (by rfl)) (lex_13_36_prefix s) (positive_select s 36) (lex_13_36_image s)

theorem lex_13_36_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5144), (Sat.Literal.pos 36), (Sat.Literal.neg 18)] := by
  exact comparison_gate s permutation13 36 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5144) (Sat.Literal.pos 36) (Sat.Literal.pos 18) (lex_13_36_prefix s) (positive_select s 36) (lex_13_36_image s)

theorem lex_13_36_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5145), (Sat.Literal.pos 5144)] :=
  (lex_13_36_gate s).prop _ (List.Mem.head _)

theorem lex_13_36_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5145), (Sat.Literal.neg 36), (Sat.Literal.pos 18)] :=
  (lex_13_36_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_36_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5145), (Sat.Literal.pos 36), (Sat.Literal.neg 18)] :=
  (lex_13_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_36_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5144), (Sat.Literal.neg 36), (Sat.Literal.neg 18), (Sat.Literal.pos 5145)] :=
  (lex_13_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_36_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5144), (Sat.Literal.pos 36), (Sat.Literal.pos 18), (Sat.Literal.pos 5145)] :=
  (lex_13_36_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_35_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5145) = lexBefore s permutation13 35 := by
  exact (positive_lex_of_descriptor s 5145 permutation13 36 (by rfl)).trans ((lex_skipped s permutation13 35 36 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 36 36 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_35_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation13 35) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation13 35 by rw [image13_eq]; rfl))

theorem lex_13_35_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5146) (Sat.Literal.pos 5145) (Sat.Literal.pos 35) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation13 35 (assignment s)
    (Sat.Literal.pos 5146) (Sat.Literal.pos 5145) (Sat.Literal.pos 35) (Sat.Literal.pos 145) (positive_of_descriptor s 5146 (.lex permutation13 35) (by rfl)) (lex_13_35_prefix s) (positive_select s 35) (lex_13_35_image s)

theorem lex_13_35_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5145), (Sat.Literal.pos 35), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation13 35 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5145) (Sat.Literal.pos 35) (Sat.Literal.pos 145) (lex_13_35_prefix s) (positive_select s 35) (lex_13_35_image s)

theorem lex_13_35_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5146), (Sat.Literal.pos 5145)] :=
  (lex_13_35_gate s).prop _ (List.Mem.head _)

theorem lex_13_35_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5146), (Sat.Literal.neg 35), (Sat.Literal.pos 145)] :=
  (lex_13_35_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_35_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5146), (Sat.Literal.pos 35), (Sat.Literal.neg 145)] :=
  (lex_13_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_35_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5145), (Sat.Literal.neg 35), (Sat.Literal.neg 145), (Sat.Literal.pos 5146)] :=
  (lex_13_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_35_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5145), (Sat.Literal.pos 35), (Sat.Literal.pos 145), (Sat.Literal.pos 5146)] :=
  (lex_13_35_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_34_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5146) = lexBefore s permutation13 34 := by
  exact (positive_lex_of_descriptor s 5146 permutation13 35 (by rfl)).trans ((lex_skipped s permutation13 34 35 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 35 35 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_34_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 17) = s (permuteMask permutation13 34) := by
  exact (positive_select s 17).trans (congrArg s (show (17 : Fin 256) = permuteMask permutation13 34 by rw [image13_eq]; rfl))

theorem lex_13_34_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5147) (Sat.Literal.pos 5146) (Sat.Literal.pos 34) (Sat.Literal.pos 17)) := by
  exact equality_gate s permutation13 34 (assignment s)
    (Sat.Literal.pos 5147) (Sat.Literal.pos 5146) (Sat.Literal.pos 34) (Sat.Literal.pos 17) (positive_of_descriptor s 5147 (.lex permutation13 34) (by rfl)) (lex_13_34_prefix s) (positive_select s 34) (lex_13_34_image s)

theorem lex_13_34_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5146), (Sat.Literal.pos 34), (Sat.Literal.neg 17)] := by
  exact comparison_gate s permutation13 34 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5146) (Sat.Literal.pos 34) (Sat.Literal.pos 17) (lex_13_34_prefix s) (positive_select s 34) (lex_13_34_image s)

theorem lex_13_34_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5147), (Sat.Literal.pos 5146)] :=
  (lex_13_34_gate s).prop _ (List.Mem.head _)

theorem lex_13_34_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5147), (Sat.Literal.neg 34), (Sat.Literal.pos 17)] :=
  (lex_13_34_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_34_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5147), (Sat.Literal.pos 34), (Sat.Literal.neg 17)] :=
  (lex_13_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_34_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5146), (Sat.Literal.neg 34), (Sat.Literal.neg 17), (Sat.Literal.pos 5147)] :=
  (lex_13_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_34_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5146), (Sat.Literal.pos 34), (Sat.Literal.pos 17), (Sat.Literal.pos 5147)] :=
  (lex_13_34_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_33_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5147) = lexBefore s permutation13 33 := by
  exact (positive_lex_of_descriptor s 5147 permutation13 34 (by rfl)).trans ((lex_skipped s permutation13 33 34 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 34 34 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_33_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation13 33) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation13 33 by rw [image13_eq]; rfl))

theorem lex_13_33_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5148) (Sat.Literal.pos 5147) (Sat.Literal.pos 33) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation13 33 (assignment s)
    (Sat.Literal.pos 5148) (Sat.Literal.pos 5147) (Sat.Literal.pos 33) (Sat.Literal.pos 144) (positive_of_descriptor s 5148 (.lex permutation13 33) (by rfl)) (lex_13_33_prefix s) (positive_select s 33) (lex_13_33_image s)

theorem lex_13_33_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5147), (Sat.Literal.pos 33), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation13 33 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5147) (Sat.Literal.pos 33) (Sat.Literal.pos 144) (lex_13_33_prefix s) (positive_select s 33) (lex_13_33_image s)

theorem lex_13_33_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5148), (Sat.Literal.pos 5147)] :=
  (lex_13_33_gate s).prop _ (List.Mem.head _)

theorem lex_13_33_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5148), (Sat.Literal.neg 33), (Sat.Literal.pos 144)] :=
  (lex_13_33_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_33_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5148), (Sat.Literal.pos 33), (Sat.Literal.neg 144)] :=
  (lex_13_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_33_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5147), (Sat.Literal.neg 33), (Sat.Literal.neg 144), (Sat.Literal.pos 5148)] :=
  (lex_13_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_33_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5147), (Sat.Literal.pos 33), (Sat.Literal.pos 144), (Sat.Literal.pos 5148)] :=
  (lex_13_33_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_32_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5148) = lexBefore s permutation13 32 := by
  exact (positive_lex_of_descriptor s 5148 permutation13 33 (by rfl)).trans ((lex_skipped s permutation13 32 33 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 33 33 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_32_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 16) = s (permuteMask permutation13 32) := by
  exact (positive_select s 16).trans (congrArg s (show (16 : Fin 256) = permuteMask permutation13 32 by rw [image13_eq]; rfl))

theorem lex_13_32_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5149) (Sat.Literal.pos 5148) (Sat.Literal.pos 32) (Sat.Literal.pos 16)) := by
  exact equality_gate s permutation13 32 (assignment s)
    (Sat.Literal.pos 5149) (Sat.Literal.pos 5148) (Sat.Literal.pos 32) (Sat.Literal.pos 16) (positive_of_descriptor s 5149 (.lex permutation13 32) (by rfl)) (lex_13_32_prefix s) (positive_select s 32) (lex_13_32_image s)

theorem lex_13_32_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5148), (Sat.Literal.pos 32), (Sat.Literal.neg 16)] := by
  exact comparison_gate s permutation13 32 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5148) (Sat.Literal.pos 32) (Sat.Literal.pos 16) (lex_13_32_prefix s) (positive_select s 32) (lex_13_32_image s)

theorem lex_13_32_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5149), (Sat.Literal.pos 5148)] :=
  (lex_13_32_gate s).prop _ (List.Mem.head _)

theorem lex_13_32_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5149), (Sat.Literal.neg 32), (Sat.Literal.pos 16)] :=
  (lex_13_32_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_32_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5149), (Sat.Literal.pos 32), (Sat.Literal.neg 16)] :=
  (lex_13_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_32_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5148), (Sat.Literal.neg 32), (Sat.Literal.neg 16), (Sat.Literal.pos 5149)] :=
  (lex_13_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_32_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5148), (Sat.Literal.pos 32), (Sat.Literal.pos 16), (Sat.Literal.pos 5149)] :=
  (lex_13_32_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_31_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5149) = lexBefore s permutation13 31 := by
  exact (positive_lex_of_descriptor s 5149 permutation13 32 (by rfl)).trans ((lex_skipped s permutation13 31 32 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 32 32 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_31_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation13 31) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation13 31 by rw [image13_eq]; rfl))

theorem lex_13_31_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5150) (Sat.Literal.pos 5149) (Sat.Literal.pos 31) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation13 31 (assignment s)
    (Sat.Literal.pos 5150) (Sat.Literal.pos 5149) (Sat.Literal.pos 31) (Sat.Literal.pos 143) (positive_of_descriptor s 5150 (.lex permutation13 31) (by rfl)) (lex_13_31_prefix s) (positive_select s 31) (lex_13_31_image s)

theorem lex_13_31_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5149), (Sat.Literal.pos 31), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation13 31 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5149) (Sat.Literal.pos 31) (Sat.Literal.pos 143) (lex_13_31_prefix s) (positive_select s 31) (lex_13_31_image s)

theorem lex_13_31_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5150), (Sat.Literal.pos 5149)] :=
  (lex_13_31_gate s).prop _ (List.Mem.head _)

theorem lex_13_31_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5150), (Sat.Literal.neg 31), (Sat.Literal.pos 143)] :=
  (lex_13_31_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_31_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5150), (Sat.Literal.pos 31), (Sat.Literal.neg 143)] :=
  (lex_13_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_31_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5149), (Sat.Literal.neg 31), (Sat.Literal.neg 143), (Sat.Literal.pos 5150)] :=
  (lex_13_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_31_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5149), (Sat.Literal.pos 31), (Sat.Literal.pos 143), (Sat.Literal.pos 5150)] :=
  (lex_13_31_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_30_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5150) = lexBefore s permutation13 30 := by
  exact (positive_lex_of_descriptor s 5150 permutation13 31 (by rfl)).trans ((lex_skipped s permutation13 30 31 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 31 31 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_30_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation13 30) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation13 30 by rw [image13_eq]; rfl))

theorem lex_13_30_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5151) (Sat.Literal.pos 5150) (Sat.Literal.pos 30) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation13 30 (assignment s)
    (Sat.Literal.pos 5151) (Sat.Literal.pos 5150) (Sat.Literal.pos 30) (Sat.Literal.pos 15) (positive_of_descriptor s 5151 (.lex permutation13 30) (by rfl)) (lex_13_30_prefix s) (positive_select s 30) (lex_13_30_image s)

theorem lex_13_30_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5150), (Sat.Literal.pos 30), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation13 30 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5150) (Sat.Literal.pos 30) (Sat.Literal.pos 15) (lex_13_30_prefix s) (positive_select s 30) (lex_13_30_image s)

theorem lex_13_30_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5151), (Sat.Literal.pos 5150)] :=
  (lex_13_30_gate s).prop _ (List.Mem.head _)

theorem lex_13_30_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5151), (Sat.Literal.neg 30), (Sat.Literal.pos 15)] :=
  (lex_13_30_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_30_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5151), (Sat.Literal.pos 30), (Sat.Literal.neg 15)] :=
  (lex_13_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_30_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5150), (Sat.Literal.neg 30), (Sat.Literal.neg 15), (Sat.Literal.pos 5151)] :=
  (lex_13_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_30_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5150), (Sat.Literal.pos 30), (Sat.Literal.pos 15), (Sat.Literal.pos 5151)] :=
  (lex_13_30_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_29_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5151) = lexBefore s permutation13 29 := by
  exact (positive_lex_of_descriptor s 5151 permutation13 30 (by rfl)).trans ((lex_skipped s permutation13 29 30 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 30 30 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_29_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation13 29) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation13 29 by rw [image13_eq]; rfl))

theorem lex_13_29_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5152) (Sat.Literal.pos 5151) (Sat.Literal.pos 29) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation13 29 (assignment s)
    (Sat.Literal.pos 5152) (Sat.Literal.pos 5151) (Sat.Literal.pos 29) (Sat.Literal.pos 142) (positive_of_descriptor s 5152 (.lex permutation13 29) (by rfl)) (lex_13_29_prefix s) (positive_select s 29) (lex_13_29_image s)

theorem lex_13_29_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5151), (Sat.Literal.pos 29), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation13 29 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5151) (Sat.Literal.pos 29) (Sat.Literal.pos 142) (lex_13_29_prefix s) (positive_select s 29) (lex_13_29_image s)

theorem lex_13_29_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5152), (Sat.Literal.pos 5151)] :=
  (lex_13_29_gate s).prop _ (List.Mem.head _)

theorem lex_13_29_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5152), (Sat.Literal.neg 29), (Sat.Literal.pos 142)] :=
  (lex_13_29_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_29_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5152), (Sat.Literal.pos 29), (Sat.Literal.neg 142)] :=
  (lex_13_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_29_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5151), (Sat.Literal.neg 29), (Sat.Literal.neg 142), (Sat.Literal.pos 5152)] :=
  (lex_13_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_29_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5151), (Sat.Literal.pos 29), (Sat.Literal.pos 142), (Sat.Literal.pos 5152)] :=
  (lex_13_29_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_28_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5152) = lexBefore s permutation13 28 := by
  exact (positive_lex_of_descriptor s 5152 permutation13 29 (by rfl)).trans ((lex_skipped s permutation13 28 29 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 29 29 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_28_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation13 28) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation13 28 by rw [image13_eq]; rfl))

theorem lex_13_28_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5153) (Sat.Literal.pos 5152) (Sat.Literal.pos 28) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation13 28 (assignment s)
    (Sat.Literal.pos 5153) (Sat.Literal.pos 5152) (Sat.Literal.pos 28) (Sat.Literal.pos 14) (positive_of_descriptor s 5153 (.lex permutation13 28) (by rfl)) (lex_13_28_prefix s) (positive_select s 28) (lex_13_28_image s)

theorem lex_13_28_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5152), (Sat.Literal.pos 28), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation13 28 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5152) (Sat.Literal.pos 28) (Sat.Literal.pos 14) (lex_13_28_prefix s) (positive_select s 28) (lex_13_28_image s)

theorem lex_13_28_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5153), (Sat.Literal.pos 5152)] :=
  (lex_13_28_gate s).prop _ (List.Mem.head _)

theorem lex_13_28_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5153), (Sat.Literal.neg 28), (Sat.Literal.pos 14)] :=
  (lex_13_28_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_28_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5153), (Sat.Literal.pos 28), (Sat.Literal.neg 14)] :=
  (lex_13_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_28_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5152), (Sat.Literal.neg 28), (Sat.Literal.neg 14), (Sat.Literal.pos 5153)] :=
  (lex_13_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_28_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5152), (Sat.Literal.pos 28), (Sat.Literal.pos 14), (Sat.Literal.pos 5153)] :=
  (lex_13_28_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_27_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5153) = lexBefore s permutation13 27 := by
  exact (positive_lex_of_descriptor s 5153 permutation13 28 (by rfl)).trans ((lex_skipped s permutation13 27 28 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 28 28 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_27_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation13 27) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation13 27 by rw [image13_eq]; rfl))

theorem lex_13_27_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5154) (Sat.Literal.pos 5153) (Sat.Literal.pos 27) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation13 27 (assignment s)
    (Sat.Literal.pos 5154) (Sat.Literal.pos 5153) (Sat.Literal.pos 27) (Sat.Literal.pos 141) (positive_of_descriptor s 5154 (.lex permutation13 27) (by rfl)) (lex_13_27_prefix s) (positive_select s 27) (lex_13_27_image s)

theorem lex_13_27_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5153), (Sat.Literal.pos 27), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation13 27 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5153) (Sat.Literal.pos 27) (Sat.Literal.pos 141) (lex_13_27_prefix s) (positive_select s 27) (lex_13_27_image s)

theorem lex_13_27_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5154), (Sat.Literal.pos 5153)] :=
  (lex_13_27_gate s).prop _ (List.Mem.head _)

theorem lex_13_27_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5154), (Sat.Literal.neg 27), (Sat.Literal.pos 141)] :=
  (lex_13_27_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_27_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5154), (Sat.Literal.pos 27), (Sat.Literal.neg 141)] :=
  (lex_13_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_27_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5153), (Sat.Literal.neg 27), (Sat.Literal.neg 141), (Sat.Literal.pos 5154)] :=
  (lex_13_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_27_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5153), (Sat.Literal.pos 27), (Sat.Literal.pos 141), (Sat.Literal.pos 5154)] :=
  (lex_13_27_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_26_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5154) = lexBefore s permutation13 26 := by
  exact (positive_lex_of_descriptor s 5154 permutation13 27 (by rfl)).trans ((lex_skipped s permutation13 26 27 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 27 27 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_26_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation13 26) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation13 26 by rw [image13_eq]; rfl))

theorem lex_13_26_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5155) (Sat.Literal.pos 5154) (Sat.Literal.pos 26) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation13 26 (assignment s)
    (Sat.Literal.pos 5155) (Sat.Literal.pos 5154) (Sat.Literal.pos 26) (Sat.Literal.pos 13) (positive_of_descriptor s 5155 (.lex permutation13 26) (by rfl)) (lex_13_26_prefix s) (positive_select s 26) (lex_13_26_image s)

theorem lex_13_26_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5154), (Sat.Literal.pos 26), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation13 26 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5154) (Sat.Literal.pos 26) (Sat.Literal.pos 13) (lex_13_26_prefix s) (positive_select s 26) (lex_13_26_image s)

theorem lex_13_26_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5155), (Sat.Literal.pos 5154)] :=
  (lex_13_26_gate s).prop _ (List.Mem.head _)

theorem lex_13_26_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5155), (Sat.Literal.neg 26), (Sat.Literal.pos 13)] :=
  (lex_13_26_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_26_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5155), (Sat.Literal.pos 26), (Sat.Literal.neg 13)] :=
  (lex_13_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_26_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5154), (Sat.Literal.neg 26), (Sat.Literal.neg 13), (Sat.Literal.pos 5155)] :=
  (lex_13_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_26_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5154), (Sat.Literal.pos 26), (Sat.Literal.pos 13), (Sat.Literal.pos 5155)] :=
  (lex_13_26_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_25_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5155) = lexBefore s permutation13 25 := by
  exact (positive_lex_of_descriptor s 5155 permutation13 26 (by rfl)).trans ((lex_skipped s permutation13 25 26 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 26 26 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_25_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation13 25) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation13 25 by rw [image13_eq]; rfl))

theorem lex_13_25_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5156) (Sat.Literal.pos 5155) (Sat.Literal.pos 25) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation13 25 (assignment s)
    (Sat.Literal.pos 5156) (Sat.Literal.pos 5155) (Sat.Literal.pos 25) (Sat.Literal.pos 140) (positive_of_descriptor s 5156 (.lex permutation13 25) (by rfl)) (lex_13_25_prefix s) (positive_select s 25) (lex_13_25_image s)

theorem lex_13_25_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5155), (Sat.Literal.pos 25), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation13 25 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5155) (Sat.Literal.pos 25) (Sat.Literal.pos 140) (lex_13_25_prefix s) (positive_select s 25) (lex_13_25_image s)

theorem lex_13_25_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5156), (Sat.Literal.pos 5155)] :=
  (lex_13_25_gate s).prop _ (List.Mem.head _)

theorem lex_13_25_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5156), (Sat.Literal.neg 25), (Sat.Literal.pos 140)] :=
  (lex_13_25_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_25_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5156), (Sat.Literal.pos 25), (Sat.Literal.neg 140)] :=
  (lex_13_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_25_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5155), (Sat.Literal.neg 25), (Sat.Literal.neg 140), (Sat.Literal.pos 5156)] :=
  (lex_13_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_25_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5155), (Sat.Literal.pos 25), (Sat.Literal.pos 140), (Sat.Literal.pos 5156)] :=
  (lex_13_25_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_24_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5156) = lexBefore s permutation13 24 := by
  exact (positive_lex_of_descriptor s 5156 permutation13 25 (by rfl)).trans ((lex_skipped s permutation13 24 25 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 25 25 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_24_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 12) = s (permuteMask permutation13 24) := by
  exact (positive_select s 12).trans (congrArg s (show (12 : Fin 256) = permuteMask permutation13 24 by rw [image13_eq]; rfl))

theorem lex_13_24_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5157) (Sat.Literal.pos 5156) (Sat.Literal.pos 24) (Sat.Literal.pos 12)) := by
  exact equality_gate s permutation13 24 (assignment s)
    (Sat.Literal.pos 5157) (Sat.Literal.pos 5156) (Sat.Literal.pos 24) (Sat.Literal.pos 12) (positive_of_descriptor s 5157 (.lex permutation13 24) (by rfl)) (lex_13_24_prefix s) (positive_select s 24) (lex_13_24_image s)

theorem lex_13_24_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5156), (Sat.Literal.pos 24), (Sat.Literal.neg 12)] := by
  exact comparison_gate s permutation13 24 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5156) (Sat.Literal.pos 24) (Sat.Literal.pos 12) (lex_13_24_prefix s) (positive_select s 24) (lex_13_24_image s)

theorem lex_13_24_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5157), (Sat.Literal.pos 5156)] :=
  (lex_13_24_gate s).prop _ (List.Mem.head _)

theorem lex_13_24_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5157), (Sat.Literal.neg 24), (Sat.Literal.pos 12)] :=
  (lex_13_24_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_24_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5157), (Sat.Literal.pos 24), (Sat.Literal.neg 12)] :=
  (lex_13_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_24_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5156), (Sat.Literal.neg 24), (Sat.Literal.neg 12), (Sat.Literal.pos 5157)] :=
  (lex_13_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_24_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5156), (Sat.Literal.pos 24), (Sat.Literal.pos 12), (Sat.Literal.pos 5157)] :=
  (lex_13_24_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_23_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5157) = lexBefore s permutation13 23 := by
  exact (positive_lex_of_descriptor s 5157 permutation13 24 (by rfl)).trans ((lex_skipped s permutation13 23 24 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 24 24 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_23_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation13 23) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation13 23 by rw [image13_eq]; rfl))

theorem lex_13_23_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5158) (Sat.Literal.pos 5157) (Sat.Literal.pos 23) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation13 23 (assignment s)
    (Sat.Literal.pos 5158) (Sat.Literal.pos 5157) (Sat.Literal.pos 23) (Sat.Literal.pos 139) (positive_of_descriptor s 5158 (.lex permutation13 23) (by rfl)) (lex_13_23_prefix s) (positive_select s 23) (lex_13_23_image s)

theorem lex_13_23_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5157), (Sat.Literal.pos 23), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation13 23 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5157) (Sat.Literal.pos 23) (Sat.Literal.pos 139) (lex_13_23_prefix s) (positive_select s 23) (lex_13_23_image s)

theorem lex_13_23_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5158), (Sat.Literal.pos 5157)] :=
  (lex_13_23_gate s).prop _ (List.Mem.head _)

theorem lex_13_23_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5158), (Sat.Literal.neg 23), (Sat.Literal.pos 139)] :=
  (lex_13_23_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_23_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5158), (Sat.Literal.pos 23), (Sat.Literal.neg 139)] :=
  (lex_13_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_23_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5157), (Sat.Literal.neg 23), (Sat.Literal.neg 139), (Sat.Literal.pos 5158)] :=
  (lex_13_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_23_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5157), (Sat.Literal.pos 23), (Sat.Literal.pos 139), (Sat.Literal.pos 5158)] :=
  (lex_13_23_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_22_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5158) = lexBefore s permutation13 22 := by
  exact (positive_lex_of_descriptor s 5158 permutation13 23 (by rfl)).trans ((lex_skipped s permutation13 22 23 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 23 23 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_22_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 11) = s (permuteMask permutation13 22) := by
  exact (positive_select s 11).trans (congrArg s (show (11 : Fin 256) = permuteMask permutation13 22 by rw [image13_eq]; rfl))

theorem lex_13_22_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5159) (Sat.Literal.pos 5158) (Sat.Literal.pos 22) (Sat.Literal.pos 11)) := by
  exact equality_gate s permutation13 22 (assignment s)
    (Sat.Literal.pos 5159) (Sat.Literal.pos 5158) (Sat.Literal.pos 22) (Sat.Literal.pos 11) (positive_of_descriptor s 5159 (.lex permutation13 22) (by rfl)) (lex_13_22_prefix s) (positive_select s 22) (lex_13_22_image s)

theorem lex_13_22_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5158), (Sat.Literal.pos 22), (Sat.Literal.neg 11)] := by
  exact comparison_gate s permutation13 22 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5158) (Sat.Literal.pos 22) (Sat.Literal.pos 11) (lex_13_22_prefix s) (positive_select s 22) (lex_13_22_image s)

theorem lex_13_22_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5159), (Sat.Literal.pos 5158)] :=
  (lex_13_22_gate s).prop _ (List.Mem.head _)

theorem lex_13_22_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5159), (Sat.Literal.neg 22), (Sat.Literal.pos 11)] :=
  (lex_13_22_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_22_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5159), (Sat.Literal.pos 22), (Sat.Literal.neg 11)] :=
  (lex_13_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_22_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5158), (Sat.Literal.neg 22), (Sat.Literal.neg 11), (Sat.Literal.pos 5159)] :=
  (lex_13_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_22_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5158), (Sat.Literal.pos 22), (Sat.Literal.pos 11), (Sat.Literal.pos 5159)] :=
  (lex_13_22_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_21_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5159) = lexBefore s permutation13 21 := by
  exact (positive_lex_of_descriptor s 5159 permutation13 22 (by rfl)).trans ((lex_skipped s permutation13 21 22 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 22 22 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_21_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation13 21) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation13 21 by rw [image13_eq]; rfl))

theorem lex_13_21_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5160) (Sat.Literal.pos 5159) (Sat.Literal.pos 21) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation13 21 (assignment s)
    (Sat.Literal.pos 5160) (Sat.Literal.pos 5159) (Sat.Literal.pos 21) (Sat.Literal.pos 138) (positive_of_descriptor s 5160 (.lex permutation13 21) (by rfl)) (lex_13_21_prefix s) (positive_select s 21) (lex_13_21_image s)

theorem lex_13_21_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5159), (Sat.Literal.pos 21), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation13 21 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5159) (Sat.Literal.pos 21) (Sat.Literal.pos 138) (lex_13_21_prefix s) (positive_select s 21) (lex_13_21_image s)

theorem lex_13_21_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5160), (Sat.Literal.pos 5159)] :=
  (lex_13_21_gate s).prop _ (List.Mem.head _)

theorem lex_13_21_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5160), (Sat.Literal.neg 21), (Sat.Literal.pos 138)] :=
  (lex_13_21_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_21_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5160), (Sat.Literal.pos 21), (Sat.Literal.neg 138)] :=
  (lex_13_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_21_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5159), (Sat.Literal.neg 21), (Sat.Literal.neg 138), (Sat.Literal.pos 5160)] :=
  (lex_13_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_21_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5159), (Sat.Literal.pos 21), (Sat.Literal.pos 138), (Sat.Literal.pos 5160)] :=
  (lex_13_21_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_20_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5160) = lexBefore s permutation13 20 := by
  exact (positive_lex_of_descriptor s 5160 permutation13 21 (by rfl)).trans ((lex_skipped s permutation13 20 21 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 21 21 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_20_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 10) = s (permuteMask permutation13 20) := by
  exact (positive_select s 10).trans (congrArg s (show (10 : Fin 256) = permuteMask permutation13 20 by rw [image13_eq]; rfl))

theorem lex_13_20_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5161) (Sat.Literal.pos 5160) (Sat.Literal.pos 20) (Sat.Literal.pos 10)) := by
  exact equality_gate s permutation13 20 (assignment s)
    (Sat.Literal.pos 5161) (Sat.Literal.pos 5160) (Sat.Literal.pos 20) (Sat.Literal.pos 10) (positive_of_descriptor s 5161 (.lex permutation13 20) (by rfl)) (lex_13_20_prefix s) (positive_select s 20) (lex_13_20_image s)

theorem lex_13_20_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5160), (Sat.Literal.pos 20), (Sat.Literal.neg 10)] := by
  exact comparison_gate s permutation13 20 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5160) (Sat.Literal.pos 20) (Sat.Literal.pos 10) (lex_13_20_prefix s) (positive_select s 20) (lex_13_20_image s)

theorem lex_13_20_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5161), (Sat.Literal.pos 5160)] :=
  (lex_13_20_gate s).prop _ (List.Mem.head _)

theorem lex_13_20_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5161), (Sat.Literal.neg 20), (Sat.Literal.pos 10)] :=
  (lex_13_20_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_20_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5161), (Sat.Literal.pos 20), (Sat.Literal.neg 10)] :=
  (lex_13_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_20_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5160), (Sat.Literal.neg 20), (Sat.Literal.neg 10), (Sat.Literal.pos 5161)] :=
  (lex_13_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_20_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5160), (Sat.Literal.pos 20), (Sat.Literal.pos 10), (Sat.Literal.pos 5161)] :=
  (lex_13_20_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_19_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5161) = lexBefore s permutation13 19 := by
  exact (positive_lex_of_descriptor s 5161 permutation13 20 (by rfl)).trans ((lex_skipped s permutation13 19 20 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 20 20 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_19_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation13 19) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation13 19 by rw [image13_eq]; rfl))

theorem lex_13_19_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5162) (Sat.Literal.pos 5161) (Sat.Literal.pos 19) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation13 19 (assignment s)
    (Sat.Literal.pos 5162) (Sat.Literal.pos 5161) (Sat.Literal.pos 19) (Sat.Literal.pos 137) (positive_of_descriptor s 5162 (.lex permutation13 19) (by rfl)) (lex_13_19_prefix s) (positive_select s 19) (lex_13_19_image s)

theorem lex_13_19_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5161), (Sat.Literal.pos 19), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation13 19 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5161) (Sat.Literal.pos 19) (Sat.Literal.pos 137) (lex_13_19_prefix s) (positive_select s 19) (lex_13_19_image s)

theorem lex_13_19_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5162), (Sat.Literal.pos 5161)] :=
  (lex_13_19_gate s).prop _ (List.Mem.head _)

theorem lex_13_19_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5162), (Sat.Literal.neg 19), (Sat.Literal.pos 137)] :=
  (lex_13_19_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_19_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5162), (Sat.Literal.pos 19), (Sat.Literal.neg 137)] :=
  (lex_13_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_19_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5161), (Sat.Literal.neg 19), (Sat.Literal.neg 137), (Sat.Literal.pos 5162)] :=
  (lex_13_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_19_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5161), (Sat.Literal.pos 19), (Sat.Literal.pos 137), (Sat.Literal.pos 5162)] :=
  (lex_13_19_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_18_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5162) = lexBefore s permutation13 18 := by
  exact (positive_lex_of_descriptor s 5162 permutation13 19 (by rfl)).trans ((lex_skipped s permutation13 18 19 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 19 19 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_18_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 9) = s (permuteMask permutation13 18) := by
  exact (positive_select s 9).trans (congrArg s (show (9 : Fin 256) = permuteMask permutation13 18 by rw [image13_eq]; rfl))

theorem lex_13_18_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5163) (Sat.Literal.pos 5162) (Sat.Literal.pos 18) (Sat.Literal.pos 9)) := by
  exact equality_gate s permutation13 18 (assignment s)
    (Sat.Literal.pos 5163) (Sat.Literal.pos 5162) (Sat.Literal.pos 18) (Sat.Literal.pos 9) (positive_of_descriptor s 5163 (.lex permutation13 18) (by rfl)) (lex_13_18_prefix s) (positive_select s 18) (lex_13_18_image s)

theorem lex_13_18_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5162), (Sat.Literal.pos 18), (Sat.Literal.neg 9)] := by
  exact comparison_gate s permutation13 18 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5162) (Sat.Literal.pos 18) (Sat.Literal.pos 9) (lex_13_18_prefix s) (positive_select s 18) (lex_13_18_image s)

theorem lex_13_18_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5163), (Sat.Literal.pos 5162)] :=
  (lex_13_18_gate s).prop _ (List.Mem.head _)

theorem lex_13_18_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5163), (Sat.Literal.neg 18), (Sat.Literal.pos 9)] :=
  (lex_13_18_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_18_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5163), (Sat.Literal.pos 18), (Sat.Literal.neg 9)] :=
  (lex_13_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_18_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5162), (Sat.Literal.neg 18), (Sat.Literal.neg 9), (Sat.Literal.pos 5163)] :=
  (lex_13_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_18_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5162), (Sat.Literal.pos 18), (Sat.Literal.pos 9), (Sat.Literal.pos 5163)] :=
  (lex_13_18_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_17_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5163) = lexBefore s permutation13 17 := by
  exact (positive_lex_of_descriptor s 5163 permutation13 18 (by rfl)).trans ((lex_skipped s permutation13 17 18 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 18 18 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_17_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation13 17) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation13 17 by rw [image13_eq]; rfl))

theorem lex_13_17_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5164) (Sat.Literal.pos 5163) (Sat.Literal.pos 17) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation13 17 (assignment s)
    (Sat.Literal.pos 5164) (Sat.Literal.pos 5163) (Sat.Literal.pos 17) (Sat.Literal.pos 136) (positive_of_descriptor s 5164 (.lex permutation13 17) (by rfl)) (lex_13_17_prefix s) (positive_select s 17) (lex_13_17_image s)

theorem lex_13_17_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5163), (Sat.Literal.pos 17), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation13 17 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5163) (Sat.Literal.pos 17) (Sat.Literal.pos 136) (lex_13_17_prefix s) (positive_select s 17) (lex_13_17_image s)

theorem lex_13_17_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5164), (Sat.Literal.pos 5163)] :=
  (lex_13_17_gate s).prop _ (List.Mem.head _)

theorem lex_13_17_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5164), (Sat.Literal.neg 17), (Sat.Literal.pos 136)] :=
  (lex_13_17_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_17_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5164), (Sat.Literal.pos 17), (Sat.Literal.neg 136)] :=
  (lex_13_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_17_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5163), (Sat.Literal.neg 17), (Sat.Literal.neg 136), (Sat.Literal.pos 5164)] :=
  (lex_13_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_17_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5163), (Sat.Literal.pos 17), (Sat.Literal.pos 136), (Sat.Literal.pos 5164)] :=
  (lex_13_17_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_16_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5164) = lexBefore s permutation13 16 := by
  exact (positive_lex_of_descriptor s 5164 permutation13 17 (by rfl)).trans ((lex_skipped s permutation13 16 17 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 17 17 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_16_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation13 16) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation13 16 by rw [image13_eq]; rfl))

theorem lex_13_16_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5165) (Sat.Literal.pos 5164) (Sat.Literal.pos 16) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation13 16 (assignment s)
    (Sat.Literal.pos 5165) (Sat.Literal.pos 5164) (Sat.Literal.pos 16) (Sat.Literal.pos 8) (positive_of_descriptor s 5165 (.lex permutation13 16) (by rfl)) (lex_13_16_prefix s) (positive_select s 16) (lex_13_16_image s)

theorem lex_13_16_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5164), (Sat.Literal.pos 16), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation13 16 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5164) (Sat.Literal.pos 16) (Sat.Literal.pos 8) (lex_13_16_prefix s) (positive_select s 16) (lex_13_16_image s)

theorem lex_13_16_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5165), (Sat.Literal.pos 5164)] :=
  (lex_13_16_gate s).prop _ (List.Mem.head _)

theorem lex_13_16_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5165), (Sat.Literal.neg 16), (Sat.Literal.pos 8)] :=
  (lex_13_16_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_16_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5165), (Sat.Literal.pos 16), (Sat.Literal.neg 8)] :=
  (lex_13_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_16_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5164), (Sat.Literal.neg 16), (Sat.Literal.neg 8), (Sat.Literal.pos 5165)] :=
  (lex_13_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_16_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5164), (Sat.Literal.pos 16), (Sat.Literal.pos 8), (Sat.Literal.pos 5165)] :=
  (lex_13_16_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_15_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5165) = lexBefore s permutation13 15 := by
  exact (positive_lex_of_descriptor s 5165 permutation13 16 (by rfl)).trans ((lex_skipped s permutation13 15 16 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 16 16 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_15_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation13 15) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation13 15 by rw [image13_eq]; rfl))

theorem lex_13_15_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5166) (Sat.Literal.pos 5165) (Sat.Literal.pos 15) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation13 15 (assignment s)
    (Sat.Literal.pos 5166) (Sat.Literal.pos 5165) (Sat.Literal.pos 15) (Sat.Literal.pos 135) (positive_of_descriptor s 5166 (.lex permutation13 15) (by rfl)) (lex_13_15_prefix s) (positive_select s 15) (lex_13_15_image s)

theorem lex_13_15_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5165), (Sat.Literal.pos 15), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation13 15 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5165) (Sat.Literal.pos 15) (Sat.Literal.pos 135) (lex_13_15_prefix s) (positive_select s 15) (lex_13_15_image s)

theorem lex_13_15_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5166), (Sat.Literal.pos 5165)] :=
  (lex_13_15_gate s).prop _ (List.Mem.head _)

theorem lex_13_15_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5166), (Sat.Literal.neg 15), (Sat.Literal.pos 135)] :=
  (lex_13_15_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_15_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5166), (Sat.Literal.pos 15), (Sat.Literal.neg 135)] :=
  (lex_13_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_15_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5165), (Sat.Literal.neg 15), (Sat.Literal.neg 135), (Sat.Literal.pos 5166)] :=
  (lex_13_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_15_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5165), (Sat.Literal.pos 15), (Sat.Literal.pos 135), (Sat.Literal.pos 5166)] :=
  (lex_13_15_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_14_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5166) = lexBefore s permutation13 14 := by
  exact (positive_lex_of_descriptor s 5166 permutation13 15 (by rfl)).trans ((lex_skipped s permutation13 14 15 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 15 15 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_14_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation13 14) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation13 14 by rw [image13_eq]; rfl))

theorem lex_13_14_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5167) (Sat.Literal.pos 5166) (Sat.Literal.pos 14) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation13 14 (assignment s)
    (Sat.Literal.pos 5167) (Sat.Literal.pos 5166) (Sat.Literal.pos 14) (Sat.Literal.pos 7) (positive_of_descriptor s 5167 (.lex permutation13 14) (by rfl)) (lex_13_14_prefix s) (positive_select s 14) (lex_13_14_image s)

theorem lex_13_14_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5166), (Sat.Literal.pos 14), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation13 14 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5166) (Sat.Literal.pos 14) (Sat.Literal.pos 7) (lex_13_14_prefix s) (positive_select s 14) (lex_13_14_image s)

theorem lex_13_14_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5167), (Sat.Literal.pos 5166)] :=
  (lex_13_14_gate s).prop _ (List.Mem.head _)

theorem lex_13_14_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5167), (Sat.Literal.neg 14), (Sat.Literal.pos 7)] :=
  (lex_13_14_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_14_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5167), (Sat.Literal.pos 14), (Sat.Literal.neg 7)] :=
  (lex_13_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_14_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5166), (Sat.Literal.neg 14), (Sat.Literal.neg 7), (Sat.Literal.pos 5167)] :=
  (lex_13_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_14_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5166), (Sat.Literal.pos 14), (Sat.Literal.pos 7), (Sat.Literal.pos 5167)] :=
  (lex_13_14_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_13_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5167) = lexBefore s permutation13 13 := by
  exact (positive_lex_of_descriptor s 5167 permutation13 14 (by rfl)).trans ((lex_skipped s permutation13 13 14 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 14 14 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_13_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation13 13) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation13 13 by rw [image13_eq]; rfl))

theorem lex_13_13_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5168) (Sat.Literal.pos 5167) (Sat.Literal.pos 13) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation13 13 (assignment s)
    (Sat.Literal.pos 5168) (Sat.Literal.pos 5167) (Sat.Literal.pos 13) (Sat.Literal.pos 134) (positive_of_descriptor s 5168 (.lex permutation13 13) (by rfl)) (lex_13_13_prefix s) (positive_select s 13) (lex_13_13_image s)

theorem lex_13_13_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5167), (Sat.Literal.pos 13), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation13 13 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5167) (Sat.Literal.pos 13) (Sat.Literal.pos 134) (lex_13_13_prefix s) (positive_select s 13) (lex_13_13_image s)

theorem lex_13_13_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5168), (Sat.Literal.pos 5167)] :=
  (lex_13_13_gate s).prop _ (List.Mem.head _)

theorem lex_13_13_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5168), (Sat.Literal.neg 13), (Sat.Literal.pos 134)] :=
  (lex_13_13_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_13_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5168), (Sat.Literal.pos 13), (Sat.Literal.neg 134)] :=
  (lex_13_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_13_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5167), (Sat.Literal.neg 13), (Sat.Literal.neg 134), (Sat.Literal.pos 5168)] :=
  (lex_13_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_13_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5167), (Sat.Literal.pos 13), (Sat.Literal.pos 134), (Sat.Literal.pos 5168)] :=
  (lex_13_13_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_12_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5168) = lexBefore s permutation13 12 := by
  exact (positive_lex_of_descriptor s 5168 permutation13 13 (by rfl)).trans ((lex_skipped s permutation13 12 13 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 13 13 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_12_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation13 12) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation13 12 by rw [image13_eq]; rfl))

theorem lex_13_12_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5169) (Sat.Literal.pos 5168) (Sat.Literal.pos 12) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation13 12 (assignment s)
    (Sat.Literal.pos 5169) (Sat.Literal.pos 5168) (Sat.Literal.pos 12) (Sat.Literal.pos 6) (positive_of_descriptor s 5169 (.lex permutation13 12) (by rfl)) (lex_13_12_prefix s) (positive_select s 12) (lex_13_12_image s)

theorem lex_13_12_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5168), (Sat.Literal.pos 12), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation13 12 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5168) (Sat.Literal.pos 12) (Sat.Literal.pos 6) (lex_13_12_prefix s) (positive_select s 12) (lex_13_12_image s)

theorem lex_13_12_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5169), (Sat.Literal.pos 5168)] :=
  (lex_13_12_gate s).prop _ (List.Mem.head _)

theorem lex_13_12_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5169), (Sat.Literal.neg 12), (Sat.Literal.pos 6)] :=
  (lex_13_12_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_12_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5169), (Sat.Literal.pos 12), (Sat.Literal.neg 6)] :=
  (lex_13_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_12_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5168), (Sat.Literal.neg 12), (Sat.Literal.neg 6), (Sat.Literal.pos 5169)] :=
  (lex_13_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_12_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5168), (Sat.Literal.pos 12), (Sat.Literal.pos 6), (Sat.Literal.pos 5169)] :=
  (lex_13_12_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_11_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5169) = lexBefore s permutation13 11 := by
  exact (positive_lex_of_descriptor s 5169 permutation13 12 (by rfl)).trans ((lex_skipped s permutation13 11 12 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 12 12 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_11_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation13 11) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation13 11 by rw [image13_eq]; rfl))

theorem lex_13_11_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5170) (Sat.Literal.pos 5169) (Sat.Literal.pos 11) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation13 11 (assignment s)
    (Sat.Literal.pos 5170) (Sat.Literal.pos 5169) (Sat.Literal.pos 11) (Sat.Literal.pos 133) (positive_of_descriptor s 5170 (.lex permutation13 11) (by rfl)) (lex_13_11_prefix s) (positive_select s 11) (lex_13_11_image s)

theorem lex_13_11_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5169), (Sat.Literal.pos 11), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation13 11 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5169) (Sat.Literal.pos 11) (Sat.Literal.pos 133) (lex_13_11_prefix s) (positive_select s 11) (lex_13_11_image s)

theorem lex_13_11_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5170), (Sat.Literal.pos 5169)] :=
  (lex_13_11_gate s).prop _ (List.Mem.head _)

theorem lex_13_11_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5170), (Sat.Literal.neg 11), (Sat.Literal.pos 133)] :=
  (lex_13_11_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_11_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5170), (Sat.Literal.pos 11), (Sat.Literal.neg 133)] :=
  (lex_13_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_11_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5169), (Sat.Literal.neg 11), (Sat.Literal.neg 133), (Sat.Literal.pos 5170)] :=
  (lex_13_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_11_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5169), (Sat.Literal.pos 11), (Sat.Literal.pos 133), (Sat.Literal.pos 5170)] :=
  (lex_13_11_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_10_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5170) = lexBefore s permutation13 10 := by
  exact (positive_lex_of_descriptor s 5170 permutation13 11 (by rfl)).trans ((lex_skipped s permutation13 10 11 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 11 11 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_10_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation13 10) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation13 10 by rw [image13_eq]; rfl))

theorem lex_13_10_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5171) (Sat.Literal.pos 5170) (Sat.Literal.pos 10) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation13 10 (assignment s)
    (Sat.Literal.pos 5171) (Sat.Literal.pos 5170) (Sat.Literal.pos 10) (Sat.Literal.pos 5) (positive_of_descriptor s 5171 (.lex permutation13 10) (by rfl)) (lex_13_10_prefix s) (positive_select s 10) (lex_13_10_image s)

theorem lex_13_10_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5170), (Sat.Literal.pos 10), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation13 10 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5170) (Sat.Literal.pos 10) (Sat.Literal.pos 5) (lex_13_10_prefix s) (positive_select s 10) (lex_13_10_image s)

theorem lex_13_10_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5171), (Sat.Literal.pos 5170)] :=
  (lex_13_10_gate s).prop _ (List.Mem.head _)

theorem lex_13_10_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5171), (Sat.Literal.neg 10), (Sat.Literal.pos 5)] :=
  (lex_13_10_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_10_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5171), (Sat.Literal.pos 10), (Sat.Literal.neg 5)] :=
  (lex_13_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_10_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5170), (Sat.Literal.neg 10), (Sat.Literal.neg 5), (Sat.Literal.pos 5171)] :=
  (lex_13_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_10_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5170), (Sat.Literal.pos 10), (Sat.Literal.pos 5), (Sat.Literal.pos 5171)] :=
  (lex_13_10_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_9_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5171) = lexBefore s permutation13 9 := by
  exact (positive_lex_of_descriptor s 5171 permutation13 10 (by rfl)).trans ((lex_skipped s permutation13 9 10 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 10 10 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_9_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation13 9) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation13 9 by rw [image13_eq]; rfl))

theorem lex_13_9_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5172) (Sat.Literal.pos 5171) (Sat.Literal.pos 9) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation13 9 (assignment s)
    (Sat.Literal.pos 5172) (Sat.Literal.pos 5171) (Sat.Literal.pos 9) (Sat.Literal.pos 132) (positive_of_descriptor s 5172 (.lex permutation13 9) (by rfl)) (lex_13_9_prefix s) (positive_select s 9) (lex_13_9_image s)

theorem lex_13_9_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5171), (Sat.Literal.pos 9), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation13 9 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5171) (Sat.Literal.pos 9) (Sat.Literal.pos 132) (lex_13_9_prefix s) (positive_select s 9) (lex_13_9_image s)

theorem lex_13_9_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5172), (Sat.Literal.pos 5171)] :=
  (lex_13_9_gate s).prop _ (List.Mem.head _)

theorem lex_13_9_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5172), (Sat.Literal.neg 9), (Sat.Literal.pos 132)] :=
  (lex_13_9_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_9_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5172), (Sat.Literal.pos 9), (Sat.Literal.neg 132)] :=
  (lex_13_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_9_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5171), (Sat.Literal.neg 9), (Sat.Literal.neg 132), (Sat.Literal.pos 5172)] :=
  (lex_13_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_9_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5171), (Sat.Literal.pos 9), (Sat.Literal.pos 132), (Sat.Literal.pos 5172)] :=
  (lex_13_9_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_8_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5172) = lexBefore s permutation13 8 := by
  exact (positive_lex_of_descriptor s 5172 permutation13 9 (by rfl)).trans ((lex_skipped s permutation13 8 9 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 9 9 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_8_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation13 8) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation13 8 by rw [image13_eq]; rfl))

theorem lex_13_8_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5173) (Sat.Literal.pos 5172) (Sat.Literal.pos 8) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation13 8 (assignment s)
    (Sat.Literal.pos 5173) (Sat.Literal.pos 5172) (Sat.Literal.pos 8) (Sat.Literal.pos 4) (positive_of_descriptor s 5173 (.lex permutation13 8) (by rfl)) (lex_13_8_prefix s) (positive_select s 8) (lex_13_8_image s)

theorem lex_13_8_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5172), (Sat.Literal.pos 8), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation13 8 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5172) (Sat.Literal.pos 8) (Sat.Literal.pos 4) (lex_13_8_prefix s) (positive_select s 8) (lex_13_8_image s)

theorem lex_13_8_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5173), (Sat.Literal.pos 5172)] :=
  (lex_13_8_gate s).prop _ (List.Mem.head _)

theorem lex_13_8_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5173), (Sat.Literal.neg 8), (Sat.Literal.pos 4)] :=
  (lex_13_8_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_8_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5173), (Sat.Literal.pos 8), (Sat.Literal.neg 4)] :=
  (lex_13_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_8_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5172), (Sat.Literal.neg 8), (Sat.Literal.neg 4), (Sat.Literal.pos 5173)] :=
  (lex_13_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_8_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5172), (Sat.Literal.pos 8), (Sat.Literal.pos 4), (Sat.Literal.pos 5173)] :=
  (lex_13_8_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_7_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5173) = lexBefore s permutation13 7 := by
  exact (positive_lex_of_descriptor s 5173 permutation13 8 (by rfl)).trans ((lex_skipped s permutation13 7 8 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 8 8 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_7_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation13 7) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation13 7 by rw [image13_eq]; rfl))

theorem lex_13_7_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5174) (Sat.Literal.pos 5173) (Sat.Literal.pos 7) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation13 7 (assignment s)
    (Sat.Literal.pos 5174) (Sat.Literal.pos 5173) (Sat.Literal.pos 7) (Sat.Literal.pos 131) (positive_of_descriptor s 5174 (.lex permutation13 7) (by rfl)) (lex_13_7_prefix s) (positive_select s 7) (lex_13_7_image s)

theorem lex_13_7_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5173), (Sat.Literal.pos 7), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation13 7 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5173) (Sat.Literal.pos 7) (Sat.Literal.pos 131) (lex_13_7_prefix s) (positive_select s 7) (lex_13_7_image s)

theorem lex_13_7_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5174), (Sat.Literal.pos 5173)] :=
  (lex_13_7_gate s).prop _ (List.Mem.head _)

theorem lex_13_7_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5174), (Sat.Literal.neg 7), (Sat.Literal.pos 131)] :=
  (lex_13_7_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_7_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5174), (Sat.Literal.pos 7), (Sat.Literal.neg 131)] :=
  (lex_13_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_7_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5173), (Sat.Literal.neg 7), (Sat.Literal.neg 131), (Sat.Literal.pos 5174)] :=
  (lex_13_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_7_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5173), (Sat.Literal.pos 7), (Sat.Literal.pos 131), (Sat.Literal.pos 5174)] :=
  (lex_13_7_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_6_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5174) = lexBefore s permutation13 6 := by
  exact (positive_lex_of_descriptor s 5174 permutation13 7 (by rfl)).trans ((lex_skipped s permutation13 6 7 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 7 7 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_6_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3) = s (permuteMask permutation13 6) := by
  exact (positive_select s 3).trans (congrArg s (show (3 : Fin 256) = permuteMask permutation13 6 by rw [image13_eq]; rfl))

theorem lex_13_6_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5175) (Sat.Literal.pos 5174) (Sat.Literal.pos 6) (Sat.Literal.pos 3)) := by
  exact equality_gate s permutation13 6 (assignment s)
    (Sat.Literal.pos 5175) (Sat.Literal.pos 5174) (Sat.Literal.pos 6) (Sat.Literal.pos 3) (positive_of_descriptor s 5175 (.lex permutation13 6) (by rfl)) (lex_13_6_prefix s) (positive_select s 6) (lex_13_6_image s)

theorem lex_13_6_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5174), (Sat.Literal.pos 6), (Sat.Literal.neg 3)] := by
  exact comparison_gate s permutation13 6 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5174) (Sat.Literal.pos 6) (Sat.Literal.pos 3) (lex_13_6_prefix s) (positive_select s 6) (lex_13_6_image s)

theorem lex_13_6_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5175), (Sat.Literal.pos 5174)] :=
  (lex_13_6_gate s).prop _ (List.Mem.head _)

theorem lex_13_6_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5175), (Sat.Literal.neg 6), (Sat.Literal.pos 3)] :=
  (lex_13_6_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_6_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5175), (Sat.Literal.pos 6), (Sat.Literal.neg 3)] :=
  (lex_13_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_6_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5174), (Sat.Literal.neg 6), (Sat.Literal.neg 3), (Sat.Literal.pos 5175)] :=
  (lex_13_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_6_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5174), (Sat.Literal.pos 6), (Sat.Literal.pos 3), (Sat.Literal.pos 5175)] :=
  (lex_13_6_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_5_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5175) = lexBefore s permutation13 5 := by
  exact (positive_lex_of_descriptor s 5175 permutation13 6 (by rfl)).trans ((lex_skipped s permutation13 5 6 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 6 6 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_5_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation13 5) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation13 5 by rw [image13_eq]; rfl))

theorem lex_13_5_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5176) (Sat.Literal.pos 5175) (Sat.Literal.pos 5) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation13 5 (assignment s)
    (Sat.Literal.pos 5176) (Sat.Literal.pos 5175) (Sat.Literal.pos 5) (Sat.Literal.pos 130) (positive_of_descriptor s 5176 (.lex permutation13 5) (by rfl)) (lex_13_5_prefix s) (positive_select s 5) (lex_13_5_image s)

theorem lex_13_5_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5175), (Sat.Literal.pos 5), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation13 5 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5175) (Sat.Literal.pos 5) (Sat.Literal.pos 130) (lex_13_5_prefix s) (positive_select s 5) (lex_13_5_image s)

theorem lex_13_5_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5176), (Sat.Literal.pos 5175)] :=
  (lex_13_5_gate s).prop _ (List.Mem.head _)

theorem lex_13_5_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5176), (Sat.Literal.neg 5), (Sat.Literal.pos 130)] :=
  (lex_13_5_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_5_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5176), (Sat.Literal.pos 5), (Sat.Literal.neg 130)] :=
  (lex_13_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_5_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5175), (Sat.Literal.neg 5), (Sat.Literal.neg 130), (Sat.Literal.pos 5176)] :=
  (lex_13_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_5_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5175), (Sat.Literal.pos 5), (Sat.Literal.pos 130), (Sat.Literal.pos 5176)] :=
  (lex_13_5_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_4_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5176) = lexBefore s permutation13 4 := by
  exact (positive_lex_of_descriptor s 5176 permutation13 5 (by rfl)).trans ((lex_skipped s permutation13 4 5 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 5 5 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_4_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2) = s (permuteMask permutation13 4) := by
  exact (positive_select s 2).trans (congrArg s (show (2 : Fin 256) = permuteMask permutation13 4 by rw [image13_eq]; rfl))

theorem lex_13_4_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5177) (Sat.Literal.pos 5176) (Sat.Literal.pos 4) (Sat.Literal.pos 2)) := by
  exact equality_gate s permutation13 4 (assignment s)
    (Sat.Literal.pos 5177) (Sat.Literal.pos 5176) (Sat.Literal.pos 4) (Sat.Literal.pos 2) (positive_of_descriptor s 5177 (.lex permutation13 4) (by rfl)) (lex_13_4_prefix s) (positive_select s 4) (lex_13_4_image s)

theorem lex_13_4_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5176), (Sat.Literal.pos 4), (Sat.Literal.neg 2)] := by
  exact comparison_gate s permutation13 4 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5176) (Sat.Literal.pos 4) (Sat.Literal.pos 2) (lex_13_4_prefix s) (positive_select s 4) (lex_13_4_image s)

theorem lex_13_4_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5177), (Sat.Literal.pos 5176)] :=
  (lex_13_4_gate s).prop _ (List.Mem.head _)

theorem lex_13_4_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5177), (Sat.Literal.neg 4), (Sat.Literal.pos 2)] :=
  (lex_13_4_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_4_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5177), (Sat.Literal.pos 4), (Sat.Literal.neg 2)] :=
  (lex_13_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_4_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5176), (Sat.Literal.neg 4), (Sat.Literal.neg 2), (Sat.Literal.pos 5177)] :=
  (lex_13_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_4_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5176), (Sat.Literal.pos 4), (Sat.Literal.pos 2), (Sat.Literal.pos 5177)] :=
  (lex_13_4_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_3_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5177) = lexBefore s permutation13 3 := by
  exact (positive_lex_of_descriptor s 5177 permutation13 4 (by rfl)).trans ((lex_skipped s permutation13 3 4 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 4 4 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_3_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation13 3) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation13 3 by rw [image13_eq]; rfl))

theorem lex_13_3_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5178) (Sat.Literal.pos 5177) (Sat.Literal.pos 3) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation13 3 (assignment s)
    (Sat.Literal.pos 5178) (Sat.Literal.pos 5177) (Sat.Literal.pos 3) (Sat.Literal.pos 129) (positive_of_descriptor s 5178 (.lex permutation13 3) (by rfl)) (lex_13_3_prefix s) (positive_select s 3) (lex_13_3_image s)

theorem lex_13_3_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5177), (Sat.Literal.pos 3), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation13 3 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5177) (Sat.Literal.pos 3) (Sat.Literal.pos 129) (lex_13_3_prefix s) (positive_select s 3) (lex_13_3_image s)

theorem lex_13_3_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5178), (Sat.Literal.pos 5177)] :=
  (lex_13_3_gate s).prop _ (List.Mem.head _)

theorem lex_13_3_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5178), (Sat.Literal.neg 3), (Sat.Literal.pos 129)] :=
  (lex_13_3_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_3_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5178), (Sat.Literal.pos 3), (Sat.Literal.neg 129)] :=
  (lex_13_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_3_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5177), (Sat.Literal.neg 3), (Sat.Literal.neg 129), (Sat.Literal.pos 5178)] :=
  (lex_13_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_3_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5177), (Sat.Literal.pos 3), (Sat.Literal.pos 129), (Sat.Literal.pos 5178)] :=
  (lex_13_3_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5178) = lexBefore s permutation13 2 := by
  exact (positive_lex_of_descriptor s 5178 permutation13 3 (by rfl)).trans ((lex_skipped s permutation13 2 3 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 1) = s (permuteMask permutation13 2) := by
  exact (positive_select s 1).trans (congrArg s (show (1 : Fin 256) = permuteMask permutation13 2 by rw [image13_eq]; rfl))

theorem lex_13_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5179) (Sat.Literal.pos 5178) (Sat.Literal.pos 2) (Sat.Literal.pos 1)) := by
  exact equality_gate s permutation13 2 (assignment s)
    (Sat.Literal.pos 5179) (Sat.Literal.pos 5178) (Sat.Literal.pos 2) (Sat.Literal.pos 1) (positive_of_descriptor s 5179 (.lex permutation13 2) (by rfl)) (lex_13_2_prefix s) (positive_select s 2) (lex_13_2_image s)

theorem lex_13_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5178), (Sat.Literal.pos 2), (Sat.Literal.neg 1)] := by
  exact comparison_gate s permutation13 2 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5178) (Sat.Literal.pos 2) (Sat.Literal.pos 1) (lex_13_2_prefix s) (positive_select s 2) (lex_13_2_image s)

theorem lex_13_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5179), (Sat.Literal.pos 5178)] :=
  (lex_13_2_gate s).prop _ (List.Mem.head _)

theorem lex_13_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5179), (Sat.Literal.neg 2), (Sat.Literal.pos 1)] :=
  (lex_13_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5179), (Sat.Literal.pos 2), (Sat.Literal.neg 1)] :=
  (lex_13_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5178), (Sat.Literal.neg 2), (Sat.Literal.neg 1), (Sat.Literal.pos 5179)] :=
  (lex_13_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5178), (Sat.Literal.pos 2), (Sat.Literal.pos 1), (Sat.Literal.pos 5179)] :=
  (lex_13_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5179) = lexBefore s permutation13 1 := by
  exact (positive_lex_of_descriptor s 5179 permutation13 2 (by rfl)).trans ((lex_skipped s permutation13 1 2 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation13 1) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation13 1 by rw [image13_eq]; rfl))

theorem lex_13_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5180) (Sat.Literal.pos 5179) (Sat.Literal.pos 1) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation13 1 (assignment s)
    (Sat.Literal.pos 5180) (Sat.Literal.pos 5179) (Sat.Literal.pos 1) (Sat.Literal.pos 128) (positive_of_descriptor s 5180 (.lex permutation13 1) (by rfl)) (lex_13_1_prefix s) (positive_select s 1) (lex_13_1_image s)

theorem lex_13_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5179), (Sat.Literal.pos 1), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation13 1 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5179) (Sat.Literal.pos 1) (Sat.Literal.pos 128) (lex_13_1_prefix s) (positive_select s 1) (lex_13_1_image s)

theorem lex_13_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5180), (Sat.Literal.pos 5179)] :=
  (lex_13_1_gate s).prop _ (List.Mem.head _)

theorem lex_13_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5180), (Sat.Literal.neg 1), (Sat.Literal.pos 128)] :=
  (lex_13_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5180), (Sat.Literal.pos 1), (Sat.Literal.neg 128)] :=
  (lex_13_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5179), (Sat.Literal.neg 1), (Sat.Literal.neg 128), (Sat.Literal.pos 5180)] :=
  (lex_13_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5179), (Sat.Literal.pos 1), (Sat.Literal.pos 128), (Sat.Literal.pos 5180)] :=
  (lex_13_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_13_56_gate

end Crown.CertificateData
