import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_8_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3924) = lexBefore s permutation8 2 := by
  exact (positive_lex_of_descriptor s 3924 permutation8 3 (by rfl)).trans ((lex_skipped s permutation8 2 3 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 8) = s (permuteMask permutation8 2) := by
  exact (positive_select s 8).trans (congrArg s (show (8 : Fin 256) = permuteMask permutation8 2 by rw [image8_eq]; rfl))

theorem lex_8_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3925) (Sat.Literal.pos 3924) (Sat.Literal.pos 2) (Sat.Literal.pos 8)) := by
  exact equality_gate s permutation8 2 (assignment s)
    (Sat.Literal.pos 3925) (Sat.Literal.pos 3924) (Sat.Literal.pos 2) (Sat.Literal.pos 8) (positive_of_descriptor s 3925 (.lex permutation8 2) (by rfl)) (lex_8_2_prefix s) (positive_select s 2) (lex_8_2_image s)

theorem lex_8_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3924), (Sat.Literal.pos 2), (Sat.Literal.neg 8)] := by
  exact comparison_gate s permutation8 2 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3924) (Sat.Literal.pos 2) (Sat.Literal.pos 8) (lex_8_2_prefix s) (positive_select s 2) (lex_8_2_image s)

theorem lex_8_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3925), (Sat.Literal.pos 3924)] :=
  (lex_8_2_gate s).prop _ (List.Mem.head _)

theorem lex_8_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3925), (Sat.Literal.neg 2), (Sat.Literal.pos 8)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3925), (Sat.Literal.pos 2), (Sat.Literal.neg 8)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3924), (Sat.Literal.neg 2), (Sat.Literal.neg 8), (Sat.Literal.pos 3925)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3924), (Sat.Literal.pos 2), (Sat.Literal.pos 8), (Sat.Literal.pos 3925)] :=
  (lex_8_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_8_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3925) = lexBefore s permutation8 1 := by
  exact (positive_lex_of_descriptor s 3925 permutation8 2 (by rfl)).trans ((lex_skipped s permutation8 1 2 (by decide) (by intro j hj hp; rw [image8_eq]; exact fixedOnRange_spec image8 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_8_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4) = s (permuteMask permutation8 1) := by
  exact (positive_select s 4).trans (congrArg s (show (4 : Fin 256) = permuteMask permutation8 1 by rw [image8_eq]; rfl))

theorem lex_8_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3926) (Sat.Literal.pos 3925) (Sat.Literal.pos 1) (Sat.Literal.pos 4)) := by
  exact equality_gate s permutation8 1 (assignment s)
    (Sat.Literal.pos 3926) (Sat.Literal.pos 3925) (Sat.Literal.pos 1) (Sat.Literal.pos 4) (positive_of_descriptor s 3926 (.lex permutation8 1) (by rfl)) (lex_8_1_prefix s) (positive_select s 1) (lex_8_1_image s)

theorem lex_8_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3925), (Sat.Literal.pos 1), (Sat.Literal.neg 4)] := by
  exact comparison_gate s permutation8 1 (hmax permutation8) (assignment s)
    (Sat.Literal.pos 3925) (Sat.Literal.pos 1) (Sat.Literal.pos 4) (lex_8_1_prefix s) (positive_select s 1) (lex_8_1_image s)

theorem lex_8_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3926), (Sat.Literal.pos 3925)] :=
  (lex_8_1_gate s).prop _ (List.Mem.head _)

theorem lex_8_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3926), (Sat.Literal.neg 1), (Sat.Literal.pos 4)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_8_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3926), (Sat.Literal.pos 1), (Sat.Literal.neg 4)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_8_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3925), (Sat.Literal.neg 1), (Sat.Literal.neg 4), (Sat.Literal.pos 3926)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_8_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3925), (Sat.Literal.pos 1), (Sat.Literal.pos 4), (Sat.Literal.pos 3926)] :=
  (lex_8_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation9 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation9 254 (by intro j hj; rw [image9_eq]; exact fixedOnRange_spec image9 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_9_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation9 254) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation9 254 by rw [image9_eq]; rfl))

theorem lex_9_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3927) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation9 254 (assignment s)
    (Sat.Literal.pos 3927) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 247) (positive_of_descriptor s 3927 (.lex permutation9 254) (by rfl)) (lex_9_254_prefix s) (positive_select s 254) (lex_9_254_image s)

theorem lex_9_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation9 254 (hmax permutation9) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 247) (lex_9_254_prefix s) (positive_select s 254) (lex_9_254_image s)

theorem lex_9_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3927), (Sat.Literal.neg 256)] :=
  (lex_9_254_gate s).prop _ (List.Mem.head _)

theorem lex_9_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3927), (Sat.Literal.neg 254), (Sat.Literal.pos 247)] :=
  (lex_9_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3927), (Sat.Literal.pos 254), (Sat.Literal.neg 247)] :=
  (lex_9_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 247), (Sat.Literal.pos 3927)] :=
  (lex_9_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 247), (Sat.Literal.pos 3927)] :=
  (lex_9_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3927) = lexBefore s permutation9 253 := by
  exact (positive_lex_of_descriptor s 3927 permutation9 254 (by rfl)).trans ((lex_skipped s permutation9 253 254 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation9 253) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation9 253 by rw [image9_eq]; rfl))

theorem lex_9_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3928) (Sat.Literal.pos 3927) (Sat.Literal.pos 253) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation9 253 (assignment s)
    (Sat.Literal.pos 3928) (Sat.Literal.pos 3927) (Sat.Literal.pos 253) (Sat.Literal.pos 239) (positive_of_descriptor s 3928 (.lex permutation9 253) (by rfl)) (lex_9_253_prefix s) (positive_select s 253) (lex_9_253_image s)

theorem lex_9_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3927), (Sat.Literal.pos 253), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation9 253 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3927) (Sat.Literal.pos 253) (Sat.Literal.pos 239) (lex_9_253_prefix s) (positive_select s 253) (lex_9_253_image s)

theorem lex_9_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3928), (Sat.Literal.pos 3927)] :=
  (lex_9_253_gate s).prop _ (List.Mem.head _)

theorem lex_9_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3928), (Sat.Literal.neg 253), (Sat.Literal.pos 239)] :=
  (lex_9_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3928), (Sat.Literal.pos 253), (Sat.Literal.neg 239)] :=
  (lex_9_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3927), (Sat.Literal.neg 253), (Sat.Literal.neg 239), (Sat.Literal.pos 3928)] :=
  (lex_9_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3927), (Sat.Literal.pos 253), (Sat.Literal.pos 239), (Sat.Literal.pos 3928)] :=
  (lex_9_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3928) = lexBefore s permutation9 252 := by
  exact (positive_lex_of_descriptor s 3928 permutation9 253 (by rfl)).trans ((lex_skipped s permutation9 252 253 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation9 252) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation9 252 by rw [image9_eq]; rfl))

theorem lex_9_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3929) (Sat.Literal.pos 3928) (Sat.Literal.pos 252) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation9 252 (assignment s)
    (Sat.Literal.pos 3929) (Sat.Literal.pos 3928) (Sat.Literal.pos 252) (Sat.Literal.pos 231) (positive_of_descriptor s 3929 (.lex permutation9 252) (by rfl)) (lex_9_252_prefix s) (positive_select s 252) (lex_9_252_image s)

theorem lex_9_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3928), (Sat.Literal.pos 252), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation9 252 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3928) (Sat.Literal.pos 252) (Sat.Literal.pos 231) (lex_9_252_prefix s) (positive_select s 252) (lex_9_252_image s)

theorem lex_9_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3929), (Sat.Literal.pos 3928)] :=
  (lex_9_252_gate s).prop _ (List.Mem.head _)

theorem lex_9_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3929), (Sat.Literal.neg 252), (Sat.Literal.pos 231)] :=
  (lex_9_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3929), (Sat.Literal.pos 252), (Sat.Literal.neg 231)] :=
  (lex_9_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3928), (Sat.Literal.neg 252), (Sat.Literal.neg 231), (Sat.Literal.pos 3929)] :=
  (lex_9_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3928), (Sat.Literal.pos 252), (Sat.Literal.pos 231), (Sat.Literal.pos 3929)] :=
  (lex_9_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3929) = lexBefore s permutation9 251 := by
  exact (positive_lex_of_descriptor s 3929 permutation9 252 (by rfl)).trans ((lex_skipped s permutation9 251 252 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation9 251) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation9 251 by rw [image9_eq]; rfl))

theorem lex_9_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3930) (Sat.Literal.pos 3929) (Sat.Literal.pos 251) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation9 251 (assignment s)
    (Sat.Literal.pos 3930) (Sat.Literal.pos 3929) (Sat.Literal.pos 251) (Sat.Literal.pos 223) (positive_of_descriptor s 3930 (.lex permutation9 251) (by rfl)) (lex_9_251_prefix s) (positive_select s 251) (lex_9_251_image s)

theorem lex_9_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3929), (Sat.Literal.pos 251), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation9 251 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3929) (Sat.Literal.pos 251) (Sat.Literal.pos 223) (lex_9_251_prefix s) (positive_select s 251) (lex_9_251_image s)

theorem lex_9_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3930), (Sat.Literal.pos 3929)] :=
  (lex_9_251_gate s).prop _ (List.Mem.head _)

theorem lex_9_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3930), (Sat.Literal.neg 251), (Sat.Literal.pos 223)] :=
  (lex_9_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3930), (Sat.Literal.pos 251), (Sat.Literal.neg 223)] :=
  (lex_9_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3929), (Sat.Literal.neg 251), (Sat.Literal.neg 223), (Sat.Literal.pos 3930)] :=
  (lex_9_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3929), (Sat.Literal.pos 251), (Sat.Literal.pos 223), (Sat.Literal.pos 3930)] :=
  (lex_9_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3930) = lexBefore s permutation9 250 := by
  exact (positive_lex_of_descriptor s 3930 permutation9 251 (by rfl)).trans ((lex_skipped s permutation9 250 251 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation9 250) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation9 250 by rw [image9_eq]; rfl))

theorem lex_9_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3931) (Sat.Literal.pos 3930) (Sat.Literal.pos 250) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation9 250 (assignment s)
    (Sat.Literal.pos 3931) (Sat.Literal.pos 3930) (Sat.Literal.pos 250) (Sat.Literal.pos 215) (positive_of_descriptor s 3931 (.lex permutation9 250) (by rfl)) (lex_9_250_prefix s) (positive_select s 250) (lex_9_250_image s)

theorem lex_9_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3930), (Sat.Literal.pos 250), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation9 250 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3930) (Sat.Literal.pos 250) (Sat.Literal.pos 215) (lex_9_250_prefix s) (positive_select s 250) (lex_9_250_image s)

theorem lex_9_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3931), (Sat.Literal.pos 3930)] :=
  (lex_9_250_gate s).prop _ (List.Mem.head _)

theorem lex_9_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3931), (Sat.Literal.neg 250), (Sat.Literal.pos 215)] :=
  (lex_9_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3931), (Sat.Literal.pos 250), (Sat.Literal.neg 215)] :=
  (lex_9_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3930), (Sat.Literal.neg 250), (Sat.Literal.neg 215), (Sat.Literal.pos 3931)] :=
  (lex_9_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3930), (Sat.Literal.pos 250), (Sat.Literal.pos 215), (Sat.Literal.pos 3931)] :=
  (lex_9_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3931) = lexBefore s permutation9 249 := by
  exact (positive_lex_of_descriptor s 3931 permutation9 250 (by rfl)).trans ((lex_skipped s permutation9 249 250 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation9 249) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation9 249 by rw [image9_eq]; rfl))

theorem lex_9_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3932) (Sat.Literal.pos 3931) (Sat.Literal.pos 249) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation9 249 (assignment s)
    (Sat.Literal.pos 3932) (Sat.Literal.pos 3931) (Sat.Literal.pos 249) (Sat.Literal.pos 207) (positive_of_descriptor s 3932 (.lex permutation9 249) (by rfl)) (lex_9_249_prefix s) (positive_select s 249) (lex_9_249_image s)

theorem lex_9_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3931), (Sat.Literal.pos 249), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation9 249 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3931) (Sat.Literal.pos 249) (Sat.Literal.pos 207) (lex_9_249_prefix s) (positive_select s 249) (lex_9_249_image s)

theorem lex_9_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3932), (Sat.Literal.pos 3931)] :=
  (lex_9_249_gate s).prop _ (List.Mem.head _)

theorem lex_9_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3932), (Sat.Literal.neg 249), (Sat.Literal.pos 207)] :=
  (lex_9_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3932), (Sat.Literal.pos 249), (Sat.Literal.neg 207)] :=
  (lex_9_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3931), (Sat.Literal.neg 249), (Sat.Literal.neg 207), (Sat.Literal.pos 3932)] :=
  (lex_9_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3931), (Sat.Literal.pos 249), (Sat.Literal.pos 207), (Sat.Literal.pos 3932)] :=
  (lex_9_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3932) = lexBefore s permutation9 248 := by
  exact (positive_lex_of_descriptor s 3932 permutation9 249 (by rfl)).trans ((lex_skipped s permutation9 248 249 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation9 248) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation9 248 by rw [image9_eq]; rfl))

theorem lex_9_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3933) (Sat.Literal.pos 3932) (Sat.Literal.pos 248) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation9 248 (assignment s)
    (Sat.Literal.pos 3933) (Sat.Literal.pos 3932) (Sat.Literal.pos 248) (Sat.Literal.pos 199) (positive_of_descriptor s 3933 (.lex permutation9 248) (by rfl)) (lex_9_248_prefix s) (positive_select s 248) (lex_9_248_image s)

theorem lex_9_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3932), (Sat.Literal.pos 248), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation9 248 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3932) (Sat.Literal.pos 248) (Sat.Literal.pos 199) (lex_9_248_prefix s) (positive_select s 248) (lex_9_248_image s)

theorem lex_9_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3933), (Sat.Literal.pos 3932)] :=
  (lex_9_248_gate s).prop _ (List.Mem.head _)

theorem lex_9_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3933), (Sat.Literal.neg 248), (Sat.Literal.pos 199)] :=
  (lex_9_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3933), (Sat.Literal.pos 248), (Sat.Literal.neg 199)] :=
  (lex_9_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3932), (Sat.Literal.neg 248), (Sat.Literal.neg 199), (Sat.Literal.pos 3933)] :=
  (lex_9_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3932), (Sat.Literal.pos 248), (Sat.Literal.pos 199), (Sat.Literal.pos 3933)] :=
  (lex_9_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3933) = lexBefore s permutation9 247 := by
  exact (positive_lex_of_descriptor s 3933 permutation9 248 (by rfl)).trans ((lex_skipped s permutation9 247 248 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation9 247) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation9 247 by rw [image9_eq]; rfl))

theorem lex_9_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3934) (Sat.Literal.pos 3933) (Sat.Literal.pos 247) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation9 247 (assignment s)
    (Sat.Literal.pos 3934) (Sat.Literal.pos 3933) (Sat.Literal.pos 247) (Sat.Literal.pos 191) (positive_of_descriptor s 3934 (.lex permutation9 247) (by rfl)) (lex_9_247_prefix s) (positive_select s 247) (lex_9_247_image s)

theorem lex_9_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3933), (Sat.Literal.pos 247), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation9 247 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3933) (Sat.Literal.pos 247) (Sat.Literal.pos 191) (lex_9_247_prefix s) (positive_select s 247) (lex_9_247_image s)

theorem lex_9_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3934), (Sat.Literal.pos 3933)] :=
  (lex_9_247_gate s).prop _ (List.Mem.head _)

theorem lex_9_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3934), (Sat.Literal.neg 247), (Sat.Literal.pos 191)] :=
  (lex_9_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3934), (Sat.Literal.pos 247), (Sat.Literal.neg 191)] :=
  (lex_9_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3933), (Sat.Literal.neg 247), (Sat.Literal.neg 191), (Sat.Literal.pos 3934)] :=
  (lex_9_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3933), (Sat.Literal.pos 247), (Sat.Literal.pos 191), (Sat.Literal.pos 3934)] :=
  (lex_9_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3934) = lexBefore s permutation9 246 := by
  exact (positive_lex_of_descriptor s 3934 permutation9 247 (by rfl)).trans ((lex_skipped s permutation9 246 247 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation9 246) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation9 246 by rw [image9_eq]; rfl))

theorem lex_9_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3935) (Sat.Literal.pos 3934) (Sat.Literal.pos 246) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation9 246 (assignment s)
    (Sat.Literal.pos 3935) (Sat.Literal.pos 3934) (Sat.Literal.pos 246) (Sat.Literal.pos 183) (positive_of_descriptor s 3935 (.lex permutation9 246) (by rfl)) (lex_9_246_prefix s) (positive_select s 246) (lex_9_246_image s)

theorem lex_9_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3934), (Sat.Literal.pos 246), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation9 246 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3934) (Sat.Literal.pos 246) (Sat.Literal.pos 183) (lex_9_246_prefix s) (positive_select s 246) (lex_9_246_image s)

theorem lex_9_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3935), (Sat.Literal.pos 3934)] :=
  (lex_9_246_gate s).prop _ (List.Mem.head _)

theorem lex_9_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3935), (Sat.Literal.neg 246), (Sat.Literal.pos 183)] :=
  (lex_9_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3935), (Sat.Literal.pos 246), (Sat.Literal.neg 183)] :=
  (lex_9_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3934), (Sat.Literal.neg 246), (Sat.Literal.neg 183), (Sat.Literal.pos 3935)] :=
  (lex_9_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3934), (Sat.Literal.pos 246), (Sat.Literal.pos 183), (Sat.Literal.pos 3935)] :=
  (lex_9_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3935) = lexBefore s permutation9 245 := by
  exact (positive_lex_of_descriptor s 3935 permutation9 246 (by rfl)).trans ((lex_skipped s permutation9 245 246 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation9 245) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation9 245 by rw [image9_eq]; rfl))

theorem lex_9_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3936) (Sat.Literal.pos 3935) (Sat.Literal.pos 245) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation9 245 (assignment s)
    (Sat.Literal.pos 3936) (Sat.Literal.pos 3935) (Sat.Literal.pos 245) (Sat.Literal.pos 175) (positive_of_descriptor s 3936 (.lex permutation9 245) (by rfl)) (lex_9_245_prefix s) (positive_select s 245) (lex_9_245_image s)

theorem lex_9_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3935), (Sat.Literal.pos 245), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation9 245 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3935) (Sat.Literal.pos 245) (Sat.Literal.pos 175) (lex_9_245_prefix s) (positive_select s 245) (lex_9_245_image s)

theorem lex_9_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3936), (Sat.Literal.pos 3935)] :=
  (lex_9_245_gate s).prop _ (List.Mem.head _)

theorem lex_9_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3936), (Sat.Literal.neg 245), (Sat.Literal.pos 175)] :=
  (lex_9_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3936), (Sat.Literal.pos 245), (Sat.Literal.neg 175)] :=
  (lex_9_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3935), (Sat.Literal.neg 245), (Sat.Literal.neg 175), (Sat.Literal.pos 3936)] :=
  (lex_9_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3935), (Sat.Literal.pos 245), (Sat.Literal.pos 175), (Sat.Literal.pos 3936)] :=
  (lex_9_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3936) = lexBefore s permutation9 244 := by
  exact (positive_lex_of_descriptor s 3936 permutation9 245 (by rfl)).trans ((lex_skipped s permutation9 244 245 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation9 244) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation9 244 by rw [image9_eq]; rfl))

theorem lex_9_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3937) (Sat.Literal.pos 3936) (Sat.Literal.pos 244) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation9 244 (assignment s)
    (Sat.Literal.pos 3937) (Sat.Literal.pos 3936) (Sat.Literal.pos 244) (Sat.Literal.pos 167) (positive_of_descriptor s 3937 (.lex permutation9 244) (by rfl)) (lex_9_244_prefix s) (positive_select s 244) (lex_9_244_image s)

theorem lex_9_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3936), (Sat.Literal.pos 244), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation9 244 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3936) (Sat.Literal.pos 244) (Sat.Literal.pos 167) (lex_9_244_prefix s) (positive_select s 244) (lex_9_244_image s)

theorem lex_9_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3937), (Sat.Literal.pos 3936)] :=
  (lex_9_244_gate s).prop _ (List.Mem.head _)

theorem lex_9_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3937), (Sat.Literal.neg 244), (Sat.Literal.pos 167)] :=
  (lex_9_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3937), (Sat.Literal.pos 244), (Sat.Literal.neg 167)] :=
  (lex_9_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3936), (Sat.Literal.neg 244), (Sat.Literal.neg 167), (Sat.Literal.pos 3937)] :=
  (lex_9_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3936), (Sat.Literal.pos 244), (Sat.Literal.pos 167), (Sat.Literal.pos 3937)] :=
  (lex_9_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3937) = lexBefore s permutation9 243 := by
  exact (positive_lex_of_descriptor s 3937 permutation9 244 (by rfl)).trans ((lex_skipped s permutation9 243 244 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation9 243) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation9 243 by rw [image9_eq]; rfl))

theorem lex_9_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3938) (Sat.Literal.pos 3937) (Sat.Literal.pos 243) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation9 243 (assignment s)
    (Sat.Literal.pos 3938) (Sat.Literal.pos 3937) (Sat.Literal.pos 243) (Sat.Literal.pos 159) (positive_of_descriptor s 3938 (.lex permutation9 243) (by rfl)) (lex_9_243_prefix s) (positive_select s 243) (lex_9_243_image s)

theorem lex_9_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3937), (Sat.Literal.pos 243), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation9 243 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3937) (Sat.Literal.pos 243) (Sat.Literal.pos 159) (lex_9_243_prefix s) (positive_select s 243) (lex_9_243_image s)

theorem lex_9_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3938), (Sat.Literal.pos 3937)] :=
  (lex_9_243_gate s).prop _ (List.Mem.head _)

theorem lex_9_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3938), (Sat.Literal.neg 243), (Sat.Literal.pos 159)] :=
  (lex_9_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3938), (Sat.Literal.pos 243), (Sat.Literal.neg 159)] :=
  (lex_9_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3937), (Sat.Literal.neg 243), (Sat.Literal.neg 159), (Sat.Literal.pos 3938)] :=
  (lex_9_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3937), (Sat.Literal.pos 243), (Sat.Literal.pos 159), (Sat.Literal.pos 3938)] :=
  (lex_9_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3938) = lexBefore s permutation9 242 := by
  exact (positive_lex_of_descriptor s 3938 permutation9 243 (by rfl)).trans ((lex_skipped s permutation9 242 243 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation9 242) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation9 242 by rw [image9_eq]; rfl))

theorem lex_9_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3939) (Sat.Literal.pos 3938) (Sat.Literal.pos 242) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation9 242 (assignment s)
    (Sat.Literal.pos 3939) (Sat.Literal.pos 3938) (Sat.Literal.pos 242) (Sat.Literal.pos 151) (positive_of_descriptor s 3939 (.lex permutation9 242) (by rfl)) (lex_9_242_prefix s) (positive_select s 242) (lex_9_242_image s)

theorem lex_9_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3938), (Sat.Literal.pos 242), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation9 242 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3938) (Sat.Literal.pos 242) (Sat.Literal.pos 151) (lex_9_242_prefix s) (positive_select s 242) (lex_9_242_image s)

theorem lex_9_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3939), (Sat.Literal.pos 3938)] :=
  (lex_9_242_gate s).prop _ (List.Mem.head _)

theorem lex_9_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3939), (Sat.Literal.neg 242), (Sat.Literal.pos 151)] :=
  (lex_9_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3939), (Sat.Literal.pos 242), (Sat.Literal.neg 151)] :=
  (lex_9_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3938), (Sat.Literal.neg 242), (Sat.Literal.neg 151), (Sat.Literal.pos 3939)] :=
  (lex_9_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3938), (Sat.Literal.pos 242), (Sat.Literal.pos 151), (Sat.Literal.pos 3939)] :=
  (lex_9_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3939) = lexBefore s permutation9 241 := by
  exact (positive_lex_of_descriptor s 3939 permutation9 242 (by rfl)).trans ((lex_skipped s permutation9 241 242 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation9 241) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation9 241 by rw [image9_eq]; rfl))

theorem lex_9_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3940) (Sat.Literal.pos 3939) (Sat.Literal.pos 241) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation9 241 (assignment s)
    (Sat.Literal.pos 3940) (Sat.Literal.pos 3939) (Sat.Literal.pos 241) (Sat.Literal.pos 143) (positive_of_descriptor s 3940 (.lex permutation9 241) (by rfl)) (lex_9_241_prefix s) (positive_select s 241) (lex_9_241_image s)

theorem lex_9_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3939), (Sat.Literal.pos 241), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation9 241 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3939) (Sat.Literal.pos 241) (Sat.Literal.pos 143) (lex_9_241_prefix s) (positive_select s 241) (lex_9_241_image s)

theorem lex_9_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3940), (Sat.Literal.pos 3939)] :=
  (lex_9_241_gate s).prop _ (List.Mem.head _)

theorem lex_9_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3940), (Sat.Literal.neg 241), (Sat.Literal.pos 143)] :=
  (lex_9_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3940), (Sat.Literal.pos 241), (Sat.Literal.neg 143)] :=
  (lex_9_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3939), (Sat.Literal.neg 241), (Sat.Literal.neg 143), (Sat.Literal.pos 3940)] :=
  (lex_9_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3939), (Sat.Literal.pos 241), (Sat.Literal.pos 143), (Sat.Literal.pos 3940)] :=
  (lex_9_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3940) = lexBefore s permutation9 240 := by
  exact (positive_lex_of_descriptor s 3940 permutation9 241 (by rfl)).trans ((lex_skipped s permutation9 240 241 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation9 240) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation9 240 by rw [image9_eq]; rfl))

theorem lex_9_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3941) (Sat.Literal.pos 3940) (Sat.Literal.pos 240) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation9 240 (assignment s)
    (Sat.Literal.pos 3941) (Sat.Literal.pos 3940) (Sat.Literal.pos 240) (Sat.Literal.pos 135) (positive_of_descriptor s 3941 (.lex permutation9 240) (by rfl)) (lex_9_240_prefix s) (positive_select s 240) (lex_9_240_image s)

theorem lex_9_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3940), (Sat.Literal.pos 240), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation9 240 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3940) (Sat.Literal.pos 240) (Sat.Literal.pos 135) (lex_9_240_prefix s) (positive_select s 240) (lex_9_240_image s)

theorem lex_9_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3941), (Sat.Literal.pos 3940)] :=
  (lex_9_240_gate s).prop _ (List.Mem.head _)

theorem lex_9_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3941), (Sat.Literal.neg 240), (Sat.Literal.pos 135)] :=
  (lex_9_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3941), (Sat.Literal.pos 240), (Sat.Literal.neg 135)] :=
  (lex_9_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3940), (Sat.Literal.neg 240), (Sat.Literal.neg 135), (Sat.Literal.pos 3941)] :=
  (lex_9_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3940), (Sat.Literal.pos 240), (Sat.Literal.pos 135), (Sat.Literal.pos 3941)] :=
  (lex_9_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3941) = lexBefore s permutation9 239 := by
  exact (positive_lex_of_descriptor s 3941 permutation9 240 (by rfl)).trans ((lex_skipped s permutation9 239 240 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation9 239) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation9 239 by rw [image9_eq]; rfl))

theorem lex_9_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3942) (Sat.Literal.pos 3941) (Sat.Literal.pos 239) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation9 239 (assignment s)
    (Sat.Literal.pos 3942) (Sat.Literal.pos 3941) (Sat.Literal.pos 239) (Sat.Literal.pos 127) (positive_of_descriptor s 3942 (.lex permutation9 239) (by rfl)) (lex_9_239_prefix s) (positive_select s 239) (lex_9_239_image s)

theorem lex_9_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3941), (Sat.Literal.pos 239), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation9 239 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3941) (Sat.Literal.pos 239) (Sat.Literal.pos 127) (lex_9_239_prefix s) (positive_select s 239) (lex_9_239_image s)

theorem lex_9_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3942), (Sat.Literal.pos 3941)] :=
  (lex_9_239_gate s).prop _ (List.Mem.head _)

theorem lex_9_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3942), (Sat.Literal.neg 239), (Sat.Literal.pos 127)] :=
  (lex_9_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3942), (Sat.Literal.pos 239), (Sat.Literal.neg 127)] :=
  (lex_9_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3941), (Sat.Literal.neg 239), (Sat.Literal.neg 127), (Sat.Literal.pos 3942)] :=
  (lex_9_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3941), (Sat.Literal.pos 239), (Sat.Literal.pos 127), (Sat.Literal.pos 3942)] :=
  (lex_9_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3942) = lexBefore s permutation9 238 := by
  exact (positive_lex_of_descriptor s 3942 permutation9 239 (by rfl)).trans ((lex_skipped s permutation9 238 239 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation9 238) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation9 238 by rw [image9_eq]; rfl))

theorem lex_9_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3943) (Sat.Literal.pos 3942) (Sat.Literal.pos 238) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation9 238 (assignment s)
    (Sat.Literal.pos 3943) (Sat.Literal.pos 3942) (Sat.Literal.pos 238) (Sat.Literal.pos 119) (positive_of_descriptor s 3943 (.lex permutation9 238) (by rfl)) (lex_9_238_prefix s) (positive_select s 238) (lex_9_238_image s)

theorem lex_9_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3942), (Sat.Literal.pos 238), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation9 238 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3942) (Sat.Literal.pos 238) (Sat.Literal.pos 119) (lex_9_238_prefix s) (positive_select s 238) (lex_9_238_image s)

theorem lex_9_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3943), (Sat.Literal.pos 3942)] :=
  (lex_9_238_gate s).prop _ (List.Mem.head _)

theorem lex_9_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3943), (Sat.Literal.neg 238), (Sat.Literal.pos 119)] :=
  (lex_9_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3943), (Sat.Literal.pos 238), (Sat.Literal.neg 119)] :=
  (lex_9_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3942), (Sat.Literal.neg 238), (Sat.Literal.neg 119), (Sat.Literal.pos 3943)] :=
  (lex_9_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3942), (Sat.Literal.pos 238), (Sat.Literal.pos 119), (Sat.Literal.pos 3943)] :=
  (lex_9_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3943) = lexBefore s permutation9 237 := by
  exact (positive_lex_of_descriptor s 3943 permutation9 238 (by rfl)).trans ((lex_skipped s permutation9 237 238 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation9 237) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation9 237 by rw [image9_eq]; rfl))

theorem lex_9_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3944) (Sat.Literal.pos 3943) (Sat.Literal.pos 237) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation9 237 (assignment s)
    (Sat.Literal.pos 3944) (Sat.Literal.pos 3943) (Sat.Literal.pos 237) (Sat.Literal.pos 111) (positive_of_descriptor s 3944 (.lex permutation9 237) (by rfl)) (lex_9_237_prefix s) (positive_select s 237) (lex_9_237_image s)

theorem lex_9_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3943), (Sat.Literal.pos 237), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation9 237 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3943) (Sat.Literal.pos 237) (Sat.Literal.pos 111) (lex_9_237_prefix s) (positive_select s 237) (lex_9_237_image s)

theorem lex_9_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3944), (Sat.Literal.pos 3943)] :=
  (lex_9_237_gate s).prop _ (List.Mem.head _)

theorem lex_9_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3944), (Sat.Literal.neg 237), (Sat.Literal.pos 111)] :=
  (lex_9_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3944), (Sat.Literal.pos 237), (Sat.Literal.neg 111)] :=
  (lex_9_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3943), (Sat.Literal.neg 237), (Sat.Literal.neg 111), (Sat.Literal.pos 3944)] :=
  (lex_9_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3943), (Sat.Literal.pos 237), (Sat.Literal.pos 111), (Sat.Literal.pos 3944)] :=
  (lex_9_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3944) = lexBefore s permutation9 236 := by
  exact (positive_lex_of_descriptor s 3944 permutation9 237 (by rfl)).trans ((lex_skipped s permutation9 236 237 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation9 236) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation9 236 by rw [image9_eq]; rfl))

theorem lex_9_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3945) (Sat.Literal.pos 3944) (Sat.Literal.pos 236) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation9 236 (assignment s)
    (Sat.Literal.pos 3945) (Sat.Literal.pos 3944) (Sat.Literal.pos 236) (Sat.Literal.pos 103) (positive_of_descriptor s 3945 (.lex permutation9 236) (by rfl)) (lex_9_236_prefix s) (positive_select s 236) (lex_9_236_image s)

theorem lex_9_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3944), (Sat.Literal.pos 236), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation9 236 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3944) (Sat.Literal.pos 236) (Sat.Literal.pos 103) (lex_9_236_prefix s) (positive_select s 236) (lex_9_236_image s)

theorem lex_9_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3945), (Sat.Literal.pos 3944)] :=
  (lex_9_236_gate s).prop _ (List.Mem.head _)

theorem lex_9_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3945), (Sat.Literal.neg 236), (Sat.Literal.pos 103)] :=
  (lex_9_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3945), (Sat.Literal.pos 236), (Sat.Literal.neg 103)] :=
  (lex_9_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3944), (Sat.Literal.neg 236), (Sat.Literal.neg 103), (Sat.Literal.pos 3945)] :=
  (lex_9_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3944), (Sat.Literal.pos 236), (Sat.Literal.pos 103), (Sat.Literal.pos 3945)] :=
  (lex_9_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3945) = lexBefore s permutation9 235 := by
  exact (positive_lex_of_descriptor s 3945 permutation9 236 (by rfl)).trans ((lex_skipped s permutation9 235 236 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation9 235) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation9 235 by rw [image9_eq]; rfl))

theorem lex_9_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3946) (Sat.Literal.pos 3945) (Sat.Literal.pos 235) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation9 235 (assignment s)
    (Sat.Literal.pos 3946) (Sat.Literal.pos 3945) (Sat.Literal.pos 235) (Sat.Literal.pos 95) (positive_of_descriptor s 3946 (.lex permutation9 235) (by rfl)) (lex_9_235_prefix s) (positive_select s 235) (lex_9_235_image s)

theorem lex_9_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3945), (Sat.Literal.pos 235), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation9 235 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3945) (Sat.Literal.pos 235) (Sat.Literal.pos 95) (lex_9_235_prefix s) (positive_select s 235) (lex_9_235_image s)

theorem lex_9_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3946), (Sat.Literal.pos 3945)] :=
  (lex_9_235_gate s).prop _ (List.Mem.head _)

theorem lex_9_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3946), (Sat.Literal.neg 235), (Sat.Literal.pos 95)] :=
  (lex_9_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3946), (Sat.Literal.pos 235), (Sat.Literal.neg 95)] :=
  (lex_9_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3945), (Sat.Literal.neg 235), (Sat.Literal.neg 95), (Sat.Literal.pos 3946)] :=
  (lex_9_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3945), (Sat.Literal.pos 235), (Sat.Literal.pos 95), (Sat.Literal.pos 3946)] :=
  (lex_9_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3946) = lexBefore s permutation9 234 := by
  exact (positive_lex_of_descriptor s 3946 permutation9 235 (by rfl)).trans ((lex_skipped s permutation9 234 235 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation9 234) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation9 234 by rw [image9_eq]; rfl))

theorem lex_9_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3947) (Sat.Literal.pos 3946) (Sat.Literal.pos 234) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation9 234 (assignment s)
    (Sat.Literal.pos 3947) (Sat.Literal.pos 3946) (Sat.Literal.pos 234) (Sat.Literal.pos 87) (positive_of_descriptor s 3947 (.lex permutation9 234) (by rfl)) (lex_9_234_prefix s) (positive_select s 234) (lex_9_234_image s)

theorem lex_9_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3946), (Sat.Literal.pos 234), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation9 234 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3946) (Sat.Literal.pos 234) (Sat.Literal.pos 87) (lex_9_234_prefix s) (positive_select s 234) (lex_9_234_image s)

theorem lex_9_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3947), (Sat.Literal.pos 3946)] :=
  (lex_9_234_gate s).prop _ (List.Mem.head _)

theorem lex_9_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3947), (Sat.Literal.neg 234), (Sat.Literal.pos 87)] :=
  (lex_9_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3947), (Sat.Literal.pos 234), (Sat.Literal.neg 87)] :=
  (lex_9_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3946), (Sat.Literal.neg 234), (Sat.Literal.neg 87), (Sat.Literal.pos 3947)] :=
  (lex_9_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3946), (Sat.Literal.pos 234), (Sat.Literal.pos 87), (Sat.Literal.pos 3947)] :=
  (lex_9_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3947) = lexBefore s permutation9 233 := by
  exact (positive_lex_of_descriptor s 3947 permutation9 234 (by rfl)).trans ((lex_skipped s permutation9 233 234 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation9 233) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation9 233 by rw [image9_eq]; rfl))

theorem lex_9_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3948) (Sat.Literal.pos 3947) (Sat.Literal.pos 233) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation9 233 (assignment s)
    (Sat.Literal.pos 3948) (Sat.Literal.pos 3947) (Sat.Literal.pos 233) (Sat.Literal.pos 79) (positive_of_descriptor s 3948 (.lex permutation9 233) (by rfl)) (lex_9_233_prefix s) (positive_select s 233) (lex_9_233_image s)

theorem lex_9_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3947), (Sat.Literal.pos 233), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation9 233 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3947) (Sat.Literal.pos 233) (Sat.Literal.pos 79) (lex_9_233_prefix s) (positive_select s 233) (lex_9_233_image s)

theorem lex_9_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3948), (Sat.Literal.pos 3947)] :=
  (lex_9_233_gate s).prop _ (List.Mem.head _)

theorem lex_9_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3948), (Sat.Literal.neg 233), (Sat.Literal.pos 79)] :=
  (lex_9_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3948), (Sat.Literal.pos 233), (Sat.Literal.neg 79)] :=
  (lex_9_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3947), (Sat.Literal.neg 233), (Sat.Literal.neg 79), (Sat.Literal.pos 3948)] :=
  (lex_9_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3947), (Sat.Literal.pos 233), (Sat.Literal.pos 79), (Sat.Literal.pos 3948)] :=
  (lex_9_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3948) = lexBefore s permutation9 232 := by
  exact (positive_lex_of_descriptor s 3948 permutation9 233 (by rfl)).trans ((lex_skipped s permutation9 232 233 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation9 232) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation9 232 by rw [image9_eq]; rfl))

theorem lex_9_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3949) (Sat.Literal.pos 3948) (Sat.Literal.pos 232) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation9 232 (assignment s)
    (Sat.Literal.pos 3949) (Sat.Literal.pos 3948) (Sat.Literal.pos 232) (Sat.Literal.pos 71) (positive_of_descriptor s 3949 (.lex permutation9 232) (by rfl)) (lex_9_232_prefix s) (positive_select s 232) (lex_9_232_image s)

theorem lex_9_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3948), (Sat.Literal.pos 232), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation9 232 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3948) (Sat.Literal.pos 232) (Sat.Literal.pos 71) (lex_9_232_prefix s) (positive_select s 232) (lex_9_232_image s)

theorem lex_9_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3949), (Sat.Literal.pos 3948)] :=
  (lex_9_232_gate s).prop _ (List.Mem.head _)

theorem lex_9_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3949), (Sat.Literal.neg 232), (Sat.Literal.pos 71)] :=
  (lex_9_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3949), (Sat.Literal.pos 232), (Sat.Literal.neg 71)] :=
  (lex_9_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3948), (Sat.Literal.neg 232), (Sat.Literal.neg 71), (Sat.Literal.pos 3949)] :=
  (lex_9_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3948), (Sat.Literal.pos 232), (Sat.Literal.pos 71), (Sat.Literal.pos 3949)] :=
  (lex_9_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3949) = lexBefore s permutation9 231 := by
  exact (positive_lex_of_descriptor s 3949 permutation9 232 (by rfl)).trans ((lex_skipped s permutation9 231 232 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation9 231) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation9 231 by rw [image9_eq]; rfl))

theorem lex_9_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3950) (Sat.Literal.pos 3949) (Sat.Literal.pos 231) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation9 231 (assignment s)
    (Sat.Literal.pos 3950) (Sat.Literal.pos 3949) (Sat.Literal.pos 231) (Sat.Literal.pos 63) (positive_of_descriptor s 3950 (.lex permutation9 231) (by rfl)) (lex_9_231_prefix s) (positive_select s 231) (lex_9_231_image s)

theorem lex_9_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3949), (Sat.Literal.pos 231), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation9 231 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3949) (Sat.Literal.pos 231) (Sat.Literal.pos 63) (lex_9_231_prefix s) (positive_select s 231) (lex_9_231_image s)

theorem lex_9_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3950), (Sat.Literal.pos 3949)] :=
  (lex_9_231_gate s).prop _ (List.Mem.head _)

theorem lex_9_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3950), (Sat.Literal.neg 231), (Sat.Literal.pos 63)] :=
  (lex_9_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3950), (Sat.Literal.pos 231), (Sat.Literal.neg 63)] :=
  (lex_9_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3949), (Sat.Literal.neg 231), (Sat.Literal.neg 63), (Sat.Literal.pos 3950)] :=
  (lex_9_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3949), (Sat.Literal.pos 231), (Sat.Literal.pos 63), (Sat.Literal.pos 3950)] :=
  (lex_9_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3950) = lexBefore s permutation9 230 := by
  exact (positive_lex_of_descriptor s 3950 permutation9 231 (by rfl)).trans ((lex_skipped s permutation9 230 231 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation9 230) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation9 230 by rw [image9_eq]; rfl))

theorem lex_9_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3951) (Sat.Literal.pos 3950) (Sat.Literal.pos 230) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation9 230 (assignment s)
    (Sat.Literal.pos 3951) (Sat.Literal.pos 3950) (Sat.Literal.pos 230) (Sat.Literal.pos 55) (positive_of_descriptor s 3951 (.lex permutation9 230) (by rfl)) (lex_9_230_prefix s) (positive_select s 230) (lex_9_230_image s)

theorem lex_9_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3950), (Sat.Literal.pos 230), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation9 230 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3950) (Sat.Literal.pos 230) (Sat.Literal.pos 55) (lex_9_230_prefix s) (positive_select s 230) (lex_9_230_image s)

theorem lex_9_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3951), (Sat.Literal.pos 3950)] :=
  (lex_9_230_gate s).prop _ (List.Mem.head _)

theorem lex_9_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3951), (Sat.Literal.neg 230), (Sat.Literal.pos 55)] :=
  (lex_9_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3951), (Sat.Literal.pos 230), (Sat.Literal.neg 55)] :=
  (lex_9_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3950), (Sat.Literal.neg 230), (Sat.Literal.neg 55), (Sat.Literal.pos 3951)] :=
  (lex_9_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3950), (Sat.Literal.pos 230), (Sat.Literal.pos 55), (Sat.Literal.pos 3951)] :=
  (lex_9_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3951) = lexBefore s permutation9 229 := by
  exact (positive_lex_of_descriptor s 3951 permutation9 230 (by rfl)).trans ((lex_skipped s permutation9 229 230 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation9 229) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation9 229 by rw [image9_eq]; rfl))

theorem lex_9_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3952) (Sat.Literal.pos 3951) (Sat.Literal.pos 229) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation9 229 (assignment s)
    (Sat.Literal.pos 3952) (Sat.Literal.pos 3951) (Sat.Literal.pos 229) (Sat.Literal.pos 47) (positive_of_descriptor s 3952 (.lex permutation9 229) (by rfl)) (lex_9_229_prefix s) (positive_select s 229) (lex_9_229_image s)

theorem lex_9_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3951), (Sat.Literal.pos 229), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation9 229 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3951) (Sat.Literal.pos 229) (Sat.Literal.pos 47) (lex_9_229_prefix s) (positive_select s 229) (lex_9_229_image s)

theorem lex_9_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3952), (Sat.Literal.pos 3951)] :=
  (lex_9_229_gate s).prop _ (List.Mem.head _)

theorem lex_9_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3952), (Sat.Literal.neg 229), (Sat.Literal.pos 47)] :=
  (lex_9_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3952), (Sat.Literal.pos 229), (Sat.Literal.neg 47)] :=
  (lex_9_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3951), (Sat.Literal.neg 229), (Sat.Literal.neg 47), (Sat.Literal.pos 3952)] :=
  (lex_9_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3951), (Sat.Literal.pos 229), (Sat.Literal.pos 47), (Sat.Literal.pos 3952)] :=
  (lex_9_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3952) = lexBefore s permutation9 228 := by
  exact (positive_lex_of_descriptor s 3952 permutation9 229 (by rfl)).trans ((lex_skipped s permutation9 228 229 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 39) = s (permuteMask permutation9 228) := by
  exact (positive_select s 39).trans (congrArg s (show (39 : Fin 256) = permuteMask permutation9 228 by rw [image9_eq]; rfl))

theorem lex_9_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3953) (Sat.Literal.pos 3952) (Sat.Literal.pos 228) (Sat.Literal.pos 39)) := by
  exact equality_gate s permutation9 228 (assignment s)
    (Sat.Literal.pos 3953) (Sat.Literal.pos 3952) (Sat.Literal.pos 228) (Sat.Literal.pos 39) (positive_of_descriptor s 3953 (.lex permutation9 228) (by rfl)) (lex_9_228_prefix s) (positive_select s 228) (lex_9_228_image s)

theorem lex_9_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3952), (Sat.Literal.pos 228), (Sat.Literal.neg 39)] := by
  exact comparison_gate s permutation9 228 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3952) (Sat.Literal.pos 228) (Sat.Literal.pos 39) (lex_9_228_prefix s) (positive_select s 228) (lex_9_228_image s)

theorem lex_9_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3953), (Sat.Literal.pos 3952)] :=
  (lex_9_228_gate s).prop _ (List.Mem.head _)

theorem lex_9_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3953), (Sat.Literal.neg 228), (Sat.Literal.pos 39)] :=
  (lex_9_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3953), (Sat.Literal.pos 228), (Sat.Literal.neg 39)] :=
  (lex_9_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3952), (Sat.Literal.neg 228), (Sat.Literal.neg 39), (Sat.Literal.pos 3953)] :=
  (lex_9_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3952), (Sat.Literal.pos 228), (Sat.Literal.pos 39), (Sat.Literal.pos 3953)] :=
  (lex_9_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3953) = lexBefore s permutation9 227 := by
  exact (positive_lex_of_descriptor s 3953 permutation9 228 (by rfl)).trans ((lex_skipped s permutation9 227 228 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation9 227) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation9 227 by rw [image9_eq]; rfl))

theorem lex_9_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3954) (Sat.Literal.pos 3953) (Sat.Literal.pos 227) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation9 227 (assignment s)
    (Sat.Literal.pos 3954) (Sat.Literal.pos 3953) (Sat.Literal.pos 227) (Sat.Literal.pos 31) (positive_of_descriptor s 3954 (.lex permutation9 227) (by rfl)) (lex_9_227_prefix s) (positive_select s 227) (lex_9_227_image s)

theorem lex_9_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3953), (Sat.Literal.pos 227), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation9 227 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3953) (Sat.Literal.pos 227) (Sat.Literal.pos 31) (lex_9_227_prefix s) (positive_select s 227) (lex_9_227_image s)

theorem lex_9_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3954), (Sat.Literal.pos 3953)] :=
  (lex_9_227_gate s).prop _ (List.Mem.head _)

theorem lex_9_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3954), (Sat.Literal.neg 227), (Sat.Literal.pos 31)] :=
  (lex_9_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3954), (Sat.Literal.pos 227), (Sat.Literal.neg 31)] :=
  (lex_9_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3953), (Sat.Literal.neg 227), (Sat.Literal.neg 31), (Sat.Literal.pos 3954)] :=
  (lex_9_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3953), (Sat.Literal.pos 227), (Sat.Literal.pos 31), (Sat.Literal.pos 3954)] :=
  (lex_9_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3954) = lexBefore s permutation9 226 := by
  exact (positive_lex_of_descriptor s 3954 permutation9 227 (by rfl)).trans ((lex_skipped s permutation9 226 227 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation9 226) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation9 226 by rw [image9_eq]; rfl))

theorem lex_9_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3955) (Sat.Literal.pos 3954) (Sat.Literal.pos 226) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation9 226 (assignment s)
    (Sat.Literal.pos 3955) (Sat.Literal.pos 3954) (Sat.Literal.pos 226) (Sat.Literal.pos 23) (positive_of_descriptor s 3955 (.lex permutation9 226) (by rfl)) (lex_9_226_prefix s) (positive_select s 226) (lex_9_226_image s)

theorem lex_9_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3954), (Sat.Literal.pos 226), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation9 226 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3954) (Sat.Literal.pos 226) (Sat.Literal.pos 23) (lex_9_226_prefix s) (positive_select s 226) (lex_9_226_image s)

theorem lex_9_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3955), (Sat.Literal.pos 3954)] :=
  (lex_9_226_gate s).prop _ (List.Mem.head _)

theorem lex_9_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3955), (Sat.Literal.neg 226), (Sat.Literal.pos 23)] :=
  (lex_9_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3955), (Sat.Literal.pos 226), (Sat.Literal.neg 23)] :=
  (lex_9_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3954), (Sat.Literal.neg 226), (Sat.Literal.neg 23), (Sat.Literal.pos 3955)] :=
  (lex_9_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3954), (Sat.Literal.pos 226), (Sat.Literal.pos 23), (Sat.Literal.pos 3955)] :=
  (lex_9_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3955) = lexBefore s permutation9 225 := by
  exact (positive_lex_of_descriptor s 3955 permutation9 226 (by rfl)).trans ((lex_skipped s permutation9 225 226 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 15) = s (permuteMask permutation9 225) := by
  exact (positive_select s 15).trans (congrArg s (show (15 : Fin 256) = permuteMask permutation9 225 by rw [image9_eq]; rfl))

theorem lex_9_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3956) (Sat.Literal.pos 3955) (Sat.Literal.pos 225) (Sat.Literal.pos 15)) := by
  exact equality_gate s permutation9 225 (assignment s)
    (Sat.Literal.pos 3956) (Sat.Literal.pos 3955) (Sat.Literal.pos 225) (Sat.Literal.pos 15) (positive_of_descriptor s 3956 (.lex permutation9 225) (by rfl)) (lex_9_225_prefix s) (positive_select s 225) (lex_9_225_image s)

theorem lex_9_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3955), (Sat.Literal.pos 225), (Sat.Literal.neg 15)] := by
  exact comparison_gate s permutation9 225 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3955) (Sat.Literal.pos 225) (Sat.Literal.pos 15) (lex_9_225_prefix s) (positive_select s 225) (lex_9_225_image s)

theorem lex_9_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3956), (Sat.Literal.pos 3955)] :=
  (lex_9_225_gate s).prop _ (List.Mem.head _)

theorem lex_9_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3956), (Sat.Literal.neg 225), (Sat.Literal.pos 15)] :=
  (lex_9_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3956), (Sat.Literal.pos 225), (Sat.Literal.neg 15)] :=
  (lex_9_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3955), (Sat.Literal.neg 225), (Sat.Literal.neg 15), (Sat.Literal.pos 3956)] :=
  (lex_9_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3955), (Sat.Literal.pos 225), (Sat.Literal.pos 15), (Sat.Literal.pos 3956)] :=
  (lex_9_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3956) = lexBefore s permutation9 224 := by
  exact (positive_lex_of_descriptor s 3956 permutation9 225 (by rfl)).trans ((lex_skipped s permutation9 224 225 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 7) = s (permuteMask permutation9 224) := by
  exact (positive_select s 7).trans (congrArg s (show (7 : Fin 256) = permuteMask permutation9 224 by rw [image9_eq]; rfl))

theorem lex_9_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3957) (Sat.Literal.pos 3956) (Sat.Literal.pos 224) (Sat.Literal.pos 7)) := by
  exact equality_gate s permutation9 224 (assignment s)
    (Sat.Literal.pos 3957) (Sat.Literal.pos 3956) (Sat.Literal.pos 224) (Sat.Literal.pos 7) (positive_of_descriptor s 3957 (.lex permutation9 224) (by rfl)) (lex_9_224_prefix s) (positive_select s 224) (lex_9_224_image s)

theorem lex_9_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3956), (Sat.Literal.pos 224), (Sat.Literal.neg 7)] := by
  exact comparison_gate s permutation9 224 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3956) (Sat.Literal.pos 224) (Sat.Literal.pos 7) (lex_9_224_prefix s) (positive_select s 224) (lex_9_224_image s)

theorem lex_9_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3957), (Sat.Literal.pos 3956)] :=
  (lex_9_224_gate s).prop _ (List.Mem.head _)

theorem lex_9_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3957), (Sat.Literal.neg 224), (Sat.Literal.pos 7)] :=
  (lex_9_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3957), (Sat.Literal.pos 224), (Sat.Literal.neg 7)] :=
  (lex_9_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3956), (Sat.Literal.neg 224), (Sat.Literal.neg 7), (Sat.Literal.pos 3957)] :=
  (lex_9_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3956), (Sat.Literal.pos 224), (Sat.Literal.pos 7), (Sat.Literal.pos 3957)] :=
  (lex_9_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3957) = lexBefore s permutation9 223 := by
  exact (positive_lex_of_descriptor s 3957 permutation9 224 (by rfl)).trans ((lex_skipped s permutation9 223 224 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation9 223) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation9 223 by rw [image9_eq]; rfl))

theorem lex_9_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3958) (Sat.Literal.pos 3957) (Sat.Literal.pos 223) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation9 223 (assignment s)
    (Sat.Literal.pos 3958) (Sat.Literal.pos 3957) (Sat.Literal.pos 223) (Sat.Literal.pos 254) (positive_of_descriptor s 3958 (.lex permutation9 223) (by rfl)) (lex_9_223_prefix s) (positive_select s 223) (lex_9_223_image s)

theorem lex_9_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3957), (Sat.Literal.pos 223), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation9 223 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3957) (Sat.Literal.pos 223) (Sat.Literal.pos 254) (lex_9_223_prefix s) (positive_select s 223) (lex_9_223_image s)

theorem lex_9_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3958), (Sat.Literal.pos 3957)] :=
  (lex_9_223_gate s).prop _ (List.Mem.head _)

theorem lex_9_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3958), (Sat.Literal.neg 223), (Sat.Literal.pos 254)] :=
  (lex_9_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3958), (Sat.Literal.pos 223), (Sat.Literal.neg 254)] :=
  (lex_9_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3957), (Sat.Literal.neg 223), (Sat.Literal.neg 254), (Sat.Literal.pos 3958)] :=
  (lex_9_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3957), (Sat.Literal.pos 223), (Sat.Literal.pos 254), (Sat.Literal.pos 3958)] :=
  (lex_9_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3958) = lexBefore s permutation9 222 := by
  exact (positive_lex_of_descriptor s 3958 permutation9 223 (by rfl)).trans ((lex_skipped s permutation9 222 223 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation9 222) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation9 222 by rw [image9_eq]; rfl))

theorem lex_9_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3959) (Sat.Literal.pos 3958) (Sat.Literal.pos 222) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation9 222 (assignment s)
    (Sat.Literal.pos 3959) (Sat.Literal.pos 3958) (Sat.Literal.pos 222) (Sat.Literal.pos 246) (positive_of_descriptor s 3959 (.lex permutation9 222) (by rfl)) (lex_9_222_prefix s) (positive_select s 222) (lex_9_222_image s)

theorem lex_9_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3958), (Sat.Literal.pos 222), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation9 222 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3958) (Sat.Literal.pos 222) (Sat.Literal.pos 246) (lex_9_222_prefix s) (positive_select s 222) (lex_9_222_image s)

theorem lex_9_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3959), (Sat.Literal.pos 3958)] :=
  (lex_9_222_gate s).prop _ (List.Mem.head _)

theorem lex_9_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3959), (Sat.Literal.neg 222), (Sat.Literal.pos 246)] :=
  (lex_9_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3959), (Sat.Literal.pos 222), (Sat.Literal.neg 246)] :=
  (lex_9_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3958), (Sat.Literal.neg 222), (Sat.Literal.neg 246), (Sat.Literal.pos 3959)] :=
  (lex_9_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3958), (Sat.Literal.pos 222), (Sat.Literal.pos 246), (Sat.Literal.pos 3959)] :=
  (lex_9_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3959) = lexBefore s permutation9 221 := by
  exact (positive_lex_of_descriptor s 3959 permutation9 222 (by rfl)).trans ((lex_skipped s permutation9 221 222 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation9 221) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation9 221 by rw [image9_eq]; rfl))

theorem lex_9_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3960) (Sat.Literal.pos 3959) (Sat.Literal.pos 221) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation9 221 (assignment s)
    (Sat.Literal.pos 3960) (Sat.Literal.pos 3959) (Sat.Literal.pos 221) (Sat.Literal.pos 238) (positive_of_descriptor s 3960 (.lex permutation9 221) (by rfl)) (lex_9_221_prefix s) (positive_select s 221) (lex_9_221_image s)

theorem lex_9_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3959), (Sat.Literal.pos 221), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation9 221 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3959) (Sat.Literal.pos 221) (Sat.Literal.pos 238) (lex_9_221_prefix s) (positive_select s 221) (lex_9_221_image s)

theorem lex_9_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3960), (Sat.Literal.pos 3959)] :=
  (lex_9_221_gate s).prop _ (List.Mem.head _)

theorem lex_9_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3960), (Sat.Literal.neg 221), (Sat.Literal.pos 238)] :=
  (lex_9_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3960), (Sat.Literal.pos 221), (Sat.Literal.neg 238)] :=
  (lex_9_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3959), (Sat.Literal.neg 221), (Sat.Literal.neg 238), (Sat.Literal.pos 3960)] :=
  (lex_9_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3959), (Sat.Literal.pos 221), (Sat.Literal.pos 238), (Sat.Literal.pos 3960)] :=
  (lex_9_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3960) = lexBefore s permutation9 220 := by
  exact (positive_lex_of_descriptor s 3960 permutation9 221 (by rfl)).trans ((lex_skipped s permutation9 220 221 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation9 220) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation9 220 by rw [image9_eq]; rfl))

theorem lex_9_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3961) (Sat.Literal.pos 3960) (Sat.Literal.pos 220) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation9 220 (assignment s)
    (Sat.Literal.pos 3961) (Sat.Literal.pos 3960) (Sat.Literal.pos 220) (Sat.Literal.pos 230) (positive_of_descriptor s 3961 (.lex permutation9 220) (by rfl)) (lex_9_220_prefix s) (positive_select s 220) (lex_9_220_image s)

theorem lex_9_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3960), (Sat.Literal.pos 220), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation9 220 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3960) (Sat.Literal.pos 220) (Sat.Literal.pos 230) (lex_9_220_prefix s) (positive_select s 220) (lex_9_220_image s)

theorem lex_9_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3961), (Sat.Literal.pos 3960)] :=
  (lex_9_220_gate s).prop _ (List.Mem.head _)

theorem lex_9_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3961), (Sat.Literal.neg 220), (Sat.Literal.pos 230)] :=
  (lex_9_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3961), (Sat.Literal.pos 220), (Sat.Literal.neg 230)] :=
  (lex_9_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3960), (Sat.Literal.neg 220), (Sat.Literal.neg 230), (Sat.Literal.pos 3961)] :=
  (lex_9_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3960), (Sat.Literal.pos 220), (Sat.Literal.pos 230), (Sat.Literal.pos 3961)] :=
  (lex_9_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3961) = lexBefore s permutation9 219 := by
  exact (positive_lex_of_descriptor s 3961 permutation9 220 (by rfl)).trans ((lex_skipped s permutation9 219 220 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation9 219) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation9 219 by rw [image9_eq]; rfl))

theorem lex_9_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3962) (Sat.Literal.pos 3961) (Sat.Literal.pos 219) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation9 219 (assignment s)
    (Sat.Literal.pos 3962) (Sat.Literal.pos 3961) (Sat.Literal.pos 219) (Sat.Literal.pos 222) (positive_of_descriptor s 3962 (.lex permutation9 219) (by rfl)) (lex_9_219_prefix s) (positive_select s 219) (lex_9_219_image s)

theorem lex_9_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3961), (Sat.Literal.pos 219), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation9 219 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3961) (Sat.Literal.pos 219) (Sat.Literal.pos 222) (lex_9_219_prefix s) (positive_select s 219) (lex_9_219_image s)

theorem lex_9_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3962), (Sat.Literal.pos 3961)] :=
  (lex_9_219_gate s).prop _ (List.Mem.head _)

theorem lex_9_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3962), (Sat.Literal.neg 219), (Sat.Literal.pos 222)] :=
  (lex_9_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3962), (Sat.Literal.pos 219), (Sat.Literal.neg 222)] :=
  (lex_9_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3961), (Sat.Literal.neg 219), (Sat.Literal.neg 222), (Sat.Literal.pos 3962)] :=
  (lex_9_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3961), (Sat.Literal.pos 219), (Sat.Literal.pos 222), (Sat.Literal.pos 3962)] :=
  (lex_9_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3962) = lexBefore s permutation9 218 := by
  exact (positive_lex_of_descriptor s 3962 permutation9 219 (by rfl)).trans ((lex_skipped s permutation9 218 219 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation9 218) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation9 218 by rw [image9_eq]; rfl))

theorem lex_9_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3963) (Sat.Literal.pos 3962) (Sat.Literal.pos 218) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation9 218 (assignment s)
    (Sat.Literal.pos 3963) (Sat.Literal.pos 3962) (Sat.Literal.pos 218) (Sat.Literal.pos 214) (positive_of_descriptor s 3963 (.lex permutation9 218) (by rfl)) (lex_9_218_prefix s) (positive_select s 218) (lex_9_218_image s)

theorem lex_9_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3962), (Sat.Literal.pos 218), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation9 218 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3962) (Sat.Literal.pos 218) (Sat.Literal.pos 214) (lex_9_218_prefix s) (positive_select s 218) (lex_9_218_image s)

theorem lex_9_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3963), (Sat.Literal.pos 3962)] :=
  (lex_9_218_gate s).prop _ (List.Mem.head _)

theorem lex_9_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3963), (Sat.Literal.neg 218), (Sat.Literal.pos 214)] :=
  (lex_9_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3963), (Sat.Literal.pos 218), (Sat.Literal.neg 214)] :=
  (lex_9_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3962), (Sat.Literal.neg 218), (Sat.Literal.neg 214), (Sat.Literal.pos 3963)] :=
  (lex_9_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3962), (Sat.Literal.pos 218), (Sat.Literal.pos 214), (Sat.Literal.pos 3963)] :=
  (lex_9_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3963) = lexBefore s permutation9 217 := by
  exact (positive_lex_of_descriptor s 3963 permutation9 218 (by rfl)).trans ((lex_skipped s permutation9 217 218 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation9 217) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation9 217 by rw [image9_eq]; rfl))

theorem lex_9_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3964) (Sat.Literal.pos 3963) (Sat.Literal.pos 217) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation9 217 (assignment s)
    (Sat.Literal.pos 3964) (Sat.Literal.pos 3963) (Sat.Literal.pos 217) (Sat.Literal.pos 206) (positive_of_descriptor s 3964 (.lex permutation9 217) (by rfl)) (lex_9_217_prefix s) (positive_select s 217) (lex_9_217_image s)

theorem lex_9_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3963), (Sat.Literal.pos 217), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation9 217 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3963) (Sat.Literal.pos 217) (Sat.Literal.pos 206) (lex_9_217_prefix s) (positive_select s 217) (lex_9_217_image s)

theorem lex_9_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3964), (Sat.Literal.pos 3963)] :=
  (lex_9_217_gate s).prop _ (List.Mem.head _)

theorem lex_9_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3964), (Sat.Literal.neg 217), (Sat.Literal.pos 206)] :=
  (lex_9_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3964), (Sat.Literal.pos 217), (Sat.Literal.neg 206)] :=
  (lex_9_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3963), (Sat.Literal.neg 217), (Sat.Literal.neg 206), (Sat.Literal.pos 3964)] :=
  (lex_9_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3963), (Sat.Literal.pos 217), (Sat.Literal.pos 206), (Sat.Literal.pos 3964)] :=
  (lex_9_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3964) = lexBefore s permutation9 216 := by
  exact (positive_lex_of_descriptor s 3964 permutation9 217 (by rfl)).trans ((lex_skipped s permutation9 216 217 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation9 216) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation9 216 by rw [image9_eq]; rfl))

theorem lex_9_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3965) (Sat.Literal.pos 3964) (Sat.Literal.pos 216) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation9 216 (assignment s)
    (Sat.Literal.pos 3965) (Sat.Literal.pos 3964) (Sat.Literal.pos 216) (Sat.Literal.pos 198) (positive_of_descriptor s 3965 (.lex permutation9 216) (by rfl)) (lex_9_216_prefix s) (positive_select s 216) (lex_9_216_image s)

theorem lex_9_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3964), (Sat.Literal.pos 216), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation9 216 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3964) (Sat.Literal.pos 216) (Sat.Literal.pos 198) (lex_9_216_prefix s) (positive_select s 216) (lex_9_216_image s)

theorem lex_9_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3965), (Sat.Literal.pos 3964)] :=
  (lex_9_216_gate s).prop _ (List.Mem.head _)

theorem lex_9_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3965), (Sat.Literal.neg 216), (Sat.Literal.pos 198)] :=
  (lex_9_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3965), (Sat.Literal.pos 216), (Sat.Literal.neg 198)] :=
  (lex_9_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3964), (Sat.Literal.neg 216), (Sat.Literal.neg 198), (Sat.Literal.pos 3965)] :=
  (lex_9_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3964), (Sat.Literal.pos 216), (Sat.Literal.pos 198), (Sat.Literal.pos 3965)] :=
  (lex_9_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3965) = lexBefore s permutation9 215 := by
  exact (positive_lex_of_descriptor s 3965 permutation9 216 (by rfl)).trans ((lex_skipped s permutation9 215 216 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation9 215) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation9 215 by rw [image9_eq]; rfl))

theorem lex_9_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3966) (Sat.Literal.pos 3965) (Sat.Literal.pos 215) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation9 215 (assignment s)
    (Sat.Literal.pos 3966) (Sat.Literal.pos 3965) (Sat.Literal.pos 215) (Sat.Literal.pos 190) (positive_of_descriptor s 3966 (.lex permutation9 215) (by rfl)) (lex_9_215_prefix s) (positive_select s 215) (lex_9_215_image s)

theorem lex_9_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3965), (Sat.Literal.pos 215), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation9 215 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3965) (Sat.Literal.pos 215) (Sat.Literal.pos 190) (lex_9_215_prefix s) (positive_select s 215) (lex_9_215_image s)

theorem lex_9_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3966), (Sat.Literal.pos 3965)] :=
  (lex_9_215_gate s).prop _ (List.Mem.head _)

theorem lex_9_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3966), (Sat.Literal.neg 215), (Sat.Literal.pos 190)] :=
  (lex_9_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3966), (Sat.Literal.pos 215), (Sat.Literal.neg 190)] :=
  (lex_9_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3965), (Sat.Literal.neg 215), (Sat.Literal.neg 190), (Sat.Literal.pos 3966)] :=
  (lex_9_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3965), (Sat.Literal.pos 215), (Sat.Literal.pos 190), (Sat.Literal.pos 3966)] :=
  (lex_9_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3966) = lexBefore s permutation9 214 := by
  exact (positive_lex_of_descriptor s 3966 permutation9 215 (by rfl)).trans ((lex_skipped s permutation9 214 215 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation9 214) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation9 214 by rw [image9_eq]; rfl))

theorem lex_9_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3967) (Sat.Literal.pos 3966) (Sat.Literal.pos 214) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation9 214 (assignment s)
    (Sat.Literal.pos 3967) (Sat.Literal.pos 3966) (Sat.Literal.pos 214) (Sat.Literal.pos 182) (positive_of_descriptor s 3967 (.lex permutation9 214) (by rfl)) (lex_9_214_prefix s) (positive_select s 214) (lex_9_214_image s)

theorem lex_9_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3966), (Sat.Literal.pos 214), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation9 214 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3966) (Sat.Literal.pos 214) (Sat.Literal.pos 182) (lex_9_214_prefix s) (positive_select s 214) (lex_9_214_image s)

theorem lex_9_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3967), (Sat.Literal.pos 3966)] :=
  (lex_9_214_gate s).prop _ (List.Mem.head _)

theorem lex_9_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3967), (Sat.Literal.neg 214), (Sat.Literal.pos 182)] :=
  (lex_9_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3967), (Sat.Literal.pos 214), (Sat.Literal.neg 182)] :=
  (lex_9_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3966), (Sat.Literal.neg 214), (Sat.Literal.neg 182), (Sat.Literal.pos 3967)] :=
  (lex_9_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3966), (Sat.Literal.pos 214), (Sat.Literal.pos 182), (Sat.Literal.pos 3967)] :=
  (lex_9_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3967) = lexBefore s permutation9 213 := by
  exact (positive_lex_of_descriptor s 3967 permutation9 214 (by rfl)).trans ((lex_skipped s permutation9 213 214 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation9 213) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation9 213 by rw [image9_eq]; rfl))

theorem lex_9_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3968) (Sat.Literal.pos 3967) (Sat.Literal.pos 213) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation9 213 (assignment s)
    (Sat.Literal.pos 3968) (Sat.Literal.pos 3967) (Sat.Literal.pos 213) (Sat.Literal.pos 174) (positive_of_descriptor s 3968 (.lex permutation9 213) (by rfl)) (lex_9_213_prefix s) (positive_select s 213) (lex_9_213_image s)

theorem lex_9_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3967), (Sat.Literal.pos 213), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation9 213 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3967) (Sat.Literal.pos 213) (Sat.Literal.pos 174) (lex_9_213_prefix s) (positive_select s 213) (lex_9_213_image s)

theorem lex_9_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3968), (Sat.Literal.pos 3967)] :=
  (lex_9_213_gate s).prop _ (List.Mem.head _)

theorem lex_9_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3968), (Sat.Literal.neg 213), (Sat.Literal.pos 174)] :=
  (lex_9_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3968), (Sat.Literal.pos 213), (Sat.Literal.neg 174)] :=
  (lex_9_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3967), (Sat.Literal.neg 213), (Sat.Literal.neg 174), (Sat.Literal.pos 3968)] :=
  (lex_9_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3967), (Sat.Literal.pos 213), (Sat.Literal.pos 174), (Sat.Literal.pos 3968)] :=
  (lex_9_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3968) = lexBefore s permutation9 212 := by
  exact (positive_lex_of_descriptor s 3968 permutation9 213 (by rfl)).trans ((lex_skipped s permutation9 212 213 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation9 212) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation9 212 by rw [image9_eq]; rfl))

theorem lex_9_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3969) (Sat.Literal.pos 3968) (Sat.Literal.pos 212) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation9 212 (assignment s)
    (Sat.Literal.pos 3969) (Sat.Literal.pos 3968) (Sat.Literal.pos 212) (Sat.Literal.pos 166) (positive_of_descriptor s 3969 (.lex permutation9 212) (by rfl)) (lex_9_212_prefix s) (positive_select s 212) (lex_9_212_image s)

theorem lex_9_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3968), (Sat.Literal.pos 212), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation9 212 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3968) (Sat.Literal.pos 212) (Sat.Literal.pos 166) (lex_9_212_prefix s) (positive_select s 212) (lex_9_212_image s)

theorem lex_9_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3969), (Sat.Literal.pos 3968)] :=
  (lex_9_212_gate s).prop _ (List.Mem.head _)

theorem lex_9_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3969), (Sat.Literal.neg 212), (Sat.Literal.pos 166)] :=
  (lex_9_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3969), (Sat.Literal.pos 212), (Sat.Literal.neg 166)] :=
  (lex_9_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3968), (Sat.Literal.neg 212), (Sat.Literal.neg 166), (Sat.Literal.pos 3969)] :=
  (lex_9_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3968), (Sat.Literal.pos 212), (Sat.Literal.pos 166), (Sat.Literal.pos 3969)] :=
  (lex_9_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3969) = lexBefore s permutation9 211 := by
  exact (positive_lex_of_descriptor s 3969 permutation9 212 (by rfl)).trans ((lex_skipped s permutation9 211 212 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation9 211) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation9 211 by rw [image9_eq]; rfl))

theorem lex_9_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3970) (Sat.Literal.pos 3969) (Sat.Literal.pos 211) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation9 211 (assignment s)
    (Sat.Literal.pos 3970) (Sat.Literal.pos 3969) (Sat.Literal.pos 211) (Sat.Literal.pos 158) (positive_of_descriptor s 3970 (.lex permutation9 211) (by rfl)) (lex_9_211_prefix s) (positive_select s 211) (lex_9_211_image s)

theorem lex_9_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3969), (Sat.Literal.pos 211), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation9 211 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3969) (Sat.Literal.pos 211) (Sat.Literal.pos 158) (lex_9_211_prefix s) (positive_select s 211) (lex_9_211_image s)

theorem lex_9_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3970), (Sat.Literal.pos 3969)] :=
  (lex_9_211_gate s).prop _ (List.Mem.head _)

theorem lex_9_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3970), (Sat.Literal.neg 211), (Sat.Literal.pos 158)] :=
  (lex_9_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3970), (Sat.Literal.pos 211), (Sat.Literal.neg 158)] :=
  (lex_9_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3969), (Sat.Literal.neg 211), (Sat.Literal.neg 158), (Sat.Literal.pos 3970)] :=
  (lex_9_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3969), (Sat.Literal.pos 211), (Sat.Literal.pos 158), (Sat.Literal.pos 3970)] :=
  (lex_9_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3970) = lexBefore s permutation9 210 := by
  exact (positive_lex_of_descriptor s 3970 permutation9 211 (by rfl)).trans ((lex_skipped s permutation9 210 211 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation9 210) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation9 210 by rw [image9_eq]; rfl))

theorem lex_9_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3971) (Sat.Literal.pos 3970) (Sat.Literal.pos 210) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation9 210 (assignment s)
    (Sat.Literal.pos 3971) (Sat.Literal.pos 3970) (Sat.Literal.pos 210) (Sat.Literal.pos 150) (positive_of_descriptor s 3971 (.lex permutation9 210) (by rfl)) (lex_9_210_prefix s) (positive_select s 210) (lex_9_210_image s)

theorem lex_9_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3970), (Sat.Literal.pos 210), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation9 210 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3970) (Sat.Literal.pos 210) (Sat.Literal.pos 150) (lex_9_210_prefix s) (positive_select s 210) (lex_9_210_image s)

theorem lex_9_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3971), (Sat.Literal.pos 3970)] :=
  (lex_9_210_gate s).prop _ (List.Mem.head _)

theorem lex_9_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3971), (Sat.Literal.neg 210), (Sat.Literal.pos 150)] :=
  (lex_9_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3971), (Sat.Literal.pos 210), (Sat.Literal.neg 150)] :=
  (lex_9_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3970), (Sat.Literal.neg 210), (Sat.Literal.neg 150), (Sat.Literal.pos 3971)] :=
  (lex_9_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3970), (Sat.Literal.pos 210), (Sat.Literal.pos 150), (Sat.Literal.pos 3971)] :=
  (lex_9_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3971) = lexBefore s permutation9 209 := by
  exact (positive_lex_of_descriptor s 3971 permutation9 210 (by rfl)).trans ((lex_skipped s permutation9 209 210 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation9 209) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation9 209 by rw [image9_eq]; rfl))

theorem lex_9_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3972) (Sat.Literal.pos 3971) (Sat.Literal.pos 209) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation9 209 (assignment s)
    (Sat.Literal.pos 3972) (Sat.Literal.pos 3971) (Sat.Literal.pos 209) (Sat.Literal.pos 142) (positive_of_descriptor s 3972 (.lex permutation9 209) (by rfl)) (lex_9_209_prefix s) (positive_select s 209) (lex_9_209_image s)

theorem lex_9_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3971), (Sat.Literal.pos 209), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation9 209 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3971) (Sat.Literal.pos 209) (Sat.Literal.pos 142) (lex_9_209_prefix s) (positive_select s 209) (lex_9_209_image s)

theorem lex_9_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3972), (Sat.Literal.pos 3971)] :=
  (lex_9_209_gate s).prop _ (List.Mem.head _)

theorem lex_9_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3972), (Sat.Literal.neg 209), (Sat.Literal.pos 142)] :=
  (lex_9_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3972), (Sat.Literal.pos 209), (Sat.Literal.neg 142)] :=
  (lex_9_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3971), (Sat.Literal.neg 209), (Sat.Literal.neg 142), (Sat.Literal.pos 3972)] :=
  (lex_9_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3971), (Sat.Literal.pos 209), (Sat.Literal.pos 142), (Sat.Literal.pos 3972)] :=
  (lex_9_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3972) = lexBefore s permutation9 208 := by
  exact (positive_lex_of_descriptor s 3972 permutation9 209 (by rfl)).trans ((lex_skipped s permutation9 208 209 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation9 208) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation9 208 by rw [image9_eq]; rfl))

theorem lex_9_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3973) (Sat.Literal.pos 3972) (Sat.Literal.pos 208) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation9 208 (assignment s)
    (Sat.Literal.pos 3973) (Sat.Literal.pos 3972) (Sat.Literal.pos 208) (Sat.Literal.pos 134) (positive_of_descriptor s 3973 (.lex permutation9 208) (by rfl)) (lex_9_208_prefix s) (positive_select s 208) (lex_9_208_image s)

theorem lex_9_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3972), (Sat.Literal.pos 208), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation9 208 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3972) (Sat.Literal.pos 208) (Sat.Literal.pos 134) (lex_9_208_prefix s) (positive_select s 208) (lex_9_208_image s)

theorem lex_9_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3973), (Sat.Literal.pos 3972)] :=
  (lex_9_208_gate s).prop _ (List.Mem.head _)

theorem lex_9_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3973), (Sat.Literal.neg 208), (Sat.Literal.pos 134)] :=
  (lex_9_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3973), (Sat.Literal.pos 208), (Sat.Literal.neg 134)] :=
  (lex_9_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3972), (Sat.Literal.neg 208), (Sat.Literal.neg 134), (Sat.Literal.pos 3973)] :=
  (lex_9_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3972), (Sat.Literal.pos 208), (Sat.Literal.pos 134), (Sat.Literal.pos 3973)] :=
  (lex_9_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3973) = lexBefore s permutation9 207 := by
  exact (positive_lex_of_descriptor s 3973 permutation9 208 (by rfl)).trans ((lex_skipped s permutation9 207 208 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation9 207) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation9 207 by rw [image9_eq]; rfl))

theorem lex_9_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3974) (Sat.Literal.pos 3973) (Sat.Literal.pos 207) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation9 207 (assignment s)
    (Sat.Literal.pos 3974) (Sat.Literal.pos 3973) (Sat.Literal.pos 207) (Sat.Literal.pos 126) (positive_of_descriptor s 3974 (.lex permutation9 207) (by rfl)) (lex_9_207_prefix s) (positive_select s 207) (lex_9_207_image s)

theorem lex_9_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3973), (Sat.Literal.pos 207), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation9 207 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3973) (Sat.Literal.pos 207) (Sat.Literal.pos 126) (lex_9_207_prefix s) (positive_select s 207) (lex_9_207_image s)

theorem lex_9_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3974), (Sat.Literal.pos 3973)] :=
  (lex_9_207_gate s).prop _ (List.Mem.head _)

theorem lex_9_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3974), (Sat.Literal.neg 207), (Sat.Literal.pos 126)] :=
  (lex_9_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3974), (Sat.Literal.pos 207), (Sat.Literal.neg 126)] :=
  (lex_9_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3973), (Sat.Literal.neg 207), (Sat.Literal.neg 126), (Sat.Literal.pos 3974)] :=
  (lex_9_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3973), (Sat.Literal.pos 207), (Sat.Literal.pos 126), (Sat.Literal.pos 3974)] :=
  (lex_9_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3974) = lexBefore s permutation9 206 := by
  exact (positive_lex_of_descriptor s 3974 permutation9 207 (by rfl)).trans ((lex_skipped s permutation9 206 207 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation9 206) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation9 206 by rw [image9_eq]; rfl))

theorem lex_9_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3975) (Sat.Literal.pos 3974) (Sat.Literal.pos 206) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation9 206 (assignment s)
    (Sat.Literal.pos 3975) (Sat.Literal.pos 3974) (Sat.Literal.pos 206) (Sat.Literal.pos 118) (positive_of_descriptor s 3975 (.lex permutation9 206) (by rfl)) (lex_9_206_prefix s) (positive_select s 206) (lex_9_206_image s)

theorem lex_9_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3974), (Sat.Literal.pos 206), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation9 206 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3974) (Sat.Literal.pos 206) (Sat.Literal.pos 118) (lex_9_206_prefix s) (positive_select s 206) (lex_9_206_image s)

theorem lex_9_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3975), (Sat.Literal.pos 3974)] :=
  (lex_9_206_gate s).prop _ (List.Mem.head _)

theorem lex_9_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3975), (Sat.Literal.neg 206), (Sat.Literal.pos 118)] :=
  (lex_9_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3975), (Sat.Literal.pos 206), (Sat.Literal.neg 118)] :=
  (lex_9_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3974), (Sat.Literal.neg 206), (Sat.Literal.neg 118), (Sat.Literal.pos 3975)] :=
  (lex_9_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3974), (Sat.Literal.pos 206), (Sat.Literal.pos 118), (Sat.Literal.pos 3975)] :=
  (lex_9_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3975) = lexBefore s permutation9 205 := by
  exact (positive_lex_of_descriptor s 3975 permutation9 206 (by rfl)).trans ((lex_skipped s permutation9 205 206 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation9 205) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation9 205 by rw [image9_eq]; rfl))

theorem lex_9_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3976) (Sat.Literal.pos 3975) (Sat.Literal.pos 205) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation9 205 (assignment s)
    (Sat.Literal.pos 3976) (Sat.Literal.pos 3975) (Sat.Literal.pos 205) (Sat.Literal.pos 110) (positive_of_descriptor s 3976 (.lex permutation9 205) (by rfl)) (lex_9_205_prefix s) (positive_select s 205) (lex_9_205_image s)

theorem lex_9_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3975), (Sat.Literal.pos 205), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation9 205 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3975) (Sat.Literal.pos 205) (Sat.Literal.pos 110) (lex_9_205_prefix s) (positive_select s 205) (lex_9_205_image s)

theorem lex_9_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3976), (Sat.Literal.pos 3975)] :=
  (lex_9_205_gate s).prop _ (List.Mem.head _)

theorem lex_9_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3976), (Sat.Literal.neg 205), (Sat.Literal.pos 110)] :=
  (lex_9_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3976), (Sat.Literal.pos 205), (Sat.Literal.neg 110)] :=
  (lex_9_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3975), (Sat.Literal.neg 205), (Sat.Literal.neg 110), (Sat.Literal.pos 3976)] :=
  (lex_9_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3975), (Sat.Literal.pos 205), (Sat.Literal.pos 110), (Sat.Literal.pos 3976)] :=
  (lex_9_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3976) = lexBefore s permutation9 204 := by
  exact (positive_lex_of_descriptor s 3976 permutation9 205 (by rfl)).trans ((lex_skipped s permutation9 204 205 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation9 204) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation9 204 by rw [image9_eq]; rfl))

theorem lex_9_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3977) (Sat.Literal.pos 3976) (Sat.Literal.pos 204) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation9 204 (assignment s)
    (Sat.Literal.pos 3977) (Sat.Literal.pos 3976) (Sat.Literal.pos 204) (Sat.Literal.pos 102) (positive_of_descriptor s 3977 (.lex permutation9 204) (by rfl)) (lex_9_204_prefix s) (positive_select s 204) (lex_9_204_image s)

theorem lex_9_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3976), (Sat.Literal.pos 204), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation9 204 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3976) (Sat.Literal.pos 204) (Sat.Literal.pos 102) (lex_9_204_prefix s) (positive_select s 204) (lex_9_204_image s)

theorem lex_9_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3977), (Sat.Literal.pos 3976)] :=
  (lex_9_204_gate s).prop _ (List.Mem.head _)

theorem lex_9_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3977), (Sat.Literal.neg 204), (Sat.Literal.pos 102)] :=
  (lex_9_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3977), (Sat.Literal.pos 204), (Sat.Literal.neg 102)] :=
  (lex_9_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3976), (Sat.Literal.neg 204), (Sat.Literal.neg 102), (Sat.Literal.pos 3977)] :=
  (lex_9_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3976), (Sat.Literal.pos 204), (Sat.Literal.pos 102), (Sat.Literal.pos 3977)] :=
  (lex_9_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3977) = lexBefore s permutation9 203 := by
  exact (positive_lex_of_descriptor s 3977 permutation9 204 (by rfl)).trans ((lex_skipped s permutation9 203 204 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation9 203) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation9 203 by rw [image9_eq]; rfl))

theorem lex_9_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3978) (Sat.Literal.pos 3977) (Sat.Literal.pos 203) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation9 203 (assignment s)
    (Sat.Literal.pos 3978) (Sat.Literal.pos 3977) (Sat.Literal.pos 203) (Sat.Literal.pos 94) (positive_of_descriptor s 3978 (.lex permutation9 203) (by rfl)) (lex_9_203_prefix s) (positive_select s 203) (lex_9_203_image s)

theorem lex_9_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3977), (Sat.Literal.pos 203), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation9 203 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3977) (Sat.Literal.pos 203) (Sat.Literal.pos 94) (lex_9_203_prefix s) (positive_select s 203) (lex_9_203_image s)

theorem lex_9_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3978), (Sat.Literal.pos 3977)] :=
  (lex_9_203_gate s).prop _ (List.Mem.head _)

theorem lex_9_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3978), (Sat.Literal.neg 203), (Sat.Literal.pos 94)] :=
  (lex_9_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3978), (Sat.Literal.pos 203), (Sat.Literal.neg 94)] :=
  (lex_9_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3977), (Sat.Literal.neg 203), (Sat.Literal.neg 94), (Sat.Literal.pos 3978)] :=
  (lex_9_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3977), (Sat.Literal.pos 203), (Sat.Literal.pos 94), (Sat.Literal.pos 3978)] :=
  (lex_9_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3978) = lexBefore s permutation9 202 := by
  exact (positive_lex_of_descriptor s 3978 permutation9 203 (by rfl)).trans ((lex_skipped s permutation9 202 203 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation9 202) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation9 202 by rw [image9_eq]; rfl))

theorem lex_9_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3979) (Sat.Literal.pos 3978) (Sat.Literal.pos 202) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation9 202 (assignment s)
    (Sat.Literal.pos 3979) (Sat.Literal.pos 3978) (Sat.Literal.pos 202) (Sat.Literal.pos 86) (positive_of_descriptor s 3979 (.lex permutation9 202) (by rfl)) (lex_9_202_prefix s) (positive_select s 202) (lex_9_202_image s)

theorem lex_9_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3978), (Sat.Literal.pos 202), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation9 202 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3978) (Sat.Literal.pos 202) (Sat.Literal.pos 86) (lex_9_202_prefix s) (positive_select s 202) (lex_9_202_image s)

theorem lex_9_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3979), (Sat.Literal.pos 3978)] :=
  (lex_9_202_gate s).prop _ (List.Mem.head _)

theorem lex_9_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3979), (Sat.Literal.neg 202), (Sat.Literal.pos 86)] :=
  (lex_9_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3979), (Sat.Literal.pos 202), (Sat.Literal.neg 86)] :=
  (lex_9_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3978), (Sat.Literal.neg 202), (Sat.Literal.neg 86), (Sat.Literal.pos 3979)] :=
  (lex_9_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3978), (Sat.Literal.pos 202), (Sat.Literal.pos 86), (Sat.Literal.pos 3979)] :=
  (lex_9_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3979) = lexBefore s permutation9 201 := by
  exact (positive_lex_of_descriptor s 3979 permutation9 202 (by rfl)).trans ((lex_skipped s permutation9 201 202 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation9 201) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation9 201 by rw [image9_eq]; rfl))

theorem lex_9_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3980) (Sat.Literal.pos 3979) (Sat.Literal.pos 201) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation9 201 (assignment s)
    (Sat.Literal.pos 3980) (Sat.Literal.pos 3979) (Sat.Literal.pos 201) (Sat.Literal.pos 78) (positive_of_descriptor s 3980 (.lex permutation9 201) (by rfl)) (lex_9_201_prefix s) (positive_select s 201) (lex_9_201_image s)

theorem lex_9_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3979), (Sat.Literal.pos 201), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation9 201 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3979) (Sat.Literal.pos 201) (Sat.Literal.pos 78) (lex_9_201_prefix s) (positive_select s 201) (lex_9_201_image s)

theorem lex_9_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3980), (Sat.Literal.pos 3979)] :=
  (lex_9_201_gate s).prop _ (List.Mem.head _)

theorem lex_9_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3980), (Sat.Literal.neg 201), (Sat.Literal.pos 78)] :=
  (lex_9_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3980), (Sat.Literal.pos 201), (Sat.Literal.neg 78)] :=
  (lex_9_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3979), (Sat.Literal.neg 201), (Sat.Literal.neg 78), (Sat.Literal.pos 3980)] :=
  (lex_9_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3979), (Sat.Literal.pos 201), (Sat.Literal.pos 78), (Sat.Literal.pos 3980)] :=
  (lex_9_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3980) = lexBefore s permutation9 200 := by
  exact (positive_lex_of_descriptor s 3980 permutation9 201 (by rfl)).trans ((lex_skipped s permutation9 200 201 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation9 200) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation9 200 by rw [image9_eq]; rfl))

theorem lex_9_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3981) (Sat.Literal.pos 3980) (Sat.Literal.pos 200) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation9 200 (assignment s)
    (Sat.Literal.pos 3981) (Sat.Literal.pos 3980) (Sat.Literal.pos 200) (Sat.Literal.pos 70) (positive_of_descriptor s 3981 (.lex permutation9 200) (by rfl)) (lex_9_200_prefix s) (positive_select s 200) (lex_9_200_image s)

theorem lex_9_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3980), (Sat.Literal.pos 200), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation9 200 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3980) (Sat.Literal.pos 200) (Sat.Literal.pos 70) (lex_9_200_prefix s) (positive_select s 200) (lex_9_200_image s)

theorem lex_9_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3981), (Sat.Literal.pos 3980)] :=
  (lex_9_200_gate s).prop _ (List.Mem.head _)

theorem lex_9_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3981), (Sat.Literal.neg 200), (Sat.Literal.pos 70)] :=
  (lex_9_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3981), (Sat.Literal.pos 200), (Sat.Literal.neg 70)] :=
  (lex_9_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3980), (Sat.Literal.neg 200), (Sat.Literal.neg 70), (Sat.Literal.pos 3981)] :=
  (lex_9_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3980), (Sat.Literal.pos 200), (Sat.Literal.pos 70), (Sat.Literal.pos 3981)] :=
  (lex_9_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3981) = lexBefore s permutation9 199 := by
  exact (positive_lex_of_descriptor s 3981 permutation9 200 (by rfl)).trans ((lex_skipped s permutation9 199 200 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation9 199) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation9 199 by rw [image9_eq]; rfl))

theorem lex_9_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3982) (Sat.Literal.pos 3981) (Sat.Literal.pos 199) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation9 199 (assignment s)
    (Sat.Literal.pos 3982) (Sat.Literal.pos 3981) (Sat.Literal.pos 199) (Sat.Literal.pos 62) (positive_of_descriptor s 3982 (.lex permutation9 199) (by rfl)) (lex_9_199_prefix s) (positive_select s 199) (lex_9_199_image s)

theorem lex_9_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3981), (Sat.Literal.pos 199), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation9 199 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3981) (Sat.Literal.pos 199) (Sat.Literal.pos 62) (lex_9_199_prefix s) (positive_select s 199) (lex_9_199_image s)

theorem lex_9_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3982), (Sat.Literal.pos 3981)] :=
  (lex_9_199_gate s).prop _ (List.Mem.head _)

theorem lex_9_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3982), (Sat.Literal.neg 199), (Sat.Literal.pos 62)] :=
  (lex_9_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3982), (Sat.Literal.pos 199), (Sat.Literal.neg 62)] :=
  (lex_9_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3981), (Sat.Literal.neg 199), (Sat.Literal.neg 62), (Sat.Literal.pos 3982)] :=
  (lex_9_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3981), (Sat.Literal.pos 199), (Sat.Literal.pos 62), (Sat.Literal.pos 3982)] :=
  (lex_9_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3982) = lexBefore s permutation9 198 := by
  exact (positive_lex_of_descriptor s 3982 permutation9 199 (by rfl)).trans ((lex_skipped s permutation9 198 199 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation9 198) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation9 198 by rw [image9_eq]; rfl))

theorem lex_9_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3983) (Sat.Literal.pos 3982) (Sat.Literal.pos 198) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation9 198 (assignment s)
    (Sat.Literal.pos 3983) (Sat.Literal.pos 3982) (Sat.Literal.pos 198) (Sat.Literal.pos 54) (positive_of_descriptor s 3983 (.lex permutation9 198) (by rfl)) (lex_9_198_prefix s) (positive_select s 198) (lex_9_198_image s)

theorem lex_9_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3982), (Sat.Literal.pos 198), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation9 198 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3982) (Sat.Literal.pos 198) (Sat.Literal.pos 54) (lex_9_198_prefix s) (positive_select s 198) (lex_9_198_image s)

theorem lex_9_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3983), (Sat.Literal.pos 3982)] :=
  (lex_9_198_gate s).prop _ (List.Mem.head _)

theorem lex_9_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3983), (Sat.Literal.neg 198), (Sat.Literal.pos 54)] :=
  (lex_9_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3983), (Sat.Literal.pos 198), (Sat.Literal.neg 54)] :=
  (lex_9_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3982), (Sat.Literal.neg 198), (Sat.Literal.neg 54), (Sat.Literal.pos 3983)] :=
  (lex_9_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3982), (Sat.Literal.pos 198), (Sat.Literal.pos 54), (Sat.Literal.pos 3983)] :=
  (lex_9_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3983) = lexBefore s permutation9 197 := by
  exact (positive_lex_of_descriptor s 3983 permutation9 198 (by rfl)).trans ((lex_skipped s permutation9 197 198 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 46) = s (permuteMask permutation9 197) := by
  exact (positive_select s 46).trans (congrArg s (show (46 : Fin 256) = permuteMask permutation9 197 by rw [image9_eq]; rfl))

theorem lex_9_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3984) (Sat.Literal.pos 3983) (Sat.Literal.pos 197) (Sat.Literal.pos 46)) := by
  exact equality_gate s permutation9 197 (assignment s)
    (Sat.Literal.pos 3984) (Sat.Literal.pos 3983) (Sat.Literal.pos 197) (Sat.Literal.pos 46) (positive_of_descriptor s 3984 (.lex permutation9 197) (by rfl)) (lex_9_197_prefix s) (positive_select s 197) (lex_9_197_image s)

theorem lex_9_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3983), (Sat.Literal.pos 197), (Sat.Literal.neg 46)] := by
  exact comparison_gate s permutation9 197 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3983) (Sat.Literal.pos 197) (Sat.Literal.pos 46) (lex_9_197_prefix s) (positive_select s 197) (lex_9_197_image s)

theorem lex_9_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3984), (Sat.Literal.pos 3983)] :=
  (lex_9_197_gate s).prop _ (List.Mem.head _)

theorem lex_9_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3984), (Sat.Literal.neg 197), (Sat.Literal.pos 46)] :=
  (lex_9_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3984), (Sat.Literal.pos 197), (Sat.Literal.neg 46)] :=
  (lex_9_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3983), (Sat.Literal.neg 197), (Sat.Literal.neg 46), (Sat.Literal.pos 3984)] :=
  (lex_9_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3983), (Sat.Literal.pos 197), (Sat.Literal.pos 46), (Sat.Literal.pos 3984)] :=
  (lex_9_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3984) = lexBefore s permutation9 196 := by
  exact (positive_lex_of_descriptor s 3984 permutation9 197 (by rfl)).trans ((lex_skipped s permutation9 196 197 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 38) = s (permuteMask permutation9 196) := by
  exact (positive_select s 38).trans (congrArg s (show (38 : Fin 256) = permuteMask permutation9 196 by rw [image9_eq]; rfl))

theorem lex_9_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3985) (Sat.Literal.pos 3984) (Sat.Literal.pos 196) (Sat.Literal.pos 38)) := by
  exact equality_gate s permutation9 196 (assignment s)
    (Sat.Literal.pos 3985) (Sat.Literal.pos 3984) (Sat.Literal.pos 196) (Sat.Literal.pos 38) (positive_of_descriptor s 3985 (.lex permutation9 196) (by rfl)) (lex_9_196_prefix s) (positive_select s 196) (lex_9_196_image s)

theorem lex_9_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3984), (Sat.Literal.pos 196), (Sat.Literal.neg 38)] := by
  exact comparison_gate s permutation9 196 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3984) (Sat.Literal.pos 196) (Sat.Literal.pos 38) (lex_9_196_prefix s) (positive_select s 196) (lex_9_196_image s)

theorem lex_9_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3985), (Sat.Literal.pos 3984)] :=
  (lex_9_196_gate s).prop _ (List.Mem.head _)

theorem lex_9_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3985), (Sat.Literal.neg 196), (Sat.Literal.pos 38)] :=
  (lex_9_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3985), (Sat.Literal.pos 196), (Sat.Literal.neg 38)] :=
  (lex_9_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3984), (Sat.Literal.neg 196), (Sat.Literal.neg 38), (Sat.Literal.pos 3985)] :=
  (lex_9_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3984), (Sat.Literal.pos 196), (Sat.Literal.pos 38), (Sat.Literal.pos 3985)] :=
  (lex_9_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3985) = lexBefore s permutation9 195 := by
  exact (positive_lex_of_descriptor s 3985 permutation9 196 (by rfl)).trans ((lex_skipped s permutation9 195 196 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation9 195) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation9 195 by rw [image9_eq]; rfl))

theorem lex_9_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3986) (Sat.Literal.pos 3985) (Sat.Literal.pos 195) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation9 195 (assignment s)
    (Sat.Literal.pos 3986) (Sat.Literal.pos 3985) (Sat.Literal.pos 195) (Sat.Literal.pos 30) (positive_of_descriptor s 3986 (.lex permutation9 195) (by rfl)) (lex_9_195_prefix s) (positive_select s 195) (lex_9_195_image s)

theorem lex_9_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3985), (Sat.Literal.pos 195), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation9 195 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3985) (Sat.Literal.pos 195) (Sat.Literal.pos 30) (lex_9_195_prefix s) (positive_select s 195) (lex_9_195_image s)

theorem lex_9_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3986), (Sat.Literal.pos 3985)] :=
  (lex_9_195_gate s).prop _ (List.Mem.head _)

theorem lex_9_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3986), (Sat.Literal.neg 195), (Sat.Literal.pos 30)] :=
  (lex_9_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3986), (Sat.Literal.pos 195), (Sat.Literal.neg 30)] :=
  (lex_9_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3985), (Sat.Literal.neg 195), (Sat.Literal.neg 30), (Sat.Literal.pos 3986)] :=
  (lex_9_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3985), (Sat.Literal.pos 195), (Sat.Literal.pos 30), (Sat.Literal.pos 3986)] :=
  (lex_9_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3986) = lexBefore s permutation9 194 := by
  exact (positive_lex_of_descriptor s 3986 permutation9 195 (by rfl)).trans ((lex_skipped s permutation9 194 195 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation9 194) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation9 194 by rw [image9_eq]; rfl))

theorem lex_9_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3987) (Sat.Literal.pos 3986) (Sat.Literal.pos 194) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation9 194 (assignment s)
    (Sat.Literal.pos 3987) (Sat.Literal.pos 3986) (Sat.Literal.pos 194) (Sat.Literal.pos 22) (positive_of_descriptor s 3987 (.lex permutation9 194) (by rfl)) (lex_9_194_prefix s) (positive_select s 194) (lex_9_194_image s)

theorem lex_9_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3986), (Sat.Literal.pos 194), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation9 194 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3986) (Sat.Literal.pos 194) (Sat.Literal.pos 22) (lex_9_194_prefix s) (positive_select s 194) (lex_9_194_image s)

theorem lex_9_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3987), (Sat.Literal.pos 3986)] :=
  (lex_9_194_gate s).prop _ (List.Mem.head _)

theorem lex_9_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3987), (Sat.Literal.neg 194), (Sat.Literal.pos 22)] :=
  (lex_9_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3987), (Sat.Literal.pos 194), (Sat.Literal.neg 22)] :=
  (lex_9_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3986), (Sat.Literal.neg 194), (Sat.Literal.neg 22), (Sat.Literal.pos 3987)] :=
  (lex_9_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3986), (Sat.Literal.pos 194), (Sat.Literal.pos 22), (Sat.Literal.pos 3987)] :=
  (lex_9_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3987) = lexBefore s permutation9 193 := by
  exact (positive_lex_of_descriptor s 3987 permutation9 194 (by rfl)).trans ((lex_skipped s permutation9 193 194 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 14) = s (permuteMask permutation9 193) := by
  exact (positive_select s 14).trans (congrArg s (show (14 : Fin 256) = permuteMask permutation9 193 by rw [image9_eq]; rfl))

theorem lex_9_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3988) (Sat.Literal.pos 3987) (Sat.Literal.pos 193) (Sat.Literal.pos 14)) := by
  exact equality_gate s permutation9 193 (assignment s)
    (Sat.Literal.pos 3988) (Sat.Literal.pos 3987) (Sat.Literal.pos 193) (Sat.Literal.pos 14) (positive_of_descriptor s 3988 (.lex permutation9 193) (by rfl)) (lex_9_193_prefix s) (positive_select s 193) (lex_9_193_image s)

theorem lex_9_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3987), (Sat.Literal.pos 193), (Sat.Literal.neg 14)] := by
  exact comparison_gate s permutation9 193 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3987) (Sat.Literal.pos 193) (Sat.Literal.pos 14) (lex_9_193_prefix s) (positive_select s 193) (lex_9_193_image s)

theorem lex_9_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3988), (Sat.Literal.pos 3987)] :=
  (lex_9_193_gate s).prop _ (List.Mem.head _)

theorem lex_9_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3988), (Sat.Literal.neg 193), (Sat.Literal.pos 14)] :=
  (lex_9_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3988), (Sat.Literal.pos 193), (Sat.Literal.neg 14)] :=
  (lex_9_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3987), (Sat.Literal.neg 193), (Sat.Literal.neg 14), (Sat.Literal.pos 3988)] :=
  (lex_9_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3987), (Sat.Literal.pos 193), (Sat.Literal.pos 14), (Sat.Literal.pos 3988)] :=
  (lex_9_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3988) = lexBefore s permutation9 192 := by
  exact (positive_lex_of_descriptor s 3988 permutation9 193 (by rfl)).trans ((lex_skipped s permutation9 192 193 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 6) = s (permuteMask permutation9 192) := by
  exact (positive_select s 6).trans (congrArg s (show (6 : Fin 256) = permuteMask permutation9 192 by rw [image9_eq]; rfl))

theorem lex_9_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3989) (Sat.Literal.pos 3988) (Sat.Literal.pos 192) (Sat.Literal.pos 6)) := by
  exact equality_gate s permutation9 192 (assignment s)
    (Sat.Literal.pos 3989) (Sat.Literal.pos 3988) (Sat.Literal.pos 192) (Sat.Literal.pos 6) (positive_of_descriptor s 3989 (.lex permutation9 192) (by rfl)) (lex_9_192_prefix s) (positive_select s 192) (lex_9_192_image s)

theorem lex_9_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3988), (Sat.Literal.pos 192), (Sat.Literal.neg 6)] := by
  exact comparison_gate s permutation9 192 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3988) (Sat.Literal.pos 192) (Sat.Literal.pos 6) (lex_9_192_prefix s) (positive_select s 192) (lex_9_192_image s)

theorem lex_9_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3989), (Sat.Literal.pos 3988)] :=
  (lex_9_192_gate s).prop _ (List.Mem.head _)

theorem lex_9_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3989), (Sat.Literal.neg 192), (Sat.Literal.pos 6)] :=
  (lex_9_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3989), (Sat.Literal.pos 192), (Sat.Literal.neg 6)] :=
  (lex_9_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3988), (Sat.Literal.neg 192), (Sat.Literal.neg 6), (Sat.Literal.pos 3989)] :=
  (lex_9_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3988), (Sat.Literal.pos 192), (Sat.Literal.pos 6), (Sat.Literal.pos 3989)] :=
  (lex_9_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3989) = lexBefore s permutation9 191 := by
  exact (positive_lex_of_descriptor s 3989 permutation9 192 (by rfl)).trans ((lex_skipped s permutation9 191 192 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation9 191) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation9 191 by rw [image9_eq]; rfl))

theorem lex_9_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3990) (Sat.Literal.pos 3989) (Sat.Literal.pos 191) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation9 191 (assignment s)
    (Sat.Literal.pos 3990) (Sat.Literal.pos 3989) (Sat.Literal.pos 191) (Sat.Literal.pos 253) (positive_of_descriptor s 3990 (.lex permutation9 191) (by rfl)) (lex_9_191_prefix s) (positive_select s 191) (lex_9_191_image s)

theorem lex_9_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3989), (Sat.Literal.pos 191), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation9 191 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3989) (Sat.Literal.pos 191) (Sat.Literal.pos 253) (lex_9_191_prefix s) (positive_select s 191) (lex_9_191_image s)

theorem lex_9_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3990), (Sat.Literal.pos 3989)] :=
  (lex_9_191_gate s).prop _ (List.Mem.head _)

theorem lex_9_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3990), (Sat.Literal.neg 191), (Sat.Literal.pos 253)] :=
  (lex_9_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3990), (Sat.Literal.pos 191), (Sat.Literal.neg 253)] :=
  (lex_9_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3989), (Sat.Literal.neg 191), (Sat.Literal.neg 253), (Sat.Literal.pos 3990)] :=
  (lex_9_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3989), (Sat.Literal.pos 191), (Sat.Literal.pos 253), (Sat.Literal.pos 3990)] :=
  (lex_9_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3990) = lexBefore s permutation9 190 := by
  exact (positive_lex_of_descriptor s 3990 permutation9 191 (by rfl)).trans ((lex_skipped s permutation9 190 191 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation9 190) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation9 190 by rw [image9_eq]; rfl))

theorem lex_9_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3991) (Sat.Literal.pos 3990) (Sat.Literal.pos 190) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation9 190 (assignment s)
    (Sat.Literal.pos 3991) (Sat.Literal.pos 3990) (Sat.Literal.pos 190) (Sat.Literal.pos 245) (positive_of_descriptor s 3991 (.lex permutation9 190) (by rfl)) (lex_9_190_prefix s) (positive_select s 190) (lex_9_190_image s)

theorem lex_9_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3990), (Sat.Literal.pos 190), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation9 190 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3990) (Sat.Literal.pos 190) (Sat.Literal.pos 245) (lex_9_190_prefix s) (positive_select s 190) (lex_9_190_image s)

theorem lex_9_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3991), (Sat.Literal.pos 3990)] :=
  (lex_9_190_gate s).prop _ (List.Mem.head _)

theorem lex_9_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3991), (Sat.Literal.neg 190), (Sat.Literal.pos 245)] :=
  (lex_9_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3991), (Sat.Literal.pos 190), (Sat.Literal.neg 245)] :=
  (lex_9_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3990), (Sat.Literal.neg 190), (Sat.Literal.neg 245), (Sat.Literal.pos 3991)] :=
  (lex_9_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3990), (Sat.Literal.pos 190), (Sat.Literal.pos 245), (Sat.Literal.pos 3991)] :=
  (lex_9_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3991) = lexBefore s permutation9 189 := by
  exact (positive_lex_of_descriptor s 3991 permutation9 190 (by rfl)).trans ((lex_skipped s permutation9 189 190 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation9 189) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation9 189 by rw [image9_eq]; rfl))

theorem lex_9_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3992) (Sat.Literal.pos 3991) (Sat.Literal.pos 189) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation9 189 (assignment s)
    (Sat.Literal.pos 3992) (Sat.Literal.pos 3991) (Sat.Literal.pos 189) (Sat.Literal.pos 237) (positive_of_descriptor s 3992 (.lex permutation9 189) (by rfl)) (lex_9_189_prefix s) (positive_select s 189) (lex_9_189_image s)

theorem lex_9_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3991), (Sat.Literal.pos 189), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation9 189 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3991) (Sat.Literal.pos 189) (Sat.Literal.pos 237) (lex_9_189_prefix s) (positive_select s 189) (lex_9_189_image s)

theorem lex_9_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3992), (Sat.Literal.pos 3991)] :=
  (lex_9_189_gate s).prop _ (List.Mem.head _)

theorem lex_9_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3992), (Sat.Literal.neg 189), (Sat.Literal.pos 237)] :=
  (lex_9_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3992), (Sat.Literal.pos 189), (Sat.Literal.neg 237)] :=
  (lex_9_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3991), (Sat.Literal.neg 189), (Sat.Literal.neg 237), (Sat.Literal.pos 3992)] :=
  (lex_9_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3991), (Sat.Literal.pos 189), (Sat.Literal.pos 237), (Sat.Literal.pos 3992)] :=
  (lex_9_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3992) = lexBefore s permutation9 188 := by
  exact (positive_lex_of_descriptor s 3992 permutation9 189 (by rfl)).trans ((lex_skipped s permutation9 188 189 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation9 188) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation9 188 by rw [image9_eq]; rfl))

theorem lex_9_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3993) (Sat.Literal.pos 3992) (Sat.Literal.pos 188) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation9 188 (assignment s)
    (Sat.Literal.pos 3993) (Sat.Literal.pos 3992) (Sat.Literal.pos 188) (Sat.Literal.pos 229) (positive_of_descriptor s 3993 (.lex permutation9 188) (by rfl)) (lex_9_188_prefix s) (positive_select s 188) (lex_9_188_image s)

theorem lex_9_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3992), (Sat.Literal.pos 188), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation9 188 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3992) (Sat.Literal.pos 188) (Sat.Literal.pos 229) (lex_9_188_prefix s) (positive_select s 188) (lex_9_188_image s)

theorem lex_9_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3993), (Sat.Literal.pos 3992)] :=
  (lex_9_188_gate s).prop _ (List.Mem.head _)

theorem lex_9_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3993), (Sat.Literal.neg 188), (Sat.Literal.pos 229)] :=
  (lex_9_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3993), (Sat.Literal.pos 188), (Sat.Literal.neg 229)] :=
  (lex_9_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3992), (Sat.Literal.neg 188), (Sat.Literal.neg 229), (Sat.Literal.pos 3993)] :=
  (lex_9_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3992), (Sat.Literal.pos 188), (Sat.Literal.pos 229), (Sat.Literal.pos 3993)] :=
  (lex_9_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3993) = lexBefore s permutation9 187 := by
  exact (positive_lex_of_descriptor s 3993 permutation9 188 (by rfl)).trans ((lex_skipped s permutation9 187 188 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation9 187) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation9 187 by rw [image9_eq]; rfl))

theorem lex_9_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3994) (Sat.Literal.pos 3993) (Sat.Literal.pos 187) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation9 187 (assignment s)
    (Sat.Literal.pos 3994) (Sat.Literal.pos 3993) (Sat.Literal.pos 187) (Sat.Literal.pos 221) (positive_of_descriptor s 3994 (.lex permutation9 187) (by rfl)) (lex_9_187_prefix s) (positive_select s 187) (lex_9_187_image s)

theorem lex_9_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3993), (Sat.Literal.pos 187), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation9 187 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3993) (Sat.Literal.pos 187) (Sat.Literal.pos 221) (lex_9_187_prefix s) (positive_select s 187) (lex_9_187_image s)

theorem lex_9_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3994), (Sat.Literal.pos 3993)] :=
  (lex_9_187_gate s).prop _ (List.Mem.head _)

theorem lex_9_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3994), (Sat.Literal.neg 187), (Sat.Literal.pos 221)] :=
  (lex_9_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3994), (Sat.Literal.pos 187), (Sat.Literal.neg 221)] :=
  (lex_9_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3993), (Sat.Literal.neg 187), (Sat.Literal.neg 221), (Sat.Literal.pos 3994)] :=
  (lex_9_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3993), (Sat.Literal.pos 187), (Sat.Literal.pos 221), (Sat.Literal.pos 3994)] :=
  (lex_9_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3994) = lexBefore s permutation9 186 := by
  exact (positive_lex_of_descriptor s 3994 permutation9 187 (by rfl)).trans ((lex_skipped s permutation9 186 187 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation9 186) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation9 186 by rw [image9_eq]; rfl))

theorem lex_9_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3995) (Sat.Literal.pos 3994) (Sat.Literal.pos 186) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation9 186 (assignment s)
    (Sat.Literal.pos 3995) (Sat.Literal.pos 3994) (Sat.Literal.pos 186) (Sat.Literal.pos 213) (positive_of_descriptor s 3995 (.lex permutation9 186) (by rfl)) (lex_9_186_prefix s) (positive_select s 186) (lex_9_186_image s)

theorem lex_9_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3994), (Sat.Literal.pos 186), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation9 186 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3994) (Sat.Literal.pos 186) (Sat.Literal.pos 213) (lex_9_186_prefix s) (positive_select s 186) (lex_9_186_image s)

theorem lex_9_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3995), (Sat.Literal.pos 3994)] :=
  (lex_9_186_gate s).prop _ (List.Mem.head _)

theorem lex_9_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3995), (Sat.Literal.neg 186), (Sat.Literal.pos 213)] :=
  (lex_9_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3995), (Sat.Literal.pos 186), (Sat.Literal.neg 213)] :=
  (lex_9_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3994), (Sat.Literal.neg 186), (Sat.Literal.neg 213), (Sat.Literal.pos 3995)] :=
  (lex_9_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3994), (Sat.Literal.pos 186), (Sat.Literal.pos 213), (Sat.Literal.pos 3995)] :=
  (lex_9_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3995) = lexBefore s permutation9 185 := by
  exact (positive_lex_of_descriptor s 3995 permutation9 186 (by rfl)).trans ((lex_skipped s permutation9 185 186 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation9 185) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation9 185 by rw [image9_eq]; rfl))

theorem lex_9_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3996) (Sat.Literal.pos 3995) (Sat.Literal.pos 185) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation9 185 (assignment s)
    (Sat.Literal.pos 3996) (Sat.Literal.pos 3995) (Sat.Literal.pos 185) (Sat.Literal.pos 205) (positive_of_descriptor s 3996 (.lex permutation9 185) (by rfl)) (lex_9_185_prefix s) (positive_select s 185) (lex_9_185_image s)

theorem lex_9_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3995), (Sat.Literal.pos 185), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation9 185 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3995) (Sat.Literal.pos 185) (Sat.Literal.pos 205) (lex_9_185_prefix s) (positive_select s 185) (lex_9_185_image s)

theorem lex_9_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3996), (Sat.Literal.pos 3995)] :=
  (lex_9_185_gate s).prop _ (List.Mem.head _)

theorem lex_9_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3996), (Sat.Literal.neg 185), (Sat.Literal.pos 205)] :=
  (lex_9_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3996), (Sat.Literal.pos 185), (Sat.Literal.neg 205)] :=
  (lex_9_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3995), (Sat.Literal.neg 185), (Sat.Literal.neg 205), (Sat.Literal.pos 3996)] :=
  (lex_9_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3995), (Sat.Literal.pos 185), (Sat.Literal.pos 205), (Sat.Literal.pos 3996)] :=
  (lex_9_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3996) = lexBefore s permutation9 184 := by
  exact (positive_lex_of_descriptor s 3996 permutation9 185 (by rfl)).trans ((lex_skipped s permutation9 184 185 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation9 184) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation9 184 by rw [image9_eq]; rfl))

theorem lex_9_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3997) (Sat.Literal.pos 3996) (Sat.Literal.pos 184) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation9 184 (assignment s)
    (Sat.Literal.pos 3997) (Sat.Literal.pos 3996) (Sat.Literal.pos 184) (Sat.Literal.pos 197) (positive_of_descriptor s 3997 (.lex permutation9 184) (by rfl)) (lex_9_184_prefix s) (positive_select s 184) (lex_9_184_image s)

theorem lex_9_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3996), (Sat.Literal.pos 184), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation9 184 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3996) (Sat.Literal.pos 184) (Sat.Literal.pos 197) (lex_9_184_prefix s) (positive_select s 184) (lex_9_184_image s)

theorem lex_9_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3997), (Sat.Literal.pos 3996)] :=
  (lex_9_184_gate s).prop _ (List.Mem.head _)

theorem lex_9_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3997), (Sat.Literal.neg 184), (Sat.Literal.pos 197)] :=
  (lex_9_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3997), (Sat.Literal.pos 184), (Sat.Literal.neg 197)] :=
  (lex_9_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3996), (Sat.Literal.neg 184), (Sat.Literal.neg 197), (Sat.Literal.pos 3997)] :=
  (lex_9_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3996), (Sat.Literal.pos 184), (Sat.Literal.pos 197), (Sat.Literal.pos 3997)] :=
  (lex_9_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3997) = lexBefore s permutation9 183 := by
  exact (positive_lex_of_descriptor s 3997 permutation9 184 (by rfl)).trans ((lex_skipped s permutation9 183 184 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation9 183) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation9 183 by rw [image9_eq]; rfl))

theorem lex_9_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3998) (Sat.Literal.pos 3997) (Sat.Literal.pos 183) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation9 183 (assignment s)
    (Sat.Literal.pos 3998) (Sat.Literal.pos 3997) (Sat.Literal.pos 183) (Sat.Literal.pos 189) (positive_of_descriptor s 3998 (.lex permutation9 183) (by rfl)) (lex_9_183_prefix s) (positive_select s 183) (lex_9_183_image s)

theorem lex_9_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3997), (Sat.Literal.pos 183), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation9 183 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3997) (Sat.Literal.pos 183) (Sat.Literal.pos 189) (lex_9_183_prefix s) (positive_select s 183) (lex_9_183_image s)

theorem lex_9_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3998), (Sat.Literal.pos 3997)] :=
  (lex_9_183_gate s).prop _ (List.Mem.head _)

theorem lex_9_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3998), (Sat.Literal.neg 183), (Sat.Literal.pos 189)] :=
  (lex_9_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3998), (Sat.Literal.pos 183), (Sat.Literal.neg 189)] :=
  (lex_9_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3997), (Sat.Literal.neg 183), (Sat.Literal.neg 189), (Sat.Literal.pos 3998)] :=
  (lex_9_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3997), (Sat.Literal.pos 183), (Sat.Literal.pos 189), (Sat.Literal.pos 3998)] :=
  (lex_9_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3998) = lexBefore s permutation9 182 := by
  exact (positive_lex_of_descriptor s 3998 permutation9 183 (by rfl)).trans ((lex_skipped s permutation9 182 183 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation9 182) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation9 182 by rw [image9_eq]; rfl))

theorem lex_9_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3999) (Sat.Literal.pos 3998) (Sat.Literal.pos 182) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation9 182 (assignment s)
    (Sat.Literal.pos 3999) (Sat.Literal.pos 3998) (Sat.Literal.pos 182) (Sat.Literal.pos 181) (positive_of_descriptor s 3999 (.lex permutation9 182) (by rfl)) (lex_9_182_prefix s) (positive_select s 182) (lex_9_182_image s)

theorem lex_9_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3998), (Sat.Literal.pos 182), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation9 182 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3998) (Sat.Literal.pos 182) (Sat.Literal.pos 181) (lex_9_182_prefix s) (positive_select s 182) (lex_9_182_image s)

theorem lex_9_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3999), (Sat.Literal.pos 3998)] :=
  (lex_9_182_gate s).prop _ (List.Mem.head _)

theorem lex_9_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3999), (Sat.Literal.neg 182), (Sat.Literal.pos 181)] :=
  (lex_9_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3999), (Sat.Literal.pos 182), (Sat.Literal.neg 181)] :=
  (lex_9_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3998), (Sat.Literal.neg 182), (Sat.Literal.neg 181), (Sat.Literal.pos 3999)] :=
  (lex_9_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3998), (Sat.Literal.pos 182), (Sat.Literal.pos 181), (Sat.Literal.pos 3999)] :=
  (lex_9_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3999) = lexBefore s permutation9 181 := by
  exact (positive_lex_of_descriptor s 3999 permutation9 182 (by rfl)).trans ((lex_skipped s permutation9 181 182 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation9 181) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation9 181 by rw [image9_eq]; rfl))

theorem lex_9_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4000) (Sat.Literal.pos 3999) (Sat.Literal.pos 181) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation9 181 (assignment s)
    (Sat.Literal.pos 4000) (Sat.Literal.pos 3999) (Sat.Literal.pos 181) (Sat.Literal.pos 173) (positive_of_descriptor s 4000 (.lex permutation9 181) (by rfl)) (lex_9_181_prefix s) (positive_select s 181) (lex_9_181_image s)

theorem lex_9_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3999), (Sat.Literal.pos 181), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation9 181 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 3999) (Sat.Literal.pos 181) (Sat.Literal.pos 173) (lex_9_181_prefix s) (positive_select s 181) (lex_9_181_image s)

theorem lex_9_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4000), (Sat.Literal.pos 3999)] :=
  (lex_9_181_gate s).prop _ (List.Mem.head _)

theorem lex_9_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4000), (Sat.Literal.neg 181), (Sat.Literal.pos 173)] :=
  (lex_9_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4000), (Sat.Literal.pos 181), (Sat.Literal.neg 173)] :=
  (lex_9_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3999), (Sat.Literal.neg 181), (Sat.Literal.neg 173), (Sat.Literal.pos 4000)] :=
  (lex_9_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3999), (Sat.Literal.pos 181), (Sat.Literal.pos 173), (Sat.Literal.pos 4000)] :=
  (lex_9_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4000) = lexBefore s permutation9 180 := by
  exact (positive_lex_of_descriptor s 4000 permutation9 181 (by rfl)).trans ((lex_skipped s permutation9 180 181 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation9 180) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation9 180 by rw [image9_eq]; rfl))

theorem lex_9_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4001) (Sat.Literal.pos 4000) (Sat.Literal.pos 180) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation9 180 (assignment s)
    (Sat.Literal.pos 4001) (Sat.Literal.pos 4000) (Sat.Literal.pos 180) (Sat.Literal.pos 165) (positive_of_descriptor s 4001 (.lex permutation9 180) (by rfl)) (lex_9_180_prefix s) (positive_select s 180) (lex_9_180_image s)

theorem lex_9_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4000), (Sat.Literal.pos 180), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation9 180 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4000) (Sat.Literal.pos 180) (Sat.Literal.pos 165) (lex_9_180_prefix s) (positive_select s 180) (lex_9_180_image s)

theorem lex_9_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4001), (Sat.Literal.pos 4000)] :=
  (lex_9_180_gate s).prop _ (List.Mem.head _)

theorem lex_9_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4001), (Sat.Literal.neg 180), (Sat.Literal.pos 165)] :=
  (lex_9_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4001), (Sat.Literal.pos 180), (Sat.Literal.neg 165)] :=
  (lex_9_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4000), (Sat.Literal.neg 180), (Sat.Literal.neg 165), (Sat.Literal.pos 4001)] :=
  (lex_9_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4000), (Sat.Literal.pos 180), (Sat.Literal.pos 165), (Sat.Literal.pos 4001)] :=
  (lex_9_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4001) = lexBefore s permutation9 179 := by
  exact (positive_lex_of_descriptor s 4001 permutation9 180 (by rfl)).trans ((lex_skipped s permutation9 179 180 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation9 179) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation9 179 by rw [image9_eq]; rfl))

theorem lex_9_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4002) (Sat.Literal.pos 4001) (Sat.Literal.pos 179) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation9 179 (assignment s)
    (Sat.Literal.pos 4002) (Sat.Literal.pos 4001) (Sat.Literal.pos 179) (Sat.Literal.pos 157) (positive_of_descriptor s 4002 (.lex permutation9 179) (by rfl)) (lex_9_179_prefix s) (positive_select s 179) (lex_9_179_image s)

theorem lex_9_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4001), (Sat.Literal.pos 179), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation9 179 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4001) (Sat.Literal.pos 179) (Sat.Literal.pos 157) (lex_9_179_prefix s) (positive_select s 179) (lex_9_179_image s)

theorem lex_9_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4002), (Sat.Literal.pos 4001)] :=
  (lex_9_179_gate s).prop _ (List.Mem.head _)

theorem lex_9_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4002), (Sat.Literal.neg 179), (Sat.Literal.pos 157)] :=
  (lex_9_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4002), (Sat.Literal.pos 179), (Sat.Literal.neg 157)] :=
  (lex_9_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4001), (Sat.Literal.neg 179), (Sat.Literal.neg 157), (Sat.Literal.pos 4002)] :=
  (lex_9_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4001), (Sat.Literal.pos 179), (Sat.Literal.pos 157), (Sat.Literal.pos 4002)] :=
  (lex_9_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4002) = lexBefore s permutation9 178 := by
  exact (positive_lex_of_descriptor s 4002 permutation9 179 (by rfl)).trans ((lex_skipped s permutation9 178 179 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation9 178) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation9 178 by rw [image9_eq]; rfl))

theorem lex_9_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4003) (Sat.Literal.pos 4002) (Sat.Literal.pos 178) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation9 178 (assignment s)
    (Sat.Literal.pos 4003) (Sat.Literal.pos 4002) (Sat.Literal.pos 178) (Sat.Literal.pos 149) (positive_of_descriptor s 4003 (.lex permutation9 178) (by rfl)) (lex_9_178_prefix s) (positive_select s 178) (lex_9_178_image s)

theorem lex_9_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4002), (Sat.Literal.pos 178), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation9 178 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4002) (Sat.Literal.pos 178) (Sat.Literal.pos 149) (lex_9_178_prefix s) (positive_select s 178) (lex_9_178_image s)

theorem lex_9_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4003), (Sat.Literal.pos 4002)] :=
  (lex_9_178_gate s).prop _ (List.Mem.head _)

theorem lex_9_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4003), (Sat.Literal.neg 178), (Sat.Literal.pos 149)] :=
  (lex_9_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4003), (Sat.Literal.pos 178), (Sat.Literal.neg 149)] :=
  (lex_9_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4002), (Sat.Literal.neg 178), (Sat.Literal.neg 149), (Sat.Literal.pos 4003)] :=
  (lex_9_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4002), (Sat.Literal.pos 178), (Sat.Literal.pos 149), (Sat.Literal.pos 4003)] :=
  (lex_9_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4003) = lexBefore s permutation9 177 := by
  exact (positive_lex_of_descriptor s 4003 permutation9 178 (by rfl)).trans ((lex_skipped s permutation9 177 178 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation9 177) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation9 177 by rw [image9_eq]; rfl))

theorem lex_9_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4004) (Sat.Literal.pos 4003) (Sat.Literal.pos 177) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation9 177 (assignment s)
    (Sat.Literal.pos 4004) (Sat.Literal.pos 4003) (Sat.Literal.pos 177) (Sat.Literal.pos 141) (positive_of_descriptor s 4004 (.lex permutation9 177) (by rfl)) (lex_9_177_prefix s) (positive_select s 177) (lex_9_177_image s)

theorem lex_9_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4003), (Sat.Literal.pos 177), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation9 177 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4003) (Sat.Literal.pos 177) (Sat.Literal.pos 141) (lex_9_177_prefix s) (positive_select s 177) (lex_9_177_image s)

theorem lex_9_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4004), (Sat.Literal.pos 4003)] :=
  (lex_9_177_gate s).prop _ (List.Mem.head _)

theorem lex_9_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4004), (Sat.Literal.neg 177), (Sat.Literal.pos 141)] :=
  (lex_9_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4004), (Sat.Literal.pos 177), (Sat.Literal.neg 141)] :=
  (lex_9_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4003), (Sat.Literal.neg 177), (Sat.Literal.neg 141), (Sat.Literal.pos 4004)] :=
  (lex_9_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4003), (Sat.Literal.pos 177), (Sat.Literal.pos 141), (Sat.Literal.pos 4004)] :=
  (lex_9_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4004) = lexBefore s permutation9 176 := by
  exact (positive_lex_of_descriptor s 4004 permutation9 177 (by rfl)).trans ((lex_skipped s permutation9 176 177 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation9 176) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation9 176 by rw [image9_eq]; rfl))

theorem lex_9_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4005) (Sat.Literal.pos 4004) (Sat.Literal.pos 176) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation9 176 (assignment s)
    (Sat.Literal.pos 4005) (Sat.Literal.pos 4004) (Sat.Literal.pos 176) (Sat.Literal.pos 133) (positive_of_descriptor s 4005 (.lex permutation9 176) (by rfl)) (lex_9_176_prefix s) (positive_select s 176) (lex_9_176_image s)

theorem lex_9_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4004), (Sat.Literal.pos 176), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation9 176 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4004) (Sat.Literal.pos 176) (Sat.Literal.pos 133) (lex_9_176_prefix s) (positive_select s 176) (lex_9_176_image s)

theorem lex_9_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4005), (Sat.Literal.pos 4004)] :=
  (lex_9_176_gate s).prop _ (List.Mem.head _)

theorem lex_9_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4005), (Sat.Literal.neg 176), (Sat.Literal.pos 133)] :=
  (lex_9_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4005), (Sat.Literal.pos 176), (Sat.Literal.neg 133)] :=
  (lex_9_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4004), (Sat.Literal.neg 176), (Sat.Literal.neg 133), (Sat.Literal.pos 4005)] :=
  (lex_9_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4004), (Sat.Literal.pos 176), (Sat.Literal.pos 133), (Sat.Literal.pos 4005)] :=
  (lex_9_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4005) = lexBefore s permutation9 175 := by
  exact (positive_lex_of_descriptor s 4005 permutation9 176 (by rfl)).trans ((lex_skipped s permutation9 175 176 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation9 175) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation9 175 by rw [image9_eq]; rfl))

theorem lex_9_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4006) (Sat.Literal.pos 4005) (Sat.Literal.pos 175) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation9 175 (assignment s)
    (Sat.Literal.pos 4006) (Sat.Literal.pos 4005) (Sat.Literal.pos 175) (Sat.Literal.pos 125) (positive_of_descriptor s 4006 (.lex permutation9 175) (by rfl)) (lex_9_175_prefix s) (positive_select s 175) (lex_9_175_image s)

theorem lex_9_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4005), (Sat.Literal.pos 175), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation9 175 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4005) (Sat.Literal.pos 175) (Sat.Literal.pos 125) (lex_9_175_prefix s) (positive_select s 175) (lex_9_175_image s)

theorem lex_9_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4006), (Sat.Literal.pos 4005)] :=
  (lex_9_175_gate s).prop _ (List.Mem.head _)

theorem lex_9_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4006), (Sat.Literal.neg 175), (Sat.Literal.pos 125)] :=
  (lex_9_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4006), (Sat.Literal.pos 175), (Sat.Literal.neg 125)] :=
  (lex_9_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4005), (Sat.Literal.neg 175), (Sat.Literal.neg 125), (Sat.Literal.pos 4006)] :=
  (lex_9_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4005), (Sat.Literal.pos 175), (Sat.Literal.pos 125), (Sat.Literal.pos 4006)] :=
  (lex_9_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4006) = lexBefore s permutation9 174 := by
  exact (positive_lex_of_descriptor s 4006 permutation9 175 (by rfl)).trans ((lex_skipped s permutation9 174 175 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation9 174) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation9 174 by rw [image9_eq]; rfl))

theorem lex_9_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4007) (Sat.Literal.pos 4006) (Sat.Literal.pos 174) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation9 174 (assignment s)
    (Sat.Literal.pos 4007) (Sat.Literal.pos 4006) (Sat.Literal.pos 174) (Sat.Literal.pos 117) (positive_of_descriptor s 4007 (.lex permutation9 174) (by rfl)) (lex_9_174_prefix s) (positive_select s 174) (lex_9_174_image s)

theorem lex_9_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4006), (Sat.Literal.pos 174), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation9 174 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4006) (Sat.Literal.pos 174) (Sat.Literal.pos 117) (lex_9_174_prefix s) (positive_select s 174) (lex_9_174_image s)

theorem lex_9_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4007), (Sat.Literal.pos 4006)] :=
  (lex_9_174_gate s).prop _ (List.Mem.head _)

theorem lex_9_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4007), (Sat.Literal.neg 174), (Sat.Literal.pos 117)] :=
  (lex_9_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4007), (Sat.Literal.pos 174), (Sat.Literal.neg 117)] :=
  (lex_9_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4006), (Sat.Literal.neg 174), (Sat.Literal.neg 117), (Sat.Literal.pos 4007)] :=
  (lex_9_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4006), (Sat.Literal.pos 174), (Sat.Literal.pos 117), (Sat.Literal.pos 4007)] :=
  (lex_9_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4007) = lexBefore s permutation9 173 := by
  exact (positive_lex_of_descriptor s 4007 permutation9 174 (by rfl)).trans ((lex_skipped s permutation9 173 174 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation9 173) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation9 173 by rw [image9_eq]; rfl))

theorem lex_9_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4008) (Sat.Literal.pos 4007) (Sat.Literal.pos 173) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation9 173 (assignment s)
    (Sat.Literal.pos 4008) (Sat.Literal.pos 4007) (Sat.Literal.pos 173) (Sat.Literal.pos 109) (positive_of_descriptor s 4008 (.lex permutation9 173) (by rfl)) (lex_9_173_prefix s) (positive_select s 173) (lex_9_173_image s)

theorem lex_9_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4007), (Sat.Literal.pos 173), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation9 173 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4007) (Sat.Literal.pos 173) (Sat.Literal.pos 109) (lex_9_173_prefix s) (positive_select s 173) (lex_9_173_image s)

theorem lex_9_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4008), (Sat.Literal.pos 4007)] :=
  (lex_9_173_gate s).prop _ (List.Mem.head _)

theorem lex_9_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4008), (Sat.Literal.neg 173), (Sat.Literal.pos 109)] :=
  (lex_9_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4008), (Sat.Literal.pos 173), (Sat.Literal.neg 109)] :=
  (lex_9_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4007), (Sat.Literal.neg 173), (Sat.Literal.neg 109), (Sat.Literal.pos 4008)] :=
  (lex_9_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4007), (Sat.Literal.pos 173), (Sat.Literal.pos 109), (Sat.Literal.pos 4008)] :=
  (lex_9_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4008) = lexBefore s permutation9 172 := by
  exact (positive_lex_of_descriptor s 4008 permutation9 173 (by rfl)).trans ((lex_skipped s permutation9 172 173 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation9 172) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation9 172 by rw [image9_eq]; rfl))

theorem lex_9_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4009) (Sat.Literal.pos 4008) (Sat.Literal.pos 172) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation9 172 (assignment s)
    (Sat.Literal.pos 4009) (Sat.Literal.pos 4008) (Sat.Literal.pos 172) (Sat.Literal.pos 101) (positive_of_descriptor s 4009 (.lex permutation9 172) (by rfl)) (lex_9_172_prefix s) (positive_select s 172) (lex_9_172_image s)

theorem lex_9_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4008), (Sat.Literal.pos 172), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation9 172 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4008) (Sat.Literal.pos 172) (Sat.Literal.pos 101) (lex_9_172_prefix s) (positive_select s 172) (lex_9_172_image s)

theorem lex_9_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4009), (Sat.Literal.pos 4008)] :=
  (lex_9_172_gate s).prop _ (List.Mem.head _)

theorem lex_9_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4009), (Sat.Literal.neg 172), (Sat.Literal.pos 101)] :=
  (lex_9_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4009), (Sat.Literal.pos 172), (Sat.Literal.neg 101)] :=
  (lex_9_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4008), (Sat.Literal.neg 172), (Sat.Literal.neg 101), (Sat.Literal.pos 4009)] :=
  (lex_9_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4008), (Sat.Literal.pos 172), (Sat.Literal.pos 101), (Sat.Literal.pos 4009)] :=
  (lex_9_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4009) = lexBefore s permutation9 171 := by
  exact (positive_lex_of_descriptor s 4009 permutation9 172 (by rfl)).trans ((lex_skipped s permutation9 171 172 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation9 171) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation9 171 by rw [image9_eq]; rfl))

theorem lex_9_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4010) (Sat.Literal.pos 4009) (Sat.Literal.pos 171) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation9 171 (assignment s)
    (Sat.Literal.pos 4010) (Sat.Literal.pos 4009) (Sat.Literal.pos 171) (Sat.Literal.pos 93) (positive_of_descriptor s 4010 (.lex permutation9 171) (by rfl)) (lex_9_171_prefix s) (positive_select s 171) (lex_9_171_image s)

theorem lex_9_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4009), (Sat.Literal.pos 171), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation9 171 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4009) (Sat.Literal.pos 171) (Sat.Literal.pos 93) (lex_9_171_prefix s) (positive_select s 171) (lex_9_171_image s)

theorem lex_9_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4010), (Sat.Literal.pos 4009)] :=
  (lex_9_171_gate s).prop _ (List.Mem.head _)

theorem lex_9_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4010), (Sat.Literal.neg 171), (Sat.Literal.pos 93)] :=
  (lex_9_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4010), (Sat.Literal.pos 171), (Sat.Literal.neg 93)] :=
  (lex_9_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4009), (Sat.Literal.neg 171), (Sat.Literal.neg 93), (Sat.Literal.pos 4010)] :=
  (lex_9_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4009), (Sat.Literal.pos 171), (Sat.Literal.pos 93), (Sat.Literal.pos 4010)] :=
  (lex_9_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4010) = lexBefore s permutation9 170 := by
  exact (positive_lex_of_descriptor s 4010 permutation9 171 (by rfl)).trans ((lex_skipped s permutation9 170 171 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation9 170) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation9 170 by rw [image9_eq]; rfl))

theorem lex_9_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4011) (Sat.Literal.pos 4010) (Sat.Literal.pos 170) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation9 170 (assignment s)
    (Sat.Literal.pos 4011) (Sat.Literal.pos 4010) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (positive_of_descriptor s 4011 (.lex permutation9 170) (by rfl)) (lex_9_170_prefix s) (positive_select s 170) (lex_9_170_image s)

theorem lex_9_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4010), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation9 170 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4010) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (lex_9_170_prefix s) (positive_select s 170) (lex_9_170_image s)

theorem lex_9_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4011), (Sat.Literal.pos 4010)] :=
  (lex_9_170_gate s).prop _ (List.Mem.head _)

theorem lex_9_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4011), (Sat.Literal.neg 170), (Sat.Literal.pos 85)] :=
  (lex_9_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4011), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] :=
  (lex_9_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4010), (Sat.Literal.neg 170), (Sat.Literal.neg 85), (Sat.Literal.pos 4011)] :=
  (lex_9_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4010), (Sat.Literal.pos 170), (Sat.Literal.pos 85), (Sat.Literal.pos 4011)] :=
  (lex_9_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4011) = lexBefore s permutation9 169 := by
  exact (positive_lex_of_descriptor s 4011 permutation9 170 (by rfl)).trans ((lex_skipped s permutation9 169 170 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation9 169) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation9 169 by rw [image9_eq]; rfl))

theorem lex_9_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4012) (Sat.Literal.pos 4011) (Sat.Literal.pos 169) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation9 169 (assignment s)
    (Sat.Literal.pos 4012) (Sat.Literal.pos 4011) (Sat.Literal.pos 169) (Sat.Literal.pos 77) (positive_of_descriptor s 4012 (.lex permutation9 169) (by rfl)) (lex_9_169_prefix s) (positive_select s 169) (lex_9_169_image s)

theorem lex_9_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4011), (Sat.Literal.pos 169), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation9 169 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4011) (Sat.Literal.pos 169) (Sat.Literal.pos 77) (lex_9_169_prefix s) (positive_select s 169) (lex_9_169_image s)

theorem lex_9_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4012), (Sat.Literal.pos 4011)] :=
  (lex_9_169_gate s).prop _ (List.Mem.head _)

theorem lex_9_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4012), (Sat.Literal.neg 169), (Sat.Literal.pos 77)] :=
  (lex_9_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4012), (Sat.Literal.pos 169), (Sat.Literal.neg 77)] :=
  (lex_9_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4011), (Sat.Literal.neg 169), (Sat.Literal.neg 77), (Sat.Literal.pos 4012)] :=
  (lex_9_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4011), (Sat.Literal.pos 169), (Sat.Literal.pos 77), (Sat.Literal.pos 4012)] :=
  (lex_9_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4012) = lexBefore s permutation9 168 := by
  exact (positive_lex_of_descriptor s 4012 permutation9 169 (by rfl)).trans ((lex_skipped s permutation9 168 169 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation9 168) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation9 168 by rw [image9_eq]; rfl))

theorem lex_9_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4013) (Sat.Literal.pos 4012) (Sat.Literal.pos 168) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation9 168 (assignment s)
    (Sat.Literal.pos 4013) (Sat.Literal.pos 4012) (Sat.Literal.pos 168) (Sat.Literal.pos 69) (positive_of_descriptor s 4013 (.lex permutation9 168) (by rfl)) (lex_9_168_prefix s) (positive_select s 168) (lex_9_168_image s)

theorem lex_9_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4012), (Sat.Literal.pos 168), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation9 168 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4012) (Sat.Literal.pos 168) (Sat.Literal.pos 69) (lex_9_168_prefix s) (positive_select s 168) (lex_9_168_image s)

theorem lex_9_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4013), (Sat.Literal.pos 4012)] :=
  (lex_9_168_gate s).prop _ (List.Mem.head _)

theorem lex_9_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4013), (Sat.Literal.neg 168), (Sat.Literal.pos 69)] :=
  (lex_9_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4013), (Sat.Literal.pos 168), (Sat.Literal.neg 69)] :=
  (lex_9_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4012), (Sat.Literal.neg 168), (Sat.Literal.neg 69), (Sat.Literal.pos 4013)] :=
  (lex_9_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4012), (Sat.Literal.pos 168), (Sat.Literal.pos 69), (Sat.Literal.pos 4013)] :=
  (lex_9_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4013) = lexBefore s permutation9 167 := by
  exact (positive_lex_of_descriptor s 4013 permutation9 168 (by rfl)).trans ((lex_skipped s permutation9 167 168 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation9 167) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation9 167 by rw [image9_eq]; rfl))

theorem lex_9_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4014) (Sat.Literal.pos 4013) (Sat.Literal.pos 167) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation9 167 (assignment s)
    (Sat.Literal.pos 4014) (Sat.Literal.pos 4013) (Sat.Literal.pos 167) (Sat.Literal.pos 61) (positive_of_descriptor s 4014 (.lex permutation9 167) (by rfl)) (lex_9_167_prefix s) (positive_select s 167) (lex_9_167_image s)

theorem lex_9_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4013), (Sat.Literal.pos 167), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation9 167 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4013) (Sat.Literal.pos 167) (Sat.Literal.pos 61) (lex_9_167_prefix s) (positive_select s 167) (lex_9_167_image s)

theorem lex_9_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4014), (Sat.Literal.pos 4013)] :=
  (lex_9_167_gate s).prop _ (List.Mem.head _)

theorem lex_9_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4014), (Sat.Literal.neg 167), (Sat.Literal.pos 61)] :=
  (lex_9_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4014), (Sat.Literal.pos 167), (Sat.Literal.neg 61)] :=
  (lex_9_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4013), (Sat.Literal.neg 167), (Sat.Literal.neg 61), (Sat.Literal.pos 4014)] :=
  (lex_9_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4013), (Sat.Literal.pos 167), (Sat.Literal.pos 61), (Sat.Literal.pos 4014)] :=
  (lex_9_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4014) = lexBefore s permutation9 166 := by
  exact (positive_lex_of_descriptor s 4014 permutation9 167 (by rfl)).trans ((lex_skipped s permutation9 166 167 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation9 166) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation9 166 by rw [image9_eq]; rfl))

theorem lex_9_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4015) (Sat.Literal.pos 4014) (Sat.Literal.pos 166) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation9 166 (assignment s)
    (Sat.Literal.pos 4015) (Sat.Literal.pos 4014) (Sat.Literal.pos 166) (Sat.Literal.pos 53) (positive_of_descriptor s 4015 (.lex permutation9 166) (by rfl)) (lex_9_166_prefix s) (positive_select s 166) (lex_9_166_image s)

theorem lex_9_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4014), (Sat.Literal.pos 166), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation9 166 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4014) (Sat.Literal.pos 166) (Sat.Literal.pos 53) (lex_9_166_prefix s) (positive_select s 166) (lex_9_166_image s)

theorem lex_9_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4015), (Sat.Literal.pos 4014)] :=
  (lex_9_166_gate s).prop _ (List.Mem.head _)

theorem lex_9_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4015), (Sat.Literal.neg 166), (Sat.Literal.pos 53)] :=
  (lex_9_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4015), (Sat.Literal.pos 166), (Sat.Literal.neg 53)] :=
  (lex_9_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4014), (Sat.Literal.neg 166), (Sat.Literal.neg 53), (Sat.Literal.pos 4015)] :=
  (lex_9_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4014), (Sat.Literal.pos 166), (Sat.Literal.pos 53), (Sat.Literal.pos 4015)] :=
  (lex_9_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4015) = lexBefore s permutation9 165 := by
  exact (positive_lex_of_descriptor s 4015 permutation9 166 (by rfl)).trans ((lex_skipped s permutation9 165 166 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 45) = s (permuteMask permutation9 165) := by
  exact (positive_select s 45).trans (congrArg s (show (45 : Fin 256) = permuteMask permutation9 165 by rw [image9_eq]; rfl))

theorem lex_9_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4016) (Sat.Literal.pos 4015) (Sat.Literal.pos 165) (Sat.Literal.pos 45)) := by
  exact equality_gate s permutation9 165 (assignment s)
    (Sat.Literal.pos 4016) (Sat.Literal.pos 4015) (Sat.Literal.pos 165) (Sat.Literal.pos 45) (positive_of_descriptor s 4016 (.lex permutation9 165) (by rfl)) (lex_9_165_prefix s) (positive_select s 165) (lex_9_165_image s)

theorem lex_9_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4015), (Sat.Literal.pos 165), (Sat.Literal.neg 45)] := by
  exact comparison_gate s permutation9 165 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4015) (Sat.Literal.pos 165) (Sat.Literal.pos 45) (lex_9_165_prefix s) (positive_select s 165) (lex_9_165_image s)

theorem lex_9_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4016), (Sat.Literal.pos 4015)] :=
  (lex_9_165_gate s).prop _ (List.Mem.head _)

theorem lex_9_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4016), (Sat.Literal.neg 165), (Sat.Literal.pos 45)] :=
  (lex_9_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4016), (Sat.Literal.pos 165), (Sat.Literal.neg 45)] :=
  (lex_9_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4015), (Sat.Literal.neg 165), (Sat.Literal.neg 45), (Sat.Literal.pos 4016)] :=
  (lex_9_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4015), (Sat.Literal.pos 165), (Sat.Literal.pos 45), (Sat.Literal.pos 4016)] :=
  (lex_9_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4016) = lexBefore s permutation9 164 := by
  exact (positive_lex_of_descriptor s 4016 permutation9 165 (by rfl)).trans ((lex_skipped s permutation9 164 165 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 37) = s (permuteMask permutation9 164) := by
  exact (positive_select s 37).trans (congrArg s (show (37 : Fin 256) = permuteMask permutation9 164 by rw [image9_eq]; rfl))

theorem lex_9_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4017) (Sat.Literal.pos 4016) (Sat.Literal.pos 164) (Sat.Literal.pos 37)) := by
  exact equality_gate s permutation9 164 (assignment s)
    (Sat.Literal.pos 4017) (Sat.Literal.pos 4016) (Sat.Literal.pos 164) (Sat.Literal.pos 37) (positive_of_descriptor s 4017 (.lex permutation9 164) (by rfl)) (lex_9_164_prefix s) (positive_select s 164) (lex_9_164_image s)

theorem lex_9_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4016), (Sat.Literal.pos 164), (Sat.Literal.neg 37)] := by
  exact comparison_gate s permutation9 164 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4016) (Sat.Literal.pos 164) (Sat.Literal.pos 37) (lex_9_164_prefix s) (positive_select s 164) (lex_9_164_image s)

theorem lex_9_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4017), (Sat.Literal.pos 4016)] :=
  (lex_9_164_gate s).prop _ (List.Mem.head _)

theorem lex_9_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4017), (Sat.Literal.neg 164), (Sat.Literal.pos 37)] :=
  (lex_9_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4017), (Sat.Literal.pos 164), (Sat.Literal.neg 37)] :=
  (lex_9_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4016), (Sat.Literal.neg 164), (Sat.Literal.neg 37), (Sat.Literal.pos 4017)] :=
  (lex_9_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4016), (Sat.Literal.pos 164), (Sat.Literal.pos 37), (Sat.Literal.pos 4017)] :=
  (lex_9_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4017) = lexBefore s permutation9 163 := by
  exact (positive_lex_of_descriptor s 4017 permutation9 164 (by rfl)).trans ((lex_skipped s permutation9 163 164 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation9 163) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation9 163 by rw [image9_eq]; rfl))

theorem lex_9_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4018) (Sat.Literal.pos 4017) (Sat.Literal.pos 163) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation9 163 (assignment s)
    (Sat.Literal.pos 4018) (Sat.Literal.pos 4017) (Sat.Literal.pos 163) (Sat.Literal.pos 29) (positive_of_descriptor s 4018 (.lex permutation9 163) (by rfl)) (lex_9_163_prefix s) (positive_select s 163) (lex_9_163_image s)

theorem lex_9_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4017), (Sat.Literal.pos 163), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation9 163 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4017) (Sat.Literal.pos 163) (Sat.Literal.pos 29) (lex_9_163_prefix s) (positive_select s 163) (lex_9_163_image s)

theorem lex_9_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4018), (Sat.Literal.pos 4017)] :=
  (lex_9_163_gate s).prop _ (List.Mem.head _)

theorem lex_9_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4018), (Sat.Literal.neg 163), (Sat.Literal.pos 29)] :=
  (lex_9_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4018), (Sat.Literal.pos 163), (Sat.Literal.neg 29)] :=
  (lex_9_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4017), (Sat.Literal.neg 163), (Sat.Literal.neg 29), (Sat.Literal.pos 4018)] :=
  (lex_9_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4017), (Sat.Literal.pos 163), (Sat.Literal.pos 29), (Sat.Literal.pos 4018)] :=
  (lex_9_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4018) = lexBefore s permutation9 162 := by
  exact (positive_lex_of_descriptor s 4018 permutation9 163 (by rfl)).trans ((lex_skipped s permutation9 162 163 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation9 162) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation9 162 by rw [image9_eq]; rfl))

theorem lex_9_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4019) (Sat.Literal.pos 4018) (Sat.Literal.pos 162) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation9 162 (assignment s)
    (Sat.Literal.pos 4019) (Sat.Literal.pos 4018) (Sat.Literal.pos 162) (Sat.Literal.pos 21) (positive_of_descriptor s 4019 (.lex permutation9 162) (by rfl)) (lex_9_162_prefix s) (positive_select s 162) (lex_9_162_image s)

theorem lex_9_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4018), (Sat.Literal.pos 162), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation9 162 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4018) (Sat.Literal.pos 162) (Sat.Literal.pos 21) (lex_9_162_prefix s) (positive_select s 162) (lex_9_162_image s)

theorem lex_9_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4019), (Sat.Literal.pos 4018)] :=
  (lex_9_162_gate s).prop _ (List.Mem.head _)

theorem lex_9_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4019), (Sat.Literal.neg 162), (Sat.Literal.pos 21)] :=
  (lex_9_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4019), (Sat.Literal.pos 162), (Sat.Literal.neg 21)] :=
  (lex_9_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4018), (Sat.Literal.neg 162), (Sat.Literal.neg 21), (Sat.Literal.pos 4019)] :=
  (lex_9_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4018), (Sat.Literal.pos 162), (Sat.Literal.pos 21), (Sat.Literal.pos 4019)] :=
  (lex_9_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4019) = lexBefore s permutation9 161 := by
  exact (positive_lex_of_descriptor s 4019 permutation9 162 (by rfl)).trans ((lex_skipped s permutation9 161 162 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 13) = s (permuteMask permutation9 161) := by
  exact (positive_select s 13).trans (congrArg s (show (13 : Fin 256) = permuteMask permutation9 161 by rw [image9_eq]; rfl))

theorem lex_9_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4020) (Sat.Literal.pos 4019) (Sat.Literal.pos 161) (Sat.Literal.pos 13)) := by
  exact equality_gate s permutation9 161 (assignment s)
    (Sat.Literal.pos 4020) (Sat.Literal.pos 4019) (Sat.Literal.pos 161) (Sat.Literal.pos 13) (positive_of_descriptor s 4020 (.lex permutation9 161) (by rfl)) (lex_9_161_prefix s) (positive_select s 161) (lex_9_161_image s)

theorem lex_9_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4019), (Sat.Literal.pos 161), (Sat.Literal.neg 13)] := by
  exact comparison_gate s permutation9 161 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4019) (Sat.Literal.pos 161) (Sat.Literal.pos 13) (lex_9_161_prefix s) (positive_select s 161) (lex_9_161_image s)

theorem lex_9_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4020), (Sat.Literal.pos 4019)] :=
  (lex_9_161_gate s).prop _ (List.Mem.head _)

theorem lex_9_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4020), (Sat.Literal.neg 161), (Sat.Literal.pos 13)] :=
  (lex_9_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4020), (Sat.Literal.pos 161), (Sat.Literal.neg 13)] :=
  (lex_9_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4019), (Sat.Literal.neg 161), (Sat.Literal.neg 13), (Sat.Literal.pos 4020)] :=
  (lex_9_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4019), (Sat.Literal.pos 161), (Sat.Literal.pos 13), (Sat.Literal.pos 4020)] :=
  (lex_9_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4020) = lexBefore s permutation9 160 := by
  exact (positive_lex_of_descriptor s 4020 permutation9 161 (by rfl)).trans ((lex_skipped s permutation9 160 161 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5) = s (permuteMask permutation9 160) := by
  exact (positive_select s 5).trans (congrArg s (show (5 : Fin 256) = permuteMask permutation9 160 by rw [image9_eq]; rfl))

theorem lex_9_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4021) (Sat.Literal.pos 4020) (Sat.Literal.pos 160) (Sat.Literal.pos 5)) := by
  exact equality_gate s permutation9 160 (assignment s)
    (Sat.Literal.pos 4021) (Sat.Literal.pos 4020) (Sat.Literal.pos 160) (Sat.Literal.pos 5) (positive_of_descriptor s 4021 (.lex permutation9 160) (by rfl)) (lex_9_160_prefix s) (positive_select s 160) (lex_9_160_image s)

theorem lex_9_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4020), (Sat.Literal.pos 160), (Sat.Literal.neg 5)] := by
  exact comparison_gate s permutation9 160 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4020) (Sat.Literal.pos 160) (Sat.Literal.pos 5) (lex_9_160_prefix s) (positive_select s 160) (lex_9_160_image s)

theorem lex_9_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4021), (Sat.Literal.pos 4020)] :=
  (lex_9_160_gate s).prop _ (List.Mem.head _)

theorem lex_9_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4021), (Sat.Literal.neg 160), (Sat.Literal.pos 5)] :=
  (lex_9_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4021), (Sat.Literal.pos 160), (Sat.Literal.neg 5)] :=
  (lex_9_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4020), (Sat.Literal.neg 160), (Sat.Literal.neg 5), (Sat.Literal.pos 4021)] :=
  (lex_9_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4020), (Sat.Literal.pos 160), (Sat.Literal.pos 5), (Sat.Literal.pos 4021)] :=
  (lex_9_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4021) = lexBefore s permutation9 159 := by
  exact (positive_lex_of_descriptor s 4021 permutation9 160 (by rfl)).trans ((lex_skipped s permutation9 159 160 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation9 159) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation9 159 by rw [image9_eq]; rfl))

theorem lex_9_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4022) (Sat.Literal.pos 4021) (Sat.Literal.pos 159) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation9 159 (assignment s)
    (Sat.Literal.pos 4022) (Sat.Literal.pos 4021) (Sat.Literal.pos 159) (Sat.Literal.pos 252) (positive_of_descriptor s 4022 (.lex permutation9 159) (by rfl)) (lex_9_159_prefix s) (positive_select s 159) (lex_9_159_image s)

theorem lex_9_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4021), (Sat.Literal.pos 159), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation9 159 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4021) (Sat.Literal.pos 159) (Sat.Literal.pos 252) (lex_9_159_prefix s) (positive_select s 159) (lex_9_159_image s)

theorem lex_9_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4022), (Sat.Literal.pos 4021)] :=
  (lex_9_159_gate s).prop _ (List.Mem.head _)

theorem lex_9_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4022), (Sat.Literal.neg 159), (Sat.Literal.pos 252)] :=
  (lex_9_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4022), (Sat.Literal.pos 159), (Sat.Literal.neg 252)] :=
  (lex_9_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4021), (Sat.Literal.neg 159), (Sat.Literal.neg 252), (Sat.Literal.pos 4022)] :=
  (lex_9_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4021), (Sat.Literal.pos 159), (Sat.Literal.pos 252), (Sat.Literal.pos 4022)] :=
  (lex_9_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4022) = lexBefore s permutation9 158 := by
  exact (positive_lex_of_descriptor s 4022 permutation9 159 (by rfl)).trans ((lex_skipped s permutation9 158 159 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation9 158) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation9 158 by rw [image9_eq]; rfl))

theorem lex_9_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4023) (Sat.Literal.pos 4022) (Sat.Literal.pos 158) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation9 158 (assignment s)
    (Sat.Literal.pos 4023) (Sat.Literal.pos 4022) (Sat.Literal.pos 158) (Sat.Literal.pos 244) (positive_of_descriptor s 4023 (.lex permutation9 158) (by rfl)) (lex_9_158_prefix s) (positive_select s 158) (lex_9_158_image s)

theorem lex_9_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4022), (Sat.Literal.pos 158), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation9 158 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4022) (Sat.Literal.pos 158) (Sat.Literal.pos 244) (lex_9_158_prefix s) (positive_select s 158) (lex_9_158_image s)

theorem lex_9_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4023), (Sat.Literal.pos 4022)] :=
  (lex_9_158_gate s).prop _ (List.Mem.head _)

theorem lex_9_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4023), (Sat.Literal.neg 158), (Sat.Literal.pos 244)] :=
  (lex_9_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4023), (Sat.Literal.pos 158), (Sat.Literal.neg 244)] :=
  (lex_9_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4022), (Sat.Literal.neg 158), (Sat.Literal.neg 244), (Sat.Literal.pos 4023)] :=
  (lex_9_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4022), (Sat.Literal.pos 158), (Sat.Literal.pos 244), (Sat.Literal.pos 4023)] :=
  (lex_9_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_9_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4023) = lexBefore s permutation9 157 := by
  exact (positive_lex_of_descriptor s 4023 permutation9 158 (by rfl)).trans ((lex_skipped s permutation9 157 158 (by decide) (by intro j hj hp; rw [image9_eq]; exact fixedOnRange_spec image9 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_9_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation9 157) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation9 157 by rw [image9_eq]; rfl))

theorem lex_9_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4024) (Sat.Literal.pos 4023) (Sat.Literal.pos 157) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation9 157 (assignment s)
    (Sat.Literal.pos 4024) (Sat.Literal.pos 4023) (Sat.Literal.pos 157) (Sat.Literal.pos 236) (positive_of_descriptor s 4024 (.lex permutation9 157) (by rfl)) (lex_9_157_prefix s) (positive_select s 157) (lex_9_157_image s)

theorem lex_9_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4023), (Sat.Literal.pos 157), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation9 157 (hmax permutation9) (assignment s)
    (Sat.Literal.pos 4023) (Sat.Literal.pos 157) (Sat.Literal.pos 236) (lex_9_157_prefix s) (positive_select s 157) (lex_9_157_image s)

theorem lex_9_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4024), (Sat.Literal.pos 4023)] :=
  (lex_9_157_gate s).prop _ (List.Mem.head _)

theorem lex_9_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4024), (Sat.Literal.neg 157), (Sat.Literal.pos 236)] :=
  (lex_9_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_9_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4024), (Sat.Literal.pos 157), (Sat.Literal.neg 236)] :=
  (lex_9_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_9_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4023), (Sat.Literal.neg 157), (Sat.Literal.neg 236), (Sat.Literal.pos 4024)] :=
  (lex_9_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_9_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4023), (Sat.Literal.pos 157), (Sat.Literal.pos 236), (Sat.Literal.pos 4024)] :=
  (lex_9_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_8_2_gate

end Crown.CertificateData
