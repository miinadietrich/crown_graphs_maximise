import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_12_2_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4924) = lexBefore s permutation12 2 := by
  exact (positive_lex_of_descriptor s 4924 permutation12 3 (by rfl)).trans ((lex_skipped s permutation12 2 3 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 3 3 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_2_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation12 2) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation12 2 by rw [image12_eq]; rfl))

theorem lex_12_2_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4925) (Sat.Literal.pos 4924) (Sat.Literal.pos 2) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation12 2 (assignment s)
    (Sat.Literal.pos 4925) (Sat.Literal.pos 4924) (Sat.Literal.pos 2) (Sat.Literal.pos 128) (positive_of_descriptor s 4925 (.lex permutation12 2) (by rfl)) (lex_12_2_prefix s) (positive_select s 2) (lex_12_2_image s)

theorem lex_12_2_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4924), (Sat.Literal.pos 2), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation12 2 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4924) (Sat.Literal.pos 2) (Sat.Literal.pos 128) (lex_12_2_prefix s) (positive_select s 2) (lex_12_2_image s)

theorem lex_12_2_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4925), (Sat.Literal.pos 4924)] :=
  (lex_12_2_gate s).prop _ (List.Mem.head _)

theorem lex_12_2_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4925), (Sat.Literal.neg 2), (Sat.Literal.pos 128)] :=
  (lex_12_2_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_2_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4925), (Sat.Literal.pos 2), (Sat.Literal.neg 128)] :=
  (lex_12_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_2_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4924), (Sat.Literal.neg 2), (Sat.Literal.neg 128), (Sat.Literal.pos 4925)] :=
  (lex_12_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_2_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4924), (Sat.Literal.pos 2), (Sat.Literal.pos 128), (Sat.Literal.pos 4925)] :=
  (lex_12_2_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_12_1_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4925) = lexBefore s permutation12 1 := by
  exact (positive_lex_of_descriptor s 4925 permutation12 2 (by rfl)).trans ((lex_skipped s permutation12 1 2 (by decide) (by intro j hj hp; rw [image12_eq]; exact fixedOnRange_spec image12 2 2 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_12_1_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation12 1) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation12 1 by rw [image12_eq]; rfl))

theorem lex_12_1_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4926) (Sat.Literal.pos 4925) (Sat.Literal.pos 1) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation12 1 (assignment s)
    (Sat.Literal.pos 4926) (Sat.Literal.pos 4925) (Sat.Literal.pos 1) (Sat.Literal.pos 64) (positive_of_descriptor s 4926 (.lex permutation12 1) (by rfl)) (lex_12_1_prefix s) (positive_select s 1) (lex_12_1_image s)

theorem lex_12_1_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4925), (Sat.Literal.pos 1), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation12 1 (hmax permutation12) (assignment s)
    (Sat.Literal.pos 4925) (Sat.Literal.pos 1) (Sat.Literal.pos 64) (lex_12_1_prefix s) (positive_select s 1) (lex_12_1_image s)

theorem lex_12_1_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4926), (Sat.Literal.pos 4925)] :=
  (lex_12_1_gate s).prop _ (List.Mem.head _)

theorem lex_12_1_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4926), (Sat.Literal.neg 1), (Sat.Literal.pos 64)] :=
  (lex_12_1_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_12_1_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4926), (Sat.Literal.pos 1), (Sat.Literal.neg 64)] :=
  (lex_12_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_12_1_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4925), (Sat.Literal.neg 1), (Sat.Literal.neg 64), (Sat.Literal.pos 4926)] :=
  (lex_12_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_12_1_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4925), (Sat.Literal.pos 1), (Sat.Literal.pos 64), (Sat.Literal.pos 4926)] :=
  (lex_12_1_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation13 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation13 254 (by intro j hj; rw [image13_eq]; exact fixedOnRange_spec image13 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_13_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation13 254) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation13 254 by rw [image13_eq]; rfl))

theorem lex_13_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4927) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation13 254 (assignment s)
    (Sat.Literal.pos 4927) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 127) (positive_of_descriptor s 4927 (.lex permutation13 254) (by rfl)) (lex_13_254_prefix s) (positive_select s 254) (lex_13_254_image s)

theorem lex_13_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation13 254 (hmax permutation13) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 127) (lex_13_254_prefix s) (positive_select s 254) (lex_13_254_image s)

theorem lex_13_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4927), (Sat.Literal.neg 256)] :=
  (lex_13_254_gate s).prop _ (List.Mem.head _)

theorem lex_13_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4927), (Sat.Literal.neg 254), (Sat.Literal.pos 127)] :=
  (lex_13_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4927), (Sat.Literal.pos 254), (Sat.Literal.neg 127)] :=
  (lex_13_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 127), (Sat.Literal.pos 4927)] :=
  (lex_13_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 127), (Sat.Literal.pos 4927)] :=
  (lex_13_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4927) = lexBefore s permutation13 253 := by
  exact (positive_lex_of_descriptor s 4927 permutation13 254 (by rfl)).trans ((lex_skipped s permutation13 253 254 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation13 253) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation13 253 by rw [image13_eq]; rfl))

theorem lex_13_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4928) (Sat.Literal.pos 4927) (Sat.Literal.pos 253) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation13 253 (assignment s)
    (Sat.Literal.pos 4928) (Sat.Literal.pos 4927) (Sat.Literal.pos 253) (Sat.Literal.pos 254) (positive_of_descriptor s 4928 (.lex permutation13 253) (by rfl)) (lex_13_253_prefix s) (positive_select s 253) (lex_13_253_image s)

theorem lex_13_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4927), (Sat.Literal.pos 253), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation13 253 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4927) (Sat.Literal.pos 253) (Sat.Literal.pos 254) (lex_13_253_prefix s) (positive_select s 253) (lex_13_253_image s)

theorem lex_13_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4928), (Sat.Literal.pos 4927)] :=
  (lex_13_253_gate s).prop _ (List.Mem.head _)

theorem lex_13_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4928), (Sat.Literal.neg 253), (Sat.Literal.pos 254)] :=
  (lex_13_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4928), (Sat.Literal.pos 253), (Sat.Literal.neg 254)] :=
  (lex_13_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4927), (Sat.Literal.neg 253), (Sat.Literal.neg 254), (Sat.Literal.pos 4928)] :=
  (lex_13_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4927), (Sat.Literal.pos 253), (Sat.Literal.pos 254), (Sat.Literal.pos 4928)] :=
  (lex_13_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4928) = lexBefore s permutation13 252 := by
  exact (positive_lex_of_descriptor s 4928 permutation13 253 (by rfl)).trans ((lex_skipped s permutation13 252 253 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation13 252) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation13 252 by rw [image13_eq]; rfl))

theorem lex_13_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4929) (Sat.Literal.pos 4928) (Sat.Literal.pos 252) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation13 252 (assignment s)
    (Sat.Literal.pos 4929) (Sat.Literal.pos 4928) (Sat.Literal.pos 252) (Sat.Literal.pos 126) (positive_of_descriptor s 4929 (.lex permutation13 252) (by rfl)) (lex_13_252_prefix s) (positive_select s 252) (lex_13_252_image s)

theorem lex_13_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4928), (Sat.Literal.pos 252), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation13 252 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4928) (Sat.Literal.pos 252) (Sat.Literal.pos 126) (lex_13_252_prefix s) (positive_select s 252) (lex_13_252_image s)

theorem lex_13_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4929), (Sat.Literal.pos 4928)] :=
  (lex_13_252_gate s).prop _ (List.Mem.head _)

theorem lex_13_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4929), (Sat.Literal.neg 252), (Sat.Literal.pos 126)] :=
  (lex_13_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4929), (Sat.Literal.pos 252), (Sat.Literal.neg 126)] :=
  (lex_13_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4928), (Sat.Literal.neg 252), (Sat.Literal.neg 126), (Sat.Literal.pos 4929)] :=
  (lex_13_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4928), (Sat.Literal.pos 252), (Sat.Literal.pos 126), (Sat.Literal.pos 4929)] :=
  (lex_13_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4929) = lexBefore s permutation13 251 := by
  exact (positive_lex_of_descriptor s 4929 permutation13 252 (by rfl)).trans ((lex_skipped s permutation13 251 252 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation13 251) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation13 251 by rw [image13_eq]; rfl))

theorem lex_13_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4930) (Sat.Literal.pos 4929) (Sat.Literal.pos 251) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation13 251 (assignment s)
    (Sat.Literal.pos 4930) (Sat.Literal.pos 4929) (Sat.Literal.pos 251) (Sat.Literal.pos 253) (positive_of_descriptor s 4930 (.lex permutation13 251) (by rfl)) (lex_13_251_prefix s) (positive_select s 251) (lex_13_251_image s)

theorem lex_13_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4929), (Sat.Literal.pos 251), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation13 251 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4929) (Sat.Literal.pos 251) (Sat.Literal.pos 253) (lex_13_251_prefix s) (positive_select s 251) (lex_13_251_image s)

theorem lex_13_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4930), (Sat.Literal.pos 4929)] :=
  (lex_13_251_gate s).prop _ (List.Mem.head _)

theorem lex_13_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4930), (Sat.Literal.neg 251), (Sat.Literal.pos 253)] :=
  (lex_13_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4930), (Sat.Literal.pos 251), (Sat.Literal.neg 253)] :=
  (lex_13_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4929), (Sat.Literal.neg 251), (Sat.Literal.neg 253), (Sat.Literal.pos 4930)] :=
  (lex_13_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4929), (Sat.Literal.pos 251), (Sat.Literal.pos 253), (Sat.Literal.pos 4930)] :=
  (lex_13_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4930) = lexBefore s permutation13 250 := by
  exact (positive_lex_of_descriptor s 4930 permutation13 251 (by rfl)).trans ((lex_skipped s permutation13 250 251 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation13 250) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation13 250 by rw [image13_eq]; rfl))

theorem lex_13_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4931) (Sat.Literal.pos 4930) (Sat.Literal.pos 250) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation13 250 (assignment s)
    (Sat.Literal.pos 4931) (Sat.Literal.pos 4930) (Sat.Literal.pos 250) (Sat.Literal.pos 125) (positive_of_descriptor s 4931 (.lex permutation13 250) (by rfl)) (lex_13_250_prefix s) (positive_select s 250) (lex_13_250_image s)

theorem lex_13_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4930), (Sat.Literal.pos 250), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation13 250 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4930) (Sat.Literal.pos 250) (Sat.Literal.pos 125) (lex_13_250_prefix s) (positive_select s 250) (lex_13_250_image s)

theorem lex_13_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4931), (Sat.Literal.pos 4930)] :=
  (lex_13_250_gate s).prop _ (List.Mem.head _)

theorem lex_13_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4931), (Sat.Literal.neg 250), (Sat.Literal.pos 125)] :=
  (lex_13_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4931), (Sat.Literal.pos 250), (Sat.Literal.neg 125)] :=
  (lex_13_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4930), (Sat.Literal.neg 250), (Sat.Literal.neg 125), (Sat.Literal.pos 4931)] :=
  (lex_13_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4930), (Sat.Literal.pos 250), (Sat.Literal.pos 125), (Sat.Literal.pos 4931)] :=
  (lex_13_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4931) = lexBefore s permutation13 249 := by
  exact (positive_lex_of_descriptor s 4931 permutation13 250 (by rfl)).trans ((lex_skipped s permutation13 249 250 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation13 249) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation13 249 by rw [image13_eq]; rfl))

theorem lex_13_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4932) (Sat.Literal.pos 4931) (Sat.Literal.pos 249) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation13 249 (assignment s)
    (Sat.Literal.pos 4932) (Sat.Literal.pos 4931) (Sat.Literal.pos 249) (Sat.Literal.pos 252) (positive_of_descriptor s 4932 (.lex permutation13 249) (by rfl)) (lex_13_249_prefix s) (positive_select s 249) (lex_13_249_image s)

theorem lex_13_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4931), (Sat.Literal.pos 249), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation13 249 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4931) (Sat.Literal.pos 249) (Sat.Literal.pos 252) (lex_13_249_prefix s) (positive_select s 249) (lex_13_249_image s)

theorem lex_13_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4932), (Sat.Literal.pos 4931)] :=
  (lex_13_249_gate s).prop _ (List.Mem.head _)

theorem lex_13_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4932), (Sat.Literal.neg 249), (Sat.Literal.pos 252)] :=
  (lex_13_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4932), (Sat.Literal.pos 249), (Sat.Literal.neg 252)] :=
  (lex_13_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4931), (Sat.Literal.neg 249), (Sat.Literal.neg 252), (Sat.Literal.pos 4932)] :=
  (lex_13_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4931), (Sat.Literal.pos 249), (Sat.Literal.pos 252), (Sat.Literal.pos 4932)] :=
  (lex_13_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4932) = lexBefore s permutation13 248 := by
  exact (positive_lex_of_descriptor s 4932 permutation13 249 (by rfl)).trans ((lex_skipped s permutation13 248 249 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation13 248) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation13 248 by rw [image13_eq]; rfl))

theorem lex_13_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4933) (Sat.Literal.pos 4932) (Sat.Literal.pos 248) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation13 248 (assignment s)
    (Sat.Literal.pos 4933) (Sat.Literal.pos 4932) (Sat.Literal.pos 248) (Sat.Literal.pos 124) (positive_of_descriptor s 4933 (.lex permutation13 248) (by rfl)) (lex_13_248_prefix s) (positive_select s 248) (lex_13_248_image s)

theorem lex_13_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4932), (Sat.Literal.pos 248), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation13 248 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4932) (Sat.Literal.pos 248) (Sat.Literal.pos 124) (lex_13_248_prefix s) (positive_select s 248) (lex_13_248_image s)

theorem lex_13_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4933), (Sat.Literal.pos 4932)] :=
  (lex_13_248_gate s).prop _ (List.Mem.head _)

theorem lex_13_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4933), (Sat.Literal.neg 248), (Sat.Literal.pos 124)] :=
  (lex_13_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4933), (Sat.Literal.pos 248), (Sat.Literal.neg 124)] :=
  (lex_13_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4932), (Sat.Literal.neg 248), (Sat.Literal.neg 124), (Sat.Literal.pos 4933)] :=
  (lex_13_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4932), (Sat.Literal.pos 248), (Sat.Literal.pos 124), (Sat.Literal.pos 4933)] :=
  (lex_13_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4933) = lexBefore s permutation13 247 := by
  exact (positive_lex_of_descriptor s 4933 permutation13 248 (by rfl)).trans ((lex_skipped s permutation13 247 248 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation13 247) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation13 247 by rw [image13_eq]; rfl))

theorem lex_13_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4934) (Sat.Literal.pos 4933) (Sat.Literal.pos 247) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation13 247 (assignment s)
    (Sat.Literal.pos 4934) (Sat.Literal.pos 4933) (Sat.Literal.pos 247) (Sat.Literal.pos 251) (positive_of_descriptor s 4934 (.lex permutation13 247) (by rfl)) (lex_13_247_prefix s) (positive_select s 247) (lex_13_247_image s)

theorem lex_13_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4933), (Sat.Literal.pos 247), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation13 247 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4933) (Sat.Literal.pos 247) (Sat.Literal.pos 251) (lex_13_247_prefix s) (positive_select s 247) (lex_13_247_image s)

theorem lex_13_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4934), (Sat.Literal.pos 4933)] :=
  (lex_13_247_gate s).prop _ (List.Mem.head _)

theorem lex_13_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4934), (Sat.Literal.neg 247), (Sat.Literal.pos 251)] :=
  (lex_13_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4934), (Sat.Literal.pos 247), (Sat.Literal.neg 251)] :=
  (lex_13_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4933), (Sat.Literal.neg 247), (Sat.Literal.neg 251), (Sat.Literal.pos 4934)] :=
  (lex_13_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4933), (Sat.Literal.pos 247), (Sat.Literal.pos 251), (Sat.Literal.pos 4934)] :=
  (lex_13_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4934) = lexBefore s permutation13 246 := by
  exact (positive_lex_of_descriptor s 4934 permutation13 247 (by rfl)).trans ((lex_skipped s permutation13 246 247 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation13 246) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation13 246 by rw [image13_eq]; rfl))

theorem lex_13_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4935) (Sat.Literal.pos 4934) (Sat.Literal.pos 246) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation13 246 (assignment s)
    (Sat.Literal.pos 4935) (Sat.Literal.pos 4934) (Sat.Literal.pos 246) (Sat.Literal.pos 123) (positive_of_descriptor s 4935 (.lex permutation13 246) (by rfl)) (lex_13_246_prefix s) (positive_select s 246) (lex_13_246_image s)

theorem lex_13_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4934), (Sat.Literal.pos 246), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation13 246 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4934) (Sat.Literal.pos 246) (Sat.Literal.pos 123) (lex_13_246_prefix s) (positive_select s 246) (lex_13_246_image s)

theorem lex_13_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4935), (Sat.Literal.pos 4934)] :=
  (lex_13_246_gate s).prop _ (List.Mem.head _)

theorem lex_13_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4935), (Sat.Literal.neg 246), (Sat.Literal.pos 123)] :=
  (lex_13_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4935), (Sat.Literal.pos 246), (Sat.Literal.neg 123)] :=
  (lex_13_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4934), (Sat.Literal.neg 246), (Sat.Literal.neg 123), (Sat.Literal.pos 4935)] :=
  (lex_13_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4934), (Sat.Literal.pos 246), (Sat.Literal.pos 123), (Sat.Literal.pos 4935)] :=
  (lex_13_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4935) = lexBefore s permutation13 245 := by
  exact (positive_lex_of_descriptor s 4935 permutation13 246 (by rfl)).trans ((lex_skipped s permutation13 245 246 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation13 245) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation13 245 by rw [image13_eq]; rfl))

theorem lex_13_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4936) (Sat.Literal.pos 4935) (Sat.Literal.pos 245) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation13 245 (assignment s)
    (Sat.Literal.pos 4936) (Sat.Literal.pos 4935) (Sat.Literal.pos 245) (Sat.Literal.pos 250) (positive_of_descriptor s 4936 (.lex permutation13 245) (by rfl)) (lex_13_245_prefix s) (positive_select s 245) (lex_13_245_image s)

theorem lex_13_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4935), (Sat.Literal.pos 245), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation13 245 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4935) (Sat.Literal.pos 245) (Sat.Literal.pos 250) (lex_13_245_prefix s) (positive_select s 245) (lex_13_245_image s)

theorem lex_13_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4936), (Sat.Literal.pos 4935)] :=
  (lex_13_245_gate s).prop _ (List.Mem.head _)

theorem lex_13_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4936), (Sat.Literal.neg 245), (Sat.Literal.pos 250)] :=
  (lex_13_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4936), (Sat.Literal.pos 245), (Sat.Literal.neg 250)] :=
  (lex_13_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4935), (Sat.Literal.neg 245), (Sat.Literal.neg 250), (Sat.Literal.pos 4936)] :=
  (lex_13_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4935), (Sat.Literal.pos 245), (Sat.Literal.pos 250), (Sat.Literal.pos 4936)] :=
  (lex_13_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4936) = lexBefore s permutation13 244 := by
  exact (positive_lex_of_descriptor s 4936 permutation13 245 (by rfl)).trans ((lex_skipped s permutation13 244 245 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation13 244) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation13 244 by rw [image13_eq]; rfl))

theorem lex_13_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4937) (Sat.Literal.pos 4936) (Sat.Literal.pos 244) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation13 244 (assignment s)
    (Sat.Literal.pos 4937) (Sat.Literal.pos 4936) (Sat.Literal.pos 244) (Sat.Literal.pos 122) (positive_of_descriptor s 4937 (.lex permutation13 244) (by rfl)) (lex_13_244_prefix s) (positive_select s 244) (lex_13_244_image s)

theorem lex_13_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4936), (Sat.Literal.pos 244), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation13 244 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4936) (Sat.Literal.pos 244) (Sat.Literal.pos 122) (lex_13_244_prefix s) (positive_select s 244) (lex_13_244_image s)

theorem lex_13_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4937), (Sat.Literal.pos 4936)] :=
  (lex_13_244_gate s).prop _ (List.Mem.head _)

theorem lex_13_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4937), (Sat.Literal.neg 244), (Sat.Literal.pos 122)] :=
  (lex_13_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4937), (Sat.Literal.pos 244), (Sat.Literal.neg 122)] :=
  (lex_13_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4936), (Sat.Literal.neg 244), (Sat.Literal.neg 122), (Sat.Literal.pos 4937)] :=
  (lex_13_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4936), (Sat.Literal.pos 244), (Sat.Literal.pos 122), (Sat.Literal.pos 4937)] :=
  (lex_13_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4937) = lexBefore s permutation13 243 := by
  exact (positive_lex_of_descriptor s 4937 permutation13 244 (by rfl)).trans ((lex_skipped s permutation13 243 244 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation13 243) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation13 243 by rw [image13_eq]; rfl))

theorem lex_13_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4938) (Sat.Literal.pos 4937) (Sat.Literal.pos 243) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation13 243 (assignment s)
    (Sat.Literal.pos 4938) (Sat.Literal.pos 4937) (Sat.Literal.pos 243) (Sat.Literal.pos 249) (positive_of_descriptor s 4938 (.lex permutation13 243) (by rfl)) (lex_13_243_prefix s) (positive_select s 243) (lex_13_243_image s)

theorem lex_13_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4937), (Sat.Literal.pos 243), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation13 243 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4937) (Sat.Literal.pos 243) (Sat.Literal.pos 249) (lex_13_243_prefix s) (positive_select s 243) (lex_13_243_image s)

theorem lex_13_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4938), (Sat.Literal.pos 4937)] :=
  (lex_13_243_gate s).prop _ (List.Mem.head _)

theorem lex_13_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4938), (Sat.Literal.neg 243), (Sat.Literal.pos 249)] :=
  (lex_13_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4938), (Sat.Literal.pos 243), (Sat.Literal.neg 249)] :=
  (lex_13_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4937), (Sat.Literal.neg 243), (Sat.Literal.neg 249), (Sat.Literal.pos 4938)] :=
  (lex_13_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4937), (Sat.Literal.pos 243), (Sat.Literal.pos 249), (Sat.Literal.pos 4938)] :=
  (lex_13_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4938) = lexBefore s permutation13 242 := by
  exact (positive_lex_of_descriptor s 4938 permutation13 243 (by rfl)).trans ((lex_skipped s permutation13 242 243 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation13 242) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation13 242 by rw [image13_eq]; rfl))

theorem lex_13_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4939) (Sat.Literal.pos 4938) (Sat.Literal.pos 242) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation13 242 (assignment s)
    (Sat.Literal.pos 4939) (Sat.Literal.pos 4938) (Sat.Literal.pos 242) (Sat.Literal.pos 121) (positive_of_descriptor s 4939 (.lex permutation13 242) (by rfl)) (lex_13_242_prefix s) (positive_select s 242) (lex_13_242_image s)

theorem lex_13_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4938), (Sat.Literal.pos 242), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation13 242 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4938) (Sat.Literal.pos 242) (Sat.Literal.pos 121) (lex_13_242_prefix s) (positive_select s 242) (lex_13_242_image s)

theorem lex_13_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4939), (Sat.Literal.pos 4938)] :=
  (lex_13_242_gate s).prop _ (List.Mem.head _)

theorem lex_13_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4939), (Sat.Literal.neg 242), (Sat.Literal.pos 121)] :=
  (lex_13_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4939), (Sat.Literal.pos 242), (Sat.Literal.neg 121)] :=
  (lex_13_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4938), (Sat.Literal.neg 242), (Sat.Literal.neg 121), (Sat.Literal.pos 4939)] :=
  (lex_13_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4938), (Sat.Literal.pos 242), (Sat.Literal.pos 121), (Sat.Literal.pos 4939)] :=
  (lex_13_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4939) = lexBefore s permutation13 241 := by
  exact (positive_lex_of_descriptor s 4939 permutation13 242 (by rfl)).trans ((lex_skipped s permutation13 241 242 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation13 241) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation13 241 by rw [image13_eq]; rfl))

theorem lex_13_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4940) (Sat.Literal.pos 4939) (Sat.Literal.pos 241) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation13 241 (assignment s)
    (Sat.Literal.pos 4940) (Sat.Literal.pos 4939) (Sat.Literal.pos 241) (Sat.Literal.pos 248) (positive_of_descriptor s 4940 (.lex permutation13 241) (by rfl)) (lex_13_241_prefix s) (positive_select s 241) (lex_13_241_image s)

theorem lex_13_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4939), (Sat.Literal.pos 241), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation13 241 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4939) (Sat.Literal.pos 241) (Sat.Literal.pos 248) (lex_13_241_prefix s) (positive_select s 241) (lex_13_241_image s)

theorem lex_13_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4940), (Sat.Literal.pos 4939)] :=
  (lex_13_241_gate s).prop _ (List.Mem.head _)

theorem lex_13_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4940), (Sat.Literal.neg 241), (Sat.Literal.pos 248)] :=
  (lex_13_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4940), (Sat.Literal.pos 241), (Sat.Literal.neg 248)] :=
  (lex_13_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4939), (Sat.Literal.neg 241), (Sat.Literal.neg 248), (Sat.Literal.pos 4940)] :=
  (lex_13_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4939), (Sat.Literal.pos 241), (Sat.Literal.pos 248), (Sat.Literal.pos 4940)] :=
  (lex_13_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4940) = lexBefore s permutation13 240 := by
  exact (positive_lex_of_descriptor s 4940 permutation13 241 (by rfl)).trans ((lex_skipped s permutation13 240 241 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation13 240) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation13 240 by rw [image13_eq]; rfl))

theorem lex_13_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4941) (Sat.Literal.pos 4940) (Sat.Literal.pos 240) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation13 240 (assignment s)
    (Sat.Literal.pos 4941) (Sat.Literal.pos 4940) (Sat.Literal.pos 240) (Sat.Literal.pos 120) (positive_of_descriptor s 4941 (.lex permutation13 240) (by rfl)) (lex_13_240_prefix s) (positive_select s 240) (lex_13_240_image s)

theorem lex_13_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4940), (Sat.Literal.pos 240), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation13 240 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4940) (Sat.Literal.pos 240) (Sat.Literal.pos 120) (lex_13_240_prefix s) (positive_select s 240) (lex_13_240_image s)

theorem lex_13_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4941), (Sat.Literal.pos 4940)] :=
  (lex_13_240_gate s).prop _ (List.Mem.head _)

theorem lex_13_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4941), (Sat.Literal.neg 240), (Sat.Literal.pos 120)] :=
  (lex_13_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4941), (Sat.Literal.pos 240), (Sat.Literal.neg 120)] :=
  (lex_13_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4940), (Sat.Literal.neg 240), (Sat.Literal.neg 120), (Sat.Literal.pos 4941)] :=
  (lex_13_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4940), (Sat.Literal.pos 240), (Sat.Literal.pos 120), (Sat.Literal.pos 4941)] :=
  (lex_13_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4941) = lexBefore s permutation13 239 := by
  exact (positive_lex_of_descriptor s 4941 permutation13 240 (by rfl)).trans ((lex_skipped s permutation13 239 240 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation13 239) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation13 239 by rw [image13_eq]; rfl))

theorem lex_13_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4942) (Sat.Literal.pos 4941) (Sat.Literal.pos 239) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation13 239 (assignment s)
    (Sat.Literal.pos 4942) (Sat.Literal.pos 4941) (Sat.Literal.pos 239) (Sat.Literal.pos 247) (positive_of_descriptor s 4942 (.lex permutation13 239) (by rfl)) (lex_13_239_prefix s) (positive_select s 239) (lex_13_239_image s)

theorem lex_13_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4941), (Sat.Literal.pos 239), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation13 239 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4941) (Sat.Literal.pos 239) (Sat.Literal.pos 247) (lex_13_239_prefix s) (positive_select s 239) (lex_13_239_image s)

theorem lex_13_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4942), (Sat.Literal.pos 4941)] :=
  (lex_13_239_gate s).prop _ (List.Mem.head _)

theorem lex_13_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4942), (Sat.Literal.neg 239), (Sat.Literal.pos 247)] :=
  (lex_13_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4942), (Sat.Literal.pos 239), (Sat.Literal.neg 247)] :=
  (lex_13_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4941), (Sat.Literal.neg 239), (Sat.Literal.neg 247), (Sat.Literal.pos 4942)] :=
  (lex_13_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4941), (Sat.Literal.pos 239), (Sat.Literal.pos 247), (Sat.Literal.pos 4942)] :=
  (lex_13_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4942) = lexBefore s permutation13 238 := by
  exact (positive_lex_of_descriptor s 4942 permutation13 239 (by rfl)).trans ((lex_skipped s permutation13 238 239 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation13 238) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation13 238 by rw [image13_eq]; rfl))

theorem lex_13_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4943) (Sat.Literal.pos 4942) (Sat.Literal.pos 238) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation13 238 (assignment s)
    (Sat.Literal.pos 4943) (Sat.Literal.pos 4942) (Sat.Literal.pos 238) (Sat.Literal.pos 119) (positive_of_descriptor s 4943 (.lex permutation13 238) (by rfl)) (lex_13_238_prefix s) (positive_select s 238) (lex_13_238_image s)

theorem lex_13_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4942), (Sat.Literal.pos 238), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation13 238 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4942) (Sat.Literal.pos 238) (Sat.Literal.pos 119) (lex_13_238_prefix s) (positive_select s 238) (lex_13_238_image s)

theorem lex_13_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4943), (Sat.Literal.pos 4942)] :=
  (lex_13_238_gate s).prop _ (List.Mem.head _)

theorem lex_13_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4943), (Sat.Literal.neg 238), (Sat.Literal.pos 119)] :=
  (lex_13_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4943), (Sat.Literal.pos 238), (Sat.Literal.neg 119)] :=
  (lex_13_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4942), (Sat.Literal.neg 238), (Sat.Literal.neg 119), (Sat.Literal.pos 4943)] :=
  (lex_13_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4942), (Sat.Literal.pos 238), (Sat.Literal.pos 119), (Sat.Literal.pos 4943)] :=
  (lex_13_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4943) = lexBefore s permutation13 237 := by
  exact (positive_lex_of_descriptor s 4943 permutation13 238 (by rfl)).trans ((lex_skipped s permutation13 237 238 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation13 237) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation13 237 by rw [image13_eq]; rfl))

theorem lex_13_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4944) (Sat.Literal.pos 4943) (Sat.Literal.pos 237) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation13 237 (assignment s)
    (Sat.Literal.pos 4944) (Sat.Literal.pos 4943) (Sat.Literal.pos 237) (Sat.Literal.pos 246) (positive_of_descriptor s 4944 (.lex permutation13 237) (by rfl)) (lex_13_237_prefix s) (positive_select s 237) (lex_13_237_image s)

theorem lex_13_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4943), (Sat.Literal.pos 237), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation13 237 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4943) (Sat.Literal.pos 237) (Sat.Literal.pos 246) (lex_13_237_prefix s) (positive_select s 237) (lex_13_237_image s)

theorem lex_13_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4944), (Sat.Literal.pos 4943)] :=
  (lex_13_237_gate s).prop _ (List.Mem.head _)

theorem lex_13_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4944), (Sat.Literal.neg 237), (Sat.Literal.pos 246)] :=
  (lex_13_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4944), (Sat.Literal.pos 237), (Sat.Literal.neg 246)] :=
  (lex_13_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4943), (Sat.Literal.neg 237), (Sat.Literal.neg 246), (Sat.Literal.pos 4944)] :=
  (lex_13_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4943), (Sat.Literal.pos 237), (Sat.Literal.pos 246), (Sat.Literal.pos 4944)] :=
  (lex_13_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4944) = lexBefore s permutation13 236 := by
  exact (positive_lex_of_descriptor s 4944 permutation13 237 (by rfl)).trans ((lex_skipped s permutation13 236 237 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation13 236) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation13 236 by rw [image13_eq]; rfl))

theorem lex_13_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4945) (Sat.Literal.pos 4944) (Sat.Literal.pos 236) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation13 236 (assignment s)
    (Sat.Literal.pos 4945) (Sat.Literal.pos 4944) (Sat.Literal.pos 236) (Sat.Literal.pos 118) (positive_of_descriptor s 4945 (.lex permutation13 236) (by rfl)) (lex_13_236_prefix s) (positive_select s 236) (lex_13_236_image s)

theorem lex_13_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4944), (Sat.Literal.pos 236), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation13 236 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4944) (Sat.Literal.pos 236) (Sat.Literal.pos 118) (lex_13_236_prefix s) (positive_select s 236) (lex_13_236_image s)

theorem lex_13_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4945), (Sat.Literal.pos 4944)] :=
  (lex_13_236_gate s).prop _ (List.Mem.head _)

theorem lex_13_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4945), (Sat.Literal.neg 236), (Sat.Literal.pos 118)] :=
  (lex_13_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4945), (Sat.Literal.pos 236), (Sat.Literal.neg 118)] :=
  (lex_13_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4944), (Sat.Literal.neg 236), (Sat.Literal.neg 118), (Sat.Literal.pos 4945)] :=
  (lex_13_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4944), (Sat.Literal.pos 236), (Sat.Literal.pos 118), (Sat.Literal.pos 4945)] :=
  (lex_13_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4945) = lexBefore s permutation13 235 := by
  exact (positive_lex_of_descriptor s 4945 permutation13 236 (by rfl)).trans ((lex_skipped s permutation13 235 236 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation13 235) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation13 235 by rw [image13_eq]; rfl))

theorem lex_13_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4946) (Sat.Literal.pos 4945) (Sat.Literal.pos 235) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation13 235 (assignment s)
    (Sat.Literal.pos 4946) (Sat.Literal.pos 4945) (Sat.Literal.pos 235) (Sat.Literal.pos 245) (positive_of_descriptor s 4946 (.lex permutation13 235) (by rfl)) (lex_13_235_prefix s) (positive_select s 235) (lex_13_235_image s)

theorem lex_13_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4945), (Sat.Literal.pos 235), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation13 235 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4945) (Sat.Literal.pos 235) (Sat.Literal.pos 245) (lex_13_235_prefix s) (positive_select s 235) (lex_13_235_image s)

theorem lex_13_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4946), (Sat.Literal.pos 4945)] :=
  (lex_13_235_gate s).prop _ (List.Mem.head _)

theorem lex_13_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4946), (Sat.Literal.neg 235), (Sat.Literal.pos 245)] :=
  (lex_13_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4946), (Sat.Literal.pos 235), (Sat.Literal.neg 245)] :=
  (lex_13_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4945), (Sat.Literal.neg 235), (Sat.Literal.neg 245), (Sat.Literal.pos 4946)] :=
  (lex_13_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4945), (Sat.Literal.pos 235), (Sat.Literal.pos 245), (Sat.Literal.pos 4946)] :=
  (lex_13_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4946) = lexBefore s permutation13 234 := by
  exact (positive_lex_of_descriptor s 4946 permutation13 235 (by rfl)).trans ((lex_skipped s permutation13 234 235 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation13 234) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation13 234 by rw [image13_eq]; rfl))

theorem lex_13_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4947) (Sat.Literal.pos 4946) (Sat.Literal.pos 234) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation13 234 (assignment s)
    (Sat.Literal.pos 4947) (Sat.Literal.pos 4946) (Sat.Literal.pos 234) (Sat.Literal.pos 117) (positive_of_descriptor s 4947 (.lex permutation13 234) (by rfl)) (lex_13_234_prefix s) (positive_select s 234) (lex_13_234_image s)

theorem lex_13_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4946), (Sat.Literal.pos 234), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation13 234 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4946) (Sat.Literal.pos 234) (Sat.Literal.pos 117) (lex_13_234_prefix s) (positive_select s 234) (lex_13_234_image s)

theorem lex_13_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4947), (Sat.Literal.pos 4946)] :=
  (lex_13_234_gate s).prop _ (List.Mem.head _)

theorem lex_13_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4947), (Sat.Literal.neg 234), (Sat.Literal.pos 117)] :=
  (lex_13_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4947), (Sat.Literal.pos 234), (Sat.Literal.neg 117)] :=
  (lex_13_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4946), (Sat.Literal.neg 234), (Sat.Literal.neg 117), (Sat.Literal.pos 4947)] :=
  (lex_13_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4946), (Sat.Literal.pos 234), (Sat.Literal.pos 117), (Sat.Literal.pos 4947)] :=
  (lex_13_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4947) = lexBefore s permutation13 233 := by
  exact (positive_lex_of_descriptor s 4947 permutation13 234 (by rfl)).trans ((lex_skipped s permutation13 233 234 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation13 233) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation13 233 by rw [image13_eq]; rfl))

theorem lex_13_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4948) (Sat.Literal.pos 4947) (Sat.Literal.pos 233) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation13 233 (assignment s)
    (Sat.Literal.pos 4948) (Sat.Literal.pos 4947) (Sat.Literal.pos 233) (Sat.Literal.pos 244) (positive_of_descriptor s 4948 (.lex permutation13 233) (by rfl)) (lex_13_233_prefix s) (positive_select s 233) (lex_13_233_image s)

theorem lex_13_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4947), (Sat.Literal.pos 233), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation13 233 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4947) (Sat.Literal.pos 233) (Sat.Literal.pos 244) (lex_13_233_prefix s) (positive_select s 233) (lex_13_233_image s)

theorem lex_13_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4948), (Sat.Literal.pos 4947)] :=
  (lex_13_233_gate s).prop _ (List.Mem.head _)

theorem lex_13_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4948), (Sat.Literal.neg 233), (Sat.Literal.pos 244)] :=
  (lex_13_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4948), (Sat.Literal.pos 233), (Sat.Literal.neg 244)] :=
  (lex_13_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4947), (Sat.Literal.neg 233), (Sat.Literal.neg 244), (Sat.Literal.pos 4948)] :=
  (lex_13_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4947), (Sat.Literal.pos 233), (Sat.Literal.pos 244), (Sat.Literal.pos 4948)] :=
  (lex_13_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4948) = lexBefore s permutation13 232 := by
  exact (positive_lex_of_descriptor s 4948 permutation13 233 (by rfl)).trans ((lex_skipped s permutation13 232 233 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation13 232) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation13 232 by rw [image13_eq]; rfl))

theorem lex_13_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4949) (Sat.Literal.pos 4948) (Sat.Literal.pos 232) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation13 232 (assignment s)
    (Sat.Literal.pos 4949) (Sat.Literal.pos 4948) (Sat.Literal.pos 232) (Sat.Literal.pos 116) (positive_of_descriptor s 4949 (.lex permutation13 232) (by rfl)) (lex_13_232_prefix s) (positive_select s 232) (lex_13_232_image s)

theorem lex_13_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4948), (Sat.Literal.pos 232), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation13 232 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4948) (Sat.Literal.pos 232) (Sat.Literal.pos 116) (lex_13_232_prefix s) (positive_select s 232) (lex_13_232_image s)

theorem lex_13_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4949), (Sat.Literal.pos 4948)] :=
  (lex_13_232_gate s).prop _ (List.Mem.head _)

theorem lex_13_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4949), (Sat.Literal.neg 232), (Sat.Literal.pos 116)] :=
  (lex_13_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4949), (Sat.Literal.pos 232), (Sat.Literal.neg 116)] :=
  (lex_13_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4948), (Sat.Literal.neg 232), (Sat.Literal.neg 116), (Sat.Literal.pos 4949)] :=
  (lex_13_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4948), (Sat.Literal.pos 232), (Sat.Literal.pos 116), (Sat.Literal.pos 4949)] :=
  (lex_13_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4949) = lexBefore s permutation13 231 := by
  exact (positive_lex_of_descriptor s 4949 permutation13 232 (by rfl)).trans ((lex_skipped s permutation13 231 232 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation13 231) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation13 231 by rw [image13_eq]; rfl))

theorem lex_13_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4950) (Sat.Literal.pos 4949) (Sat.Literal.pos 231) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation13 231 (assignment s)
    (Sat.Literal.pos 4950) (Sat.Literal.pos 4949) (Sat.Literal.pos 231) (Sat.Literal.pos 243) (positive_of_descriptor s 4950 (.lex permutation13 231) (by rfl)) (lex_13_231_prefix s) (positive_select s 231) (lex_13_231_image s)

theorem lex_13_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4949), (Sat.Literal.pos 231), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation13 231 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4949) (Sat.Literal.pos 231) (Sat.Literal.pos 243) (lex_13_231_prefix s) (positive_select s 231) (lex_13_231_image s)

theorem lex_13_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4950), (Sat.Literal.pos 4949)] :=
  (lex_13_231_gate s).prop _ (List.Mem.head _)

theorem lex_13_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4950), (Sat.Literal.neg 231), (Sat.Literal.pos 243)] :=
  (lex_13_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4950), (Sat.Literal.pos 231), (Sat.Literal.neg 243)] :=
  (lex_13_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4949), (Sat.Literal.neg 231), (Sat.Literal.neg 243), (Sat.Literal.pos 4950)] :=
  (lex_13_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4949), (Sat.Literal.pos 231), (Sat.Literal.pos 243), (Sat.Literal.pos 4950)] :=
  (lex_13_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4950) = lexBefore s permutation13 230 := by
  exact (positive_lex_of_descriptor s 4950 permutation13 231 (by rfl)).trans ((lex_skipped s permutation13 230 231 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation13 230) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation13 230 by rw [image13_eq]; rfl))

theorem lex_13_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4951) (Sat.Literal.pos 4950) (Sat.Literal.pos 230) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation13 230 (assignment s)
    (Sat.Literal.pos 4951) (Sat.Literal.pos 4950) (Sat.Literal.pos 230) (Sat.Literal.pos 115) (positive_of_descriptor s 4951 (.lex permutation13 230) (by rfl)) (lex_13_230_prefix s) (positive_select s 230) (lex_13_230_image s)

theorem lex_13_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4950), (Sat.Literal.pos 230), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation13 230 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4950) (Sat.Literal.pos 230) (Sat.Literal.pos 115) (lex_13_230_prefix s) (positive_select s 230) (lex_13_230_image s)

theorem lex_13_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4951), (Sat.Literal.pos 4950)] :=
  (lex_13_230_gate s).prop _ (List.Mem.head _)

theorem lex_13_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4951), (Sat.Literal.neg 230), (Sat.Literal.pos 115)] :=
  (lex_13_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4951), (Sat.Literal.pos 230), (Sat.Literal.neg 115)] :=
  (lex_13_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4950), (Sat.Literal.neg 230), (Sat.Literal.neg 115), (Sat.Literal.pos 4951)] :=
  (lex_13_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4950), (Sat.Literal.pos 230), (Sat.Literal.pos 115), (Sat.Literal.pos 4951)] :=
  (lex_13_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4951) = lexBefore s permutation13 229 := by
  exact (positive_lex_of_descriptor s 4951 permutation13 230 (by rfl)).trans ((lex_skipped s permutation13 229 230 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation13 229) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation13 229 by rw [image13_eq]; rfl))

theorem lex_13_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4952) (Sat.Literal.pos 4951) (Sat.Literal.pos 229) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation13 229 (assignment s)
    (Sat.Literal.pos 4952) (Sat.Literal.pos 4951) (Sat.Literal.pos 229) (Sat.Literal.pos 242) (positive_of_descriptor s 4952 (.lex permutation13 229) (by rfl)) (lex_13_229_prefix s) (positive_select s 229) (lex_13_229_image s)

theorem lex_13_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4951), (Sat.Literal.pos 229), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation13 229 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4951) (Sat.Literal.pos 229) (Sat.Literal.pos 242) (lex_13_229_prefix s) (positive_select s 229) (lex_13_229_image s)

theorem lex_13_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4952), (Sat.Literal.pos 4951)] :=
  (lex_13_229_gate s).prop _ (List.Mem.head _)

theorem lex_13_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4952), (Sat.Literal.neg 229), (Sat.Literal.pos 242)] :=
  (lex_13_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4952), (Sat.Literal.pos 229), (Sat.Literal.neg 242)] :=
  (lex_13_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4951), (Sat.Literal.neg 229), (Sat.Literal.neg 242), (Sat.Literal.pos 4952)] :=
  (lex_13_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4951), (Sat.Literal.pos 229), (Sat.Literal.pos 242), (Sat.Literal.pos 4952)] :=
  (lex_13_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4952) = lexBefore s permutation13 228 := by
  exact (positive_lex_of_descriptor s 4952 permutation13 229 (by rfl)).trans ((lex_skipped s permutation13 228 229 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation13 228) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation13 228 by rw [image13_eq]; rfl))

theorem lex_13_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4953) (Sat.Literal.pos 4952) (Sat.Literal.pos 228) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation13 228 (assignment s)
    (Sat.Literal.pos 4953) (Sat.Literal.pos 4952) (Sat.Literal.pos 228) (Sat.Literal.pos 114) (positive_of_descriptor s 4953 (.lex permutation13 228) (by rfl)) (lex_13_228_prefix s) (positive_select s 228) (lex_13_228_image s)

theorem lex_13_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4952), (Sat.Literal.pos 228), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation13 228 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4952) (Sat.Literal.pos 228) (Sat.Literal.pos 114) (lex_13_228_prefix s) (positive_select s 228) (lex_13_228_image s)

theorem lex_13_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4953), (Sat.Literal.pos 4952)] :=
  (lex_13_228_gate s).prop _ (List.Mem.head _)

theorem lex_13_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4953), (Sat.Literal.neg 228), (Sat.Literal.pos 114)] :=
  (lex_13_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4953), (Sat.Literal.pos 228), (Sat.Literal.neg 114)] :=
  (lex_13_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4952), (Sat.Literal.neg 228), (Sat.Literal.neg 114), (Sat.Literal.pos 4953)] :=
  (lex_13_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4952), (Sat.Literal.pos 228), (Sat.Literal.pos 114), (Sat.Literal.pos 4953)] :=
  (lex_13_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4953) = lexBefore s permutation13 227 := by
  exact (positive_lex_of_descriptor s 4953 permutation13 228 (by rfl)).trans ((lex_skipped s permutation13 227 228 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation13 227) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation13 227 by rw [image13_eq]; rfl))

theorem lex_13_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4954) (Sat.Literal.pos 4953) (Sat.Literal.pos 227) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation13 227 (assignment s)
    (Sat.Literal.pos 4954) (Sat.Literal.pos 4953) (Sat.Literal.pos 227) (Sat.Literal.pos 241) (positive_of_descriptor s 4954 (.lex permutation13 227) (by rfl)) (lex_13_227_prefix s) (positive_select s 227) (lex_13_227_image s)

theorem lex_13_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4953), (Sat.Literal.pos 227), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation13 227 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4953) (Sat.Literal.pos 227) (Sat.Literal.pos 241) (lex_13_227_prefix s) (positive_select s 227) (lex_13_227_image s)

theorem lex_13_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4954), (Sat.Literal.pos 4953)] :=
  (lex_13_227_gate s).prop _ (List.Mem.head _)

theorem lex_13_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4954), (Sat.Literal.neg 227), (Sat.Literal.pos 241)] :=
  (lex_13_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4954), (Sat.Literal.pos 227), (Sat.Literal.neg 241)] :=
  (lex_13_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4953), (Sat.Literal.neg 227), (Sat.Literal.neg 241), (Sat.Literal.pos 4954)] :=
  (lex_13_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4953), (Sat.Literal.pos 227), (Sat.Literal.pos 241), (Sat.Literal.pos 4954)] :=
  (lex_13_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4954) = lexBefore s permutation13 226 := by
  exact (positive_lex_of_descriptor s 4954 permutation13 227 (by rfl)).trans ((lex_skipped s permutation13 226 227 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation13 226) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation13 226 by rw [image13_eq]; rfl))

theorem lex_13_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4955) (Sat.Literal.pos 4954) (Sat.Literal.pos 226) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation13 226 (assignment s)
    (Sat.Literal.pos 4955) (Sat.Literal.pos 4954) (Sat.Literal.pos 226) (Sat.Literal.pos 113) (positive_of_descriptor s 4955 (.lex permutation13 226) (by rfl)) (lex_13_226_prefix s) (positive_select s 226) (lex_13_226_image s)

theorem lex_13_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4954), (Sat.Literal.pos 226), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation13 226 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4954) (Sat.Literal.pos 226) (Sat.Literal.pos 113) (lex_13_226_prefix s) (positive_select s 226) (lex_13_226_image s)

theorem lex_13_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4955), (Sat.Literal.pos 4954)] :=
  (lex_13_226_gate s).prop _ (List.Mem.head _)

theorem lex_13_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4955), (Sat.Literal.neg 226), (Sat.Literal.pos 113)] :=
  (lex_13_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4955), (Sat.Literal.pos 226), (Sat.Literal.neg 113)] :=
  (lex_13_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4954), (Sat.Literal.neg 226), (Sat.Literal.neg 113), (Sat.Literal.pos 4955)] :=
  (lex_13_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4954), (Sat.Literal.pos 226), (Sat.Literal.pos 113), (Sat.Literal.pos 4955)] :=
  (lex_13_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4955) = lexBefore s permutation13 225 := by
  exact (positive_lex_of_descriptor s 4955 permutation13 226 (by rfl)).trans ((lex_skipped s permutation13 225 226 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 240) = s (permuteMask permutation13 225) := by
  exact (positive_select s 240).trans (congrArg s (show (240 : Fin 256) = permuteMask permutation13 225 by rw [image13_eq]; rfl))

theorem lex_13_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4956) (Sat.Literal.pos 4955) (Sat.Literal.pos 225) (Sat.Literal.pos 240)) := by
  exact equality_gate s permutation13 225 (assignment s)
    (Sat.Literal.pos 4956) (Sat.Literal.pos 4955) (Sat.Literal.pos 225) (Sat.Literal.pos 240) (positive_of_descriptor s 4956 (.lex permutation13 225) (by rfl)) (lex_13_225_prefix s) (positive_select s 225) (lex_13_225_image s)

theorem lex_13_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4955), (Sat.Literal.pos 225), (Sat.Literal.neg 240)] := by
  exact comparison_gate s permutation13 225 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4955) (Sat.Literal.pos 225) (Sat.Literal.pos 240) (lex_13_225_prefix s) (positive_select s 225) (lex_13_225_image s)

theorem lex_13_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4956), (Sat.Literal.pos 4955)] :=
  (lex_13_225_gate s).prop _ (List.Mem.head _)

theorem lex_13_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4956), (Sat.Literal.neg 225), (Sat.Literal.pos 240)] :=
  (lex_13_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4956), (Sat.Literal.pos 225), (Sat.Literal.neg 240)] :=
  (lex_13_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4955), (Sat.Literal.neg 225), (Sat.Literal.neg 240), (Sat.Literal.pos 4956)] :=
  (lex_13_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4955), (Sat.Literal.pos 225), (Sat.Literal.pos 240), (Sat.Literal.pos 4956)] :=
  (lex_13_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4956) = lexBefore s permutation13 224 := by
  exact (positive_lex_of_descriptor s 4956 permutation13 225 (by rfl)).trans ((lex_skipped s permutation13 224 225 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 112) = s (permuteMask permutation13 224) := by
  exact (positive_select s 112).trans (congrArg s (show (112 : Fin 256) = permuteMask permutation13 224 by rw [image13_eq]; rfl))

theorem lex_13_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4957) (Sat.Literal.pos 4956) (Sat.Literal.pos 224) (Sat.Literal.pos 112)) := by
  exact equality_gate s permutation13 224 (assignment s)
    (Sat.Literal.pos 4957) (Sat.Literal.pos 4956) (Sat.Literal.pos 224) (Sat.Literal.pos 112) (positive_of_descriptor s 4957 (.lex permutation13 224) (by rfl)) (lex_13_224_prefix s) (positive_select s 224) (lex_13_224_image s)

theorem lex_13_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4956), (Sat.Literal.pos 224), (Sat.Literal.neg 112)] := by
  exact comparison_gate s permutation13 224 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4956) (Sat.Literal.pos 224) (Sat.Literal.pos 112) (lex_13_224_prefix s) (positive_select s 224) (lex_13_224_image s)

theorem lex_13_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4957), (Sat.Literal.pos 4956)] :=
  (lex_13_224_gate s).prop _ (List.Mem.head _)

theorem lex_13_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4957), (Sat.Literal.neg 224), (Sat.Literal.pos 112)] :=
  (lex_13_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4957), (Sat.Literal.pos 224), (Sat.Literal.neg 112)] :=
  (lex_13_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4956), (Sat.Literal.neg 224), (Sat.Literal.neg 112), (Sat.Literal.pos 4957)] :=
  (lex_13_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4956), (Sat.Literal.pos 224), (Sat.Literal.pos 112), (Sat.Literal.pos 4957)] :=
  (lex_13_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4957) = lexBefore s permutation13 223 := by
  exact (positive_lex_of_descriptor s 4957 permutation13 224 (by rfl)).trans ((lex_skipped s permutation13 223 224 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation13 223) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation13 223 by rw [image13_eq]; rfl))

theorem lex_13_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4958) (Sat.Literal.pos 4957) (Sat.Literal.pos 223) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation13 223 (assignment s)
    (Sat.Literal.pos 4958) (Sat.Literal.pos 4957) (Sat.Literal.pos 223) (Sat.Literal.pos 239) (positive_of_descriptor s 4958 (.lex permutation13 223) (by rfl)) (lex_13_223_prefix s) (positive_select s 223) (lex_13_223_image s)

theorem lex_13_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4957), (Sat.Literal.pos 223), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation13 223 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4957) (Sat.Literal.pos 223) (Sat.Literal.pos 239) (lex_13_223_prefix s) (positive_select s 223) (lex_13_223_image s)

theorem lex_13_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4958), (Sat.Literal.pos 4957)] :=
  (lex_13_223_gate s).prop _ (List.Mem.head _)

theorem lex_13_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4958), (Sat.Literal.neg 223), (Sat.Literal.pos 239)] :=
  (lex_13_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4958), (Sat.Literal.pos 223), (Sat.Literal.neg 239)] :=
  (lex_13_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4957), (Sat.Literal.neg 223), (Sat.Literal.neg 239), (Sat.Literal.pos 4958)] :=
  (lex_13_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4957), (Sat.Literal.pos 223), (Sat.Literal.pos 239), (Sat.Literal.pos 4958)] :=
  (lex_13_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4958) = lexBefore s permutation13 222 := by
  exact (positive_lex_of_descriptor s 4958 permutation13 223 (by rfl)).trans ((lex_skipped s permutation13 222 223 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation13 222) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation13 222 by rw [image13_eq]; rfl))

theorem lex_13_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4959) (Sat.Literal.pos 4958) (Sat.Literal.pos 222) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation13 222 (assignment s)
    (Sat.Literal.pos 4959) (Sat.Literal.pos 4958) (Sat.Literal.pos 222) (Sat.Literal.pos 111) (positive_of_descriptor s 4959 (.lex permutation13 222) (by rfl)) (lex_13_222_prefix s) (positive_select s 222) (lex_13_222_image s)

theorem lex_13_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4958), (Sat.Literal.pos 222), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation13 222 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4958) (Sat.Literal.pos 222) (Sat.Literal.pos 111) (lex_13_222_prefix s) (positive_select s 222) (lex_13_222_image s)

theorem lex_13_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4959), (Sat.Literal.pos 4958)] :=
  (lex_13_222_gate s).prop _ (List.Mem.head _)

theorem lex_13_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4959), (Sat.Literal.neg 222), (Sat.Literal.pos 111)] :=
  (lex_13_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4959), (Sat.Literal.pos 222), (Sat.Literal.neg 111)] :=
  (lex_13_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4958), (Sat.Literal.neg 222), (Sat.Literal.neg 111), (Sat.Literal.pos 4959)] :=
  (lex_13_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4958), (Sat.Literal.pos 222), (Sat.Literal.pos 111), (Sat.Literal.pos 4959)] :=
  (lex_13_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4959) = lexBefore s permutation13 221 := by
  exact (positive_lex_of_descriptor s 4959 permutation13 222 (by rfl)).trans ((lex_skipped s permutation13 221 222 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation13 221) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation13 221 by rw [image13_eq]; rfl))

theorem lex_13_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4960) (Sat.Literal.pos 4959) (Sat.Literal.pos 221) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation13 221 (assignment s)
    (Sat.Literal.pos 4960) (Sat.Literal.pos 4959) (Sat.Literal.pos 221) (Sat.Literal.pos 238) (positive_of_descriptor s 4960 (.lex permutation13 221) (by rfl)) (lex_13_221_prefix s) (positive_select s 221) (lex_13_221_image s)

theorem lex_13_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4959), (Sat.Literal.pos 221), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation13 221 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4959) (Sat.Literal.pos 221) (Sat.Literal.pos 238) (lex_13_221_prefix s) (positive_select s 221) (lex_13_221_image s)

theorem lex_13_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4960), (Sat.Literal.pos 4959)] :=
  (lex_13_221_gate s).prop _ (List.Mem.head _)

theorem lex_13_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4960), (Sat.Literal.neg 221), (Sat.Literal.pos 238)] :=
  (lex_13_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4960), (Sat.Literal.pos 221), (Sat.Literal.neg 238)] :=
  (lex_13_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4959), (Sat.Literal.neg 221), (Sat.Literal.neg 238), (Sat.Literal.pos 4960)] :=
  (lex_13_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4959), (Sat.Literal.pos 221), (Sat.Literal.pos 238), (Sat.Literal.pos 4960)] :=
  (lex_13_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4960) = lexBefore s permutation13 220 := by
  exact (positive_lex_of_descriptor s 4960 permutation13 221 (by rfl)).trans ((lex_skipped s permutation13 220 221 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation13 220) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation13 220 by rw [image13_eq]; rfl))

theorem lex_13_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4961) (Sat.Literal.pos 4960) (Sat.Literal.pos 220) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation13 220 (assignment s)
    (Sat.Literal.pos 4961) (Sat.Literal.pos 4960) (Sat.Literal.pos 220) (Sat.Literal.pos 110) (positive_of_descriptor s 4961 (.lex permutation13 220) (by rfl)) (lex_13_220_prefix s) (positive_select s 220) (lex_13_220_image s)

theorem lex_13_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4960), (Sat.Literal.pos 220), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation13 220 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4960) (Sat.Literal.pos 220) (Sat.Literal.pos 110) (lex_13_220_prefix s) (positive_select s 220) (lex_13_220_image s)

theorem lex_13_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4961), (Sat.Literal.pos 4960)] :=
  (lex_13_220_gate s).prop _ (List.Mem.head _)

theorem lex_13_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4961), (Sat.Literal.neg 220), (Sat.Literal.pos 110)] :=
  (lex_13_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4961), (Sat.Literal.pos 220), (Sat.Literal.neg 110)] :=
  (lex_13_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4960), (Sat.Literal.neg 220), (Sat.Literal.neg 110), (Sat.Literal.pos 4961)] :=
  (lex_13_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4960), (Sat.Literal.pos 220), (Sat.Literal.pos 110), (Sat.Literal.pos 4961)] :=
  (lex_13_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4961) = lexBefore s permutation13 219 := by
  exact (positive_lex_of_descriptor s 4961 permutation13 220 (by rfl)).trans ((lex_skipped s permutation13 219 220 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation13 219) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation13 219 by rw [image13_eq]; rfl))

theorem lex_13_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4962) (Sat.Literal.pos 4961) (Sat.Literal.pos 219) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation13 219 (assignment s)
    (Sat.Literal.pos 4962) (Sat.Literal.pos 4961) (Sat.Literal.pos 219) (Sat.Literal.pos 237) (positive_of_descriptor s 4962 (.lex permutation13 219) (by rfl)) (lex_13_219_prefix s) (positive_select s 219) (lex_13_219_image s)

theorem lex_13_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4961), (Sat.Literal.pos 219), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation13 219 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4961) (Sat.Literal.pos 219) (Sat.Literal.pos 237) (lex_13_219_prefix s) (positive_select s 219) (lex_13_219_image s)

theorem lex_13_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4962), (Sat.Literal.pos 4961)] :=
  (lex_13_219_gate s).prop _ (List.Mem.head _)

theorem lex_13_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4962), (Sat.Literal.neg 219), (Sat.Literal.pos 237)] :=
  (lex_13_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4962), (Sat.Literal.pos 219), (Sat.Literal.neg 237)] :=
  (lex_13_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4961), (Sat.Literal.neg 219), (Sat.Literal.neg 237), (Sat.Literal.pos 4962)] :=
  (lex_13_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4961), (Sat.Literal.pos 219), (Sat.Literal.pos 237), (Sat.Literal.pos 4962)] :=
  (lex_13_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4962) = lexBefore s permutation13 218 := by
  exact (positive_lex_of_descriptor s 4962 permutation13 219 (by rfl)).trans ((lex_skipped s permutation13 218 219 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation13 218) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation13 218 by rw [image13_eq]; rfl))

theorem lex_13_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4963) (Sat.Literal.pos 4962) (Sat.Literal.pos 218) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation13 218 (assignment s)
    (Sat.Literal.pos 4963) (Sat.Literal.pos 4962) (Sat.Literal.pos 218) (Sat.Literal.pos 109) (positive_of_descriptor s 4963 (.lex permutation13 218) (by rfl)) (lex_13_218_prefix s) (positive_select s 218) (lex_13_218_image s)

theorem lex_13_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4962), (Sat.Literal.pos 218), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation13 218 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4962) (Sat.Literal.pos 218) (Sat.Literal.pos 109) (lex_13_218_prefix s) (positive_select s 218) (lex_13_218_image s)

theorem lex_13_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4963), (Sat.Literal.pos 4962)] :=
  (lex_13_218_gate s).prop _ (List.Mem.head _)

theorem lex_13_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4963), (Sat.Literal.neg 218), (Sat.Literal.pos 109)] :=
  (lex_13_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4963), (Sat.Literal.pos 218), (Sat.Literal.neg 109)] :=
  (lex_13_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4962), (Sat.Literal.neg 218), (Sat.Literal.neg 109), (Sat.Literal.pos 4963)] :=
  (lex_13_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4962), (Sat.Literal.pos 218), (Sat.Literal.pos 109), (Sat.Literal.pos 4963)] :=
  (lex_13_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4963) = lexBefore s permutation13 217 := by
  exact (positive_lex_of_descriptor s 4963 permutation13 218 (by rfl)).trans ((lex_skipped s permutation13 217 218 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 236) = s (permuteMask permutation13 217) := by
  exact (positive_select s 236).trans (congrArg s (show (236 : Fin 256) = permuteMask permutation13 217 by rw [image13_eq]; rfl))

theorem lex_13_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4964) (Sat.Literal.pos 4963) (Sat.Literal.pos 217) (Sat.Literal.pos 236)) := by
  exact equality_gate s permutation13 217 (assignment s)
    (Sat.Literal.pos 4964) (Sat.Literal.pos 4963) (Sat.Literal.pos 217) (Sat.Literal.pos 236) (positive_of_descriptor s 4964 (.lex permutation13 217) (by rfl)) (lex_13_217_prefix s) (positive_select s 217) (lex_13_217_image s)

theorem lex_13_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4963), (Sat.Literal.pos 217), (Sat.Literal.neg 236)] := by
  exact comparison_gate s permutation13 217 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4963) (Sat.Literal.pos 217) (Sat.Literal.pos 236) (lex_13_217_prefix s) (positive_select s 217) (lex_13_217_image s)

theorem lex_13_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4964), (Sat.Literal.pos 4963)] :=
  (lex_13_217_gate s).prop _ (List.Mem.head _)

theorem lex_13_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4964), (Sat.Literal.neg 217), (Sat.Literal.pos 236)] :=
  (lex_13_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4964), (Sat.Literal.pos 217), (Sat.Literal.neg 236)] :=
  (lex_13_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4963), (Sat.Literal.neg 217), (Sat.Literal.neg 236), (Sat.Literal.pos 4964)] :=
  (lex_13_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4963), (Sat.Literal.pos 217), (Sat.Literal.pos 236), (Sat.Literal.pos 4964)] :=
  (lex_13_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4964) = lexBefore s permutation13 216 := by
  exact (positive_lex_of_descriptor s 4964 permutation13 217 (by rfl)).trans ((lex_skipped s permutation13 216 217 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 108) = s (permuteMask permutation13 216) := by
  exact (positive_select s 108).trans (congrArg s (show (108 : Fin 256) = permuteMask permutation13 216 by rw [image13_eq]; rfl))

theorem lex_13_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4965) (Sat.Literal.pos 4964) (Sat.Literal.pos 216) (Sat.Literal.pos 108)) := by
  exact equality_gate s permutation13 216 (assignment s)
    (Sat.Literal.pos 4965) (Sat.Literal.pos 4964) (Sat.Literal.pos 216) (Sat.Literal.pos 108) (positive_of_descriptor s 4965 (.lex permutation13 216) (by rfl)) (lex_13_216_prefix s) (positive_select s 216) (lex_13_216_image s)

theorem lex_13_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4964), (Sat.Literal.pos 216), (Sat.Literal.neg 108)] := by
  exact comparison_gate s permutation13 216 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4964) (Sat.Literal.pos 216) (Sat.Literal.pos 108) (lex_13_216_prefix s) (positive_select s 216) (lex_13_216_image s)

theorem lex_13_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4965), (Sat.Literal.pos 4964)] :=
  (lex_13_216_gate s).prop _ (List.Mem.head _)

theorem lex_13_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4965), (Sat.Literal.neg 216), (Sat.Literal.pos 108)] :=
  (lex_13_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4965), (Sat.Literal.pos 216), (Sat.Literal.neg 108)] :=
  (lex_13_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4964), (Sat.Literal.neg 216), (Sat.Literal.neg 108), (Sat.Literal.pos 4965)] :=
  (lex_13_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4964), (Sat.Literal.pos 216), (Sat.Literal.pos 108), (Sat.Literal.pos 4965)] :=
  (lex_13_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4965) = lexBefore s permutation13 215 := by
  exact (positive_lex_of_descriptor s 4965 permutation13 216 (by rfl)).trans ((lex_skipped s permutation13 215 216 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation13 215) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation13 215 by rw [image13_eq]; rfl))

theorem lex_13_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4966) (Sat.Literal.pos 4965) (Sat.Literal.pos 215) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation13 215 (assignment s)
    (Sat.Literal.pos 4966) (Sat.Literal.pos 4965) (Sat.Literal.pos 215) (Sat.Literal.pos 235) (positive_of_descriptor s 4966 (.lex permutation13 215) (by rfl)) (lex_13_215_prefix s) (positive_select s 215) (lex_13_215_image s)

theorem lex_13_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4965), (Sat.Literal.pos 215), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation13 215 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4965) (Sat.Literal.pos 215) (Sat.Literal.pos 235) (lex_13_215_prefix s) (positive_select s 215) (lex_13_215_image s)

theorem lex_13_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4966), (Sat.Literal.pos 4965)] :=
  (lex_13_215_gate s).prop _ (List.Mem.head _)

theorem lex_13_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4966), (Sat.Literal.neg 215), (Sat.Literal.pos 235)] :=
  (lex_13_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4966), (Sat.Literal.pos 215), (Sat.Literal.neg 235)] :=
  (lex_13_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4965), (Sat.Literal.neg 215), (Sat.Literal.neg 235), (Sat.Literal.pos 4966)] :=
  (lex_13_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4965), (Sat.Literal.pos 215), (Sat.Literal.pos 235), (Sat.Literal.pos 4966)] :=
  (lex_13_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4966) = lexBefore s permutation13 214 := by
  exact (positive_lex_of_descriptor s 4966 permutation13 215 (by rfl)).trans ((lex_skipped s permutation13 214 215 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation13 214) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation13 214 by rw [image13_eq]; rfl))

theorem lex_13_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4967) (Sat.Literal.pos 4966) (Sat.Literal.pos 214) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation13 214 (assignment s)
    (Sat.Literal.pos 4967) (Sat.Literal.pos 4966) (Sat.Literal.pos 214) (Sat.Literal.pos 107) (positive_of_descriptor s 4967 (.lex permutation13 214) (by rfl)) (lex_13_214_prefix s) (positive_select s 214) (lex_13_214_image s)

theorem lex_13_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4966), (Sat.Literal.pos 214), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation13 214 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4966) (Sat.Literal.pos 214) (Sat.Literal.pos 107) (lex_13_214_prefix s) (positive_select s 214) (lex_13_214_image s)

theorem lex_13_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4967), (Sat.Literal.pos 4966)] :=
  (lex_13_214_gate s).prop _ (List.Mem.head _)

theorem lex_13_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4967), (Sat.Literal.neg 214), (Sat.Literal.pos 107)] :=
  (lex_13_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4967), (Sat.Literal.pos 214), (Sat.Literal.neg 107)] :=
  (lex_13_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4966), (Sat.Literal.neg 214), (Sat.Literal.neg 107), (Sat.Literal.pos 4967)] :=
  (lex_13_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4966), (Sat.Literal.pos 214), (Sat.Literal.pos 107), (Sat.Literal.pos 4967)] :=
  (lex_13_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4967) = lexBefore s permutation13 213 := by
  exact (positive_lex_of_descriptor s 4967 permutation13 214 (by rfl)).trans ((lex_skipped s permutation13 213 214 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation13 213) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation13 213 by rw [image13_eq]; rfl))

theorem lex_13_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4968) (Sat.Literal.pos 4967) (Sat.Literal.pos 213) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation13 213 (assignment s)
    (Sat.Literal.pos 4968) (Sat.Literal.pos 4967) (Sat.Literal.pos 213) (Sat.Literal.pos 234) (positive_of_descriptor s 4968 (.lex permutation13 213) (by rfl)) (lex_13_213_prefix s) (positive_select s 213) (lex_13_213_image s)

theorem lex_13_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4967), (Sat.Literal.pos 213), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation13 213 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4967) (Sat.Literal.pos 213) (Sat.Literal.pos 234) (lex_13_213_prefix s) (positive_select s 213) (lex_13_213_image s)

theorem lex_13_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4968), (Sat.Literal.pos 4967)] :=
  (lex_13_213_gate s).prop _ (List.Mem.head _)

theorem lex_13_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4968), (Sat.Literal.neg 213), (Sat.Literal.pos 234)] :=
  (lex_13_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4968), (Sat.Literal.pos 213), (Sat.Literal.neg 234)] :=
  (lex_13_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4967), (Sat.Literal.neg 213), (Sat.Literal.neg 234), (Sat.Literal.pos 4968)] :=
  (lex_13_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4967), (Sat.Literal.pos 213), (Sat.Literal.pos 234), (Sat.Literal.pos 4968)] :=
  (lex_13_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4968) = lexBefore s permutation13 212 := by
  exact (positive_lex_of_descriptor s 4968 permutation13 213 (by rfl)).trans ((lex_skipped s permutation13 212 213 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation13 212) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation13 212 by rw [image13_eq]; rfl))

theorem lex_13_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4969) (Sat.Literal.pos 4968) (Sat.Literal.pos 212) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation13 212 (assignment s)
    (Sat.Literal.pos 4969) (Sat.Literal.pos 4968) (Sat.Literal.pos 212) (Sat.Literal.pos 106) (positive_of_descriptor s 4969 (.lex permutation13 212) (by rfl)) (lex_13_212_prefix s) (positive_select s 212) (lex_13_212_image s)

theorem lex_13_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4968), (Sat.Literal.pos 212), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation13 212 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4968) (Sat.Literal.pos 212) (Sat.Literal.pos 106) (lex_13_212_prefix s) (positive_select s 212) (lex_13_212_image s)

theorem lex_13_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4969), (Sat.Literal.pos 4968)] :=
  (lex_13_212_gate s).prop _ (List.Mem.head _)

theorem lex_13_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4969), (Sat.Literal.neg 212), (Sat.Literal.pos 106)] :=
  (lex_13_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4969), (Sat.Literal.pos 212), (Sat.Literal.neg 106)] :=
  (lex_13_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4968), (Sat.Literal.neg 212), (Sat.Literal.neg 106), (Sat.Literal.pos 4969)] :=
  (lex_13_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4968), (Sat.Literal.pos 212), (Sat.Literal.pos 106), (Sat.Literal.pos 4969)] :=
  (lex_13_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4969) = lexBefore s permutation13 211 := by
  exact (positive_lex_of_descriptor s 4969 permutation13 212 (by rfl)).trans ((lex_skipped s permutation13 211 212 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation13 211) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation13 211 by rw [image13_eq]; rfl))

theorem lex_13_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4970) (Sat.Literal.pos 4969) (Sat.Literal.pos 211) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation13 211 (assignment s)
    (Sat.Literal.pos 4970) (Sat.Literal.pos 4969) (Sat.Literal.pos 211) (Sat.Literal.pos 233) (positive_of_descriptor s 4970 (.lex permutation13 211) (by rfl)) (lex_13_211_prefix s) (positive_select s 211) (lex_13_211_image s)

theorem lex_13_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4969), (Sat.Literal.pos 211), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation13 211 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4969) (Sat.Literal.pos 211) (Sat.Literal.pos 233) (lex_13_211_prefix s) (positive_select s 211) (lex_13_211_image s)

theorem lex_13_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4970), (Sat.Literal.pos 4969)] :=
  (lex_13_211_gate s).prop _ (List.Mem.head _)

theorem lex_13_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4970), (Sat.Literal.neg 211), (Sat.Literal.pos 233)] :=
  (lex_13_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4970), (Sat.Literal.pos 211), (Sat.Literal.neg 233)] :=
  (lex_13_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4969), (Sat.Literal.neg 211), (Sat.Literal.neg 233), (Sat.Literal.pos 4970)] :=
  (lex_13_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4969), (Sat.Literal.pos 211), (Sat.Literal.pos 233), (Sat.Literal.pos 4970)] :=
  (lex_13_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4970) = lexBefore s permutation13 210 := by
  exact (positive_lex_of_descriptor s 4970 permutation13 211 (by rfl)).trans ((lex_skipped s permutation13 210 211 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation13 210) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation13 210 by rw [image13_eq]; rfl))

theorem lex_13_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4971) (Sat.Literal.pos 4970) (Sat.Literal.pos 210) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation13 210 (assignment s)
    (Sat.Literal.pos 4971) (Sat.Literal.pos 4970) (Sat.Literal.pos 210) (Sat.Literal.pos 105) (positive_of_descriptor s 4971 (.lex permutation13 210) (by rfl)) (lex_13_210_prefix s) (positive_select s 210) (lex_13_210_image s)

theorem lex_13_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4970), (Sat.Literal.pos 210), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation13 210 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4970) (Sat.Literal.pos 210) (Sat.Literal.pos 105) (lex_13_210_prefix s) (positive_select s 210) (lex_13_210_image s)

theorem lex_13_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4971), (Sat.Literal.pos 4970)] :=
  (lex_13_210_gate s).prop _ (List.Mem.head _)

theorem lex_13_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4971), (Sat.Literal.neg 210), (Sat.Literal.pos 105)] :=
  (lex_13_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4971), (Sat.Literal.pos 210), (Sat.Literal.neg 105)] :=
  (lex_13_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4970), (Sat.Literal.neg 210), (Sat.Literal.neg 105), (Sat.Literal.pos 4971)] :=
  (lex_13_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4970), (Sat.Literal.pos 210), (Sat.Literal.pos 105), (Sat.Literal.pos 4971)] :=
  (lex_13_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4971) = lexBefore s permutation13 209 := by
  exact (positive_lex_of_descriptor s 4971 permutation13 210 (by rfl)).trans ((lex_skipped s permutation13 209 210 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 232) = s (permuteMask permutation13 209) := by
  exact (positive_select s 232).trans (congrArg s (show (232 : Fin 256) = permuteMask permutation13 209 by rw [image13_eq]; rfl))

theorem lex_13_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4972) (Sat.Literal.pos 4971) (Sat.Literal.pos 209) (Sat.Literal.pos 232)) := by
  exact equality_gate s permutation13 209 (assignment s)
    (Sat.Literal.pos 4972) (Sat.Literal.pos 4971) (Sat.Literal.pos 209) (Sat.Literal.pos 232) (positive_of_descriptor s 4972 (.lex permutation13 209) (by rfl)) (lex_13_209_prefix s) (positive_select s 209) (lex_13_209_image s)

theorem lex_13_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4971), (Sat.Literal.pos 209), (Sat.Literal.neg 232)] := by
  exact comparison_gate s permutation13 209 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4971) (Sat.Literal.pos 209) (Sat.Literal.pos 232) (lex_13_209_prefix s) (positive_select s 209) (lex_13_209_image s)

theorem lex_13_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4972), (Sat.Literal.pos 4971)] :=
  (lex_13_209_gate s).prop _ (List.Mem.head _)

theorem lex_13_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4972), (Sat.Literal.neg 209), (Sat.Literal.pos 232)] :=
  (lex_13_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4972), (Sat.Literal.pos 209), (Sat.Literal.neg 232)] :=
  (lex_13_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4971), (Sat.Literal.neg 209), (Sat.Literal.neg 232), (Sat.Literal.pos 4972)] :=
  (lex_13_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4971), (Sat.Literal.pos 209), (Sat.Literal.pos 232), (Sat.Literal.pos 4972)] :=
  (lex_13_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4972) = lexBefore s permutation13 208 := by
  exact (positive_lex_of_descriptor s 4972 permutation13 209 (by rfl)).trans ((lex_skipped s permutation13 208 209 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 104) = s (permuteMask permutation13 208) := by
  exact (positive_select s 104).trans (congrArg s (show (104 : Fin 256) = permuteMask permutation13 208 by rw [image13_eq]; rfl))

theorem lex_13_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4973) (Sat.Literal.pos 4972) (Sat.Literal.pos 208) (Sat.Literal.pos 104)) := by
  exact equality_gate s permutation13 208 (assignment s)
    (Sat.Literal.pos 4973) (Sat.Literal.pos 4972) (Sat.Literal.pos 208) (Sat.Literal.pos 104) (positive_of_descriptor s 4973 (.lex permutation13 208) (by rfl)) (lex_13_208_prefix s) (positive_select s 208) (lex_13_208_image s)

theorem lex_13_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4972), (Sat.Literal.pos 208), (Sat.Literal.neg 104)] := by
  exact comparison_gate s permutation13 208 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4972) (Sat.Literal.pos 208) (Sat.Literal.pos 104) (lex_13_208_prefix s) (positive_select s 208) (lex_13_208_image s)

theorem lex_13_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4973), (Sat.Literal.pos 4972)] :=
  (lex_13_208_gate s).prop _ (List.Mem.head _)

theorem lex_13_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4973), (Sat.Literal.neg 208), (Sat.Literal.pos 104)] :=
  (lex_13_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4973), (Sat.Literal.pos 208), (Sat.Literal.neg 104)] :=
  (lex_13_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4972), (Sat.Literal.neg 208), (Sat.Literal.neg 104), (Sat.Literal.pos 4973)] :=
  (lex_13_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4972), (Sat.Literal.pos 208), (Sat.Literal.pos 104), (Sat.Literal.pos 4973)] :=
  (lex_13_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4973) = lexBefore s permutation13 207 := by
  exact (positive_lex_of_descriptor s 4973 permutation13 208 (by rfl)).trans ((lex_skipped s permutation13 207 208 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation13 207) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation13 207 by rw [image13_eq]; rfl))

theorem lex_13_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4974) (Sat.Literal.pos 4973) (Sat.Literal.pos 207) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation13 207 (assignment s)
    (Sat.Literal.pos 4974) (Sat.Literal.pos 4973) (Sat.Literal.pos 207) (Sat.Literal.pos 231) (positive_of_descriptor s 4974 (.lex permutation13 207) (by rfl)) (lex_13_207_prefix s) (positive_select s 207) (lex_13_207_image s)

theorem lex_13_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4973), (Sat.Literal.pos 207), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation13 207 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4973) (Sat.Literal.pos 207) (Sat.Literal.pos 231) (lex_13_207_prefix s) (positive_select s 207) (lex_13_207_image s)

theorem lex_13_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4974), (Sat.Literal.pos 4973)] :=
  (lex_13_207_gate s).prop _ (List.Mem.head _)

theorem lex_13_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4974), (Sat.Literal.neg 207), (Sat.Literal.pos 231)] :=
  (lex_13_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4974), (Sat.Literal.pos 207), (Sat.Literal.neg 231)] :=
  (lex_13_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4973), (Sat.Literal.neg 207), (Sat.Literal.neg 231), (Sat.Literal.pos 4974)] :=
  (lex_13_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4973), (Sat.Literal.pos 207), (Sat.Literal.pos 231), (Sat.Literal.pos 4974)] :=
  (lex_13_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4974) = lexBefore s permutation13 206 := by
  exact (positive_lex_of_descriptor s 4974 permutation13 207 (by rfl)).trans ((lex_skipped s permutation13 206 207 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation13 206) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation13 206 by rw [image13_eq]; rfl))

theorem lex_13_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4975) (Sat.Literal.pos 4974) (Sat.Literal.pos 206) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation13 206 (assignment s)
    (Sat.Literal.pos 4975) (Sat.Literal.pos 4974) (Sat.Literal.pos 206) (Sat.Literal.pos 103) (positive_of_descriptor s 4975 (.lex permutation13 206) (by rfl)) (lex_13_206_prefix s) (positive_select s 206) (lex_13_206_image s)

theorem lex_13_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4974), (Sat.Literal.pos 206), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation13 206 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4974) (Sat.Literal.pos 206) (Sat.Literal.pos 103) (lex_13_206_prefix s) (positive_select s 206) (lex_13_206_image s)

theorem lex_13_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4975), (Sat.Literal.pos 4974)] :=
  (lex_13_206_gate s).prop _ (List.Mem.head _)

theorem lex_13_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4975), (Sat.Literal.neg 206), (Sat.Literal.pos 103)] :=
  (lex_13_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4975), (Sat.Literal.pos 206), (Sat.Literal.neg 103)] :=
  (lex_13_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4974), (Sat.Literal.neg 206), (Sat.Literal.neg 103), (Sat.Literal.pos 4975)] :=
  (lex_13_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4974), (Sat.Literal.pos 206), (Sat.Literal.pos 103), (Sat.Literal.pos 4975)] :=
  (lex_13_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4975) = lexBefore s permutation13 205 := by
  exact (positive_lex_of_descriptor s 4975 permutation13 206 (by rfl)).trans ((lex_skipped s permutation13 205 206 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation13 205) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation13 205 by rw [image13_eq]; rfl))

theorem lex_13_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4976) (Sat.Literal.pos 4975) (Sat.Literal.pos 205) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation13 205 (assignment s)
    (Sat.Literal.pos 4976) (Sat.Literal.pos 4975) (Sat.Literal.pos 205) (Sat.Literal.pos 230) (positive_of_descriptor s 4976 (.lex permutation13 205) (by rfl)) (lex_13_205_prefix s) (positive_select s 205) (lex_13_205_image s)

theorem lex_13_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4975), (Sat.Literal.pos 205), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation13 205 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4975) (Sat.Literal.pos 205) (Sat.Literal.pos 230) (lex_13_205_prefix s) (positive_select s 205) (lex_13_205_image s)

theorem lex_13_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4976), (Sat.Literal.pos 4975)] :=
  (lex_13_205_gate s).prop _ (List.Mem.head _)

theorem lex_13_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4976), (Sat.Literal.neg 205), (Sat.Literal.pos 230)] :=
  (lex_13_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4976), (Sat.Literal.pos 205), (Sat.Literal.neg 230)] :=
  (lex_13_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4975), (Sat.Literal.neg 205), (Sat.Literal.neg 230), (Sat.Literal.pos 4976)] :=
  (lex_13_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4975), (Sat.Literal.pos 205), (Sat.Literal.pos 230), (Sat.Literal.pos 4976)] :=
  (lex_13_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4976) = lexBefore s permutation13 204 := by
  exact (positive_lex_of_descriptor s 4976 permutation13 205 (by rfl)).trans ((lex_skipped s permutation13 204 205 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation13 204) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation13 204 by rw [image13_eq]; rfl))

theorem lex_13_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4977) (Sat.Literal.pos 4976) (Sat.Literal.pos 204) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation13 204 (assignment s)
    (Sat.Literal.pos 4977) (Sat.Literal.pos 4976) (Sat.Literal.pos 204) (Sat.Literal.pos 102) (positive_of_descriptor s 4977 (.lex permutation13 204) (by rfl)) (lex_13_204_prefix s) (positive_select s 204) (lex_13_204_image s)

theorem lex_13_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4976), (Sat.Literal.pos 204), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation13 204 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4976) (Sat.Literal.pos 204) (Sat.Literal.pos 102) (lex_13_204_prefix s) (positive_select s 204) (lex_13_204_image s)

theorem lex_13_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4977), (Sat.Literal.pos 4976)] :=
  (lex_13_204_gate s).prop _ (List.Mem.head _)

theorem lex_13_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4977), (Sat.Literal.neg 204), (Sat.Literal.pos 102)] :=
  (lex_13_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4977), (Sat.Literal.pos 204), (Sat.Literal.neg 102)] :=
  (lex_13_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4976), (Sat.Literal.neg 204), (Sat.Literal.neg 102), (Sat.Literal.pos 4977)] :=
  (lex_13_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4976), (Sat.Literal.pos 204), (Sat.Literal.pos 102), (Sat.Literal.pos 4977)] :=
  (lex_13_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4977) = lexBefore s permutation13 203 := by
  exact (positive_lex_of_descriptor s 4977 permutation13 204 (by rfl)).trans ((lex_skipped s permutation13 203 204 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation13 203) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation13 203 by rw [image13_eq]; rfl))

theorem lex_13_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4978) (Sat.Literal.pos 4977) (Sat.Literal.pos 203) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation13 203 (assignment s)
    (Sat.Literal.pos 4978) (Sat.Literal.pos 4977) (Sat.Literal.pos 203) (Sat.Literal.pos 229) (positive_of_descriptor s 4978 (.lex permutation13 203) (by rfl)) (lex_13_203_prefix s) (positive_select s 203) (lex_13_203_image s)

theorem lex_13_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4977), (Sat.Literal.pos 203), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation13 203 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4977) (Sat.Literal.pos 203) (Sat.Literal.pos 229) (lex_13_203_prefix s) (positive_select s 203) (lex_13_203_image s)

theorem lex_13_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4978), (Sat.Literal.pos 4977)] :=
  (lex_13_203_gate s).prop _ (List.Mem.head _)

theorem lex_13_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4978), (Sat.Literal.neg 203), (Sat.Literal.pos 229)] :=
  (lex_13_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4978), (Sat.Literal.pos 203), (Sat.Literal.neg 229)] :=
  (lex_13_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4977), (Sat.Literal.neg 203), (Sat.Literal.neg 229), (Sat.Literal.pos 4978)] :=
  (lex_13_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4977), (Sat.Literal.pos 203), (Sat.Literal.pos 229), (Sat.Literal.pos 4978)] :=
  (lex_13_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4978) = lexBefore s permutation13 202 := by
  exact (positive_lex_of_descriptor s 4978 permutation13 203 (by rfl)).trans ((lex_skipped s permutation13 202 203 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation13 202) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation13 202 by rw [image13_eq]; rfl))

theorem lex_13_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4979) (Sat.Literal.pos 4978) (Sat.Literal.pos 202) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation13 202 (assignment s)
    (Sat.Literal.pos 4979) (Sat.Literal.pos 4978) (Sat.Literal.pos 202) (Sat.Literal.pos 101) (positive_of_descriptor s 4979 (.lex permutation13 202) (by rfl)) (lex_13_202_prefix s) (positive_select s 202) (lex_13_202_image s)

theorem lex_13_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4978), (Sat.Literal.pos 202), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation13 202 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4978) (Sat.Literal.pos 202) (Sat.Literal.pos 101) (lex_13_202_prefix s) (positive_select s 202) (lex_13_202_image s)

theorem lex_13_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4979), (Sat.Literal.pos 4978)] :=
  (lex_13_202_gate s).prop _ (List.Mem.head _)

theorem lex_13_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4979), (Sat.Literal.neg 202), (Sat.Literal.pos 101)] :=
  (lex_13_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4979), (Sat.Literal.pos 202), (Sat.Literal.neg 101)] :=
  (lex_13_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4978), (Sat.Literal.neg 202), (Sat.Literal.neg 101), (Sat.Literal.pos 4979)] :=
  (lex_13_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4978), (Sat.Literal.pos 202), (Sat.Literal.pos 101), (Sat.Literal.pos 4979)] :=
  (lex_13_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4979) = lexBefore s permutation13 201 := by
  exact (positive_lex_of_descriptor s 4979 permutation13 202 (by rfl)).trans ((lex_skipped s permutation13 201 202 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 228) = s (permuteMask permutation13 201) := by
  exact (positive_select s 228).trans (congrArg s (show (228 : Fin 256) = permuteMask permutation13 201 by rw [image13_eq]; rfl))

theorem lex_13_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4980) (Sat.Literal.pos 4979) (Sat.Literal.pos 201) (Sat.Literal.pos 228)) := by
  exact equality_gate s permutation13 201 (assignment s)
    (Sat.Literal.pos 4980) (Sat.Literal.pos 4979) (Sat.Literal.pos 201) (Sat.Literal.pos 228) (positive_of_descriptor s 4980 (.lex permutation13 201) (by rfl)) (lex_13_201_prefix s) (positive_select s 201) (lex_13_201_image s)

theorem lex_13_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4979), (Sat.Literal.pos 201), (Sat.Literal.neg 228)] := by
  exact comparison_gate s permutation13 201 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4979) (Sat.Literal.pos 201) (Sat.Literal.pos 228) (lex_13_201_prefix s) (positive_select s 201) (lex_13_201_image s)

theorem lex_13_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4980), (Sat.Literal.pos 4979)] :=
  (lex_13_201_gate s).prop _ (List.Mem.head _)

theorem lex_13_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4980), (Sat.Literal.neg 201), (Sat.Literal.pos 228)] :=
  (lex_13_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4980), (Sat.Literal.pos 201), (Sat.Literal.neg 228)] :=
  (lex_13_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4979), (Sat.Literal.neg 201), (Sat.Literal.neg 228), (Sat.Literal.pos 4980)] :=
  (lex_13_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4979), (Sat.Literal.pos 201), (Sat.Literal.pos 228), (Sat.Literal.pos 4980)] :=
  (lex_13_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4980) = lexBefore s permutation13 200 := by
  exact (positive_lex_of_descriptor s 4980 permutation13 201 (by rfl)).trans ((lex_skipped s permutation13 200 201 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 100) = s (permuteMask permutation13 200) := by
  exact (positive_select s 100).trans (congrArg s (show (100 : Fin 256) = permuteMask permutation13 200 by rw [image13_eq]; rfl))

theorem lex_13_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4981) (Sat.Literal.pos 4980) (Sat.Literal.pos 200) (Sat.Literal.pos 100)) := by
  exact equality_gate s permutation13 200 (assignment s)
    (Sat.Literal.pos 4981) (Sat.Literal.pos 4980) (Sat.Literal.pos 200) (Sat.Literal.pos 100) (positive_of_descriptor s 4981 (.lex permutation13 200) (by rfl)) (lex_13_200_prefix s) (positive_select s 200) (lex_13_200_image s)

theorem lex_13_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4980), (Sat.Literal.pos 200), (Sat.Literal.neg 100)] := by
  exact comparison_gate s permutation13 200 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4980) (Sat.Literal.pos 200) (Sat.Literal.pos 100) (lex_13_200_prefix s) (positive_select s 200) (lex_13_200_image s)

theorem lex_13_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4981), (Sat.Literal.pos 4980)] :=
  (lex_13_200_gate s).prop _ (List.Mem.head _)

theorem lex_13_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4981), (Sat.Literal.neg 200), (Sat.Literal.pos 100)] :=
  (lex_13_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4981), (Sat.Literal.pos 200), (Sat.Literal.neg 100)] :=
  (lex_13_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4980), (Sat.Literal.neg 200), (Sat.Literal.neg 100), (Sat.Literal.pos 4981)] :=
  (lex_13_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4980), (Sat.Literal.pos 200), (Sat.Literal.pos 100), (Sat.Literal.pos 4981)] :=
  (lex_13_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4981) = lexBefore s permutation13 199 := by
  exact (positive_lex_of_descriptor s 4981 permutation13 200 (by rfl)).trans ((lex_skipped s permutation13 199 200 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation13 199) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation13 199 by rw [image13_eq]; rfl))

theorem lex_13_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4982) (Sat.Literal.pos 4981) (Sat.Literal.pos 199) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation13 199 (assignment s)
    (Sat.Literal.pos 4982) (Sat.Literal.pos 4981) (Sat.Literal.pos 199) (Sat.Literal.pos 227) (positive_of_descriptor s 4982 (.lex permutation13 199) (by rfl)) (lex_13_199_prefix s) (positive_select s 199) (lex_13_199_image s)

theorem lex_13_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4981), (Sat.Literal.pos 199), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation13 199 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4981) (Sat.Literal.pos 199) (Sat.Literal.pos 227) (lex_13_199_prefix s) (positive_select s 199) (lex_13_199_image s)

theorem lex_13_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4982), (Sat.Literal.pos 4981)] :=
  (lex_13_199_gate s).prop _ (List.Mem.head _)

theorem lex_13_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4982), (Sat.Literal.neg 199), (Sat.Literal.pos 227)] :=
  (lex_13_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4982), (Sat.Literal.pos 199), (Sat.Literal.neg 227)] :=
  (lex_13_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4981), (Sat.Literal.neg 199), (Sat.Literal.neg 227), (Sat.Literal.pos 4982)] :=
  (lex_13_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4981), (Sat.Literal.pos 199), (Sat.Literal.pos 227), (Sat.Literal.pos 4982)] :=
  (lex_13_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4982) = lexBefore s permutation13 198 := by
  exact (positive_lex_of_descriptor s 4982 permutation13 199 (by rfl)).trans ((lex_skipped s permutation13 198 199 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation13 198) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation13 198 by rw [image13_eq]; rfl))

theorem lex_13_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4983) (Sat.Literal.pos 4982) (Sat.Literal.pos 198) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation13 198 (assignment s)
    (Sat.Literal.pos 4983) (Sat.Literal.pos 4982) (Sat.Literal.pos 198) (Sat.Literal.pos 99) (positive_of_descriptor s 4983 (.lex permutation13 198) (by rfl)) (lex_13_198_prefix s) (positive_select s 198) (lex_13_198_image s)

theorem lex_13_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4982), (Sat.Literal.pos 198), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation13 198 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4982) (Sat.Literal.pos 198) (Sat.Literal.pos 99) (lex_13_198_prefix s) (positive_select s 198) (lex_13_198_image s)

theorem lex_13_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4983), (Sat.Literal.pos 4982)] :=
  (lex_13_198_gate s).prop _ (List.Mem.head _)

theorem lex_13_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4983), (Sat.Literal.neg 198), (Sat.Literal.pos 99)] :=
  (lex_13_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4983), (Sat.Literal.pos 198), (Sat.Literal.neg 99)] :=
  (lex_13_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4982), (Sat.Literal.neg 198), (Sat.Literal.neg 99), (Sat.Literal.pos 4983)] :=
  (lex_13_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4982), (Sat.Literal.pos 198), (Sat.Literal.pos 99), (Sat.Literal.pos 4983)] :=
  (lex_13_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4983) = lexBefore s permutation13 197 := by
  exact (positive_lex_of_descriptor s 4983 permutation13 198 (by rfl)).trans ((lex_skipped s permutation13 197 198 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation13 197) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation13 197 by rw [image13_eq]; rfl))

theorem lex_13_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4984) (Sat.Literal.pos 4983) (Sat.Literal.pos 197) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation13 197 (assignment s)
    (Sat.Literal.pos 4984) (Sat.Literal.pos 4983) (Sat.Literal.pos 197) (Sat.Literal.pos 226) (positive_of_descriptor s 4984 (.lex permutation13 197) (by rfl)) (lex_13_197_prefix s) (positive_select s 197) (lex_13_197_image s)

theorem lex_13_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4983), (Sat.Literal.pos 197), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation13 197 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4983) (Sat.Literal.pos 197) (Sat.Literal.pos 226) (lex_13_197_prefix s) (positive_select s 197) (lex_13_197_image s)

theorem lex_13_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4984), (Sat.Literal.pos 4983)] :=
  (lex_13_197_gate s).prop _ (List.Mem.head _)

theorem lex_13_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4984), (Sat.Literal.neg 197), (Sat.Literal.pos 226)] :=
  (lex_13_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4984), (Sat.Literal.pos 197), (Sat.Literal.neg 226)] :=
  (lex_13_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4983), (Sat.Literal.neg 197), (Sat.Literal.neg 226), (Sat.Literal.pos 4984)] :=
  (lex_13_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4983), (Sat.Literal.pos 197), (Sat.Literal.pos 226), (Sat.Literal.pos 4984)] :=
  (lex_13_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4984) = lexBefore s permutation13 196 := by
  exact (positive_lex_of_descriptor s 4984 permutation13 197 (by rfl)).trans ((lex_skipped s permutation13 196 197 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation13 196) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation13 196 by rw [image13_eq]; rfl))

theorem lex_13_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4985) (Sat.Literal.pos 4984) (Sat.Literal.pos 196) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation13 196 (assignment s)
    (Sat.Literal.pos 4985) (Sat.Literal.pos 4984) (Sat.Literal.pos 196) (Sat.Literal.pos 98) (positive_of_descriptor s 4985 (.lex permutation13 196) (by rfl)) (lex_13_196_prefix s) (positive_select s 196) (lex_13_196_image s)

theorem lex_13_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4984), (Sat.Literal.pos 196), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation13 196 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4984) (Sat.Literal.pos 196) (Sat.Literal.pos 98) (lex_13_196_prefix s) (positive_select s 196) (lex_13_196_image s)

theorem lex_13_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4985), (Sat.Literal.pos 4984)] :=
  (lex_13_196_gate s).prop _ (List.Mem.head _)

theorem lex_13_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4985), (Sat.Literal.neg 196), (Sat.Literal.pos 98)] :=
  (lex_13_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4985), (Sat.Literal.pos 196), (Sat.Literal.neg 98)] :=
  (lex_13_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4984), (Sat.Literal.neg 196), (Sat.Literal.neg 98), (Sat.Literal.pos 4985)] :=
  (lex_13_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4984), (Sat.Literal.pos 196), (Sat.Literal.pos 98), (Sat.Literal.pos 4985)] :=
  (lex_13_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4985) = lexBefore s permutation13 195 := by
  exact (positive_lex_of_descriptor s 4985 permutation13 196 (by rfl)).trans ((lex_skipped s permutation13 195 196 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation13 195) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation13 195 by rw [image13_eq]; rfl))

theorem lex_13_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4986) (Sat.Literal.pos 4985) (Sat.Literal.pos 195) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation13 195 (assignment s)
    (Sat.Literal.pos 4986) (Sat.Literal.pos 4985) (Sat.Literal.pos 195) (Sat.Literal.pos 225) (positive_of_descriptor s 4986 (.lex permutation13 195) (by rfl)) (lex_13_195_prefix s) (positive_select s 195) (lex_13_195_image s)

theorem lex_13_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4985), (Sat.Literal.pos 195), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation13 195 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4985) (Sat.Literal.pos 195) (Sat.Literal.pos 225) (lex_13_195_prefix s) (positive_select s 195) (lex_13_195_image s)

theorem lex_13_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4986), (Sat.Literal.pos 4985)] :=
  (lex_13_195_gate s).prop _ (List.Mem.head _)

theorem lex_13_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4986), (Sat.Literal.neg 195), (Sat.Literal.pos 225)] :=
  (lex_13_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4986), (Sat.Literal.pos 195), (Sat.Literal.neg 225)] :=
  (lex_13_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4985), (Sat.Literal.neg 195), (Sat.Literal.neg 225), (Sat.Literal.pos 4986)] :=
  (lex_13_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4985), (Sat.Literal.pos 195), (Sat.Literal.pos 225), (Sat.Literal.pos 4986)] :=
  (lex_13_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4986) = lexBefore s permutation13 194 := by
  exact (positive_lex_of_descriptor s 4986 permutation13 195 (by rfl)).trans ((lex_skipped s permutation13 194 195 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation13 194) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation13 194 by rw [image13_eq]; rfl))

theorem lex_13_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4987) (Sat.Literal.pos 4986) (Sat.Literal.pos 194) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation13 194 (assignment s)
    (Sat.Literal.pos 4987) (Sat.Literal.pos 4986) (Sat.Literal.pos 194) (Sat.Literal.pos 97) (positive_of_descriptor s 4987 (.lex permutation13 194) (by rfl)) (lex_13_194_prefix s) (positive_select s 194) (lex_13_194_image s)

theorem lex_13_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4986), (Sat.Literal.pos 194), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation13 194 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4986) (Sat.Literal.pos 194) (Sat.Literal.pos 97) (lex_13_194_prefix s) (positive_select s 194) (lex_13_194_image s)

theorem lex_13_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4987), (Sat.Literal.pos 4986)] :=
  (lex_13_194_gate s).prop _ (List.Mem.head _)

theorem lex_13_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4987), (Sat.Literal.neg 194), (Sat.Literal.pos 97)] :=
  (lex_13_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4987), (Sat.Literal.pos 194), (Sat.Literal.neg 97)] :=
  (lex_13_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4986), (Sat.Literal.neg 194), (Sat.Literal.neg 97), (Sat.Literal.pos 4987)] :=
  (lex_13_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4986), (Sat.Literal.pos 194), (Sat.Literal.pos 97), (Sat.Literal.pos 4987)] :=
  (lex_13_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4987) = lexBefore s permutation13 193 := by
  exact (positive_lex_of_descriptor s 4987 permutation13 194 (by rfl)).trans ((lex_skipped s permutation13 193 194 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 224) = s (permuteMask permutation13 193) := by
  exact (positive_select s 224).trans (congrArg s (show (224 : Fin 256) = permuteMask permutation13 193 by rw [image13_eq]; rfl))

theorem lex_13_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4988) (Sat.Literal.pos 4987) (Sat.Literal.pos 193) (Sat.Literal.pos 224)) := by
  exact equality_gate s permutation13 193 (assignment s)
    (Sat.Literal.pos 4988) (Sat.Literal.pos 4987) (Sat.Literal.pos 193) (Sat.Literal.pos 224) (positive_of_descriptor s 4988 (.lex permutation13 193) (by rfl)) (lex_13_193_prefix s) (positive_select s 193) (lex_13_193_image s)

theorem lex_13_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4987), (Sat.Literal.pos 193), (Sat.Literal.neg 224)] := by
  exact comparison_gate s permutation13 193 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4987) (Sat.Literal.pos 193) (Sat.Literal.pos 224) (lex_13_193_prefix s) (positive_select s 193) (lex_13_193_image s)

theorem lex_13_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4988), (Sat.Literal.pos 4987)] :=
  (lex_13_193_gate s).prop _ (List.Mem.head _)

theorem lex_13_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4988), (Sat.Literal.neg 193), (Sat.Literal.pos 224)] :=
  (lex_13_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4988), (Sat.Literal.pos 193), (Sat.Literal.neg 224)] :=
  (lex_13_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4987), (Sat.Literal.neg 193), (Sat.Literal.neg 224), (Sat.Literal.pos 4988)] :=
  (lex_13_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4987), (Sat.Literal.pos 193), (Sat.Literal.pos 224), (Sat.Literal.pos 4988)] :=
  (lex_13_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4988) = lexBefore s permutation13 192 := by
  exact (positive_lex_of_descriptor s 4988 permutation13 193 (by rfl)).trans ((lex_skipped s permutation13 192 193 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 96) = s (permuteMask permutation13 192) := by
  exact (positive_select s 96).trans (congrArg s (show (96 : Fin 256) = permuteMask permutation13 192 by rw [image13_eq]; rfl))

theorem lex_13_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4989) (Sat.Literal.pos 4988) (Sat.Literal.pos 192) (Sat.Literal.pos 96)) := by
  exact equality_gate s permutation13 192 (assignment s)
    (Sat.Literal.pos 4989) (Sat.Literal.pos 4988) (Sat.Literal.pos 192) (Sat.Literal.pos 96) (positive_of_descriptor s 4989 (.lex permutation13 192) (by rfl)) (lex_13_192_prefix s) (positive_select s 192) (lex_13_192_image s)

theorem lex_13_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4988), (Sat.Literal.pos 192), (Sat.Literal.neg 96)] := by
  exact comparison_gate s permutation13 192 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4988) (Sat.Literal.pos 192) (Sat.Literal.pos 96) (lex_13_192_prefix s) (positive_select s 192) (lex_13_192_image s)

theorem lex_13_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4989), (Sat.Literal.pos 4988)] :=
  (lex_13_192_gate s).prop _ (List.Mem.head _)

theorem lex_13_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4989), (Sat.Literal.neg 192), (Sat.Literal.pos 96)] :=
  (lex_13_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4989), (Sat.Literal.pos 192), (Sat.Literal.neg 96)] :=
  (lex_13_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4988), (Sat.Literal.neg 192), (Sat.Literal.neg 96), (Sat.Literal.pos 4989)] :=
  (lex_13_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4988), (Sat.Literal.pos 192), (Sat.Literal.pos 96), (Sat.Literal.pos 4989)] :=
  (lex_13_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4989) = lexBefore s permutation13 191 := by
  exact (positive_lex_of_descriptor s 4989 permutation13 192 (by rfl)).trans ((lex_skipped s permutation13 191 192 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation13 191) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation13 191 by rw [image13_eq]; rfl))

theorem lex_13_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4990) (Sat.Literal.pos 4989) (Sat.Literal.pos 191) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation13 191 (assignment s)
    (Sat.Literal.pos 4990) (Sat.Literal.pos 4989) (Sat.Literal.pos 191) (Sat.Literal.pos 223) (positive_of_descriptor s 4990 (.lex permutation13 191) (by rfl)) (lex_13_191_prefix s) (positive_select s 191) (lex_13_191_image s)

theorem lex_13_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4989), (Sat.Literal.pos 191), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation13 191 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4989) (Sat.Literal.pos 191) (Sat.Literal.pos 223) (lex_13_191_prefix s) (positive_select s 191) (lex_13_191_image s)

theorem lex_13_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4990), (Sat.Literal.pos 4989)] :=
  (lex_13_191_gate s).prop _ (List.Mem.head _)

theorem lex_13_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4990), (Sat.Literal.neg 191), (Sat.Literal.pos 223)] :=
  (lex_13_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4990), (Sat.Literal.pos 191), (Sat.Literal.neg 223)] :=
  (lex_13_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4989), (Sat.Literal.neg 191), (Sat.Literal.neg 223), (Sat.Literal.pos 4990)] :=
  (lex_13_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4989), (Sat.Literal.pos 191), (Sat.Literal.pos 223), (Sat.Literal.pos 4990)] :=
  (lex_13_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4990) = lexBefore s permutation13 190 := by
  exact (positive_lex_of_descriptor s 4990 permutation13 191 (by rfl)).trans ((lex_skipped s permutation13 190 191 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation13 190) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation13 190 by rw [image13_eq]; rfl))

theorem lex_13_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4991) (Sat.Literal.pos 4990) (Sat.Literal.pos 190) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation13 190 (assignment s)
    (Sat.Literal.pos 4991) (Sat.Literal.pos 4990) (Sat.Literal.pos 190) (Sat.Literal.pos 95) (positive_of_descriptor s 4991 (.lex permutation13 190) (by rfl)) (lex_13_190_prefix s) (positive_select s 190) (lex_13_190_image s)

theorem lex_13_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4990), (Sat.Literal.pos 190), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation13 190 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4990) (Sat.Literal.pos 190) (Sat.Literal.pos 95) (lex_13_190_prefix s) (positive_select s 190) (lex_13_190_image s)

theorem lex_13_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4991), (Sat.Literal.pos 4990)] :=
  (lex_13_190_gate s).prop _ (List.Mem.head _)

theorem lex_13_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4991), (Sat.Literal.neg 190), (Sat.Literal.pos 95)] :=
  (lex_13_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4991), (Sat.Literal.pos 190), (Sat.Literal.neg 95)] :=
  (lex_13_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4990), (Sat.Literal.neg 190), (Sat.Literal.neg 95), (Sat.Literal.pos 4991)] :=
  (lex_13_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4990), (Sat.Literal.pos 190), (Sat.Literal.pos 95), (Sat.Literal.pos 4991)] :=
  (lex_13_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4991) = lexBefore s permutation13 189 := by
  exact (positive_lex_of_descriptor s 4991 permutation13 190 (by rfl)).trans ((lex_skipped s permutation13 189 190 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation13 189) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation13 189 by rw [image13_eq]; rfl))

theorem lex_13_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4992) (Sat.Literal.pos 4991) (Sat.Literal.pos 189) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation13 189 (assignment s)
    (Sat.Literal.pos 4992) (Sat.Literal.pos 4991) (Sat.Literal.pos 189) (Sat.Literal.pos 222) (positive_of_descriptor s 4992 (.lex permutation13 189) (by rfl)) (lex_13_189_prefix s) (positive_select s 189) (lex_13_189_image s)

theorem lex_13_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4991), (Sat.Literal.pos 189), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation13 189 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4991) (Sat.Literal.pos 189) (Sat.Literal.pos 222) (lex_13_189_prefix s) (positive_select s 189) (lex_13_189_image s)

theorem lex_13_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4992), (Sat.Literal.pos 4991)] :=
  (lex_13_189_gate s).prop _ (List.Mem.head _)

theorem lex_13_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4992), (Sat.Literal.neg 189), (Sat.Literal.pos 222)] :=
  (lex_13_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4992), (Sat.Literal.pos 189), (Sat.Literal.neg 222)] :=
  (lex_13_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4991), (Sat.Literal.neg 189), (Sat.Literal.neg 222), (Sat.Literal.pos 4992)] :=
  (lex_13_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4991), (Sat.Literal.pos 189), (Sat.Literal.pos 222), (Sat.Literal.pos 4992)] :=
  (lex_13_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4992) = lexBefore s permutation13 188 := by
  exact (positive_lex_of_descriptor s 4992 permutation13 189 (by rfl)).trans ((lex_skipped s permutation13 188 189 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation13 188) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation13 188 by rw [image13_eq]; rfl))

theorem lex_13_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4993) (Sat.Literal.pos 4992) (Sat.Literal.pos 188) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation13 188 (assignment s)
    (Sat.Literal.pos 4993) (Sat.Literal.pos 4992) (Sat.Literal.pos 188) (Sat.Literal.pos 94) (positive_of_descriptor s 4993 (.lex permutation13 188) (by rfl)) (lex_13_188_prefix s) (positive_select s 188) (lex_13_188_image s)

theorem lex_13_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4992), (Sat.Literal.pos 188), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation13 188 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4992) (Sat.Literal.pos 188) (Sat.Literal.pos 94) (lex_13_188_prefix s) (positive_select s 188) (lex_13_188_image s)

theorem lex_13_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4993), (Sat.Literal.pos 4992)] :=
  (lex_13_188_gate s).prop _ (List.Mem.head _)

theorem lex_13_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4993), (Sat.Literal.neg 188), (Sat.Literal.pos 94)] :=
  (lex_13_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4993), (Sat.Literal.pos 188), (Sat.Literal.neg 94)] :=
  (lex_13_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4992), (Sat.Literal.neg 188), (Sat.Literal.neg 94), (Sat.Literal.pos 4993)] :=
  (lex_13_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4992), (Sat.Literal.pos 188), (Sat.Literal.pos 94), (Sat.Literal.pos 4993)] :=
  (lex_13_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4993) = lexBefore s permutation13 187 := by
  exact (positive_lex_of_descriptor s 4993 permutation13 188 (by rfl)).trans ((lex_skipped s permutation13 187 188 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation13 187) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation13 187 by rw [image13_eq]; rfl))

theorem lex_13_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4994) (Sat.Literal.pos 4993) (Sat.Literal.pos 187) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation13 187 (assignment s)
    (Sat.Literal.pos 4994) (Sat.Literal.pos 4993) (Sat.Literal.pos 187) (Sat.Literal.pos 221) (positive_of_descriptor s 4994 (.lex permutation13 187) (by rfl)) (lex_13_187_prefix s) (positive_select s 187) (lex_13_187_image s)

theorem lex_13_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4993), (Sat.Literal.pos 187), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation13 187 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4993) (Sat.Literal.pos 187) (Sat.Literal.pos 221) (lex_13_187_prefix s) (positive_select s 187) (lex_13_187_image s)

theorem lex_13_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4994), (Sat.Literal.pos 4993)] :=
  (lex_13_187_gate s).prop _ (List.Mem.head _)

theorem lex_13_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4994), (Sat.Literal.neg 187), (Sat.Literal.pos 221)] :=
  (lex_13_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4994), (Sat.Literal.pos 187), (Sat.Literal.neg 221)] :=
  (lex_13_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4993), (Sat.Literal.neg 187), (Sat.Literal.neg 221), (Sat.Literal.pos 4994)] :=
  (lex_13_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4993), (Sat.Literal.pos 187), (Sat.Literal.pos 221), (Sat.Literal.pos 4994)] :=
  (lex_13_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4994) = lexBefore s permutation13 186 := by
  exact (positive_lex_of_descriptor s 4994 permutation13 187 (by rfl)).trans ((lex_skipped s permutation13 186 187 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation13 186) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation13 186 by rw [image13_eq]; rfl))

theorem lex_13_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4995) (Sat.Literal.pos 4994) (Sat.Literal.pos 186) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation13 186 (assignment s)
    (Sat.Literal.pos 4995) (Sat.Literal.pos 4994) (Sat.Literal.pos 186) (Sat.Literal.pos 93) (positive_of_descriptor s 4995 (.lex permutation13 186) (by rfl)) (lex_13_186_prefix s) (positive_select s 186) (lex_13_186_image s)

theorem lex_13_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4994), (Sat.Literal.pos 186), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation13 186 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4994) (Sat.Literal.pos 186) (Sat.Literal.pos 93) (lex_13_186_prefix s) (positive_select s 186) (lex_13_186_image s)

theorem lex_13_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4995), (Sat.Literal.pos 4994)] :=
  (lex_13_186_gate s).prop _ (List.Mem.head _)

theorem lex_13_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4995), (Sat.Literal.neg 186), (Sat.Literal.pos 93)] :=
  (lex_13_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4995), (Sat.Literal.pos 186), (Sat.Literal.neg 93)] :=
  (lex_13_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4994), (Sat.Literal.neg 186), (Sat.Literal.neg 93), (Sat.Literal.pos 4995)] :=
  (lex_13_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4994), (Sat.Literal.pos 186), (Sat.Literal.pos 93), (Sat.Literal.pos 4995)] :=
  (lex_13_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4995) = lexBefore s permutation13 185 := by
  exact (positive_lex_of_descriptor s 4995 permutation13 186 (by rfl)).trans ((lex_skipped s permutation13 185 186 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation13 185) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation13 185 by rw [image13_eq]; rfl))

theorem lex_13_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4996) (Sat.Literal.pos 4995) (Sat.Literal.pos 185) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation13 185 (assignment s)
    (Sat.Literal.pos 4996) (Sat.Literal.pos 4995) (Sat.Literal.pos 185) (Sat.Literal.pos 220) (positive_of_descriptor s 4996 (.lex permutation13 185) (by rfl)) (lex_13_185_prefix s) (positive_select s 185) (lex_13_185_image s)

theorem lex_13_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4995), (Sat.Literal.pos 185), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation13 185 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4995) (Sat.Literal.pos 185) (Sat.Literal.pos 220) (lex_13_185_prefix s) (positive_select s 185) (lex_13_185_image s)

theorem lex_13_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4996), (Sat.Literal.pos 4995)] :=
  (lex_13_185_gate s).prop _ (List.Mem.head _)

theorem lex_13_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4996), (Sat.Literal.neg 185), (Sat.Literal.pos 220)] :=
  (lex_13_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4996), (Sat.Literal.pos 185), (Sat.Literal.neg 220)] :=
  (lex_13_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4995), (Sat.Literal.neg 185), (Sat.Literal.neg 220), (Sat.Literal.pos 4996)] :=
  (lex_13_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4995), (Sat.Literal.pos 185), (Sat.Literal.pos 220), (Sat.Literal.pos 4996)] :=
  (lex_13_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4996) = lexBefore s permutation13 184 := by
  exact (positive_lex_of_descriptor s 4996 permutation13 185 (by rfl)).trans ((lex_skipped s permutation13 184 185 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation13 184) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation13 184 by rw [image13_eq]; rfl))

theorem lex_13_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4997) (Sat.Literal.pos 4996) (Sat.Literal.pos 184) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation13 184 (assignment s)
    (Sat.Literal.pos 4997) (Sat.Literal.pos 4996) (Sat.Literal.pos 184) (Sat.Literal.pos 92) (positive_of_descriptor s 4997 (.lex permutation13 184) (by rfl)) (lex_13_184_prefix s) (positive_select s 184) (lex_13_184_image s)

theorem lex_13_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4996), (Sat.Literal.pos 184), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation13 184 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4996) (Sat.Literal.pos 184) (Sat.Literal.pos 92) (lex_13_184_prefix s) (positive_select s 184) (lex_13_184_image s)

theorem lex_13_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4997), (Sat.Literal.pos 4996)] :=
  (lex_13_184_gate s).prop _ (List.Mem.head _)

theorem lex_13_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4997), (Sat.Literal.neg 184), (Sat.Literal.pos 92)] :=
  (lex_13_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4997), (Sat.Literal.pos 184), (Sat.Literal.neg 92)] :=
  (lex_13_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4996), (Sat.Literal.neg 184), (Sat.Literal.neg 92), (Sat.Literal.pos 4997)] :=
  (lex_13_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4996), (Sat.Literal.pos 184), (Sat.Literal.pos 92), (Sat.Literal.pos 4997)] :=
  (lex_13_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4997) = lexBefore s permutation13 183 := by
  exact (positive_lex_of_descriptor s 4997 permutation13 184 (by rfl)).trans ((lex_skipped s permutation13 183 184 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation13 183) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation13 183 by rw [image13_eq]; rfl))

theorem lex_13_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4998) (Sat.Literal.pos 4997) (Sat.Literal.pos 183) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation13 183 (assignment s)
    (Sat.Literal.pos 4998) (Sat.Literal.pos 4997) (Sat.Literal.pos 183) (Sat.Literal.pos 219) (positive_of_descriptor s 4998 (.lex permutation13 183) (by rfl)) (lex_13_183_prefix s) (positive_select s 183) (lex_13_183_image s)

theorem lex_13_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4997), (Sat.Literal.pos 183), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation13 183 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4997) (Sat.Literal.pos 183) (Sat.Literal.pos 219) (lex_13_183_prefix s) (positive_select s 183) (lex_13_183_image s)

theorem lex_13_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4998), (Sat.Literal.pos 4997)] :=
  (lex_13_183_gate s).prop _ (List.Mem.head _)

theorem lex_13_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4998), (Sat.Literal.neg 183), (Sat.Literal.pos 219)] :=
  (lex_13_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4998), (Sat.Literal.pos 183), (Sat.Literal.neg 219)] :=
  (lex_13_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4997), (Sat.Literal.neg 183), (Sat.Literal.neg 219), (Sat.Literal.pos 4998)] :=
  (lex_13_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4997), (Sat.Literal.pos 183), (Sat.Literal.pos 219), (Sat.Literal.pos 4998)] :=
  (lex_13_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4998) = lexBefore s permutation13 182 := by
  exact (positive_lex_of_descriptor s 4998 permutation13 183 (by rfl)).trans ((lex_skipped s permutation13 182 183 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation13 182) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation13 182 by rw [image13_eq]; rfl))

theorem lex_13_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4999) (Sat.Literal.pos 4998) (Sat.Literal.pos 182) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation13 182 (assignment s)
    (Sat.Literal.pos 4999) (Sat.Literal.pos 4998) (Sat.Literal.pos 182) (Sat.Literal.pos 91) (positive_of_descriptor s 4999 (.lex permutation13 182) (by rfl)) (lex_13_182_prefix s) (positive_select s 182) (lex_13_182_image s)

theorem lex_13_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4998), (Sat.Literal.pos 182), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation13 182 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4998) (Sat.Literal.pos 182) (Sat.Literal.pos 91) (lex_13_182_prefix s) (positive_select s 182) (lex_13_182_image s)

theorem lex_13_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4999), (Sat.Literal.pos 4998)] :=
  (lex_13_182_gate s).prop _ (List.Mem.head _)

theorem lex_13_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4999), (Sat.Literal.neg 182), (Sat.Literal.pos 91)] :=
  (lex_13_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4999), (Sat.Literal.pos 182), (Sat.Literal.neg 91)] :=
  (lex_13_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4998), (Sat.Literal.neg 182), (Sat.Literal.neg 91), (Sat.Literal.pos 4999)] :=
  (lex_13_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4998), (Sat.Literal.pos 182), (Sat.Literal.pos 91), (Sat.Literal.pos 4999)] :=
  (lex_13_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4999) = lexBefore s permutation13 181 := by
  exact (positive_lex_of_descriptor s 4999 permutation13 182 (by rfl)).trans ((lex_skipped s permutation13 181 182 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation13 181) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation13 181 by rw [image13_eq]; rfl))

theorem lex_13_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5000) (Sat.Literal.pos 4999) (Sat.Literal.pos 181) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation13 181 (assignment s)
    (Sat.Literal.pos 5000) (Sat.Literal.pos 4999) (Sat.Literal.pos 181) (Sat.Literal.pos 218) (positive_of_descriptor s 5000 (.lex permutation13 181) (by rfl)) (lex_13_181_prefix s) (positive_select s 181) (lex_13_181_image s)

theorem lex_13_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4999), (Sat.Literal.pos 181), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation13 181 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 4999) (Sat.Literal.pos 181) (Sat.Literal.pos 218) (lex_13_181_prefix s) (positive_select s 181) (lex_13_181_image s)

theorem lex_13_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5000), (Sat.Literal.pos 4999)] :=
  (lex_13_181_gate s).prop _ (List.Mem.head _)

theorem lex_13_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5000), (Sat.Literal.neg 181), (Sat.Literal.pos 218)] :=
  (lex_13_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5000), (Sat.Literal.pos 181), (Sat.Literal.neg 218)] :=
  (lex_13_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4999), (Sat.Literal.neg 181), (Sat.Literal.neg 218), (Sat.Literal.pos 5000)] :=
  (lex_13_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4999), (Sat.Literal.pos 181), (Sat.Literal.pos 218), (Sat.Literal.pos 5000)] :=
  (lex_13_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5000) = lexBefore s permutation13 180 := by
  exact (positive_lex_of_descriptor s 5000 permutation13 181 (by rfl)).trans ((lex_skipped s permutation13 180 181 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation13 180) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation13 180 by rw [image13_eq]; rfl))

theorem lex_13_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5001) (Sat.Literal.pos 5000) (Sat.Literal.pos 180) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation13 180 (assignment s)
    (Sat.Literal.pos 5001) (Sat.Literal.pos 5000) (Sat.Literal.pos 180) (Sat.Literal.pos 90) (positive_of_descriptor s 5001 (.lex permutation13 180) (by rfl)) (lex_13_180_prefix s) (positive_select s 180) (lex_13_180_image s)

theorem lex_13_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5000), (Sat.Literal.pos 180), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation13 180 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5000) (Sat.Literal.pos 180) (Sat.Literal.pos 90) (lex_13_180_prefix s) (positive_select s 180) (lex_13_180_image s)

theorem lex_13_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5001), (Sat.Literal.pos 5000)] :=
  (lex_13_180_gate s).prop _ (List.Mem.head _)

theorem lex_13_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5001), (Sat.Literal.neg 180), (Sat.Literal.pos 90)] :=
  (lex_13_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5001), (Sat.Literal.pos 180), (Sat.Literal.neg 90)] :=
  (lex_13_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5000), (Sat.Literal.neg 180), (Sat.Literal.neg 90), (Sat.Literal.pos 5001)] :=
  (lex_13_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5000), (Sat.Literal.pos 180), (Sat.Literal.pos 90), (Sat.Literal.pos 5001)] :=
  (lex_13_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5001) = lexBefore s permutation13 179 := by
  exact (positive_lex_of_descriptor s 5001 permutation13 180 (by rfl)).trans ((lex_skipped s permutation13 179 180 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation13 179) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation13 179 by rw [image13_eq]; rfl))

theorem lex_13_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5002) (Sat.Literal.pos 5001) (Sat.Literal.pos 179) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation13 179 (assignment s)
    (Sat.Literal.pos 5002) (Sat.Literal.pos 5001) (Sat.Literal.pos 179) (Sat.Literal.pos 217) (positive_of_descriptor s 5002 (.lex permutation13 179) (by rfl)) (lex_13_179_prefix s) (positive_select s 179) (lex_13_179_image s)

theorem lex_13_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5001), (Sat.Literal.pos 179), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation13 179 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5001) (Sat.Literal.pos 179) (Sat.Literal.pos 217) (lex_13_179_prefix s) (positive_select s 179) (lex_13_179_image s)

theorem lex_13_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5002), (Sat.Literal.pos 5001)] :=
  (lex_13_179_gate s).prop _ (List.Mem.head _)

theorem lex_13_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5002), (Sat.Literal.neg 179), (Sat.Literal.pos 217)] :=
  (lex_13_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5002), (Sat.Literal.pos 179), (Sat.Literal.neg 217)] :=
  (lex_13_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5001), (Sat.Literal.neg 179), (Sat.Literal.neg 217), (Sat.Literal.pos 5002)] :=
  (lex_13_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5001), (Sat.Literal.pos 179), (Sat.Literal.pos 217), (Sat.Literal.pos 5002)] :=
  (lex_13_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5002) = lexBefore s permutation13 178 := by
  exact (positive_lex_of_descriptor s 5002 permutation13 179 (by rfl)).trans ((lex_skipped s permutation13 178 179 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation13 178) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation13 178 by rw [image13_eq]; rfl))

theorem lex_13_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5003) (Sat.Literal.pos 5002) (Sat.Literal.pos 178) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation13 178 (assignment s)
    (Sat.Literal.pos 5003) (Sat.Literal.pos 5002) (Sat.Literal.pos 178) (Sat.Literal.pos 89) (positive_of_descriptor s 5003 (.lex permutation13 178) (by rfl)) (lex_13_178_prefix s) (positive_select s 178) (lex_13_178_image s)

theorem lex_13_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5002), (Sat.Literal.pos 178), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation13 178 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5002) (Sat.Literal.pos 178) (Sat.Literal.pos 89) (lex_13_178_prefix s) (positive_select s 178) (lex_13_178_image s)

theorem lex_13_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5003), (Sat.Literal.pos 5002)] :=
  (lex_13_178_gate s).prop _ (List.Mem.head _)

theorem lex_13_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5003), (Sat.Literal.neg 178), (Sat.Literal.pos 89)] :=
  (lex_13_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5003), (Sat.Literal.pos 178), (Sat.Literal.neg 89)] :=
  (lex_13_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5002), (Sat.Literal.neg 178), (Sat.Literal.neg 89), (Sat.Literal.pos 5003)] :=
  (lex_13_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5002), (Sat.Literal.pos 178), (Sat.Literal.pos 89), (Sat.Literal.pos 5003)] :=
  (lex_13_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5003) = lexBefore s permutation13 177 := by
  exact (positive_lex_of_descriptor s 5003 permutation13 178 (by rfl)).trans ((lex_skipped s permutation13 177 178 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation13 177) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation13 177 by rw [image13_eq]; rfl))

theorem lex_13_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5004) (Sat.Literal.pos 5003) (Sat.Literal.pos 177) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation13 177 (assignment s)
    (Sat.Literal.pos 5004) (Sat.Literal.pos 5003) (Sat.Literal.pos 177) (Sat.Literal.pos 216) (positive_of_descriptor s 5004 (.lex permutation13 177) (by rfl)) (lex_13_177_prefix s) (positive_select s 177) (lex_13_177_image s)

theorem lex_13_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5003), (Sat.Literal.pos 177), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation13 177 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5003) (Sat.Literal.pos 177) (Sat.Literal.pos 216) (lex_13_177_prefix s) (positive_select s 177) (lex_13_177_image s)

theorem lex_13_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5004), (Sat.Literal.pos 5003)] :=
  (lex_13_177_gate s).prop _ (List.Mem.head _)

theorem lex_13_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5004), (Sat.Literal.neg 177), (Sat.Literal.pos 216)] :=
  (lex_13_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5004), (Sat.Literal.pos 177), (Sat.Literal.neg 216)] :=
  (lex_13_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5003), (Sat.Literal.neg 177), (Sat.Literal.neg 216), (Sat.Literal.pos 5004)] :=
  (lex_13_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5003), (Sat.Literal.pos 177), (Sat.Literal.pos 216), (Sat.Literal.pos 5004)] :=
  (lex_13_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5004) = lexBefore s permutation13 176 := by
  exact (positive_lex_of_descriptor s 5004 permutation13 177 (by rfl)).trans ((lex_skipped s permutation13 176 177 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation13 176) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation13 176 by rw [image13_eq]; rfl))

theorem lex_13_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5005) (Sat.Literal.pos 5004) (Sat.Literal.pos 176) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation13 176 (assignment s)
    (Sat.Literal.pos 5005) (Sat.Literal.pos 5004) (Sat.Literal.pos 176) (Sat.Literal.pos 88) (positive_of_descriptor s 5005 (.lex permutation13 176) (by rfl)) (lex_13_176_prefix s) (positive_select s 176) (lex_13_176_image s)

theorem lex_13_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5004), (Sat.Literal.pos 176), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation13 176 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5004) (Sat.Literal.pos 176) (Sat.Literal.pos 88) (lex_13_176_prefix s) (positive_select s 176) (lex_13_176_image s)

theorem lex_13_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5005), (Sat.Literal.pos 5004)] :=
  (lex_13_176_gate s).prop _ (List.Mem.head _)

theorem lex_13_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5005), (Sat.Literal.neg 176), (Sat.Literal.pos 88)] :=
  (lex_13_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5005), (Sat.Literal.pos 176), (Sat.Literal.neg 88)] :=
  (lex_13_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5004), (Sat.Literal.neg 176), (Sat.Literal.neg 88), (Sat.Literal.pos 5005)] :=
  (lex_13_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5004), (Sat.Literal.pos 176), (Sat.Literal.pos 88), (Sat.Literal.pos 5005)] :=
  (lex_13_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5005) = lexBefore s permutation13 175 := by
  exact (positive_lex_of_descriptor s 5005 permutation13 176 (by rfl)).trans ((lex_skipped s permutation13 175 176 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation13 175) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation13 175 by rw [image13_eq]; rfl))

theorem lex_13_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5006) (Sat.Literal.pos 5005) (Sat.Literal.pos 175) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation13 175 (assignment s)
    (Sat.Literal.pos 5006) (Sat.Literal.pos 5005) (Sat.Literal.pos 175) (Sat.Literal.pos 215) (positive_of_descriptor s 5006 (.lex permutation13 175) (by rfl)) (lex_13_175_prefix s) (positive_select s 175) (lex_13_175_image s)

theorem lex_13_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5005), (Sat.Literal.pos 175), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation13 175 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5005) (Sat.Literal.pos 175) (Sat.Literal.pos 215) (lex_13_175_prefix s) (positive_select s 175) (lex_13_175_image s)

theorem lex_13_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5006), (Sat.Literal.pos 5005)] :=
  (lex_13_175_gate s).prop _ (List.Mem.head _)

theorem lex_13_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5006), (Sat.Literal.neg 175), (Sat.Literal.pos 215)] :=
  (lex_13_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5006), (Sat.Literal.pos 175), (Sat.Literal.neg 215)] :=
  (lex_13_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5005), (Sat.Literal.neg 175), (Sat.Literal.neg 215), (Sat.Literal.pos 5006)] :=
  (lex_13_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5005), (Sat.Literal.pos 175), (Sat.Literal.pos 215), (Sat.Literal.pos 5006)] :=
  (lex_13_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5006) = lexBefore s permutation13 174 := by
  exact (positive_lex_of_descriptor s 5006 permutation13 175 (by rfl)).trans ((lex_skipped s permutation13 174 175 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation13 174) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation13 174 by rw [image13_eq]; rfl))

theorem lex_13_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5007) (Sat.Literal.pos 5006) (Sat.Literal.pos 174) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation13 174 (assignment s)
    (Sat.Literal.pos 5007) (Sat.Literal.pos 5006) (Sat.Literal.pos 174) (Sat.Literal.pos 87) (positive_of_descriptor s 5007 (.lex permutation13 174) (by rfl)) (lex_13_174_prefix s) (positive_select s 174) (lex_13_174_image s)

theorem lex_13_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5006), (Sat.Literal.pos 174), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation13 174 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5006) (Sat.Literal.pos 174) (Sat.Literal.pos 87) (lex_13_174_prefix s) (positive_select s 174) (lex_13_174_image s)

theorem lex_13_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5007), (Sat.Literal.pos 5006)] :=
  (lex_13_174_gate s).prop _ (List.Mem.head _)

theorem lex_13_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5007), (Sat.Literal.neg 174), (Sat.Literal.pos 87)] :=
  (lex_13_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5007), (Sat.Literal.pos 174), (Sat.Literal.neg 87)] :=
  (lex_13_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5006), (Sat.Literal.neg 174), (Sat.Literal.neg 87), (Sat.Literal.pos 5007)] :=
  (lex_13_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5006), (Sat.Literal.pos 174), (Sat.Literal.pos 87), (Sat.Literal.pos 5007)] :=
  (lex_13_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5007) = lexBefore s permutation13 173 := by
  exact (positive_lex_of_descriptor s 5007 permutation13 174 (by rfl)).trans ((lex_skipped s permutation13 173 174 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation13 173) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation13 173 by rw [image13_eq]; rfl))

theorem lex_13_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5008) (Sat.Literal.pos 5007) (Sat.Literal.pos 173) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation13 173 (assignment s)
    (Sat.Literal.pos 5008) (Sat.Literal.pos 5007) (Sat.Literal.pos 173) (Sat.Literal.pos 214) (positive_of_descriptor s 5008 (.lex permutation13 173) (by rfl)) (lex_13_173_prefix s) (positive_select s 173) (lex_13_173_image s)

theorem lex_13_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5007), (Sat.Literal.pos 173), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation13 173 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5007) (Sat.Literal.pos 173) (Sat.Literal.pos 214) (lex_13_173_prefix s) (positive_select s 173) (lex_13_173_image s)

theorem lex_13_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5008), (Sat.Literal.pos 5007)] :=
  (lex_13_173_gate s).prop _ (List.Mem.head _)

theorem lex_13_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5008), (Sat.Literal.neg 173), (Sat.Literal.pos 214)] :=
  (lex_13_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5008), (Sat.Literal.pos 173), (Sat.Literal.neg 214)] :=
  (lex_13_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5007), (Sat.Literal.neg 173), (Sat.Literal.neg 214), (Sat.Literal.pos 5008)] :=
  (lex_13_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5007), (Sat.Literal.pos 173), (Sat.Literal.pos 214), (Sat.Literal.pos 5008)] :=
  (lex_13_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5008) = lexBefore s permutation13 172 := by
  exact (positive_lex_of_descriptor s 5008 permutation13 173 (by rfl)).trans ((lex_skipped s permutation13 172 173 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation13 172) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation13 172 by rw [image13_eq]; rfl))

theorem lex_13_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5009) (Sat.Literal.pos 5008) (Sat.Literal.pos 172) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation13 172 (assignment s)
    (Sat.Literal.pos 5009) (Sat.Literal.pos 5008) (Sat.Literal.pos 172) (Sat.Literal.pos 86) (positive_of_descriptor s 5009 (.lex permutation13 172) (by rfl)) (lex_13_172_prefix s) (positive_select s 172) (lex_13_172_image s)

theorem lex_13_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5008), (Sat.Literal.pos 172), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation13 172 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5008) (Sat.Literal.pos 172) (Sat.Literal.pos 86) (lex_13_172_prefix s) (positive_select s 172) (lex_13_172_image s)

theorem lex_13_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5009), (Sat.Literal.pos 5008)] :=
  (lex_13_172_gate s).prop _ (List.Mem.head _)

theorem lex_13_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5009), (Sat.Literal.neg 172), (Sat.Literal.pos 86)] :=
  (lex_13_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5009), (Sat.Literal.pos 172), (Sat.Literal.neg 86)] :=
  (lex_13_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5008), (Sat.Literal.neg 172), (Sat.Literal.neg 86), (Sat.Literal.pos 5009)] :=
  (lex_13_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5008), (Sat.Literal.pos 172), (Sat.Literal.pos 86), (Sat.Literal.pos 5009)] :=
  (lex_13_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5009) = lexBefore s permutation13 171 := by
  exact (positive_lex_of_descriptor s 5009 permutation13 172 (by rfl)).trans ((lex_skipped s permutation13 171 172 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation13 171) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation13 171 by rw [image13_eq]; rfl))

theorem lex_13_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5010) (Sat.Literal.pos 5009) (Sat.Literal.pos 171) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation13 171 (assignment s)
    (Sat.Literal.pos 5010) (Sat.Literal.pos 5009) (Sat.Literal.pos 171) (Sat.Literal.pos 213) (positive_of_descriptor s 5010 (.lex permutation13 171) (by rfl)) (lex_13_171_prefix s) (positive_select s 171) (lex_13_171_image s)

theorem lex_13_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5009), (Sat.Literal.pos 171), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation13 171 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5009) (Sat.Literal.pos 171) (Sat.Literal.pos 213) (lex_13_171_prefix s) (positive_select s 171) (lex_13_171_image s)

theorem lex_13_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5010), (Sat.Literal.pos 5009)] :=
  (lex_13_171_gate s).prop _ (List.Mem.head _)

theorem lex_13_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5010), (Sat.Literal.neg 171), (Sat.Literal.pos 213)] :=
  (lex_13_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5010), (Sat.Literal.pos 171), (Sat.Literal.neg 213)] :=
  (lex_13_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5009), (Sat.Literal.neg 171), (Sat.Literal.neg 213), (Sat.Literal.pos 5010)] :=
  (lex_13_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5009), (Sat.Literal.pos 171), (Sat.Literal.pos 213), (Sat.Literal.pos 5010)] :=
  (lex_13_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5010) = lexBefore s permutation13 170 := by
  exact (positive_lex_of_descriptor s 5010 permutation13 171 (by rfl)).trans ((lex_skipped s permutation13 170 171 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation13 170) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation13 170 by rw [image13_eq]; rfl))

theorem lex_13_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5011) (Sat.Literal.pos 5010) (Sat.Literal.pos 170) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation13 170 (assignment s)
    (Sat.Literal.pos 5011) (Sat.Literal.pos 5010) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (positive_of_descriptor s 5011 (.lex permutation13 170) (by rfl)) (lex_13_170_prefix s) (positive_select s 170) (lex_13_170_image s)

theorem lex_13_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5010), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation13 170 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5010) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (lex_13_170_prefix s) (positive_select s 170) (lex_13_170_image s)

theorem lex_13_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5011), (Sat.Literal.pos 5010)] :=
  (lex_13_170_gate s).prop _ (List.Mem.head _)

theorem lex_13_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5011), (Sat.Literal.neg 170), (Sat.Literal.pos 85)] :=
  (lex_13_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5011), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] :=
  (lex_13_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5010), (Sat.Literal.neg 170), (Sat.Literal.neg 85), (Sat.Literal.pos 5011)] :=
  (lex_13_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5010), (Sat.Literal.pos 170), (Sat.Literal.pos 85), (Sat.Literal.pos 5011)] :=
  (lex_13_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5011) = lexBefore s permutation13 169 := by
  exact (positive_lex_of_descriptor s 5011 permutation13 170 (by rfl)).trans ((lex_skipped s permutation13 169 170 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation13 169) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation13 169 by rw [image13_eq]; rfl))

theorem lex_13_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5012) (Sat.Literal.pos 5011) (Sat.Literal.pos 169) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation13 169 (assignment s)
    (Sat.Literal.pos 5012) (Sat.Literal.pos 5011) (Sat.Literal.pos 169) (Sat.Literal.pos 212) (positive_of_descriptor s 5012 (.lex permutation13 169) (by rfl)) (lex_13_169_prefix s) (positive_select s 169) (lex_13_169_image s)

theorem lex_13_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5011), (Sat.Literal.pos 169), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation13 169 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5011) (Sat.Literal.pos 169) (Sat.Literal.pos 212) (lex_13_169_prefix s) (positive_select s 169) (lex_13_169_image s)

theorem lex_13_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5012), (Sat.Literal.pos 5011)] :=
  (lex_13_169_gate s).prop _ (List.Mem.head _)

theorem lex_13_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5012), (Sat.Literal.neg 169), (Sat.Literal.pos 212)] :=
  (lex_13_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5012), (Sat.Literal.pos 169), (Sat.Literal.neg 212)] :=
  (lex_13_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5011), (Sat.Literal.neg 169), (Sat.Literal.neg 212), (Sat.Literal.pos 5012)] :=
  (lex_13_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5011), (Sat.Literal.pos 169), (Sat.Literal.pos 212), (Sat.Literal.pos 5012)] :=
  (lex_13_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5012) = lexBefore s permutation13 168 := by
  exact (positive_lex_of_descriptor s 5012 permutation13 169 (by rfl)).trans ((lex_skipped s permutation13 168 169 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation13 168) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation13 168 by rw [image13_eq]; rfl))

theorem lex_13_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5013) (Sat.Literal.pos 5012) (Sat.Literal.pos 168) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation13 168 (assignment s)
    (Sat.Literal.pos 5013) (Sat.Literal.pos 5012) (Sat.Literal.pos 168) (Sat.Literal.pos 84) (positive_of_descriptor s 5013 (.lex permutation13 168) (by rfl)) (lex_13_168_prefix s) (positive_select s 168) (lex_13_168_image s)

theorem lex_13_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5012), (Sat.Literal.pos 168), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation13 168 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5012) (Sat.Literal.pos 168) (Sat.Literal.pos 84) (lex_13_168_prefix s) (positive_select s 168) (lex_13_168_image s)

theorem lex_13_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5013), (Sat.Literal.pos 5012)] :=
  (lex_13_168_gate s).prop _ (List.Mem.head _)

theorem lex_13_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5013), (Sat.Literal.neg 168), (Sat.Literal.pos 84)] :=
  (lex_13_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5013), (Sat.Literal.pos 168), (Sat.Literal.neg 84)] :=
  (lex_13_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5012), (Sat.Literal.neg 168), (Sat.Literal.neg 84), (Sat.Literal.pos 5013)] :=
  (lex_13_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5012), (Sat.Literal.pos 168), (Sat.Literal.pos 84), (Sat.Literal.pos 5013)] :=
  (lex_13_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5013) = lexBefore s permutation13 167 := by
  exact (positive_lex_of_descriptor s 5013 permutation13 168 (by rfl)).trans ((lex_skipped s permutation13 167 168 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation13 167) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation13 167 by rw [image13_eq]; rfl))

theorem lex_13_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5014) (Sat.Literal.pos 5013) (Sat.Literal.pos 167) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation13 167 (assignment s)
    (Sat.Literal.pos 5014) (Sat.Literal.pos 5013) (Sat.Literal.pos 167) (Sat.Literal.pos 211) (positive_of_descriptor s 5014 (.lex permutation13 167) (by rfl)) (lex_13_167_prefix s) (positive_select s 167) (lex_13_167_image s)

theorem lex_13_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5013), (Sat.Literal.pos 167), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation13 167 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5013) (Sat.Literal.pos 167) (Sat.Literal.pos 211) (lex_13_167_prefix s) (positive_select s 167) (lex_13_167_image s)

theorem lex_13_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5014), (Sat.Literal.pos 5013)] :=
  (lex_13_167_gate s).prop _ (List.Mem.head _)

theorem lex_13_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5014), (Sat.Literal.neg 167), (Sat.Literal.pos 211)] :=
  (lex_13_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5014), (Sat.Literal.pos 167), (Sat.Literal.neg 211)] :=
  (lex_13_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5013), (Sat.Literal.neg 167), (Sat.Literal.neg 211), (Sat.Literal.pos 5014)] :=
  (lex_13_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5013), (Sat.Literal.pos 167), (Sat.Literal.pos 211), (Sat.Literal.pos 5014)] :=
  (lex_13_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5014) = lexBefore s permutation13 166 := by
  exact (positive_lex_of_descriptor s 5014 permutation13 167 (by rfl)).trans ((lex_skipped s permutation13 166 167 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation13 166) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation13 166 by rw [image13_eq]; rfl))

theorem lex_13_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5015) (Sat.Literal.pos 5014) (Sat.Literal.pos 166) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation13 166 (assignment s)
    (Sat.Literal.pos 5015) (Sat.Literal.pos 5014) (Sat.Literal.pos 166) (Sat.Literal.pos 83) (positive_of_descriptor s 5015 (.lex permutation13 166) (by rfl)) (lex_13_166_prefix s) (positive_select s 166) (lex_13_166_image s)

theorem lex_13_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5014), (Sat.Literal.pos 166), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation13 166 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5014) (Sat.Literal.pos 166) (Sat.Literal.pos 83) (lex_13_166_prefix s) (positive_select s 166) (lex_13_166_image s)

theorem lex_13_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5015), (Sat.Literal.pos 5014)] :=
  (lex_13_166_gate s).prop _ (List.Mem.head _)

theorem lex_13_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5015), (Sat.Literal.neg 166), (Sat.Literal.pos 83)] :=
  (lex_13_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5015), (Sat.Literal.pos 166), (Sat.Literal.neg 83)] :=
  (lex_13_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5014), (Sat.Literal.neg 166), (Sat.Literal.neg 83), (Sat.Literal.pos 5015)] :=
  (lex_13_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5014), (Sat.Literal.pos 166), (Sat.Literal.pos 83), (Sat.Literal.pos 5015)] :=
  (lex_13_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5015) = lexBefore s permutation13 165 := by
  exact (positive_lex_of_descriptor s 5015 permutation13 166 (by rfl)).trans ((lex_skipped s permutation13 165 166 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation13 165) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation13 165 by rw [image13_eq]; rfl))

theorem lex_13_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5016) (Sat.Literal.pos 5015) (Sat.Literal.pos 165) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation13 165 (assignment s)
    (Sat.Literal.pos 5016) (Sat.Literal.pos 5015) (Sat.Literal.pos 165) (Sat.Literal.pos 210) (positive_of_descriptor s 5016 (.lex permutation13 165) (by rfl)) (lex_13_165_prefix s) (positive_select s 165) (lex_13_165_image s)

theorem lex_13_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5015), (Sat.Literal.pos 165), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation13 165 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5015) (Sat.Literal.pos 165) (Sat.Literal.pos 210) (lex_13_165_prefix s) (positive_select s 165) (lex_13_165_image s)

theorem lex_13_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5016), (Sat.Literal.pos 5015)] :=
  (lex_13_165_gate s).prop _ (List.Mem.head _)

theorem lex_13_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5016), (Sat.Literal.neg 165), (Sat.Literal.pos 210)] :=
  (lex_13_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5016), (Sat.Literal.pos 165), (Sat.Literal.neg 210)] :=
  (lex_13_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5015), (Sat.Literal.neg 165), (Sat.Literal.neg 210), (Sat.Literal.pos 5016)] :=
  (lex_13_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5015), (Sat.Literal.pos 165), (Sat.Literal.pos 210), (Sat.Literal.pos 5016)] :=
  (lex_13_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5016) = lexBefore s permutation13 164 := by
  exact (positive_lex_of_descriptor s 5016 permutation13 165 (by rfl)).trans ((lex_skipped s permutation13 164 165 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation13 164) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation13 164 by rw [image13_eq]; rfl))

theorem lex_13_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5017) (Sat.Literal.pos 5016) (Sat.Literal.pos 164) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation13 164 (assignment s)
    (Sat.Literal.pos 5017) (Sat.Literal.pos 5016) (Sat.Literal.pos 164) (Sat.Literal.pos 82) (positive_of_descriptor s 5017 (.lex permutation13 164) (by rfl)) (lex_13_164_prefix s) (positive_select s 164) (lex_13_164_image s)

theorem lex_13_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5016), (Sat.Literal.pos 164), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation13 164 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5016) (Sat.Literal.pos 164) (Sat.Literal.pos 82) (lex_13_164_prefix s) (positive_select s 164) (lex_13_164_image s)

theorem lex_13_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5017), (Sat.Literal.pos 5016)] :=
  (lex_13_164_gate s).prop _ (List.Mem.head _)

theorem lex_13_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5017), (Sat.Literal.neg 164), (Sat.Literal.pos 82)] :=
  (lex_13_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5017), (Sat.Literal.pos 164), (Sat.Literal.neg 82)] :=
  (lex_13_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5016), (Sat.Literal.neg 164), (Sat.Literal.neg 82), (Sat.Literal.pos 5017)] :=
  (lex_13_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5016), (Sat.Literal.pos 164), (Sat.Literal.pos 82), (Sat.Literal.pos 5017)] :=
  (lex_13_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5017) = lexBefore s permutation13 163 := by
  exact (positive_lex_of_descriptor s 5017 permutation13 164 (by rfl)).trans ((lex_skipped s permutation13 163 164 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation13 163) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation13 163 by rw [image13_eq]; rfl))

theorem lex_13_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5018) (Sat.Literal.pos 5017) (Sat.Literal.pos 163) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation13 163 (assignment s)
    (Sat.Literal.pos 5018) (Sat.Literal.pos 5017) (Sat.Literal.pos 163) (Sat.Literal.pos 209) (positive_of_descriptor s 5018 (.lex permutation13 163) (by rfl)) (lex_13_163_prefix s) (positive_select s 163) (lex_13_163_image s)

theorem lex_13_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5017), (Sat.Literal.pos 163), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation13 163 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5017) (Sat.Literal.pos 163) (Sat.Literal.pos 209) (lex_13_163_prefix s) (positive_select s 163) (lex_13_163_image s)

theorem lex_13_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5018), (Sat.Literal.pos 5017)] :=
  (lex_13_163_gate s).prop _ (List.Mem.head _)

theorem lex_13_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5018), (Sat.Literal.neg 163), (Sat.Literal.pos 209)] :=
  (lex_13_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5018), (Sat.Literal.pos 163), (Sat.Literal.neg 209)] :=
  (lex_13_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5017), (Sat.Literal.neg 163), (Sat.Literal.neg 209), (Sat.Literal.pos 5018)] :=
  (lex_13_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5017), (Sat.Literal.pos 163), (Sat.Literal.pos 209), (Sat.Literal.pos 5018)] :=
  (lex_13_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5018) = lexBefore s permutation13 162 := by
  exact (positive_lex_of_descriptor s 5018 permutation13 163 (by rfl)).trans ((lex_skipped s permutation13 162 163 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation13 162) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation13 162 by rw [image13_eq]; rfl))

theorem lex_13_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5019) (Sat.Literal.pos 5018) (Sat.Literal.pos 162) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation13 162 (assignment s)
    (Sat.Literal.pos 5019) (Sat.Literal.pos 5018) (Sat.Literal.pos 162) (Sat.Literal.pos 81) (positive_of_descriptor s 5019 (.lex permutation13 162) (by rfl)) (lex_13_162_prefix s) (positive_select s 162) (lex_13_162_image s)

theorem lex_13_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5018), (Sat.Literal.pos 162), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation13 162 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5018) (Sat.Literal.pos 162) (Sat.Literal.pos 81) (lex_13_162_prefix s) (positive_select s 162) (lex_13_162_image s)

theorem lex_13_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5019), (Sat.Literal.pos 5018)] :=
  (lex_13_162_gate s).prop _ (List.Mem.head _)

theorem lex_13_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5019), (Sat.Literal.neg 162), (Sat.Literal.pos 81)] :=
  (lex_13_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5019), (Sat.Literal.pos 162), (Sat.Literal.neg 81)] :=
  (lex_13_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5018), (Sat.Literal.neg 162), (Sat.Literal.neg 81), (Sat.Literal.pos 5019)] :=
  (lex_13_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5018), (Sat.Literal.pos 162), (Sat.Literal.pos 81), (Sat.Literal.pos 5019)] :=
  (lex_13_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5019) = lexBefore s permutation13 161 := by
  exact (positive_lex_of_descriptor s 5019 permutation13 162 (by rfl)).trans ((lex_skipped s permutation13 161 162 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 208) = s (permuteMask permutation13 161) := by
  exact (positive_select s 208).trans (congrArg s (show (208 : Fin 256) = permuteMask permutation13 161 by rw [image13_eq]; rfl))

theorem lex_13_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5020) (Sat.Literal.pos 5019) (Sat.Literal.pos 161) (Sat.Literal.pos 208)) := by
  exact equality_gate s permutation13 161 (assignment s)
    (Sat.Literal.pos 5020) (Sat.Literal.pos 5019) (Sat.Literal.pos 161) (Sat.Literal.pos 208) (positive_of_descriptor s 5020 (.lex permutation13 161) (by rfl)) (lex_13_161_prefix s) (positive_select s 161) (lex_13_161_image s)

theorem lex_13_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5019), (Sat.Literal.pos 161), (Sat.Literal.neg 208)] := by
  exact comparison_gate s permutation13 161 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5019) (Sat.Literal.pos 161) (Sat.Literal.pos 208) (lex_13_161_prefix s) (positive_select s 161) (lex_13_161_image s)

theorem lex_13_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5020), (Sat.Literal.pos 5019)] :=
  (lex_13_161_gate s).prop _ (List.Mem.head _)

theorem lex_13_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5020), (Sat.Literal.neg 161), (Sat.Literal.pos 208)] :=
  (lex_13_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5020), (Sat.Literal.pos 161), (Sat.Literal.neg 208)] :=
  (lex_13_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5019), (Sat.Literal.neg 161), (Sat.Literal.neg 208), (Sat.Literal.pos 5020)] :=
  (lex_13_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5019), (Sat.Literal.pos 161), (Sat.Literal.pos 208), (Sat.Literal.pos 5020)] :=
  (lex_13_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5020) = lexBefore s permutation13 160 := by
  exact (positive_lex_of_descriptor s 5020 permutation13 161 (by rfl)).trans ((lex_skipped s permutation13 160 161 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation13 160) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation13 160 by rw [image13_eq]; rfl))

theorem lex_13_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5021) (Sat.Literal.pos 5020) (Sat.Literal.pos 160) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation13 160 (assignment s)
    (Sat.Literal.pos 5021) (Sat.Literal.pos 5020) (Sat.Literal.pos 160) (Sat.Literal.pos 80) (positive_of_descriptor s 5021 (.lex permutation13 160) (by rfl)) (lex_13_160_prefix s) (positive_select s 160) (lex_13_160_image s)

theorem lex_13_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5020), (Sat.Literal.pos 160), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation13 160 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5020) (Sat.Literal.pos 160) (Sat.Literal.pos 80) (lex_13_160_prefix s) (positive_select s 160) (lex_13_160_image s)

theorem lex_13_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5021), (Sat.Literal.pos 5020)] :=
  (lex_13_160_gate s).prop _ (List.Mem.head _)

theorem lex_13_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5021), (Sat.Literal.neg 160), (Sat.Literal.pos 80)] :=
  (lex_13_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5021), (Sat.Literal.pos 160), (Sat.Literal.neg 80)] :=
  (lex_13_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5020), (Sat.Literal.neg 160), (Sat.Literal.neg 80), (Sat.Literal.pos 5021)] :=
  (lex_13_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5020), (Sat.Literal.pos 160), (Sat.Literal.pos 80), (Sat.Literal.pos 5021)] :=
  (lex_13_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5021) = lexBefore s permutation13 159 := by
  exact (positive_lex_of_descriptor s 5021 permutation13 160 (by rfl)).trans ((lex_skipped s permutation13 159 160 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation13 159) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation13 159 by rw [image13_eq]; rfl))

theorem lex_13_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5022) (Sat.Literal.pos 5021) (Sat.Literal.pos 159) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation13 159 (assignment s)
    (Sat.Literal.pos 5022) (Sat.Literal.pos 5021) (Sat.Literal.pos 159) (Sat.Literal.pos 207) (positive_of_descriptor s 5022 (.lex permutation13 159) (by rfl)) (lex_13_159_prefix s) (positive_select s 159) (lex_13_159_image s)

theorem lex_13_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5021), (Sat.Literal.pos 159), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation13 159 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5021) (Sat.Literal.pos 159) (Sat.Literal.pos 207) (lex_13_159_prefix s) (positive_select s 159) (lex_13_159_image s)

theorem lex_13_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5022), (Sat.Literal.pos 5021)] :=
  (lex_13_159_gate s).prop _ (List.Mem.head _)

theorem lex_13_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5022), (Sat.Literal.neg 159), (Sat.Literal.pos 207)] :=
  (lex_13_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5022), (Sat.Literal.pos 159), (Sat.Literal.neg 207)] :=
  (lex_13_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5021), (Sat.Literal.neg 159), (Sat.Literal.neg 207), (Sat.Literal.pos 5022)] :=
  (lex_13_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5021), (Sat.Literal.pos 159), (Sat.Literal.pos 207), (Sat.Literal.pos 5022)] :=
  (lex_13_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5022) = lexBefore s permutation13 158 := by
  exact (positive_lex_of_descriptor s 5022 permutation13 159 (by rfl)).trans ((lex_skipped s permutation13 158 159 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation13 158) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation13 158 by rw [image13_eq]; rfl))

theorem lex_13_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5023) (Sat.Literal.pos 5022) (Sat.Literal.pos 158) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation13 158 (assignment s)
    (Sat.Literal.pos 5023) (Sat.Literal.pos 5022) (Sat.Literal.pos 158) (Sat.Literal.pos 79) (positive_of_descriptor s 5023 (.lex permutation13 158) (by rfl)) (lex_13_158_prefix s) (positive_select s 158) (lex_13_158_image s)

theorem lex_13_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5022), (Sat.Literal.pos 158), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation13 158 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5022) (Sat.Literal.pos 158) (Sat.Literal.pos 79) (lex_13_158_prefix s) (positive_select s 158) (lex_13_158_image s)

theorem lex_13_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5023), (Sat.Literal.pos 5022)] :=
  (lex_13_158_gate s).prop _ (List.Mem.head _)

theorem lex_13_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5023), (Sat.Literal.neg 158), (Sat.Literal.pos 79)] :=
  (lex_13_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5023), (Sat.Literal.pos 158), (Sat.Literal.neg 79)] :=
  (lex_13_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5022), (Sat.Literal.neg 158), (Sat.Literal.neg 79), (Sat.Literal.pos 5023)] :=
  (lex_13_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5022), (Sat.Literal.pos 158), (Sat.Literal.pos 79), (Sat.Literal.pos 5023)] :=
  (lex_13_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_13_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 5023) = lexBefore s permutation13 157 := by
  exact (positive_lex_of_descriptor s 5023 permutation13 158 (by rfl)).trans ((lex_skipped s permutation13 157 158 (by decide) (by intro j hj hp; rw [image13_eq]; exact fixedOnRange_spec image13 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_13_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation13 157) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation13 157 by rw [image13_eq]; rfl))

theorem lex_13_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 5024) (Sat.Literal.pos 5023) (Sat.Literal.pos 157) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation13 157 (assignment s)
    (Sat.Literal.pos 5024) (Sat.Literal.pos 5023) (Sat.Literal.pos 157) (Sat.Literal.pos 206) (positive_of_descriptor s 5024 (.lex permutation13 157) (by rfl)) (lex_13_157_prefix s) (positive_select s 157) (lex_13_157_image s)

theorem lex_13_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5023), (Sat.Literal.pos 157), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation13 157 (hmax permutation13) (assignment s)
    (Sat.Literal.pos 5023) (Sat.Literal.pos 157) (Sat.Literal.pos 206) (lex_13_157_prefix s) (positive_select s 157) (lex_13_157_image s)

theorem lex_13_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5024), (Sat.Literal.pos 5023)] :=
  (lex_13_157_gate s).prop _ (List.Mem.head _)

theorem lex_13_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5024), (Sat.Literal.neg 157), (Sat.Literal.pos 206)] :=
  (lex_13_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_13_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5024), (Sat.Literal.pos 157), (Sat.Literal.neg 206)] :=
  (lex_13_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_13_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5023), (Sat.Literal.neg 157), (Sat.Literal.neg 206), (Sat.Literal.pos 5024)] :=
  (lex_13_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_13_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 5023), (Sat.Literal.pos 157), (Sat.Literal.pos 206), (Sat.Literal.pos 5024)] :=
  (lex_13_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_12_2_gate

end Crown.CertificateData
