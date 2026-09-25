import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_0_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation0 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation0 254 (by intro j hj; rw [image0_eq]; exact fixedOnRange_spec image0 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_0_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation0 254) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation0 254 by rw [image0_eq]; rfl))

theorem lex_0_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2525) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation0 254 (assignment s)
    (Sat.Literal.pos 2525) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 253) (positive_of_descriptor s 2525 (.lex permutation0 254) (by rfl)) (lex_0_254_prefix s) (positive_select s 254) (lex_0_254_image s)

theorem lex_0_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation0 254 (hmax permutation0) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 253) (lex_0_254_prefix s) (positive_select s 254) (lex_0_254_image s)

theorem lex_0_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2525), (Sat.Literal.neg 256)] :=
  (lex_0_254_gate s).prop _ (List.Mem.head _)

theorem lex_0_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2525), (Sat.Literal.neg 254), (Sat.Literal.pos 253)] :=
  (lex_0_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2525), (Sat.Literal.pos 254), (Sat.Literal.neg 253)] :=
  (lex_0_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 253), (Sat.Literal.pos 2525)] :=
  (lex_0_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 253), (Sat.Literal.pos 2525)] :=
  (lex_0_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2525) = lexBefore s permutation0 253 := by
  exact (positive_lex_of_descriptor s 2525 permutation0 254 (by rfl)).trans ((lex_skipped s permutation0 253 254 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation0 253) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation0 253 by rw [image0_eq]; rfl))

theorem lex_0_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2526) (Sat.Literal.pos 2525) (Sat.Literal.pos 253) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation0 253 (assignment s)
    (Sat.Literal.pos 2526) (Sat.Literal.pos 2525) (Sat.Literal.pos 253) (Sat.Literal.pos 254) (positive_of_descriptor s 2526 (.lex permutation0 253) (by rfl)) (lex_0_253_prefix s) (positive_select s 253) (lex_0_253_image s)

theorem lex_0_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2525), (Sat.Literal.pos 253), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation0 253 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2525) (Sat.Literal.pos 253) (Sat.Literal.pos 254) (lex_0_253_prefix s) (positive_select s 253) (lex_0_253_image s)

theorem lex_0_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2526), (Sat.Literal.pos 2525)] :=
  (lex_0_253_gate s).prop _ (List.Mem.head _)

theorem lex_0_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2526), (Sat.Literal.neg 253), (Sat.Literal.pos 254)] :=
  (lex_0_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2526), (Sat.Literal.pos 253), (Sat.Literal.neg 254)] :=
  (lex_0_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2525), (Sat.Literal.neg 253), (Sat.Literal.neg 254), (Sat.Literal.pos 2526)] :=
  (lex_0_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2525), (Sat.Literal.pos 253), (Sat.Literal.pos 254), (Sat.Literal.pos 2526)] :=
  (lex_0_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2526) = lexBefore s permutation0 250 := by
  exact (positive_lex_of_descriptor s 2526 permutation0 253 (by rfl)).trans ((lex_skipped s permutation0 250 253 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 251 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation0 250) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation0 250 by rw [image0_eq]; rfl))

theorem lex_0_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2527) (Sat.Literal.pos 2526) (Sat.Literal.pos 250) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation0 250 (assignment s)
    (Sat.Literal.pos 2527) (Sat.Literal.pos 2526) (Sat.Literal.pos 250) (Sat.Literal.pos 249) (positive_of_descriptor s 2527 (.lex permutation0 250) (by rfl)) (lex_0_250_prefix s) (positive_select s 250) (lex_0_250_image s)

theorem lex_0_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2526), (Sat.Literal.pos 250), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation0 250 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2526) (Sat.Literal.pos 250) (Sat.Literal.pos 249) (lex_0_250_prefix s) (positive_select s 250) (lex_0_250_image s)

theorem lex_0_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2527), (Sat.Literal.pos 2526)] :=
  (lex_0_250_gate s).prop _ (List.Mem.head _)

theorem lex_0_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2527), (Sat.Literal.neg 250), (Sat.Literal.pos 249)] :=
  (lex_0_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2527), (Sat.Literal.pos 250), (Sat.Literal.neg 249)] :=
  (lex_0_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2526), (Sat.Literal.neg 250), (Sat.Literal.neg 249), (Sat.Literal.pos 2527)] :=
  (lex_0_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2526), (Sat.Literal.pos 250), (Sat.Literal.pos 249), (Sat.Literal.pos 2527)] :=
  (lex_0_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2527) = lexBefore s permutation0 249 := by
  exact (positive_lex_of_descriptor s 2527 permutation0 250 (by rfl)).trans ((lex_skipped s permutation0 249 250 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation0 249) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation0 249 by rw [image0_eq]; rfl))

theorem lex_0_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2528) (Sat.Literal.pos 2527) (Sat.Literal.pos 249) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation0 249 (assignment s)
    (Sat.Literal.pos 2528) (Sat.Literal.pos 2527) (Sat.Literal.pos 249) (Sat.Literal.pos 250) (positive_of_descriptor s 2528 (.lex permutation0 249) (by rfl)) (lex_0_249_prefix s) (positive_select s 249) (lex_0_249_image s)

theorem lex_0_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2527), (Sat.Literal.pos 249), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation0 249 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2527) (Sat.Literal.pos 249) (Sat.Literal.pos 250) (lex_0_249_prefix s) (positive_select s 249) (lex_0_249_image s)

theorem lex_0_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2528), (Sat.Literal.pos 2527)] :=
  (lex_0_249_gate s).prop _ (List.Mem.head _)

theorem lex_0_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2528), (Sat.Literal.neg 249), (Sat.Literal.pos 250)] :=
  (lex_0_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2528), (Sat.Literal.pos 249), (Sat.Literal.neg 250)] :=
  (lex_0_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2527), (Sat.Literal.neg 249), (Sat.Literal.neg 250), (Sat.Literal.pos 2528)] :=
  (lex_0_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2527), (Sat.Literal.pos 249), (Sat.Literal.pos 250), (Sat.Literal.pos 2528)] :=
  (lex_0_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2528) = lexBefore s permutation0 246 := by
  exact (positive_lex_of_descriptor s 2528 permutation0 249 (by rfl)).trans ((lex_skipped s permutation0 246 249 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 247 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation0 246) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation0 246 by rw [image0_eq]; rfl))

theorem lex_0_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2529) (Sat.Literal.pos 2528) (Sat.Literal.pos 246) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation0 246 (assignment s)
    (Sat.Literal.pos 2529) (Sat.Literal.pos 2528) (Sat.Literal.pos 246) (Sat.Literal.pos 245) (positive_of_descriptor s 2529 (.lex permutation0 246) (by rfl)) (lex_0_246_prefix s) (positive_select s 246) (lex_0_246_image s)

theorem lex_0_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2528), (Sat.Literal.pos 246), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation0 246 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2528) (Sat.Literal.pos 246) (Sat.Literal.pos 245) (lex_0_246_prefix s) (positive_select s 246) (lex_0_246_image s)

theorem lex_0_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2529), (Sat.Literal.pos 2528)] :=
  (lex_0_246_gate s).prop _ (List.Mem.head _)

theorem lex_0_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2529), (Sat.Literal.neg 246), (Sat.Literal.pos 245)] :=
  (lex_0_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2529), (Sat.Literal.pos 246), (Sat.Literal.neg 245)] :=
  (lex_0_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2528), (Sat.Literal.neg 246), (Sat.Literal.neg 245), (Sat.Literal.pos 2529)] :=
  (lex_0_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2528), (Sat.Literal.pos 246), (Sat.Literal.pos 245), (Sat.Literal.pos 2529)] :=
  (lex_0_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2529) = lexBefore s permutation0 245 := by
  exact (positive_lex_of_descriptor s 2529 permutation0 246 (by rfl)).trans ((lex_skipped s permutation0 245 246 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation0 245) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation0 245 by rw [image0_eq]; rfl))

theorem lex_0_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2530) (Sat.Literal.pos 2529) (Sat.Literal.pos 245) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation0 245 (assignment s)
    (Sat.Literal.pos 2530) (Sat.Literal.pos 2529) (Sat.Literal.pos 245) (Sat.Literal.pos 246) (positive_of_descriptor s 2530 (.lex permutation0 245) (by rfl)) (lex_0_245_prefix s) (positive_select s 245) (lex_0_245_image s)

theorem lex_0_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2529), (Sat.Literal.pos 245), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation0 245 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2529) (Sat.Literal.pos 245) (Sat.Literal.pos 246) (lex_0_245_prefix s) (positive_select s 245) (lex_0_245_image s)

theorem lex_0_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2530), (Sat.Literal.pos 2529)] :=
  (lex_0_245_gate s).prop _ (List.Mem.head _)

theorem lex_0_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2530), (Sat.Literal.neg 245), (Sat.Literal.pos 246)] :=
  (lex_0_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2530), (Sat.Literal.pos 245), (Sat.Literal.neg 246)] :=
  (lex_0_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2529), (Sat.Literal.neg 245), (Sat.Literal.neg 246), (Sat.Literal.pos 2530)] :=
  (lex_0_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2529), (Sat.Literal.pos 245), (Sat.Literal.pos 246), (Sat.Literal.pos 2530)] :=
  (lex_0_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2530) = lexBefore s permutation0 242 := by
  exact (positive_lex_of_descriptor s 2530 permutation0 245 (by rfl)).trans ((lex_skipped s permutation0 242 245 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 243 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation0 242) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation0 242 by rw [image0_eq]; rfl))

theorem lex_0_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2531) (Sat.Literal.pos 2530) (Sat.Literal.pos 242) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation0 242 (assignment s)
    (Sat.Literal.pos 2531) (Sat.Literal.pos 2530) (Sat.Literal.pos 242) (Sat.Literal.pos 241) (positive_of_descriptor s 2531 (.lex permutation0 242) (by rfl)) (lex_0_242_prefix s) (positive_select s 242) (lex_0_242_image s)

theorem lex_0_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2530), (Sat.Literal.pos 242), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation0 242 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2530) (Sat.Literal.pos 242) (Sat.Literal.pos 241) (lex_0_242_prefix s) (positive_select s 242) (lex_0_242_image s)

theorem lex_0_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2531), (Sat.Literal.pos 2530)] :=
  (lex_0_242_gate s).prop _ (List.Mem.head _)

theorem lex_0_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2531), (Sat.Literal.neg 242), (Sat.Literal.pos 241)] :=
  (lex_0_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2531), (Sat.Literal.pos 242), (Sat.Literal.neg 241)] :=
  (lex_0_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2530), (Sat.Literal.neg 242), (Sat.Literal.neg 241), (Sat.Literal.pos 2531)] :=
  (lex_0_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2530), (Sat.Literal.pos 242), (Sat.Literal.pos 241), (Sat.Literal.pos 2531)] :=
  (lex_0_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2531) = lexBefore s permutation0 241 := by
  exact (positive_lex_of_descriptor s 2531 permutation0 242 (by rfl)).trans ((lex_skipped s permutation0 241 242 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation0 241) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation0 241 by rw [image0_eq]; rfl))

theorem lex_0_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2532) (Sat.Literal.pos 2531) (Sat.Literal.pos 241) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation0 241 (assignment s)
    (Sat.Literal.pos 2532) (Sat.Literal.pos 2531) (Sat.Literal.pos 241) (Sat.Literal.pos 242) (positive_of_descriptor s 2532 (.lex permutation0 241) (by rfl)) (lex_0_241_prefix s) (positive_select s 241) (lex_0_241_image s)

theorem lex_0_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2531), (Sat.Literal.pos 241), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation0 241 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2531) (Sat.Literal.pos 241) (Sat.Literal.pos 242) (lex_0_241_prefix s) (positive_select s 241) (lex_0_241_image s)

theorem lex_0_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2532), (Sat.Literal.pos 2531)] :=
  (lex_0_241_gate s).prop _ (List.Mem.head _)

theorem lex_0_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2532), (Sat.Literal.neg 241), (Sat.Literal.pos 242)] :=
  (lex_0_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2532), (Sat.Literal.pos 241), (Sat.Literal.neg 242)] :=
  (lex_0_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2531), (Sat.Literal.neg 241), (Sat.Literal.neg 242), (Sat.Literal.pos 2532)] :=
  (lex_0_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2531), (Sat.Literal.pos 241), (Sat.Literal.pos 242), (Sat.Literal.pos 2532)] :=
  (lex_0_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2532) = lexBefore s permutation0 238 := by
  exact (positive_lex_of_descriptor s 2532 permutation0 241 (by rfl)).trans ((lex_skipped s permutation0 238 241 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 239 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation0 238) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation0 238 by rw [image0_eq]; rfl))

theorem lex_0_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2533) (Sat.Literal.pos 2532) (Sat.Literal.pos 238) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation0 238 (assignment s)
    (Sat.Literal.pos 2533) (Sat.Literal.pos 2532) (Sat.Literal.pos 238) (Sat.Literal.pos 237) (positive_of_descriptor s 2533 (.lex permutation0 238) (by rfl)) (lex_0_238_prefix s) (positive_select s 238) (lex_0_238_image s)

theorem lex_0_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2532), (Sat.Literal.pos 238), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation0 238 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2532) (Sat.Literal.pos 238) (Sat.Literal.pos 237) (lex_0_238_prefix s) (positive_select s 238) (lex_0_238_image s)

theorem lex_0_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2533), (Sat.Literal.pos 2532)] :=
  (lex_0_238_gate s).prop _ (List.Mem.head _)

theorem lex_0_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2533), (Sat.Literal.neg 238), (Sat.Literal.pos 237)] :=
  (lex_0_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2533), (Sat.Literal.pos 238), (Sat.Literal.neg 237)] :=
  (lex_0_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2532), (Sat.Literal.neg 238), (Sat.Literal.neg 237), (Sat.Literal.pos 2533)] :=
  (lex_0_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2532), (Sat.Literal.pos 238), (Sat.Literal.pos 237), (Sat.Literal.pos 2533)] :=
  (lex_0_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2533) = lexBefore s permutation0 237 := by
  exact (positive_lex_of_descriptor s 2533 permutation0 238 (by rfl)).trans ((lex_skipped s permutation0 237 238 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 238) = s (permuteMask permutation0 237) := by
  exact (positive_select s 238).trans (congrArg s (show (238 : Fin 256) = permuteMask permutation0 237 by rw [image0_eq]; rfl))

theorem lex_0_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2534) (Sat.Literal.pos 2533) (Sat.Literal.pos 237) (Sat.Literal.pos 238)) := by
  exact equality_gate s permutation0 237 (assignment s)
    (Sat.Literal.pos 2534) (Sat.Literal.pos 2533) (Sat.Literal.pos 237) (Sat.Literal.pos 238) (positive_of_descriptor s 2534 (.lex permutation0 237) (by rfl)) (lex_0_237_prefix s) (positive_select s 237) (lex_0_237_image s)

theorem lex_0_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2533), (Sat.Literal.pos 237), (Sat.Literal.neg 238)] := by
  exact comparison_gate s permutation0 237 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2533) (Sat.Literal.pos 237) (Sat.Literal.pos 238) (lex_0_237_prefix s) (positive_select s 237) (lex_0_237_image s)

theorem lex_0_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2534), (Sat.Literal.pos 2533)] :=
  (lex_0_237_gate s).prop _ (List.Mem.head _)

theorem lex_0_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2534), (Sat.Literal.neg 237), (Sat.Literal.pos 238)] :=
  (lex_0_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2534), (Sat.Literal.pos 237), (Sat.Literal.neg 238)] :=
  (lex_0_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2533), (Sat.Literal.neg 237), (Sat.Literal.neg 238), (Sat.Literal.pos 2534)] :=
  (lex_0_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2533), (Sat.Literal.pos 237), (Sat.Literal.pos 238), (Sat.Literal.pos 2534)] :=
  (lex_0_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2534) = lexBefore s permutation0 234 := by
  exact (positive_lex_of_descriptor s 2534 permutation0 237 (by rfl)).trans ((lex_skipped s permutation0 234 237 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 235 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation0 234) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation0 234 by rw [image0_eq]; rfl))

theorem lex_0_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2535) (Sat.Literal.pos 2534) (Sat.Literal.pos 234) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation0 234 (assignment s)
    (Sat.Literal.pos 2535) (Sat.Literal.pos 2534) (Sat.Literal.pos 234) (Sat.Literal.pos 233) (positive_of_descriptor s 2535 (.lex permutation0 234) (by rfl)) (lex_0_234_prefix s) (positive_select s 234) (lex_0_234_image s)

theorem lex_0_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2534), (Sat.Literal.pos 234), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation0 234 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2534) (Sat.Literal.pos 234) (Sat.Literal.pos 233) (lex_0_234_prefix s) (positive_select s 234) (lex_0_234_image s)

theorem lex_0_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2535), (Sat.Literal.pos 2534)] :=
  (lex_0_234_gate s).prop _ (List.Mem.head _)

theorem lex_0_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2535), (Sat.Literal.neg 234), (Sat.Literal.pos 233)] :=
  (lex_0_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2535), (Sat.Literal.pos 234), (Sat.Literal.neg 233)] :=
  (lex_0_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2534), (Sat.Literal.neg 234), (Sat.Literal.neg 233), (Sat.Literal.pos 2535)] :=
  (lex_0_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2534), (Sat.Literal.pos 234), (Sat.Literal.pos 233), (Sat.Literal.pos 2535)] :=
  (lex_0_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2535) = lexBefore s permutation0 233 := by
  exact (positive_lex_of_descriptor s 2535 permutation0 234 (by rfl)).trans ((lex_skipped s permutation0 233 234 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 234) = s (permuteMask permutation0 233) := by
  exact (positive_select s 234).trans (congrArg s (show (234 : Fin 256) = permuteMask permutation0 233 by rw [image0_eq]; rfl))

theorem lex_0_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2536) (Sat.Literal.pos 2535) (Sat.Literal.pos 233) (Sat.Literal.pos 234)) := by
  exact equality_gate s permutation0 233 (assignment s)
    (Sat.Literal.pos 2536) (Sat.Literal.pos 2535) (Sat.Literal.pos 233) (Sat.Literal.pos 234) (positive_of_descriptor s 2536 (.lex permutation0 233) (by rfl)) (lex_0_233_prefix s) (positive_select s 233) (lex_0_233_image s)

theorem lex_0_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2535), (Sat.Literal.pos 233), (Sat.Literal.neg 234)] := by
  exact comparison_gate s permutation0 233 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2535) (Sat.Literal.pos 233) (Sat.Literal.pos 234) (lex_0_233_prefix s) (positive_select s 233) (lex_0_233_image s)

theorem lex_0_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2536), (Sat.Literal.pos 2535)] :=
  (lex_0_233_gate s).prop _ (List.Mem.head _)

theorem lex_0_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2536), (Sat.Literal.neg 233), (Sat.Literal.pos 234)] :=
  (lex_0_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2536), (Sat.Literal.pos 233), (Sat.Literal.neg 234)] :=
  (lex_0_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2535), (Sat.Literal.neg 233), (Sat.Literal.neg 234), (Sat.Literal.pos 2536)] :=
  (lex_0_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2535), (Sat.Literal.pos 233), (Sat.Literal.pos 234), (Sat.Literal.pos 2536)] :=
  (lex_0_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2536) = lexBefore s permutation0 230 := by
  exact (positive_lex_of_descriptor s 2536 permutation0 233 (by rfl)).trans ((lex_skipped s permutation0 230 233 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 231 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation0 230) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation0 230 by rw [image0_eq]; rfl))

theorem lex_0_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2537) (Sat.Literal.pos 2536) (Sat.Literal.pos 230) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation0 230 (assignment s)
    (Sat.Literal.pos 2537) (Sat.Literal.pos 2536) (Sat.Literal.pos 230) (Sat.Literal.pos 229) (positive_of_descriptor s 2537 (.lex permutation0 230) (by rfl)) (lex_0_230_prefix s) (positive_select s 230) (lex_0_230_image s)

theorem lex_0_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2536), (Sat.Literal.pos 230), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation0 230 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2536) (Sat.Literal.pos 230) (Sat.Literal.pos 229) (lex_0_230_prefix s) (positive_select s 230) (lex_0_230_image s)

theorem lex_0_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2537), (Sat.Literal.pos 2536)] :=
  (lex_0_230_gate s).prop _ (List.Mem.head _)

theorem lex_0_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2537), (Sat.Literal.neg 230), (Sat.Literal.pos 229)] :=
  (lex_0_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2537), (Sat.Literal.pos 230), (Sat.Literal.neg 229)] :=
  (lex_0_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2536), (Sat.Literal.neg 230), (Sat.Literal.neg 229), (Sat.Literal.pos 2537)] :=
  (lex_0_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2536), (Sat.Literal.pos 230), (Sat.Literal.pos 229), (Sat.Literal.pos 2537)] :=
  (lex_0_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2537) = lexBefore s permutation0 229 := by
  exact (positive_lex_of_descriptor s 2537 permutation0 230 (by rfl)).trans ((lex_skipped s permutation0 229 230 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 230) = s (permuteMask permutation0 229) := by
  exact (positive_select s 230).trans (congrArg s (show (230 : Fin 256) = permuteMask permutation0 229 by rw [image0_eq]; rfl))

theorem lex_0_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2538) (Sat.Literal.pos 2537) (Sat.Literal.pos 229) (Sat.Literal.pos 230)) := by
  exact equality_gate s permutation0 229 (assignment s)
    (Sat.Literal.pos 2538) (Sat.Literal.pos 2537) (Sat.Literal.pos 229) (Sat.Literal.pos 230) (positive_of_descriptor s 2538 (.lex permutation0 229) (by rfl)) (lex_0_229_prefix s) (positive_select s 229) (lex_0_229_image s)

theorem lex_0_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2537), (Sat.Literal.pos 229), (Sat.Literal.neg 230)] := by
  exact comparison_gate s permutation0 229 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2537) (Sat.Literal.pos 229) (Sat.Literal.pos 230) (lex_0_229_prefix s) (positive_select s 229) (lex_0_229_image s)

theorem lex_0_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2538), (Sat.Literal.pos 2537)] :=
  (lex_0_229_gate s).prop _ (List.Mem.head _)

theorem lex_0_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2538), (Sat.Literal.neg 229), (Sat.Literal.pos 230)] :=
  (lex_0_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2538), (Sat.Literal.pos 229), (Sat.Literal.neg 230)] :=
  (lex_0_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2537), (Sat.Literal.neg 229), (Sat.Literal.neg 230), (Sat.Literal.pos 2538)] :=
  (lex_0_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2537), (Sat.Literal.pos 229), (Sat.Literal.pos 230), (Sat.Literal.pos 2538)] :=
  (lex_0_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2538) = lexBefore s permutation0 226 := by
  exact (positive_lex_of_descriptor s 2538 permutation0 229 (by rfl)).trans ((lex_skipped s permutation0 226 229 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 227 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation0 226) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation0 226 by rw [image0_eq]; rfl))

theorem lex_0_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2539) (Sat.Literal.pos 2538) (Sat.Literal.pos 226) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation0 226 (assignment s)
    (Sat.Literal.pos 2539) (Sat.Literal.pos 2538) (Sat.Literal.pos 226) (Sat.Literal.pos 225) (positive_of_descriptor s 2539 (.lex permutation0 226) (by rfl)) (lex_0_226_prefix s) (positive_select s 226) (lex_0_226_image s)

theorem lex_0_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2538), (Sat.Literal.pos 226), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation0 226 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2538) (Sat.Literal.pos 226) (Sat.Literal.pos 225) (lex_0_226_prefix s) (positive_select s 226) (lex_0_226_image s)

theorem lex_0_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2539), (Sat.Literal.pos 2538)] :=
  (lex_0_226_gate s).prop _ (List.Mem.head _)

theorem lex_0_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2539), (Sat.Literal.neg 226), (Sat.Literal.pos 225)] :=
  (lex_0_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2539), (Sat.Literal.pos 226), (Sat.Literal.neg 225)] :=
  (lex_0_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2538), (Sat.Literal.neg 226), (Sat.Literal.neg 225), (Sat.Literal.pos 2539)] :=
  (lex_0_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2538), (Sat.Literal.pos 226), (Sat.Literal.pos 225), (Sat.Literal.pos 2539)] :=
  (lex_0_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2539) = lexBefore s permutation0 225 := by
  exact (positive_lex_of_descriptor s 2539 permutation0 226 (by rfl)).trans ((lex_skipped s permutation0 225 226 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 226) = s (permuteMask permutation0 225) := by
  exact (positive_select s 226).trans (congrArg s (show (226 : Fin 256) = permuteMask permutation0 225 by rw [image0_eq]; rfl))

theorem lex_0_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2540) (Sat.Literal.pos 2539) (Sat.Literal.pos 225) (Sat.Literal.pos 226)) := by
  exact equality_gate s permutation0 225 (assignment s)
    (Sat.Literal.pos 2540) (Sat.Literal.pos 2539) (Sat.Literal.pos 225) (Sat.Literal.pos 226) (positive_of_descriptor s 2540 (.lex permutation0 225) (by rfl)) (lex_0_225_prefix s) (positive_select s 225) (lex_0_225_image s)

theorem lex_0_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2539), (Sat.Literal.pos 225), (Sat.Literal.neg 226)] := by
  exact comparison_gate s permutation0 225 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2539) (Sat.Literal.pos 225) (Sat.Literal.pos 226) (lex_0_225_prefix s) (positive_select s 225) (lex_0_225_image s)

theorem lex_0_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2540), (Sat.Literal.pos 2539)] :=
  (lex_0_225_gate s).prop _ (List.Mem.head _)

theorem lex_0_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2540), (Sat.Literal.neg 225), (Sat.Literal.pos 226)] :=
  (lex_0_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2540), (Sat.Literal.pos 225), (Sat.Literal.neg 226)] :=
  (lex_0_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2539), (Sat.Literal.neg 225), (Sat.Literal.neg 226), (Sat.Literal.pos 2540)] :=
  (lex_0_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2539), (Sat.Literal.pos 225), (Sat.Literal.pos 226), (Sat.Literal.pos 2540)] :=
  (lex_0_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2540) = lexBefore s permutation0 222 := by
  exact (positive_lex_of_descriptor s 2540 permutation0 225 (by rfl)).trans ((lex_skipped s permutation0 222 225 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 223 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation0 222) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation0 222 by rw [image0_eq]; rfl))

theorem lex_0_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2541) (Sat.Literal.pos 2540) (Sat.Literal.pos 222) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation0 222 (assignment s)
    (Sat.Literal.pos 2541) (Sat.Literal.pos 2540) (Sat.Literal.pos 222) (Sat.Literal.pos 221) (positive_of_descriptor s 2541 (.lex permutation0 222) (by rfl)) (lex_0_222_prefix s) (positive_select s 222) (lex_0_222_image s)

theorem lex_0_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2540), (Sat.Literal.pos 222), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation0 222 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2540) (Sat.Literal.pos 222) (Sat.Literal.pos 221) (lex_0_222_prefix s) (positive_select s 222) (lex_0_222_image s)

theorem lex_0_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2541), (Sat.Literal.pos 2540)] :=
  (lex_0_222_gate s).prop _ (List.Mem.head _)

theorem lex_0_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2541), (Sat.Literal.neg 222), (Sat.Literal.pos 221)] :=
  (lex_0_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2541), (Sat.Literal.pos 222), (Sat.Literal.neg 221)] :=
  (lex_0_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2540), (Sat.Literal.neg 222), (Sat.Literal.neg 221), (Sat.Literal.pos 2541)] :=
  (lex_0_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2540), (Sat.Literal.pos 222), (Sat.Literal.pos 221), (Sat.Literal.pos 2541)] :=
  (lex_0_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2541) = lexBefore s permutation0 221 := by
  exact (positive_lex_of_descriptor s 2541 permutation0 222 (by rfl)).trans ((lex_skipped s permutation0 221 222 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation0 221) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation0 221 by rw [image0_eq]; rfl))

theorem lex_0_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2542) (Sat.Literal.pos 2541) (Sat.Literal.pos 221) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation0 221 (assignment s)
    (Sat.Literal.pos 2542) (Sat.Literal.pos 2541) (Sat.Literal.pos 221) (Sat.Literal.pos 222) (positive_of_descriptor s 2542 (.lex permutation0 221) (by rfl)) (lex_0_221_prefix s) (positive_select s 221) (lex_0_221_image s)

theorem lex_0_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2541), (Sat.Literal.pos 221), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation0 221 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2541) (Sat.Literal.pos 221) (Sat.Literal.pos 222) (lex_0_221_prefix s) (positive_select s 221) (lex_0_221_image s)

theorem lex_0_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2542), (Sat.Literal.pos 2541)] :=
  (lex_0_221_gate s).prop _ (List.Mem.head _)

theorem lex_0_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2542), (Sat.Literal.neg 221), (Sat.Literal.pos 222)] :=
  (lex_0_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2542), (Sat.Literal.pos 221), (Sat.Literal.neg 222)] :=
  (lex_0_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2541), (Sat.Literal.neg 221), (Sat.Literal.neg 222), (Sat.Literal.pos 2542)] :=
  (lex_0_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2541), (Sat.Literal.pos 221), (Sat.Literal.pos 222), (Sat.Literal.pos 2542)] :=
  (lex_0_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2542) = lexBefore s permutation0 218 := by
  exact (positive_lex_of_descriptor s 2542 permutation0 221 (by rfl)).trans ((lex_skipped s permutation0 218 221 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 219 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation0 218) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation0 218 by rw [image0_eq]; rfl))

theorem lex_0_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2543) (Sat.Literal.pos 2542) (Sat.Literal.pos 218) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation0 218 (assignment s)
    (Sat.Literal.pos 2543) (Sat.Literal.pos 2542) (Sat.Literal.pos 218) (Sat.Literal.pos 217) (positive_of_descriptor s 2543 (.lex permutation0 218) (by rfl)) (lex_0_218_prefix s) (positive_select s 218) (lex_0_218_image s)

theorem lex_0_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2542), (Sat.Literal.pos 218), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation0 218 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2542) (Sat.Literal.pos 218) (Sat.Literal.pos 217) (lex_0_218_prefix s) (positive_select s 218) (lex_0_218_image s)

theorem lex_0_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2543), (Sat.Literal.pos 2542)] :=
  (lex_0_218_gate s).prop _ (List.Mem.head _)

theorem lex_0_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2543), (Sat.Literal.neg 218), (Sat.Literal.pos 217)] :=
  (lex_0_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2543), (Sat.Literal.pos 218), (Sat.Literal.neg 217)] :=
  (lex_0_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2542), (Sat.Literal.neg 218), (Sat.Literal.neg 217), (Sat.Literal.pos 2543)] :=
  (lex_0_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2542), (Sat.Literal.pos 218), (Sat.Literal.pos 217), (Sat.Literal.pos 2543)] :=
  (lex_0_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2543) = lexBefore s permutation0 217 := by
  exact (positive_lex_of_descriptor s 2543 permutation0 218 (by rfl)).trans ((lex_skipped s permutation0 217 218 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation0 217) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation0 217 by rw [image0_eq]; rfl))

theorem lex_0_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2544) (Sat.Literal.pos 2543) (Sat.Literal.pos 217) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation0 217 (assignment s)
    (Sat.Literal.pos 2544) (Sat.Literal.pos 2543) (Sat.Literal.pos 217) (Sat.Literal.pos 218) (positive_of_descriptor s 2544 (.lex permutation0 217) (by rfl)) (lex_0_217_prefix s) (positive_select s 217) (lex_0_217_image s)

theorem lex_0_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2543), (Sat.Literal.pos 217), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation0 217 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2543) (Sat.Literal.pos 217) (Sat.Literal.pos 218) (lex_0_217_prefix s) (positive_select s 217) (lex_0_217_image s)

theorem lex_0_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2544), (Sat.Literal.pos 2543)] :=
  (lex_0_217_gate s).prop _ (List.Mem.head _)

theorem lex_0_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2544), (Sat.Literal.neg 217), (Sat.Literal.pos 218)] :=
  (lex_0_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2544), (Sat.Literal.pos 217), (Sat.Literal.neg 218)] :=
  (lex_0_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2543), (Sat.Literal.neg 217), (Sat.Literal.neg 218), (Sat.Literal.pos 2544)] :=
  (lex_0_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2543), (Sat.Literal.pos 217), (Sat.Literal.pos 218), (Sat.Literal.pos 2544)] :=
  (lex_0_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2544) = lexBefore s permutation0 214 := by
  exact (positive_lex_of_descriptor s 2544 permutation0 217 (by rfl)).trans ((lex_skipped s permutation0 214 217 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 215 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation0 214) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation0 214 by rw [image0_eq]; rfl))

theorem lex_0_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2545) (Sat.Literal.pos 2544) (Sat.Literal.pos 214) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation0 214 (assignment s)
    (Sat.Literal.pos 2545) (Sat.Literal.pos 2544) (Sat.Literal.pos 214) (Sat.Literal.pos 213) (positive_of_descriptor s 2545 (.lex permutation0 214) (by rfl)) (lex_0_214_prefix s) (positive_select s 214) (lex_0_214_image s)

theorem lex_0_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2544), (Sat.Literal.pos 214), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation0 214 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2544) (Sat.Literal.pos 214) (Sat.Literal.pos 213) (lex_0_214_prefix s) (positive_select s 214) (lex_0_214_image s)

theorem lex_0_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2545), (Sat.Literal.pos 2544)] :=
  (lex_0_214_gate s).prop _ (List.Mem.head _)

theorem lex_0_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2545), (Sat.Literal.neg 214), (Sat.Literal.pos 213)] :=
  (lex_0_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2545), (Sat.Literal.pos 214), (Sat.Literal.neg 213)] :=
  (lex_0_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2544), (Sat.Literal.neg 214), (Sat.Literal.neg 213), (Sat.Literal.pos 2545)] :=
  (lex_0_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2544), (Sat.Literal.pos 214), (Sat.Literal.pos 213), (Sat.Literal.pos 2545)] :=
  (lex_0_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2545) = lexBefore s permutation0 213 := by
  exact (positive_lex_of_descriptor s 2545 permutation0 214 (by rfl)).trans ((lex_skipped s permutation0 213 214 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation0 213) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation0 213 by rw [image0_eq]; rfl))

theorem lex_0_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2546) (Sat.Literal.pos 2545) (Sat.Literal.pos 213) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation0 213 (assignment s)
    (Sat.Literal.pos 2546) (Sat.Literal.pos 2545) (Sat.Literal.pos 213) (Sat.Literal.pos 214) (positive_of_descriptor s 2546 (.lex permutation0 213) (by rfl)) (lex_0_213_prefix s) (positive_select s 213) (lex_0_213_image s)

theorem lex_0_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2545), (Sat.Literal.pos 213), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation0 213 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2545) (Sat.Literal.pos 213) (Sat.Literal.pos 214) (lex_0_213_prefix s) (positive_select s 213) (lex_0_213_image s)

theorem lex_0_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2546), (Sat.Literal.pos 2545)] :=
  (lex_0_213_gate s).prop _ (List.Mem.head _)

theorem lex_0_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2546), (Sat.Literal.neg 213), (Sat.Literal.pos 214)] :=
  (lex_0_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2546), (Sat.Literal.pos 213), (Sat.Literal.neg 214)] :=
  (lex_0_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2545), (Sat.Literal.neg 213), (Sat.Literal.neg 214), (Sat.Literal.pos 2546)] :=
  (lex_0_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2545), (Sat.Literal.pos 213), (Sat.Literal.pos 214), (Sat.Literal.pos 2546)] :=
  (lex_0_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2546) = lexBefore s permutation0 210 := by
  exact (positive_lex_of_descriptor s 2546 permutation0 213 (by rfl)).trans ((lex_skipped s permutation0 210 213 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 211 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation0 210) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation0 210 by rw [image0_eq]; rfl))

theorem lex_0_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2547) (Sat.Literal.pos 2546) (Sat.Literal.pos 210) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation0 210 (assignment s)
    (Sat.Literal.pos 2547) (Sat.Literal.pos 2546) (Sat.Literal.pos 210) (Sat.Literal.pos 209) (positive_of_descriptor s 2547 (.lex permutation0 210) (by rfl)) (lex_0_210_prefix s) (positive_select s 210) (lex_0_210_image s)

theorem lex_0_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2546), (Sat.Literal.pos 210), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation0 210 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2546) (Sat.Literal.pos 210) (Sat.Literal.pos 209) (lex_0_210_prefix s) (positive_select s 210) (lex_0_210_image s)

theorem lex_0_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2547), (Sat.Literal.pos 2546)] :=
  (lex_0_210_gate s).prop _ (List.Mem.head _)

theorem lex_0_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2547), (Sat.Literal.neg 210), (Sat.Literal.pos 209)] :=
  (lex_0_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2547), (Sat.Literal.pos 210), (Sat.Literal.neg 209)] :=
  (lex_0_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2546), (Sat.Literal.neg 210), (Sat.Literal.neg 209), (Sat.Literal.pos 2547)] :=
  (lex_0_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2546), (Sat.Literal.pos 210), (Sat.Literal.pos 209), (Sat.Literal.pos 2547)] :=
  (lex_0_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2547) = lexBefore s permutation0 209 := by
  exact (positive_lex_of_descriptor s 2547 permutation0 210 (by rfl)).trans ((lex_skipped s permutation0 209 210 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 210) = s (permuteMask permutation0 209) := by
  exact (positive_select s 210).trans (congrArg s (show (210 : Fin 256) = permuteMask permutation0 209 by rw [image0_eq]; rfl))

theorem lex_0_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2548) (Sat.Literal.pos 2547) (Sat.Literal.pos 209) (Sat.Literal.pos 210)) := by
  exact equality_gate s permutation0 209 (assignment s)
    (Sat.Literal.pos 2548) (Sat.Literal.pos 2547) (Sat.Literal.pos 209) (Sat.Literal.pos 210) (positive_of_descriptor s 2548 (.lex permutation0 209) (by rfl)) (lex_0_209_prefix s) (positive_select s 209) (lex_0_209_image s)

theorem lex_0_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2547), (Sat.Literal.pos 209), (Sat.Literal.neg 210)] := by
  exact comparison_gate s permutation0 209 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2547) (Sat.Literal.pos 209) (Sat.Literal.pos 210) (lex_0_209_prefix s) (positive_select s 209) (lex_0_209_image s)

theorem lex_0_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2548), (Sat.Literal.pos 2547)] :=
  (lex_0_209_gate s).prop _ (List.Mem.head _)

theorem lex_0_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2548), (Sat.Literal.neg 209), (Sat.Literal.pos 210)] :=
  (lex_0_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2548), (Sat.Literal.pos 209), (Sat.Literal.neg 210)] :=
  (lex_0_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2547), (Sat.Literal.neg 209), (Sat.Literal.neg 210), (Sat.Literal.pos 2548)] :=
  (lex_0_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2547), (Sat.Literal.pos 209), (Sat.Literal.pos 210), (Sat.Literal.pos 2548)] :=
  (lex_0_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2548) = lexBefore s permutation0 206 := by
  exact (positive_lex_of_descriptor s 2548 permutation0 209 (by rfl)).trans ((lex_skipped s permutation0 206 209 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 207 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation0 206) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation0 206 by rw [image0_eq]; rfl))

theorem lex_0_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2549) (Sat.Literal.pos 2548) (Sat.Literal.pos 206) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation0 206 (assignment s)
    (Sat.Literal.pos 2549) (Sat.Literal.pos 2548) (Sat.Literal.pos 206) (Sat.Literal.pos 205) (positive_of_descriptor s 2549 (.lex permutation0 206) (by rfl)) (lex_0_206_prefix s) (positive_select s 206) (lex_0_206_image s)

theorem lex_0_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2548), (Sat.Literal.pos 206), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation0 206 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2548) (Sat.Literal.pos 206) (Sat.Literal.pos 205) (lex_0_206_prefix s) (positive_select s 206) (lex_0_206_image s)

theorem lex_0_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2549), (Sat.Literal.pos 2548)] :=
  (lex_0_206_gate s).prop _ (List.Mem.head _)

theorem lex_0_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2549), (Sat.Literal.neg 206), (Sat.Literal.pos 205)] :=
  (lex_0_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2549), (Sat.Literal.pos 206), (Sat.Literal.neg 205)] :=
  (lex_0_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2548), (Sat.Literal.neg 206), (Sat.Literal.neg 205), (Sat.Literal.pos 2549)] :=
  (lex_0_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2548), (Sat.Literal.pos 206), (Sat.Literal.pos 205), (Sat.Literal.pos 2549)] :=
  (lex_0_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2549) = lexBefore s permutation0 205 := by
  exact (positive_lex_of_descriptor s 2549 permutation0 206 (by rfl)).trans ((lex_skipped s permutation0 205 206 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 206) = s (permuteMask permutation0 205) := by
  exact (positive_select s 206).trans (congrArg s (show (206 : Fin 256) = permuteMask permutation0 205 by rw [image0_eq]; rfl))

theorem lex_0_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2550) (Sat.Literal.pos 2549) (Sat.Literal.pos 205) (Sat.Literal.pos 206)) := by
  exact equality_gate s permutation0 205 (assignment s)
    (Sat.Literal.pos 2550) (Sat.Literal.pos 2549) (Sat.Literal.pos 205) (Sat.Literal.pos 206) (positive_of_descriptor s 2550 (.lex permutation0 205) (by rfl)) (lex_0_205_prefix s) (positive_select s 205) (lex_0_205_image s)

theorem lex_0_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2549), (Sat.Literal.pos 205), (Sat.Literal.neg 206)] := by
  exact comparison_gate s permutation0 205 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2549) (Sat.Literal.pos 205) (Sat.Literal.pos 206) (lex_0_205_prefix s) (positive_select s 205) (lex_0_205_image s)

theorem lex_0_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2550), (Sat.Literal.pos 2549)] :=
  (lex_0_205_gate s).prop _ (List.Mem.head _)

theorem lex_0_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2550), (Sat.Literal.neg 205), (Sat.Literal.pos 206)] :=
  (lex_0_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2550), (Sat.Literal.pos 205), (Sat.Literal.neg 206)] :=
  (lex_0_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2549), (Sat.Literal.neg 205), (Sat.Literal.neg 206), (Sat.Literal.pos 2550)] :=
  (lex_0_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2549), (Sat.Literal.pos 205), (Sat.Literal.pos 206), (Sat.Literal.pos 2550)] :=
  (lex_0_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2550) = lexBefore s permutation0 202 := by
  exact (positive_lex_of_descriptor s 2550 permutation0 205 (by rfl)).trans ((lex_skipped s permutation0 202 205 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 203 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation0 202) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation0 202 by rw [image0_eq]; rfl))

theorem lex_0_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2551) (Sat.Literal.pos 2550) (Sat.Literal.pos 202) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation0 202 (assignment s)
    (Sat.Literal.pos 2551) (Sat.Literal.pos 2550) (Sat.Literal.pos 202) (Sat.Literal.pos 201) (positive_of_descriptor s 2551 (.lex permutation0 202) (by rfl)) (lex_0_202_prefix s) (positive_select s 202) (lex_0_202_image s)

theorem lex_0_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2550), (Sat.Literal.pos 202), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation0 202 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2550) (Sat.Literal.pos 202) (Sat.Literal.pos 201) (lex_0_202_prefix s) (positive_select s 202) (lex_0_202_image s)

theorem lex_0_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2551), (Sat.Literal.pos 2550)] :=
  (lex_0_202_gate s).prop _ (List.Mem.head _)

theorem lex_0_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2551), (Sat.Literal.neg 202), (Sat.Literal.pos 201)] :=
  (lex_0_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2551), (Sat.Literal.pos 202), (Sat.Literal.neg 201)] :=
  (lex_0_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2550), (Sat.Literal.neg 202), (Sat.Literal.neg 201), (Sat.Literal.pos 2551)] :=
  (lex_0_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2550), (Sat.Literal.pos 202), (Sat.Literal.pos 201), (Sat.Literal.pos 2551)] :=
  (lex_0_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2551) = lexBefore s permutation0 201 := by
  exact (positive_lex_of_descriptor s 2551 permutation0 202 (by rfl)).trans ((lex_skipped s permutation0 201 202 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 202) = s (permuteMask permutation0 201) := by
  exact (positive_select s 202).trans (congrArg s (show (202 : Fin 256) = permuteMask permutation0 201 by rw [image0_eq]; rfl))

theorem lex_0_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2552) (Sat.Literal.pos 2551) (Sat.Literal.pos 201) (Sat.Literal.pos 202)) := by
  exact equality_gate s permutation0 201 (assignment s)
    (Sat.Literal.pos 2552) (Sat.Literal.pos 2551) (Sat.Literal.pos 201) (Sat.Literal.pos 202) (positive_of_descriptor s 2552 (.lex permutation0 201) (by rfl)) (lex_0_201_prefix s) (positive_select s 201) (lex_0_201_image s)

theorem lex_0_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2551), (Sat.Literal.pos 201), (Sat.Literal.neg 202)] := by
  exact comparison_gate s permutation0 201 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2551) (Sat.Literal.pos 201) (Sat.Literal.pos 202) (lex_0_201_prefix s) (positive_select s 201) (lex_0_201_image s)

theorem lex_0_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2552), (Sat.Literal.pos 2551)] :=
  (lex_0_201_gate s).prop _ (List.Mem.head _)

theorem lex_0_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2552), (Sat.Literal.neg 201), (Sat.Literal.pos 202)] :=
  (lex_0_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2552), (Sat.Literal.pos 201), (Sat.Literal.neg 202)] :=
  (lex_0_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2551), (Sat.Literal.neg 201), (Sat.Literal.neg 202), (Sat.Literal.pos 2552)] :=
  (lex_0_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2551), (Sat.Literal.pos 201), (Sat.Literal.pos 202), (Sat.Literal.pos 2552)] :=
  (lex_0_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2552) = lexBefore s permutation0 198 := by
  exact (positive_lex_of_descriptor s 2552 permutation0 201 (by rfl)).trans ((lex_skipped s permutation0 198 201 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 199 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation0 198) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation0 198 by rw [image0_eq]; rfl))

theorem lex_0_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2553) (Sat.Literal.pos 2552) (Sat.Literal.pos 198) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation0 198 (assignment s)
    (Sat.Literal.pos 2553) (Sat.Literal.pos 2552) (Sat.Literal.pos 198) (Sat.Literal.pos 197) (positive_of_descriptor s 2553 (.lex permutation0 198) (by rfl)) (lex_0_198_prefix s) (positive_select s 198) (lex_0_198_image s)

theorem lex_0_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2552), (Sat.Literal.pos 198), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation0 198 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2552) (Sat.Literal.pos 198) (Sat.Literal.pos 197) (lex_0_198_prefix s) (positive_select s 198) (lex_0_198_image s)

theorem lex_0_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2553), (Sat.Literal.pos 2552)] :=
  (lex_0_198_gate s).prop _ (List.Mem.head _)

theorem lex_0_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2553), (Sat.Literal.neg 198), (Sat.Literal.pos 197)] :=
  (lex_0_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2553), (Sat.Literal.pos 198), (Sat.Literal.neg 197)] :=
  (lex_0_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2552), (Sat.Literal.neg 198), (Sat.Literal.neg 197), (Sat.Literal.pos 2553)] :=
  (lex_0_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2552), (Sat.Literal.pos 198), (Sat.Literal.pos 197), (Sat.Literal.pos 2553)] :=
  (lex_0_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2553) = lexBefore s permutation0 197 := by
  exact (positive_lex_of_descriptor s 2553 permutation0 198 (by rfl)).trans ((lex_skipped s permutation0 197 198 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 198) = s (permuteMask permutation0 197) := by
  exact (positive_select s 198).trans (congrArg s (show (198 : Fin 256) = permuteMask permutation0 197 by rw [image0_eq]; rfl))

theorem lex_0_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2554) (Sat.Literal.pos 2553) (Sat.Literal.pos 197) (Sat.Literal.pos 198)) := by
  exact equality_gate s permutation0 197 (assignment s)
    (Sat.Literal.pos 2554) (Sat.Literal.pos 2553) (Sat.Literal.pos 197) (Sat.Literal.pos 198) (positive_of_descriptor s 2554 (.lex permutation0 197) (by rfl)) (lex_0_197_prefix s) (positive_select s 197) (lex_0_197_image s)

theorem lex_0_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2553), (Sat.Literal.pos 197), (Sat.Literal.neg 198)] := by
  exact comparison_gate s permutation0 197 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2553) (Sat.Literal.pos 197) (Sat.Literal.pos 198) (lex_0_197_prefix s) (positive_select s 197) (lex_0_197_image s)

theorem lex_0_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2554), (Sat.Literal.pos 2553)] :=
  (lex_0_197_gate s).prop _ (List.Mem.head _)

theorem lex_0_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2554), (Sat.Literal.neg 197), (Sat.Literal.pos 198)] :=
  (lex_0_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2554), (Sat.Literal.pos 197), (Sat.Literal.neg 198)] :=
  (lex_0_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2553), (Sat.Literal.neg 197), (Sat.Literal.neg 198), (Sat.Literal.pos 2554)] :=
  (lex_0_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2553), (Sat.Literal.pos 197), (Sat.Literal.pos 198), (Sat.Literal.pos 2554)] :=
  (lex_0_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2554) = lexBefore s permutation0 194 := by
  exact (positive_lex_of_descriptor s 2554 permutation0 197 (by rfl)).trans ((lex_skipped s permutation0 194 197 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 195 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation0 194) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation0 194 by rw [image0_eq]; rfl))

theorem lex_0_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2555) (Sat.Literal.pos 2554) (Sat.Literal.pos 194) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation0 194 (assignment s)
    (Sat.Literal.pos 2555) (Sat.Literal.pos 2554) (Sat.Literal.pos 194) (Sat.Literal.pos 193) (positive_of_descriptor s 2555 (.lex permutation0 194) (by rfl)) (lex_0_194_prefix s) (positive_select s 194) (lex_0_194_image s)

theorem lex_0_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2554), (Sat.Literal.pos 194), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation0 194 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2554) (Sat.Literal.pos 194) (Sat.Literal.pos 193) (lex_0_194_prefix s) (positive_select s 194) (lex_0_194_image s)

theorem lex_0_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2555), (Sat.Literal.pos 2554)] :=
  (lex_0_194_gate s).prop _ (List.Mem.head _)

theorem lex_0_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2555), (Sat.Literal.neg 194), (Sat.Literal.pos 193)] :=
  (lex_0_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2555), (Sat.Literal.pos 194), (Sat.Literal.neg 193)] :=
  (lex_0_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2554), (Sat.Literal.neg 194), (Sat.Literal.neg 193), (Sat.Literal.pos 2555)] :=
  (lex_0_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2554), (Sat.Literal.pos 194), (Sat.Literal.pos 193), (Sat.Literal.pos 2555)] :=
  (lex_0_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2555) = lexBefore s permutation0 193 := by
  exact (positive_lex_of_descriptor s 2555 permutation0 194 (by rfl)).trans ((lex_skipped s permutation0 193 194 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 194) = s (permuteMask permutation0 193) := by
  exact (positive_select s 194).trans (congrArg s (show (194 : Fin 256) = permuteMask permutation0 193 by rw [image0_eq]; rfl))

theorem lex_0_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2556) (Sat.Literal.pos 2555) (Sat.Literal.pos 193) (Sat.Literal.pos 194)) := by
  exact equality_gate s permutation0 193 (assignment s)
    (Sat.Literal.pos 2556) (Sat.Literal.pos 2555) (Sat.Literal.pos 193) (Sat.Literal.pos 194) (positive_of_descriptor s 2556 (.lex permutation0 193) (by rfl)) (lex_0_193_prefix s) (positive_select s 193) (lex_0_193_image s)

theorem lex_0_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2555), (Sat.Literal.pos 193), (Sat.Literal.neg 194)] := by
  exact comparison_gate s permutation0 193 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2555) (Sat.Literal.pos 193) (Sat.Literal.pos 194) (lex_0_193_prefix s) (positive_select s 193) (lex_0_193_image s)

theorem lex_0_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2556), (Sat.Literal.pos 2555)] :=
  (lex_0_193_gate s).prop _ (List.Mem.head _)

theorem lex_0_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2556), (Sat.Literal.neg 193), (Sat.Literal.pos 194)] :=
  (lex_0_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2556), (Sat.Literal.pos 193), (Sat.Literal.neg 194)] :=
  (lex_0_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2555), (Sat.Literal.neg 193), (Sat.Literal.neg 194), (Sat.Literal.pos 2556)] :=
  (lex_0_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2555), (Sat.Literal.pos 193), (Sat.Literal.pos 194), (Sat.Literal.pos 2556)] :=
  (lex_0_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2556) = lexBefore s permutation0 190 := by
  exact (positive_lex_of_descriptor s 2556 permutation0 193 (by rfl)).trans ((lex_skipped s permutation0 190 193 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 191 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation0 190) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation0 190 by rw [image0_eq]; rfl))

theorem lex_0_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2557) (Sat.Literal.pos 2556) (Sat.Literal.pos 190) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation0 190 (assignment s)
    (Sat.Literal.pos 2557) (Sat.Literal.pos 2556) (Sat.Literal.pos 190) (Sat.Literal.pos 189) (positive_of_descriptor s 2557 (.lex permutation0 190) (by rfl)) (lex_0_190_prefix s) (positive_select s 190) (lex_0_190_image s)

theorem lex_0_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2556), (Sat.Literal.pos 190), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation0 190 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2556) (Sat.Literal.pos 190) (Sat.Literal.pos 189) (lex_0_190_prefix s) (positive_select s 190) (lex_0_190_image s)

theorem lex_0_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2557), (Sat.Literal.pos 2556)] :=
  (lex_0_190_gate s).prop _ (List.Mem.head _)

theorem lex_0_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2557), (Sat.Literal.neg 190), (Sat.Literal.pos 189)] :=
  (lex_0_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2557), (Sat.Literal.pos 190), (Sat.Literal.neg 189)] :=
  (lex_0_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2556), (Sat.Literal.neg 190), (Sat.Literal.neg 189), (Sat.Literal.pos 2557)] :=
  (lex_0_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2556), (Sat.Literal.pos 190), (Sat.Literal.pos 189), (Sat.Literal.pos 2557)] :=
  (lex_0_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2557) = lexBefore s permutation0 189 := by
  exact (positive_lex_of_descriptor s 2557 permutation0 190 (by rfl)).trans ((lex_skipped s permutation0 189 190 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation0 189) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation0 189 by rw [image0_eq]; rfl))

theorem lex_0_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2558) (Sat.Literal.pos 2557) (Sat.Literal.pos 189) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation0 189 (assignment s)
    (Sat.Literal.pos 2558) (Sat.Literal.pos 2557) (Sat.Literal.pos 189) (Sat.Literal.pos 190) (positive_of_descriptor s 2558 (.lex permutation0 189) (by rfl)) (lex_0_189_prefix s) (positive_select s 189) (lex_0_189_image s)

theorem lex_0_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2557), (Sat.Literal.pos 189), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation0 189 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2557) (Sat.Literal.pos 189) (Sat.Literal.pos 190) (lex_0_189_prefix s) (positive_select s 189) (lex_0_189_image s)

theorem lex_0_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2558), (Sat.Literal.pos 2557)] :=
  (lex_0_189_gate s).prop _ (List.Mem.head _)

theorem lex_0_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2558), (Sat.Literal.neg 189), (Sat.Literal.pos 190)] :=
  (lex_0_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2558), (Sat.Literal.pos 189), (Sat.Literal.neg 190)] :=
  (lex_0_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2557), (Sat.Literal.neg 189), (Sat.Literal.neg 190), (Sat.Literal.pos 2558)] :=
  (lex_0_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2557), (Sat.Literal.pos 189), (Sat.Literal.pos 190), (Sat.Literal.pos 2558)] :=
  (lex_0_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2558) = lexBefore s permutation0 186 := by
  exact (positive_lex_of_descriptor s 2558 permutation0 189 (by rfl)).trans ((lex_skipped s permutation0 186 189 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 187 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation0 186) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation0 186 by rw [image0_eq]; rfl))

theorem lex_0_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2559) (Sat.Literal.pos 2558) (Sat.Literal.pos 186) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation0 186 (assignment s)
    (Sat.Literal.pos 2559) (Sat.Literal.pos 2558) (Sat.Literal.pos 186) (Sat.Literal.pos 185) (positive_of_descriptor s 2559 (.lex permutation0 186) (by rfl)) (lex_0_186_prefix s) (positive_select s 186) (lex_0_186_image s)

theorem lex_0_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2558), (Sat.Literal.pos 186), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation0 186 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2558) (Sat.Literal.pos 186) (Sat.Literal.pos 185) (lex_0_186_prefix s) (positive_select s 186) (lex_0_186_image s)

theorem lex_0_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2559), (Sat.Literal.pos 2558)] :=
  (lex_0_186_gate s).prop _ (List.Mem.head _)

theorem lex_0_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2559), (Sat.Literal.neg 186), (Sat.Literal.pos 185)] :=
  (lex_0_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2559), (Sat.Literal.pos 186), (Sat.Literal.neg 185)] :=
  (lex_0_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2558), (Sat.Literal.neg 186), (Sat.Literal.neg 185), (Sat.Literal.pos 2559)] :=
  (lex_0_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2558), (Sat.Literal.pos 186), (Sat.Literal.pos 185), (Sat.Literal.pos 2559)] :=
  (lex_0_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2559) = lexBefore s permutation0 185 := by
  exact (positive_lex_of_descriptor s 2559 permutation0 186 (by rfl)).trans ((lex_skipped s permutation0 185 186 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation0 185) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation0 185 by rw [image0_eq]; rfl))

theorem lex_0_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2560) (Sat.Literal.pos 2559) (Sat.Literal.pos 185) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation0 185 (assignment s)
    (Sat.Literal.pos 2560) (Sat.Literal.pos 2559) (Sat.Literal.pos 185) (Sat.Literal.pos 186) (positive_of_descriptor s 2560 (.lex permutation0 185) (by rfl)) (lex_0_185_prefix s) (positive_select s 185) (lex_0_185_image s)

theorem lex_0_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2559), (Sat.Literal.pos 185), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation0 185 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2559) (Sat.Literal.pos 185) (Sat.Literal.pos 186) (lex_0_185_prefix s) (positive_select s 185) (lex_0_185_image s)

theorem lex_0_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2560), (Sat.Literal.pos 2559)] :=
  (lex_0_185_gate s).prop _ (List.Mem.head _)

theorem lex_0_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2560), (Sat.Literal.neg 185), (Sat.Literal.pos 186)] :=
  (lex_0_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2560), (Sat.Literal.pos 185), (Sat.Literal.neg 186)] :=
  (lex_0_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2559), (Sat.Literal.neg 185), (Sat.Literal.neg 186), (Sat.Literal.pos 2560)] :=
  (lex_0_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2559), (Sat.Literal.pos 185), (Sat.Literal.pos 186), (Sat.Literal.pos 2560)] :=
  (lex_0_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2560) = lexBefore s permutation0 182 := by
  exact (positive_lex_of_descriptor s 2560 permutation0 185 (by rfl)).trans ((lex_skipped s permutation0 182 185 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 183 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation0 182) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation0 182 by rw [image0_eq]; rfl))

theorem lex_0_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2561) (Sat.Literal.pos 2560) (Sat.Literal.pos 182) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation0 182 (assignment s)
    (Sat.Literal.pos 2561) (Sat.Literal.pos 2560) (Sat.Literal.pos 182) (Sat.Literal.pos 181) (positive_of_descriptor s 2561 (.lex permutation0 182) (by rfl)) (lex_0_182_prefix s) (positive_select s 182) (lex_0_182_image s)

theorem lex_0_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2560), (Sat.Literal.pos 182), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation0 182 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2560) (Sat.Literal.pos 182) (Sat.Literal.pos 181) (lex_0_182_prefix s) (positive_select s 182) (lex_0_182_image s)

theorem lex_0_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2561), (Sat.Literal.pos 2560)] :=
  (lex_0_182_gate s).prop _ (List.Mem.head _)

theorem lex_0_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2561), (Sat.Literal.neg 182), (Sat.Literal.pos 181)] :=
  (lex_0_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2561), (Sat.Literal.pos 182), (Sat.Literal.neg 181)] :=
  (lex_0_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2560), (Sat.Literal.neg 182), (Sat.Literal.neg 181), (Sat.Literal.pos 2561)] :=
  (lex_0_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2560), (Sat.Literal.pos 182), (Sat.Literal.pos 181), (Sat.Literal.pos 2561)] :=
  (lex_0_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2561) = lexBefore s permutation0 181 := by
  exact (positive_lex_of_descriptor s 2561 permutation0 182 (by rfl)).trans ((lex_skipped s permutation0 181 182 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation0 181) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation0 181 by rw [image0_eq]; rfl))

theorem lex_0_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2562) (Sat.Literal.pos 2561) (Sat.Literal.pos 181) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation0 181 (assignment s)
    (Sat.Literal.pos 2562) (Sat.Literal.pos 2561) (Sat.Literal.pos 181) (Sat.Literal.pos 182) (positive_of_descriptor s 2562 (.lex permutation0 181) (by rfl)) (lex_0_181_prefix s) (positive_select s 181) (lex_0_181_image s)

theorem lex_0_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2561), (Sat.Literal.pos 181), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation0 181 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2561) (Sat.Literal.pos 181) (Sat.Literal.pos 182) (lex_0_181_prefix s) (positive_select s 181) (lex_0_181_image s)

theorem lex_0_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2562), (Sat.Literal.pos 2561)] :=
  (lex_0_181_gate s).prop _ (List.Mem.head _)

theorem lex_0_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2562), (Sat.Literal.neg 181), (Sat.Literal.pos 182)] :=
  (lex_0_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2562), (Sat.Literal.pos 181), (Sat.Literal.neg 182)] :=
  (lex_0_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2561), (Sat.Literal.neg 181), (Sat.Literal.neg 182), (Sat.Literal.pos 2562)] :=
  (lex_0_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2561), (Sat.Literal.pos 181), (Sat.Literal.pos 182), (Sat.Literal.pos 2562)] :=
  (lex_0_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2562) = lexBefore s permutation0 178 := by
  exact (positive_lex_of_descriptor s 2562 permutation0 181 (by rfl)).trans ((lex_skipped s permutation0 178 181 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 179 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation0 178) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation0 178 by rw [image0_eq]; rfl))

theorem lex_0_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2563) (Sat.Literal.pos 2562) (Sat.Literal.pos 178) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation0 178 (assignment s)
    (Sat.Literal.pos 2563) (Sat.Literal.pos 2562) (Sat.Literal.pos 178) (Sat.Literal.pos 177) (positive_of_descriptor s 2563 (.lex permutation0 178) (by rfl)) (lex_0_178_prefix s) (positive_select s 178) (lex_0_178_image s)

theorem lex_0_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2562), (Sat.Literal.pos 178), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation0 178 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2562) (Sat.Literal.pos 178) (Sat.Literal.pos 177) (lex_0_178_prefix s) (positive_select s 178) (lex_0_178_image s)

theorem lex_0_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2563), (Sat.Literal.pos 2562)] :=
  (lex_0_178_gate s).prop _ (List.Mem.head _)

theorem lex_0_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2563), (Sat.Literal.neg 178), (Sat.Literal.pos 177)] :=
  (lex_0_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2563), (Sat.Literal.pos 178), (Sat.Literal.neg 177)] :=
  (lex_0_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2562), (Sat.Literal.neg 178), (Sat.Literal.neg 177), (Sat.Literal.pos 2563)] :=
  (lex_0_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2562), (Sat.Literal.pos 178), (Sat.Literal.pos 177), (Sat.Literal.pos 2563)] :=
  (lex_0_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2563) = lexBefore s permutation0 177 := by
  exact (positive_lex_of_descriptor s 2563 permutation0 178 (by rfl)).trans ((lex_skipped s permutation0 177 178 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation0 177) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation0 177 by rw [image0_eq]; rfl))

theorem lex_0_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2564) (Sat.Literal.pos 2563) (Sat.Literal.pos 177) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation0 177 (assignment s)
    (Sat.Literal.pos 2564) (Sat.Literal.pos 2563) (Sat.Literal.pos 177) (Sat.Literal.pos 178) (positive_of_descriptor s 2564 (.lex permutation0 177) (by rfl)) (lex_0_177_prefix s) (positive_select s 177) (lex_0_177_image s)

theorem lex_0_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2563), (Sat.Literal.pos 177), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation0 177 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2563) (Sat.Literal.pos 177) (Sat.Literal.pos 178) (lex_0_177_prefix s) (positive_select s 177) (lex_0_177_image s)

theorem lex_0_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2564), (Sat.Literal.pos 2563)] :=
  (lex_0_177_gate s).prop _ (List.Mem.head _)

theorem lex_0_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2564), (Sat.Literal.neg 177), (Sat.Literal.pos 178)] :=
  (lex_0_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2564), (Sat.Literal.pos 177), (Sat.Literal.neg 178)] :=
  (lex_0_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2563), (Sat.Literal.neg 177), (Sat.Literal.neg 178), (Sat.Literal.pos 2564)] :=
  (lex_0_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2563), (Sat.Literal.pos 177), (Sat.Literal.pos 178), (Sat.Literal.pos 2564)] :=
  (lex_0_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2564) = lexBefore s permutation0 174 := by
  exact (positive_lex_of_descriptor s 2564 permutation0 177 (by rfl)).trans ((lex_skipped s permutation0 174 177 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 175 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation0 174) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation0 174 by rw [image0_eq]; rfl))

theorem lex_0_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2565) (Sat.Literal.pos 2564) (Sat.Literal.pos 174) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation0 174 (assignment s)
    (Sat.Literal.pos 2565) (Sat.Literal.pos 2564) (Sat.Literal.pos 174) (Sat.Literal.pos 173) (positive_of_descriptor s 2565 (.lex permutation0 174) (by rfl)) (lex_0_174_prefix s) (positive_select s 174) (lex_0_174_image s)

theorem lex_0_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2564), (Sat.Literal.pos 174), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation0 174 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2564) (Sat.Literal.pos 174) (Sat.Literal.pos 173) (lex_0_174_prefix s) (positive_select s 174) (lex_0_174_image s)

theorem lex_0_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2565), (Sat.Literal.pos 2564)] :=
  (lex_0_174_gate s).prop _ (List.Mem.head _)

theorem lex_0_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2565), (Sat.Literal.neg 174), (Sat.Literal.pos 173)] :=
  (lex_0_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2565), (Sat.Literal.pos 174), (Sat.Literal.neg 173)] :=
  (lex_0_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2564), (Sat.Literal.neg 174), (Sat.Literal.neg 173), (Sat.Literal.pos 2565)] :=
  (lex_0_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2564), (Sat.Literal.pos 174), (Sat.Literal.pos 173), (Sat.Literal.pos 2565)] :=
  (lex_0_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2565) = lexBefore s permutation0 173 := by
  exact (positive_lex_of_descriptor s 2565 permutation0 174 (by rfl)).trans ((lex_skipped s permutation0 173 174 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation0 173) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation0 173 by rw [image0_eq]; rfl))

theorem lex_0_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2566) (Sat.Literal.pos 2565) (Sat.Literal.pos 173) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation0 173 (assignment s)
    (Sat.Literal.pos 2566) (Sat.Literal.pos 2565) (Sat.Literal.pos 173) (Sat.Literal.pos 174) (positive_of_descriptor s 2566 (.lex permutation0 173) (by rfl)) (lex_0_173_prefix s) (positive_select s 173) (lex_0_173_image s)

theorem lex_0_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2565), (Sat.Literal.pos 173), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation0 173 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2565) (Sat.Literal.pos 173) (Sat.Literal.pos 174) (lex_0_173_prefix s) (positive_select s 173) (lex_0_173_image s)

theorem lex_0_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2566), (Sat.Literal.pos 2565)] :=
  (lex_0_173_gate s).prop _ (List.Mem.head _)

theorem lex_0_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2566), (Sat.Literal.neg 173), (Sat.Literal.pos 174)] :=
  (lex_0_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2566), (Sat.Literal.pos 173), (Sat.Literal.neg 174)] :=
  (lex_0_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2565), (Sat.Literal.neg 173), (Sat.Literal.neg 174), (Sat.Literal.pos 2566)] :=
  (lex_0_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2565), (Sat.Literal.pos 173), (Sat.Literal.pos 174), (Sat.Literal.pos 2566)] :=
  (lex_0_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2566) = lexBefore s permutation0 170 := by
  exact (positive_lex_of_descriptor s 2566 permutation0 173 (by rfl)).trans ((lex_skipped s permutation0 170 173 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 171 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation0 170) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation0 170 by rw [image0_eq]; rfl))

theorem lex_0_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2567) (Sat.Literal.pos 2566) (Sat.Literal.pos 170) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation0 170 (assignment s)
    (Sat.Literal.pos 2567) (Sat.Literal.pos 2566) (Sat.Literal.pos 170) (Sat.Literal.pos 169) (positive_of_descriptor s 2567 (.lex permutation0 170) (by rfl)) (lex_0_170_prefix s) (positive_select s 170) (lex_0_170_image s)

theorem lex_0_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2566), (Sat.Literal.pos 170), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation0 170 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2566) (Sat.Literal.pos 170) (Sat.Literal.pos 169) (lex_0_170_prefix s) (positive_select s 170) (lex_0_170_image s)

theorem lex_0_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2567), (Sat.Literal.pos 2566)] :=
  (lex_0_170_gate s).prop _ (List.Mem.head _)

theorem lex_0_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2567), (Sat.Literal.neg 170), (Sat.Literal.pos 169)] :=
  (lex_0_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2567), (Sat.Literal.pos 170), (Sat.Literal.neg 169)] :=
  (lex_0_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2566), (Sat.Literal.neg 170), (Sat.Literal.neg 169), (Sat.Literal.pos 2567)] :=
  (lex_0_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2566), (Sat.Literal.pos 170), (Sat.Literal.pos 169), (Sat.Literal.pos 2567)] :=
  (lex_0_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2567) = lexBefore s permutation0 169 := by
  exact (positive_lex_of_descriptor s 2567 permutation0 170 (by rfl)).trans ((lex_skipped s permutation0 169 170 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation0 169) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation0 169 by rw [image0_eq]; rfl))

theorem lex_0_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2568) (Sat.Literal.pos 2567) (Sat.Literal.pos 169) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation0 169 (assignment s)
    (Sat.Literal.pos 2568) (Sat.Literal.pos 2567) (Sat.Literal.pos 169) (Sat.Literal.pos 170) (positive_of_descriptor s 2568 (.lex permutation0 169) (by rfl)) (lex_0_169_prefix s) (positive_select s 169) (lex_0_169_image s)

theorem lex_0_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2567), (Sat.Literal.pos 169), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation0 169 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2567) (Sat.Literal.pos 169) (Sat.Literal.pos 170) (lex_0_169_prefix s) (positive_select s 169) (lex_0_169_image s)

theorem lex_0_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2568), (Sat.Literal.pos 2567)] :=
  (lex_0_169_gate s).prop _ (List.Mem.head _)

theorem lex_0_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2568), (Sat.Literal.neg 169), (Sat.Literal.pos 170)] :=
  (lex_0_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2568), (Sat.Literal.pos 169), (Sat.Literal.neg 170)] :=
  (lex_0_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2567), (Sat.Literal.neg 169), (Sat.Literal.neg 170), (Sat.Literal.pos 2568)] :=
  (lex_0_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2567), (Sat.Literal.pos 169), (Sat.Literal.pos 170), (Sat.Literal.pos 2568)] :=
  (lex_0_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2568) = lexBefore s permutation0 166 := by
  exact (positive_lex_of_descriptor s 2568 permutation0 169 (by rfl)).trans ((lex_skipped s permutation0 166 169 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 167 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation0 166) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation0 166 by rw [image0_eq]; rfl))

theorem lex_0_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2569) (Sat.Literal.pos 2568) (Sat.Literal.pos 166) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation0 166 (assignment s)
    (Sat.Literal.pos 2569) (Sat.Literal.pos 2568) (Sat.Literal.pos 166) (Sat.Literal.pos 165) (positive_of_descriptor s 2569 (.lex permutation0 166) (by rfl)) (lex_0_166_prefix s) (positive_select s 166) (lex_0_166_image s)

theorem lex_0_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2568), (Sat.Literal.pos 166), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation0 166 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2568) (Sat.Literal.pos 166) (Sat.Literal.pos 165) (lex_0_166_prefix s) (positive_select s 166) (lex_0_166_image s)

theorem lex_0_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2569), (Sat.Literal.pos 2568)] :=
  (lex_0_166_gate s).prop _ (List.Mem.head _)

theorem lex_0_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2569), (Sat.Literal.neg 166), (Sat.Literal.pos 165)] :=
  (lex_0_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2569), (Sat.Literal.pos 166), (Sat.Literal.neg 165)] :=
  (lex_0_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2568), (Sat.Literal.neg 166), (Sat.Literal.neg 165), (Sat.Literal.pos 2569)] :=
  (lex_0_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2568), (Sat.Literal.pos 166), (Sat.Literal.pos 165), (Sat.Literal.pos 2569)] :=
  (lex_0_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2569) = lexBefore s permutation0 165 := by
  exact (positive_lex_of_descriptor s 2569 permutation0 166 (by rfl)).trans ((lex_skipped s permutation0 165 166 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation0 165) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation0 165 by rw [image0_eq]; rfl))

theorem lex_0_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2570) (Sat.Literal.pos 2569) (Sat.Literal.pos 165) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation0 165 (assignment s)
    (Sat.Literal.pos 2570) (Sat.Literal.pos 2569) (Sat.Literal.pos 165) (Sat.Literal.pos 166) (positive_of_descriptor s 2570 (.lex permutation0 165) (by rfl)) (lex_0_165_prefix s) (positive_select s 165) (lex_0_165_image s)

theorem lex_0_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2569), (Sat.Literal.pos 165), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation0 165 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2569) (Sat.Literal.pos 165) (Sat.Literal.pos 166) (lex_0_165_prefix s) (positive_select s 165) (lex_0_165_image s)

theorem lex_0_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2570), (Sat.Literal.pos 2569)] :=
  (lex_0_165_gate s).prop _ (List.Mem.head _)

theorem lex_0_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2570), (Sat.Literal.neg 165), (Sat.Literal.pos 166)] :=
  (lex_0_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2570), (Sat.Literal.pos 165), (Sat.Literal.neg 166)] :=
  (lex_0_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2569), (Sat.Literal.neg 165), (Sat.Literal.neg 166), (Sat.Literal.pos 2570)] :=
  (lex_0_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2569), (Sat.Literal.pos 165), (Sat.Literal.pos 166), (Sat.Literal.pos 2570)] :=
  (lex_0_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2570) = lexBefore s permutation0 162 := by
  exact (positive_lex_of_descriptor s 2570 permutation0 165 (by rfl)).trans ((lex_skipped s permutation0 162 165 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 163 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation0 162) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation0 162 by rw [image0_eq]; rfl))

theorem lex_0_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2571) (Sat.Literal.pos 2570) (Sat.Literal.pos 162) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation0 162 (assignment s)
    (Sat.Literal.pos 2571) (Sat.Literal.pos 2570) (Sat.Literal.pos 162) (Sat.Literal.pos 161) (positive_of_descriptor s 2571 (.lex permutation0 162) (by rfl)) (lex_0_162_prefix s) (positive_select s 162) (lex_0_162_image s)

theorem lex_0_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2570), (Sat.Literal.pos 162), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation0 162 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2570) (Sat.Literal.pos 162) (Sat.Literal.pos 161) (lex_0_162_prefix s) (positive_select s 162) (lex_0_162_image s)

theorem lex_0_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2571), (Sat.Literal.pos 2570)] :=
  (lex_0_162_gate s).prop _ (List.Mem.head _)

theorem lex_0_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2571), (Sat.Literal.neg 162), (Sat.Literal.pos 161)] :=
  (lex_0_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2571), (Sat.Literal.pos 162), (Sat.Literal.neg 161)] :=
  (lex_0_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2570), (Sat.Literal.neg 162), (Sat.Literal.neg 161), (Sat.Literal.pos 2571)] :=
  (lex_0_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2570), (Sat.Literal.pos 162), (Sat.Literal.pos 161), (Sat.Literal.pos 2571)] :=
  (lex_0_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2571) = lexBefore s permutation0 161 := by
  exact (positive_lex_of_descriptor s 2571 permutation0 162 (by rfl)).trans ((lex_skipped s permutation0 161 162 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation0 161) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation0 161 by rw [image0_eq]; rfl))

theorem lex_0_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2572) (Sat.Literal.pos 2571) (Sat.Literal.pos 161) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation0 161 (assignment s)
    (Sat.Literal.pos 2572) (Sat.Literal.pos 2571) (Sat.Literal.pos 161) (Sat.Literal.pos 162) (positive_of_descriptor s 2572 (.lex permutation0 161) (by rfl)) (lex_0_161_prefix s) (positive_select s 161) (lex_0_161_image s)

theorem lex_0_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2571), (Sat.Literal.pos 161), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation0 161 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2571) (Sat.Literal.pos 161) (Sat.Literal.pos 162) (lex_0_161_prefix s) (positive_select s 161) (lex_0_161_image s)

theorem lex_0_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2572), (Sat.Literal.pos 2571)] :=
  (lex_0_161_gate s).prop _ (List.Mem.head _)

theorem lex_0_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2572), (Sat.Literal.neg 161), (Sat.Literal.pos 162)] :=
  (lex_0_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2572), (Sat.Literal.pos 161), (Sat.Literal.neg 162)] :=
  (lex_0_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2571), (Sat.Literal.neg 161), (Sat.Literal.neg 162), (Sat.Literal.pos 2572)] :=
  (lex_0_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2571), (Sat.Literal.pos 161), (Sat.Literal.pos 162), (Sat.Literal.pos 2572)] :=
  (lex_0_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2572) = lexBefore s permutation0 158 := by
  exact (positive_lex_of_descriptor s 2572 permutation0 161 (by rfl)).trans ((lex_skipped s permutation0 158 161 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 159 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation0 158) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation0 158 by rw [image0_eq]; rfl))

theorem lex_0_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2573) (Sat.Literal.pos 2572) (Sat.Literal.pos 158) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation0 158 (assignment s)
    (Sat.Literal.pos 2573) (Sat.Literal.pos 2572) (Sat.Literal.pos 158) (Sat.Literal.pos 157) (positive_of_descriptor s 2573 (.lex permutation0 158) (by rfl)) (lex_0_158_prefix s) (positive_select s 158) (lex_0_158_image s)

theorem lex_0_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2572), (Sat.Literal.pos 158), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation0 158 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2572) (Sat.Literal.pos 158) (Sat.Literal.pos 157) (lex_0_158_prefix s) (positive_select s 158) (lex_0_158_image s)

theorem lex_0_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2573), (Sat.Literal.pos 2572)] :=
  (lex_0_158_gate s).prop _ (List.Mem.head _)

theorem lex_0_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2573), (Sat.Literal.neg 158), (Sat.Literal.pos 157)] :=
  (lex_0_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2573), (Sat.Literal.pos 158), (Sat.Literal.neg 157)] :=
  (lex_0_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2572), (Sat.Literal.neg 158), (Sat.Literal.neg 157), (Sat.Literal.pos 2573)] :=
  (lex_0_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2572), (Sat.Literal.pos 158), (Sat.Literal.pos 157), (Sat.Literal.pos 2573)] :=
  (lex_0_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2573) = lexBefore s permutation0 157 := by
  exact (positive_lex_of_descriptor s 2573 permutation0 158 (by rfl)).trans ((lex_skipped s permutation0 157 158 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation0 157) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation0 157 by rw [image0_eq]; rfl))

theorem lex_0_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2574) (Sat.Literal.pos 2573) (Sat.Literal.pos 157) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation0 157 (assignment s)
    (Sat.Literal.pos 2574) (Sat.Literal.pos 2573) (Sat.Literal.pos 157) (Sat.Literal.pos 158) (positive_of_descriptor s 2574 (.lex permutation0 157) (by rfl)) (lex_0_157_prefix s) (positive_select s 157) (lex_0_157_image s)

theorem lex_0_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2573), (Sat.Literal.pos 157), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation0 157 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2573) (Sat.Literal.pos 157) (Sat.Literal.pos 158) (lex_0_157_prefix s) (positive_select s 157) (lex_0_157_image s)

theorem lex_0_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2574), (Sat.Literal.pos 2573)] :=
  (lex_0_157_gate s).prop _ (List.Mem.head _)

theorem lex_0_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2574), (Sat.Literal.neg 157), (Sat.Literal.pos 158)] :=
  (lex_0_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2574), (Sat.Literal.pos 157), (Sat.Literal.neg 158)] :=
  (lex_0_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2573), (Sat.Literal.neg 157), (Sat.Literal.neg 158), (Sat.Literal.pos 2574)] :=
  (lex_0_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2573), (Sat.Literal.pos 157), (Sat.Literal.pos 158), (Sat.Literal.pos 2574)] :=
  (lex_0_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2574) = lexBefore s permutation0 154 := by
  exact (positive_lex_of_descriptor s 2574 permutation0 157 (by rfl)).trans ((lex_skipped s permutation0 154 157 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 155 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation0 154) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation0 154 by rw [image0_eq]; rfl))

theorem lex_0_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2575) (Sat.Literal.pos 2574) (Sat.Literal.pos 154) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation0 154 (assignment s)
    (Sat.Literal.pos 2575) (Sat.Literal.pos 2574) (Sat.Literal.pos 154) (Sat.Literal.pos 153) (positive_of_descriptor s 2575 (.lex permutation0 154) (by rfl)) (lex_0_154_prefix s) (positive_select s 154) (lex_0_154_image s)

theorem lex_0_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2574), (Sat.Literal.pos 154), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation0 154 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2574) (Sat.Literal.pos 154) (Sat.Literal.pos 153) (lex_0_154_prefix s) (positive_select s 154) (lex_0_154_image s)

theorem lex_0_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2575), (Sat.Literal.pos 2574)] :=
  (lex_0_154_gate s).prop _ (List.Mem.head _)

theorem lex_0_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2575), (Sat.Literal.neg 154), (Sat.Literal.pos 153)] :=
  (lex_0_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2575), (Sat.Literal.pos 154), (Sat.Literal.neg 153)] :=
  (lex_0_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2574), (Sat.Literal.neg 154), (Sat.Literal.neg 153), (Sat.Literal.pos 2575)] :=
  (lex_0_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2574), (Sat.Literal.pos 154), (Sat.Literal.pos 153), (Sat.Literal.pos 2575)] :=
  (lex_0_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2575) = lexBefore s permutation0 153 := by
  exact (positive_lex_of_descriptor s 2575 permutation0 154 (by rfl)).trans ((lex_skipped s permutation0 153 154 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation0 153) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation0 153 by rw [image0_eq]; rfl))

theorem lex_0_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2576) (Sat.Literal.pos 2575) (Sat.Literal.pos 153) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation0 153 (assignment s)
    (Sat.Literal.pos 2576) (Sat.Literal.pos 2575) (Sat.Literal.pos 153) (Sat.Literal.pos 154) (positive_of_descriptor s 2576 (.lex permutation0 153) (by rfl)) (lex_0_153_prefix s) (positive_select s 153) (lex_0_153_image s)

theorem lex_0_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2575), (Sat.Literal.pos 153), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation0 153 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2575) (Sat.Literal.pos 153) (Sat.Literal.pos 154) (lex_0_153_prefix s) (positive_select s 153) (lex_0_153_image s)

theorem lex_0_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2576), (Sat.Literal.pos 2575)] :=
  (lex_0_153_gate s).prop _ (List.Mem.head _)

theorem lex_0_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2576), (Sat.Literal.neg 153), (Sat.Literal.pos 154)] :=
  (lex_0_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2576), (Sat.Literal.pos 153), (Sat.Literal.neg 154)] :=
  (lex_0_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2575), (Sat.Literal.neg 153), (Sat.Literal.neg 154), (Sat.Literal.pos 2576)] :=
  (lex_0_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2575), (Sat.Literal.pos 153), (Sat.Literal.pos 154), (Sat.Literal.pos 2576)] :=
  (lex_0_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2576) = lexBefore s permutation0 150 := by
  exact (positive_lex_of_descriptor s 2576 permutation0 153 (by rfl)).trans ((lex_skipped s permutation0 150 153 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 151 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation0 150) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation0 150 by rw [image0_eq]; rfl))

theorem lex_0_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2577) (Sat.Literal.pos 2576) (Sat.Literal.pos 150) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation0 150 (assignment s)
    (Sat.Literal.pos 2577) (Sat.Literal.pos 2576) (Sat.Literal.pos 150) (Sat.Literal.pos 149) (positive_of_descriptor s 2577 (.lex permutation0 150) (by rfl)) (lex_0_150_prefix s) (positive_select s 150) (lex_0_150_image s)

theorem lex_0_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2576), (Sat.Literal.pos 150), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation0 150 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2576) (Sat.Literal.pos 150) (Sat.Literal.pos 149) (lex_0_150_prefix s) (positive_select s 150) (lex_0_150_image s)

theorem lex_0_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2577), (Sat.Literal.pos 2576)] :=
  (lex_0_150_gate s).prop _ (List.Mem.head _)

theorem lex_0_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2577), (Sat.Literal.neg 150), (Sat.Literal.pos 149)] :=
  (lex_0_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2577), (Sat.Literal.pos 150), (Sat.Literal.neg 149)] :=
  (lex_0_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2576), (Sat.Literal.neg 150), (Sat.Literal.neg 149), (Sat.Literal.pos 2577)] :=
  (lex_0_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2576), (Sat.Literal.pos 150), (Sat.Literal.pos 149), (Sat.Literal.pos 2577)] :=
  (lex_0_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2577) = lexBefore s permutation0 149 := by
  exact (positive_lex_of_descriptor s 2577 permutation0 150 (by rfl)).trans ((lex_skipped s permutation0 149 150 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation0 149) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation0 149 by rw [image0_eq]; rfl))

theorem lex_0_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2578) (Sat.Literal.pos 2577) (Sat.Literal.pos 149) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation0 149 (assignment s)
    (Sat.Literal.pos 2578) (Sat.Literal.pos 2577) (Sat.Literal.pos 149) (Sat.Literal.pos 150) (positive_of_descriptor s 2578 (.lex permutation0 149) (by rfl)) (lex_0_149_prefix s) (positive_select s 149) (lex_0_149_image s)

theorem lex_0_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2577), (Sat.Literal.pos 149), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation0 149 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2577) (Sat.Literal.pos 149) (Sat.Literal.pos 150) (lex_0_149_prefix s) (positive_select s 149) (lex_0_149_image s)

theorem lex_0_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2578), (Sat.Literal.pos 2577)] :=
  (lex_0_149_gate s).prop _ (List.Mem.head _)

theorem lex_0_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2578), (Sat.Literal.neg 149), (Sat.Literal.pos 150)] :=
  (lex_0_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2578), (Sat.Literal.pos 149), (Sat.Literal.neg 150)] :=
  (lex_0_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2577), (Sat.Literal.neg 149), (Sat.Literal.neg 150), (Sat.Literal.pos 2578)] :=
  (lex_0_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2577), (Sat.Literal.pos 149), (Sat.Literal.pos 150), (Sat.Literal.pos 2578)] :=
  (lex_0_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2578) = lexBefore s permutation0 146 := by
  exact (positive_lex_of_descriptor s 2578 permutation0 149 (by rfl)).trans ((lex_skipped s permutation0 146 149 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 147 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation0 146) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation0 146 by rw [image0_eq]; rfl))

theorem lex_0_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2579) (Sat.Literal.pos 2578) (Sat.Literal.pos 146) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation0 146 (assignment s)
    (Sat.Literal.pos 2579) (Sat.Literal.pos 2578) (Sat.Literal.pos 146) (Sat.Literal.pos 145) (positive_of_descriptor s 2579 (.lex permutation0 146) (by rfl)) (lex_0_146_prefix s) (positive_select s 146) (lex_0_146_image s)

theorem lex_0_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2578), (Sat.Literal.pos 146), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation0 146 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2578) (Sat.Literal.pos 146) (Sat.Literal.pos 145) (lex_0_146_prefix s) (positive_select s 146) (lex_0_146_image s)

theorem lex_0_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2579), (Sat.Literal.pos 2578)] :=
  (lex_0_146_gate s).prop _ (List.Mem.head _)

theorem lex_0_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2579), (Sat.Literal.neg 146), (Sat.Literal.pos 145)] :=
  (lex_0_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2579), (Sat.Literal.pos 146), (Sat.Literal.neg 145)] :=
  (lex_0_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2578), (Sat.Literal.neg 146), (Sat.Literal.neg 145), (Sat.Literal.pos 2579)] :=
  (lex_0_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2578), (Sat.Literal.pos 146), (Sat.Literal.pos 145), (Sat.Literal.pos 2579)] :=
  (lex_0_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2579) = lexBefore s permutation0 145 := by
  exact (positive_lex_of_descriptor s 2579 permutation0 146 (by rfl)).trans ((lex_skipped s permutation0 145 146 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation0 145) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation0 145 by rw [image0_eq]; rfl))

theorem lex_0_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2580) (Sat.Literal.pos 2579) (Sat.Literal.pos 145) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation0 145 (assignment s)
    (Sat.Literal.pos 2580) (Sat.Literal.pos 2579) (Sat.Literal.pos 145) (Sat.Literal.pos 146) (positive_of_descriptor s 2580 (.lex permutation0 145) (by rfl)) (lex_0_145_prefix s) (positive_select s 145) (lex_0_145_image s)

theorem lex_0_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2579), (Sat.Literal.pos 145), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation0 145 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2579) (Sat.Literal.pos 145) (Sat.Literal.pos 146) (lex_0_145_prefix s) (positive_select s 145) (lex_0_145_image s)

theorem lex_0_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2580), (Sat.Literal.pos 2579)] :=
  (lex_0_145_gate s).prop _ (List.Mem.head _)

theorem lex_0_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2580), (Sat.Literal.neg 145), (Sat.Literal.pos 146)] :=
  (lex_0_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2580), (Sat.Literal.pos 145), (Sat.Literal.neg 146)] :=
  (lex_0_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2579), (Sat.Literal.neg 145), (Sat.Literal.neg 146), (Sat.Literal.pos 2580)] :=
  (lex_0_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2579), (Sat.Literal.pos 145), (Sat.Literal.pos 146), (Sat.Literal.pos 2580)] :=
  (lex_0_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2580) = lexBefore s permutation0 142 := by
  exact (positive_lex_of_descriptor s 2580 permutation0 145 (by rfl)).trans ((lex_skipped s permutation0 142 145 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 143 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation0 142) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation0 142 by rw [image0_eq]; rfl))

theorem lex_0_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2581) (Sat.Literal.pos 2580) (Sat.Literal.pos 142) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation0 142 (assignment s)
    (Sat.Literal.pos 2581) (Sat.Literal.pos 2580) (Sat.Literal.pos 142) (Sat.Literal.pos 141) (positive_of_descriptor s 2581 (.lex permutation0 142) (by rfl)) (lex_0_142_prefix s) (positive_select s 142) (lex_0_142_image s)

theorem lex_0_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2580), (Sat.Literal.pos 142), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation0 142 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2580) (Sat.Literal.pos 142) (Sat.Literal.pos 141) (lex_0_142_prefix s) (positive_select s 142) (lex_0_142_image s)

theorem lex_0_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2581), (Sat.Literal.pos 2580)] :=
  (lex_0_142_gate s).prop _ (List.Mem.head _)

theorem lex_0_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2581), (Sat.Literal.neg 142), (Sat.Literal.pos 141)] :=
  (lex_0_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2581), (Sat.Literal.pos 142), (Sat.Literal.neg 141)] :=
  (lex_0_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2580), (Sat.Literal.neg 142), (Sat.Literal.neg 141), (Sat.Literal.pos 2581)] :=
  (lex_0_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2580), (Sat.Literal.pos 142), (Sat.Literal.pos 141), (Sat.Literal.pos 2581)] :=
  (lex_0_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2581) = lexBefore s permutation0 141 := by
  exact (positive_lex_of_descriptor s 2581 permutation0 142 (by rfl)).trans ((lex_skipped s permutation0 141 142 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation0 141) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation0 141 by rw [image0_eq]; rfl))

theorem lex_0_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2582) (Sat.Literal.pos 2581) (Sat.Literal.pos 141) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation0 141 (assignment s)
    (Sat.Literal.pos 2582) (Sat.Literal.pos 2581) (Sat.Literal.pos 141) (Sat.Literal.pos 142) (positive_of_descriptor s 2582 (.lex permutation0 141) (by rfl)) (lex_0_141_prefix s) (positive_select s 141) (lex_0_141_image s)

theorem lex_0_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2581), (Sat.Literal.pos 141), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation0 141 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2581) (Sat.Literal.pos 141) (Sat.Literal.pos 142) (lex_0_141_prefix s) (positive_select s 141) (lex_0_141_image s)

theorem lex_0_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2582), (Sat.Literal.pos 2581)] :=
  (lex_0_141_gate s).prop _ (List.Mem.head _)

theorem lex_0_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2582), (Sat.Literal.neg 141), (Sat.Literal.pos 142)] :=
  (lex_0_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2582), (Sat.Literal.pos 141), (Sat.Literal.neg 142)] :=
  (lex_0_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2581), (Sat.Literal.neg 141), (Sat.Literal.neg 142), (Sat.Literal.pos 2582)] :=
  (lex_0_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2581), (Sat.Literal.pos 141), (Sat.Literal.pos 142), (Sat.Literal.pos 2582)] :=
  (lex_0_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2582) = lexBefore s permutation0 138 := by
  exact (positive_lex_of_descriptor s 2582 permutation0 141 (by rfl)).trans ((lex_skipped s permutation0 138 141 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 139 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation0 138) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation0 138 by rw [image0_eq]; rfl))

theorem lex_0_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2583) (Sat.Literal.pos 2582) (Sat.Literal.pos 138) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation0 138 (assignment s)
    (Sat.Literal.pos 2583) (Sat.Literal.pos 2582) (Sat.Literal.pos 138) (Sat.Literal.pos 137) (positive_of_descriptor s 2583 (.lex permutation0 138) (by rfl)) (lex_0_138_prefix s) (positive_select s 138) (lex_0_138_image s)

theorem lex_0_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2582), (Sat.Literal.pos 138), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation0 138 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2582) (Sat.Literal.pos 138) (Sat.Literal.pos 137) (lex_0_138_prefix s) (positive_select s 138) (lex_0_138_image s)

theorem lex_0_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2583), (Sat.Literal.pos 2582)] :=
  (lex_0_138_gate s).prop _ (List.Mem.head _)

theorem lex_0_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2583), (Sat.Literal.neg 138), (Sat.Literal.pos 137)] :=
  (lex_0_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2583), (Sat.Literal.pos 138), (Sat.Literal.neg 137)] :=
  (lex_0_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2582), (Sat.Literal.neg 138), (Sat.Literal.neg 137), (Sat.Literal.pos 2583)] :=
  (lex_0_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2582), (Sat.Literal.pos 138), (Sat.Literal.pos 137), (Sat.Literal.pos 2583)] :=
  (lex_0_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2583) = lexBefore s permutation0 137 := by
  exact (positive_lex_of_descriptor s 2583 permutation0 138 (by rfl)).trans ((lex_skipped s permutation0 137 138 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation0 137) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation0 137 by rw [image0_eq]; rfl))

theorem lex_0_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2584) (Sat.Literal.pos 2583) (Sat.Literal.pos 137) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation0 137 (assignment s)
    (Sat.Literal.pos 2584) (Sat.Literal.pos 2583) (Sat.Literal.pos 137) (Sat.Literal.pos 138) (positive_of_descriptor s 2584 (.lex permutation0 137) (by rfl)) (lex_0_137_prefix s) (positive_select s 137) (lex_0_137_image s)

theorem lex_0_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2583), (Sat.Literal.pos 137), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation0 137 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2583) (Sat.Literal.pos 137) (Sat.Literal.pos 138) (lex_0_137_prefix s) (positive_select s 137) (lex_0_137_image s)

theorem lex_0_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2584), (Sat.Literal.pos 2583)] :=
  (lex_0_137_gate s).prop _ (List.Mem.head _)

theorem lex_0_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2584), (Sat.Literal.neg 137), (Sat.Literal.pos 138)] :=
  (lex_0_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2584), (Sat.Literal.pos 137), (Sat.Literal.neg 138)] :=
  (lex_0_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2583), (Sat.Literal.neg 137), (Sat.Literal.neg 138), (Sat.Literal.pos 2584)] :=
  (lex_0_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2583), (Sat.Literal.pos 137), (Sat.Literal.pos 138), (Sat.Literal.pos 2584)] :=
  (lex_0_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2584) = lexBefore s permutation0 134 := by
  exact (positive_lex_of_descriptor s 2584 permutation0 137 (by rfl)).trans ((lex_skipped s permutation0 134 137 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 135 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation0 134) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation0 134 by rw [image0_eq]; rfl))

theorem lex_0_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2585) (Sat.Literal.pos 2584) (Sat.Literal.pos 134) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation0 134 (assignment s)
    (Sat.Literal.pos 2585) (Sat.Literal.pos 2584) (Sat.Literal.pos 134) (Sat.Literal.pos 133) (positive_of_descriptor s 2585 (.lex permutation0 134) (by rfl)) (lex_0_134_prefix s) (positive_select s 134) (lex_0_134_image s)

theorem lex_0_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2584), (Sat.Literal.pos 134), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation0 134 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2584) (Sat.Literal.pos 134) (Sat.Literal.pos 133) (lex_0_134_prefix s) (positive_select s 134) (lex_0_134_image s)

theorem lex_0_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2585), (Sat.Literal.pos 2584)] :=
  (lex_0_134_gate s).prop _ (List.Mem.head _)

theorem lex_0_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2585), (Sat.Literal.neg 134), (Sat.Literal.pos 133)] :=
  (lex_0_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2585), (Sat.Literal.pos 134), (Sat.Literal.neg 133)] :=
  (lex_0_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2584), (Sat.Literal.neg 134), (Sat.Literal.neg 133), (Sat.Literal.pos 2585)] :=
  (lex_0_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2584), (Sat.Literal.pos 134), (Sat.Literal.pos 133), (Sat.Literal.pos 2585)] :=
  (lex_0_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2585) = lexBefore s permutation0 133 := by
  exact (positive_lex_of_descriptor s 2585 permutation0 134 (by rfl)).trans ((lex_skipped s permutation0 133 134 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation0 133) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation0 133 by rw [image0_eq]; rfl))

theorem lex_0_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2586) (Sat.Literal.pos 2585) (Sat.Literal.pos 133) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation0 133 (assignment s)
    (Sat.Literal.pos 2586) (Sat.Literal.pos 2585) (Sat.Literal.pos 133) (Sat.Literal.pos 134) (positive_of_descriptor s 2586 (.lex permutation0 133) (by rfl)) (lex_0_133_prefix s) (positive_select s 133) (lex_0_133_image s)

theorem lex_0_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2585), (Sat.Literal.pos 133), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation0 133 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2585) (Sat.Literal.pos 133) (Sat.Literal.pos 134) (lex_0_133_prefix s) (positive_select s 133) (lex_0_133_image s)

theorem lex_0_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2586), (Sat.Literal.pos 2585)] :=
  (lex_0_133_gate s).prop _ (List.Mem.head _)

theorem lex_0_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2586), (Sat.Literal.neg 133), (Sat.Literal.pos 134)] :=
  (lex_0_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2586), (Sat.Literal.pos 133), (Sat.Literal.neg 134)] :=
  (lex_0_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2585), (Sat.Literal.neg 133), (Sat.Literal.neg 134), (Sat.Literal.pos 2586)] :=
  (lex_0_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2585), (Sat.Literal.pos 133), (Sat.Literal.pos 134), (Sat.Literal.pos 2586)] :=
  (lex_0_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2586) = lexBefore s permutation0 130 := by
  exact (positive_lex_of_descriptor s 2586 permutation0 133 (by rfl)).trans ((lex_skipped s permutation0 130 133 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 131 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation0 130) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation0 130 by rw [image0_eq]; rfl))

theorem lex_0_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2587) (Sat.Literal.pos 2586) (Sat.Literal.pos 130) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation0 130 (assignment s)
    (Sat.Literal.pos 2587) (Sat.Literal.pos 2586) (Sat.Literal.pos 130) (Sat.Literal.pos 129) (positive_of_descriptor s 2587 (.lex permutation0 130) (by rfl)) (lex_0_130_prefix s) (positive_select s 130) (lex_0_130_image s)

theorem lex_0_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2586), (Sat.Literal.pos 130), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation0 130 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2586) (Sat.Literal.pos 130) (Sat.Literal.pos 129) (lex_0_130_prefix s) (positive_select s 130) (lex_0_130_image s)

theorem lex_0_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2587), (Sat.Literal.pos 2586)] :=
  (lex_0_130_gate s).prop _ (List.Mem.head _)

theorem lex_0_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2587), (Sat.Literal.neg 130), (Sat.Literal.pos 129)] :=
  (lex_0_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2587), (Sat.Literal.pos 130), (Sat.Literal.neg 129)] :=
  (lex_0_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2586), (Sat.Literal.neg 130), (Sat.Literal.neg 129), (Sat.Literal.pos 2587)] :=
  (lex_0_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2586), (Sat.Literal.pos 130), (Sat.Literal.pos 129), (Sat.Literal.pos 2587)] :=
  (lex_0_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2587) = lexBefore s permutation0 129 := by
  exact (positive_lex_of_descriptor s 2587 permutation0 130 (by rfl)).trans ((lex_skipped s permutation0 129 130 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation0 129) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation0 129 by rw [image0_eq]; rfl))

theorem lex_0_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2588) (Sat.Literal.pos 2587) (Sat.Literal.pos 129) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation0 129 (assignment s)
    (Sat.Literal.pos 2588) (Sat.Literal.pos 2587) (Sat.Literal.pos 129) (Sat.Literal.pos 130) (positive_of_descriptor s 2588 (.lex permutation0 129) (by rfl)) (lex_0_129_prefix s) (positive_select s 129) (lex_0_129_image s)

theorem lex_0_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2587), (Sat.Literal.pos 129), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation0 129 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2587) (Sat.Literal.pos 129) (Sat.Literal.pos 130) (lex_0_129_prefix s) (positive_select s 129) (lex_0_129_image s)

theorem lex_0_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2588), (Sat.Literal.pos 2587)] :=
  (lex_0_129_gate s).prop _ (List.Mem.head _)

theorem lex_0_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2588), (Sat.Literal.neg 129), (Sat.Literal.pos 130)] :=
  (lex_0_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2588), (Sat.Literal.pos 129), (Sat.Literal.neg 130)] :=
  (lex_0_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2587), (Sat.Literal.neg 129), (Sat.Literal.neg 130), (Sat.Literal.pos 2588)] :=
  (lex_0_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2587), (Sat.Literal.pos 129), (Sat.Literal.pos 130), (Sat.Literal.pos 2588)] :=
  (lex_0_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2588) = lexBefore s permutation0 126 := by
  exact (positive_lex_of_descriptor s 2588 permutation0 129 (by rfl)).trans ((lex_skipped s permutation0 126 129 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 127 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation0 126) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation0 126 by rw [image0_eq]; rfl))

theorem lex_0_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2589) (Sat.Literal.pos 2588) (Sat.Literal.pos 126) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation0 126 (assignment s)
    (Sat.Literal.pos 2589) (Sat.Literal.pos 2588) (Sat.Literal.pos 126) (Sat.Literal.pos 125) (positive_of_descriptor s 2589 (.lex permutation0 126) (by rfl)) (lex_0_126_prefix s) (positive_select s 126) (lex_0_126_image s)

theorem lex_0_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2588), (Sat.Literal.pos 126), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation0 126 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2588) (Sat.Literal.pos 126) (Sat.Literal.pos 125) (lex_0_126_prefix s) (positive_select s 126) (lex_0_126_image s)

theorem lex_0_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2589), (Sat.Literal.pos 2588)] :=
  (lex_0_126_gate s).prop _ (List.Mem.head _)

theorem lex_0_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2589), (Sat.Literal.neg 126), (Sat.Literal.pos 125)] :=
  (lex_0_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2589), (Sat.Literal.pos 126), (Sat.Literal.neg 125)] :=
  (lex_0_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2588), (Sat.Literal.neg 126), (Sat.Literal.neg 125), (Sat.Literal.pos 2589)] :=
  (lex_0_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2588), (Sat.Literal.pos 126), (Sat.Literal.pos 125), (Sat.Literal.pos 2589)] :=
  (lex_0_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2589) = lexBefore s permutation0 125 := by
  exact (positive_lex_of_descriptor s 2589 permutation0 126 (by rfl)).trans ((lex_skipped s permutation0 125 126 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation0 125) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation0 125 by rw [image0_eq]; rfl))

theorem lex_0_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2590) (Sat.Literal.pos 2589) (Sat.Literal.pos 125) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation0 125 (assignment s)
    (Sat.Literal.pos 2590) (Sat.Literal.pos 2589) (Sat.Literal.pos 125) (Sat.Literal.pos 126) (positive_of_descriptor s 2590 (.lex permutation0 125) (by rfl)) (lex_0_125_prefix s) (positive_select s 125) (lex_0_125_image s)

theorem lex_0_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2589), (Sat.Literal.pos 125), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation0 125 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2589) (Sat.Literal.pos 125) (Sat.Literal.pos 126) (lex_0_125_prefix s) (positive_select s 125) (lex_0_125_image s)

theorem lex_0_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2590), (Sat.Literal.pos 2589)] :=
  (lex_0_125_gate s).prop _ (List.Mem.head _)

theorem lex_0_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2590), (Sat.Literal.neg 125), (Sat.Literal.pos 126)] :=
  (lex_0_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2590), (Sat.Literal.pos 125), (Sat.Literal.neg 126)] :=
  (lex_0_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2589), (Sat.Literal.neg 125), (Sat.Literal.neg 126), (Sat.Literal.pos 2590)] :=
  (lex_0_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2589), (Sat.Literal.pos 125), (Sat.Literal.pos 126), (Sat.Literal.pos 2590)] :=
  (lex_0_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2590) = lexBefore s permutation0 122 := by
  exact (positive_lex_of_descriptor s 2590 permutation0 125 (by rfl)).trans ((lex_skipped s permutation0 122 125 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 123 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation0 122) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation0 122 by rw [image0_eq]; rfl))

theorem lex_0_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2591) (Sat.Literal.pos 2590) (Sat.Literal.pos 122) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation0 122 (assignment s)
    (Sat.Literal.pos 2591) (Sat.Literal.pos 2590) (Sat.Literal.pos 122) (Sat.Literal.pos 121) (positive_of_descriptor s 2591 (.lex permutation0 122) (by rfl)) (lex_0_122_prefix s) (positive_select s 122) (lex_0_122_image s)

theorem lex_0_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2590), (Sat.Literal.pos 122), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation0 122 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2590) (Sat.Literal.pos 122) (Sat.Literal.pos 121) (lex_0_122_prefix s) (positive_select s 122) (lex_0_122_image s)

theorem lex_0_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2591), (Sat.Literal.pos 2590)] :=
  (lex_0_122_gate s).prop _ (List.Mem.head _)

theorem lex_0_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2591), (Sat.Literal.neg 122), (Sat.Literal.pos 121)] :=
  (lex_0_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2591), (Sat.Literal.pos 122), (Sat.Literal.neg 121)] :=
  (lex_0_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2590), (Sat.Literal.neg 122), (Sat.Literal.neg 121), (Sat.Literal.pos 2591)] :=
  (lex_0_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2590), (Sat.Literal.pos 122), (Sat.Literal.pos 121), (Sat.Literal.pos 2591)] :=
  (lex_0_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2591) = lexBefore s permutation0 121 := by
  exact (positive_lex_of_descriptor s 2591 permutation0 122 (by rfl)).trans ((lex_skipped s permutation0 121 122 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation0 121) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation0 121 by rw [image0_eq]; rfl))

theorem lex_0_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2592) (Sat.Literal.pos 2591) (Sat.Literal.pos 121) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation0 121 (assignment s)
    (Sat.Literal.pos 2592) (Sat.Literal.pos 2591) (Sat.Literal.pos 121) (Sat.Literal.pos 122) (positive_of_descriptor s 2592 (.lex permutation0 121) (by rfl)) (lex_0_121_prefix s) (positive_select s 121) (lex_0_121_image s)

theorem lex_0_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2591), (Sat.Literal.pos 121), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation0 121 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2591) (Sat.Literal.pos 121) (Sat.Literal.pos 122) (lex_0_121_prefix s) (positive_select s 121) (lex_0_121_image s)

theorem lex_0_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2592), (Sat.Literal.pos 2591)] :=
  (lex_0_121_gate s).prop _ (List.Mem.head _)

theorem lex_0_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2592), (Sat.Literal.neg 121), (Sat.Literal.pos 122)] :=
  (lex_0_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2592), (Sat.Literal.pos 121), (Sat.Literal.neg 122)] :=
  (lex_0_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2591), (Sat.Literal.neg 121), (Sat.Literal.neg 122), (Sat.Literal.pos 2592)] :=
  (lex_0_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2591), (Sat.Literal.pos 121), (Sat.Literal.pos 122), (Sat.Literal.pos 2592)] :=
  (lex_0_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2592) = lexBefore s permutation0 118 := by
  exact (positive_lex_of_descriptor s 2592 permutation0 121 (by rfl)).trans ((lex_skipped s permutation0 118 121 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 119 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation0 118) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation0 118 by rw [image0_eq]; rfl))

theorem lex_0_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2593) (Sat.Literal.pos 2592) (Sat.Literal.pos 118) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation0 118 (assignment s)
    (Sat.Literal.pos 2593) (Sat.Literal.pos 2592) (Sat.Literal.pos 118) (Sat.Literal.pos 117) (positive_of_descriptor s 2593 (.lex permutation0 118) (by rfl)) (lex_0_118_prefix s) (positive_select s 118) (lex_0_118_image s)

theorem lex_0_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2592), (Sat.Literal.pos 118), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation0 118 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2592) (Sat.Literal.pos 118) (Sat.Literal.pos 117) (lex_0_118_prefix s) (positive_select s 118) (lex_0_118_image s)

theorem lex_0_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2593), (Sat.Literal.pos 2592)] :=
  (lex_0_118_gate s).prop _ (List.Mem.head _)

theorem lex_0_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2593), (Sat.Literal.neg 118), (Sat.Literal.pos 117)] :=
  (lex_0_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2593), (Sat.Literal.pos 118), (Sat.Literal.neg 117)] :=
  (lex_0_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2592), (Sat.Literal.neg 118), (Sat.Literal.neg 117), (Sat.Literal.pos 2593)] :=
  (lex_0_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2592), (Sat.Literal.pos 118), (Sat.Literal.pos 117), (Sat.Literal.pos 2593)] :=
  (lex_0_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2593) = lexBefore s permutation0 117 := by
  exact (positive_lex_of_descriptor s 2593 permutation0 118 (by rfl)).trans ((lex_skipped s permutation0 117 118 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation0 117) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation0 117 by rw [image0_eq]; rfl))

theorem lex_0_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2594) (Sat.Literal.pos 2593) (Sat.Literal.pos 117) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation0 117 (assignment s)
    (Sat.Literal.pos 2594) (Sat.Literal.pos 2593) (Sat.Literal.pos 117) (Sat.Literal.pos 118) (positive_of_descriptor s 2594 (.lex permutation0 117) (by rfl)) (lex_0_117_prefix s) (positive_select s 117) (lex_0_117_image s)

theorem lex_0_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2593), (Sat.Literal.pos 117), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation0 117 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2593) (Sat.Literal.pos 117) (Sat.Literal.pos 118) (lex_0_117_prefix s) (positive_select s 117) (lex_0_117_image s)

theorem lex_0_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2594), (Sat.Literal.pos 2593)] :=
  (lex_0_117_gate s).prop _ (List.Mem.head _)

theorem lex_0_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2594), (Sat.Literal.neg 117), (Sat.Literal.pos 118)] :=
  (lex_0_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2594), (Sat.Literal.pos 117), (Sat.Literal.neg 118)] :=
  (lex_0_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2593), (Sat.Literal.neg 117), (Sat.Literal.neg 118), (Sat.Literal.pos 2594)] :=
  (lex_0_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2593), (Sat.Literal.pos 117), (Sat.Literal.pos 118), (Sat.Literal.pos 2594)] :=
  (lex_0_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2594) = lexBefore s permutation0 114 := by
  exact (positive_lex_of_descriptor s 2594 permutation0 117 (by rfl)).trans ((lex_skipped s permutation0 114 117 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 115 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation0 114) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation0 114 by rw [image0_eq]; rfl))

theorem lex_0_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2595) (Sat.Literal.pos 2594) (Sat.Literal.pos 114) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation0 114 (assignment s)
    (Sat.Literal.pos 2595) (Sat.Literal.pos 2594) (Sat.Literal.pos 114) (Sat.Literal.pos 113) (positive_of_descriptor s 2595 (.lex permutation0 114) (by rfl)) (lex_0_114_prefix s) (positive_select s 114) (lex_0_114_image s)

theorem lex_0_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2594), (Sat.Literal.pos 114), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation0 114 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2594) (Sat.Literal.pos 114) (Sat.Literal.pos 113) (lex_0_114_prefix s) (positive_select s 114) (lex_0_114_image s)

theorem lex_0_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2595), (Sat.Literal.pos 2594)] :=
  (lex_0_114_gate s).prop _ (List.Mem.head _)

theorem lex_0_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2595), (Sat.Literal.neg 114), (Sat.Literal.pos 113)] :=
  (lex_0_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2595), (Sat.Literal.pos 114), (Sat.Literal.neg 113)] :=
  (lex_0_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2594), (Sat.Literal.neg 114), (Sat.Literal.neg 113), (Sat.Literal.pos 2595)] :=
  (lex_0_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2594), (Sat.Literal.pos 114), (Sat.Literal.pos 113), (Sat.Literal.pos 2595)] :=
  (lex_0_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2595) = lexBefore s permutation0 113 := by
  exact (positive_lex_of_descriptor s 2595 permutation0 114 (by rfl)).trans ((lex_skipped s permutation0 113 114 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 114) = s (permuteMask permutation0 113) := by
  exact (positive_select s 114).trans (congrArg s (show (114 : Fin 256) = permuteMask permutation0 113 by rw [image0_eq]; rfl))

theorem lex_0_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2596) (Sat.Literal.pos 2595) (Sat.Literal.pos 113) (Sat.Literal.pos 114)) := by
  exact equality_gate s permutation0 113 (assignment s)
    (Sat.Literal.pos 2596) (Sat.Literal.pos 2595) (Sat.Literal.pos 113) (Sat.Literal.pos 114) (positive_of_descriptor s 2596 (.lex permutation0 113) (by rfl)) (lex_0_113_prefix s) (positive_select s 113) (lex_0_113_image s)

theorem lex_0_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2595), (Sat.Literal.pos 113), (Sat.Literal.neg 114)] := by
  exact comparison_gate s permutation0 113 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2595) (Sat.Literal.pos 113) (Sat.Literal.pos 114) (lex_0_113_prefix s) (positive_select s 113) (lex_0_113_image s)

theorem lex_0_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2596), (Sat.Literal.pos 2595)] :=
  (lex_0_113_gate s).prop _ (List.Mem.head _)

theorem lex_0_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2596), (Sat.Literal.neg 113), (Sat.Literal.pos 114)] :=
  (lex_0_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2596), (Sat.Literal.pos 113), (Sat.Literal.neg 114)] :=
  (lex_0_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2595), (Sat.Literal.neg 113), (Sat.Literal.neg 114), (Sat.Literal.pos 2596)] :=
  (lex_0_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2595), (Sat.Literal.pos 113), (Sat.Literal.pos 114), (Sat.Literal.pos 2596)] :=
  (lex_0_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2596) = lexBefore s permutation0 110 := by
  exact (positive_lex_of_descriptor s 2596 permutation0 113 (by rfl)).trans ((lex_skipped s permutation0 110 113 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 111 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation0 110) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation0 110 by rw [image0_eq]; rfl))

theorem lex_0_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2597) (Sat.Literal.pos 2596) (Sat.Literal.pos 110) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation0 110 (assignment s)
    (Sat.Literal.pos 2597) (Sat.Literal.pos 2596) (Sat.Literal.pos 110) (Sat.Literal.pos 109) (positive_of_descriptor s 2597 (.lex permutation0 110) (by rfl)) (lex_0_110_prefix s) (positive_select s 110) (lex_0_110_image s)

theorem lex_0_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2596), (Sat.Literal.pos 110), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation0 110 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2596) (Sat.Literal.pos 110) (Sat.Literal.pos 109) (lex_0_110_prefix s) (positive_select s 110) (lex_0_110_image s)

theorem lex_0_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2597), (Sat.Literal.pos 2596)] :=
  (lex_0_110_gate s).prop _ (List.Mem.head _)

theorem lex_0_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2597), (Sat.Literal.neg 110), (Sat.Literal.pos 109)] :=
  (lex_0_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2597), (Sat.Literal.pos 110), (Sat.Literal.neg 109)] :=
  (lex_0_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2596), (Sat.Literal.neg 110), (Sat.Literal.neg 109), (Sat.Literal.pos 2597)] :=
  (lex_0_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2596), (Sat.Literal.pos 110), (Sat.Literal.pos 109), (Sat.Literal.pos 2597)] :=
  (lex_0_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2597) = lexBefore s permutation0 109 := by
  exact (positive_lex_of_descriptor s 2597 permutation0 110 (by rfl)).trans ((lex_skipped s permutation0 109 110 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 110) = s (permuteMask permutation0 109) := by
  exact (positive_select s 110).trans (congrArg s (show (110 : Fin 256) = permuteMask permutation0 109 by rw [image0_eq]; rfl))

theorem lex_0_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2598) (Sat.Literal.pos 2597) (Sat.Literal.pos 109) (Sat.Literal.pos 110)) := by
  exact equality_gate s permutation0 109 (assignment s)
    (Sat.Literal.pos 2598) (Sat.Literal.pos 2597) (Sat.Literal.pos 109) (Sat.Literal.pos 110) (positive_of_descriptor s 2598 (.lex permutation0 109) (by rfl)) (lex_0_109_prefix s) (positive_select s 109) (lex_0_109_image s)

theorem lex_0_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2597), (Sat.Literal.pos 109), (Sat.Literal.neg 110)] := by
  exact comparison_gate s permutation0 109 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2597) (Sat.Literal.pos 109) (Sat.Literal.pos 110) (lex_0_109_prefix s) (positive_select s 109) (lex_0_109_image s)

theorem lex_0_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2598), (Sat.Literal.pos 2597)] :=
  (lex_0_109_gate s).prop _ (List.Mem.head _)

theorem lex_0_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2598), (Sat.Literal.neg 109), (Sat.Literal.pos 110)] :=
  (lex_0_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2598), (Sat.Literal.pos 109), (Sat.Literal.neg 110)] :=
  (lex_0_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2597), (Sat.Literal.neg 109), (Sat.Literal.neg 110), (Sat.Literal.pos 2598)] :=
  (lex_0_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2597), (Sat.Literal.pos 109), (Sat.Literal.pos 110), (Sat.Literal.pos 2598)] :=
  (lex_0_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2598) = lexBefore s permutation0 106 := by
  exact (positive_lex_of_descriptor s 2598 permutation0 109 (by rfl)).trans ((lex_skipped s permutation0 106 109 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 107 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation0 106) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation0 106 by rw [image0_eq]; rfl))

theorem lex_0_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2599) (Sat.Literal.pos 2598) (Sat.Literal.pos 106) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation0 106 (assignment s)
    (Sat.Literal.pos 2599) (Sat.Literal.pos 2598) (Sat.Literal.pos 106) (Sat.Literal.pos 105) (positive_of_descriptor s 2599 (.lex permutation0 106) (by rfl)) (lex_0_106_prefix s) (positive_select s 106) (lex_0_106_image s)

theorem lex_0_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2598), (Sat.Literal.pos 106), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation0 106 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2598) (Sat.Literal.pos 106) (Sat.Literal.pos 105) (lex_0_106_prefix s) (positive_select s 106) (lex_0_106_image s)

theorem lex_0_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2599), (Sat.Literal.pos 2598)] :=
  (lex_0_106_gate s).prop _ (List.Mem.head _)

theorem lex_0_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2599), (Sat.Literal.neg 106), (Sat.Literal.pos 105)] :=
  (lex_0_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2599), (Sat.Literal.pos 106), (Sat.Literal.neg 105)] :=
  (lex_0_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2598), (Sat.Literal.neg 106), (Sat.Literal.neg 105), (Sat.Literal.pos 2599)] :=
  (lex_0_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2598), (Sat.Literal.pos 106), (Sat.Literal.pos 105), (Sat.Literal.pos 2599)] :=
  (lex_0_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2599) = lexBefore s permutation0 105 := by
  exact (positive_lex_of_descriptor s 2599 permutation0 106 (by rfl)).trans ((lex_skipped s permutation0 105 106 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 106) = s (permuteMask permutation0 105) := by
  exact (positive_select s 106).trans (congrArg s (show (106 : Fin 256) = permuteMask permutation0 105 by rw [image0_eq]; rfl))

theorem lex_0_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2600) (Sat.Literal.pos 2599) (Sat.Literal.pos 105) (Sat.Literal.pos 106)) := by
  exact equality_gate s permutation0 105 (assignment s)
    (Sat.Literal.pos 2600) (Sat.Literal.pos 2599) (Sat.Literal.pos 105) (Sat.Literal.pos 106) (positive_of_descriptor s 2600 (.lex permutation0 105) (by rfl)) (lex_0_105_prefix s) (positive_select s 105) (lex_0_105_image s)

theorem lex_0_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2599), (Sat.Literal.pos 105), (Sat.Literal.neg 106)] := by
  exact comparison_gate s permutation0 105 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2599) (Sat.Literal.pos 105) (Sat.Literal.pos 106) (lex_0_105_prefix s) (positive_select s 105) (lex_0_105_image s)

theorem lex_0_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2600), (Sat.Literal.pos 2599)] :=
  (lex_0_105_gate s).prop _ (List.Mem.head _)

theorem lex_0_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2600), (Sat.Literal.neg 105), (Sat.Literal.pos 106)] :=
  (lex_0_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2600), (Sat.Literal.pos 105), (Sat.Literal.neg 106)] :=
  (lex_0_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2599), (Sat.Literal.neg 105), (Sat.Literal.neg 106), (Sat.Literal.pos 2600)] :=
  (lex_0_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2599), (Sat.Literal.pos 105), (Sat.Literal.pos 106), (Sat.Literal.pos 2600)] :=
  (lex_0_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2600) = lexBefore s permutation0 102 := by
  exact (positive_lex_of_descriptor s 2600 permutation0 105 (by rfl)).trans ((lex_skipped s permutation0 102 105 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 103 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation0 102) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation0 102 by rw [image0_eq]; rfl))

theorem lex_0_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2601) (Sat.Literal.pos 2600) (Sat.Literal.pos 102) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation0 102 (assignment s)
    (Sat.Literal.pos 2601) (Sat.Literal.pos 2600) (Sat.Literal.pos 102) (Sat.Literal.pos 101) (positive_of_descriptor s 2601 (.lex permutation0 102) (by rfl)) (lex_0_102_prefix s) (positive_select s 102) (lex_0_102_image s)

theorem lex_0_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2600), (Sat.Literal.pos 102), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation0 102 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2600) (Sat.Literal.pos 102) (Sat.Literal.pos 101) (lex_0_102_prefix s) (positive_select s 102) (lex_0_102_image s)

theorem lex_0_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2601), (Sat.Literal.pos 2600)] :=
  (lex_0_102_gate s).prop _ (List.Mem.head _)

theorem lex_0_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2601), (Sat.Literal.neg 102), (Sat.Literal.pos 101)] :=
  (lex_0_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2601), (Sat.Literal.pos 102), (Sat.Literal.neg 101)] :=
  (lex_0_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2600), (Sat.Literal.neg 102), (Sat.Literal.neg 101), (Sat.Literal.pos 2601)] :=
  (lex_0_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2600), (Sat.Literal.pos 102), (Sat.Literal.pos 101), (Sat.Literal.pos 2601)] :=
  (lex_0_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2601) = lexBefore s permutation0 101 := by
  exact (positive_lex_of_descriptor s 2601 permutation0 102 (by rfl)).trans ((lex_skipped s permutation0 101 102 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 102) = s (permuteMask permutation0 101) := by
  exact (positive_select s 102).trans (congrArg s (show (102 : Fin 256) = permuteMask permutation0 101 by rw [image0_eq]; rfl))

theorem lex_0_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2602) (Sat.Literal.pos 2601) (Sat.Literal.pos 101) (Sat.Literal.pos 102)) := by
  exact equality_gate s permutation0 101 (assignment s)
    (Sat.Literal.pos 2602) (Sat.Literal.pos 2601) (Sat.Literal.pos 101) (Sat.Literal.pos 102) (positive_of_descriptor s 2602 (.lex permutation0 101) (by rfl)) (lex_0_101_prefix s) (positive_select s 101) (lex_0_101_image s)

theorem lex_0_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2601), (Sat.Literal.pos 101), (Sat.Literal.neg 102)] := by
  exact comparison_gate s permutation0 101 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2601) (Sat.Literal.pos 101) (Sat.Literal.pos 102) (lex_0_101_prefix s) (positive_select s 101) (lex_0_101_image s)

theorem lex_0_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2602), (Sat.Literal.pos 2601)] :=
  (lex_0_101_gate s).prop _ (List.Mem.head _)

theorem lex_0_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2602), (Sat.Literal.neg 101), (Sat.Literal.pos 102)] :=
  (lex_0_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2602), (Sat.Literal.pos 101), (Sat.Literal.neg 102)] :=
  (lex_0_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2601), (Sat.Literal.neg 101), (Sat.Literal.neg 102), (Sat.Literal.pos 2602)] :=
  (lex_0_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2601), (Sat.Literal.pos 101), (Sat.Literal.pos 102), (Sat.Literal.pos 2602)] :=
  (lex_0_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2602) = lexBefore s permutation0 98 := by
  exact (positive_lex_of_descriptor s 2602 permutation0 101 (by rfl)).trans ((lex_skipped s permutation0 98 101 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 99 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation0 98) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation0 98 by rw [image0_eq]; rfl))

theorem lex_0_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2603) (Sat.Literal.pos 2602) (Sat.Literal.pos 98) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation0 98 (assignment s)
    (Sat.Literal.pos 2603) (Sat.Literal.pos 2602) (Sat.Literal.pos 98) (Sat.Literal.pos 97) (positive_of_descriptor s 2603 (.lex permutation0 98) (by rfl)) (lex_0_98_prefix s) (positive_select s 98) (lex_0_98_image s)

theorem lex_0_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2602), (Sat.Literal.pos 98), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation0 98 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2602) (Sat.Literal.pos 98) (Sat.Literal.pos 97) (lex_0_98_prefix s) (positive_select s 98) (lex_0_98_image s)

theorem lex_0_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2603), (Sat.Literal.pos 2602)] :=
  (lex_0_98_gate s).prop _ (List.Mem.head _)

theorem lex_0_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2603), (Sat.Literal.neg 98), (Sat.Literal.pos 97)] :=
  (lex_0_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2603), (Sat.Literal.pos 98), (Sat.Literal.neg 97)] :=
  (lex_0_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2602), (Sat.Literal.neg 98), (Sat.Literal.neg 97), (Sat.Literal.pos 2603)] :=
  (lex_0_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2602), (Sat.Literal.pos 98), (Sat.Literal.pos 97), (Sat.Literal.pos 2603)] :=
  (lex_0_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2603) = lexBefore s permutation0 97 := by
  exact (positive_lex_of_descriptor s 2603 permutation0 98 (by rfl)).trans ((lex_skipped s permutation0 97 98 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 98) = s (permuteMask permutation0 97) := by
  exact (positive_select s 98).trans (congrArg s (show (98 : Fin 256) = permuteMask permutation0 97 by rw [image0_eq]; rfl))

theorem lex_0_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2604) (Sat.Literal.pos 2603) (Sat.Literal.pos 97) (Sat.Literal.pos 98)) := by
  exact equality_gate s permutation0 97 (assignment s)
    (Sat.Literal.pos 2604) (Sat.Literal.pos 2603) (Sat.Literal.pos 97) (Sat.Literal.pos 98) (positive_of_descriptor s 2604 (.lex permutation0 97) (by rfl)) (lex_0_97_prefix s) (positive_select s 97) (lex_0_97_image s)

theorem lex_0_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2603), (Sat.Literal.pos 97), (Sat.Literal.neg 98)] := by
  exact comparison_gate s permutation0 97 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2603) (Sat.Literal.pos 97) (Sat.Literal.pos 98) (lex_0_97_prefix s) (positive_select s 97) (lex_0_97_image s)

theorem lex_0_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2604), (Sat.Literal.pos 2603)] :=
  (lex_0_97_gate s).prop _ (List.Mem.head _)

theorem lex_0_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2604), (Sat.Literal.neg 97), (Sat.Literal.pos 98)] :=
  (lex_0_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2604), (Sat.Literal.pos 97), (Sat.Literal.neg 98)] :=
  (lex_0_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2603), (Sat.Literal.neg 97), (Sat.Literal.neg 98), (Sat.Literal.pos 2604)] :=
  (lex_0_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2603), (Sat.Literal.pos 97), (Sat.Literal.pos 98), (Sat.Literal.pos 2604)] :=
  (lex_0_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2604) = lexBefore s permutation0 94 := by
  exact (positive_lex_of_descriptor s 2604 permutation0 97 (by rfl)).trans ((lex_skipped s permutation0 94 97 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 95 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation0 94) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation0 94 by rw [image0_eq]; rfl))

theorem lex_0_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2605) (Sat.Literal.pos 2604) (Sat.Literal.pos 94) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation0 94 (assignment s)
    (Sat.Literal.pos 2605) (Sat.Literal.pos 2604) (Sat.Literal.pos 94) (Sat.Literal.pos 93) (positive_of_descriptor s 2605 (.lex permutation0 94) (by rfl)) (lex_0_94_prefix s) (positive_select s 94) (lex_0_94_image s)

theorem lex_0_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2604), (Sat.Literal.pos 94), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation0 94 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2604) (Sat.Literal.pos 94) (Sat.Literal.pos 93) (lex_0_94_prefix s) (positive_select s 94) (lex_0_94_image s)

theorem lex_0_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2605), (Sat.Literal.pos 2604)] :=
  (lex_0_94_gate s).prop _ (List.Mem.head _)

theorem lex_0_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2605), (Sat.Literal.neg 94), (Sat.Literal.pos 93)] :=
  (lex_0_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2605), (Sat.Literal.pos 94), (Sat.Literal.neg 93)] :=
  (lex_0_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2604), (Sat.Literal.neg 94), (Sat.Literal.neg 93), (Sat.Literal.pos 2605)] :=
  (lex_0_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2604), (Sat.Literal.pos 94), (Sat.Literal.pos 93), (Sat.Literal.pos 2605)] :=
  (lex_0_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2605) = lexBefore s permutation0 93 := by
  exact (positive_lex_of_descriptor s 2605 permutation0 94 (by rfl)).trans ((lex_skipped s permutation0 93 94 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation0 93) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation0 93 by rw [image0_eq]; rfl))

theorem lex_0_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2606) (Sat.Literal.pos 2605) (Sat.Literal.pos 93) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation0 93 (assignment s)
    (Sat.Literal.pos 2606) (Sat.Literal.pos 2605) (Sat.Literal.pos 93) (Sat.Literal.pos 94) (positive_of_descriptor s 2606 (.lex permutation0 93) (by rfl)) (lex_0_93_prefix s) (positive_select s 93) (lex_0_93_image s)

theorem lex_0_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2605), (Sat.Literal.pos 93), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation0 93 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2605) (Sat.Literal.pos 93) (Sat.Literal.pos 94) (lex_0_93_prefix s) (positive_select s 93) (lex_0_93_image s)

theorem lex_0_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2606), (Sat.Literal.pos 2605)] :=
  (lex_0_93_gate s).prop _ (List.Mem.head _)

theorem lex_0_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2606), (Sat.Literal.neg 93), (Sat.Literal.pos 94)] :=
  (lex_0_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2606), (Sat.Literal.pos 93), (Sat.Literal.neg 94)] :=
  (lex_0_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2605), (Sat.Literal.neg 93), (Sat.Literal.neg 94), (Sat.Literal.pos 2606)] :=
  (lex_0_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2605), (Sat.Literal.pos 93), (Sat.Literal.pos 94), (Sat.Literal.pos 2606)] :=
  (lex_0_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2606) = lexBefore s permutation0 90 := by
  exact (positive_lex_of_descriptor s 2606 permutation0 93 (by rfl)).trans ((lex_skipped s permutation0 90 93 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 91 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation0 90) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation0 90 by rw [image0_eq]; rfl))

theorem lex_0_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2607) (Sat.Literal.pos 2606) (Sat.Literal.pos 90) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation0 90 (assignment s)
    (Sat.Literal.pos 2607) (Sat.Literal.pos 2606) (Sat.Literal.pos 90) (Sat.Literal.pos 89) (positive_of_descriptor s 2607 (.lex permutation0 90) (by rfl)) (lex_0_90_prefix s) (positive_select s 90) (lex_0_90_image s)

theorem lex_0_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2606), (Sat.Literal.pos 90), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation0 90 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2606) (Sat.Literal.pos 90) (Sat.Literal.pos 89) (lex_0_90_prefix s) (positive_select s 90) (lex_0_90_image s)

theorem lex_0_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2607), (Sat.Literal.pos 2606)] :=
  (lex_0_90_gate s).prop _ (List.Mem.head _)

theorem lex_0_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2607), (Sat.Literal.neg 90), (Sat.Literal.pos 89)] :=
  (lex_0_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2607), (Sat.Literal.pos 90), (Sat.Literal.neg 89)] :=
  (lex_0_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2606), (Sat.Literal.neg 90), (Sat.Literal.neg 89), (Sat.Literal.pos 2607)] :=
  (lex_0_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2606), (Sat.Literal.pos 90), (Sat.Literal.pos 89), (Sat.Literal.pos 2607)] :=
  (lex_0_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2607) = lexBefore s permutation0 89 := by
  exact (positive_lex_of_descriptor s 2607 permutation0 90 (by rfl)).trans ((lex_skipped s permutation0 89 90 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation0 89) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation0 89 by rw [image0_eq]; rfl))

theorem lex_0_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2608) (Sat.Literal.pos 2607) (Sat.Literal.pos 89) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation0 89 (assignment s)
    (Sat.Literal.pos 2608) (Sat.Literal.pos 2607) (Sat.Literal.pos 89) (Sat.Literal.pos 90) (positive_of_descriptor s 2608 (.lex permutation0 89) (by rfl)) (lex_0_89_prefix s) (positive_select s 89) (lex_0_89_image s)

theorem lex_0_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2607), (Sat.Literal.pos 89), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation0 89 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2607) (Sat.Literal.pos 89) (Sat.Literal.pos 90) (lex_0_89_prefix s) (positive_select s 89) (lex_0_89_image s)

theorem lex_0_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2608), (Sat.Literal.pos 2607)] :=
  (lex_0_89_gate s).prop _ (List.Mem.head _)

theorem lex_0_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2608), (Sat.Literal.neg 89), (Sat.Literal.pos 90)] :=
  (lex_0_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2608), (Sat.Literal.pos 89), (Sat.Literal.neg 90)] :=
  (lex_0_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2607), (Sat.Literal.neg 89), (Sat.Literal.neg 90), (Sat.Literal.pos 2608)] :=
  (lex_0_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2607), (Sat.Literal.pos 89), (Sat.Literal.pos 90), (Sat.Literal.pos 2608)] :=
  (lex_0_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2608) = lexBefore s permutation0 86 := by
  exact (positive_lex_of_descriptor s 2608 permutation0 89 (by rfl)).trans ((lex_skipped s permutation0 86 89 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 87 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation0 86) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation0 86 by rw [image0_eq]; rfl))

theorem lex_0_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2609) (Sat.Literal.pos 2608) (Sat.Literal.pos 86) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation0 86 (assignment s)
    (Sat.Literal.pos 2609) (Sat.Literal.pos 2608) (Sat.Literal.pos 86) (Sat.Literal.pos 85) (positive_of_descriptor s 2609 (.lex permutation0 86) (by rfl)) (lex_0_86_prefix s) (positive_select s 86) (lex_0_86_image s)

theorem lex_0_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2608), (Sat.Literal.pos 86), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation0 86 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2608) (Sat.Literal.pos 86) (Sat.Literal.pos 85) (lex_0_86_prefix s) (positive_select s 86) (lex_0_86_image s)

theorem lex_0_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2609), (Sat.Literal.pos 2608)] :=
  (lex_0_86_gate s).prop _ (List.Mem.head _)

theorem lex_0_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2609), (Sat.Literal.neg 86), (Sat.Literal.pos 85)] :=
  (lex_0_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2609), (Sat.Literal.pos 86), (Sat.Literal.neg 85)] :=
  (lex_0_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2608), (Sat.Literal.neg 86), (Sat.Literal.neg 85), (Sat.Literal.pos 2609)] :=
  (lex_0_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2608), (Sat.Literal.pos 86), (Sat.Literal.pos 85), (Sat.Literal.pos 2609)] :=
  (lex_0_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2609) = lexBefore s permutation0 85 := by
  exact (positive_lex_of_descriptor s 2609 permutation0 86 (by rfl)).trans ((lex_skipped s permutation0 85 86 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation0 85) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation0 85 by rw [image0_eq]; rfl))

theorem lex_0_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2610) (Sat.Literal.pos 2609) (Sat.Literal.pos 85) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation0 85 (assignment s)
    (Sat.Literal.pos 2610) (Sat.Literal.pos 2609) (Sat.Literal.pos 85) (Sat.Literal.pos 86) (positive_of_descriptor s 2610 (.lex permutation0 85) (by rfl)) (lex_0_85_prefix s) (positive_select s 85) (lex_0_85_image s)

theorem lex_0_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2609), (Sat.Literal.pos 85), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation0 85 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2609) (Sat.Literal.pos 85) (Sat.Literal.pos 86) (lex_0_85_prefix s) (positive_select s 85) (lex_0_85_image s)

theorem lex_0_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2610), (Sat.Literal.pos 2609)] :=
  (lex_0_85_gate s).prop _ (List.Mem.head _)

theorem lex_0_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2610), (Sat.Literal.neg 85), (Sat.Literal.pos 86)] :=
  (lex_0_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2610), (Sat.Literal.pos 85), (Sat.Literal.neg 86)] :=
  (lex_0_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2609), (Sat.Literal.neg 85), (Sat.Literal.neg 86), (Sat.Literal.pos 2610)] :=
  (lex_0_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2609), (Sat.Literal.pos 85), (Sat.Literal.pos 86), (Sat.Literal.pos 2610)] :=
  (lex_0_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2610) = lexBefore s permutation0 82 := by
  exact (positive_lex_of_descriptor s 2610 permutation0 85 (by rfl)).trans ((lex_skipped s permutation0 82 85 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 83 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation0 82) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation0 82 by rw [image0_eq]; rfl))

theorem lex_0_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2611) (Sat.Literal.pos 2610) (Sat.Literal.pos 82) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation0 82 (assignment s)
    (Sat.Literal.pos 2611) (Sat.Literal.pos 2610) (Sat.Literal.pos 82) (Sat.Literal.pos 81) (positive_of_descriptor s 2611 (.lex permutation0 82) (by rfl)) (lex_0_82_prefix s) (positive_select s 82) (lex_0_82_image s)

theorem lex_0_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2610), (Sat.Literal.pos 82), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation0 82 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2610) (Sat.Literal.pos 82) (Sat.Literal.pos 81) (lex_0_82_prefix s) (positive_select s 82) (lex_0_82_image s)

theorem lex_0_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2611), (Sat.Literal.pos 2610)] :=
  (lex_0_82_gate s).prop _ (List.Mem.head _)

theorem lex_0_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2611), (Sat.Literal.neg 82), (Sat.Literal.pos 81)] :=
  (lex_0_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2611), (Sat.Literal.pos 82), (Sat.Literal.neg 81)] :=
  (lex_0_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2610), (Sat.Literal.neg 82), (Sat.Literal.neg 81), (Sat.Literal.pos 2611)] :=
  (lex_0_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2610), (Sat.Literal.pos 82), (Sat.Literal.pos 81), (Sat.Literal.pos 2611)] :=
  (lex_0_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2611) = lexBefore s permutation0 81 := by
  exact (positive_lex_of_descriptor s 2611 permutation0 82 (by rfl)).trans ((lex_skipped s permutation0 81 82 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation0 81) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation0 81 by rw [image0_eq]; rfl))

theorem lex_0_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2612) (Sat.Literal.pos 2611) (Sat.Literal.pos 81) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation0 81 (assignment s)
    (Sat.Literal.pos 2612) (Sat.Literal.pos 2611) (Sat.Literal.pos 81) (Sat.Literal.pos 82) (positive_of_descriptor s 2612 (.lex permutation0 81) (by rfl)) (lex_0_81_prefix s) (positive_select s 81) (lex_0_81_image s)

theorem lex_0_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2611), (Sat.Literal.pos 81), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation0 81 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2611) (Sat.Literal.pos 81) (Sat.Literal.pos 82) (lex_0_81_prefix s) (positive_select s 81) (lex_0_81_image s)

theorem lex_0_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2612), (Sat.Literal.pos 2611)] :=
  (lex_0_81_gate s).prop _ (List.Mem.head _)

theorem lex_0_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2612), (Sat.Literal.neg 81), (Sat.Literal.pos 82)] :=
  (lex_0_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2612), (Sat.Literal.pos 81), (Sat.Literal.neg 82)] :=
  (lex_0_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2611), (Sat.Literal.neg 81), (Sat.Literal.neg 82), (Sat.Literal.pos 2612)] :=
  (lex_0_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2611), (Sat.Literal.pos 81), (Sat.Literal.pos 82), (Sat.Literal.pos 2612)] :=
  (lex_0_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2612) = lexBefore s permutation0 78 := by
  exact (positive_lex_of_descriptor s 2612 permutation0 81 (by rfl)).trans ((lex_skipped s permutation0 78 81 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 79 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation0 78) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation0 78 by rw [image0_eq]; rfl))

theorem lex_0_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2613) (Sat.Literal.pos 2612) (Sat.Literal.pos 78) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation0 78 (assignment s)
    (Sat.Literal.pos 2613) (Sat.Literal.pos 2612) (Sat.Literal.pos 78) (Sat.Literal.pos 77) (positive_of_descriptor s 2613 (.lex permutation0 78) (by rfl)) (lex_0_78_prefix s) (positive_select s 78) (lex_0_78_image s)

theorem lex_0_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2612), (Sat.Literal.pos 78), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation0 78 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2612) (Sat.Literal.pos 78) (Sat.Literal.pos 77) (lex_0_78_prefix s) (positive_select s 78) (lex_0_78_image s)

theorem lex_0_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2613), (Sat.Literal.pos 2612)] :=
  (lex_0_78_gate s).prop _ (List.Mem.head _)

theorem lex_0_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2613), (Sat.Literal.neg 78), (Sat.Literal.pos 77)] :=
  (lex_0_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2613), (Sat.Literal.pos 78), (Sat.Literal.neg 77)] :=
  (lex_0_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2612), (Sat.Literal.neg 78), (Sat.Literal.neg 77), (Sat.Literal.pos 2613)] :=
  (lex_0_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2612), (Sat.Literal.pos 78), (Sat.Literal.pos 77), (Sat.Literal.pos 2613)] :=
  (lex_0_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2613) = lexBefore s permutation0 77 := by
  exact (positive_lex_of_descriptor s 2613 permutation0 78 (by rfl)).trans ((lex_skipped s permutation0 77 78 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation0 77) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation0 77 by rw [image0_eq]; rfl))

theorem lex_0_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2614) (Sat.Literal.pos 2613) (Sat.Literal.pos 77) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation0 77 (assignment s)
    (Sat.Literal.pos 2614) (Sat.Literal.pos 2613) (Sat.Literal.pos 77) (Sat.Literal.pos 78) (positive_of_descriptor s 2614 (.lex permutation0 77) (by rfl)) (lex_0_77_prefix s) (positive_select s 77) (lex_0_77_image s)

theorem lex_0_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2613), (Sat.Literal.pos 77), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation0 77 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2613) (Sat.Literal.pos 77) (Sat.Literal.pos 78) (lex_0_77_prefix s) (positive_select s 77) (lex_0_77_image s)

theorem lex_0_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2614), (Sat.Literal.pos 2613)] :=
  (lex_0_77_gate s).prop _ (List.Mem.head _)

theorem lex_0_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2614), (Sat.Literal.neg 77), (Sat.Literal.pos 78)] :=
  (lex_0_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2614), (Sat.Literal.pos 77), (Sat.Literal.neg 78)] :=
  (lex_0_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2613), (Sat.Literal.neg 77), (Sat.Literal.neg 78), (Sat.Literal.pos 2614)] :=
  (lex_0_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2613), (Sat.Literal.pos 77), (Sat.Literal.pos 78), (Sat.Literal.pos 2614)] :=
  (lex_0_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2614) = lexBefore s permutation0 74 := by
  exact (positive_lex_of_descriptor s 2614 permutation0 77 (by rfl)).trans ((lex_skipped s permutation0 74 77 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 75 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation0 74) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation0 74 by rw [image0_eq]; rfl))

theorem lex_0_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2615) (Sat.Literal.pos 2614) (Sat.Literal.pos 74) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation0 74 (assignment s)
    (Sat.Literal.pos 2615) (Sat.Literal.pos 2614) (Sat.Literal.pos 74) (Sat.Literal.pos 73) (positive_of_descriptor s 2615 (.lex permutation0 74) (by rfl)) (lex_0_74_prefix s) (positive_select s 74) (lex_0_74_image s)

theorem lex_0_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2614), (Sat.Literal.pos 74), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation0 74 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2614) (Sat.Literal.pos 74) (Sat.Literal.pos 73) (lex_0_74_prefix s) (positive_select s 74) (lex_0_74_image s)

theorem lex_0_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2615), (Sat.Literal.pos 2614)] :=
  (lex_0_74_gate s).prop _ (List.Mem.head _)

theorem lex_0_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2615), (Sat.Literal.neg 74), (Sat.Literal.pos 73)] :=
  (lex_0_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2615), (Sat.Literal.pos 74), (Sat.Literal.neg 73)] :=
  (lex_0_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2614), (Sat.Literal.neg 74), (Sat.Literal.neg 73), (Sat.Literal.pos 2615)] :=
  (lex_0_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2614), (Sat.Literal.pos 74), (Sat.Literal.pos 73), (Sat.Literal.pos 2615)] :=
  (lex_0_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2615) = lexBefore s permutation0 73 := by
  exact (positive_lex_of_descriptor s 2615 permutation0 74 (by rfl)).trans ((lex_skipped s permutation0 73 74 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation0 73) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation0 73 by rw [image0_eq]; rfl))

theorem lex_0_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2616) (Sat.Literal.pos 2615) (Sat.Literal.pos 73) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation0 73 (assignment s)
    (Sat.Literal.pos 2616) (Sat.Literal.pos 2615) (Sat.Literal.pos 73) (Sat.Literal.pos 74) (positive_of_descriptor s 2616 (.lex permutation0 73) (by rfl)) (lex_0_73_prefix s) (positive_select s 73) (lex_0_73_image s)

theorem lex_0_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2615), (Sat.Literal.pos 73), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation0 73 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2615) (Sat.Literal.pos 73) (Sat.Literal.pos 74) (lex_0_73_prefix s) (positive_select s 73) (lex_0_73_image s)

theorem lex_0_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2616), (Sat.Literal.pos 2615)] :=
  (lex_0_73_gate s).prop _ (List.Mem.head _)

theorem lex_0_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2616), (Sat.Literal.neg 73), (Sat.Literal.pos 74)] :=
  (lex_0_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2616), (Sat.Literal.pos 73), (Sat.Literal.neg 74)] :=
  (lex_0_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2615), (Sat.Literal.neg 73), (Sat.Literal.neg 74), (Sat.Literal.pos 2616)] :=
  (lex_0_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2615), (Sat.Literal.pos 73), (Sat.Literal.pos 74), (Sat.Literal.pos 2616)] :=
  (lex_0_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2616) = lexBefore s permutation0 70 := by
  exact (positive_lex_of_descriptor s 2616 permutation0 73 (by rfl)).trans ((lex_skipped s permutation0 70 73 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 71 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation0 70) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation0 70 by rw [image0_eq]; rfl))

theorem lex_0_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2617) (Sat.Literal.pos 2616) (Sat.Literal.pos 70) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation0 70 (assignment s)
    (Sat.Literal.pos 2617) (Sat.Literal.pos 2616) (Sat.Literal.pos 70) (Sat.Literal.pos 69) (positive_of_descriptor s 2617 (.lex permutation0 70) (by rfl)) (lex_0_70_prefix s) (positive_select s 70) (lex_0_70_image s)

theorem lex_0_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2616), (Sat.Literal.pos 70), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation0 70 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2616) (Sat.Literal.pos 70) (Sat.Literal.pos 69) (lex_0_70_prefix s) (positive_select s 70) (lex_0_70_image s)

theorem lex_0_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2617), (Sat.Literal.pos 2616)] :=
  (lex_0_70_gate s).prop _ (List.Mem.head _)

theorem lex_0_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2617), (Sat.Literal.neg 70), (Sat.Literal.pos 69)] :=
  (lex_0_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2617), (Sat.Literal.pos 70), (Sat.Literal.neg 69)] :=
  (lex_0_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2616), (Sat.Literal.neg 70), (Sat.Literal.neg 69), (Sat.Literal.pos 2617)] :=
  (lex_0_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2616), (Sat.Literal.pos 70), (Sat.Literal.pos 69), (Sat.Literal.pos 2617)] :=
  (lex_0_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2617) = lexBefore s permutation0 69 := by
  exact (positive_lex_of_descriptor s 2617 permutation0 70 (by rfl)).trans ((lex_skipped s permutation0 69 70 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation0 69) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation0 69 by rw [image0_eq]; rfl))

theorem lex_0_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2618) (Sat.Literal.pos 2617) (Sat.Literal.pos 69) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation0 69 (assignment s)
    (Sat.Literal.pos 2618) (Sat.Literal.pos 2617) (Sat.Literal.pos 69) (Sat.Literal.pos 70) (positive_of_descriptor s 2618 (.lex permutation0 69) (by rfl)) (lex_0_69_prefix s) (positive_select s 69) (lex_0_69_image s)

theorem lex_0_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2617), (Sat.Literal.pos 69), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation0 69 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2617) (Sat.Literal.pos 69) (Sat.Literal.pos 70) (lex_0_69_prefix s) (positive_select s 69) (lex_0_69_image s)

theorem lex_0_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2618), (Sat.Literal.pos 2617)] :=
  (lex_0_69_gate s).prop _ (List.Mem.head _)

theorem lex_0_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2618), (Sat.Literal.neg 69), (Sat.Literal.pos 70)] :=
  (lex_0_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2618), (Sat.Literal.pos 69), (Sat.Literal.neg 70)] :=
  (lex_0_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2617), (Sat.Literal.neg 69), (Sat.Literal.neg 70), (Sat.Literal.pos 2618)] :=
  (lex_0_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2617), (Sat.Literal.pos 69), (Sat.Literal.pos 70), (Sat.Literal.pos 2618)] :=
  (lex_0_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2618) = lexBefore s permutation0 66 := by
  exact (positive_lex_of_descriptor s 2618 permutation0 69 (by rfl)).trans ((lex_skipped s permutation0 66 69 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 67 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation0 66) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation0 66 by rw [image0_eq]; rfl))

theorem lex_0_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2619) (Sat.Literal.pos 2618) (Sat.Literal.pos 66) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation0 66 (assignment s)
    (Sat.Literal.pos 2619) (Sat.Literal.pos 2618) (Sat.Literal.pos 66) (Sat.Literal.pos 65) (positive_of_descriptor s 2619 (.lex permutation0 66) (by rfl)) (lex_0_66_prefix s) (positive_select s 66) (lex_0_66_image s)

theorem lex_0_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2618), (Sat.Literal.pos 66), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation0 66 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2618) (Sat.Literal.pos 66) (Sat.Literal.pos 65) (lex_0_66_prefix s) (positive_select s 66) (lex_0_66_image s)

theorem lex_0_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2619), (Sat.Literal.pos 2618)] :=
  (lex_0_66_gate s).prop _ (List.Mem.head _)

theorem lex_0_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2619), (Sat.Literal.neg 66), (Sat.Literal.pos 65)] :=
  (lex_0_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2619), (Sat.Literal.pos 66), (Sat.Literal.neg 65)] :=
  (lex_0_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2618), (Sat.Literal.neg 66), (Sat.Literal.neg 65), (Sat.Literal.pos 2619)] :=
  (lex_0_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2618), (Sat.Literal.pos 66), (Sat.Literal.pos 65), (Sat.Literal.pos 2619)] :=
  (lex_0_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2619) = lexBefore s permutation0 65 := by
  exact (positive_lex_of_descriptor s 2619 permutation0 66 (by rfl)).trans ((lex_skipped s permutation0 65 66 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation0 65) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation0 65 by rw [image0_eq]; rfl))

theorem lex_0_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2620) (Sat.Literal.pos 2619) (Sat.Literal.pos 65) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation0 65 (assignment s)
    (Sat.Literal.pos 2620) (Sat.Literal.pos 2619) (Sat.Literal.pos 65) (Sat.Literal.pos 66) (positive_of_descriptor s 2620 (.lex permutation0 65) (by rfl)) (lex_0_65_prefix s) (positive_select s 65) (lex_0_65_image s)

theorem lex_0_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2619), (Sat.Literal.pos 65), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation0 65 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2619) (Sat.Literal.pos 65) (Sat.Literal.pos 66) (lex_0_65_prefix s) (positive_select s 65) (lex_0_65_image s)

theorem lex_0_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2620), (Sat.Literal.pos 2619)] :=
  (lex_0_65_gate s).prop _ (List.Mem.head _)

theorem lex_0_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2620), (Sat.Literal.neg 65), (Sat.Literal.pos 66)] :=
  (lex_0_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2620), (Sat.Literal.pos 65), (Sat.Literal.neg 66)] :=
  (lex_0_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2619), (Sat.Literal.neg 65), (Sat.Literal.neg 66), (Sat.Literal.pos 2620)] :=
  (lex_0_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2619), (Sat.Literal.pos 65), (Sat.Literal.pos 66), (Sat.Literal.pos 2620)] :=
  (lex_0_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_62_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2620) = lexBefore s permutation0 62 := by
  exact (positive_lex_of_descriptor s 2620 permutation0 65 (by rfl)).trans ((lex_skipped s permutation0 62 65 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 63 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_62_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation0 62) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation0 62 by rw [image0_eq]; rfl))

theorem lex_0_62_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2621) (Sat.Literal.pos 2620) (Sat.Literal.pos 62) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation0 62 (assignment s)
    (Sat.Literal.pos 2621) (Sat.Literal.pos 2620) (Sat.Literal.pos 62) (Sat.Literal.pos 61) (positive_of_descriptor s 2621 (.lex permutation0 62) (by rfl)) (lex_0_62_prefix s) (positive_select s 62) (lex_0_62_image s)

theorem lex_0_62_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2620), (Sat.Literal.pos 62), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation0 62 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2620) (Sat.Literal.pos 62) (Sat.Literal.pos 61) (lex_0_62_prefix s) (positive_select s 62) (lex_0_62_image s)

theorem lex_0_62_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2621), (Sat.Literal.pos 2620)] :=
  (lex_0_62_gate s).prop _ (List.Mem.head _)

theorem lex_0_62_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2621), (Sat.Literal.neg 62), (Sat.Literal.pos 61)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_62_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2621), (Sat.Literal.pos 62), (Sat.Literal.neg 61)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_62_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2620), (Sat.Literal.neg 62), (Sat.Literal.neg 61), (Sat.Literal.pos 2621)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_62_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2620), (Sat.Literal.pos 62), (Sat.Literal.pos 61), (Sat.Literal.pos 2621)] :=
  (lex_0_62_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_61_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2621) = lexBefore s permutation0 61 := by
  exact (positive_lex_of_descriptor s 2621 permutation0 62 (by rfl)).trans ((lex_skipped s permutation0 61 62 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 62 62 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_61_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation0 61) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation0 61 by rw [image0_eq]; rfl))

theorem lex_0_61_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2622) (Sat.Literal.pos 2621) (Sat.Literal.pos 61) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation0 61 (assignment s)
    (Sat.Literal.pos 2622) (Sat.Literal.pos 2621) (Sat.Literal.pos 61) (Sat.Literal.pos 62) (positive_of_descriptor s 2622 (.lex permutation0 61) (by rfl)) (lex_0_61_prefix s) (positive_select s 61) (lex_0_61_image s)

theorem lex_0_61_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2621), (Sat.Literal.pos 61), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation0 61 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2621) (Sat.Literal.pos 61) (Sat.Literal.pos 62) (lex_0_61_prefix s) (positive_select s 61) (lex_0_61_image s)

theorem lex_0_61_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2622), (Sat.Literal.pos 2621)] :=
  (lex_0_61_gate s).prop _ (List.Mem.head _)

theorem lex_0_61_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2622), (Sat.Literal.neg 61), (Sat.Literal.pos 62)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_61_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2622), (Sat.Literal.pos 61), (Sat.Literal.neg 62)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_61_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2621), (Sat.Literal.neg 61), (Sat.Literal.neg 62), (Sat.Literal.pos 2622)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_61_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2621), (Sat.Literal.pos 61), (Sat.Literal.pos 62), (Sat.Literal.pos 2622)] :=
  (lex_0_61_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_58_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2622) = lexBefore s permutation0 58 := by
  exact (positive_lex_of_descriptor s 2622 permutation0 61 (by rfl)).trans ((lex_skipped s permutation0 58 61 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 59 61 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_58_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation0 58) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation0 58 by rw [image0_eq]; rfl))

theorem lex_0_58_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2623) (Sat.Literal.pos 2622) (Sat.Literal.pos 58) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation0 58 (assignment s)
    (Sat.Literal.pos 2623) (Sat.Literal.pos 2622) (Sat.Literal.pos 58) (Sat.Literal.pos 57) (positive_of_descriptor s 2623 (.lex permutation0 58) (by rfl)) (lex_0_58_prefix s) (positive_select s 58) (lex_0_58_image s)

theorem lex_0_58_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2622), (Sat.Literal.pos 58), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation0 58 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2622) (Sat.Literal.pos 58) (Sat.Literal.pos 57) (lex_0_58_prefix s) (positive_select s 58) (lex_0_58_image s)

theorem lex_0_58_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2623), (Sat.Literal.pos 2622)] :=
  (lex_0_58_gate s).prop _ (List.Mem.head _)

theorem lex_0_58_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2623), (Sat.Literal.neg 58), (Sat.Literal.pos 57)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_58_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2623), (Sat.Literal.pos 58), (Sat.Literal.neg 57)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_58_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2622), (Sat.Literal.neg 58), (Sat.Literal.neg 57), (Sat.Literal.pos 2623)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_58_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2622), (Sat.Literal.pos 58), (Sat.Literal.pos 57), (Sat.Literal.pos 2623)] :=
  (lex_0_58_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_0_57_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 2623) = lexBefore s permutation0 57 := by
  exact (positive_lex_of_descriptor s 2623 permutation0 58 (by rfl)).trans ((lex_skipped s permutation0 57 58 (by decide) (by intro j hj hp; rw [image0_eq]; exact fixedOnRange_spec image0 58 58 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_0_57_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation0 57) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation0 57 by rw [image0_eq]; rfl))

theorem lex_0_57_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 2624) (Sat.Literal.pos 2623) (Sat.Literal.pos 57) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation0 57 (assignment s)
    (Sat.Literal.pos 2624) (Sat.Literal.pos 2623) (Sat.Literal.pos 57) (Sat.Literal.pos 58) (positive_of_descriptor s 2624 (.lex permutation0 57) (by rfl)) (lex_0_57_prefix s) (positive_select s 57) (lex_0_57_image s)

theorem lex_0_57_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2623), (Sat.Literal.pos 57), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation0 57 (hmax permutation0) (assignment s)
    (Sat.Literal.pos 2623) (Sat.Literal.pos 57) (Sat.Literal.pos 58) (lex_0_57_prefix s) (positive_select s 57) (lex_0_57_image s)

theorem lex_0_57_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2624), (Sat.Literal.pos 2623)] :=
  (lex_0_57_gate s).prop _ (List.Mem.head _)

theorem lex_0_57_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2624), (Sat.Literal.neg 57), (Sat.Literal.pos 58)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_0_57_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2624), (Sat.Literal.pos 57), (Sat.Literal.neg 58)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_0_57_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2623), (Sat.Literal.neg 57), (Sat.Literal.neg 58), (Sat.Literal.pos 2624)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_0_57_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 2623), (Sat.Literal.pos 57), (Sat.Literal.pos 58), (Sat.Literal.pos 2624)] :=
  (lex_0_57_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_0_254_gate

end Crown.CertificateData
