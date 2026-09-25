import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_7_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3424) = lexBefore s permutation7 250 := by
  exact (positive_lex_of_descriptor s 3424 permutation7 251 (by rfl)).trans ((lex_skipped s permutation7 250 251 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation7 250) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation7 250 by rw [image7_eq]; rfl))

theorem lex_7_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3425) (Sat.Literal.pos 3424) (Sat.Literal.pos 250) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation7 250 (assignment s)
    (Sat.Literal.pos 3425) (Sat.Literal.pos 3424) (Sat.Literal.pos 250) (Sat.Literal.pos 245) (positive_of_descriptor s 3425 (.lex permutation7 250) (by rfl)) (lex_7_250_prefix s) (positive_select s 250) (lex_7_250_image s)

theorem lex_7_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3424), (Sat.Literal.pos 250), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation7 250 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3424) (Sat.Literal.pos 250) (Sat.Literal.pos 245) (lex_7_250_prefix s) (positive_select s 250) (lex_7_250_image s)

theorem lex_7_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3425), (Sat.Literal.pos 3424)] :=
  (lex_7_250_gate s).prop _ (List.Mem.head _)

theorem lex_7_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3425), (Sat.Literal.neg 250), (Sat.Literal.pos 245)] :=
  (lex_7_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3425), (Sat.Literal.pos 250), (Sat.Literal.neg 245)] :=
  (lex_7_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3424), (Sat.Literal.neg 250), (Sat.Literal.neg 245), (Sat.Literal.pos 3425)] :=
  (lex_7_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3424), (Sat.Literal.pos 250), (Sat.Literal.pos 245), (Sat.Literal.pos 3425)] :=
  (lex_7_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3425) = lexBefore s permutation7 249 := by
  exact (positive_lex_of_descriptor s 3425 permutation7 250 (by rfl)).trans ((lex_skipped s permutation7 249 250 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation7 249) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation7 249 by rw [image7_eq]; rfl))

theorem lex_7_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3426) (Sat.Literal.pos 3425) (Sat.Literal.pos 249) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation7 249 (assignment s)
    (Sat.Literal.pos 3426) (Sat.Literal.pos 3425) (Sat.Literal.pos 249) (Sat.Literal.pos 243) (positive_of_descriptor s 3426 (.lex permutation7 249) (by rfl)) (lex_7_249_prefix s) (positive_select s 249) (lex_7_249_image s)

theorem lex_7_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3425), (Sat.Literal.pos 249), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation7 249 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3425) (Sat.Literal.pos 249) (Sat.Literal.pos 243) (lex_7_249_prefix s) (positive_select s 249) (lex_7_249_image s)

theorem lex_7_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3426), (Sat.Literal.pos 3425)] :=
  (lex_7_249_gate s).prop _ (List.Mem.head _)

theorem lex_7_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3426), (Sat.Literal.neg 249), (Sat.Literal.pos 243)] :=
  (lex_7_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3426), (Sat.Literal.pos 249), (Sat.Literal.neg 243)] :=
  (lex_7_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3425), (Sat.Literal.neg 249), (Sat.Literal.neg 243), (Sat.Literal.pos 3426)] :=
  (lex_7_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3425), (Sat.Literal.pos 249), (Sat.Literal.pos 243), (Sat.Literal.pos 3426)] :=
  (lex_7_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3426) = lexBefore s permutation7 248 := by
  exact (positive_lex_of_descriptor s 3426 permutation7 249 (by rfl)).trans ((lex_skipped s permutation7 248 249 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 241) = s (permuteMask permutation7 248) := by
  exact (positive_select s 241).trans (congrArg s (show (241 : Fin 256) = permuteMask permutation7 248 by rw [image7_eq]; rfl))

theorem lex_7_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3427) (Sat.Literal.pos 3426) (Sat.Literal.pos 248) (Sat.Literal.pos 241)) := by
  exact equality_gate s permutation7 248 (assignment s)
    (Sat.Literal.pos 3427) (Sat.Literal.pos 3426) (Sat.Literal.pos 248) (Sat.Literal.pos 241) (positive_of_descriptor s 3427 (.lex permutation7 248) (by rfl)) (lex_7_248_prefix s) (positive_select s 248) (lex_7_248_image s)

theorem lex_7_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3426), (Sat.Literal.pos 248), (Sat.Literal.neg 241)] := by
  exact comparison_gate s permutation7 248 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3426) (Sat.Literal.pos 248) (Sat.Literal.pos 241) (lex_7_248_prefix s) (positive_select s 248) (lex_7_248_image s)

theorem lex_7_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3427), (Sat.Literal.pos 3426)] :=
  (lex_7_248_gate s).prop _ (List.Mem.head _)

theorem lex_7_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3427), (Sat.Literal.neg 248), (Sat.Literal.pos 241)] :=
  (lex_7_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3427), (Sat.Literal.pos 248), (Sat.Literal.neg 241)] :=
  (lex_7_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3426), (Sat.Literal.neg 248), (Sat.Literal.neg 241), (Sat.Literal.pos 3427)] :=
  (lex_7_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3426), (Sat.Literal.pos 248), (Sat.Literal.pos 241), (Sat.Literal.pos 3427)] :=
  (lex_7_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3427) = lexBefore s permutation7 247 := by
  exact (positive_lex_of_descriptor s 3427 permutation7 248 (by rfl)).trans ((lex_skipped s permutation7 247 248 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 239) = s (permuteMask permutation7 247) := by
  exact (positive_select s 239).trans (congrArg s (show (239 : Fin 256) = permuteMask permutation7 247 by rw [image7_eq]; rfl))

theorem lex_7_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3428) (Sat.Literal.pos 3427) (Sat.Literal.pos 247) (Sat.Literal.pos 239)) := by
  exact equality_gate s permutation7 247 (assignment s)
    (Sat.Literal.pos 3428) (Sat.Literal.pos 3427) (Sat.Literal.pos 247) (Sat.Literal.pos 239) (positive_of_descriptor s 3428 (.lex permutation7 247) (by rfl)) (lex_7_247_prefix s) (positive_select s 247) (lex_7_247_image s)

theorem lex_7_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3427), (Sat.Literal.pos 247), (Sat.Literal.neg 239)] := by
  exact comparison_gate s permutation7 247 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3427) (Sat.Literal.pos 247) (Sat.Literal.pos 239) (lex_7_247_prefix s) (positive_select s 247) (lex_7_247_image s)

theorem lex_7_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3428), (Sat.Literal.pos 3427)] :=
  (lex_7_247_gate s).prop _ (List.Mem.head _)

theorem lex_7_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3428), (Sat.Literal.neg 247), (Sat.Literal.pos 239)] :=
  (lex_7_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3428), (Sat.Literal.pos 247), (Sat.Literal.neg 239)] :=
  (lex_7_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3427), (Sat.Literal.neg 247), (Sat.Literal.neg 239), (Sat.Literal.pos 3428)] :=
  (lex_7_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3427), (Sat.Literal.pos 247), (Sat.Literal.pos 239), (Sat.Literal.pos 3428)] :=
  (lex_7_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3428) = lexBefore s permutation7 246 := by
  exact (positive_lex_of_descriptor s 3428 permutation7 247 (by rfl)).trans ((lex_skipped s permutation7 246 247 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 237) = s (permuteMask permutation7 246) := by
  exact (positive_select s 237).trans (congrArg s (show (237 : Fin 256) = permuteMask permutation7 246 by rw [image7_eq]; rfl))

theorem lex_7_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3429) (Sat.Literal.pos 3428) (Sat.Literal.pos 246) (Sat.Literal.pos 237)) := by
  exact equality_gate s permutation7 246 (assignment s)
    (Sat.Literal.pos 3429) (Sat.Literal.pos 3428) (Sat.Literal.pos 246) (Sat.Literal.pos 237) (positive_of_descriptor s 3429 (.lex permutation7 246) (by rfl)) (lex_7_246_prefix s) (positive_select s 246) (lex_7_246_image s)

theorem lex_7_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3428), (Sat.Literal.pos 246), (Sat.Literal.neg 237)] := by
  exact comparison_gate s permutation7 246 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3428) (Sat.Literal.pos 246) (Sat.Literal.pos 237) (lex_7_246_prefix s) (positive_select s 246) (lex_7_246_image s)

theorem lex_7_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3429), (Sat.Literal.pos 3428)] :=
  (lex_7_246_gate s).prop _ (List.Mem.head _)

theorem lex_7_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3429), (Sat.Literal.neg 246), (Sat.Literal.pos 237)] :=
  (lex_7_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3429), (Sat.Literal.pos 246), (Sat.Literal.neg 237)] :=
  (lex_7_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3428), (Sat.Literal.neg 246), (Sat.Literal.neg 237), (Sat.Literal.pos 3429)] :=
  (lex_7_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3428), (Sat.Literal.pos 246), (Sat.Literal.pos 237), (Sat.Literal.pos 3429)] :=
  (lex_7_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3429) = lexBefore s permutation7 245 := by
  exact (positive_lex_of_descriptor s 3429 permutation7 246 (by rfl)).trans ((lex_skipped s permutation7 245 246 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 235) = s (permuteMask permutation7 245) := by
  exact (positive_select s 235).trans (congrArg s (show (235 : Fin 256) = permuteMask permutation7 245 by rw [image7_eq]; rfl))

theorem lex_7_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3430) (Sat.Literal.pos 3429) (Sat.Literal.pos 245) (Sat.Literal.pos 235)) := by
  exact equality_gate s permutation7 245 (assignment s)
    (Sat.Literal.pos 3430) (Sat.Literal.pos 3429) (Sat.Literal.pos 245) (Sat.Literal.pos 235) (positive_of_descriptor s 3430 (.lex permutation7 245) (by rfl)) (lex_7_245_prefix s) (positive_select s 245) (lex_7_245_image s)

theorem lex_7_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3429), (Sat.Literal.pos 245), (Sat.Literal.neg 235)] := by
  exact comparison_gate s permutation7 245 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3429) (Sat.Literal.pos 245) (Sat.Literal.pos 235) (lex_7_245_prefix s) (positive_select s 245) (lex_7_245_image s)

theorem lex_7_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3430), (Sat.Literal.pos 3429)] :=
  (lex_7_245_gate s).prop _ (List.Mem.head _)

theorem lex_7_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3430), (Sat.Literal.neg 245), (Sat.Literal.pos 235)] :=
  (lex_7_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3430), (Sat.Literal.pos 245), (Sat.Literal.neg 235)] :=
  (lex_7_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3429), (Sat.Literal.neg 245), (Sat.Literal.neg 235), (Sat.Literal.pos 3430)] :=
  (lex_7_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3429), (Sat.Literal.pos 245), (Sat.Literal.pos 235), (Sat.Literal.pos 3430)] :=
  (lex_7_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3430) = lexBefore s permutation7 244 := by
  exact (positive_lex_of_descriptor s 3430 permutation7 245 (by rfl)).trans ((lex_skipped s permutation7 244 245 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 233) = s (permuteMask permutation7 244) := by
  exact (positive_select s 233).trans (congrArg s (show (233 : Fin 256) = permuteMask permutation7 244 by rw [image7_eq]; rfl))

theorem lex_7_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3431) (Sat.Literal.pos 3430) (Sat.Literal.pos 244) (Sat.Literal.pos 233)) := by
  exact equality_gate s permutation7 244 (assignment s)
    (Sat.Literal.pos 3431) (Sat.Literal.pos 3430) (Sat.Literal.pos 244) (Sat.Literal.pos 233) (positive_of_descriptor s 3431 (.lex permutation7 244) (by rfl)) (lex_7_244_prefix s) (positive_select s 244) (lex_7_244_image s)

theorem lex_7_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3430), (Sat.Literal.pos 244), (Sat.Literal.neg 233)] := by
  exact comparison_gate s permutation7 244 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3430) (Sat.Literal.pos 244) (Sat.Literal.pos 233) (lex_7_244_prefix s) (positive_select s 244) (lex_7_244_image s)

theorem lex_7_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3431), (Sat.Literal.pos 3430)] :=
  (lex_7_244_gate s).prop _ (List.Mem.head _)

theorem lex_7_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3431), (Sat.Literal.neg 244), (Sat.Literal.pos 233)] :=
  (lex_7_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3431), (Sat.Literal.pos 244), (Sat.Literal.neg 233)] :=
  (lex_7_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3430), (Sat.Literal.neg 244), (Sat.Literal.neg 233), (Sat.Literal.pos 3431)] :=
  (lex_7_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3430), (Sat.Literal.pos 244), (Sat.Literal.pos 233), (Sat.Literal.pos 3431)] :=
  (lex_7_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3431) = lexBefore s permutation7 243 := by
  exact (positive_lex_of_descriptor s 3431 permutation7 244 (by rfl)).trans ((lex_skipped s permutation7 243 244 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 231) = s (permuteMask permutation7 243) := by
  exact (positive_select s 231).trans (congrArg s (show (231 : Fin 256) = permuteMask permutation7 243 by rw [image7_eq]; rfl))

theorem lex_7_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3432) (Sat.Literal.pos 3431) (Sat.Literal.pos 243) (Sat.Literal.pos 231)) := by
  exact equality_gate s permutation7 243 (assignment s)
    (Sat.Literal.pos 3432) (Sat.Literal.pos 3431) (Sat.Literal.pos 243) (Sat.Literal.pos 231) (positive_of_descriptor s 3432 (.lex permutation7 243) (by rfl)) (lex_7_243_prefix s) (positive_select s 243) (lex_7_243_image s)

theorem lex_7_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3431), (Sat.Literal.pos 243), (Sat.Literal.neg 231)] := by
  exact comparison_gate s permutation7 243 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3431) (Sat.Literal.pos 243) (Sat.Literal.pos 231) (lex_7_243_prefix s) (positive_select s 243) (lex_7_243_image s)

theorem lex_7_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3432), (Sat.Literal.pos 3431)] :=
  (lex_7_243_gate s).prop _ (List.Mem.head _)

theorem lex_7_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3432), (Sat.Literal.neg 243), (Sat.Literal.pos 231)] :=
  (lex_7_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3432), (Sat.Literal.pos 243), (Sat.Literal.neg 231)] :=
  (lex_7_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3431), (Sat.Literal.neg 243), (Sat.Literal.neg 231), (Sat.Literal.pos 3432)] :=
  (lex_7_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3431), (Sat.Literal.pos 243), (Sat.Literal.pos 231), (Sat.Literal.pos 3432)] :=
  (lex_7_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3432) = lexBefore s permutation7 242 := by
  exact (positive_lex_of_descriptor s 3432 permutation7 243 (by rfl)).trans ((lex_skipped s permutation7 242 243 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 229) = s (permuteMask permutation7 242) := by
  exact (positive_select s 229).trans (congrArg s (show (229 : Fin 256) = permuteMask permutation7 242 by rw [image7_eq]; rfl))

theorem lex_7_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3433) (Sat.Literal.pos 3432) (Sat.Literal.pos 242) (Sat.Literal.pos 229)) := by
  exact equality_gate s permutation7 242 (assignment s)
    (Sat.Literal.pos 3433) (Sat.Literal.pos 3432) (Sat.Literal.pos 242) (Sat.Literal.pos 229) (positive_of_descriptor s 3433 (.lex permutation7 242) (by rfl)) (lex_7_242_prefix s) (positive_select s 242) (lex_7_242_image s)

theorem lex_7_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3432), (Sat.Literal.pos 242), (Sat.Literal.neg 229)] := by
  exact comparison_gate s permutation7 242 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3432) (Sat.Literal.pos 242) (Sat.Literal.pos 229) (lex_7_242_prefix s) (positive_select s 242) (lex_7_242_image s)

theorem lex_7_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3433), (Sat.Literal.pos 3432)] :=
  (lex_7_242_gate s).prop _ (List.Mem.head _)

theorem lex_7_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3433), (Sat.Literal.neg 242), (Sat.Literal.pos 229)] :=
  (lex_7_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3433), (Sat.Literal.pos 242), (Sat.Literal.neg 229)] :=
  (lex_7_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3432), (Sat.Literal.neg 242), (Sat.Literal.neg 229), (Sat.Literal.pos 3433)] :=
  (lex_7_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3432), (Sat.Literal.pos 242), (Sat.Literal.pos 229), (Sat.Literal.pos 3433)] :=
  (lex_7_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3433) = lexBefore s permutation7 241 := by
  exact (positive_lex_of_descriptor s 3433 permutation7 242 (by rfl)).trans ((lex_skipped s permutation7 241 242 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 227) = s (permuteMask permutation7 241) := by
  exact (positive_select s 227).trans (congrArg s (show (227 : Fin 256) = permuteMask permutation7 241 by rw [image7_eq]; rfl))

theorem lex_7_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3434) (Sat.Literal.pos 3433) (Sat.Literal.pos 241) (Sat.Literal.pos 227)) := by
  exact equality_gate s permutation7 241 (assignment s)
    (Sat.Literal.pos 3434) (Sat.Literal.pos 3433) (Sat.Literal.pos 241) (Sat.Literal.pos 227) (positive_of_descriptor s 3434 (.lex permutation7 241) (by rfl)) (lex_7_241_prefix s) (positive_select s 241) (lex_7_241_image s)

theorem lex_7_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3433), (Sat.Literal.pos 241), (Sat.Literal.neg 227)] := by
  exact comparison_gate s permutation7 241 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3433) (Sat.Literal.pos 241) (Sat.Literal.pos 227) (lex_7_241_prefix s) (positive_select s 241) (lex_7_241_image s)

theorem lex_7_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3434), (Sat.Literal.pos 3433)] :=
  (lex_7_241_gate s).prop _ (List.Mem.head _)

theorem lex_7_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3434), (Sat.Literal.neg 241), (Sat.Literal.pos 227)] :=
  (lex_7_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3434), (Sat.Literal.pos 241), (Sat.Literal.neg 227)] :=
  (lex_7_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3433), (Sat.Literal.neg 241), (Sat.Literal.neg 227), (Sat.Literal.pos 3434)] :=
  (lex_7_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3433), (Sat.Literal.pos 241), (Sat.Literal.pos 227), (Sat.Literal.pos 3434)] :=
  (lex_7_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3434) = lexBefore s permutation7 240 := by
  exact (positive_lex_of_descriptor s 3434 permutation7 241 (by rfl)).trans ((lex_skipped s permutation7 240 241 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 225) = s (permuteMask permutation7 240) := by
  exact (positive_select s 225).trans (congrArg s (show (225 : Fin 256) = permuteMask permutation7 240 by rw [image7_eq]; rfl))

theorem lex_7_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3435) (Sat.Literal.pos 3434) (Sat.Literal.pos 240) (Sat.Literal.pos 225)) := by
  exact equality_gate s permutation7 240 (assignment s)
    (Sat.Literal.pos 3435) (Sat.Literal.pos 3434) (Sat.Literal.pos 240) (Sat.Literal.pos 225) (positive_of_descriptor s 3435 (.lex permutation7 240) (by rfl)) (lex_7_240_prefix s) (positive_select s 240) (lex_7_240_image s)

theorem lex_7_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3434), (Sat.Literal.pos 240), (Sat.Literal.neg 225)] := by
  exact comparison_gate s permutation7 240 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3434) (Sat.Literal.pos 240) (Sat.Literal.pos 225) (lex_7_240_prefix s) (positive_select s 240) (lex_7_240_image s)

theorem lex_7_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3435), (Sat.Literal.pos 3434)] :=
  (lex_7_240_gate s).prop _ (List.Mem.head _)

theorem lex_7_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3435), (Sat.Literal.neg 240), (Sat.Literal.pos 225)] :=
  (lex_7_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3435), (Sat.Literal.pos 240), (Sat.Literal.neg 225)] :=
  (lex_7_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3434), (Sat.Literal.neg 240), (Sat.Literal.neg 225), (Sat.Literal.pos 3435)] :=
  (lex_7_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3434), (Sat.Literal.pos 240), (Sat.Literal.pos 225), (Sat.Literal.pos 3435)] :=
  (lex_7_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3435) = lexBefore s permutation7 239 := by
  exact (positive_lex_of_descriptor s 3435 permutation7 240 (by rfl)).trans ((lex_skipped s permutation7 239 240 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 223) = s (permuteMask permutation7 239) := by
  exact (positive_select s 223).trans (congrArg s (show (223 : Fin 256) = permuteMask permutation7 239 by rw [image7_eq]; rfl))

theorem lex_7_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3436) (Sat.Literal.pos 3435) (Sat.Literal.pos 239) (Sat.Literal.pos 223)) := by
  exact equality_gate s permutation7 239 (assignment s)
    (Sat.Literal.pos 3436) (Sat.Literal.pos 3435) (Sat.Literal.pos 239) (Sat.Literal.pos 223) (positive_of_descriptor s 3436 (.lex permutation7 239) (by rfl)) (lex_7_239_prefix s) (positive_select s 239) (lex_7_239_image s)

theorem lex_7_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3435), (Sat.Literal.pos 239), (Sat.Literal.neg 223)] := by
  exact comparison_gate s permutation7 239 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3435) (Sat.Literal.pos 239) (Sat.Literal.pos 223) (lex_7_239_prefix s) (positive_select s 239) (lex_7_239_image s)

theorem lex_7_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3436), (Sat.Literal.pos 3435)] :=
  (lex_7_239_gate s).prop _ (List.Mem.head _)

theorem lex_7_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3436), (Sat.Literal.neg 239), (Sat.Literal.pos 223)] :=
  (lex_7_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3436), (Sat.Literal.pos 239), (Sat.Literal.neg 223)] :=
  (lex_7_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3435), (Sat.Literal.neg 239), (Sat.Literal.neg 223), (Sat.Literal.pos 3436)] :=
  (lex_7_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3435), (Sat.Literal.pos 239), (Sat.Literal.pos 223), (Sat.Literal.pos 3436)] :=
  (lex_7_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3436) = lexBefore s permutation7 238 := by
  exact (positive_lex_of_descriptor s 3436 permutation7 239 (by rfl)).trans ((lex_skipped s permutation7 238 239 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation7 238) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation7 238 by rw [image7_eq]; rfl))

theorem lex_7_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3437) (Sat.Literal.pos 3436) (Sat.Literal.pos 238) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation7 238 (assignment s)
    (Sat.Literal.pos 3437) (Sat.Literal.pos 3436) (Sat.Literal.pos 238) (Sat.Literal.pos 221) (positive_of_descriptor s 3437 (.lex permutation7 238) (by rfl)) (lex_7_238_prefix s) (positive_select s 238) (lex_7_238_image s)

theorem lex_7_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3436), (Sat.Literal.pos 238), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation7 238 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3436) (Sat.Literal.pos 238) (Sat.Literal.pos 221) (lex_7_238_prefix s) (positive_select s 238) (lex_7_238_image s)

theorem lex_7_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3437), (Sat.Literal.pos 3436)] :=
  (lex_7_238_gate s).prop _ (List.Mem.head _)

theorem lex_7_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3437), (Sat.Literal.neg 238), (Sat.Literal.pos 221)] :=
  (lex_7_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3437), (Sat.Literal.pos 238), (Sat.Literal.neg 221)] :=
  (lex_7_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3436), (Sat.Literal.neg 238), (Sat.Literal.neg 221), (Sat.Literal.pos 3437)] :=
  (lex_7_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3436), (Sat.Literal.pos 238), (Sat.Literal.pos 221), (Sat.Literal.pos 3437)] :=
  (lex_7_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3437) = lexBefore s permutation7 237 := by
  exact (positive_lex_of_descriptor s 3437 permutation7 238 (by rfl)).trans ((lex_skipped s permutation7 237 238 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation7 237) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation7 237 by rw [image7_eq]; rfl))

theorem lex_7_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3438) (Sat.Literal.pos 3437) (Sat.Literal.pos 237) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation7 237 (assignment s)
    (Sat.Literal.pos 3438) (Sat.Literal.pos 3437) (Sat.Literal.pos 237) (Sat.Literal.pos 219) (positive_of_descriptor s 3438 (.lex permutation7 237) (by rfl)) (lex_7_237_prefix s) (positive_select s 237) (lex_7_237_image s)

theorem lex_7_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3437), (Sat.Literal.pos 237), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation7 237 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3437) (Sat.Literal.pos 237) (Sat.Literal.pos 219) (lex_7_237_prefix s) (positive_select s 237) (lex_7_237_image s)

theorem lex_7_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3438), (Sat.Literal.pos 3437)] :=
  (lex_7_237_gate s).prop _ (List.Mem.head _)

theorem lex_7_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3438), (Sat.Literal.neg 237), (Sat.Literal.pos 219)] :=
  (lex_7_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3438), (Sat.Literal.pos 237), (Sat.Literal.neg 219)] :=
  (lex_7_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3437), (Sat.Literal.neg 237), (Sat.Literal.neg 219), (Sat.Literal.pos 3438)] :=
  (lex_7_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3437), (Sat.Literal.pos 237), (Sat.Literal.pos 219), (Sat.Literal.pos 3438)] :=
  (lex_7_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3438) = lexBefore s permutation7 236 := by
  exact (positive_lex_of_descriptor s 3438 permutation7 237 (by rfl)).trans ((lex_skipped s permutation7 236 237 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation7 236) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation7 236 by rw [image7_eq]; rfl))

theorem lex_7_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3439) (Sat.Literal.pos 3438) (Sat.Literal.pos 236) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation7 236 (assignment s)
    (Sat.Literal.pos 3439) (Sat.Literal.pos 3438) (Sat.Literal.pos 236) (Sat.Literal.pos 217) (positive_of_descriptor s 3439 (.lex permutation7 236) (by rfl)) (lex_7_236_prefix s) (positive_select s 236) (lex_7_236_image s)

theorem lex_7_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3438), (Sat.Literal.pos 236), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation7 236 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3438) (Sat.Literal.pos 236) (Sat.Literal.pos 217) (lex_7_236_prefix s) (positive_select s 236) (lex_7_236_image s)

theorem lex_7_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3439), (Sat.Literal.pos 3438)] :=
  (lex_7_236_gate s).prop _ (List.Mem.head _)

theorem lex_7_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3439), (Sat.Literal.neg 236), (Sat.Literal.pos 217)] :=
  (lex_7_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3439), (Sat.Literal.pos 236), (Sat.Literal.neg 217)] :=
  (lex_7_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3438), (Sat.Literal.neg 236), (Sat.Literal.neg 217), (Sat.Literal.pos 3439)] :=
  (lex_7_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3438), (Sat.Literal.pos 236), (Sat.Literal.pos 217), (Sat.Literal.pos 3439)] :=
  (lex_7_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3439) = lexBefore s permutation7 235 := by
  exact (positive_lex_of_descriptor s 3439 permutation7 236 (by rfl)).trans ((lex_skipped s permutation7 235 236 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation7 235) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation7 235 by rw [image7_eq]; rfl))

theorem lex_7_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3440) (Sat.Literal.pos 3439) (Sat.Literal.pos 235) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation7 235 (assignment s)
    (Sat.Literal.pos 3440) (Sat.Literal.pos 3439) (Sat.Literal.pos 235) (Sat.Literal.pos 215) (positive_of_descriptor s 3440 (.lex permutation7 235) (by rfl)) (lex_7_235_prefix s) (positive_select s 235) (lex_7_235_image s)

theorem lex_7_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3439), (Sat.Literal.pos 235), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation7 235 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3439) (Sat.Literal.pos 235) (Sat.Literal.pos 215) (lex_7_235_prefix s) (positive_select s 235) (lex_7_235_image s)

theorem lex_7_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3440), (Sat.Literal.pos 3439)] :=
  (lex_7_235_gate s).prop _ (List.Mem.head _)

theorem lex_7_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3440), (Sat.Literal.neg 235), (Sat.Literal.pos 215)] :=
  (lex_7_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3440), (Sat.Literal.pos 235), (Sat.Literal.neg 215)] :=
  (lex_7_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3439), (Sat.Literal.neg 235), (Sat.Literal.neg 215), (Sat.Literal.pos 3440)] :=
  (lex_7_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3439), (Sat.Literal.pos 235), (Sat.Literal.pos 215), (Sat.Literal.pos 3440)] :=
  (lex_7_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3440) = lexBefore s permutation7 234 := by
  exact (positive_lex_of_descriptor s 3440 permutation7 235 (by rfl)).trans ((lex_skipped s permutation7 234 235 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation7 234) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation7 234 by rw [image7_eq]; rfl))

theorem lex_7_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3441) (Sat.Literal.pos 3440) (Sat.Literal.pos 234) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation7 234 (assignment s)
    (Sat.Literal.pos 3441) (Sat.Literal.pos 3440) (Sat.Literal.pos 234) (Sat.Literal.pos 213) (positive_of_descriptor s 3441 (.lex permutation7 234) (by rfl)) (lex_7_234_prefix s) (positive_select s 234) (lex_7_234_image s)

theorem lex_7_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3440), (Sat.Literal.pos 234), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation7 234 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3440) (Sat.Literal.pos 234) (Sat.Literal.pos 213) (lex_7_234_prefix s) (positive_select s 234) (lex_7_234_image s)

theorem lex_7_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3441), (Sat.Literal.pos 3440)] :=
  (lex_7_234_gate s).prop _ (List.Mem.head _)

theorem lex_7_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3441), (Sat.Literal.neg 234), (Sat.Literal.pos 213)] :=
  (lex_7_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3441), (Sat.Literal.pos 234), (Sat.Literal.neg 213)] :=
  (lex_7_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3440), (Sat.Literal.neg 234), (Sat.Literal.neg 213), (Sat.Literal.pos 3441)] :=
  (lex_7_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3440), (Sat.Literal.pos 234), (Sat.Literal.pos 213), (Sat.Literal.pos 3441)] :=
  (lex_7_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3441) = lexBefore s permutation7 233 := by
  exact (positive_lex_of_descriptor s 3441 permutation7 234 (by rfl)).trans ((lex_skipped s permutation7 233 234 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation7 233) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation7 233 by rw [image7_eq]; rfl))

theorem lex_7_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3442) (Sat.Literal.pos 3441) (Sat.Literal.pos 233) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation7 233 (assignment s)
    (Sat.Literal.pos 3442) (Sat.Literal.pos 3441) (Sat.Literal.pos 233) (Sat.Literal.pos 211) (positive_of_descriptor s 3442 (.lex permutation7 233) (by rfl)) (lex_7_233_prefix s) (positive_select s 233) (lex_7_233_image s)

theorem lex_7_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3441), (Sat.Literal.pos 233), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation7 233 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3441) (Sat.Literal.pos 233) (Sat.Literal.pos 211) (lex_7_233_prefix s) (positive_select s 233) (lex_7_233_image s)

theorem lex_7_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3442), (Sat.Literal.pos 3441)] :=
  (lex_7_233_gate s).prop _ (List.Mem.head _)

theorem lex_7_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3442), (Sat.Literal.neg 233), (Sat.Literal.pos 211)] :=
  (lex_7_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3442), (Sat.Literal.pos 233), (Sat.Literal.neg 211)] :=
  (lex_7_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3441), (Sat.Literal.neg 233), (Sat.Literal.neg 211), (Sat.Literal.pos 3442)] :=
  (lex_7_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3441), (Sat.Literal.pos 233), (Sat.Literal.pos 211), (Sat.Literal.pos 3442)] :=
  (lex_7_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3442) = lexBefore s permutation7 232 := by
  exact (positive_lex_of_descriptor s 3442 permutation7 233 (by rfl)).trans ((lex_skipped s permutation7 232 233 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 209) = s (permuteMask permutation7 232) := by
  exact (positive_select s 209).trans (congrArg s (show (209 : Fin 256) = permuteMask permutation7 232 by rw [image7_eq]; rfl))

theorem lex_7_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3443) (Sat.Literal.pos 3442) (Sat.Literal.pos 232) (Sat.Literal.pos 209)) := by
  exact equality_gate s permutation7 232 (assignment s)
    (Sat.Literal.pos 3443) (Sat.Literal.pos 3442) (Sat.Literal.pos 232) (Sat.Literal.pos 209) (positive_of_descriptor s 3443 (.lex permutation7 232) (by rfl)) (lex_7_232_prefix s) (positive_select s 232) (lex_7_232_image s)

theorem lex_7_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3442), (Sat.Literal.pos 232), (Sat.Literal.neg 209)] := by
  exact comparison_gate s permutation7 232 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3442) (Sat.Literal.pos 232) (Sat.Literal.pos 209) (lex_7_232_prefix s) (positive_select s 232) (lex_7_232_image s)

theorem lex_7_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3443), (Sat.Literal.pos 3442)] :=
  (lex_7_232_gate s).prop _ (List.Mem.head _)

theorem lex_7_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3443), (Sat.Literal.neg 232), (Sat.Literal.pos 209)] :=
  (lex_7_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3443), (Sat.Literal.pos 232), (Sat.Literal.neg 209)] :=
  (lex_7_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3442), (Sat.Literal.neg 232), (Sat.Literal.neg 209), (Sat.Literal.pos 3443)] :=
  (lex_7_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3442), (Sat.Literal.pos 232), (Sat.Literal.pos 209), (Sat.Literal.pos 3443)] :=
  (lex_7_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3443) = lexBefore s permutation7 231 := by
  exact (positive_lex_of_descriptor s 3443 permutation7 232 (by rfl)).trans ((lex_skipped s permutation7 231 232 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 207) = s (permuteMask permutation7 231) := by
  exact (positive_select s 207).trans (congrArg s (show (207 : Fin 256) = permuteMask permutation7 231 by rw [image7_eq]; rfl))

theorem lex_7_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3444) (Sat.Literal.pos 3443) (Sat.Literal.pos 231) (Sat.Literal.pos 207)) := by
  exact equality_gate s permutation7 231 (assignment s)
    (Sat.Literal.pos 3444) (Sat.Literal.pos 3443) (Sat.Literal.pos 231) (Sat.Literal.pos 207) (positive_of_descriptor s 3444 (.lex permutation7 231) (by rfl)) (lex_7_231_prefix s) (positive_select s 231) (lex_7_231_image s)

theorem lex_7_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3443), (Sat.Literal.pos 231), (Sat.Literal.neg 207)] := by
  exact comparison_gate s permutation7 231 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3443) (Sat.Literal.pos 231) (Sat.Literal.pos 207) (lex_7_231_prefix s) (positive_select s 231) (lex_7_231_image s)

theorem lex_7_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3444), (Sat.Literal.pos 3443)] :=
  (lex_7_231_gate s).prop _ (List.Mem.head _)

theorem lex_7_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3444), (Sat.Literal.neg 231), (Sat.Literal.pos 207)] :=
  (lex_7_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3444), (Sat.Literal.pos 231), (Sat.Literal.neg 207)] :=
  (lex_7_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3443), (Sat.Literal.neg 231), (Sat.Literal.neg 207), (Sat.Literal.pos 3444)] :=
  (lex_7_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3443), (Sat.Literal.pos 231), (Sat.Literal.pos 207), (Sat.Literal.pos 3444)] :=
  (lex_7_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3444) = lexBefore s permutation7 230 := by
  exact (positive_lex_of_descriptor s 3444 permutation7 231 (by rfl)).trans ((lex_skipped s permutation7 230 231 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 205) = s (permuteMask permutation7 230) := by
  exact (positive_select s 205).trans (congrArg s (show (205 : Fin 256) = permuteMask permutation7 230 by rw [image7_eq]; rfl))

theorem lex_7_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3445) (Sat.Literal.pos 3444) (Sat.Literal.pos 230) (Sat.Literal.pos 205)) := by
  exact equality_gate s permutation7 230 (assignment s)
    (Sat.Literal.pos 3445) (Sat.Literal.pos 3444) (Sat.Literal.pos 230) (Sat.Literal.pos 205) (positive_of_descriptor s 3445 (.lex permutation7 230) (by rfl)) (lex_7_230_prefix s) (positive_select s 230) (lex_7_230_image s)

theorem lex_7_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3444), (Sat.Literal.pos 230), (Sat.Literal.neg 205)] := by
  exact comparison_gate s permutation7 230 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3444) (Sat.Literal.pos 230) (Sat.Literal.pos 205) (lex_7_230_prefix s) (positive_select s 230) (lex_7_230_image s)

theorem lex_7_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3445), (Sat.Literal.pos 3444)] :=
  (lex_7_230_gate s).prop _ (List.Mem.head _)

theorem lex_7_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3445), (Sat.Literal.neg 230), (Sat.Literal.pos 205)] :=
  (lex_7_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3445), (Sat.Literal.pos 230), (Sat.Literal.neg 205)] :=
  (lex_7_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3444), (Sat.Literal.neg 230), (Sat.Literal.neg 205), (Sat.Literal.pos 3445)] :=
  (lex_7_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3444), (Sat.Literal.pos 230), (Sat.Literal.pos 205), (Sat.Literal.pos 3445)] :=
  (lex_7_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3445) = lexBefore s permutation7 229 := by
  exact (positive_lex_of_descriptor s 3445 permutation7 230 (by rfl)).trans ((lex_skipped s permutation7 229 230 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 203) = s (permuteMask permutation7 229) := by
  exact (positive_select s 203).trans (congrArg s (show (203 : Fin 256) = permuteMask permutation7 229 by rw [image7_eq]; rfl))

theorem lex_7_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3446) (Sat.Literal.pos 3445) (Sat.Literal.pos 229) (Sat.Literal.pos 203)) := by
  exact equality_gate s permutation7 229 (assignment s)
    (Sat.Literal.pos 3446) (Sat.Literal.pos 3445) (Sat.Literal.pos 229) (Sat.Literal.pos 203) (positive_of_descriptor s 3446 (.lex permutation7 229) (by rfl)) (lex_7_229_prefix s) (positive_select s 229) (lex_7_229_image s)

theorem lex_7_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3445), (Sat.Literal.pos 229), (Sat.Literal.neg 203)] := by
  exact comparison_gate s permutation7 229 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3445) (Sat.Literal.pos 229) (Sat.Literal.pos 203) (lex_7_229_prefix s) (positive_select s 229) (lex_7_229_image s)

theorem lex_7_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3446), (Sat.Literal.pos 3445)] :=
  (lex_7_229_gate s).prop _ (List.Mem.head _)

theorem lex_7_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3446), (Sat.Literal.neg 229), (Sat.Literal.pos 203)] :=
  (lex_7_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3446), (Sat.Literal.pos 229), (Sat.Literal.neg 203)] :=
  (lex_7_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3445), (Sat.Literal.neg 229), (Sat.Literal.neg 203), (Sat.Literal.pos 3446)] :=
  (lex_7_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3445), (Sat.Literal.pos 229), (Sat.Literal.pos 203), (Sat.Literal.pos 3446)] :=
  (lex_7_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3446) = lexBefore s permutation7 228 := by
  exact (positive_lex_of_descriptor s 3446 permutation7 229 (by rfl)).trans ((lex_skipped s permutation7 228 229 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 201) = s (permuteMask permutation7 228) := by
  exact (positive_select s 201).trans (congrArg s (show (201 : Fin 256) = permuteMask permutation7 228 by rw [image7_eq]; rfl))

theorem lex_7_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3447) (Sat.Literal.pos 3446) (Sat.Literal.pos 228) (Sat.Literal.pos 201)) := by
  exact equality_gate s permutation7 228 (assignment s)
    (Sat.Literal.pos 3447) (Sat.Literal.pos 3446) (Sat.Literal.pos 228) (Sat.Literal.pos 201) (positive_of_descriptor s 3447 (.lex permutation7 228) (by rfl)) (lex_7_228_prefix s) (positive_select s 228) (lex_7_228_image s)

theorem lex_7_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3446), (Sat.Literal.pos 228), (Sat.Literal.neg 201)] := by
  exact comparison_gate s permutation7 228 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3446) (Sat.Literal.pos 228) (Sat.Literal.pos 201) (lex_7_228_prefix s) (positive_select s 228) (lex_7_228_image s)

theorem lex_7_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3447), (Sat.Literal.pos 3446)] :=
  (lex_7_228_gate s).prop _ (List.Mem.head _)

theorem lex_7_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3447), (Sat.Literal.neg 228), (Sat.Literal.pos 201)] :=
  (lex_7_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3447), (Sat.Literal.pos 228), (Sat.Literal.neg 201)] :=
  (lex_7_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3446), (Sat.Literal.neg 228), (Sat.Literal.neg 201), (Sat.Literal.pos 3447)] :=
  (lex_7_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3446), (Sat.Literal.pos 228), (Sat.Literal.pos 201), (Sat.Literal.pos 3447)] :=
  (lex_7_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3447) = lexBefore s permutation7 227 := by
  exact (positive_lex_of_descriptor s 3447 permutation7 228 (by rfl)).trans ((lex_skipped s permutation7 227 228 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 199) = s (permuteMask permutation7 227) := by
  exact (positive_select s 199).trans (congrArg s (show (199 : Fin 256) = permuteMask permutation7 227 by rw [image7_eq]; rfl))

theorem lex_7_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3448) (Sat.Literal.pos 3447) (Sat.Literal.pos 227) (Sat.Literal.pos 199)) := by
  exact equality_gate s permutation7 227 (assignment s)
    (Sat.Literal.pos 3448) (Sat.Literal.pos 3447) (Sat.Literal.pos 227) (Sat.Literal.pos 199) (positive_of_descriptor s 3448 (.lex permutation7 227) (by rfl)) (lex_7_227_prefix s) (positive_select s 227) (lex_7_227_image s)

theorem lex_7_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3447), (Sat.Literal.pos 227), (Sat.Literal.neg 199)] := by
  exact comparison_gate s permutation7 227 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3447) (Sat.Literal.pos 227) (Sat.Literal.pos 199) (lex_7_227_prefix s) (positive_select s 227) (lex_7_227_image s)

theorem lex_7_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3448), (Sat.Literal.pos 3447)] :=
  (lex_7_227_gate s).prop _ (List.Mem.head _)

theorem lex_7_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3448), (Sat.Literal.neg 227), (Sat.Literal.pos 199)] :=
  (lex_7_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3448), (Sat.Literal.pos 227), (Sat.Literal.neg 199)] :=
  (lex_7_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3447), (Sat.Literal.neg 227), (Sat.Literal.neg 199), (Sat.Literal.pos 3448)] :=
  (lex_7_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3447), (Sat.Literal.pos 227), (Sat.Literal.pos 199), (Sat.Literal.pos 3448)] :=
  (lex_7_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3448) = lexBefore s permutation7 226 := by
  exact (positive_lex_of_descriptor s 3448 permutation7 227 (by rfl)).trans ((lex_skipped s permutation7 226 227 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 197) = s (permuteMask permutation7 226) := by
  exact (positive_select s 197).trans (congrArg s (show (197 : Fin 256) = permuteMask permutation7 226 by rw [image7_eq]; rfl))

theorem lex_7_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3449) (Sat.Literal.pos 3448) (Sat.Literal.pos 226) (Sat.Literal.pos 197)) := by
  exact equality_gate s permutation7 226 (assignment s)
    (Sat.Literal.pos 3449) (Sat.Literal.pos 3448) (Sat.Literal.pos 226) (Sat.Literal.pos 197) (positive_of_descriptor s 3449 (.lex permutation7 226) (by rfl)) (lex_7_226_prefix s) (positive_select s 226) (lex_7_226_image s)

theorem lex_7_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3448), (Sat.Literal.pos 226), (Sat.Literal.neg 197)] := by
  exact comparison_gate s permutation7 226 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3448) (Sat.Literal.pos 226) (Sat.Literal.pos 197) (lex_7_226_prefix s) (positive_select s 226) (lex_7_226_image s)

theorem lex_7_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3449), (Sat.Literal.pos 3448)] :=
  (lex_7_226_gate s).prop _ (List.Mem.head _)

theorem lex_7_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3449), (Sat.Literal.neg 226), (Sat.Literal.pos 197)] :=
  (lex_7_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3449), (Sat.Literal.pos 226), (Sat.Literal.neg 197)] :=
  (lex_7_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3448), (Sat.Literal.neg 226), (Sat.Literal.neg 197), (Sat.Literal.pos 3449)] :=
  (lex_7_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3448), (Sat.Literal.pos 226), (Sat.Literal.pos 197), (Sat.Literal.pos 3449)] :=
  (lex_7_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3449) = lexBefore s permutation7 225 := by
  exact (positive_lex_of_descriptor s 3449 permutation7 226 (by rfl)).trans ((lex_skipped s permutation7 225 226 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 195) = s (permuteMask permutation7 225) := by
  exact (positive_select s 195).trans (congrArg s (show (195 : Fin 256) = permuteMask permutation7 225 by rw [image7_eq]; rfl))

theorem lex_7_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3450) (Sat.Literal.pos 3449) (Sat.Literal.pos 225) (Sat.Literal.pos 195)) := by
  exact equality_gate s permutation7 225 (assignment s)
    (Sat.Literal.pos 3450) (Sat.Literal.pos 3449) (Sat.Literal.pos 225) (Sat.Literal.pos 195) (positive_of_descriptor s 3450 (.lex permutation7 225) (by rfl)) (lex_7_225_prefix s) (positive_select s 225) (lex_7_225_image s)

theorem lex_7_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3449), (Sat.Literal.pos 225), (Sat.Literal.neg 195)] := by
  exact comparison_gate s permutation7 225 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3449) (Sat.Literal.pos 225) (Sat.Literal.pos 195) (lex_7_225_prefix s) (positive_select s 225) (lex_7_225_image s)

theorem lex_7_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3450), (Sat.Literal.pos 3449)] :=
  (lex_7_225_gate s).prop _ (List.Mem.head _)

theorem lex_7_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3450), (Sat.Literal.neg 225), (Sat.Literal.pos 195)] :=
  (lex_7_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3450), (Sat.Literal.pos 225), (Sat.Literal.neg 195)] :=
  (lex_7_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3449), (Sat.Literal.neg 225), (Sat.Literal.neg 195), (Sat.Literal.pos 3450)] :=
  (lex_7_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3449), (Sat.Literal.pos 225), (Sat.Literal.pos 195), (Sat.Literal.pos 3450)] :=
  (lex_7_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3450) = lexBefore s permutation7 224 := by
  exact (positive_lex_of_descriptor s 3450 permutation7 225 (by rfl)).trans ((lex_skipped s permutation7 224 225 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 193) = s (permuteMask permutation7 224) := by
  exact (positive_select s 193).trans (congrArg s (show (193 : Fin 256) = permuteMask permutation7 224 by rw [image7_eq]; rfl))

theorem lex_7_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3451) (Sat.Literal.pos 3450) (Sat.Literal.pos 224) (Sat.Literal.pos 193)) := by
  exact equality_gate s permutation7 224 (assignment s)
    (Sat.Literal.pos 3451) (Sat.Literal.pos 3450) (Sat.Literal.pos 224) (Sat.Literal.pos 193) (positive_of_descriptor s 3451 (.lex permutation7 224) (by rfl)) (lex_7_224_prefix s) (positive_select s 224) (lex_7_224_image s)

theorem lex_7_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3450), (Sat.Literal.pos 224), (Sat.Literal.neg 193)] := by
  exact comparison_gate s permutation7 224 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3450) (Sat.Literal.pos 224) (Sat.Literal.pos 193) (lex_7_224_prefix s) (positive_select s 224) (lex_7_224_image s)

theorem lex_7_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3451), (Sat.Literal.pos 3450)] :=
  (lex_7_224_gate s).prop _ (List.Mem.head _)

theorem lex_7_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3451), (Sat.Literal.neg 224), (Sat.Literal.pos 193)] :=
  (lex_7_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3451), (Sat.Literal.pos 224), (Sat.Literal.neg 193)] :=
  (lex_7_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3450), (Sat.Literal.neg 224), (Sat.Literal.neg 193), (Sat.Literal.pos 3451)] :=
  (lex_7_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3450), (Sat.Literal.pos 224), (Sat.Literal.pos 193), (Sat.Literal.pos 3451)] :=
  (lex_7_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3451) = lexBefore s permutation7 223 := by
  exact (positive_lex_of_descriptor s 3451 permutation7 224 (by rfl)).trans ((lex_skipped s permutation7 223 224 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation7 223) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation7 223 by rw [image7_eq]; rfl))

theorem lex_7_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3452) (Sat.Literal.pos 3451) (Sat.Literal.pos 223) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation7 223 (assignment s)
    (Sat.Literal.pos 3452) (Sat.Literal.pos 3451) (Sat.Literal.pos 223) (Sat.Literal.pos 191) (positive_of_descriptor s 3452 (.lex permutation7 223) (by rfl)) (lex_7_223_prefix s) (positive_select s 223) (lex_7_223_image s)

theorem lex_7_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3451), (Sat.Literal.pos 223), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation7 223 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3451) (Sat.Literal.pos 223) (Sat.Literal.pos 191) (lex_7_223_prefix s) (positive_select s 223) (lex_7_223_image s)

theorem lex_7_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3452), (Sat.Literal.pos 3451)] :=
  (lex_7_223_gate s).prop _ (List.Mem.head _)

theorem lex_7_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3452), (Sat.Literal.neg 223), (Sat.Literal.pos 191)] :=
  (lex_7_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3452), (Sat.Literal.pos 223), (Sat.Literal.neg 191)] :=
  (lex_7_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3451), (Sat.Literal.neg 223), (Sat.Literal.neg 191), (Sat.Literal.pos 3452)] :=
  (lex_7_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3451), (Sat.Literal.pos 223), (Sat.Literal.pos 191), (Sat.Literal.pos 3452)] :=
  (lex_7_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3452) = lexBefore s permutation7 222 := by
  exact (positive_lex_of_descriptor s 3452 permutation7 223 (by rfl)).trans ((lex_skipped s permutation7 222 223 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation7 222) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation7 222 by rw [image7_eq]; rfl))

theorem lex_7_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3453) (Sat.Literal.pos 3452) (Sat.Literal.pos 222) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation7 222 (assignment s)
    (Sat.Literal.pos 3453) (Sat.Literal.pos 3452) (Sat.Literal.pos 222) (Sat.Literal.pos 189) (positive_of_descriptor s 3453 (.lex permutation7 222) (by rfl)) (lex_7_222_prefix s) (positive_select s 222) (lex_7_222_image s)

theorem lex_7_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3452), (Sat.Literal.pos 222), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation7 222 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3452) (Sat.Literal.pos 222) (Sat.Literal.pos 189) (lex_7_222_prefix s) (positive_select s 222) (lex_7_222_image s)

theorem lex_7_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3453), (Sat.Literal.pos 3452)] :=
  (lex_7_222_gate s).prop _ (List.Mem.head _)

theorem lex_7_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3453), (Sat.Literal.neg 222), (Sat.Literal.pos 189)] :=
  (lex_7_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3453), (Sat.Literal.pos 222), (Sat.Literal.neg 189)] :=
  (lex_7_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3452), (Sat.Literal.neg 222), (Sat.Literal.neg 189), (Sat.Literal.pos 3453)] :=
  (lex_7_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3452), (Sat.Literal.pos 222), (Sat.Literal.pos 189), (Sat.Literal.pos 3453)] :=
  (lex_7_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3453) = lexBefore s permutation7 221 := by
  exact (positive_lex_of_descriptor s 3453 permutation7 222 (by rfl)).trans ((lex_skipped s permutation7 221 222 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation7 221) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation7 221 by rw [image7_eq]; rfl))

theorem lex_7_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3454) (Sat.Literal.pos 3453) (Sat.Literal.pos 221) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation7 221 (assignment s)
    (Sat.Literal.pos 3454) (Sat.Literal.pos 3453) (Sat.Literal.pos 221) (Sat.Literal.pos 187) (positive_of_descriptor s 3454 (.lex permutation7 221) (by rfl)) (lex_7_221_prefix s) (positive_select s 221) (lex_7_221_image s)

theorem lex_7_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3453), (Sat.Literal.pos 221), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation7 221 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3453) (Sat.Literal.pos 221) (Sat.Literal.pos 187) (lex_7_221_prefix s) (positive_select s 221) (lex_7_221_image s)

theorem lex_7_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3454), (Sat.Literal.pos 3453)] :=
  (lex_7_221_gate s).prop _ (List.Mem.head _)

theorem lex_7_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3454), (Sat.Literal.neg 221), (Sat.Literal.pos 187)] :=
  (lex_7_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3454), (Sat.Literal.pos 221), (Sat.Literal.neg 187)] :=
  (lex_7_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3453), (Sat.Literal.neg 221), (Sat.Literal.neg 187), (Sat.Literal.pos 3454)] :=
  (lex_7_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3453), (Sat.Literal.pos 221), (Sat.Literal.pos 187), (Sat.Literal.pos 3454)] :=
  (lex_7_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3454) = lexBefore s permutation7 220 := by
  exact (positive_lex_of_descriptor s 3454 permutation7 221 (by rfl)).trans ((lex_skipped s permutation7 220 221 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation7 220) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation7 220 by rw [image7_eq]; rfl))

theorem lex_7_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3455) (Sat.Literal.pos 3454) (Sat.Literal.pos 220) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation7 220 (assignment s)
    (Sat.Literal.pos 3455) (Sat.Literal.pos 3454) (Sat.Literal.pos 220) (Sat.Literal.pos 185) (positive_of_descriptor s 3455 (.lex permutation7 220) (by rfl)) (lex_7_220_prefix s) (positive_select s 220) (lex_7_220_image s)

theorem lex_7_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3454), (Sat.Literal.pos 220), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation7 220 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3454) (Sat.Literal.pos 220) (Sat.Literal.pos 185) (lex_7_220_prefix s) (positive_select s 220) (lex_7_220_image s)

theorem lex_7_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3455), (Sat.Literal.pos 3454)] :=
  (lex_7_220_gate s).prop _ (List.Mem.head _)

theorem lex_7_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3455), (Sat.Literal.neg 220), (Sat.Literal.pos 185)] :=
  (lex_7_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3455), (Sat.Literal.pos 220), (Sat.Literal.neg 185)] :=
  (lex_7_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3454), (Sat.Literal.neg 220), (Sat.Literal.neg 185), (Sat.Literal.pos 3455)] :=
  (lex_7_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3454), (Sat.Literal.pos 220), (Sat.Literal.pos 185), (Sat.Literal.pos 3455)] :=
  (lex_7_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3455) = lexBefore s permutation7 219 := by
  exact (positive_lex_of_descriptor s 3455 permutation7 220 (by rfl)).trans ((lex_skipped s permutation7 219 220 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation7 219) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation7 219 by rw [image7_eq]; rfl))

theorem lex_7_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3456) (Sat.Literal.pos 3455) (Sat.Literal.pos 219) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation7 219 (assignment s)
    (Sat.Literal.pos 3456) (Sat.Literal.pos 3455) (Sat.Literal.pos 219) (Sat.Literal.pos 183) (positive_of_descriptor s 3456 (.lex permutation7 219) (by rfl)) (lex_7_219_prefix s) (positive_select s 219) (lex_7_219_image s)

theorem lex_7_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3455), (Sat.Literal.pos 219), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation7 219 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3455) (Sat.Literal.pos 219) (Sat.Literal.pos 183) (lex_7_219_prefix s) (positive_select s 219) (lex_7_219_image s)

theorem lex_7_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3456), (Sat.Literal.pos 3455)] :=
  (lex_7_219_gate s).prop _ (List.Mem.head _)

theorem lex_7_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3456), (Sat.Literal.neg 219), (Sat.Literal.pos 183)] :=
  (lex_7_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3456), (Sat.Literal.pos 219), (Sat.Literal.neg 183)] :=
  (lex_7_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3455), (Sat.Literal.neg 219), (Sat.Literal.neg 183), (Sat.Literal.pos 3456)] :=
  (lex_7_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3455), (Sat.Literal.pos 219), (Sat.Literal.pos 183), (Sat.Literal.pos 3456)] :=
  (lex_7_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3456) = lexBefore s permutation7 218 := by
  exact (positive_lex_of_descriptor s 3456 permutation7 219 (by rfl)).trans ((lex_skipped s permutation7 218 219 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation7 218) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation7 218 by rw [image7_eq]; rfl))

theorem lex_7_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3457) (Sat.Literal.pos 3456) (Sat.Literal.pos 218) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation7 218 (assignment s)
    (Sat.Literal.pos 3457) (Sat.Literal.pos 3456) (Sat.Literal.pos 218) (Sat.Literal.pos 181) (positive_of_descriptor s 3457 (.lex permutation7 218) (by rfl)) (lex_7_218_prefix s) (positive_select s 218) (lex_7_218_image s)

theorem lex_7_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3456), (Sat.Literal.pos 218), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation7 218 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3456) (Sat.Literal.pos 218) (Sat.Literal.pos 181) (lex_7_218_prefix s) (positive_select s 218) (lex_7_218_image s)

theorem lex_7_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3457), (Sat.Literal.pos 3456)] :=
  (lex_7_218_gate s).prop _ (List.Mem.head _)

theorem lex_7_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3457), (Sat.Literal.neg 218), (Sat.Literal.pos 181)] :=
  (lex_7_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3457), (Sat.Literal.pos 218), (Sat.Literal.neg 181)] :=
  (lex_7_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3456), (Sat.Literal.neg 218), (Sat.Literal.neg 181), (Sat.Literal.pos 3457)] :=
  (lex_7_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3456), (Sat.Literal.pos 218), (Sat.Literal.pos 181), (Sat.Literal.pos 3457)] :=
  (lex_7_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3457) = lexBefore s permutation7 217 := by
  exact (positive_lex_of_descriptor s 3457 permutation7 218 (by rfl)).trans ((lex_skipped s permutation7 217 218 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation7 217) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation7 217 by rw [image7_eq]; rfl))

theorem lex_7_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3458) (Sat.Literal.pos 3457) (Sat.Literal.pos 217) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation7 217 (assignment s)
    (Sat.Literal.pos 3458) (Sat.Literal.pos 3457) (Sat.Literal.pos 217) (Sat.Literal.pos 179) (positive_of_descriptor s 3458 (.lex permutation7 217) (by rfl)) (lex_7_217_prefix s) (positive_select s 217) (lex_7_217_image s)

theorem lex_7_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3457), (Sat.Literal.pos 217), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation7 217 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3457) (Sat.Literal.pos 217) (Sat.Literal.pos 179) (lex_7_217_prefix s) (positive_select s 217) (lex_7_217_image s)

theorem lex_7_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3458), (Sat.Literal.pos 3457)] :=
  (lex_7_217_gate s).prop _ (List.Mem.head _)

theorem lex_7_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3458), (Sat.Literal.neg 217), (Sat.Literal.pos 179)] :=
  (lex_7_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3458), (Sat.Literal.pos 217), (Sat.Literal.neg 179)] :=
  (lex_7_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3457), (Sat.Literal.neg 217), (Sat.Literal.neg 179), (Sat.Literal.pos 3458)] :=
  (lex_7_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3457), (Sat.Literal.pos 217), (Sat.Literal.pos 179), (Sat.Literal.pos 3458)] :=
  (lex_7_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3458) = lexBefore s permutation7 216 := by
  exact (positive_lex_of_descriptor s 3458 permutation7 217 (by rfl)).trans ((lex_skipped s permutation7 216 217 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation7 216) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation7 216 by rw [image7_eq]; rfl))

theorem lex_7_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3459) (Sat.Literal.pos 3458) (Sat.Literal.pos 216) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation7 216 (assignment s)
    (Sat.Literal.pos 3459) (Sat.Literal.pos 3458) (Sat.Literal.pos 216) (Sat.Literal.pos 177) (positive_of_descriptor s 3459 (.lex permutation7 216) (by rfl)) (lex_7_216_prefix s) (positive_select s 216) (lex_7_216_image s)

theorem lex_7_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3458), (Sat.Literal.pos 216), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation7 216 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3458) (Sat.Literal.pos 216) (Sat.Literal.pos 177) (lex_7_216_prefix s) (positive_select s 216) (lex_7_216_image s)

theorem lex_7_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3459), (Sat.Literal.pos 3458)] :=
  (lex_7_216_gate s).prop _ (List.Mem.head _)

theorem lex_7_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3459), (Sat.Literal.neg 216), (Sat.Literal.pos 177)] :=
  (lex_7_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3459), (Sat.Literal.pos 216), (Sat.Literal.neg 177)] :=
  (lex_7_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3458), (Sat.Literal.neg 216), (Sat.Literal.neg 177), (Sat.Literal.pos 3459)] :=
  (lex_7_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3458), (Sat.Literal.pos 216), (Sat.Literal.pos 177), (Sat.Literal.pos 3459)] :=
  (lex_7_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3459) = lexBefore s permutation7 215 := by
  exact (positive_lex_of_descriptor s 3459 permutation7 216 (by rfl)).trans ((lex_skipped s permutation7 215 216 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation7 215) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation7 215 by rw [image7_eq]; rfl))

theorem lex_7_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3460) (Sat.Literal.pos 3459) (Sat.Literal.pos 215) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation7 215 (assignment s)
    (Sat.Literal.pos 3460) (Sat.Literal.pos 3459) (Sat.Literal.pos 215) (Sat.Literal.pos 175) (positive_of_descriptor s 3460 (.lex permutation7 215) (by rfl)) (lex_7_215_prefix s) (positive_select s 215) (lex_7_215_image s)

theorem lex_7_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3459), (Sat.Literal.pos 215), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation7 215 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3459) (Sat.Literal.pos 215) (Sat.Literal.pos 175) (lex_7_215_prefix s) (positive_select s 215) (lex_7_215_image s)

theorem lex_7_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3460), (Sat.Literal.pos 3459)] :=
  (lex_7_215_gate s).prop _ (List.Mem.head _)

theorem lex_7_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3460), (Sat.Literal.neg 215), (Sat.Literal.pos 175)] :=
  (lex_7_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3460), (Sat.Literal.pos 215), (Sat.Literal.neg 175)] :=
  (lex_7_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3459), (Sat.Literal.neg 215), (Sat.Literal.neg 175), (Sat.Literal.pos 3460)] :=
  (lex_7_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3459), (Sat.Literal.pos 215), (Sat.Literal.pos 175), (Sat.Literal.pos 3460)] :=
  (lex_7_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3460) = lexBefore s permutation7 214 := by
  exact (positive_lex_of_descriptor s 3460 permutation7 215 (by rfl)).trans ((lex_skipped s permutation7 214 215 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation7 214) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation7 214 by rw [image7_eq]; rfl))

theorem lex_7_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3461) (Sat.Literal.pos 3460) (Sat.Literal.pos 214) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation7 214 (assignment s)
    (Sat.Literal.pos 3461) (Sat.Literal.pos 3460) (Sat.Literal.pos 214) (Sat.Literal.pos 173) (positive_of_descriptor s 3461 (.lex permutation7 214) (by rfl)) (lex_7_214_prefix s) (positive_select s 214) (lex_7_214_image s)

theorem lex_7_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3460), (Sat.Literal.pos 214), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation7 214 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3460) (Sat.Literal.pos 214) (Sat.Literal.pos 173) (lex_7_214_prefix s) (positive_select s 214) (lex_7_214_image s)

theorem lex_7_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3461), (Sat.Literal.pos 3460)] :=
  (lex_7_214_gate s).prop _ (List.Mem.head _)

theorem lex_7_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3461), (Sat.Literal.neg 214), (Sat.Literal.pos 173)] :=
  (lex_7_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3461), (Sat.Literal.pos 214), (Sat.Literal.neg 173)] :=
  (lex_7_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3460), (Sat.Literal.neg 214), (Sat.Literal.neg 173), (Sat.Literal.pos 3461)] :=
  (lex_7_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3460), (Sat.Literal.pos 214), (Sat.Literal.pos 173), (Sat.Literal.pos 3461)] :=
  (lex_7_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3461) = lexBefore s permutation7 213 := by
  exact (positive_lex_of_descriptor s 3461 permutation7 214 (by rfl)).trans ((lex_skipped s permutation7 213 214 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation7 213) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation7 213 by rw [image7_eq]; rfl))

theorem lex_7_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3462) (Sat.Literal.pos 3461) (Sat.Literal.pos 213) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation7 213 (assignment s)
    (Sat.Literal.pos 3462) (Sat.Literal.pos 3461) (Sat.Literal.pos 213) (Sat.Literal.pos 171) (positive_of_descriptor s 3462 (.lex permutation7 213) (by rfl)) (lex_7_213_prefix s) (positive_select s 213) (lex_7_213_image s)

theorem lex_7_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3461), (Sat.Literal.pos 213), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation7 213 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3461) (Sat.Literal.pos 213) (Sat.Literal.pos 171) (lex_7_213_prefix s) (positive_select s 213) (lex_7_213_image s)

theorem lex_7_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3462), (Sat.Literal.pos 3461)] :=
  (lex_7_213_gate s).prop _ (List.Mem.head _)

theorem lex_7_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3462), (Sat.Literal.neg 213), (Sat.Literal.pos 171)] :=
  (lex_7_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3462), (Sat.Literal.pos 213), (Sat.Literal.neg 171)] :=
  (lex_7_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3461), (Sat.Literal.neg 213), (Sat.Literal.neg 171), (Sat.Literal.pos 3462)] :=
  (lex_7_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3461), (Sat.Literal.pos 213), (Sat.Literal.pos 171), (Sat.Literal.pos 3462)] :=
  (lex_7_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3462) = lexBefore s permutation7 212 := by
  exact (positive_lex_of_descriptor s 3462 permutation7 213 (by rfl)).trans ((lex_skipped s permutation7 212 213 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation7 212) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation7 212 by rw [image7_eq]; rfl))

theorem lex_7_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3463) (Sat.Literal.pos 3462) (Sat.Literal.pos 212) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation7 212 (assignment s)
    (Sat.Literal.pos 3463) (Sat.Literal.pos 3462) (Sat.Literal.pos 212) (Sat.Literal.pos 169) (positive_of_descriptor s 3463 (.lex permutation7 212) (by rfl)) (lex_7_212_prefix s) (positive_select s 212) (lex_7_212_image s)

theorem lex_7_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3462), (Sat.Literal.pos 212), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation7 212 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3462) (Sat.Literal.pos 212) (Sat.Literal.pos 169) (lex_7_212_prefix s) (positive_select s 212) (lex_7_212_image s)

theorem lex_7_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3463), (Sat.Literal.pos 3462)] :=
  (lex_7_212_gate s).prop _ (List.Mem.head _)

theorem lex_7_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3463), (Sat.Literal.neg 212), (Sat.Literal.pos 169)] :=
  (lex_7_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3463), (Sat.Literal.pos 212), (Sat.Literal.neg 169)] :=
  (lex_7_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3462), (Sat.Literal.neg 212), (Sat.Literal.neg 169), (Sat.Literal.pos 3463)] :=
  (lex_7_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3462), (Sat.Literal.pos 212), (Sat.Literal.pos 169), (Sat.Literal.pos 3463)] :=
  (lex_7_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3463) = lexBefore s permutation7 211 := by
  exact (positive_lex_of_descriptor s 3463 permutation7 212 (by rfl)).trans ((lex_skipped s permutation7 211 212 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation7 211) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation7 211 by rw [image7_eq]; rfl))

theorem lex_7_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3464) (Sat.Literal.pos 3463) (Sat.Literal.pos 211) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation7 211 (assignment s)
    (Sat.Literal.pos 3464) (Sat.Literal.pos 3463) (Sat.Literal.pos 211) (Sat.Literal.pos 167) (positive_of_descriptor s 3464 (.lex permutation7 211) (by rfl)) (lex_7_211_prefix s) (positive_select s 211) (lex_7_211_image s)

theorem lex_7_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3463), (Sat.Literal.pos 211), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation7 211 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3463) (Sat.Literal.pos 211) (Sat.Literal.pos 167) (lex_7_211_prefix s) (positive_select s 211) (lex_7_211_image s)

theorem lex_7_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3464), (Sat.Literal.pos 3463)] :=
  (lex_7_211_gate s).prop _ (List.Mem.head _)

theorem lex_7_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3464), (Sat.Literal.neg 211), (Sat.Literal.pos 167)] :=
  (lex_7_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3464), (Sat.Literal.pos 211), (Sat.Literal.neg 167)] :=
  (lex_7_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3463), (Sat.Literal.neg 211), (Sat.Literal.neg 167), (Sat.Literal.pos 3464)] :=
  (lex_7_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3463), (Sat.Literal.pos 211), (Sat.Literal.pos 167), (Sat.Literal.pos 3464)] :=
  (lex_7_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3464) = lexBefore s permutation7 210 := by
  exact (positive_lex_of_descriptor s 3464 permutation7 211 (by rfl)).trans ((lex_skipped s permutation7 210 211 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation7 210) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation7 210 by rw [image7_eq]; rfl))

theorem lex_7_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3465) (Sat.Literal.pos 3464) (Sat.Literal.pos 210) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation7 210 (assignment s)
    (Sat.Literal.pos 3465) (Sat.Literal.pos 3464) (Sat.Literal.pos 210) (Sat.Literal.pos 165) (positive_of_descriptor s 3465 (.lex permutation7 210) (by rfl)) (lex_7_210_prefix s) (positive_select s 210) (lex_7_210_image s)

theorem lex_7_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3464), (Sat.Literal.pos 210), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation7 210 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3464) (Sat.Literal.pos 210) (Sat.Literal.pos 165) (lex_7_210_prefix s) (positive_select s 210) (lex_7_210_image s)

theorem lex_7_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3465), (Sat.Literal.pos 3464)] :=
  (lex_7_210_gate s).prop _ (List.Mem.head _)

theorem lex_7_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3465), (Sat.Literal.neg 210), (Sat.Literal.pos 165)] :=
  (lex_7_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3465), (Sat.Literal.pos 210), (Sat.Literal.neg 165)] :=
  (lex_7_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3464), (Sat.Literal.neg 210), (Sat.Literal.neg 165), (Sat.Literal.pos 3465)] :=
  (lex_7_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3464), (Sat.Literal.pos 210), (Sat.Literal.pos 165), (Sat.Literal.pos 3465)] :=
  (lex_7_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3465) = lexBefore s permutation7 209 := by
  exact (positive_lex_of_descriptor s 3465 permutation7 210 (by rfl)).trans ((lex_skipped s permutation7 209 210 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation7 209) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation7 209 by rw [image7_eq]; rfl))

theorem lex_7_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3466) (Sat.Literal.pos 3465) (Sat.Literal.pos 209) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation7 209 (assignment s)
    (Sat.Literal.pos 3466) (Sat.Literal.pos 3465) (Sat.Literal.pos 209) (Sat.Literal.pos 163) (positive_of_descriptor s 3466 (.lex permutation7 209) (by rfl)) (lex_7_209_prefix s) (positive_select s 209) (lex_7_209_image s)

theorem lex_7_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3465), (Sat.Literal.pos 209), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation7 209 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3465) (Sat.Literal.pos 209) (Sat.Literal.pos 163) (lex_7_209_prefix s) (positive_select s 209) (lex_7_209_image s)

theorem lex_7_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3466), (Sat.Literal.pos 3465)] :=
  (lex_7_209_gate s).prop _ (List.Mem.head _)

theorem lex_7_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3466), (Sat.Literal.neg 209), (Sat.Literal.pos 163)] :=
  (lex_7_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3466), (Sat.Literal.pos 209), (Sat.Literal.neg 163)] :=
  (lex_7_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3465), (Sat.Literal.neg 209), (Sat.Literal.neg 163), (Sat.Literal.pos 3466)] :=
  (lex_7_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3465), (Sat.Literal.pos 209), (Sat.Literal.pos 163), (Sat.Literal.pos 3466)] :=
  (lex_7_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3466) = lexBefore s permutation7 208 := by
  exact (positive_lex_of_descriptor s 3466 permutation7 209 (by rfl)).trans ((lex_skipped s permutation7 208 209 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation7 208) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation7 208 by rw [image7_eq]; rfl))

theorem lex_7_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3467) (Sat.Literal.pos 3466) (Sat.Literal.pos 208) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation7 208 (assignment s)
    (Sat.Literal.pos 3467) (Sat.Literal.pos 3466) (Sat.Literal.pos 208) (Sat.Literal.pos 161) (positive_of_descriptor s 3467 (.lex permutation7 208) (by rfl)) (lex_7_208_prefix s) (positive_select s 208) (lex_7_208_image s)

theorem lex_7_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3466), (Sat.Literal.pos 208), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation7 208 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3466) (Sat.Literal.pos 208) (Sat.Literal.pos 161) (lex_7_208_prefix s) (positive_select s 208) (lex_7_208_image s)

theorem lex_7_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3467), (Sat.Literal.pos 3466)] :=
  (lex_7_208_gate s).prop _ (List.Mem.head _)

theorem lex_7_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3467), (Sat.Literal.neg 208), (Sat.Literal.pos 161)] :=
  (lex_7_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3467), (Sat.Literal.pos 208), (Sat.Literal.neg 161)] :=
  (lex_7_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3466), (Sat.Literal.neg 208), (Sat.Literal.neg 161), (Sat.Literal.pos 3467)] :=
  (lex_7_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3466), (Sat.Literal.pos 208), (Sat.Literal.pos 161), (Sat.Literal.pos 3467)] :=
  (lex_7_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3467) = lexBefore s permutation7 207 := by
  exact (positive_lex_of_descriptor s 3467 permutation7 208 (by rfl)).trans ((lex_skipped s permutation7 207 208 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation7 207) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation7 207 by rw [image7_eq]; rfl))

theorem lex_7_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3468) (Sat.Literal.pos 3467) (Sat.Literal.pos 207) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation7 207 (assignment s)
    (Sat.Literal.pos 3468) (Sat.Literal.pos 3467) (Sat.Literal.pos 207) (Sat.Literal.pos 159) (positive_of_descriptor s 3468 (.lex permutation7 207) (by rfl)) (lex_7_207_prefix s) (positive_select s 207) (lex_7_207_image s)

theorem lex_7_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3467), (Sat.Literal.pos 207), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation7 207 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3467) (Sat.Literal.pos 207) (Sat.Literal.pos 159) (lex_7_207_prefix s) (positive_select s 207) (lex_7_207_image s)

theorem lex_7_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3468), (Sat.Literal.pos 3467)] :=
  (lex_7_207_gate s).prop _ (List.Mem.head _)

theorem lex_7_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3468), (Sat.Literal.neg 207), (Sat.Literal.pos 159)] :=
  (lex_7_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3468), (Sat.Literal.pos 207), (Sat.Literal.neg 159)] :=
  (lex_7_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3467), (Sat.Literal.neg 207), (Sat.Literal.neg 159), (Sat.Literal.pos 3468)] :=
  (lex_7_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3467), (Sat.Literal.pos 207), (Sat.Literal.pos 159), (Sat.Literal.pos 3468)] :=
  (lex_7_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3468) = lexBefore s permutation7 206 := by
  exact (positive_lex_of_descriptor s 3468 permutation7 207 (by rfl)).trans ((lex_skipped s permutation7 206 207 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation7 206) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation7 206 by rw [image7_eq]; rfl))

theorem lex_7_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3469) (Sat.Literal.pos 3468) (Sat.Literal.pos 206) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation7 206 (assignment s)
    (Sat.Literal.pos 3469) (Sat.Literal.pos 3468) (Sat.Literal.pos 206) (Sat.Literal.pos 157) (positive_of_descriptor s 3469 (.lex permutation7 206) (by rfl)) (lex_7_206_prefix s) (positive_select s 206) (lex_7_206_image s)

theorem lex_7_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3468), (Sat.Literal.pos 206), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation7 206 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3468) (Sat.Literal.pos 206) (Sat.Literal.pos 157) (lex_7_206_prefix s) (positive_select s 206) (lex_7_206_image s)

theorem lex_7_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3469), (Sat.Literal.pos 3468)] :=
  (lex_7_206_gate s).prop _ (List.Mem.head _)

theorem lex_7_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3469), (Sat.Literal.neg 206), (Sat.Literal.pos 157)] :=
  (lex_7_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3469), (Sat.Literal.pos 206), (Sat.Literal.neg 157)] :=
  (lex_7_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3468), (Sat.Literal.neg 206), (Sat.Literal.neg 157), (Sat.Literal.pos 3469)] :=
  (lex_7_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3468), (Sat.Literal.pos 206), (Sat.Literal.pos 157), (Sat.Literal.pos 3469)] :=
  (lex_7_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3469) = lexBefore s permutation7 205 := by
  exact (positive_lex_of_descriptor s 3469 permutation7 206 (by rfl)).trans ((lex_skipped s permutation7 205 206 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation7 205) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation7 205 by rw [image7_eq]; rfl))

theorem lex_7_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3470) (Sat.Literal.pos 3469) (Sat.Literal.pos 205) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation7 205 (assignment s)
    (Sat.Literal.pos 3470) (Sat.Literal.pos 3469) (Sat.Literal.pos 205) (Sat.Literal.pos 155) (positive_of_descriptor s 3470 (.lex permutation7 205) (by rfl)) (lex_7_205_prefix s) (positive_select s 205) (lex_7_205_image s)

theorem lex_7_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3469), (Sat.Literal.pos 205), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation7 205 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3469) (Sat.Literal.pos 205) (Sat.Literal.pos 155) (lex_7_205_prefix s) (positive_select s 205) (lex_7_205_image s)

theorem lex_7_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3470), (Sat.Literal.pos 3469)] :=
  (lex_7_205_gate s).prop _ (List.Mem.head _)

theorem lex_7_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3470), (Sat.Literal.neg 205), (Sat.Literal.pos 155)] :=
  (lex_7_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3470), (Sat.Literal.pos 205), (Sat.Literal.neg 155)] :=
  (lex_7_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3469), (Sat.Literal.neg 205), (Sat.Literal.neg 155), (Sat.Literal.pos 3470)] :=
  (lex_7_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3469), (Sat.Literal.pos 205), (Sat.Literal.pos 155), (Sat.Literal.pos 3470)] :=
  (lex_7_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3470) = lexBefore s permutation7 204 := by
  exact (positive_lex_of_descriptor s 3470 permutation7 205 (by rfl)).trans ((lex_skipped s permutation7 204 205 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation7 204) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation7 204 by rw [image7_eq]; rfl))

theorem lex_7_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3471) (Sat.Literal.pos 3470) (Sat.Literal.pos 204) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation7 204 (assignment s)
    (Sat.Literal.pos 3471) (Sat.Literal.pos 3470) (Sat.Literal.pos 204) (Sat.Literal.pos 153) (positive_of_descriptor s 3471 (.lex permutation7 204) (by rfl)) (lex_7_204_prefix s) (positive_select s 204) (lex_7_204_image s)

theorem lex_7_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3470), (Sat.Literal.pos 204), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation7 204 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3470) (Sat.Literal.pos 204) (Sat.Literal.pos 153) (lex_7_204_prefix s) (positive_select s 204) (lex_7_204_image s)

theorem lex_7_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3471), (Sat.Literal.pos 3470)] :=
  (lex_7_204_gate s).prop _ (List.Mem.head _)

theorem lex_7_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3471), (Sat.Literal.neg 204), (Sat.Literal.pos 153)] :=
  (lex_7_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3471), (Sat.Literal.pos 204), (Sat.Literal.neg 153)] :=
  (lex_7_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3470), (Sat.Literal.neg 204), (Sat.Literal.neg 153), (Sat.Literal.pos 3471)] :=
  (lex_7_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3470), (Sat.Literal.pos 204), (Sat.Literal.pos 153), (Sat.Literal.pos 3471)] :=
  (lex_7_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3471) = lexBefore s permutation7 203 := by
  exact (positive_lex_of_descriptor s 3471 permutation7 204 (by rfl)).trans ((lex_skipped s permutation7 203 204 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation7 203) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation7 203 by rw [image7_eq]; rfl))

theorem lex_7_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3472) (Sat.Literal.pos 3471) (Sat.Literal.pos 203) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation7 203 (assignment s)
    (Sat.Literal.pos 3472) (Sat.Literal.pos 3471) (Sat.Literal.pos 203) (Sat.Literal.pos 151) (positive_of_descriptor s 3472 (.lex permutation7 203) (by rfl)) (lex_7_203_prefix s) (positive_select s 203) (lex_7_203_image s)

theorem lex_7_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3471), (Sat.Literal.pos 203), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation7 203 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3471) (Sat.Literal.pos 203) (Sat.Literal.pos 151) (lex_7_203_prefix s) (positive_select s 203) (lex_7_203_image s)

theorem lex_7_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3472), (Sat.Literal.pos 3471)] :=
  (lex_7_203_gate s).prop _ (List.Mem.head _)

theorem lex_7_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3472), (Sat.Literal.neg 203), (Sat.Literal.pos 151)] :=
  (lex_7_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3472), (Sat.Literal.pos 203), (Sat.Literal.neg 151)] :=
  (lex_7_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3471), (Sat.Literal.neg 203), (Sat.Literal.neg 151), (Sat.Literal.pos 3472)] :=
  (lex_7_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3471), (Sat.Literal.pos 203), (Sat.Literal.pos 151), (Sat.Literal.pos 3472)] :=
  (lex_7_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3472) = lexBefore s permutation7 202 := by
  exact (positive_lex_of_descriptor s 3472 permutation7 203 (by rfl)).trans ((lex_skipped s permutation7 202 203 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation7 202) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation7 202 by rw [image7_eq]; rfl))

theorem lex_7_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3473) (Sat.Literal.pos 3472) (Sat.Literal.pos 202) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation7 202 (assignment s)
    (Sat.Literal.pos 3473) (Sat.Literal.pos 3472) (Sat.Literal.pos 202) (Sat.Literal.pos 149) (positive_of_descriptor s 3473 (.lex permutation7 202) (by rfl)) (lex_7_202_prefix s) (positive_select s 202) (lex_7_202_image s)

theorem lex_7_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3472), (Sat.Literal.pos 202), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation7 202 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3472) (Sat.Literal.pos 202) (Sat.Literal.pos 149) (lex_7_202_prefix s) (positive_select s 202) (lex_7_202_image s)

theorem lex_7_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3473), (Sat.Literal.pos 3472)] :=
  (lex_7_202_gate s).prop _ (List.Mem.head _)

theorem lex_7_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3473), (Sat.Literal.neg 202), (Sat.Literal.pos 149)] :=
  (lex_7_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3473), (Sat.Literal.pos 202), (Sat.Literal.neg 149)] :=
  (lex_7_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3472), (Sat.Literal.neg 202), (Sat.Literal.neg 149), (Sat.Literal.pos 3473)] :=
  (lex_7_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3472), (Sat.Literal.pos 202), (Sat.Literal.pos 149), (Sat.Literal.pos 3473)] :=
  (lex_7_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3473) = lexBefore s permutation7 201 := by
  exact (positive_lex_of_descriptor s 3473 permutation7 202 (by rfl)).trans ((lex_skipped s permutation7 201 202 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation7 201) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation7 201 by rw [image7_eq]; rfl))

theorem lex_7_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3474) (Sat.Literal.pos 3473) (Sat.Literal.pos 201) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation7 201 (assignment s)
    (Sat.Literal.pos 3474) (Sat.Literal.pos 3473) (Sat.Literal.pos 201) (Sat.Literal.pos 147) (positive_of_descriptor s 3474 (.lex permutation7 201) (by rfl)) (lex_7_201_prefix s) (positive_select s 201) (lex_7_201_image s)

theorem lex_7_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3473), (Sat.Literal.pos 201), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation7 201 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3473) (Sat.Literal.pos 201) (Sat.Literal.pos 147) (lex_7_201_prefix s) (positive_select s 201) (lex_7_201_image s)

theorem lex_7_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3474), (Sat.Literal.pos 3473)] :=
  (lex_7_201_gate s).prop _ (List.Mem.head _)

theorem lex_7_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3474), (Sat.Literal.neg 201), (Sat.Literal.pos 147)] :=
  (lex_7_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3474), (Sat.Literal.pos 201), (Sat.Literal.neg 147)] :=
  (lex_7_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3473), (Sat.Literal.neg 201), (Sat.Literal.neg 147), (Sat.Literal.pos 3474)] :=
  (lex_7_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3473), (Sat.Literal.pos 201), (Sat.Literal.pos 147), (Sat.Literal.pos 3474)] :=
  (lex_7_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3474) = lexBefore s permutation7 200 := by
  exact (positive_lex_of_descriptor s 3474 permutation7 201 (by rfl)).trans ((lex_skipped s permutation7 200 201 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation7 200) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation7 200 by rw [image7_eq]; rfl))

theorem lex_7_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3475) (Sat.Literal.pos 3474) (Sat.Literal.pos 200) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation7 200 (assignment s)
    (Sat.Literal.pos 3475) (Sat.Literal.pos 3474) (Sat.Literal.pos 200) (Sat.Literal.pos 145) (positive_of_descriptor s 3475 (.lex permutation7 200) (by rfl)) (lex_7_200_prefix s) (positive_select s 200) (lex_7_200_image s)

theorem lex_7_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3474), (Sat.Literal.pos 200), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation7 200 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3474) (Sat.Literal.pos 200) (Sat.Literal.pos 145) (lex_7_200_prefix s) (positive_select s 200) (lex_7_200_image s)

theorem lex_7_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3475), (Sat.Literal.pos 3474)] :=
  (lex_7_200_gate s).prop _ (List.Mem.head _)

theorem lex_7_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3475), (Sat.Literal.neg 200), (Sat.Literal.pos 145)] :=
  (lex_7_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3475), (Sat.Literal.pos 200), (Sat.Literal.neg 145)] :=
  (lex_7_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3474), (Sat.Literal.neg 200), (Sat.Literal.neg 145), (Sat.Literal.pos 3475)] :=
  (lex_7_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3474), (Sat.Literal.pos 200), (Sat.Literal.pos 145), (Sat.Literal.pos 3475)] :=
  (lex_7_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3475) = lexBefore s permutation7 199 := by
  exact (positive_lex_of_descriptor s 3475 permutation7 200 (by rfl)).trans ((lex_skipped s permutation7 199 200 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation7 199) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation7 199 by rw [image7_eq]; rfl))

theorem lex_7_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3476) (Sat.Literal.pos 3475) (Sat.Literal.pos 199) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation7 199 (assignment s)
    (Sat.Literal.pos 3476) (Sat.Literal.pos 3475) (Sat.Literal.pos 199) (Sat.Literal.pos 143) (positive_of_descriptor s 3476 (.lex permutation7 199) (by rfl)) (lex_7_199_prefix s) (positive_select s 199) (lex_7_199_image s)

theorem lex_7_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3475), (Sat.Literal.pos 199), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation7 199 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3475) (Sat.Literal.pos 199) (Sat.Literal.pos 143) (lex_7_199_prefix s) (positive_select s 199) (lex_7_199_image s)

theorem lex_7_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3476), (Sat.Literal.pos 3475)] :=
  (lex_7_199_gate s).prop _ (List.Mem.head _)

theorem lex_7_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3476), (Sat.Literal.neg 199), (Sat.Literal.pos 143)] :=
  (lex_7_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3476), (Sat.Literal.pos 199), (Sat.Literal.neg 143)] :=
  (lex_7_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3475), (Sat.Literal.neg 199), (Sat.Literal.neg 143), (Sat.Literal.pos 3476)] :=
  (lex_7_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3475), (Sat.Literal.pos 199), (Sat.Literal.pos 143), (Sat.Literal.pos 3476)] :=
  (lex_7_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3476) = lexBefore s permutation7 198 := by
  exact (positive_lex_of_descriptor s 3476 permutation7 199 (by rfl)).trans ((lex_skipped s permutation7 198 199 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation7 198) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation7 198 by rw [image7_eq]; rfl))

theorem lex_7_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3477) (Sat.Literal.pos 3476) (Sat.Literal.pos 198) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation7 198 (assignment s)
    (Sat.Literal.pos 3477) (Sat.Literal.pos 3476) (Sat.Literal.pos 198) (Sat.Literal.pos 141) (positive_of_descriptor s 3477 (.lex permutation7 198) (by rfl)) (lex_7_198_prefix s) (positive_select s 198) (lex_7_198_image s)

theorem lex_7_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3476), (Sat.Literal.pos 198), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation7 198 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3476) (Sat.Literal.pos 198) (Sat.Literal.pos 141) (lex_7_198_prefix s) (positive_select s 198) (lex_7_198_image s)

theorem lex_7_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3477), (Sat.Literal.pos 3476)] :=
  (lex_7_198_gate s).prop _ (List.Mem.head _)

theorem lex_7_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3477), (Sat.Literal.neg 198), (Sat.Literal.pos 141)] :=
  (lex_7_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3477), (Sat.Literal.pos 198), (Sat.Literal.neg 141)] :=
  (lex_7_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3476), (Sat.Literal.neg 198), (Sat.Literal.neg 141), (Sat.Literal.pos 3477)] :=
  (lex_7_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3476), (Sat.Literal.pos 198), (Sat.Literal.pos 141), (Sat.Literal.pos 3477)] :=
  (lex_7_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3477) = lexBefore s permutation7 197 := by
  exact (positive_lex_of_descriptor s 3477 permutation7 198 (by rfl)).trans ((lex_skipped s permutation7 197 198 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation7 197) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation7 197 by rw [image7_eq]; rfl))

theorem lex_7_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3478) (Sat.Literal.pos 3477) (Sat.Literal.pos 197) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation7 197 (assignment s)
    (Sat.Literal.pos 3478) (Sat.Literal.pos 3477) (Sat.Literal.pos 197) (Sat.Literal.pos 139) (positive_of_descriptor s 3478 (.lex permutation7 197) (by rfl)) (lex_7_197_prefix s) (positive_select s 197) (lex_7_197_image s)

theorem lex_7_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3477), (Sat.Literal.pos 197), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation7 197 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3477) (Sat.Literal.pos 197) (Sat.Literal.pos 139) (lex_7_197_prefix s) (positive_select s 197) (lex_7_197_image s)

theorem lex_7_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3478), (Sat.Literal.pos 3477)] :=
  (lex_7_197_gate s).prop _ (List.Mem.head _)

theorem lex_7_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3478), (Sat.Literal.neg 197), (Sat.Literal.pos 139)] :=
  (lex_7_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3478), (Sat.Literal.pos 197), (Sat.Literal.neg 139)] :=
  (lex_7_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3477), (Sat.Literal.neg 197), (Sat.Literal.neg 139), (Sat.Literal.pos 3478)] :=
  (lex_7_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3477), (Sat.Literal.pos 197), (Sat.Literal.pos 139), (Sat.Literal.pos 3478)] :=
  (lex_7_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3478) = lexBefore s permutation7 196 := by
  exact (positive_lex_of_descriptor s 3478 permutation7 197 (by rfl)).trans ((lex_skipped s permutation7 196 197 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation7 196) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation7 196 by rw [image7_eq]; rfl))

theorem lex_7_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3479) (Sat.Literal.pos 3478) (Sat.Literal.pos 196) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation7 196 (assignment s)
    (Sat.Literal.pos 3479) (Sat.Literal.pos 3478) (Sat.Literal.pos 196) (Sat.Literal.pos 137) (positive_of_descriptor s 3479 (.lex permutation7 196) (by rfl)) (lex_7_196_prefix s) (positive_select s 196) (lex_7_196_image s)

theorem lex_7_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3478), (Sat.Literal.pos 196), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation7 196 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3478) (Sat.Literal.pos 196) (Sat.Literal.pos 137) (lex_7_196_prefix s) (positive_select s 196) (lex_7_196_image s)

theorem lex_7_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3479), (Sat.Literal.pos 3478)] :=
  (lex_7_196_gate s).prop _ (List.Mem.head _)

theorem lex_7_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3479), (Sat.Literal.neg 196), (Sat.Literal.pos 137)] :=
  (lex_7_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3479), (Sat.Literal.pos 196), (Sat.Literal.neg 137)] :=
  (lex_7_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3478), (Sat.Literal.neg 196), (Sat.Literal.neg 137), (Sat.Literal.pos 3479)] :=
  (lex_7_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3478), (Sat.Literal.pos 196), (Sat.Literal.pos 137), (Sat.Literal.pos 3479)] :=
  (lex_7_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3479) = lexBefore s permutation7 195 := by
  exact (positive_lex_of_descriptor s 3479 permutation7 196 (by rfl)).trans ((lex_skipped s permutation7 195 196 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation7 195) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation7 195 by rw [image7_eq]; rfl))

theorem lex_7_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3480) (Sat.Literal.pos 3479) (Sat.Literal.pos 195) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation7 195 (assignment s)
    (Sat.Literal.pos 3480) (Sat.Literal.pos 3479) (Sat.Literal.pos 195) (Sat.Literal.pos 135) (positive_of_descriptor s 3480 (.lex permutation7 195) (by rfl)) (lex_7_195_prefix s) (positive_select s 195) (lex_7_195_image s)

theorem lex_7_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3479), (Sat.Literal.pos 195), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation7 195 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3479) (Sat.Literal.pos 195) (Sat.Literal.pos 135) (lex_7_195_prefix s) (positive_select s 195) (lex_7_195_image s)

theorem lex_7_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3480), (Sat.Literal.pos 3479)] :=
  (lex_7_195_gate s).prop _ (List.Mem.head _)

theorem lex_7_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3480), (Sat.Literal.neg 195), (Sat.Literal.pos 135)] :=
  (lex_7_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3480), (Sat.Literal.pos 195), (Sat.Literal.neg 135)] :=
  (lex_7_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3479), (Sat.Literal.neg 195), (Sat.Literal.neg 135), (Sat.Literal.pos 3480)] :=
  (lex_7_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3479), (Sat.Literal.pos 195), (Sat.Literal.pos 135), (Sat.Literal.pos 3480)] :=
  (lex_7_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3480) = lexBefore s permutation7 194 := by
  exact (positive_lex_of_descriptor s 3480 permutation7 195 (by rfl)).trans ((lex_skipped s permutation7 194 195 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation7 194) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation7 194 by rw [image7_eq]; rfl))

theorem lex_7_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3481) (Sat.Literal.pos 3480) (Sat.Literal.pos 194) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation7 194 (assignment s)
    (Sat.Literal.pos 3481) (Sat.Literal.pos 3480) (Sat.Literal.pos 194) (Sat.Literal.pos 133) (positive_of_descriptor s 3481 (.lex permutation7 194) (by rfl)) (lex_7_194_prefix s) (positive_select s 194) (lex_7_194_image s)

theorem lex_7_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3480), (Sat.Literal.pos 194), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation7 194 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3480) (Sat.Literal.pos 194) (Sat.Literal.pos 133) (lex_7_194_prefix s) (positive_select s 194) (lex_7_194_image s)

theorem lex_7_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3481), (Sat.Literal.pos 3480)] :=
  (lex_7_194_gate s).prop _ (List.Mem.head _)

theorem lex_7_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3481), (Sat.Literal.neg 194), (Sat.Literal.pos 133)] :=
  (lex_7_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3481), (Sat.Literal.pos 194), (Sat.Literal.neg 133)] :=
  (lex_7_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3480), (Sat.Literal.neg 194), (Sat.Literal.neg 133), (Sat.Literal.pos 3481)] :=
  (lex_7_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3480), (Sat.Literal.pos 194), (Sat.Literal.pos 133), (Sat.Literal.pos 3481)] :=
  (lex_7_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3481) = lexBefore s permutation7 193 := by
  exact (positive_lex_of_descriptor s 3481 permutation7 194 (by rfl)).trans ((lex_skipped s permutation7 193 194 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation7 193) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation7 193 by rw [image7_eq]; rfl))

theorem lex_7_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3482) (Sat.Literal.pos 3481) (Sat.Literal.pos 193) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation7 193 (assignment s)
    (Sat.Literal.pos 3482) (Sat.Literal.pos 3481) (Sat.Literal.pos 193) (Sat.Literal.pos 131) (positive_of_descriptor s 3482 (.lex permutation7 193) (by rfl)) (lex_7_193_prefix s) (positive_select s 193) (lex_7_193_image s)

theorem lex_7_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3481), (Sat.Literal.pos 193), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation7 193 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3481) (Sat.Literal.pos 193) (Sat.Literal.pos 131) (lex_7_193_prefix s) (positive_select s 193) (lex_7_193_image s)

theorem lex_7_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3482), (Sat.Literal.pos 3481)] :=
  (lex_7_193_gate s).prop _ (List.Mem.head _)

theorem lex_7_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3482), (Sat.Literal.neg 193), (Sat.Literal.pos 131)] :=
  (lex_7_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3482), (Sat.Literal.pos 193), (Sat.Literal.neg 131)] :=
  (lex_7_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3481), (Sat.Literal.neg 193), (Sat.Literal.neg 131), (Sat.Literal.pos 3482)] :=
  (lex_7_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3481), (Sat.Literal.pos 193), (Sat.Literal.pos 131), (Sat.Literal.pos 3482)] :=
  (lex_7_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3482) = lexBefore s permutation7 192 := by
  exact (positive_lex_of_descriptor s 3482 permutation7 193 (by rfl)).trans ((lex_skipped s permutation7 192 193 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation7 192) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation7 192 by rw [image7_eq]; rfl))

theorem lex_7_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3483) (Sat.Literal.pos 3482) (Sat.Literal.pos 192) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation7 192 (assignment s)
    (Sat.Literal.pos 3483) (Sat.Literal.pos 3482) (Sat.Literal.pos 192) (Sat.Literal.pos 129) (positive_of_descriptor s 3483 (.lex permutation7 192) (by rfl)) (lex_7_192_prefix s) (positive_select s 192) (lex_7_192_image s)

theorem lex_7_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3482), (Sat.Literal.pos 192), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation7 192 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3482) (Sat.Literal.pos 192) (Sat.Literal.pos 129) (lex_7_192_prefix s) (positive_select s 192) (lex_7_192_image s)

theorem lex_7_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3483), (Sat.Literal.pos 3482)] :=
  (lex_7_192_gate s).prop _ (List.Mem.head _)

theorem lex_7_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3483), (Sat.Literal.neg 192), (Sat.Literal.pos 129)] :=
  (lex_7_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3483), (Sat.Literal.pos 192), (Sat.Literal.neg 129)] :=
  (lex_7_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3482), (Sat.Literal.neg 192), (Sat.Literal.neg 129), (Sat.Literal.pos 3483)] :=
  (lex_7_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3482), (Sat.Literal.pos 192), (Sat.Literal.pos 129), (Sat.Literal.pos 3483)] :=
  (lex_7_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3483) = lexBefore s permutation7 191 := by
  exact (positive_lex_of_descriptor s 3483 permutation7 192 (by rfl)).trans ((lex_skipped s permutation7 191 192 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 127) = s (permuteMask permutation7 191) := by
  exact (positive_select s 127).trans (congrArg s (show (127 : Fin 256) = permuteMask permutation7 191 by rw [image7_eq]; rfl))

theorem lex_7_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3484) (Sat.Literal.pos 3483) (Sat.Literal.pos 191) (Sat.Literal.pos 127)) := by
  exact equality_gate s permutation7 191 (assignment s)
    (Sat.Literal.pos 3484) (Sat.Literal.pos 3483) (Sat.Literal.pos 191) (Sat.Literal.pos 127) (positive_of_descriptor s 3484 (.lex permutation7 191) (by rfl)) (lex_7_191_prefix s) (positive_select s 191) (lex_7_191_image s)

theorem lex_7_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3483), (Sat.Literal.pos 191), (Sat.Literal.neg 127)] := by
  exact comparison_gate s permutation7 191 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3483) (Sat.Literal.pos 191) (Sat.Literal.pos 127) (lex_7_191_prefix s) (positive_select s 191) (lex_7_191_image s)

theorem lex_7_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3484), (Sat.Literal.pos 3483)] :=
  (lex_7_191_gate s).prop _ (List.Mem.head _)

theorem lex_7_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3484), (Sat.Literal.neg 191), (Sat.Literal.pos 127)] :=
  (lex_7_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3484), (Sat.Literal.pos 191), (Sat.Literal.neg 127)] :=
  (lex_7_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3483), (Sat.Literal.neg 191), (Sat.Literal.neg 127), (Sat.Literal.pos 3484)] :=
  (lex_7_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3483), (Sat.Literal.pos 191), (Sat.Literal.pos 127), (Sat.Literal.pos 3484)] :=
  (lex_7_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3484) = lexBefore s permutation7 190 := by
  exact (positive_lex_of_descriptor s 3484 permutation7 191 (by rfl)).trans ((lex_skipped s permutation7 190 191 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation7 190) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation7 190 by rw [image7_eq]; rfl))

theorem lex_7_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3485) (Sat.Literal.pos 3484) (Sat.Literal.pos 190) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation7 190 (assignment s)
    (Sat.Literal.pos 3485) (Sat.Literal.pos 3484) (Sat.Literal.pos 190) (Sat.Literal.pos 125) (positive_of_descriptor s 3485 (.lex permutation7 190) (by rfl)) (lex_7_190_prefix s) (positive_select s 190) (lex_7_190_image s)

theorem lex_7_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3484), (Sat.Literal.pos 190), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation7 190 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3484) (Sat.Literal.pos 190) (Sat.Literal.pos 125) (lex_7_190_prefix s) (positive_select s 190) (lex_7_190_image s)

theorem lex_7_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3485), (Sat.Literal.pos 3484)] :=
  (lex_7_190_gate s).prop _ (List.Mem.head _)

theorem lex_7_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3485), (Sat.Literal.neg 190), (Sat.Literal.pos 125)] :=
  (lex_7_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3485), (Sat.Literal.pos 190), (Sat.Literal.neg 125)] :=
  (lex_7_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3484), (Sat.Literal.neg 190), (Sat.Literal.neg 125), (Sat.Literal.pos 3485)] :=
  (lex_7_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3484), (Sat.Literal.pos 190), (Sat.Literal.pos 125), (Sat.Literal.pos 3485)] :=
  (lex_7_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3485) = lexBefore s permutation7 189 := by
  exact (positive_lex_of_descriptor s 3485 permutation7 190 (by rfl)).trans ((lex_skipped s permutation7 189 190 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation7 189) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation7 189 by rw [image7_eq]; rfl))

theorem lex_7_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3486) (Sat.Literal.pos 3485) (Sat.Literal.pos 189) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation7 189 (assignment s)
    (Sat.Literal.pos 3486) (Sat.Literal.pos 3485) (Sat.Literal.pos 189) (Sat.Literal.pos 123) (positive_of_descriptor s 3486 (.lex permutation7 189) (by rfl)) (lex_7_189_prefix s) (positive_select s 189) (lex_7_189_image s)

theorem lex_7_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3485), (Sat.Literal.pos 189), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation7 189 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3485) (Sat.Literal.pos 189) (Sat.Literal.pos 123) (lex_7_189_prefix s) (positive_select s 189) (lex_7_189_image s)

theorem lex_7_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3486), (Sat.Literal.pos 3485)] :=
  (lex_7_189_gate s).prop _ (List.Mem.head _)

theorem lex_7_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3486), (Sat.Literal.neg 189), (Sat.Literal.pos 123)] :=
  (lex_7_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3486), (Sat.Literal.pos 189), (Sat.Literal.neg 123)] :=
  (lex_7_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3485), (Sat.Literal.neg 189), (Sat.Literal.neg 123), (Sat.Literal.pos 3486)] :=
  (lex_7_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3485), (Sat.Literal.pos 189), (Sat.Literal.pos 123), (Sat.Literal.pos 3486)] :=
  (lex_7_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3486) = lexBefore s permutation7 188 := by
  exact (positive_lex_of_descriptor s 3486 permutation7 189 (by rfl)).trans ((lex_skipped s permutation7 188 189 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation7 188) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation7 188 by rw [image7_eq]; rfl))

theorem lex_7_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3487) (Sat.Literal.pos 3486) (Sat.Literal.pos 188) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation7 188 (assignment s)
    (Sat.Literal.pos 3487) (Sat.Literal.pos 3486) (Sat.Literal.pos 188) (Sat.Literal.pos 121) (positive_of_descriptor s 3487 (.lex permutation7 188) (by rfl)) (lex_7_188_prefix s) (positive_select s 188) (lex_7_188_image s)

theorem lex_7_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3486), (Sat.Literal.pos 188), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation7 188 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3486) (Sat.Literal.pos 188) (Sat.Literal.pos 121) (lex_7_188_prefix s) (positive_select s 188) (lex_7_188_image s)

theorem lex_7_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3487), (Sat.Literal.pos 3486)] :=
  (lex_7_188_gate s).prop _ (List.Mem.head _)

theorem lex_7_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3487), (Sat.Literal.neg 188), (Sat.Literal.pos 121)] :=
  (lex_7_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3487), (Sat.Literal.pos 188), (Sat.Literal.neg 121)] :=
  (lex_7_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3486), (Sat.Literal.neg 188), (Sat.Literal.neg 121), (Sat.Literal.pos 3487)] :=
  (lex_7_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3486), (Sat.Literal.pos 188), (Sat.Literal.pos 121), (Sat.Literal.pos 3487)] :=
  (lex_7_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3487) = lexBefore s permutation7 187 := by
  exact (positive_lex_of_descriptor s 3487 permutation7 188 (by rfl)).trans ((lex_skipped s permutation7 187 188 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation7 187) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation7 187 by rw [image7_eq]; rfl))

theorem lex_7_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3488) (Sat.Literal.pos 3487) (Sat.Literal.pos 187) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation7 187 (assignment s)
    (Sat.Literal.pos 3488) (Sat.Literal.pos 3487) (Sat.Literal.pos 187) (Sat.Literal.pos 119) (positive_of_descriptor s 3488 (.lex permutation7 187) (by rfl)) (lex_7_187_prefix s) (positive_select s 187) (lex_7_187_image s)

theorem lex_7_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3487), (Sat.Literal.pos 187), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation7 187 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3487) (Sat.Literal.pos 187) (Sat.Literal.pos 119) (lex_7_187_prefix s) (positive_select s 187) (lex_7_187_image s)

theorem lex_7_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3488), (Sat.Literal.pos 3487)] :=
  (lex_7_187_gate s).prop _ (List.Mem.head _)

theorem lex_7_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3488), (Sat.Literal.neg 187), (Sat.Literal.pos 119)] :=
  (lex_7_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3488), (Sat.Literal.pos 187), (Sat.Literal.neg 119)] :=
  (lex_7_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3487), (Sat.Literal.neg 187), (Sat.Literal.neg 119), (Sat.Literal.pos 3488)] :=
  (lex_7_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3487), (Sat.Literal.pos 187), (Sat.Literal.pos 119), (Sat.Literal.pos 3488)] :=
  (lex_7_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3488) = lexBefore s permutation7 186 := by
  exact (positive_lex_of_descriptor s 3488 permutation7 187 (by rfl)).trans ((lex_skipped s permutation7 186 187 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation7 186) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation7 186 by rw [image7_eq]; rfl))

theorem lex_7_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3489) (Sat.Literal.pos 3488) (Sat.Literal.pos 186) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation7 186 (assignment s)
    (Sat.Literal.pos 3489) (Sat.Literal.pos 3488) (Sat.Literal.pos 186) (Sat.Literal.pos 117) (positive_of_descriptor s 3489 (.lex permutation7 186) (by rfl)) (lex_7_186_prefix s) (positive_select s 186) (lex_7_186_image s)

theorem lex_7_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3488), (Sat.Literal.pos 186), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation7 186 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3488) (Sat.Literal.pos 186) (Sat.Literal.pos 117) (lex_7_186_prefix s) (positive_select s 186) (lex_7_186_image s)

theorem lex_7_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3489), (Sat.Literal.pos 3488)] :=
  (lex_7_186_gate s).prop _ (List.Mem.head _)

theorem lex_7_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3489), (Sat.Literal.neg 186), (Sat.Literal.pos 117)] :=
  (lex_7_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3489), (Sat.Literal.pos 186), (Sat.Literal.neg 117)] :=
  (lex_7_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3488), (Sat.Literal.neg 186), (Sat.Literal.neg 117), (Sat.Literal.pos 3489)] :=
  (lex_7_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3488), (Sat.Literal.pos 186), (Sat.Literal.pos 117), (Sat.Literal.pos 3489)] :=
  (lex_7_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3489) = lexBefore s permutation7 185 := by
  exact (positive_lex_of_descriptor s 3489 permutation7 186 (by rfl)).trans ((lex_skipped s permutation7 185 186 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation7 185) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation7 185 by rw [image7_eq]; rfl))

theorem lex_7_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3490) (Sat.Literal.pos 3489) (Sat.Literal.pos 185) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation7 185 (assignment s)
    (Sat.Literal.pos 3490) (Sat.Literal.pos 3489) (Sat.Literal.pos 185) (Sat.Literal.pos 115) (positive_of_descriptor s 3490 (.lex permutation7 185) (by rfl)) (lex_7_185_prefix s) (positive_select s 185) (lex_7_185_image s)

theorem lex_7_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3489), (Sat.Literal.pos 185), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation7 185 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3489) (Sat.Literal.pos 185) (Sat.Literal.pos 115) (lex_7_185_prefix s) (positive_select s 185) (lex_7_185_image s)

theorem lex_7_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3490), (Sat.Literal.pos 3489)] :=
  (lex_7_185_gate s).prop _ (List.Mem.head _)

theorem lex_7_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3490), (Sat.Literal.neg 185), (Sat.Literal.pos 115)] :=
  (lex_7_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3490), (Sat.Literal.pos 185), (Sat.Literal.neg 115)] :=
  (lex_7_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3489), (Sat.Literal.neg 185), (Sat.Literal.neg 115), (Sat.Literal.pos 3490)] :=
  (lex_7_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3489), (Sat.Literal.pos 185), (Sat.Literal.pos 115), (Sat.Literal.pos 3490)] :=
  (lex_7_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3490) = lexBefore s permutation7 184 := by
  exact (positive_lex_of_descriptor s 3490 permutation7 185 (by rfl)).trans ((lex_skipped s permutation7 184 185 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 113) = s (permuteMask permutation7 184) := by
  exact (positive_select s 113).trans (congrArg s (show (113 : Fin 256) = permuteMask permutation7 184 by rw [image7_eq]; rfl))

theorem lex_7_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3491) (Sat.Literal.pos 3490) (Sat.Literal.pos 184) (Sat.Literal.pos 113)) := by
  exact equality_gate s permutation7 184 (assignment s)
    (Sat.Literal.pos 3491) (Sat.Literal.pos 3490) (Sat.Literal.pos 184) (Sat.Literal.pos 113) (positive_of_descriptor s 3491 (.lex permutation7 184) (by rfl)) (lex_7_184_prefix s) (positive_select s 184) (lex_7_184_image s)

theorem lex_7_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3490), (Sat.Literal.pos 184), (Sat.Literal.neg 113)] := by
  exact comparison_gate s permutation7 184 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3490) (Sat.Literal.pos 184) (Sat.Literal.pos 113) (lex_7_184_prefix s) (positive_select s 184) (lex_7_184_image s)

theorem lex_7_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3491), (Sat.Literal.pos 3490)] :=
  (lex_7_184_gate s).prop _ (List.Mem.head _)

theorem lex_7_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3491), (Sat.Literal.neg 184), (Sat.Literal.pos 113)] :=
  (lex_7_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3491), (Sat.Literal.pos 184), (Sat.Literal.neg 113)] :=
  (lex_7_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3490), (Sat.Literal.neg 184), (Sat.Literal.neg 113), (Sat.Literal.pos 3491)] :=
  (lex_7_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3490), (Sat.Literal.pos 184), (Sat.Literal.pos 113), (Sat.Literal.pos 3491)] :=
  (lex_7_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3491) = lexBefore s permutation7 183 := by
  exact (positive_lex_of_descriptor s 3491 permutation7 184 (by rfl)).trans ((lex_skipped s permutation7 183 184 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 111) = s (permuteMask permutation7 183) := by
  exact (positive_select s 111).trans (congrArg s (show (111 : Fin 256) = permuteMask permutation7 183 by rw [image7_eq]; rfl))

theorem lex_7_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3492) (Sat.Literal.pos 3491) (Sat.Literal.pos 183) (Sat.Literal.pos 111)) := by
  exact equality_gate s permutation7 183 (assignment s)
    (Sat.Literal.pos 3492) (Sat.Literal.pos 3491) (Sat.Literal.pos 183) (Sat.Literal.pos 111) (positive_of_descriptor s 3492 (.lex permutation7 183) (by rfl)) (lex_7_183_prefix s) (positive_select s 183) (lex_7_183_image s)

theorem lex_7_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3491), (Sat.Literal.pos 183), (Sat.Literal.neg 111)] := by
  exact comparison_gate s permutation7 183 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3491) (Sat.Literal.pos 183) (Sat.Literal.pos 111) (lex_7_183_prefix s) (positive_select s 183) (lex_7_183_image s)

theorem lex_7_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3492), (Sat.Literal.pos 3491)] :=
  (lex_7_183_gate s).prop _ (List.Mem.head _)

theorem lex_7_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3492), (Sat.Literal.neg 183), (Sat.Literal.pos 111)] :=
  (lex_7_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3492), (Sat.Literal.pos 183), (Sat.Literal.neg 111)] :=
  (lex_7_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3491), (Sat.Literal.neg 183), (Sat.Literal.neg 111), (Sat.Literal.pos 3492)] :=
  (lex_7_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3491), (Sat.Literal.pos 183), (Sat.Literal.pos 111), (Sat.Literal.pos 3492)] :=
  (lex_7_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3492) = lexBefore s permutation7 182 := by
  exact (positive_lex_of_descriptor s 3492 permutation7 183 (by rfl)).trans ((lex_skipped s permutation7 182 183 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 109) = s (permuteMask permutation7 182) := by
  exact (positive_select s 109).trans (congrArg s (show (109 : Fin 256) = permuteMask permutation7 182 by rw [image7_eq]; rfl))

theorem lex_7_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3493) (Sat.Literal.pos 3492) (Sat.Literal.pos 182) (Sat.Literal.pos 109)) := by
  exact equality_gate s permutation7 182 (assignment s)
    (Sat.Literal.pos 3493) (Sat.Literal.pos 3492) (Sat.Literal.pos 182) (Sat.Literal.pos 109) (positive_of_descriptor s 3493 (.lex permutation7 182) (by rfl)) (lex_7_182_prefix s) (positive_select s 182) (lex_7_182_image s)

theorem lex_7_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3492), (Sat.Literal.pos 182), (Sat.Literal.neg 109)] := by
  exact comparison_gate s permutation7 182 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3492) (Sat.Literal.pos 182) (Sat.Literal.pos 109) (lex_7_182_prefix s) (positive_select s 182) (lex_7_182_image s)

theorem lex_7_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3493), (Sat.Literal.pos 3492)] :=
  (lex_7_182_gate s).prop _ (List.Mem.head _)

theorem lex_7_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3493), (Sat.Literal.neg 182), (Sat.Literal.pos 109)] :=
  (lex_7_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3493), (Sat.Literal.pos 182), (Sat.Literal.neg 109)] :=
  (lex_7_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3492), (Sat.Literal.neg 182), (Sat.Literal.neg 109), (Sat.Literal.pos 3493)] :=
  (lex_7_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3492), (Sat.Literal.pos 182), (Sat.Literal.pos 109), (Sat.Literal.pos 3493)] :=
  (lex_7_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3493) = lexBefore s permutation7 181 := by
  exact (positive_lex_of_descriptor s 3493 permutation7 182 (by rfl)).trans ((lex_skipped s permutation7 181 182 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 107) = s (permuteMask permutation7 181) := by
  exact (positive_select s 107).trans (congrArg s (show (107 : Fin 256) = permuteMask permutation7 181 by rw [image7_eq]; rfl))

theorem lex_7_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3494) (Sat.Literal.pos 3493) (Sat.Literal.pos 181) (Sat.Literal.pos 107)) := by
  exact equality_gate s permutation7 181 (assignment s)
    (Sat.Literal.pos 3494) (Sat.Literal.pos 3493) (Sat.Literal.pos 181) (Sat.Literal.pos 107) (positive_of_descriptor s 3494 (.lex permutation7 181) (by rfl)) (lex_7_181_prefix s) (positive_select s 181) (lex_7_181_image s)

theorem lex_7_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3493), (Sat.Literal.pos 181), (Sat.Literal.neg 107)] := by
  exact comparison_gate s permutation7 181 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3493) (Sat.Literal.pos 181) (Sat.Literal.pos 107) (lex_7_181_prefix s) (positive_select s 181) (lex_7_181_image s)

theorem lex_7_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3494), (Sat.Literal.pos 3493)] :=
  (lex_7_181_gate s).prop _ (List.Mem.head _)

theorem lex_7_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3494), (Sat.Literal.neg 181), (Sat.Literal.pos 107)] :=
  (lex_7_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3494), (Sat.Literal.pos 181), (Sat.Literal.neg 107)] :=
  (lex_7_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3493), (Sat.Literal.neg 181), (Sat.Literal.neg 107), (Sat.Literal.pos 3494)] :=
  (lex_7_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3493), (Sat.Literal.pos 181), (Sat.Literal.pos 107), (Sat.Literal.pos 3494)] :=
  (lex_7_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3494) = lexBefore s permutation7 180 := by
  exact (positive_lex_of_descriptor s 3494 permutation7 181 (by rfl)).trans ((lex_skipped s permutation7 180 181 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 105) = s (permuteMask permutation7 180) := by
  exact (positive_select s 105).trans (congrArg s (show (105 : Fin 256) = permuteMask permutation7 180 by rw [image7_eq]; rfl))

theorem lex_7_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3495) (Sat.Literal.pos 3494) (Sat.Literal.pos 180) (Sat.Literal.pos 105)) := by
  exact equality_gate s permutation7 180 (assignment s)
    (Sat.Literal.pos 3495) (Sat.Literal.pos 3494) (Sat.Literal.pos 180) (Sat.Literal.pos 105) (positive_of_descriptor s 3495 (.lex permutation7 180) (by rfl)) (lex_7_180_prefix s) (positive_select s 180) (lex_7_180_image s)

theorem lex_7_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3494), (Sat.Literal.pos 180), (Sat.Literal.neg 105)] := by
  exact comparison_gate s permutation7 180 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3494) (Sat.Literal.pos 180) (Sat.Literal.pos 105) (lex_7_180_prefix s) (positive_select s 180) (lex_7_180_image s)

theorem lex_7_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3495), (Sat.Literal.pos 3494)] :=
  (lex_7_180_gate s).prop _ (List.Mem.head _)

theorem lex_7_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3495), (Sat.Literal.neg 180), (Sat.Literal.pos 105)] :=
  (lex_7_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3495), (Sat.Literal.pos 180), (Sat.Literal.neg 105)] :=
  (lex_7_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3494), (Sat.Literal.neg 180), (Sat.Literal.neg 105), (Sat.Literal.pos 3495)] :=
  (lex_7_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3494), (Sat.Literal.pos 180), (Sat.Literal.pos 105), (Sat.Literal.pos 3495)] :=
  (lex_7_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3495) = lexBefore s permutation7 179 := by
  exact (positive_lex_of_descriptor s 3495 permutation7 180 (by rfl)).trans ((lex_skipped s permutation7 179 180 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 103) = s (permuteMask permutation7 179) := by
  exact (positive_select s 103).trans (congrArg s (show (103 : Fin 256) = permuteMask permutation7 179 by rw [image7_eq]; rfl))

theorem lex_7_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3496) (Sat.Literal.pos 3495) (Sat.Literal.pos 179) (Sat.Literal.pos 103)) := by
  exact equality_gate s permutation7 179 (assignment s)
    (Sat.Literal.pos 3496) (Sat.Literal.pos 3495) (Sat.Literal.pos 179) (Sat.Literal.pos 103) (positive_of_descriptor s 3496 (.lex permutation7 179) (by rfl)) (lex_7_179_prefix s) (positive_select s 179) (lex_7_179_image s)

theorem lex_7_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3495), (Sat.Literal.pos 179), (Sat.Literal.neg 103)] := by
  exact comparison_gate s permutation7 179 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3495) (Sat.Literal.pos 179) (Sat.Literal.pos 103) (lex_7_179_prefix s) (positive_select s 179) (lex_7_179_image s)

theorem lex_7_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3496), (Sat.Literal.pos 3495)] :=
  (lex_7_179_gate s).prop _ (List.Mem.head _)

theorem lex_7_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3496), (Sat.Literal.neg 179), (Sat.Literal.pos 103)] :=
  (lex_7_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3496), (Sat.Literal.pos 179), (Sat.Literal.neg 103)] :=
  (lex_7_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3495), (Sat.Literal.neg 179), (Sat.Literal.neg 103), (Sat.Literal.pos 3496)] :=
  (lex_7_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3495), (Sat.Literal.pos 179), (Sat.Literal.pos 103), (Sat.Literal.pos 3496)] :=
  (lex_7_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3496) = lexBefore s permutation7 178 := by
  exact (positive_lex_of_descriptor s 3496 permutation7 179 (by rfl)).trans ((lex_skipped s permutation7 178 179 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 101) = s (permuteMask permutation7 178) := by
  exact (positive_select s 101).trans (congrArg s (show (101 : Fin 256) = permuteMask permutation7 178 by rw [image7_eq]; rfl))

theorem lex_7_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3497) (Sat.Literal.pos 3496) (Sat.Literal.pos 178) (Sat.Literal.pos 101)) := by
  exact equality_gate s permutation7 178 (assignment s)
    (Sat.Literal.pos 3497) (Sat.Literal.pos 3496) (Sat.Literal.pos 178) (Sat.Literal.pos 101) (positive_of_descriptor s 3497 (.lex permutation7 178) (by rfl)) (lex_7_178_prefix s) (positive_select s 178) (lex_7_178_image s)

theorem lex_7_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3496), (Sat.Literal.pos 178), (Sat.Literal.neg 101)] := by
  exact comparison_gate s permutation7 178 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3496) (Sat.Literal.pos 178) (Sat.Literal.pos 101) (lex_7_178_prefix s) (positive_select s 178) (lex_7_178_image s)

theorem lex_7_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3497), (Sat.Literal.pos 3496)] :=
  (lex_7_178_gate s).prop _ (List.Mem.head _)

theorem lex_7_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3497), (Sat.Literal.neg 178), (Sat.Literal.pos 101)] :=
  (lex_7_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3497), (Sat.Literal.pos 178), (Sat.Literal.neg 101)] :=
  (lex_7_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3496), (Sat.Literal.neg 178), (Sat.Literal.neg 101), (Sat.Literal.pos 3497)] :=
  (lex_7_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3496), (Sat.Literal.pos 178), (Sat.Literal.pos 101), (Sat.Literal.pos 3497)] :=
  (lex_7_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3497) = lexBefore s permutation7 177 := by
  exact (positive_lex_of_descriptor s 3497 permutation7 178 (by rfl)).trans ((lex_skipped s permutation7 177 178 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 99) = s (permuteMask permutation7 177) := by
  exact (positive_select s 99).trans (congrArg s (show (99 : Fin 256) = permuteMask permutation7 177 by rw [image7_eq]; rfl))

theorem lex_7_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3498) (Sat.Literal.pos 3497) (Sat.Literal.pos 177) (Sat.Literal.pos 99)) := by
  exact equality_gate s permutation7 177 (assignment s)
    (Sat.Literal.pos 3498) (Sat.Literal.pos 3497) (Sat.Literal.pos 177) (Sat.Literal.pos 99) (positive_of_descriptor s 3498 (.lex permutation7 177) (by rfl)) (lex_7_177_prefix s) (positive_select s 177) (lex_7_177_image s)

theorem lex_7_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3497), (Sat.Literal.pos 177), (Sat.Literal.neg 99)] := by
  exact comparison_gate s permutation7 177 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3497) (Sat.Literal.pos 177) (Sat.Literal.pos 99) (lex_7_177_prefix s) (positive_select s 177) (lex_7_177_image s)

theorem lex_7_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3498), (Sat.Literal.pos 3497)] :=
  (lex_7_177_gate s).prop _ (List.Mem.head _)

theorem lex_7_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3498), (Sat.Literal.neg 177), (Sat.Literal.pos 99)] :=
  (lex_7_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3498), (Sat.Literal.pos 177), (Sat.Literal.neg 99)] :=
  (lex_7_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3497), (Sat.Literal.neg 177), (Sat.Literal.neg 99), (Sat.Literal.pos 3498)] :=
  (lex_7_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3497), (Sat.Literal.pos 177), (Sat.Literal.pos 99), (Sat.Literal.pos 3498)] :=
  (lex_7_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3498) = lexBefore s permutation7 176 := by
  exact (positive_lex_of_descriptor s 3498 permutation7 177 (by rfl)).trans ((lex_skipped s permutation7 176 177 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 97) = s (permuteMask permutation7 176) := by
  exact (positive_select s 97).trans (congrArg s (show (97 : Fin 256) = permuteMask permutation7 176 by rw [image7_eq]; rfl))

theorem lex_7_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3499) (Sat.Literal.pos 3498) (Sat.Literal.pos 176) (Sat.Literal.pos 97)) := by
  exact equality_gate s permutation7 176 (assignment s)
    (Sat.Literal.pos 3499) (Sat.Literal.pos 3498) (Sat.Literal.pos 176) (Sat.Literal.pos 97) (positive_of_descriptor s 3499 (.lex permutation7 176) (by rfl)) (lex_7_176_prefix s) (positive_select s 176) (lex_7_176_image s)

theorem lex_7_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3498), (Sat.Literal.pos 176), (Sat.Literal.neg 97)] := by
  exact comparison_gate s permutation7 176 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3498) (Sat.Literal.pos 176) (Sat.Literal.pos 97) (lex_7_176_prefix s) (positive_select s 176) (lex_7_176_image s)

theorem lex_7_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3499), (Sat.Literal.pos 3498)] :=
  (lex_7_176_gate s).prop _ (List.Mem.head _)

theorem lex_7_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3499), (Sat.Literal.neg 176), (Sat.Literal.pos 97)] :=
  (lex_7_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3499), (Sat.Literal.pos 176), (Sat.Literal.neg 97)] :=
  (lex_7_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3498), (Sat.Literal.neg 176), (Sat.Literal.neg 97), (Sat.Literal.pos 3499)] :=
  (lex_7_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3498), (Sat.Literal.pos 176), (Sat.Literal.pos 97), (Sat.Literal.pos 3499)] :=
  (lex_7_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3499) = lexBefore s permutation7 175 := by
  exact (positive_lex_of_descriptor s 3499 permutation7 176 (by rfl)).trans ((lex_skipped s permutation7 175 176 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation7 175) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation7 175 by rw [image7_eq]; rfl))

theorem lex_7_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3500) (Sat.Literal.pos 3499) (Sat.Literal.pos 175) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation7 175 (assignment s)
    (Sat.Literal.pos 3500) (Sat.Literal.pos 3499) (Sat.Literal.pos 175) (Sat.Literal.pos 95) (positive_of_descriptor s 3500 (.lex permutation7 175) (by rfl)) (lex_7_175_prefix s) (positive_select s 175) (lex_7_175_image s)

theorem lex_7_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3499), (Sat.Literal.pos 175), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation7 175 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3499) (Sat.Literal.pos 175) (Sat.Literal.pos 95) (lex_7_175_prefix s) (positive_select s 175) (lex_7_175_image s)

theorem lex_7_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3500), (Sat.Literal.pos 3499)] :=
  (lex_7_175_gate s).prop _ (List.Mem.head _)

theorem lex_7_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3500), (Sat.Literal.neg 175), (Sat.Literal.pos 95)] :=
  (lex_7_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3500), (Sat.Literal.pos 175), (Sat.Literal.neg 95)] :=
  (lex_7_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3499), (Sat.Literal.neg 175), (Sat.Literal.neg 95), (Sat.Literal.pos 3500)] :=
  (lex_7_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3499), (Sat.Literal.pos 175), (Sat.Literal.pos 95), (Sat.Literal.pos 3500)] :=
  (lex_7_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3500) = lexBefore s permutation7 174 := by
  exact (positive_lex_of_descriptor s 3500 permutation7 175 (by rfl)).trans ((lex_skipped s permutation7 174 175 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation7 174) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation7 174 by rw [image7_eq]; rfl))

theorem lex_7_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3501) (Sat.Literal.pos 3500) (Sat.Literal.pos 174) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation7 174 (assignment s)
    (Sat.Literal.pos 3501) (Sat.Literal.pos 3500) (Sat.Literal.pos 174) (Sat.Literal.pos 93) (positive_of_descriptor s 3501 (.lex permutation7 174) (by rfl)) (lex_7_174_prefix s) (positive_select s 174) (lex_7_174_image s)

theorem lex_7_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3500), (Sat.Literal.pos 174), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation7 174 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3500) (Sat.Literal.pos 174) (Sat.Literal.pos 93) (lex_7_174_prefix s) (positive_select s 174) (lex_7_174_image s)

theorem lex_7_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3501), (Sat.Literal.pos 3500)] :=
  (lex_7_174_gate s).prop _ (List.Mem.head _)

theorem lex_7_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3501), (Sat.Literal.neg 174), (Sat.Literal.pos 93)] :=
  (lex_7_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3501), (Sat.Literal.pos 174), (Sat.Literal.neg 93)] :=
  (lex_7_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3500), (Sat.Literal.neg 174), (Sat.Literal.neg 93), (Sat.Literal.pos 3501)] :=
  (lex_7_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3500), (Sat.Literal.pos 174), (Sat.Literal.pos 93), (Sat.Literal.pos 3501)] :=
  (lex_7_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3501) = lexBefore s permutation7 173 := by
  exact (positive_lex_of_descriptor s 3501 permutation7 174 (by rfl)).trans ((lex_skipped s permutation7 173 174 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation7 173) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation7 173 by rw [image7_eq]; rfl))

theorem lex_7_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3502) (Sat.Literal.pos 3501) (Sat.Literal.pos 173) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation7 173 (assignment s)
    (Sat.Literal.pos 3502) (Sat.Literal.pos 3501) (Sat.Literal.pos 173) (Sat.Literal.pos 91) (positive_of_descriptor s 3502 (.lex permutation7 173) (by rfl)) (lex_7_173_prefix s) (positive_select s 173) (lex_7_173_image s)

theorem lex_7_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3501), (Sat.Literal.pos 173), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation7 173 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3501) (Sat.Literal.pos 173) (Sat.Literal.pos 91) (lex_7_173_prefix s) (positive_select s 173) (lex_7_173_image s)

theorem lex_7_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3502), (Sat.Literal.pos 3501)] :=
  (lex_7_173_gate s).prop _ (List.Mem.head _)

theorem lex_7_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3502), (Sat.Literal.neg 173), (Sat.Literal.pos 91)] :=
  (lex_7_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3502), (Sat.Literal.pos 173), (Sat.Literal.neg 91)] :=
  (lex_7_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3501), (Sat.Literal.neg 173), (Sat.Literal.neg 91), (Sat.Literal.pos 3502)] :=
  (lex_7_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3501), (Sat.Literal.pos 173), (Sat.Literal.pos 91), (Sat.Literal.pos 3502)] :=
  (lex_7_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3502) = lexBefore s permutation7 172 := by
  exact (positive_lex_of_descriptor s 3502 permutation7 173 (by rfl)).trans ((lex_skipped s permutation7 172 173 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation7 172) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation7 172 by rw [image7_eq]; rfl))

theorem lex_7_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3503) (Sat.Literal.pos 3502) (Sat.Literal.pos 172) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation7 172 (assignment s)
    (Sat.Literal.pos 3503) (Sat.Literal.pos 3502) (Sat.Literal.pos 172) (Sat.Literal.pos 89) (positive_of_descriptor s 3503 (.lex permutation7 172) (by rfl)) (lex_7_172_prefix s) (positive_select s 172) (lex_7_172_image s)

theorem lex_7_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3502), (Sat.Literal.pos 172), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation7 172 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3502) (Sat.Literal.pos 172) (Sat.Literal.pos 89) (lex_7_172_prefix s) (positive_select s 172) (lex_7_172_image s)

theorem lex_7_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3503), (Sat.Literal.pos 3502)] :=
  (lex_7_172_gate s).prop _ (List.Mem.head _)

theorem lex_7_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3503), (Sat.Literal.neg 172), (Sat.Literal.pos 89)] :=
  (lex_7_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3503), (Sat.Literal.pos 172), (Sat.Literal.neg 89)] :=
  (lex_7_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3502), (Sat.Literal.neg 172), (Sat.Literal.neg 89), (Sat.Literal.pos 3503)] :=
  (lex_7_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3502), (Sat.Literal.pos 172), (Sat.Literal.pos 89), (Sat.Literal.pos 3503)] :=
  (lex_7_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3503) = lexBefore s permutation7 171 := by
  exact (positive_lex_of_descriptor s 3503 permutation7 172 (by rfl)).trans ((lex_skipped s permutation7 171 172 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation7 171) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation7 171 by rw [image7_eq]; rfl))

theorem lex_7_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3504) (Sat.Literal.pos 3503) (Sat.Literal.pos 171) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation7 171 (assignment s)
    (Sat.Literal.pos 3504) (Sat.Literal.pos 3503) (Sat.Literal.pos 171) (Sat.Literal.pos 87) (positive_of_descriptor s 3504 (.lex permutation7 171) (by rfl)) (lex_7_171_prefix s) (positive_select s 171) (lex_7_171_image s)

theorem lex_7_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3503), (Sat.Literal.pos 171), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation7 171 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3503) (Sat.Literal.pos 171) (Sat.Literal.pos 87) (lex_7_171_prefix s) (positive_select s 171) (lex_7_171_image s)

theorem lex_7_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3504), (Sat.Literal.pos 3503)] :=
  (lex_7_171_gate s).prop _ (List.Mem.head _)

theorem lex_7_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3504), (Sat.Literal.neg 171), (Sat.Literal.pos 87)] :=
  (lex_7_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3504), (Sat.Literal.pos 171), (Sat.Literal.neg 87)] :=
  (lex_7_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3503), (Sat.Literal.neg 171), (Sat.Literal.neg 87), (Sat.Literal.pos 3504)] :=
  (lex_7_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3503), (Sat.Literal.pos 171), (Sat.Literal.pos 87), (Sat.Literal.pos 3504)] :=
  (lex_7_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3504) = lexBefore s permutation7 170 := by
  exact (positive_lex_of_descriptor s 3504 permutation7 171 (by rfl)).trans ((lex_skipped s permutation7 170 171 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation7 170) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation7 170 by rw [image7_eq]; rfl))

theorem lex_7_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3505) (Sat.Literal.pos 3504) (Sat.Literal.pos 170) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation7 170 (assignment s)
    (Sat.Literal.pos 3505) (Sat.Literal.pos 3504) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (positive_of_descriptor s 3505 (.lex permutation7 170) (by rfl)) (lex_7_170_prefix s) (positive_select s 170) (lex_7_170_image s)

theorem lex_7_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3504), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation7 170 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3504) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (lex_7_170_prefix s) (positive_select s 170) (lex_7_170_image s)

theorem lex_7_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3505), (Sat.Literal.pos 3504)] :=
  (lex_7_170_gate s).prop _ (List.Mem.head _)

theorem lex_7_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3505), (Sat.Literal.neg 170), (Sat.Literal.pos 85)] :=
  (lex_7_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3505), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] :=
  (lex_7_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3504), (Sat.Literal.neg 170), (Sat.Literal.neg 85), (Sat.Literal.pos 3505)] :=
  (lex_7_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3504), (Sat.Literal.pos 170), (Sat.Literal.pos 85), (Sat.Literal.pos 3505)] :=
  (lex_7_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3505) = lexBefore s permutation7 169 := by
  exact (positive_lex_of_descriptor s 3505 permutation7 170 (by rfl)).trans ((lex_skipped s permutation7 169 170 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation7 169) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation7 169 by rw [image7_eq]; rfl))

theorem lex_7_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3506) (Sat.Literal.pos 3505) (Sat.Literal.pos 169) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation7 169 (assignment s)
    (Sat.Literal.pos 3506) (Sat.Literal.pos 3505) (Sat.Literal.pos 169) (Sat.Literal.pos 83) (positive_of_descriptor s 3506 (.lex permutation7 169) (by rfl)) (lex_7_169_prefix s) (positive_select s 169) (lex_7_169_image s)

theorem lex_7_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3505), (Sat.Literal.pos 169), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation7 169 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3505) (Sat.Literal.pos 169) (Sat.Literal.pos 83) (lex_7_169_prefix s) (positive_select s 169) (lex_7_169_image s)

theorem lex_7_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3506), (Sat.Literal.pos 3505)] :=
  (lex_7_169_gate s).prop _ (List.Mem.head _)

theorem lex_7_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3506), (Sat.Literal.neg 169), (Sat.Literal.pos 83)] :=
  (lex_7_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3506), (Sat.Literal.pos 169), (Sat.Literal.neg 83)] :=
  (lex_7_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3505), (Sat.Literal.neg 169), (Sat.Literal.neg 83), (Sat.Literal.pos 3506)] :=
  (lex_7_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3505), (Sat.Literal.pos 169), (Sat.Literal.pos 83), (Sat.Literal.pos 3506)] :=
  (lex_7_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3506) = lexBefore s permutation7 168 := by
  exact (positive_lex_of_descriptor s 3506 permutation7 169 (by rfl)).trans ((lex_skipped s permutation7 168 169 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation7 168) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation7 168 by rw [image7_eq]; rfl))

theorem lex_7_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3507) (Sat.Literal.pos 3506) (Sat.Literal.pos 168) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation7 168 (assignment s)
    (Sat.Literal.pos 3507) (Sat.Literal.pos 3506) (Sat.Literal.pos 168) (Sat.Literal.pos 81) (positive_of_descriptor s 3507 (.lex permutation7 168) (by rfl)) (lex_7_168_prefix s) (positive_select s 168) (lex_7_168_image s)

theorem lex_7_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3506), (Sat.Literal.pos 168), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation7 168 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3506) (Sat.Literal.pos 168) (Sat.Literal.pos 81) (lex_7_168_prefix s) (positive_select s 168) (lex_7_168_image s)

theorem lex_7_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3507), (Sat.Literal.pos 3506)] :=
  (lex_7_168_gate s).prop _ (List.Mem.head _)

theorem lex_7_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3507), (Sat.Literal.neg 168), (Sat.Literal.pos 81)] :=
  (lex_7_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3507), (Sat.Literal.pos 168), (Sat.Literal.neg 81)] :=
  (lex_7_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3506), (Sat.Literal.neg 168), (Sat.Literal.neg 81), (Sat.Literal.pos 3507)] :=
  (lex_7_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3506), (Sat.Literal.pos 168), (Sat.Literal.pos 81), (Sat.Literal.pos 3507)] :=
  (lex_7_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3507) = lexBefore s permutation7 167 := by
  exact (positive_lex_of_descriptor s 3507 permutation7 168 (by rfl)).trans ((lex_skipped s permutation7 167 168 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation7 167) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation7 167 by rw [image7_eq]; rfl))

theorem lex_7_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3508) (Sat.Literal.pos 3507) (Sat.Literal.pos 167) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation7 167 (assignment s)
    (Sat.Literal.pos 3508) (Sat.Literal.pos 3507) (Sat.Literal.pos 167) (Sat.Literal.pos 79) (positive_of_descriptor s 3508 (.lex permutation7 167) (by rfl)) (lex_7_167_prefix s) (positive_select s 167) (lex_7_167_image s)

theorem lex_7_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3507), (Sat.Literal.pos 167), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation7 167 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3507) (Sat.Literal.pos 167) (Sat.Literal.pos 79) (lex_7_167_prefix s) (positive_select s 167) (lex_7_167_image s)

theorem lex_7_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3508), (Sat.Literal.pos 3507)] :=
  (lex_7_167_gate s).prop _ (List.Mem.head _)

theorem lex_7_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3508), (Sat.Literal.neg 167), (Sat.Literal.pos 79)] :=
  (lex_7_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3508), (Sat.Literal.pos 167), (Sat.Literal.neg 79)] :=
  (lex_7_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3507), (Sat.Literal.neg 167), (Sat.Literal.neg 79), (Sat.Literal.pos 3508)] :=
  (lex_7_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3507), (Sat.Literal.pos 167), (Sat.Literal.pos 79), (Sat.Literal.pos 3508)] :=
  (lex_7_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3508) = lexBefore s permutation7 166 := by
  exact (positive_lex_of_descriptor s 3508 permutation7 167 (by rfl)).trans ((lex_skipped s permutation7 166 167 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation7 166) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation7 166 by rw [image7_eq]; rfl))

theorem lex_7_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3509) (Sat.Literal.pos 3508) (Sat.Literal.pos 166) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation7 166 (assignment s)
    (Sat.Literal.pos 3509) (Sat.Literal.pos 3508) (Sat.Literal.pos 166) (Sat.Literal.pos 77) (positive_of_descriptor s 3509 (.lex permutation7 166) (by rfl)) (lex_7_166_prefix s) (positive_select s 166) (lex_7_166_image s)

theorem lex_7_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3508), (Sat.Literal.pos 166), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation7 166 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3508) (Sat.Literal.pos 166) (Sat.Literal.pos 77) (lex_7_166_prefix s) (positive_select s 166) (lex_7_166_image s)

theorem lex_7_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3509), (Sat.Literal.pos 3508)] :=
  (lex_7_166_gate s).prop _ (List.Mem.head _)

theorem lex_7_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3509), (Sat.Literal.neg 166), (Sat.Literal.pos 77)] :=
  (lex_7_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3509), (Sat.Literal.pos 166), (Sat.Literal.neg 77)] :=
  (lex_7_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3508), (Sat.Literal.neg 166), (Sat.Literal.neg 77), (Sat.Literal.pos 3509)] :=
  (lex_7_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3508), (Sat.Literal.pos 166), (Sat.Literal.pos 77), (Sat.Literal.pos 3509)] :=
  (lex_7_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3509) = lexBefore s permutation7 165 := by
  exact (positive_lex_of_descriptor s 3509 permutation7 166 (by rfl)).trans ((lex_skipped s permutation7 165 166 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation7 165) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation7 165 by rw [image7_eq]; rfl))

theorem lex_7_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3510) (Sat.Literal.pos 3509) (Sat.Literal.pos 165) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation7 165 (assignment s)
    (Sat.Literal.pos 3510) (Sat.Literal.pos 3509) (Sat.Literal.pos 165) (Sat.Literal.pos 75) (positive_of_descriptor s 3510 (.lex permutation7 165) (by rfl)) (lex_7_165_prefix s) (positive_select s 165) (lex_7_165_image s)

theorem lex_7_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3509), (Sat.Literal.pos 165), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation7 165 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3509) (Sat.Literal.pos 165) (Sat.Literal.pos 75) (lex_7_165_prefix s) (positive_select s 165) (lex_7_165_image s)

theorem lex_7_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3510), (Sat.Literal.pos 3509)] :=
  (lex_7_165_gate s).prop _ (List.Mem.head _)

theorem lex_7_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3510), (Sat.Literal.neg 165), (Sat.Literal.pos 75)] :=
  (lex_7_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3510), (Sat.Literal.pos 165), (Sat.Literal.neg 75)] :=
  (lex_7_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3509), (Sat.Literal.neg 165), (Sat.Literal.neg 75), (Sat.Literal.pos 3510)] :=
  (lex_7_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3509), (Sat.Literal.pos 165), (Sat.Literal.pos 75), (Sat.Literal.pos 3510)] :=
  (lex_7_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3510) = lexBefore s permutation7 164 := by
  exact (positive_lex_of_descriptor s 3510 permutation7 165 (by rfl)).trans ((lex_skipped s permutation7 164 165 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation7 164) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation7 164 by rw [image7_eq]; rfl))

theorem lex_7_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3511) (Sat.Literal.pos 3510) (Sat.Literal.pos 164) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation7 164 (assignment s)
    (Sat.Literal.pos 3511) (Sat.Literal.pos 3510) (Sat.Literal.pos 164) (Sat.Literal.pos 73) (positive_of_descriptor s 3511 (.lex permutation7 164) (by rfl)) (lex_7_164_prefix s) (positive_select s 164) (lex_7_164_image s)

theorem lex_7_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3510), (Sat.Literal.pos 164), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation7 164 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3510) (Sat.Literal.pos 164) (Sat.Literal.pos 73) (lex_7_164_prefix s) (positive_select s 164) (lex_7_164_image s)

theorem lex_7_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3511), (Sat.Literal.pos 3510)] :=
  (lex_7_164_gate s).prop _ (List.Mem.head _)

theorem lex_7_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3511), (Sat.Literal.neg 164), (Sat.Literal.pos 73)] :=
  (lex_7_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3511), (Sat.Literal.pos 164), (Sat.Literal.neg 73)] :=
  (lex_7_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3510), (Sat.Literal.neg 164), (Sat.Literal.neg 73), (Sat.Literal.pos 3511)] :=
  (lex_7_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3510), (Sat.Literal.pos 164), (Sat.Literal.pos 73), (Sat.Literal.pos 3511)] :=
  (lex_7_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3511) = lexBefore s permutation7 163 := by
  exact (positive_lex_of_descriptor s 3511 permutation7 164 (by rfl)).trans ((lex_skipped s permutation7 163 164 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation7 163) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation7 163 by rw [image7_eq]; rfl))

theorem lex_7_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3512) (Sat.Literal.pos 3511) (Sat.Literal.pos 163) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation7 163 (assignment s)
    (Sat.Literal.pos 3512) (Sat.Literal.pos 3511) (Sat.Literal.pos 163) (Sat.Literal.pos 71) (positive_of_descriptor s 3512 (.lex permutation7 163) (by rfl)) (lex_7_163_prefix s) (positive_select s 163) (lex_7_163_image s)

theorem lex_7_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3511), (Sat.Literal.pos 163), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation7 163 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3511) (Sat.Literal.pos 163) (Sat.Literal.pos 71) (lex_7_163_prefix s) (positive_select s 163) (lex_7_163_image s)

theorem lex_7_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3512), (Sat.Literal.pos 3511)] :=
  (lex_7_163_gate s).prop _ (List.Mem.head _)

theorem lex_7_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3512), (Sat.Literal.neg 163), (Sat.Literal.pos 71)] :=
  (lex_7_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3512), (Sat.Literal.pos 163), (Sat.Literal.neg 71)] :=
  (lex_7_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3511), (Sat.Literal.neg 163), (Sat.Literal.neg 71), (Sat.Literal.pos 3512)] :=
  (lex_7_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3511), (Sat.Literal.pos 163), (Sat.Literal.pos 71), (Sat.Literal.pos 3512)] :=
  (lex_7_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3512) = lexBefore s permutation7 162 := by
  exact (positive_lex_of_descriptor s 3512 permutation7 163 (by rfl)).trans ((lex_skipped s permutation7 162 163 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation7 162) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation7 162 by rw [image7_eq]; rfl))

theorem lex_7_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3513) (Sat.Literal.pos 3512) (Sat.Literal.pos 162) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation7 162 (assignment s)
    (Sat.Literal.pos 3513) (Sat.Literal.pos 3512) (Sat.Literal.pos 162) (Sat.Literal.pos 69) (positive_of_descriptor s 3513 (.lex permutation7 162) (by rfl)) (lex_7_162_prefix s) (positive_select s 162) (lex_7_162_image s)

theorem lex_7_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3512), (Sat.Literal.pos 162), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation7 162 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3512) (Sat.Literal.pos 162) (Sat.Literal.pos 69) (lex_7_162_prefix s) (positive_select s 162) (lex_7_162_image s)

theorem lex_7_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3513), (Sat.Literal.pos 3512)] :=
  (lex_7_162_gate s).prop _ (List.Mem.head _)

theorem lex_7_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3513), (Sat.Literal.neg 162), (Sat.Literal.pos 69)] :=
  (lex_7_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3513), (Sat.Literal.pos 162), (Sat.Literal.neg 69)] :=
  (lex_7_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3512), (Sat.Literal.neg 162), (Sat.Literal.neg 69), (Sat.Literal.pos 3513)] :=
  (lex_7_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3512), (Sat.Literal.pos 162), (Sat.Literal.pos 69), (Sat.Literal.pos 3513)] :=
  (lex_7_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3513) = lexBefore s permutation7 161 := by
  exact (positive_lex_of_descriptor s 3513 permutation7 162 (by rfl)).trans ((lex_skipped s permutation7 161 162 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation7 161) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation7 161 by rw [image7_eq]; rfl))

theorem lex_7_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3514) (Sat.Literal.pos 3513) (Sat.Literal.pos 161) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation7 161 (assignment s)
    (Sat.Literal.pos 3514) (Sat.Literal.pos 3513) (Sat.Literal.pos 161) (Sat.Literal.pos 67) (positive_of_descriptor s 3514 (.lex permutation7 161) (by rfl)) (lex_7_161_prefix s) (positive_select s 161) (lex_7_161_image s)

theorem lex_7_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3513), (Sat.Literal.pos 161), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation7 161 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3513) (Sat.Literal.pos 161) (Sat.Literal.pos 67) (lex_7_161_prefix s) (positive_select s 161) (lex_7_161_image s)

theorem lex_7_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3514), (Sat.Literal.pos 3513)] :=
  (lex_7_161_gate s).prop _ (List.Mem.head _)

theorem lex_7_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3514), (Sat.Literal.neg 161), (Sat.Literal.pos 67)] :=
  (lex_7_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3514), (Sat.Literal.pos 161), (Sat.Literal.neg 67)] :=
  (lex_7_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3513), (Sat.Literal.neg 161), (Sat.Literal.neg 67), (Sat.Literal.pos 3514)] :=
  (lex_7_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3513), (Sat.Literal.pos 161), (Sat.Literal.pos 67), (Sat.Literal.pos 3514)] :=
  (lex_7_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3514) = lexBefore s permutation7 160 := by
  exact (positive_lex_of_descriptor s 3514 permutation7 161 (by rfl)).trans ((lex_skipped s permutation7 160 161 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation7 160) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation7 160 by rw [image7_eq]; rfl))

theorem lex_7_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3515) (Sat.Literal.pos 3514) (Sat.Literal.pos 160) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation7 160 (assignment s)
    (Sat.Literal.pos 3515) (Sat.Literal.pos 3514) (Sat.Literal.pos 160) (Sat.Literal.pos 65) (positive_of_descriptor s 3515 (.lex permutation7 160) (by rfl)) (lex_7_160_prefix s) (positive_select s 160) (lex_7_160_image s)

theorem lex_7_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3514), (Sat.Literal.pos 160), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation7 160 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3514) (Sat.Literal.pos 160) (Sat.Literal.pos 65) (lex_7_160_prefix s) (positive_select s 160) (lex_7_160_image s)

theorem lex_7_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3515), (Sat.Literal.pos 3514)] :=
  (lex_7_160_gate s).prop _ (List.Mem.head _)

theorem lex_7_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3515), (Sat.Literal.neg 160), (Sat.Literal.pos 65)] :=
  (lex_7_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3515), (Sat.Literal.pos 160), (Sat.Literal.neg 65)] :=
  (lex_7_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3514), (Sat.Literal.neg 160), (Sat.Literal.neg 65), (Sat.Literal.pos 3515)] :=
  (lex_7_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3514), (Sat.Literal.pos 160), (Sat.Literal.pos 65), (Sat.Literal.pos 3515)] :=
  (lex_7_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3515) = lexBefore s permutation7 159 := by
  exact (positive_lex_of_descriptor s 3515 permutation7 160 (by rfl)).trans ((lex_skipped s permutation7 159 160 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation7 159) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation7 159 by rw [image7_eq]; rfl))

theorem lex_7_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3516) (Sat.Literal.pos 3515) (Sat.Literal.pos 159) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation7 159 (assignment s)
    (Sat.Literal.pos 3516) (Sat.Literal.pos 3515) (Sat.Literal.pos 159) (Sat.Literal.pos 63) (positive_of_descriptor s 3516 (.lex permutation7 159) (by rfl)) (lex_7_159_prefix s) (positive_select s 159) (lex_7_159_image s)

theorem lex_7_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3515), (Sat.Literal.pos 159), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation7 159 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3515) (Sat.Literal.pos 159) (Sat.Literal.pos 63) (lex_7_159_prefix s) (positive_select s 159) (lex_7_159_image s)

theorem lex_7_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3516), (Sat.Literal.pos 3515)] :=
  (lex_7_159_gate s).prop _ (List.Mem.head _)

theorem lex_7_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3516), (Sat.Literal.neg 159), (Sat.Literal.pos 63)] :=
  (lex_7_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3516), (Sat.Literal.pos 159), (Sat.Literal.neg 63)] :=
  (lex_7_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3515), (Sat.Literal.neg 159), (Sat.Literal.neg 63), (Sat.Literal.pos 3516)] :=
  (lex_7_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3515), (Sat.Literal.pos 159), (Sat.Literal.pos 63), (Sat.Literal.pos 3516)] :=
  (lex_7_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3516) = lexBefore s permutation7 158 := by
  exact (positive_lex_of_descriptor s 3516 permutation7 159 (by rfl)).trans ((lex_skipped s permutation7 158 159 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation7 158) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation7 158 by rw [image7_eq]; rfl))

theorem lex_7_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3517) (Sat.Literal.pos 3516) (Sat.Literal.pos 158) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation7 158 (assignment s)
    (Sat.Literal.pos 3517) (Sat.Literal.pos 3516) (Sat.Literal.pos 158) (Sat.Literal.pos 61) (positive_of_descriptor s 3517 (.lex permutation7 158) (by rfl)) (lex_7_158_prefix s) (positive_select s 158) (lex_7_158_image s)

theorem lex_7_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3516), (Sat.Literal.pos 158), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation7 158 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3516) (Sat.Literal.pos 158) (Sat.Literal.pos 61) (lex_7_158_prefix s) (positive_select s 158) (lex_7_158_image s)

theorem lex_7_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3517), (Sat.Literal.pos 3516)] :=
  (lex_7_158_gate s).prop _ (List.Mem.head _)

theorem lex_7_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3517), (Sat.Literal.neg 158), (Sat.Literal.pos 61)] :=
  (lex_7_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3517), (Sat.Literal.pos 158), (Sat.Literal.neg 61)] :=
  (lex_7_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3516), (Sat.Literal.neg 158), (Sat.Literal.neg 61), (Sat.Literal.pos 3517)] :=
  (lex_7_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3516), (Sat.Literal.pos 158), (Sat.Literal.pos 61), (Sat.Literal.pos 3517)] :=
  (lex_7_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3517) = lexBefore s permutation7 157 := by
  exact (positive_lex_of_descriptor s 3517 permutation7 158 (by rfl)).trans ((lex_skipped s permutation7 157 158 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation7 157) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation7 157 by rw [image7_eq]; rfl))

theorem lex_7_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3518) (Sat.Literal.pos 3517) (Sat.Literal.pos 157) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation7 157 (assignment s)
    (Sat.Literal.pos 3518) (Sat.Literal.pos 3517) (Sat.Literal.pos 157) (Sat.Literal.pos 59) (positive_of_descriptor s 3518 (.lex permutation7 157) (by rfl)) (lex_7_157_prefix s) (positive_select s 157) (lex_7_157_image s)

theorem lex_7_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3517), (Sat.Literal.pos 157), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation7 157 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3517) (Sat.Literal.pos 157) (Sat.Literal.pos 59) (lex_7_157_prefix s) (positive_select s 157) (lex_7_157_image s)

theorem lex_7_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3518), (Sat.Literal.pos 3517)] :=
  (lex_7_157_gate s).prop _ (List.Mem.head _)

theorem lex_7_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3518), (Sat.Literal.neg 157), (Sat.Literal.pos 59)] :=
  (lex_7_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3518), (Sat.Literal.pos 157), (Sat.Literal.neg 59)] :=
  (lex_7_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3517), (Sat.Literal.neg 157), (Sat.Literal.neg 59), (Sat.Literal.pos 3518)] :=
  (lex_7_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3517), (Sat.Literal.pos 157), (Sat.Literal.pos 59), (Sat.Literal.pos 3518)] :=
  (lex_7_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3518) = lexBefore s permutation7 156 := by
  exact (positive_lex_of_descriptor s 3518 permutation7 157 (by rfl)).trans ((lex_skipped s permutation7 156 157 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation7 156) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation7 156 by rw [image7_eq]; rfl))

theorem lex_7_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3519) (Sat.Literal.pos 3518) (Sat.Literal.pos 156) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation7 156 (assignment s)
    (Sat.Literal.pos 3519) (Sat.Literal.pos 3518) (Sat.Literal.pos 156) (Sat.Literal.pos 57) (positive_of_descriptor s 3519 (.lex permutation7 156) (by rfl)) (lex_7_156_prefix s) (positive_select s 156) (lex_7_156_image s)

theorem lex_7_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3518), (Sat.Literal.pos 156), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation7 156 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3518) (Sat.Literal.pos 156) (Sat.Literal.pos 57) (lex_7_156_prefix s) (positive_select s 156) (lex_7_156_image s)

theorem lex_7_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3519), (Sat.Literal.pos 3518)] :=
  (lex_7_156_gate s).prop _ (List.Mem.head _)

theorem lex_7_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3519), (Sat.Literal.neg 156), (Sat.Literal.pos 57)] :=
  (lex_7_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3519), (Sat.Literal.pos 156), (Sat.Literal.neg 57)] :=
  (lex_7_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3518), (Sat.Literal.neg 156), (Sat.Literal.neg 57), (Sat.Literal.pos 3519)] :=
  (lex_7_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3518), (Sat.Literal.pos 156), (Sat.Literal.pos 57), (Sat.Literal.pos 3519)] :=
  (lex_7_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3519) = lexBefore s permutation7 155 := by
  exact (positive_lex_of_descriptor s 3519 permutation7 156 (by rfl)).trans ((lex_skipped s permutation7 155 156 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation7 155) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation7 155 by rw [image7_eq]; rfl))

theorem lex_7_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3520) (Sat.Literal.pos 3519) (Sat.Literal.pos 155) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation7 155 (assignment s)
    (Sat.Literal.pos 3520) (Sat.Literal.pos 3519) (Sat.Literal.pos 155) (Sat.Literal.pos 55) (positive_of_descriptor s 3520 (.lex permutation7 155) (by rfl)) (lex_7_155_prefix s) (positive_select s 155) (lex_7_155_image s)

theorem lex_7_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3519), (Sat.Literal.pos 155), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation7 155 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3519) (Sat.Literal.pos 155) (Sat.Literal.pos 55) (lex_7_155_prefix s) (positive_select s 155) (lex_7_155_image s)

theorem lex_7_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3520), (Sat.Literal.pos 3519)] :=
  (lex_7_155_gate s).prop _ (List.Mem.head _)

theorem lex_7_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3520), (Sat.Literal.neg 155), (Sat.Literal.pos 55)] :=
  (lex_7_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3520), (Sat.Literal.pos 155), (Sat.Literal.neg 55)] :=
  (lex_7_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3519), (Sat.Literal.neg 155), (Sat.Literal.neg 55), (Sat.Literal.pos 3520)] :=
  (lex_7_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3519), (Sat.Literal.pos 155), (Sat.Literal.pos 55), (Sat.Literal.pos 3520)] :=
  (lex_7_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3520) = lexBefore s permutation7 154 := by
  exact (positive_lex_of_descriptor s 3520 permutation7 155 (by rfl)).trans ((lex_skipped s permutation7 154 155 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation7 154) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation7 154 by rw [image7_eq]; rfl))

theorem lex_7_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3521) (Sat.Literal.pos 3520) (Sat.Literal.pos 154) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation7 154 (assignment s)
    (Sat.Literal.pos 3521) (Sat.Literal.pos 3520) (Sat.Literal.pos 154) (Sat.Literal.pos 53) (positive_of_descriptor s 3521 (.lex permutation7 154) (by rfl)) (lex_7_154_prefix s) (positive_select s 154) (lex_7_154_image s)

theorem lex_7_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3520), (Sat.Literal.pos 154), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation7 154 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3520) (Sat.Literal.pos 154) (Sat.Literal.pos 53) (lex_7_154_prefix s) (positive_select s 154) (lex_7_154_image s)

theorem lex_7_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3521), (Sat.Literal.pos 3520)] :=
  (lex_7_154_gate s).prop _ (List.Mem.head _)

theorem lex_7_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3521), (Sat.Literal.neg 154), (Sat.Literal.pos 53)] :=
  (lex_7_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3521), (Sat.Literal.pos 154), (Sat.Literal.neg 53)] :=
  (lex_7_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3520), (Sat.Literal.neg 154), (Sat.Literal.neg 53), (Sat.Literal.pos 3521)] :=
  (lex_7_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3520), (Sat.Literal.pos 154), (Sat.Literal.pos 53), (Sat.Literal.pos 3521)] :=
  (lex_7_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3521) = lexBefore s permutation7 153 := by
  exact (positive_lex_of_descriptor s 3521 permutation7 154 (by rfl)).trans ((lex_skipped s permutation7 153 154 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation7 153) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation7 153 by rw [image7_eq]; rfl))

theorem lex_7_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3522) (Sat.Literal.pos 3521) (Sat.Literal.pos 153) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation7 153 (assignment s)
    (Sat.Literal.pos 3522) (Sat.Literal.pos 3521) (Sat.Literal.pos 153) (Sat.Literal.pos 51) (positive_of_descriptor s 3522 (.lex permutation7 153) (by rfl)) (lex_7_153_prefix s) (positive_select s 153) (lex_7_153_image s)

theorem lex_7_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3521), (Sat.Literal.pos 153), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation7 153 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3521) (Sat.Literal.pos 153) (Sat.Literal.pos 51) (lex_7_153_prefix s) (positive_select s 153) (lex_7_153_image s)

theorem lex_7_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3522), (Sat.Literal.pos 3521)] :=
  (lex_7_153_gate s).prop _ (List.Mem.head _)

theorem lex_7_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3522), (Sat.Literal.neg 153), (Sat.Literal.pos 51)] :=
  (lex_7_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3522), (Sat.Literal.pos 153), (Sat.Literal.neg 51)] :=
  (lex_7_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3521), (Sat.Literal.neg 153), (Sat.Literal.neg 51), (Sat.Literal.pos 3522)] :=
  (lex_7_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3521), (Sat.Literal.pos 153), (Sat.Literal.pos 51), (Sat.Literal.pos 3522)] :=
  (lex_7_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3522) = lexBefore s permutation7 152 := by
  exact (positive_lex_of_descriptor s 3522 permutation7 153 (by rfl)).trans ((lex_skipped s permutation7 152 153 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 49) = s (permuteMask permutation7 152) := by
  exact (positive_select s 49).trans (congrArg s (show (49 : Fin 256) = permuteMask permutation7 152 by rw [image7_eq]; rfl))

theorem lex_7_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3523) (Sat.Literal.pos 3522) (Sat.Literal.pos 152) (Sat.Literal.pos 49)) := by
  exact equality_gate s permutation7 152 (assignment s)
    (Sat.Literal.pos 3523) (Sat.Literal.pos 3522) (Sat.Literal.pos 152) (Sat.Literal.pos 49) (positive_of_descriptor s 3523 (.lex permutation7 152) (by rfl)) (lex_7_152_prefix s) (positive_select s 152) (lex_7_152_image s)

theorem lex_7_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3522), (Sat.Literal.pos 152), (Sat.Literal.neg 49)] := by
  exact comparison_gate s permutation7 152 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3522) (Sat.Literal.pos 152) (Sat.Literal.pos 49) (lex_7_152_prefix s) (positive_select s 152) (lex_7_152_image s)

theorem lex_7_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3523), (Sat.Literal.pos 3522)] :=
  (lex_7_152_gate s).prop _ (List.Mem.head _)

theorem lex_7_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3523), (Sat.Literal.neg 152), (Sat.Literal.pos 49)] :=
  (lex_7_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3523), (Sat.Literal.pos 152), (Sat.Literal.neg 49)] :=
  (lex_7_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3522), (Sat.Literal.neg 152), (Sat.Literal.neg 49), (Sat.Literal.pos 3523)] :=
  (lex_7_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3522), (Sat.Literal.pos 152), (Sat.Literal.pos 49), (Sat.Literal.pos 3523)] :=
  (lex_7_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3523) = lexBefore s permutation7 151 := by
  exact (positive_lex_of_descriptor s 3523 permutation7 152 (by rfl)).trans ((lex_skipped s permutation7 151 152 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 47) = s (permuteMask permutation7 151) := by
  exact (positive_select s 47).trans (congrArg s (show (47 : Fin 256) = permuteMask permutation7 151 by rw [image7_eq]; rfl))

theorem lex_7_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3524) (Sat.Literal.pos 3523) (Sat.Literal.pos 151) (Sat.Literal.pos 47)) := by
  exact equality_gate s permutation7 151 (assignment s)
    (Sat.Literal.pos 3524) (Sat.Literal.pos 3523) (Sat.Literal.pos 151) (Sat.Literal.pos 47) (positive_of_descriptor s 3524 (.lex permutation7 151) (by rfl)) (lex_7_151_prefix s) (positive_select s 151) (lex_7_151_image s)

theorem lex_7_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3523), (Sat.Literal.pos 151), (Sat.Literal.neg 47)] := by
  exact comparison_gate s permutation7 151 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3523) (Sat.Literal.pos 151) (Sat.Literal.pos 47) (lex_7_151_prefix s) (positive_select s 151) (lex_7_151_image s)

theorem lex_7_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3524), (Sat.Literal.pos 3523)] :=
  (lex_7_151_gate s).prop _ (List.Mem.head _)

theorem lex_7_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3524), (Sat.Literal.neg 151), (Sat.Literal.pos 47)] :=
  (lex_7_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3524), (Sat.Literal.pos 151), (Sat.Literal.neg 47)] :=
  (lex_7_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3523), (Sat.Literal.neg 151), (Sat.Literal.neg 47), (Sat.Literal.pos 3524)] :=
  (lex_7_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3523), (Sat.Literal.pos 151), (Sat.Literal.pos 47), (Sat.Literal.pos 3524)] :=
  (lex_7_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_7_250_gate

end Crown.CertificateData
