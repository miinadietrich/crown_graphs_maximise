import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_11_250_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4424) = lexBefore s permutation11 250 := by
  exact (positive_lex_of_descriptor s 4424 permutation11 251 (by rfl)).trans ((lex_skipped s permutation11 250 251 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 251 251 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_250_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation11 250) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation11 250 by rw [image11_eq]; rfl))

theorem lex_11_250_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4425) (Sat.Literal.pos 4424) (Sat.Literal.pos 250) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation11 250 (assignment s)
    (Sat.Literal.pos 4425) (Sat.Literal.pos 4424) (Sat.Literal.pos 250) (Sat.Literal.pos 95) (positive_of_descriptor s 4425 (.lex permutation11 250) (by rfl)) (lex_11_250_prefix s) (positive_select s 250) (lex_11_250_image s)

theorem lex_11_250_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4424), (Sat.Literal.pos 250), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation11 250 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4424) (Sat.Literal.pos 250) (Sat.Literal.pos 95) (lex_11_250_prefix s) (positive_select s 250) (lex_11_250_image s)

theorem lex_11_250_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4425), (Sat.Literal.pos 4424)] :=
  (lex_11_250_gate s).prop _ (List.Mem.head _)

theorem lex_11_250_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4425), (Sat.Literal.neg 250), (Sat.Literal.pos 95)] :=
  (lex_11_250_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_250_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4425), (Sat.Literal.pos 250), (Sat.Literal.neg 95)] :=
  (lex_11_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_250_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4424), (Sat.Literal.neg 250), (Sat.Literal.neg 95), (Sat.Literal.pos 4425)] :=
  (lex_11_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_250_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4424), (Sat.Literal.pos 250), (Sat.Literal.pos 95), (Sat.Literal.pos 4425)] :=
  (lex_11_250_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_249_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4425) = lexBefore s permutation11 249 := by
  exact (positive_lex_of_descriptor s 4425 permutation11 250 (by rfl)).trans ((lex_skipped s permutation11 249 250 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 250 250 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_249_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 63) = s (permuteMask permutation11 249) := by
  exact (positive_select s 63).trans (congrArg s (show (63 : Fin 256) = permuteMask permutation11 249 by rw [image11_eq]; rfl))

theorem lex_11_249_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4426) (Sat.Literal.pos 4425) (Sat.Literal.pos 249) (Sat.Literal.pos 63)) := by
  exact equality_gate s permutation11 249 (assignment s)
    (Sat.Literal.pos 4426) (Sat.Literal.pos 4425) (Sat.Literal.pos 249) (Sat.Literal.pos 63) (positive_of_descriptor s 4426 (.lex permutation11 249) (by rfl)) (lex_11_249_prefix s) (positive_select s 249) (lex_11_249_image s)

theorem lex_11_249_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4425), (Sat.Literal.pos 249), (Sat.Literal.neg 63)] := by
  exact comparison_gate s permutation11 249 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4425) (Sat.Literal.pos 249) (Sat.Literal.pos 63) (lex_11_249_prefix s) (positive_select s 249) (lex_11_249_image s)

theorem lex_11_249_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4426), (Sat.Literal.pos 4425)] :=
  (lex_11_249_gate s).prop _ (List.Mem.head _)

theorem lex_11_249_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4426), (Sat.Literal.neg 249), (Sat.Literal.pos 63)] :=
  (lex_11_249_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_249_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4426), (Sat.Literal.pos 249), (Sat.Literal.neg 63)] :=
  (lex_11_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_249_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4425), (Sat.Literal.neg 249), (Sat.Literal.neg 63), (Sat.Literal.pos 4426)] :=
  (lex_11_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_249_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4425), (Sat.Literal.pos 249), (Sat.Literal.pos 63), (Sat.Literal.pos 4426)] :=
  (lex_11_249_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_248_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4426) = lexBefore s permutation11 248 := by
  exact (positive_lex_of_descriptor s 4426 permutation11 249 (by rfl)).trans ((lex_skipped s permutation11 248 249 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 249 249 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_248_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 31) = s (permuteMask permutation11 248) := by
  exact (positive_select s 31).trans (congrArg s (show (31 : Fin 256) = permuteMask permutation11 248 by rw [image11_eq]; rfl))

theorem lex_11_248_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4427) (Sat.Literal.pos 4426) (Sat.Literal.pos 248) (Sat.Literal.pos 31)) := by
  exact equality_gate s permutation11 248 (assignment s)
    (Sat.Literal.pos 4427) (Sat.Literal.pos 4426) (Sat.Literal.pos 248) (Sat.Literal.pos 31) (positive_of_descriptor s 4427 (.lex permutation11 248) (by rfl)) (lex_11_248_prefix s) (positive_select s 248) (lex_11_248_image s)

theorem lex_11_248_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4426), (Sat.Literal.pos 248), (Sat.Literal.neg 31)] := by
  exact comparison_gate s permutation11 248 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4426) (Sat.Literal.pos 248) (Sat.Literal.pos 31) (lex_11_248_prefix s) (positive_select s 248) (lex_11_248_image s)

theorem lex_11_248_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4427), (Sat.Literal.pos 4426)] :=
  (lex_11_248_gate s).prop _ (List.Mem.head _)

theorem lex_11_248_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4427), (Sat.Literal.neg 248), (Sat.Literal.pos 31)] :=
  (lex_11_248_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_248_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4427), (Sat.Literal.pos 248), (Sat.Literal.neg 31)] :=
  (lex_11_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_248_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4426), (Sat.Literal.neg 248), (Sat.Literal.neg 31), (Sat.Literal.pos 4427)] :=
  (lex_11_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_248_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4426), (Sat.Literal.pos 248), (Sat.Literal.pos 31), (Sat.Literal.pos 4427)] :=
  (lex_11_248_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_247_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4427) = lexBefore s permutation11 247 := by
  exact (positive_lex_of_descriptor s 4427 permutation11 248 (by rfl)).trans ((lex_skipped s permutation11 247 248 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 248 248 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_247_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 254) = s (permuteMask permutation11 247) := by
  exact (positive_select s 254).trans (congrArg s (show (254 : Fin 256) = permuteMask permutation11 247 by rw [image11_eq]; rfl))

theorem lex_11_247_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4428) (Sat.Literal.pos 4427) (Sat.Literal.pos 247) (Sat.Literal.pos 254)) := by
  exact equality_gate s permutation11 247 (assignment s)
    (Sat.Literal.pos 4428) (Sat.Literal.pos 4427) (Sat.Literal.pos 247) (Sat.Literal.pos 254) (positive_of_descriptor s 4428 (.lex permutation11 247) (by rfl)) (lex_11_247_prefix s) (positive_select s 247) (lex_11_247_image s)

theorem lex_11_247_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4427), (Sat.Literal.pos 247), (Sat.Literal.neg 254)] := by
  exact comparison_gate s permutation11 247 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4427) (Sat.Literal.pos 247) (Sat.Literal.pos 254) (lex_11_247_prefix s) (positive_select s 247) (lex_11_247_image s)

theorem lex_11_247_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4428), (Sat.Literal.pos 4427)] :=
  (lex_11_247_gate s).prop _ (List.Mem.head _)

theorem lex_11_247_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4428), (Sat.Literal.neg 247), (Sat.Literal.pos 254)] :=
  (lex_11_247_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_247_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4428), (Sat.Literal.pos 247), (Sat.Literal.neg 254)] :=
  (lex_11_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_247_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4427), (Sat.Literal.neg 247), (Sat.Literal.neg 254), (Sat.Literal.pos 4428)] :=
  (lex_11_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_247_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4427), (Sat.Literal.pos 247), (Sat.Literal.pos 254), (Sat.Literal.pos 4428)] :=
  (lex_11_247_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_246_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4428) = lexBefore s permutation11 246 := by
  exact (positive_lex_of_descriptor s 4428 permutation11 247 (by rfl)).trans ((lex_skipped s permutation11 246 247 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 247 247 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_246_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 222) = s (permuteMask permutation11 246) := by
  exact (positive_select s 222).trans (congrArg s (show (222 : Fin 256) = permuteMask permutation11 246 by rw [image11_eq]; rfl))

theorem lex_11_246_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4429) (Sat.Literal.pos 4428) (Sat.Literal.pos 246) (Sat.Literal.pos 222)) := by
  exact equality_gate s permutation11 246 (assignment s)
    (Sat.Literal.pos 4429) (Sat.Literal.pos 4428) (Sat.Literal.pos 246) (Sat.Literal.pos 222) (positive_of_descriptor s 4429 (.lex permutation11 246) (by rfl)) (lex_11_246_prefix s) (positive_select s 246) (lex_11_246_image s)

theorem lex_11_246_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4428), (Sat.Literal.pos 246), (Sat.Literal.neg 222)] := by
  exact comparison_gate s permutation11 246 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4428) (Sat.Literal.pos 246) (Sat.Literal.pos 222) (lex_11_246_prefix s) (positive_select s 246) (lex_11_246_image s)

theorem lex_11_246_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4429), (Sat.Literal.pos 4428)] :=
  (lex_11_246_gate s).prop _ (List.Mem.head _)

theorem lex_11_246_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4429), (Sat.Literal.neg 246), (Sat.Literal.pos 222)] :=
  (lex_11_246_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_246_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4429), (Sat.Literal.pos 246), (Sat.Literal.neg 222)] :=
  (lex_11_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_246_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4428), (Sat.Literal.neg 246), (Sat.Literal.neg 222), (Sat.Literal.pos 4429)] :=
  (lex_11_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_246_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4428), (Sat.Literal.pos 246), (Sat.Literal.pos 222), (Sat.Literal.pos 4429)] :=
  (lex_11_246_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_245_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4429) = lexBefore s permutation11 245 := by
  exact (positive_lex_of_descriptor s 4429 permutation11 246 (by rfl)).trans ((lex_skipped s permutation11 245 246 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 246 246 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_245_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation11 245) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation11 245 by rw [image11_eq]; rfl))

theorem lex_11_245_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4430) (Sat.Literal.pos 4429) (Sat.Literal.pos 245) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation11 245 (assignment s)
    (Sat.Literal.pos 4430) (Sat.Literal.pos 4429) (Sat.Literal.pos 245) (Sat.Literal.pos 190) (positive_of_descriptor s 4430 (.lex permutation11 245) (by rfl)) (lex_11_245_prefix s) (positive_select s 245) (lex_11_245_image s)

theorem lex_11_245_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4429), (Sat.Literal.pos 245), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation11 245 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4429) (Sat.Literal.pos 245) (Sat.Literal.pos 190) (lex_11_245_prefix s) (positive_select s 245) (lex_11_245_image s)

theorem lex_11_245_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4430), (Sat.Literal.pos 4429)] :=
  (lex_11_245_gate s).prop _ (List.Mem.head _)

theorem lex_11_245_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4430), (Sat.Literal.neg 245), (Sat.Literal.pos 190)] :=
  (lex_11_245_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_245_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4430), (Sat.Literal.pos 245), (Sat.Literal.neg 190)] :=
  (lex_11_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_245_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4429), (Sat.Literal.neg 245), (Sat.Literal.neg 190), (Sat.Literal.pos 4430)] :=
  (lex_11_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_245_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4429), (Sat.Literal.pos 245), (Sat.Literal.pos 190), (Sat.Literal.pos 4430)] :=
  (lex_11_245_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_244_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4430) = lexBefore s permutation11 244 := by
  exact (positive_lex_of_descriptor s 4430 permutation11 245 (by rfl)).trans ((lex_skipped s permutation11 244 245 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 245 245 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_244_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation11 244) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation11 244 by rw [image11_eq]; rfl))

theorem lex_11_244_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4431) (Sat.Literal.pos 4430) (Sat.Literal.pos 244) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation11 244 (assignment s)
    (Sat.Literal.pos 4431) (Sat.Literal.pos 4430) (Sat.Literal.pos 244) (Sat.Literal.pos 158) (positive_of_descriptor s 4431 (.lex permutation11 244) (by rfl)) (lex_11_244_prefix s) (positive_select s 244) (lex_11_244_image s)

theorem lex_11_244_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4430), (Sat.Literal.pos 244), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation11 244 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4430) (Sat.Literal.pos 244) (Sat.Literal.pos 158) (lex_11_244_prefix s) (positive_select s 244) (lex_11_244_image s)

theorem lex_11_244_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4431), (Sat.Literal.pos 4430)] :=
  (lex_11_244_gate s).prop _ (List.Mem.head _)

theorem lex_11_244_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4431), (Sat.Literal.neg 244), (Sat.Literal.pos 158)] :=
  (lex_11_244_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_244_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4431), (Sat.Literal.pos 244), (Sat.Literal.neg 158)] :=
  (lex_11_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_244_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4430), (Sat.Literal.neg 244), (Sat.Literal.neg 158), (Sat.Literal.pos 4431)] :=
  (lex_11_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_244_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4430), (Sat.Literal.pos 244), (Sat.Literal.pos 158), (Sat.Literal.pos 4431)] :=
  (lex_11_244_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_243_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4431) = lexBefore s permutation11 243 := by
  exact (positive_lex_of_descriptor s 4431 permutation11 244 (by rfl)).trans ((lex_skipped s permutation11 243 244 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 244 244 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_243_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 126) = s (permuteMask permutation11 243) := by
  exact (positive_select s 126).trans (congrArg s (show (126 : Fin 256) = permuteMask permutation11 243 by rw [image11_eq]; rfl))

theorem lex_11_243_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4432) (Sat.Literal.pos 4431) (Sat.Literal.pos 243) (Sat.Literal.pos 126)) := by
  exact equality_gate s permutation11 243 (assignment s)
    (Sat.Literal.pos 4432) (Sat.Literal.pos 4431) (Sat.Literal.pos 243) (Sat.Literal.pos 126) (positive_of_descriptor s 4432 (.lex permutation11 243) (by rfl)) (lex_11_243_prefix s) (positive_select s 243) (lex_11_243_image s)

theorem lex_11_243_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4431), (Sat.Literal.pos 243), (Sat.Literal.neg 126)] := by
  exact comparison_gate s permutation11 243 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4431) (Sat.Literal.pos 243) (Sat.Literal.pos 126) (lex_11_243_prefix s) (positive_select s 243) (lex_11_243_image s)

theorem lex_11_243_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4432), (Sat.Literal.pos 4431)] :=
  (lex_11_243_gate s).prop _ (List.Mem.head _)

theorem lex_11_243_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4432), (Sat.Literal.neg 243), (Sat.Literal.pos 126)] :=
  (lex_11_243_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_243_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4432), (Sat.Literal.pos 243), (Sat.Literal.neg 126)] :=
  (lex_11_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_243_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4431), (Sat.Literal.neg 243), (Sat.Literal.neg 126), (Sat.Literal.pos 4432)] :=
  (lex_11_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_243_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4431), (Sat.Literal.pos 243), (Sat.Literal.pos 126), (Sat.Literal.pos 4432)] :=
  (lex_11_243_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_242_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4432) = lexBefore s permutation11 242 := by
  exact (positive_lex_of_descriptor s 4432 permutation11 243 (by rfl)).trans ((lex_skipped s permutation11 242 243 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 243 243 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_242_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation11 242) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation11 242 by rw [image11_eq]; rfl))

theorem lex_11_242_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4433) (Sat.Literal.pos 4432) (Sat.Literal.pos 242) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation11 242 (assignment s)
    (Sat.Literal.pos 4433) (Sat.Literal.pos 4432) (Sat.Literal.pos 242) (Sat.Literal.pos 94) (positive_of_descriptor s 4433 (.lex permutation11 242) (by rfl)) (lex_11_242_prefix s) (positive_select s 242) (lex_11_242_image s)

theorem lex_11_242_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4432), (Sat.Literal.pos 242), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation11 242 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4432) (Sat.Literal.pos 242) (Sat.Literal.pos 94) (lex_11_242_prefix s) (positive_select s 242) (lex_11_242_image s)

theorem lex_11_242_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4433), (Sat.Literal.pos 4432)] :=
  (lex_11_242_gate s).prop _ (List.Mem.head _)

theorem lex_11_242_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4433), (Sat.Literal.neg 242), (Sat.Literal.pos 94)] :=
  (lex_11_242_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_242_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4433), (Sat.Literal.pos 242), (Sat.Literal.neg 94)] :=
  (lex_11_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_242_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4432), (Sat.Literal.neg 242), (Sat.Literal.neg 94), (Sat.Literal.pos 4433)] :=
  (lex_11_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_242_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4432), (Sat.Literal.pos 242), (Sat.Literal.pos 94), (Sat.Literal.pos 4433)] :=
  (lex_11_242_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_241_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4433) = lexBefore s permutation11 241 := by
  exact (positive_lex_of_descriptor s 4433 permutation11 242 (by rfl)).trans ((lex_skipped s permutation11 241 242 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 242 242 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_241_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 62) = s (permuteMask permutation11 241) := by
  exact (positive_select s 62).trans (congrArg s (show (62 : Fin 256) = permuteMask permutation11 241 by rw [image11_eq]; rfl))

theorem lex_11_241_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4434) (Sat.Literal.pos 4433) (Sat.Literal.pos 241) (Sat.Literal.pos 62)) := by
  exact equality_gate s permutation11 241 (assignment s)
    (Sat.Literal.pos 4434) (Sat.Literal.pos 4433) (Sat.Literal.pos 241) (Sat.Literal.pos 62) (positive_of_descriptor s 4434 (.lex permutation11 241) (by rfl)) (lex_11_241_prefix s) (positive_select s 241) (lex_11_241_image s)

theorem lex_11_241_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4433), (Sat.Literal.pos 241), (Sat.Literal.neg 62)] := by
  exact comparison_gate s permutation11 241 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4433) (Sat.Literal.pos 241) (Sat.Literal.pos 62) (lex_11_241_prefix s) (positive_select s 241) (lex_11_241_image s)

theorem lex_11_241_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4434), (Sat.Literal.pos 4433)] :=
  (lex_11_241_gate s).prop _ (List.Mem.head _)

theorem lex_11_241_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4434), (Sat.Literal.neg 241), (Sat.Literal.pos 62)] :=
  (lex_11_241_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_241_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4434), (Sat.Literal.pos 241), (Sat.Literal.neg 62)] :=
  (lex_11_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_241_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4433), (Sat.Literal.neg 241), (Sat.Literal.neg 62), (Sat.Literal.pos 4434)] :=
  (lex_11_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_241_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4433), (Sat.Literal.pos 241), (Sat.Literal.pos 62), (Sat.Literal.pos 4434)] :=
  (lex_11_241_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_240_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4434) = lexBefore s permutation11 240 := by
  exact (positive_lex_of_descriptor s 4434 permutation11 241 (by rfl)).trans ((lex_skipped s permutation11 240 241 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 241 241 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_240_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 30) = s (permuteMask permutation11 240) := by
  exact (positive_select s 30).trans (congrArg s (show (30 : Fin 256) = permuteMask permutation11 240 by rw [image11_eq]; rfl))

theorem lex_11_240_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4435) (Sat.Literal.pos 4434) (Sat.Literal.pos 240) (Sat.Literal.pos 30)) := by
  exact equality_gate s permutation11 240 (assignment s)
    (Sat.Literal.pos 4435) (Sat.Literal.pos 4434) (Sat.Literal.pos 240) (Sat.Literal.pos 30) (positive_of_descriptor s 4435 (.lex permutation11 240) (by rfl)) (lex_11_240_prefix s) (positive_select s 240) (lex_11_240_image s)

theorem lex_11_240_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4434), (Sat.Literal.pos 240), (Sat.Literal.neg 30)] := by
  exact comparison_gate s permutation11 240 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4434) (Sat.Literal.pos 240) (Sat.Literal.pos 30) (lex_11_240_prefix s) (positive_select s 240) (lex_11_240_image s)

theorem lex_11_240_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4435), (Sat.Literal.pos 4434)] :=
  (lex_11_240_gate s).prop _ (List.Mem.head _)

theorem lex_11_240_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4435), (Sat.Literal.neg 240), (Sat.Literal.pos 30)] :=
  (lex_11_240_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_240_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4435), (Sat.Literal.pos 240), (Sat.Literal.neg 30)] :=
  (lex_11_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_240_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4434), (Sat.Literal.neg 240), (Sat.Literal.neg 30), (Sat.Literal.pos 4435)] :=
  (lex_11_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_240_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4434), (Sat.Literal.pos 240), (Sat.Literal.pos 30), (Sat.Literal.pos 4435)] :=
  (lex_11_240_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_239_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4435) = lexBefore s permutation11 239 := by
  exact (positive_lex_of_descriptor s 4435 permutation11 240 (by rfl)).trans ((lex_skipped s permutation11 239 240 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 240 240 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_239_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation11 239) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation11 239 by rw [image11_eq]; rfl))

theorem lex_11_239_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4436) (Sat.Literal.pos 4435) (Sat.Literal.pos 239) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation11 239 (assignment s)
    (Sat.Literal.pos 4436) (Sat.Literal.pos 4435) (Sat.Literal.pos 239) (Sat.Literal.pos 253) (positive_of_descriptor s 4436 (.lex permutation11 239) (by rfl)) (lex_11_239_prefix s) (positive_select s 239) (lex_11_239_image s)

theorem lex_11_239_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4435), (Sat.Literal.pos 239), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation11 239 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4435) (Sat.Literal.pos 239) (Sat.Literal.pos 253) (lex_11_239_prefix s) (positive_select s 239) (lex_11_239_image s)

theorem lex_11_239_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4436), (Sat.Literal.pos 4435)] :=
  (lex_11_239_gate s).prop _ (List.Mem.head _)

theorem lex_11_239_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4436), (Sat.Literal.neg 239), (Sat.Literal.pos 253)] :=
  (lex_11_239_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_239_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4436), (Sat.Literal.pos 239), (Sat.Literal.neg 253)] :=
  (lex_11_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_239_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4435), (Sat.Literal.neg 239), (Sat.Literal.neg 253), (Sat.Literal.pos 4436)] :=
  (lex_11_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_239_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4435), (Sat.Literal.pos 239), (Sat.Literal.pos 253), (Sat.Literal.pos 4436)] :=
  (lex_11_239_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_238_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4436) = lexBefore s permutation11 238 := by
  exact (positive_lex_of_descriptor s 4436 permutation11 239 (by rfl)).trans ((lex_skipped s permutation11 238 239 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 239 239 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_238_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 221) = s (permuteMask permutation11 238) := by
  exact (positive_select s 221).trans (congrArg s (show (221 : Fin 256) = permuteMask permutation11 238 by rw [image11_eq]; rfl))

theorem lex_11_238_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4437) (Sat.Literal.pos 4436) (Sat.Literal.pos 238) (Sat.Literal.pos 221)) := by
  exact equality_gate s permutation11 238 (assignment s)
    (Sat.Literal.pos 4437) (Sat.Literal.pos 4436) (Sat.Literal.pos 238) (Sat.Literal.pos 221) (positive_of_descriptor s 4437 (.lex permutation11 238) (by rfl)) (lex_11_238_prefix s) (positive_select s 238) (lex_11_238_image s)

theorem lex_11_238_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4436), (Sat.Literal.pos 238), (Sat.Literal.neg 221)] := by
  exact comparison_gate s permutation11 238 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4436) (Sat.Literal.pos 238) (Sat.Literal.pos 221) (lex_11_238_prefix s) (positive_select s 238) (lex_11_238_image s)

theorem lex_11_238_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4437), (Sat.Literal.pos 4436)] :=
  (lex_11_238_gate s).prop _ (List.Mem.head _)

theorem lex_11_238_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4437), (Sat.Literal.neg 238), (Sat.Literal.pos 221)] :=
  (lex_11_238_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_238_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4437), (Sat.Literal.pos 238), (Sat.Literal.neg 221)] :=
  (lex_11_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_238_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4436), (Sat.Literal.neg 238), (Sat.Literal.neg 221), (Sat.Literal.pos 4437)] :=
  (lex_11_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_238_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4436), (Sat.Literal.pos 238), (Sat.Literal.pos 221), (Sat.Literal.pos 4437)] :=
  (lex_11_238_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_237_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4437) = lexBefore s permutation11 237 := by
  exact (positive_lex_of_descriptor s 4437 permutation11 238 (by rfl)).trans ((lex_skipped s permutation11 237 238 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 238 238 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_237_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation11 237) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation11 237 by rw [image11_eq]; rfl))

theorem lex_11_237_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4438) (Sat.Literal.pos 4437) (Sat.Literal.pos 237) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation11 237 (assignment s)
    (Sat.Literal.pos 4438) (Sat.Literal.pos 4437) (Sat.Literal.pos 237) (Sat.Literal.pos 189) (positive_of_descriptor s 4438 (.lex permutation11 237) (by rfl)) (lex_11_237_prefix s) (positive_select s 237) (lex_11_237_image s)

theorem lex_11_237_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4437), (Sat.Literal.pos 237), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation11 237 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4437) (Sat.Literal.pos 237) (Sat.Literal.pos 189) (lex_11_237_prefix s) (positive_select s 237) (lex_11_237_image s)

theorem lex_11_237_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4438), (Sat.Literal.pos 4437)] :=
  (lex_11_237_gate s).prop _ (List.Mem.head _)

theorem lex_11_237_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4438), (Sat.Literal.neg 237), (Sat.Literal.pos 189)] :=
  (lex_11_237_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_237_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4438), (Sat.Literal.pos 237), (Sat.Literal.neg 189)] :=
  (lex_11_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_237_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4437), (Sat.Literal.neg 237), (Sat.Literal.neg 189), (Sat.Literal.pos 4438)] :=
  (lex_11_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_237_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4437), (Sat.Literal.pos 237), (Sat.Literal.pos 189), (Sat.Literal.pos 4438)] :=
  (lex_11_237_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_236_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4438) = lexBefore s permutation11 236 := by
  exact (positive_lex_of_descriptor s 4438 permutation11 237 (by rfl)).trans ((lex_skipped s permutation11 236 237 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 237 237 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_236_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation11 236) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation11 236 by rw [image11_eq]; rfl))

theorem lex_11_236_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4439) (Sat.Literal.pos 4438) (Sat.Literal.pos 236) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation11 236 (assignment s)
    (Sat.Literal.pos 4439) (Sat.Literal.pos 4438) (Sat.Literal.pos 236) (Sat.Literal.pos 157) (positive_of_descriptor s 4439 (.lex permutation11 236) (by rfl)) (lex_11_236_prefix s) (positive_select s 236) (lex_11_236_image s)

theorem lex_11_236_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4438), (Sat.Literal.pos 236), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation11 236 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4438) (Sat.Literal.pos 236) (Sat.Literal.pos 157) (lex_11_236_prefix s) (positive_select s 236) (lex_11_236_image s)

theorem lex_11_236_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4439), (Sat.Literal.pos 4438)] :=
  (lex_11_236_gate s).prop _ (List.Mem.head _)

theorem lex_11_236_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4439), (Sat.Literal.neg 236), (Sat.Literal.pos 157)] :=
  (lex_11_236_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_236_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4439), (Sat.Literal.pos 236), (Sat.Literal.neg 157)] :=
  (lex_11_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_236_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4438), (Sat.Literal.neg 236), (Sat.Literal.neg 157), (Sat.Literal.pos 4439)] :=
  (lex_11_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_236_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4438), (Sat.Literal.pos 236), (Sat.Literal.pos 157), (Sat.Literal.pos 4439)] :=
  (lex_11_236_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_235_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4439) = lexBefore s permutation11 235 := by
  exact (positive_lex_of_descriptor s 4439 permutation11 236 (by rfl)).trans ((lex_skipped s permutation11 235 236 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 236 236 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_235_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 125) = s (permuteMask permutation11 235) := by
  exact (positive_select s 125).trans (congrArg s (show (125 : Fin 256) = permuteMask permutation11 235 by rw [image11_eq]; rfl))

theorem lex_11_235_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4440) (Sat.Literal.pos 4439) (Sat.Literal.pos 235) (Sat.Literal.pos 125)) := by
  exact equality_gate s permutation11 235 (assignment s)
    (Sat.Literal.pos 4440) (Sat.Literal.pos 4439) (Sat.Literal.pos 235) (Sat.Literal.pos 125) (positive_of_descriptor s 4440 (.lex permutation11 235) (by rfl)) (lex_11_235_prefix s) (positive_select s 235) (lex_11_235_image s)

theorem lex_11_235_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4439), (Sat.Literal.pos 235), (Sat.Literal.neg 125)] := by
  exact comparison_gate s permutation11 235 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4439) (Sat.Literal.pos 235) (Sat.Literal.pos 125) (lex_11_235_prefix s) (positive_select s 235) (lex_11_235_image s)

theorem lex_11_235_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4440), (Sat.Literal.pos 4439)] :=
  (lex_11_235_gate s).prop _ (List.Mem.head _)

theorem lex_11_235_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4440), (Sat.Literal.neg 235), (Sat.Literal.pos 125)] :=
  (lex_11_235_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_235_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4440), (Sat.Literal.pos 235), (Sat.Literal.neg 125)] :=
  (lex_11_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_235_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4439), (Sat.Literal.neg 235), (Sat.Literal.neg 125), (Sat.Literal.pos 4440)] :=
  (lex_11_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_235_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4439), (Sat.Literal.pos 235), (Sat.Literal.pos 125), (Sat.Literal.pos 4440)] :=
  (lex_11_235_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_234_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4440) = lexBefore s permutation11 234 := by
  exact (positive_lex_of_descriptor s 4440 permutation11 235 (by rfl)).trans ((lex_skipped s permutation11 234 235 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 235 235 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_234_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation11 234) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation11 234 by rw [image11_eq]; rfl))

theorem lex_11_234_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4441) (Sat.Literal.pos 4440) (Sat.Literal.pos 234) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation11 234 (assignment s)
    (Sat.Literal.pos 4441) (Sat.Literal.pos 4440) (Sat.Literal.pos 234) (Sat.Literal.pos 93) (positive_of_descriptor s 4441 (.lex permutation11 234) (by rfl)) (lex_11_234_prefix s) (positive_select s 234) (lex_11_234_image s)

theorem lex_11_234_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4440), (Sat.Literal.pos 234), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation11 234 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4440) (Sat.Literal.pos 234) (Sat.Literal.pos 93) (lex_11_234_prefix s) (positive_select s 234) (lex_11_234_image s)

theorem lex_11_234_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4441), (Sat.Literal.pos 4440)] :=
  (lex_11_234_gate s).prop _ (List.Mem.head _)

theorem lex_11_234_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4441), (Sat.Literal.neg 234), (Sat.Literal.pos 93)] :=
  (lex_11_234_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_234_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4441), (Sat.Literal.pos 234), (Sat.Literal.neg 93)] :=
  (lex_11_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_234_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4440), (Sat.Literal.neg 234), (Sat.Literal.neg 93), (Sat.Literal.pos 4441)] :=
  (lex_11_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_234_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4440), (Sat.Literal.pos 234), (Sat.Literal.pos 93), (Sat.Literal.pos 4441)] :=
  (lex_11_234_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_233_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4441) = lexBefore s permutation11 233 := by
  exact (positive_lex_of_descriptor s 4441 permutation11 234 (by rfl)).trans ((lex_skipped s permutation11 233 234 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 234 234 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_233_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 61) = s (permuteMask permutation11 233) := by
  exact (positive_select s 61).trans (congrArg s (show (61 : Fin 256) = permuteMask permutation11 233 by rw [image11_eq]; rfl))

theorem lex_11_233_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4442) (Sat.Literal.pos 4441) (Sat.Literal.pos 233) (Sat.Literal.pos 61)) := by
  exact equality_gate s permutation11 233 (assignment s)
    (Sat.Literal.pos 4442) (Sat.Literal.pos 4441) (Sat.Literal.pos 233) (Sat.Literal.pos 61) (positive_of_descriptor s 4442 (.lex permutation11 233) (by rfl)) (lex_11_233_prefix s) (positive_select s 233) (lex_11_233_image s)

theorem lex_11_233_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4441), (Sat.Literal.pos 233), (Sat.Literal.neg 61)] := by
  exact comparison_gate s permutation11 233 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4441) (Sat.Literal.pos 233) (Sat.Literal.pos 61) (lex_11_233_prefix s) (positive_select s 233) (lex_11_233_image s)

theorem lex_11_233_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4442), (Sat.Literal.pos 4441)] :=
  (lex_11_233_gate s).prop _ (List.Mem.head _)

theorem lex_11_233_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4442), (Sat.Literal.neg 233), (Sat.Literal.pos 61)] :=
  (lex_11_233_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_233_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4442), (Sat.Literal.pos 233), (Sat.Literal.neg 61)] :=
  (lex_11_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_233_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4441), (Sat.Literal.neg 233), (Sat.Literal.neg 61), (Sat.Literal.pos 4442)] :=
  (lex_11_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_233_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4441), (Sat.Literal.pos 233), (Sat.Literal.pos 61), (Sat.Literal.pos 4442)] :=
  (lex_11_233_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_232_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4442) = lexBefore s permutation11 232 := by
  exact (positive_lex_of_descriptor s 4442 permutation11 233 (by rfl)).trans ((lex_skipped s permutation11 232 233 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 233 233 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_232_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 29) = s (permuteMask permutation11 232) := by
  exact (positive_select s 29).trans (congrArg s (show (29 : Fin 256) = permuteMask permutation11 232 by rw [image11_eq]; rfl))

theorem lex_11_232_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4443) (Sat.Literal.pos 4442) (Sat.Literal.pos 232) (Sat.Literal.pos 29)) := by
  exact equality_gate s permutation11 232 (assignment s)
    (Sat.Literal.pos 4443) (Sat.Literal.pos 4442) (Sat.Literal.pos 232) (Sat.Literal.pos 29) (positive_of_descriptor s 4443 (.lex permutation11 232) (by rfl)) (lex_11_232_prefix s) (positive_select s 232) (lex_11_232_image s)

theorem lex_11_232_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4442), (Sat.Literal.pos 232), (Sat.Literal.neg 29)] := by
  exact comparison_gate s permutation11 232 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4442) (Sat.Literal.pos 232) (Sat.Literal.pos 29) (lex_11_232_prefix s) (positive_select s 232) (lex_11_232_image s)

theorem lex_11_232_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4443), (Sat.Literal.pos 4442)] :=
  (lex_11_232_gate s).prop _ (List.Mem.head _)

theorem lex_11_232_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4443), (Sat.Literal.neg 232), (Sat.Literal.pos 29)] :=
  (lex_11_232_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_232_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4443), (Sat.Literal.pos 232), (Sat.Literal.neg 29)] :=
  (lex_11_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_232_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4442), (Sat.Literal.neg 232), (Sat.Literal.neg 29), (Sat.Literal.pos 4443)] :=
  (lex_11_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_232_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4442), (Sat.Literal.pos 232), (Sat.Literal.pos 29), (Sat.Literal.pos 4443)] :=
  (lex_11_232_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_231_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4443) = lexBefore s permutation11 231 := by
  exact (positive_lex_of_descriptor s 4443 permutation11 232 (by rfl)).trans ((lex_skipped s permutation11 231 232 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 232 232 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_231_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 252) = s (permuteMask permutation11 231) := by
  exact (positive_select s 252).trans (congrArg s (show (252 : Fin 256) = permuteMask permutation11 231 by rw [image11_eq]; rfl))

theorem lex_11_231_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4444) (Sat.Literal.pos 4443) (Sat.Literal.pos 231) (Sat.Literal.pos 252)) := by
  exact equality_gate s permutation11 231 (assignment s)
    (Sat.Literal.pos 4444) (Sat.Literal.pos 4443) (Sat.Literal.pos 231) (Sat.Literal.pos 252) (positive_of_descriptor s 4444 (.lex permutation11 231) (by rfl)) (lex_11_231_prefix s) (positive_select s 231) (lex_11_231_image s)

theorem lex_11_231_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4443), (Sat.Literal.pos 231), (Sat.Literal.neg 252)] := by
  exact comparison_gate s permutation11 231 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4443) (Sat.Literal.pos 231) (Sat.Literal.pos 252) (lex_11_231_prefix s) (positive_select s 231) (lex_11_231_image s)

theorem lex_11_231_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4444), (Sat.Literal.pos 4443)] :=
  (lex_11_231_gate s).prop _ (List.Mem.head _)

theorem lex_11_231_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4444), (Sat.Literal.neg 231), (Sat.Literal.pos 252)] :=
  (lex_11_231_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_231_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4444), (Sat.Literal.pos 231), (Sat.Literal.neg 252)] :=
  (lex_11_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_231_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4443), (Sat.Literal.neg 231), (Sat.Literal.neg 252), (Sat.Literal.pos 4444)] :=
  (lex_11_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_231_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4443), (Sat.Literal.pos 231), (Sat.Literal.pos 252), (Sat.Literal.pos 4444)] :=
  (lex_11_231_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_230_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4444) = lexBefore s permutation11 230 := by
  exact (positive_lex_of_descriptor s 4444 permutation11 231 (by rfl)).trans ((lex_skipped s permutation11 230 231 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 231 231 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_230_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 220) = s (permuteMask permutation11 230) := by
  exact (positive_select s 220).trans (congrArg s (show (220 : Fin 256) = permuteMask permutation11 230 by rw [image11_eq]; rfl))

theorem lex_11_230_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4445) (Sat.Literal.pos 4444) (Sat.Literal.pos 230) (Sat.Literal.pos 220)) := by
  exact equality_gate s permutation11 230 (assignment s)
    (Sat.Literal.pos 4445) (Sat.Literal.pos 4444) (Sat.Literal.pos 230) (Sat.Literal.pos 220) (positive_of_descriptor s 4445 (.lex permutation11 230) (by rfl)) (lex_11_230_prefix s) (positive_select s 230) (lex_11_230_image s)

theorem lex_11_230_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4444), (Sat.Literal.pos 230), (Sat.Literal.neg 220)] := by
  exact comparison_gate s permutation11 230 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4444) (Sat.Literal.pos 230) (Sat.Literal.pos 220) (lex_11_230_prefix s) (positive_select s 230) (lex_11_230_image s)

theorem lex_11_230_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4445), (Sat.Literal.pos 4444)] :=
  (lex_11_230_gate s).prop _ (List.Mem.head _)

theorem lex_11_230_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4445), (Sat.Literal.neg 230), (Sat.Literal.pos 220)] :=
  (lex_11_230_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_230_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4445), (Sat.Literal.pos 230), (Sat.Literal.neg 220)] :=
  (lex_11_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_230_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4444), (Sat.Literal.neg 230), (Sat.Literal.neg 220), (Sat.Literal.pos 4445)] :=
  (lex_11_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_230_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4444), (Sat.Literal.pos 230), (Sat.Literal.pos 220), (Sat.Literal.pos 4445)] :=
  (lex_11_230_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_229_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4445) = lexBefore s permutation11 229 := by
  exact (positive_lex_of_descriptor s 4445 permutation11 230 (by rfl)).trans ((lex_skipped s permutation11 229 230 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 230 230 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_229_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation11 229) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation11 229 by rw [image11_eq]; rfl))

theorem lex_11_229_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4446) (Sat.Literal.pos 4445) (Sat.Literal.pos 229) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation11 229 (assignment s)
    (Sat.Literal.pos 4446) (Sat.Literal.pos 4445) (Sat.Literal.pos 229) (Sat.Literal.pos 188) (positive_of_descriptor s 4446 (.lex permutation11 229) (by rfl)) (lex_11_229_prefix s) (positive_select s 229) (lex_11_229_image s)

theorem lex_11_229_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4445), (Sat.Literal.pos 229), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation11 229 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4445) (Sat.Literal.pos 229) (Sat.Literal.pos 188) (lex_11_229_prefix s) (positive_select s 229) (lex_11_229_image s)

theorem lex_11_229_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4446), (Sat.Literal.pos 4445)] :=
  (lex_11_229_gate s).prop _ (List.Mem.head _)

theorem lex_11_229_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4446), (Sat.Literal.neg 229), (Sat.Literal.pos 188)] :=
  (lex_11_229_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_229_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4446), (Sat.Literal.pos 229), (Sat.Literal.neg 188)] :=
  (lex_11_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_229_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4445), (Sat.Literal.neg 229), (Sat.Literal.neg 188), (Sat.Literal.pos 4446)] :=
  (lex_11_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_229_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4445), (Sat.Literal.pos 229), (Sat.Literal.pos 188), (Sat.Literal.pos 4446)] :=
  (lex_11_229_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_228_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4446) = lexBefore s permutation11 228 := by
  exact (positive_lex_of_descriptor s 4446 permutation11 229 (by rfl)).trans ((lex_skipped s permutation11 228 229 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 229 229 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_228_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation11 228) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation11 228 by rw [image11_eq]; rfl))

theorem lex_11_228_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4447) (Sat.Literal.pos 4446) (Sat.Literal.pos 228) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation11 228 (assignment s)
    (Sat.Literal.pos 4447) (Sat.Literal.pos 4446) (Sat.Literal.pos 228) (Sat.Literal.pos 156) (positive_of_descriptor s 4447 (.lex permutation11 228) (by rfl)) (lex_11_228_prefix s) (positive_select s 228) (lex_11_228_image s)

theorem lex_11_228_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4446), (Sat.Literal.pos 228), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation11 228 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4446) (Sat.Literal.pos 228) (Sat.Literal.pos 156) (lex_11_228_prefix s) (positive_select s 228) (lex_11_228_image s)

theorem lex_11_228_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4447), (Sat.Literal.pos 4446)] :=
  (lex_11_228_gate s).prop _ (List.Mem.head _)

theorem lex_11_228_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4447), (Sat.Literal.neg 228), (Sat.Literal.pos 156)] :=
  (lex_11_228_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_228_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4447), (Sat.Literal.pos 228), (Sat.Literal.neg 156)] :=
  (lex_11_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_228_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4446), (Sat.Literal.neg 228), (Sat.Literal.neg 156), (Sat.Literal.pos 4447)] :=
  (lex_11_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_228_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4446), (Sat.Literal.pos 228), (Sat.Literal.pos 156), (Sat.Literal.pos 4447)] :=
  (lex_11_228_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_227_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4447) = lexBefore s permutation11 227 := by
  exact (positive_lex_of_descriptor s 4447 permutation11 228 (by rfl)).trans ((lex_skipped s permutation11 227 228 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 228 228 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_227_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 124) = s (permuteMask permutation11 227) := by
  exact (positive_select s 124).trans (congrArg s (show (124 : Fin 256) = permuteMask permutation11 227 by rw [image11_eq]; rfl))

theorem lex_11_227_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4448) (Sat.Literal.pos 4447) (Sat.Literal.pos 227) (Sat.Literal.pos 124)) := by
  exact equality_gate s permutation11 227 (assignment s)
    (Sat.Literal.pos 4448) (Sat.Literal.pos 4447) (Sat.Literal.pos 227) (Sat.Literal.pos 124) (positive_of_descriptor s 4448 (.lex permutation11 227) (by rfl)) (lex_11_227_prefix s) (positive_select s 227) (lex_11_227_image s)

theorem lex_11_227_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4447), (Sat.Literal.pos 227), (Sat.Literal.neg 124)] := by
  exact comparison_gate s permutation11 227 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4447) (Sat.Literal.pos 227) (Sat.Literal.pos 124) (lex_11_227_prefix s) (positive_select s 227) (lex_11_227_image s)

theorem lex_11_227_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4448), (Sat.Literal.pos 4447)] :=
  (lex_11_227_gate s).prop _ (List.Mem.head _)

theorem lex_11_227_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4448), (Sat.Literal.neg 227), (Sat.Literal.pos 124)] :=
  (lex_11_227_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_227_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4448), (Sat.Literal.pos 227), (Sat.Literal.neg 124)] :=
  (lex_11_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_227_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4447), (Sat.Literal.neg 227), (Sat.Literal.neg 124), (Sat.Literal.pos 4448)] :=
  (lex_11_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_227_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4447), (Sat.Literal.pos 227), (Sat.Literal.pos 124), (Sat.Literal.pos 4448)] :=
  (lex_11_227_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_226_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4448) = lexBefore s permutation11 226 := by
  exact (positive_lex_of_descriptor s 4448 permutation11 227 (by rfl)).trans ((lex_skipped s permutation11 226 227 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 227 227 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_226_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation11 226) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation11 226 by rw [image11_eq]; rfl))

theorem lex_11_226_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4449) (Sat.Literal.pos 4448) (Sat.Literal.pos 226) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation11 226 (assignment s)
    (Sat.Literal.pos 4449) (Sat.Literal.pos 4448) (Sat.Literal.pos 226) (Sat.Literal.pos 92) (positive_of_descriptor s 4449 (.lex permutation11 226) (by rfl)) (lex_11_226_prefix s) (positive_select s 226) (lex_11_226_image s)

theorem lex_11_226_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4448), (Sat.Literal.pos 226), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation11 226 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4448) (Sat.Literal.pos 226) (Sat.Literal.pos 92) (lex_11_226_prefix s) (positive_select s 226) (lex_11_226_image s)

theorem lex_11_226_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4449), (Sat.Literal.pos 4448)] :=
  (lex_11_226_gate s).prop _ (List.Mem.head _)

theorem lex_11_226_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4449), (Sat.Literal.neg 226), (Sat.Literal.pos 92)] :=
  (lex_11_226_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_226_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4449), (Sat.Literal.pos 226), (Sat.Literal.neg 92)] :=
  (lex_11_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_226_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4448), (Sat.Literal.neg 226), (Sat.Literal.neg 92), (Sat.Literal.pos 4449)] :=
  (lex_11_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_226_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4448), (Sat.Literal.pos 226), (Sat.Literal.pos 92), (Sat.Literal.pos 4449)] :=
  (lex_11_226_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_225_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4449) = lexBefore s permutation11 225 := by
  exact (positive_lex_of_descriptor s 4449 permutation11 226 (by rfl)).trans ((lex_skipped s permutation11 225 226 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 226 226 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_225_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 60) = s (permuteMask permutation11 225) := by
  exact (positive_select s 60).trans (congrArg s (show (60 : Fin 256) = permuteMask permutation11 225 by rw [image11_eq]; rfl))

theorem lex_11_225_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4450) (Sat.Literal.pos 4449) (Sat.Literal.pos 225) (Sat.Literal.pos 60)) := by
  exact equality_gate s permutation11 225 (assignment s)
    (Sat.Literal.pos 4450) (Sat.Literal.pos 4449) (Sat.Literal.pos 225) (Sat.Literal.pos 60) (positive_of_descriptor s 4450 (.lex permutation11 225) (by rfl)) (lex_11_225_prefix s) (positive_select s 225) (lex_11_225_image s)

theorem lex_11_225_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4449), (Sat.Literal.pos 225), (Sat.Literal.neg 60)] := by
  exact comparison_gate s permutation11 225 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4449) (Sat.Literal.pos 225) (Sat.Literal.pos 60) (lex_11_225_prefix s) (positive_select s 225) (lex_11_225_image s)

theorem lex_11_225_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4450), (Sat.Literal.pos 4449)] :=
  (lex_11_225_gate s).prop _ (List.Mem.head _)

theorem lex_11_225_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4450), (Sat.Literal.neg 225), (Sat.Literal.pos 60)] :=
  (lex_11_225_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_225_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4450), (Sat.Literal.pos 225), (Sat.Literal.neg 60)] :=
  (lex_11_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_225_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4449), (Sat.Literal.neg 225), (Sat.Literal.neg 60), (Sat.Literal.pos 4450)] :=
  (lex_11_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_225_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4449), (Sat.Literal.pos 225), (Sat.Literal.pos 60), (Sat.Literal.pos 4450)] :=
  (lex_11_225_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_224_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4450) = lexBefore s permutation11 224 := by
  exact (positive_lex_of_descriptor s 4450 permutation11 225 (by rfl)).trans ((lex_skipped s permutation11 224 225 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 225 225 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_224_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 28) = s (permuteMask permutation11 224) := by
  exact (positive_select s 28).trans (congrArg s (show (28 : Fin 256) = permuteMask permutation11 224 by rw [image11_eq]; rfl))

theorem lex_11_224_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4451) (Sat.Literal.pos 4450) (Sat.Literal.pos 224) (Sat.Literal.pos 28)) := by
  exact equality_gate s permutation11 224 (assignment s)
    (Sat.Literal.pos 4451) (Sat.Literal.pos 4450) (Sat.Literal.pos 224) (Sat.Literal.pos 28) (positive_of_descriptor s 4451 (.lex permutation11 224) (by rfl)) (lex_11_224_prefix s) (positive_select s 224) (lex_11_224_image s)

theorem lex_11_224_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4450), (Sat.Literal.pos 224), (Sat.Literal.neg 28)] := by
  exact comparison_gate s permutation11 224 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4450) (Sat.Literal.pos 224) (Sat.Literal.pos 28) (lex_11_224_prefix s) (positive_select s 224) (lex_11_224_image s)

theorem lex_11_224_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4451), (Sat.Literal.pos 4450)] :=
  (lex_11_224_gate s).prop _ (List.Mem.head _)

theorem lex_11_224_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4451), (Sat.Literal.neg 224), (Sat.Literal.pos 28)] :=
  (lex_11_224_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_224_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4451), (Sat.Literal.pos 224), (Sat.Literal.neg 28)] :=
  (lex_11_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_224_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4450), (Sat.Literal.neg 224), (Sat.Literal.neg 28), (Sat.Literal.pos 4451)] :=
  (lex_11_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_224_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4450), (Sat.Literal.pos 224), (Sat.Literal.pos 28), (Sat.Literal.pos 4451)] :=
  (lex_11_224_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_223_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4451) = lexBefore s permutation11 223 := by
  exact (positive_lex_of_descriptor s 4451 permutation11 224 (by rfl)).trans ((lex_skipped s permutation11 223 224 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 224 224 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_223_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation11 223) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation11 223 by rw [image11_eq]; rfl))

theorem lex_11_223_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4452) (Sat.Literal.pos 4451) (Sat.Literal.pos 223) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation11 223 (assignment s)
    (Sat.Literal.pos 4452) (Sat.Literal.pos 4451) (Sat.Literal.pos 223) (Sat.Literal.pos 251) (positive_of_descriptor s 4452 (.lex permutation11 223) (by rfl)) (lex_11_223_prefix s) (positive_select s 223) (lex_11_223_image s)

theorem lex_11_223_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4451), (Sat.Literal.pos 223), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation11 223 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4451) (Sat.Literal.pos 223) (Sat.Literal.pos 251) (lex_11_223_prefix s) (positive_select s 223) (lex_11_223_image s)

theorem lex_11_223_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4452), (Sat.Literal.pos 4451)] :=
  (lex_11_223_gate s).prop _ (List.Mem.head _)

theorem lex_11_223_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4452), (Sat.Literal.neg 223), (Sat.Literal.pos 251)] :=
  (lex_11_223_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_223_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4452), (Sat.Literal.pos 223), (Sat.Literal.neg 251)] :=
  (lex_11_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_223_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4451), (Sat.Literal.neg 223), (Sat.Literal.neg 251), (Sat.Literal.pos 4452)] :=
  (lex_11_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_223_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4451), (Sat.Literal.pos 223), (Sat.Literal.pos 251), (Sat.Literal.pos 4452)] :=
  (lex_11_223_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_222_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4452) = lexBefore s permutation11 222 := by
  exact (positive_lex_of_descriptor s 4452 permutation11 223 (by rfl)).trans ((lex_skipped s permutation11 222 223 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 223 223 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_222_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 219) = s (permuteMask permutation11 222) := by
  exact (positive_select s 219).trans (congrArg s (show (219 : Fin 256) = permuteMask permutation11 222 by rw [image11_eq]; rfl))

theorem lex_11_222_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4453) (Sat.Literal.pos 4452) (Sat.Literal.pos 222) (Sat.Literal.pos 219)) := by
  exact equality_gate s permutation11 222 (assignment s)
    (Sat.Literal.pos 4453) (Sat.Literal.pos 4452) (Sat.Literal.pos 222) (Sat.Literal.pos 219) (positive_of_descriptor s 4453 (.lex permutation11 222) (by rfl)) (lex_11_222_prefix s) (positive_select s 222) (lex_11_222_image s)

theorem lex_11_222_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4452), (Sat.Literal.pos 222), (Sat.Literal.neg 219)] := by
  exact comparison_gate s permutation11 222 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4452) (Sat.Literal.pos 222) (Sat.Literal.pos 219) (lex_11_222_prefix s) (positive_select s 222) (lex_11_222_image s)

theorem lex_11_222_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4453), (Sat.Literal.pos 4452)] :=
  (lex_11_222_gate s).prop _ (List.Mem.head _)

theorem lex_11_222_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4453), (Sat.Literal.neg 222), (Sat.Literal.pos 219)] :=
  (lex_11_222_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_222_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4453), (Sat.Literal.pos 222), (Sat.Literal.neg 219)] :=
  (lex_11_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_222_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4452), (Sat.Literal.neg 222), (Sat.Literal.neg 219), (Sat.Literal.pos 4453)] :=
  (lex_11_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_222_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4452), (Sat.Literal.pos 222), (Sat.Literal.pos 219), (Sat.Literal.pos 4453)] :=
  (lex_11_222_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_221_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4453) = lexBefore s permutation11 221 := by
  exact (positive_lex_of_descriptor s 4453 permutation11 222 (by rfl)).trans ((lex_skipped s permutation11 221 222 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 222 222 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_221_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation11 221) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation11 221 by rw [image11_eq]; rfl))

theorem lex_11_221_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4454) (Sat.Literal.pos 4453) (Sat.Literal.pos 221) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation11 221 (assignment s)
    (Sat.Literal.pos 4454) (Sat.Literal.pos 4453) (Sat.Literal.pos 221) (Sat.Literal.pos 187) (positive_of_descriptor s 4454 (.lex permutation11 221) (by rfl)) (lex_11_221_prefix s) (positive_select s 221) (lex_11_221_image s)

theorem lex_11_221_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4453), (Sat.Literal.pos 221), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation11 221 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4453) (Sat.Literal.pos 221) (Sat.Literal.pos 187) (lex_11_221_prefix s) (positive_select s 221) (lex_11_221_image s)

theorem lex_11_221_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4454), (Sat.Literal.pos 4453)] :=
  (lex_11_221_gate s).prop _ (List.Mem.head _)

theorem lex_11_221_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4454), (Sat.Literal.neg 221), (Sat.Literal.pos 187)] :=
  (lex_11_221_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_221_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4454), (Sat.Literal.pos 221), (Sat.Literal.neg 187)] :=
  (lex_11_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_221_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4453), (Sat.Literal.neg 221), (Sat.Literal.neg 187), (Sat.Literal.pos 4454)] :=
  (lex_11_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_221_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4453), (Sat.Literal.pos 221), (Sat.Literal.pos 187), (Sat.Literal.pos 4454)] :=
  (lex_11_221_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_220_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4454) = lexBefore s permutation11 220 := by
  exact (positive_lex_of_descriptor s 4454 permutation11 221 (by rfl)).trans ((lex_skipped s permutation11 220 221 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 221 221 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_220_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation11 220) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation11 220 by rw [image11_eq]; rfl))

theorem lex_11_220_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4455) (Sat.Literal.pos 4454) (Sat.Literal.pos 220) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation11 220 (assignment s)
    (Sat.Literal.pos 4455) (Sat.Literal.pos 4454) (Sat.Literal.pos 220) (Sat.Literal.pos 155) (positive_of_descriptor s 4455 (.lex permutation11 220) (by rfl)) (lex_11_220_prefix s) (positive_select s 220) (lex_11_220_image s)

theorem lex_11_220_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4454), (Sat.Literal.pos 220), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation11 220 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4454) (Sat.Literal.pos 220) (Sat.Literal.pos 155) (lex_11_220_prefix s) (positive_select s 220) (lex_11_220_image s)

theorem lex_11_220_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4455), (Sat.Literal.pos 4454)] :=
  (lex_11_220_gate s).prop _ (List.Mem.head _)

theorem lex_11_220_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4455), (Sat.Literal.neg 220), (Sat.Literal.pos 155)] :=
  (lex_11_220_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_220_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4455), (Sat.Literal.pos 220), (Sat.Literal.neg 155)] :=
  (lex_11_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_220_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4454), (Sat.Literal.neg 220), (Sat.Literal.neg 155), (Sat.Literal.pos 4455)] :=
  (lex_11_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_220_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4454), (Sat.Literal.pos 220), (Sat.Literal.pos 155), (Sat.Literal.pos 4455)] :=
  (lex_11_220_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_219_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4455) = lexBefore s permutation11 219 := by
  exact (positive_lex_of_descriptor s 4455 permutation11 220 (by rfl)).trans ((lex_skipped s permutation11 219 220 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 220 220 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_219_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 123) = s (permuteMask permutation11 219) := by
  exact (positive_select s 123).trans (congrArg s (show (123 : Fin 256) = permuteMask permutation11 219 by rw [image11_eq]; rfl))

theorem lex_11_219_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4456) (Sat.Literal.pos 4455) (Sat.Literal.pos 219) (Sat.Literal.pos 123)) := by
  exact equality_gate s permutation11 219 (assignment s)
    (Sat.Literal.pos 4456) (Sat.Literal.pos 4455) (Sat.Literal.pos 219) (Sat.Literal.pos 123) (positive_of_descriptor s 4456 (.lex permutation11 219) (by rfl)) (lex_11_219_prefix s) (positive_select s 219) (lex_11_219_image s)

theorem lex_11_219_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4455), (Sat.Literal.pos 219), (Sat.Literal.neg 123)] := by
  exact comparison_gate s permutation11 219 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4455) (Sat.Literal.pos 219) (Sat.Literal.pos 123) (lex_11_219_prefix s) (positive_select s 219) (lex_11_219_image s)

theorem lex_11_219_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4456), (Sat.Literal.pos 4455)] :=
  (lex_11_219_gate s).prop _ (List.Mem.head _)

theorem lex_11_219_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4456), (Sat.Literal.neg 219), (Sat.Literal.pos 123)] :=
  (lex_11_219_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_219_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4456), (Sat.Literal.pos 219), (Sat.Literal.neg 123)] :=
  (lex_11_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_219_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4455), (Sat.Literal.neg 219), (Sat.Literal.neg 123), (Sat.Literal.pos 4456)] :=
  (lex_11_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_219_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4455), (Sat.Literal.pos 219), (Sat.Literal.pos 123), (Sat.Literal.pos 4456)] :=
  (lex_11_219_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_218_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4456) = lexBefore s permutation11 218 := by
  exact (positive_lex_of_descriptor s 4456 permutation11 219 (by rfl)).trans ((lex_skipped s permutation11 218 219 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 219 219 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_218_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation11 218) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation11 218 by rw [image11_eq]; rfl))

theorem lex_11_218_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4457) (Sat.Literal.pos 4456) (Sat.Literal.pos 218) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation11 218 (assignment s)
    (Sat.Literal.pos 4457) (Sat.Literal.pos 4456) (Sat.Literal.pos 218) (Sat.Literal.pos 91) (positive_of_descriptor s 4457 (.lex permutation11 218) (by rfl)) (lex_11_218_prefix s) (positive_select s 218) (lex_11_218_image s)

theorem lex_11_218_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4456), (Sat.Literal.pos 218), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation11 218 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4456) (Sat.Literal.pos 218) (Sat.Literal.pos 91) (lex_11_218_prefix s) (positive_select s 218) (lex_11_218_image s)

theorem lex_11_218_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4457), (Sat.Literal.pos 4456)] :=
  (lex_11_218_gate s).prop _ (List.Mem.head _)

theorem lex_11_218_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4457), (Sat.Literal.neg 218), (Sat.Literal.pos 91)] :=
  (lex_11_218_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_218_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4457), (Sat.Literal.pos 218), (Sat.Literal.neg 91)] :=
  (lex_11_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_218_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4456), (Sat.Literal.neg 218), (Sat.Literal.neg 91), (Sat.Literal.pos 4457)] :=
  (lex_11_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_218_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4456), (Sat.Literal.pos 218), (Sat.Literal.pos 91), (Sat.Literal.pos 4457)] :=
  (lex_11_218_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_217_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4457) = lexBefore s permutation11 217 := by
  exact (positive_lex_of_descriptor s 4457 permutation11 218 (by rfl)).trans ((lex_skipped s permutation11 217 218 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 218 218 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_217_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 59) = s (permuteMask permutation11 217) := by
  exact (positive_select s 59).trans (congrArg s (show (59 : Fin 256) = permuteMask permutation11 217 by rw [image11_eq]; rfl))

theorem lex_11_217_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4458) (Sat.Literal.pos 4457) (Sat.Literal.pos 217) (Sat.Literal.pos 59)) := by
  exact equality_gate s permutation11 217 (assignment s)
    (Sat.Literal.pos 4458) (Sat.Literal.pos 4457) (Sat.Literal.pos 217) (Sat.Literal.pos 59) (positive_of_descriptor s 4458 (.lex permutation11 217) (by rfl)) (lex_11_217_prefix s) (positive_select s 217) (lex_11_217_image s)

theorem lex_11_217_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4457), (Sat.Literal.pos 217), (Sat.Literal.neg 59)] := by
  exact comparison_gate s permutation11 217 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4457) (Sat.Literal.pos 217) (Sat.Literal.pos 59) (lex_11_217_prefix s) (positive_select s 217) (lex_11_217_image s)

theorem lex_11_217_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4458), (Sat.Literal.pos 4457)] :=
  (lex_11_217_gate s).prop _ (List.Mem.head _)

theorem lex_11_217_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4458), (Sat.Literal.neg 217), (Sat.Literal.pos 59)] :=
  (lex_11_217_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_217_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4458), (Sat.Literal.pos 217), (Sat.Literal.neg 59)] :=
  (lex_11_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_217_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4457), (Sat.Literal.neg 217), (Sat.Literal.neg 59), (Sat.Literal.pos 4458)] :=
  (lex_11_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_217_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4457), (Sat.Literal.pos 217), (Sat.Literal.pos 59), (Sat.Literal.pos 4458)] :=
  (lex_11_217_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_216_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4458) = lexBefore s permutation11 216 := by
  exact (positive_lex_of_descriptor s 4458 permutation11 217 (by rfl)).trans ((lex_skipped s permutation11 216 217 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 217 217 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_216_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 27) = s (permuteMask permutation11 216) := by
  exact (positive_select s 27).trans (congrArg s (show (27 : Fin 256) = permuteMask permutation11 216 by rw [image11_eq]; rfl))

theorem lex_11_216_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4459) (Sat.Literal.pos 4458) (Sat.Literal.pos 216) (Sat.Literal.pos 27)) := by
  exact equality_gate s permutation11 216 (assignment s)
    (Sat.Literal.pos 4459) (Sat.Literal.pos 4458) (Sat.Literal.pos 216) (Sat.Literal.pos 27) (positive_of_descriptor s 4459 (.lex permutation11 216) (by rfl)) (lex_11_216_prefix s) (positive_select s 216) (lex_11_216_image s)

theorem lex_11_216_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4458), (Sat.Literal.pos 216), (Sat.Literal.neg 27)] := by
  exact comparison_gate s permutation11 216 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4458) (Sat.Literal.pos 216) (Sat.Literal.pos 27) (lex_11_216_prefix s) (positive_select s 216) (lex_11_216_image s)

theorem lex_11_216_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4459), (Sat.Literal.pos 4458)] :=
  (lex_11_216_gate s).prop _ (List.Mem.head _)

theorem lex_11_216_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4459), (Sat.Literal.neg 216), (Sat.Literal.pos 27)] :=
  (lex_11_216_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_216_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4459), (Sat.Literal.pos 216), (Sat.Literal.neg 27)] :=
  (lex_11_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_216_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4458), (Sat.Literal.neg 216), (Sat.Literal.neg 27), (Sat.Literal.pos 4459)] :=
  (lex_11_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_216_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4458), (Sat.Literal.pos 216), (Sat.Literal.pos 27), (Sat.Literal.pos 4459)] :=
  (lex_11_216_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_215_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4459) = lexBefore s permutation11 215 := by
  exact (positive_lex_of_descriptor s 4459 permutation11 216 (by rfl)).trans ((lex_skipped s permutation11 215 216 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 216 216 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_215_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 250) = s (permuteMask permutation11 215) := by
  exact (positive_select s 250).trans (congrArg s (show (250 : Fin 256) = permuteMask permutation11 215 by rw [image11_eq]; rfl))

theorem lex_11_215_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4460) (Sat.Literal.pos 4459) (Sat.Literal.pos 215) (Sat.Literal.pos 250)) := by
  exact equality_gate s permutation11 215 (assignment s)
    (Sat.Literal.pos 4460) (Sat.Literal.pos 4459) (Sat.Literal.pos 215) (Sat.Literal.pos 250) (positive_of_descriptor s 4460 (.lex permutation11 215) (by rfl)) (lex_11_215_prefix s) (positive_select s 215) (lex_11_215_image s)

theorem lex_11_215_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4459), (Sat.Literal.pos 215), (Sat.Literal.neg 250)] := by
  exact comparison_gate s permutation11 215 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4459) (Sat.Literal.pos 215) (Sat.Literal.pos 250) (lex_11_215_prefix s) (positive_select s 215) (lex_11_215_image s)

theorem lex_11_215_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4460), (Sat.Literal.pos 4459)] :=
  (lex_11_215_gate s).prop _ (List.Mem.head _)

theorem lex_11_215_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4460), (Sat.Literal.neg 215), (Sat.Literal.pos 250)] :=
  (lex_11_215_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_215_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4460), (Sat.Literal.pos 215), (Sat.Literal.neg 250)] :=
  (lex_11_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_215_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4459), (Sat.Literal.neg 215), (Sat.Literal.neg 250), (Sat.Literal.pos 4460)] :=
  (lex_11_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_215_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4459), (Sat.Literal.pos 215), (Sat.Literal.pos 250), (Sat.Literal.pos 4460)] :=
  (lex_11_215_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_214_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4460) = lexBefore s permutation11 214 := by
  exact (positive_lex_of_descriptor s 4460 permutation11 215 (by rfl)).trans ((lex_skipped s permutation11 214 215 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 215 215 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_214_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 218) = s (permuteMask permutation11 214) := by
  exact (positive_select s 218).trans (congrArg s (show (218 : Fin 256) = permuteMask permutation11 214 by rw [image11_eq]; rfl))

theorem lex_11_214_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4461) (Sat.Literal.pos 4460) (Sat.Literal.pos 214) (Sat.Literal.pos 218)) := by
  exact equality_gate s permutation11 214 (assignment s)
    (Sat.Literal.pos 4461) (Sat.Literal.pos 4460) (Sat.Literal.pos 214) (Sat.Literal.pos 218) (positive_of_descriptor s 4461 (.lex permutation11 214) (by rfl)) (lex_11_214_prefix s) (positive_select s 214) (lex_11_214_image s)

theorem lex_11_214_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4460), (Sat.Literal.pos 214), (Sat.Literal.neg 218)] := by
  exact comparison_gate s permutation11 214 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4460) (Sat.Literal.pos 214) (Sat.Literal.pos 218) (lex_11_214_prefix s) (positive_select s 214) (lex_11_214_image s)

theorem lex_11_214_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4461), (Sat.Literal.pos 4460)] :=
  (lex_11_214_gate s).prop _ (List.Mem.head _)

theorem lex_11_214_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4461), (Sat.Literal.neg 214), (Sat.Literal.pos 218)] :=
  (lex_11_214_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_214_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4461), (Sat.Literal.pos 214), (Sat.Literal.neg 218)] :=
  (lex_11_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_214_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4460), (Sat.Literal.neg 214), (Sat.Literal.neg 218), (Sat.Literal.pos 4461)] :=
  (lex_11_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_214_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4460), (Sat.Literal.pos 214), (Sat.Literal.pos 218), (Sat.Literal.pos 4461)] :=
  (lex_11_214_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_213_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4461) = lexBefore s permutation11 213 := by
  exact (positive_lex_of_descriptor s 4461 permutation11 214 (by rfl)).trans ((lex_skipped s permutation11 213 214 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 214 214 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_213_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation11 213) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation11 213 by rw [image11_eq]; rfl))

theorem lex_11_213_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4462) (Sat.Literal.pos 4461) (Sat.Literal.pos 213) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation11 213 (assignment s)
    (Sat.Literal.pos 4462) (Sat.Literal.pos 4461) (Sat.Literal.pos 213) (Sat.Literal.pos 186) (positive_of_descriptor s 4462 (.lex permutation11 213) (by rfl)) (lex_11_213_prefix s) (positive_select s 213) (lex_11_213_image s)

theorem lex_11_213_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4461), (Sat.Literal.pos 213), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation11 213 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4461) (Sat.Literal.pos 213) (Sat.Literal.pos 186) (lex_11_213_prefix s) (positive_select s 213) (lex_11_213_image s)

theorem lex_11_213_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4462), (Sat.Literal.pos 4461)] :=
  (lex_11_213_gate s).prop _ (List.Mem.head _)

theorem lex_11_213_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4462), (Sat.Literal.neg 213), (Sat.Literal.pos 186)] :=
  (lex_11_213_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_213_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4462), (Sat.Literal.pos 213), (Sat.Literal.neg 186)] :=
  (lex_11_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_213_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4461), (Sat.Literal.neg 213), (Sat.Literal.neg 186), (Sat.Literal.pos 4462)] :=
  (lex_11_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_213_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4461), (Sat.Literal.pos 213), (Sat.Literal.pos 186), (Sat.Literal.pos 4462)] :=
  (lex_11_213_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_212_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4462) = lexBefore s permutation11 212 := by
  exact (positive_lex_of_descriptor s 4462 permutation11 213 (by rfl)).trans ((lex_skipped s permutation11 212 213 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 213 213 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_212_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation11 212) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation11 212 by rw [image11_eq]; rfl))

theorem lex_11_212_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4463) (Sat.Literal.pos 4462) (Sat.Literal.pos 212) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation11 212 (assignment s)
    (Sat.Literal.pos 4463) (Sat.Literal.pos 4462) (Sat.Literal.pos 212) (Sat.Literal.pos 154) (positive_of_descriptor s 4463 (.lex permutation11 212) (by rfl)) (lex_11_212_prefix s) (positive_select s 212) (lex_11_212_image s)

theorem lex_11_212_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4462), (Sat.Literal.pos 212), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation11 212 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4462) (Sat.Literal.pos 212) (Sat.Literal.pos 154) (lex_11_212_prefix s) (positive_select s 212) (lex_11_212_image s)

theorem lex_11_212_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4463), (Sat.Literal.pos 4462)] :=
  (lex_11_212_gate s).prop _ (List.Mem.head _)

theorem lex_11_212_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4463), (Sat.Literal.neg 212), (Sat.Literal.pos 154)] :=
  (lex_11_212_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_212_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4463), (Sat.Literal.pos 212), (Sat.Literal.neg 154)] :=
  (lex_11_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_212_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4462), (Sat.Literal.neg 212), (Sat.Literal.neg 154), (Sat.Literal.pos 4463)] :=
  (lex_11_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_212_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4462), (Sat.Literal.pos 212), (Sat.Literal.pos 154), (Sat.Literal.pos 4463)] :=
  (lex_11_212_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_211_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4463) = lexBefore s permutation11 211 := by
  exact (positive_lex_of_descriptor s 4463 permutation11 212 (by rfl)).trans ((lex_skipped s permutation11 211 212 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 212 212 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_211_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 122) = s (permuteMask permutation11 211) := by
  exact (positive_select s 122).trans (congrArg s (show (122 : Fin 256) = permuteMask permutation11 211 by rw [image11_eq]; rfl))

theorem lex_11_211_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4464) (Sat.Literal.pos 4463) (Sat.Literal.pos 211) (Sat.Literal.pos 122)) := by
  exact equality_gate s permutation11 211 (assignment s)
    (Sat.Literal.pos 4464) (Sat.Literal.pos 4463) (Sat.Literal.pos 211) (Sat.Literal.pos 122) (positive_of_descriptor s 4464 (.lex permutation11 211) (by rfl)) (lex_11_211_prefix s) (positive_select s 211) (lex_11_211_image s)

theorem lex_11_211_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4463), (Sat.Literal.pos 211), (Sat.Literal.neg 122)] := by
  exact comparison_gate s permutation11 211 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4463) (Sat.Literal.pos 211) (Sat.Literal.pos 122) (lex_11_211_prefix s) (positive_select s 211) (lex_11_211_image s)

theorem lex_11_211_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4464), (Sat.Literal.pos 4463)] :=
  (lex_11_211_gate s).prop _ (List.Mem.head _)

theorem lex_11_211_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4464), (Sat.Literal.neg 211), (Sat.Literal.pos 122)] :=
  (lex_11_211_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_211_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4464), (Sat.Literal.pos 211), (Sat.Literal.neg 122)] :=
  (lex_11_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_211_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4463), (Sat.Literal.neg 211), (Sat.Literal.neg 122), (Sat.Literal.pos 4464)] :=
  (lex_11_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_211_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4463), (Sat.Literal.pos 211), (Sat.Literal.pos 122), (Sat.Literal.pos 4464)] :=
  (lex_11_211_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_210_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4464) = lexBefore s permutation11 210 := by
  exact (positive_lex_of_descriptor s 4464 permutation11 211 (by rfl)).trans ((lex_skipped s permutation11 210 211 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 211 211 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_210_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation11 210) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation11 210 by rw [image11_eq]; rfl))

theorem lex_11_210_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4465) (Sat.Literal.pos 4464) (Sat.Literal.pos 210) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation11 210 (assignment s)
    (Sat.Literal.pos 4465) (Sat.Literal.pos 4464) (Sat.Literal.pos 210) (Sat.Literal.pos 90) (positive_of_descriptor s 4465 (.lex permutation11 210) (by rfl)) (lex_11_210_prefix s) (positive_select s 210) (lex_11_210_image s)

theorem lex_11_210_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4464), (Sat.Literal.pos 210), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation11 210 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4464) (Sat.Literal.pos 210) (Sat.Literal.pos 90) (lex_11_210_prefix s) (positive_select s 210) (lex_11_210_image s)

theorem lex_11_210_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4465), (Sat.Literal.pos 4464)] :=
  (lex_11_210_gate s).prop _ (List.Mem.head _)

theorem lex_11_210_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4465), (Sat.Literal.neg 210), (Sat.Literal.pos 90)] :=
  (lex_11_210_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_210_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4465), (Sat.Literal.pos 210), (Sat.Literal.neg 90)] :=
  (lex_11_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_210_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4464), (Sat.Literal.neg 210), (Sat.Literal.neg 90), (Sat.Literal.pos 4465)] :=
  (lex_11_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_210_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4464), (Sat.Literal.pos 210), (Sat.Literal.pos 90), (Sat.Literal.pos 4465)] :=
  (lex_11_210_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_209_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4465) = lexBefore s permutation11 209 := by
  exact (positive_lex_of_descriptor s 4465 permutation11 210 (by rfl)).trans ((lex_skipped s permutation11 209 210 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 210 210 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_209_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 58) = s (permuteMask permutation11 209) := by
  exact (positive_select s 58).trans (congrArg s (show (58 : Fin 256) = permuteMask permutation11 209 by rw [image11_eq]; rfl))

theorem lex_11_209_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4466) (Sat.Literal.pos 4465) (Sat.Literal.pos 209) (Sat.Literal.pos 58)) := by
  exact equality_gate s permutation11 209 (assignment s)
    (Sat.Literal.pos 4466) (Sat.Literal.pos 4465) (Sat.Literal.pos 209) (Sat.Literal.pos 58) (positive_of_descriptor s 4466 (.lex permutation11 209) (by rfl)) (lex_11_209_prefix s) (positive_select s 209) (lex_11_209_image s)

theorem lex_11_209_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4465), (Sat.Literal.pos 209), (Sat.Literal.neg 58)] := by
  exact comparison_gate s permutation11 209 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4465) (Sat.Literal.pos 209) (Sat.Literal.pos 58) (lex_11_209_prefix s) (positive_select s 209) (lex_11_209_image s)

theorem lex_11_209_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4466), (Sat.Literal.pos 4465)] :=
  (lex_11_209_gate s).prop _ (List.Mem.head _)

theorem lex_11_209_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4466), (Sat.Literal.neg 209), (Sat.Literal.pos 58)] :=
  (lex_11_209_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_209_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4466), (Sat.Literal.pos 209), (Sat.Literal.neg 58)] :=
  (lex_11_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_209_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4465), (Sat.Literal.neg 209), (Sat.Literal.neg 58), (Sat.Literal.pos 4466)] :=
  (lex_11_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_209_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4465), (Sat.Literal.pos 209), (Sat.Literal.pos 58), (Sat.Literal.pos 4466)] :=
  (lex_11_209_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_208_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4466) = lexBefore s permutation11 208 := by
  exact (positive_lex_of_descriptor s 4466 permutation11 209 (by rfl)).trans ((lex_skipped s permutation11 208 209 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 209 209 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_208_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 26) = s (permuteMask permutation11 208) := by
  exact (positive_select s 26).trans (congrArg s (show (26 : Fin 256) = permuteMask permutation11 208 by rw [image11_eq]; rfl))

theorem lex_11_208_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4467) (Sat.Literal.pos 4466) (Sat.Literal.pos 208) (Sat.Literal.pos 26)) := by
  exact equality_gate s permutation11 208 (assignment s)
    (Sat.Literal.pos 4467) (Sat.Literal.pos 4466) (Sat.Literal.pos 208) (Sat.Literal.pos 26) (positive_of_descriptor s 4467 (.lex permutation11 208) (by rfl)) (lex_11_208_prefix s) (positive_select s 208) (lex_11_208_image s)

theorem lex_11_208_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4466), (Sat.Literal.pos 208), (Sat.Literal.neg 26)] := by
  exact comparison_gate s permutation11 208 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4466) (Sat.Literal.pos 208) (Sat.Literal.pos 26) (lex_11_208_prefix s) (positive_select s 208) (lex_11_208_image s)

theorem lex_11_208_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4467), (Sat.Literal.pos 4466)] :=
  (lex_11_208_gate s).prop _ (List.Mem.head _)

theorem lex_11_208_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4467), (Sat.Literal.neg 208), (Sat.Literal.pos 26)] :=
  (lex_11_208_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_208_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4467), (Sat.Literal.pos 208), (Sat.Literal.neg 26)] :=
  (lex_11_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_208_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4466), (Sat.Literal.neg 208), (Sat.Literal.neg 26), (Sat.Literal.pos 4467)] :=
  (lex_11_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_208_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4466), (Sat.Literal.pos 208), (Sat.Literal.pos 26), (Sat.Literal.pos 4467)] :=
  (lex_11_208_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_207_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4467) = lexBefore s permutation11 207 := by
  exact (positive_lex_of_descriptor s 4467 permutation11 208 (by rfl)).trans ((lex_skipped s permutation11 207 208 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 208 208 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_207_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation11 207) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation11 207 by rw [image11_eq]; rfl))

theorem lex_11_207_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4468) (Sat.Literal.pos 4467) (Sat.Literal.pos 207) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation11 207 (assignment s)
    (Sat.Literal.pos 4468) (Sat.Literal.pos 4467) (Sat.Literal.pos 207) (Sat.Literal.pos 249) (positive_of_descriptor s 4468 (.lex permutation11 207) (by rfl)) (lex_11_207_prefix s) (positive_select s 207) (lex_11_207_image s)

theorem lex_11_207_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4467), (Sat.Literal.pos 207), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation11 207 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4467) (Sat.Literal.pos 207) (Sat.Literal.pos 249) (lex_11_207_prefix s) (positive_select s 207) (lex_11_207_image s)

theorem lex_11_207_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4468), (Sat.Literal.pos 4467)] :=
  (lex_11_207_gate s).prop _ (List.Mem.head _)

theorem lex_11_207_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4468), (Sat.Literal.neg 207), (Sat.Literal.pos 249)] :=
  (lex_11_207_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_207_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4468), (Sat.Literal.pos 207), (Sat.Literal.neg 249)] :=
  (lex_11_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_207_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4467), (Sat.Literal.neg 207), (Sat.Literal.neg 249), (Sat.Literal.pos 4468)] :=
  (lex_11_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_207_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4467), (Sat.Literal.pos 207), (Sat.Literal.pos 249), (Sat.Literal.pos 4468)] :=
  (lex_11_207_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_206_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4468) = lexBefore s permutation11 206 := by
  exact (positive_lex_of_descriptor s 4468 permutation11 207 (by rfl)).trans ((lex_skipped s permutation11 206 207 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 207 207 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_206_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 217) = s (permuteMask permutation11 206) := by
  exact (positive_select s 217).trans (congrArg s (show (217 : Fin 256) = permuteMask permutation11 206 by rw [image11_eq]; rfl))

theorem lex_11_206_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4469) (Sat.Literal.pos 4468) (Sat.Literal.pos 206) (Sat.Literal.pos 217)) := by
  exact equality_gate s permutation11 206 (assignment s)
    (Sat.Literal.pos 4469) (Sat.Literal.pos 4468) (Sat.Literal.pos 206) (Sat.Literal.pos 217) (positive_of_descriptor s 4469 (.lex permutation11 206) (by rfl)) (lex_11_206_prefix s) (positive_select s 206) (lex_11_206_image s)

theorem lex_11_206_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4468), (Sat.Literal.pos 206), (Sat.Literal.neg 217)] := by
  exact comparison_gate s permutation11 206 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4468) (Sat.Literal.pos 206) (Sat.Literal.pos 217) (lex_11_206_prefix s) (positive_select s 206) (lex_11_206_image s)

theorem lex_11_206_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4469), (Sat.Literal.pos 4468)] :=
  (lex_11_206_gate s).prop _ (List.Mem.head _)

theorem lex_11_206_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4469), (Sat.Literal.neg 206), (Sat.Literal.pos 217)] :=
  (lex_11_206_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_206_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4469), (Sat.Literal.pos 206), (Sat.Literal.neg 217)] :=
  (lex_11_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_206_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4468), (Sat.Literal.neg 206), (Sat.Literal.neg 217), (Sat.Literal.pos 4469)] :=
  (lex_11_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_206_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4468), (Sat.Literal.pos 206), (Sat.Literal.pos 217), (Sat.Literal.pos 4469)] :=
  (lex_11_206_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_205_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4469) = lexBefore s permutation11 205 := by
  exact (positive_lex_of_descriptor s 4469 permutation11 206 (by rfl)).trans ((lex_skipped s permutation11 205 206 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 206 206 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_205_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation11 205) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation11 205 by rw [image11_eq]; rfl))

theorem lex_11_205_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4470) (Sat.Literal.pos 4469) (Sat.Literal.pos 205) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation11 205 (assignment s)
    (Sat.Literal.pos 4470) (Sat.Literal.pos 4469) (Sat.Literal.pos 205) (Sat.Literal.pos 185) (positive_of_descriptor s 4470 (.lex permutation11 205) (by rfl)) (lex_11_205_prefix s) (positive_select s 205) (lex_11_205_image s)

theorem lex_11_205_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4469), (Sat.Literal.pos 205), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation11 205 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4469) (Sat.Literal.pos 205) (Sat.Literal.pos 185) (lex_11_205_prefix s) (positive_select s 205) (lex_11_205_image s)

theorem lex_11_205_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4470), (Sat.Literal.pos 4469)] :=
  (lex_11_205_gate s).prop _ (List.Mem.head _)

theorem lex_11_205_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4470), (Sat.Literal.neg 205), (Sat.Literal.pos 185)] :=
  (lex_11_205_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_205_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4470), (Sat.Literal.pos 205), (Sat.Literal.neg 185)] :=
  (lex_11_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_205_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4469), (Sat.Literal.neg 205), (Sat.Literal.neg 185), (Sat.Literal.pos 4470)] :=
  (lex_11_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_205_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4469), (Sat.Literal.pos 205), (Sat.Literal.pos 185), (Sat.Literal.pos 4470)] :=
  (lex_11_205_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_204_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4470) = lexBefore s permutation11 204 := by
  exact (positive_lex_of_descriptor s 4470 permutation11 205 (by rfl)).trans ((lex_skipped s permutation11 204 205 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 205 205 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_204_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation11 204) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation11 204 by rw [image11_eq]; rfl))

theorem lex_11_204_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4471) (Sat.Literal.pos 4470) (Sat.Literal.pos 204) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation11 204 (assignment s)
    (Sat.Literal.pos 4471) (Sat.Literal.pos 4470) (Sat.Literal.pos 204) (Sat.Literal.pos 153) (positive_of_descriptor s 4471 (.lex permutation11 204) (by rfl)) (lex_11_204_prefix s) (positive_select s 204) (lex_11_204_image s)

theorem lex_11_204_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4470), (Sat.Literal.pos 204), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation11 204 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4470) (Sat.Literal.pos 204) (Sat.Literal.pos 153) (lex_11_204_prefix s) (positive_select s 204) (lex_11_204_image s)

theorem lex_11_204_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4471), (Sat.Literal.pos 4470)] :=
  (lex_11_204_gate s).prop _ (List.Mem.head _)

theorem lex_11_204_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4471), (Sat.Literal.neg 204), (Sat.Literal.pos 153)] :=
  (lex_11_204_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_204_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4471), (Sat.Literal.pos 204), (Sat.Literal.neg 153)] :=
  (lex_11_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_204_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4470), (Sat.Literal.neg 204), (Sat.Literal.neg 153), (Sat.Literal.pos 4471)] :=
  (lex_11_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_204_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4470), (Sat.Literal.pos 204), (Sat.Literal.pos 153), (Sat.Literal.pos 4471)] :=
  (lex_11_204_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_203_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4471) = lexBefore s permutation11 203 := by
  exact (positive_lex_of_descriptor s 4471 permutation11 204 (by rfl)).trans ((lex_skipped s permutation11 203 204 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 204 204 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_203_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 121) = s (permuteMask permutation11 203) := by
  exact (positive_select s 121).trans (congrArg s (show (121 : Fin 256) = permuteMask permutation11 203 by rw [image11_eq]; rfl))

theorem lex_11_203_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4472) (Sat.Literal.pos 4471) (Sat.Literal.pos 203) (Sat.Literal.pos 121)) := by
  exact equality_gate s permutation11 203 (assignment s)
    (Sat.Literal.pos 4472) (Sat.Literal.pos 4471) (Sat.Literal.pos 203) (Sat.Literal.pos 121) (positive_of_descriptor s 4472 (.lex permutation11 203) (by rfl)) (lex_11_203_prefix s) (positive_select s 203) (lex_11_203_image s)

theorem lex_11_203_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4471), (Sat.Literal.pos 203), (Sat.Literal.neg 121)] := by
  exact comparison_gate s permutation11 203 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4471) (Sat.Literal.pos 203) (Sat.Literal.pos 121) (lex_11_203_prefix s) (positive_select s 203) (lex_11_203_image s)

theorem lex_11_203_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4472), (Sat.Literal.pos 4471)] :=
  (lex_11_203_gate s).prop _ (List.Mem.head _)

theorem lex_11_203_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4472), (Sat.Literal.neg 203), (Sat.Literal.pos 121)] :=
  (lex_11_203_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_203_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4472), (Sat.Literal.pos 203), (Sat.Literal.neg 121)] :=
  (lex_11_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_203_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4471), (Sat.Literal.neg 203), (Sat.Literal.neg 121), (Sat.Literal.pos 4472)] :=
  (lex_11_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_203_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4471), (Sat.Literal.pos 203), (Sat.Literal.pos 121), (Sat.Literal.pos 4472)] :=
  (lex_11_203_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_202_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4472) = lexBefore s permutation11 202 := by
  exact (positive_lex_of_descriptor s 4472 permutation11 203 (by rfl)).trans ((lex_skipped s permutation11 202 203 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 203 203 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_202_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation11 202) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation11 202 by rw [image11_eq]; rfl))

theorem lex_11_202_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4473) (Sat.Literal.pos 4472) (Sat.Literal.pos 202) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation11 202 (assignment s)
    (Sat.Literal.pos 4473) (Sat.Literal.pos 4472) (Sat.Literal.pos 202) (Sat.Literal.pos 89) (positive_of_descriptor s 4473 (.lex permutation11 202) (by rfl)) (lex_11_202_prefix s) (positive_select s 202) (lex_11_202_image s)

theorem lex_11_202_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4472), (Sat.Literal.pos 202), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation11 202 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4472) (Sat.Literal.pos 202) (Sat.Literal.pos 89) (lex_11_202_prefix s) (positive_select s 202) (lex_11_202_image s)

theorem lex_11_202_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4473), (Sat.Literal.pos 4472)] :=
  (lex_11_202_gate s).prop _ (List.Mem.head _)

theorem lex_11_202_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4473), (Sat.Literal.neg 202), (Sat.Literal.pos 89)] :=
  (lex_11_202_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_202_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4473), (Sat.Literal.pos 202), (Sat.Literal.neg 89)] :=
  (lex_11_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_202_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4472), (Sat.Literal.neg 202), (Sat.Literal.neg 89), (Sat.Literal.pos 4473)] :=
  (lex_11_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_202_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4472), (Sat.Literal.pos 202), (Sat.Literal.pos 89), (Sat.Literal.pos 4473)] :=
  (lex_11_202_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_201_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4473) = lexBefore s permutation11 201 := by
  exact (positive_lex_of_descriptor s 4473 permutation11 202 (by rfl)).trans ((lex_skipped s permutation11 201 202 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 202 202 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_201_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 57) = s (permuteMask permutation11 201) := by
  exact (positive_select s 57).trans (congrArg s (show (57 : Fin 256) = permuteMask permutation11 201 by rw [image11_eq]; rfl))

theorem lex_11_201_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4474) (Sat.Literal.pos 4473) (Sat.Literal.pos 201) (Sat.Literal.pos 57)) := by
  exact equality_gate s permutation11 201 (assignment s)
    (Sat.Literal.pos 4474) (Sat.Literal.pos 4473) (Sat.Literal.pos 201) (Sat.Literal.pos 57) (positive_of_descriptor s 4474 (.lex permutation11 201) (by rfl)) (lex_11_201_prefix s) (positive_select s 201) (lex_11_201_image s)

theorem lex_11_201_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4473), (Sat.Literal.pos 201), (Sat.Literal.neg 57)] := by
  exact comparison_gate s permutation11 201 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4473) (Sat.Literal.pos 201) (Sat.Literal.pos 57) (lex_11_201_prefix s) (positive_select s 201) (lex_11_201_image s)

theorem lex_11_201_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4474), (Sat.Literal.pos 4473)] :=
  (lex_11_201_gate s).prop _ (List.Mem.head _)

theorem lex_11_201_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4474), (Sat.Literal.neg 201), (Sat.Literal.pos 57)] :=
  (lex_11_201_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_201_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4474), (Sat.Literal.pos 201), (Sat.Literal.neg 57)] :=
  (lex_11_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_201_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4473), (Sat.Literal.neg 201), (Sat.Literal.neg 57), (Sat.Literal.pos 4474)] :=
  (lex_11_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_201_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4473), (Sat.Literal.pos 201), (Sat.Literal.pos 57), (Sat.Literal.pos 4474)] :=
  (lex_11_201_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_200_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4474) = lexBefore s permutation11 200 := by
  exact (positive_lex_of_descriptor s 4474 permutation11 201 (by rfl)).trans ((lex_skipped s permutation11 200 201 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 201 201 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_200_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 25) = s (permuteMask permutation11 200) := by
  exact (positive_select s 25).trans (congrArg s (show (25 : Fin 256) = permuteMask permutation11 200 by rw [image11_eq]; rfl))

theorem lex_11_200_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4475) (Sat.Literal.pos 4474) (Sat.Literal.pos 200) (Sat.Literal.pos 25)) := by
  exact equality_gate s permutation11 200 (assignment s)
    (Sat.Literal.pos 4475) (Sat.Literal.pos 4474) (Sat.Literal.pos 200) (Sat.Literal.pos 25) (positive_of_descriptor s 4475 (.lex permutation11 200) (by rfl)) (lex_11_200_prefix s) (positive_select s 200) (lex_11_200_image s)

theorem lex_11_200_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4474), (Sat.Literal.pos 200), (Sat.Literal.neg 25)] := by
  exact comparison_gate s permutation11 200 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4474) (Sat.Literal.pos 200) (Sat.Literal.pos 25) (lex_11_200_prefix s) (positive_select s 200) (lex_11_200_image s)

theorem lex_11_200_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4475), (Sat.Literal.pos 4474)] :=
  (lex_11_200_gate s).prop _ (List.Mem.head _)

theorem lex_11_200_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4475), (Sat.Literal.neg 200), (Sat.Literal.pos 25)] :=
  (lex_11_200_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_200_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4475), (Sat.Literal.pos 200), (Sat.Literal.neg 25)] :=
  (lex_11_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_200_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4474), (Sat.Literal.neg 200), (Sat.Literal.neg 25), (Sat.Literal.pos 4475)] :=
  (lex_11_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_200_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4474), (Sat.Literal.pos 200), (Sat.Literal.pos 25), (Sat.Literal.pos 4475)] :=
  (lex_11_200_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_199_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4475) = lexBefore s permutation11 199 := by
  exact (positive_lex_of_descriptor s 4475 permutation11 200 (by rfl)).trans ((lex_skipped s permutation11 199 200 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 200 200 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_199_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 248) = s (permuteMask permutation11 199) := by
  exact (positive_select s 248).trans (congrArg s (show (248 : Fin 256) = permuteMask permutation11 199 by rw [image11_eq]; rfl))

theorem lex_11_199_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4476) (Sat.Literal.pos 4475) (Sat.Literal.pos 199) (Sat.Literal.pos 248)) := by
  exact equality_gate s permutation11 199 (assignment s)
    (Sat.Literal.pos 4476) (Sat.Literal.pos 4475) (Sat.Literal.pos 199) (Sat.Literal.pos 248) (positive_of_descriptor s 4476 (.lex permutation11 199) (by rfl)) (lex_11_199_prefix s) (positive_select s 199) (lex_11_199_image s)

theorem lex_11_199_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4475), (Sat.Literal.pos 199), (Sat.Literal.neg 248)] := by
  exact comparison_gate s permutation11 199 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4475) (Sat.Literal.pos 199) (Sat.Literal.pos 248) (lex_11_199_prefix s) (positive_select s 199) (lex_11_199_image s)

theorem lex_11_199_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4476), (Sat.Literal.pos 4475)] :=
  (lex_11_199_gate s).prop _ (List.Mem.head _)

theorem lex_11_199_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4476), (Sat.Literal.neg 199), (Sat.Literal.pos 248)] :=
  (lex_11_199_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_199_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4476), (Sat.Literal.pos 199), (Sat.Literal.neg 248)] :=
  (lex_11_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_199_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4475), (Sat.Literal.neg 199), (Sat.Literal.neg 248), (Sat.Literal.pos 4476)] :=
  (lex_11_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_199_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4475), (Sat.Literal.pos 199), (Sat.Literal.pos 248), (Sat.Literal.pos 4476)] :=
  (lex_11_199_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_198_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4476) = lexBefore s permutation11 198 := by
  exact (positive_lex_of_descriptor s 4476 permutation11 199 (by rfl)).trans ((lex_skipped s permutation11 198 199 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 199 199 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_198_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 216) = s (permuteMask permutation11 198) := by
  exact (positive_select s 216).trans (congrArg s (show (216 : Fin 256) = permuteMask permutation11 198 by rw [image11_eq]; rfl))

theorem lex_11_198_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4477) (Sat.Literal.pos 4476) (Sat.Literal.pos 198) (Sat.Literal.pos 216)) := by
  exact equality_gate s permutation11 198 (assignment s)
    (Sat.Literal.pos 4477) (Sat.Literal.pos 4476) (Sat.Literal.pos 198) (Sat.Literal.pos 216) (positive_of_descriptor s 4477 (.lex permutation11 198) (by rfl)) (lex_11_198_prefix s) (positive_select s 198) (lex_11_198_image s)

theorem lex_11_198_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4476), (Sat.Literal.pos 198), (Sat.Literal.neg 216)] := by
  exact comparison_gate s permutation11 198 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4476) (Sat.Literal.pos 198) (Sat.Literal.pos 216) (lex_11_198_prefix s) (positive_select s 198) (lex_11_198_image s)

theorem lex_11_198_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4477), (Sat.Literal.pos 4476)] :=
  (lex_11_198_gate s).prop _ (List.Mem.head _)

theorem lex_11_198_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4477), (Sat.Literal.neg 198), (Sat.Literal.pos 216)] :=
  (lex_11_198_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_198_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4477), (Sat.Literal.pos 198), (Sat.Literal.neg 216)] :=
  (lex_11_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_198_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4476), (Sat.Literal.neg 198), (Sat.Literal.neg 216), (Sat.Literal.pos 4477)] :=
  (lex_11_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_198_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4476), (Sat.Literal.pos 198), (Sat.Literal.pos 216), (Sat.Literal.pos 4477)] :=
  (lex_11_198_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_197_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4477) = lexBefore s permutation11 197 := by
  exact (positive_lex_of_descriptor s 4477 permutation11 198 (by rfl)).trans ((lex_skipped s permutation11 197 198 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 198 198 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_197_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation11 197) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation11 197 by rw [image11_eq]; rfl))

theorem lex_11_197_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4478) (Sat.Literal.pos 4477) (Sat.Literal.pos 197) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation11 197 (assignment s)
    (Sat.Literal.pos 4478) (Sat.Literal.pos 4477) (Sat.Literal.pos 197) (Sat.Literal.pos 184) (positive_of_descriptor s 4478 (.lex permutation11 197) (by rfl)) (lex_11_197_prefix s) (positive_select s 197) (lex_11_197_image s)

theorem lex_11_197_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4477), (Sat.Literal.pos 197), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation11 197 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4477) (Sat.Literal.pos 197) (Sat.Literal.pos 184) (lex_11_197_prefix s) (positive_select s 197) (lex_11_197_image s)

theorem lex_11_197_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4478), (Sat.Literal.pos 4477)] :=
  (lex_11_197_gate s).prop _ (List.Mem.head _)

theorem lex_11_197_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4478), (Sat.Literal.neg 197), (Sat.Literal.pos 184)] :=
  (lex_11_197_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_197_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4478), (Sat.Literal.pos 197), (Sat.Literal.neg 184)] :=
  (lex_11_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_197_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4477), (Sat.Literal.neg 197), (Sat.Literal.neg 184), (Sat.Literal.pos 4478)] :=
  (lex_11_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_197_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4477), (Sat.Literal.pos 197), (Sat.Literal.pos 184), (Sat.Literal.pos 4478)] :=
  (lex_11_197_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_196_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4478) = lexBefore s permutation11 196 := by
  exact (positive_lex_of_descriptor s 4478 permutation11 197 (by rfl)).trans ((lex_skipped s permutation11 196 197 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 197 197 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_196_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation11 196) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation11 196 by rw [image11_eq]; rfl))

theorem lex_11_196_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4479) (Sat.Literal.pos 4478) (Sat.Literal.pos 196) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation11 196 (assignment s)
    (Sat.Literal.pos 4479) (Sat.Literal.pos 4478) (Sat.Literal.pos 196) (Sat.Literal.pos 152) (positive_of_descriptor s 4479 (.lex permutation11 196) (by rfl)) (lex_11_196_prefix s) (positive_select s 196) (lex_11_196_image s)

theorem lex_11_196_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4478), (Sat.Literal.pos 196), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation11 196 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4478) (Sat.Literal.pos 196) (Sat.Literal.pos 152) (lex_11_196_prefix s) (positive_select s 196) (lex_11_196_image s)

theorem lex_11_196_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4479), (Sat.Literal.pos 4478)] :=
  (lex_11_196_gate s).prop _ (List.Mem.head _)

theorem lex_11_196_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4479), (Sat.Literal.neg 196), (Sat.Literal.pos 152)] :=
  (lex_11_196_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_196_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4479), (Sat.Literal.pos 196), (Sat.Literal.neg 152)] :=
  (lex_11_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_196_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4478), (Sat.Literal.neg 196), (Sat.Literal.neg 152), (Sat.Literal.pos 4479)] :=
  (lex_11_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_196_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4478), (Sat.Literal.pos 196), (Sat.Literal.pos 152), (Sat.Literal.pos 4479)] :=
  (lex_11_196_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_195_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4479) = lexBefore s permutation11 195 := by
  exact (positive_lex_of_descriptor s 4479 permutation11 196 (by rfl)).trans ((lex_skipped s permutation11 195 196 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 196 196 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_195_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 120) = s (permuteMask permutation11 195) := by
  exact (positive_select s 120).trans (congrArg s (show (120 : Fin 256) = permuteMask permutation11 195 by rw [image11_eq]; rfl))

theorem lex_11_195_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4480) (Sat.Literal.pos 4479) (Sat.Literal.pos 195) (Sat.Literal.pos 120)) := by
  exact equality_gate s permutation11 195 (assignment s)
    (Sat.Literal.pos 4480) (Sat.Literal.pos 4479) (Sat.Literal.pos 195) (Sat.Literal.pos 120) (positive_of_descriptor s 4480 (.lex permutation11 195) (by rfl)) (lex_11_195_prefix s) (positive_select s 195) (lex_11_195_image s)

theorem lex_11_195_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4479), (Sat.Literal.pos 195), (Sat.Literal.neg 120)] := by
  exact comparison_gate s permutation11 195 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4479) (Sat.Literal.pos 195) (Sat.Literal.pos 120) (lex_11_195_prefix s) (positive_select s 195) (lex_11_195_image s)

theorem lex_11_195_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4480), (Sat.Literal.pos 4479)] :=
  (lex_11_195_gate s).prop _ (List.Mem.head _)

theorem lex_11_195_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4480), (Sat.Literal.neg 195), (Sat.Literal.pos 120)] :=
  (lex_11_195_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_195_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4480), (Sat.Literal.pos 195), (Sat.Literal.neg 120)] :=
  (lex_11_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_195_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4479), (Sat.Literal.neg 195), (Sat.Literal.neg 120), (Sat.Literal.pos 4480)] :=
  (lex_11_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_195_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4479), (Sat.Literal.pos 195), (Sat.Literal.pos 120), (Sat.Literal.pos 4480)] :=
  (lex_11_195_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_194_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4480) = lexBefore s permutation11 194 := by
  exact (positive_lex_of_descriptor s 4480 permutation11 195 (by rfl)).trans ((lex_skipped s permutation11 194 195 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 195 195 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_194_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation11 194) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation11 194 by rw [image11_eq]; rfl))

theorem lex_11_194_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4481) (Sat.Literal.pos 4480) (Sat.Literal.pos 194) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation11 194 (assignment s)
    (Sat.Literal.pos 4481) (Sat.Literal.pos 4480) (Sat.Literal.pos 194) (Sat.Literal.pos 88) (positive_of_descriptor s 4481 (.lex permutation11 194) (by rfl)) (lex_11_194_prefix s) (positive_select s 194) (lex_11_194_image s)

theorem lex_11_194_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4480), (Sat.Literal.pos 194), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation11 194 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4480) (Sat.Literal.pos 194) (Sat.Literal.pos 88) (lex_11_194_prefix s) (positive_select s 194) (lex_11_194_image s)

theorem lex_11_194_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4481), (Sat.Literal.pos 4480)] :=
  (lex_11_194_gate s).prop _ (List.Mem.head _)

theorem lex_11_194_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4481), (Sat.Literal.neg 194), (Sat.Literal.pos 88)] :=
  (lex_11_194_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_194_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4481), (Sat.Literal.pos 194), (Sat.Literal.neg 88)] :=
  (lex_11_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_194_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4480), (Sat.Literal.neg 194), (Sat.Literal.neg 88), (Sat.Literal.pos 4481)] :=
  (lex_11_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_194_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4480), (Sat.Literal.pos 194), (Sat.Literal.pos 88), (Sat.Literal.pos 4481)] :=
  (lex_11_194_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_193_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4481) = lexBefore s permutation11 193 := by
  exact (positive_lex_of_descriptor s 4481 permutation11 194 (by rfl)).trans ((lex_skipped s permutation11 193 194 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 194 194 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_193_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 56) = s (permuteMask permutation11 193) := by
  exact (positive_select s 56).trans (congrArg s (show (56 : Fin 256) = permuteMask permutation11 193 by rw [image11_eq]; rfl))

theorem lex_11_193_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4482) (Sat.Literal.pos 4481) (Sat.Literal.pos 193) (Sat.Literal.pos 56)) := by
  exact equality_gate s permutation11 193 (assignment s)
    (Sat.Literal.pos 4482) (Sat.Literal.pos 4481) (Sat.Literal.pos 193) (Sat.Literal.pos 56) (positive_of_descriptor s 4482 (.lex permutation11 193) (by rfl)) (lex_11_193_prefix s) (positive_select s 193) (lex_11_193_image s)

theorem lex_11_193_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4481), (Sat.Literal.pos 193), (Sat.Literal.neg 56)] := by
  exact comparison_gate s permutation11 193 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4481) (Sat.Literal.pos 193) (Sat.Literal.pos 56) (lex_11_193_prefix s) (positive_select s 193) (lex_11_193_image s)

theorem lex_11_193_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4482), (Sat.Literal.pos 4481)] :=
  (lex_11_193_gate s).prop _ (List.Mem.head _)

theorem lex_11_193_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4482), (Sat.Literal.neg 193), (Sat.Literal.pos 56)] :=
  (lex_11_193_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_193_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4482), (Sat.Literal.pos 193), (Sat.Literal.neg 56)] :=
  (lex_11_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_193_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4481), (Sat.Literal.neg 193), (Sat.Literal.neg 56), (Sat.Literal.pos 4482)] :=
  (lex_11_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_193_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4481), (Sat.Literal.pos 193), (Sat.Literal.pos 56), (Sat.Literal.pos 4482)] :=
  (lex_11_193_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_192_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4482) = lexBefore s permutation11 192 := by
  exact (positive_lex_of_descriptor s 4482 permutation11 193 (by rfl)).trans ((lex_skipped s permutation11 192 193 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 193 193 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_192_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 24) = s (permuteMask permutation11 192) := by
  exact (positive_select s 24).trans (congrArg s (show (24 : Fin 256) = permuteMask permutation11 192 by rw [image11_eq]; rfl))

theorem lex_11_192_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4483) (Sat.Literal.pos 4482) (Sat.Literal.pos 192) (Sat.Literal.pos 24)) := by
  exact equality_gate s permutation11 192 (assignment s)
    (Sat.Literal.pos 4483) (Sat.Literal.pos 4482) (Sat.Literal.pos 192) (Sat.Literal.pos 24) (positive_of_descriptor s 4483 (.lex permutation11 192) (by rfl)) (lex_11_192_prefix s) (positive_select s 192) (lex_11_192_image s)

theorem lex_11_192_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4482), (Sat.Literal.pos 192), (Sat.Literal.neg 24)] := by
  exact comparison_gate s permutation11 192 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4482) (Sat.Literal.pos 192) (Sat.Literal.pos 24) (lex_11_192_prefix s) (positive_select s 192) (lex_11_192_image s)

theorem lex_11_192_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4483), (Sat.Literal.pos 4482)] :=
  (lex_11_192_gate s).prop _ (List.Mem.head _)

theorem lex_11_192_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4483), (Sat.Literal.neg 192), (Sat.Literal.pos 24)] :=
  (lex_11_192_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_192_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4483), (Sat.Literal.pos 192), (Sat.Literal.neg 24)] :=
  (lex_11_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_192_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4482), (Sat.Literal.neg 192), (Sat.Literal.neg 24), (Sat.Literal.pos 4483)] :=
  (lex_11_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_192_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4482), (Sat.Literal.pos 192), (Sat.Literal.pos 24), (Sat.Literal.pos 4483)] :=
  (lex_11_192_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_191_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4483) = lexBefore s permutation11 191 := by
  exact (positive_lex_of_descriptor s 4483 permutation11 192 (by rfl)).trans ((lex_skipped s permutation11 191 192 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 192 192 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_191_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation11 191) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation11 191 by rw [image11_eq]; rfl))

theorem lex_11_191_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4484) (Sat.Literal.pos 4483) (Sat.Literal.pos 191) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation11 191 (assignment s)
    (Sat.Literal.pos 4484) (Sat.Literal.pos 4483) (Sat.Literal.pos 191) (Sat.Literal.pos 247) (positive_of_descriptor s 4484 (.lex permutation11 191) (by rfl)) (lex_11_191_prefix s) (positive_select s 191) (lex_11_191_image s)

theorem lex_11_191_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4483), (Sat.Literal.pos 191), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation11 191 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4483) (Sat.Literal.pos 191) (Sat.Literal.pos 247) (lex_11_191_prefix s) (positive_select s 191) (lex_11_191_image s)

theorem lex_11_191_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4484), (Sat.Literal.pos 4483)] :=
  (lex_11_191_gate s).prop _ (List.Mem.head _)

theorem lex_11_191_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4484), (Sat.Literal.neg 191), (Sat.Literal.pos 247)] :=
  (lex_11_191_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_191_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4484), (Sat.Literal.pos 191), (Sat.Literal.neg 247)] :=
  (lex_11_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_191_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4483), (Sat.Literal.neg 191), (Sat.Literal.neg 247), (Sat.Literal.pos 4484)] :=
  (lex_11_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_191_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4483), (Sat.Literal.pos 191), (Sat.Literal.pos 247), (Sat.Literal.pos 4484)] :=
  (lex_11_191_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_190_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4484) = lexBefore s permutation11 190 := by
  exact (positive_lex_of_descriptor s 4484 permutation11 191 (by rfl)).trans ((lex_skipped s permutation11 190 191 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 191 191 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_190_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 215) = s (permuteMask permutation11 190) := by
  exact (positive_select s 215).trans (congrArg s (show (215 : Fin 256) = permuteMask permutation11 190 by rw [image11_eq]; rfl))

theorem lex_11_190_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4485) (Sat.Literal.pos 4484) (Sat.Literal.pos 190) (Sat.Literal.pos 215)) := by
  exact equality_gate s permutation11 190 (assignment s)
    (Sat.Literal.pos 4485) (Sat.Literal.pos 4484) (Sat.Literal.pos 190) (Sat.Literal.pos 215) (positive_of_descriptor s 4485 (.lex permutation11 190) (by rfl)) (lex_11_190_prefix s) (positive_select s 190) (lex_11_190_image s)

theorem lex_11_190_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4484), (Sat.Literal.pos 190), (Sat.Literal.neg 215)] := by
  exact comparison_gate s permutation11 190 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4484) (Sat.Literal.pos 190) (Sat.Literal.pos 215) (lex_11_190_prefix s) (positive_select s 190) (lex_11_190_image s)

theorem lex_11_190_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4485), (Sat.Literal.pos 4484)] :=
  (lex_11_190_gate s).prop _ (List.Mem.head _)

theorem lex_11_190_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4485), (Sat.Literal.neg 190), (Sat.Literal.pos 215)] :=
  (lex_11_190_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_190_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4485), (Sat.Literal.pos 190), (Sat.Literal.neg 215)] :=
  (lex_11_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_190_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4484), (Sat.Literal.neg 190), (Sat.Literal.neg 215), (Sat.Literal.pos 4485)] :=
  (lex_11_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_190_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4484), (Sat.Literal.pos 190), (Sat.Literal.pos 215), (Sat.Literal.pos 4485)] :=
  (lex_11_190_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_189_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4485) = lexBefore s permutation11 189 := by
  exact (positive_lex_of_descriptor s 4485 permutation11 190 (by rfl)).trans ((lex_skipped s permutation11 189 190 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 190 190 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_189_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation11 189) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation11 189 by rw [image11_eq]; rfl))

theorem lex_11_189_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4486) (Sat.Literal.pos 4485) (Sat.Literal.pos 189) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation11 189 (assignment s)
    (Sat.Literal.pos 4486) (Sat.Literal.pos 4485) (Sat.Literal.pos 189) (Sat.Literal.pos 183) (positive_of_descriptor s 4486 (.lex permutation11 189) (by rfl)) (lex_11_189_prefix s) (positive_select s 189) (lex_11_189_image s)

theorem lex_11_189_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4485), (Sat.Literal.pos 189), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation11 189 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4485) (Sat.Literal.pos 189) (Sat.Literal.pos 183) (lex_11_189_prefix s) (positive_select s 189) (lex_11_189_image s)

theorem lex_11_189_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4486), (Sat.Literal.pos 4485)] :=
  (lex_11_189_gate s).prop _ (List.Mem.head _)

theorem lex_11_189_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4486), (Sat.Literal.neg 189), (Sat.Literal.pos 183)] :=
  (lex_11_189_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_189_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4486), (Sat.Literal.pos 189), (Sat.Literal.neg 183)] :=
  (lex_11_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_189_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4485), (Sat.Literal.neg 189), (Sat.Literal.neg 183), (Sat.Literal.pos 4486)] :=
  (lex_11_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_189_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4485), (Sat.Literal.pos 189), (Sat.Literal.pos 183), (Sat.Literal.pos 4486)] :=
  (lex_11_189_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_188_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4486) = lexBefore s permutation11 188 := by
  exact (positive_lex_of_descriptor s 4486 permutation11 189 (by rfl)).trans ((lex_skipped s permutation11 188 189 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 189 189 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_188_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation11 188) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation11 188 by rw [image11_eq]; rfl))

theorem lex_11_188_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4487) (Sat.Literal.pos 4486) (Sat.Literal.pos 188) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation11 188 (assignment s)
    (Sat.Literal.pos 4487) (Sat.Literal.pos 4486) (Sat.Literal.pos 188) (Sat.Literal.pos 151) (positive_of_descriptor s 4487 (.lex permutation11 188) (by rfl)) (lex_11_188_prefix s) (positive_select s 188) (lex_11_188_image s)

theorem lex_11_188_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4486), (Sat.Literal.pos 188), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation11 188 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4486) (Sat.Literal.pos 188) (Sat.Literal.pos 151) (lex_11_188_prefix s) (positive_select s 188) (lex_11_188_image s)

theorem lex_11_188_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4487), (Sat.Literal.pos 4486)] :=
  (lex_11_188_gate s).prop _ (List.Mem.head _)

theorem lex_11_188_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4487), (Sat.Literal.neg 188), (Sat.Literal.pos 151)] :=
  (lex_11_188_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_188_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4487), (Sat.Literal.pos 188), (Sat.Literal.neg 151)] :=
  (lex_11_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_188_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4486), (Sat.Literal.neg 188), (Sat.Literal.neg 151), (Sat.Literal.pos 4487)] :=
  (lex_11_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_188_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4486), (Sat.Literal.pos 188), (Sat.Literal.pos 151), (Sat.Literal.pos 4487)] :=
  (lex_11_188_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_187_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4487) = lexBefore s permutation11 187 := by
  exact (positive_lex_of_descriptor s 4487 permutation11 188 (by rfl)).trans ((lex_skipped s permutation11 187 188 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 188 188 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_187_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 119) = s (permuteMask permutation11 187) := by
  exact (positive_select s 119).trans (congrArg s (show (119 : Fin 256) = permuteMask permutation11 187 by rw [image11_eq]; rfl))

theorem lex_11_187_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4488) (Sat.Literal.pos 4487) (Sat.Literal.pos 187) (Sat.Literal.pos 119)) := by
  exact equality_gate s permutation11 187 (assignment s)
    (Sat.Literal.pos 4488) (Sat.Literal.pos 4487) (Sat.Literal.pos 187) (Sat.Literal.pos 119) (positive_of_descriptor s 4488 (.lex permutation11 187) (by rfl)) (lex_11_187_prefix s) (positive_select s 187) (lex_11_187_image s)

theorem lex_11_187_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4487), (Sat.Literal.pos 187), (Sat.Literal.neg 119)] := by
  exact comparison_gate s permutation11 187 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4487) (Sat.Literal.pos 187) (Sat.Literal.pos 119) (lex_11_187_prefix s) (positive_select s 187) (lex_11_187_image s)

theorem lex_11_187_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4488), (Sat.Literal.pos 4487)] :=
  (lex_11_187_gate s).prop _ (List.Mem.head _)

theorem lex_11_187_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4488), (Sat.Literal.neg 187), (Sat.Literal.pos 119)] :=
  (lex_11_187_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_187_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4488), (Sat.Literal.pos 187), (Sat.Literal.neg 119)] :=
  (lex_11_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_187_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4487), (Sat.Literal.neg 187), (Sat.Literal.neg 119), (Sat.Literal.pos 4488)] :=
  (lex_11_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_187_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4487), (Sat.Literal.pos 187), (Sat.Literal.pos 119), (Sat.Literal.pos 4488)] :=
  (lex_11_187_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_186_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4488) = lexBefore s permutation11 186 := by
  exact (positive_lex_of_descriptor s 4488 permutation11 187 (by rfl)).trans ((lex_skipped s permutation11 186 187 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 187 187 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_186_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation11 186) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation11 186 by rw [image11_eq]; rfl))

theorem lex_11_186_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4489) (Sat.Literal.pos 4488) (Sat.Literal.pos 186) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation11 186 (assignment s)
    (Sat.Literal.pos 4489) (Sat.Literal.pos 4488) (Sat.Literal.pos 186) (Sat.Literal.pos 87) (positive_of_descriptor s 4489 (.lex permutation11 186) (by rfl)) (lex_11_186_prefix s) (positive_select s 186) (lex_11_186_image s)

theorem lex_11_186_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4488), (Sat.Literal.pos 186), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation11 186 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4488) (Sat.Literal.pos 186) (Sat.Literal.pos 87) (lex_11_186_prefix s) (positive_select s 186) (lex_11_186_image s)

theorem lex_11_186_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4489), (Sat.Literal.pos 4488)] :=
  (lex_11_186_gate s).prop _ (List.Mem.head _)

theorem lex_11_186_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4489), (Sat.Literal.neg 186), (Sat.Literal.pos 87)] :=
  (lex_11_186_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_186_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4489), (Sat.Literal.pos 186), (Sat.Literal.neg 87)] :=
  (lex_11_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_186_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4488), (Sat.Literal.neg 186), (Sat.Literal.neg 87), (Sat.Literal.pos 4489)] :=
  (lex_11_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_186_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4488), (Sat.Literal.pos 186), (Sat.Literal.pos 87), (Sat.Literal.pos 4489)] :=
  (lex_11_186_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_185_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4489) = lexBefore s permutation11 185 := by
  exact (positive_lex_of_descriptor s 4489 permutation11 186 (by rfl)).trans ((lex_skipped s permutation11 185 186 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 186 186 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_185_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 55) = s (permuteMask permutation11 185) := by
  exact (positive_select s 55).trans (congrArg s (show (55 : Fin 256) = permuteMask permutation11 185 by rw [image11_eq]; rfl))

theorem lex_11_185_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4490) (Sat.Literal.pos 4489) (Sat.Literal.pos 185) (Sat.Literal.pos 55)) := by
  exact equality_gate s permutation11 185 (assignment s)
    (Sat.Literal.pos 4490) (Sat.Literal.pos 4489) (Sat.Literal.pos 185) (Sat.Literal.pos 55) (positive_of_descriptor s 4490 (.lex permutation11 185) (by rfl)) (lex_11_185_prefix s) (positive_select s 185) (lex_11_185_image s)

theorem lex_11_185_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4489), (Sat.Literal.pos 185), (Sat.Literal.neg 55)] := by
  exact comparison_gate s permutation11 185 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4489) (Sat.Literal.pos 185) (Sat.Literal.pos 55) (lex_11_185_prefix s) (positive_select s 185) (lex_11_185_image s)

theorem lex_11_185_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4490), (Sat.Literal.pos 4489)] :=
  (lex_11_185_gate s).prop _ (List.Mem.head _)

theorem lex_11_185_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4490), (Sat.Literal.neg 185), (Sat.Literal.pos 55)] :=
  (lex_11_185_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_185_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4490), (Sat.Literal.pos 185), (Sat.Literal.neg 55)] :=
  (lex_11_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_185_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4489), (Sat.Literal.neg 185), (Sat.Literal.neg 55), (Sat.Literal.pos 4490)] :=
  (lex_11_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_185_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4489), (Sat.Literal.pos 185), (Sat.Literal.pos 55), (Sat.Literal.pos 4490)] :=
  (lex_11_185_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_184_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4490) = lexBefore s permutation11 184 := by
  exact (positive_lex_of_descriptor s 4490 permutation11 185 (by rfl)).trans ((lex_skipped s permutation11 184 185 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 185 185 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_184_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 23) = s (permuteMask permutation11 184) := by
  exact (positive_select s 23).trans (congrArg s (show (23 : Fin 256) = permuteMask permutation11 184 by rw [image11_eq]; rfl))

theorem lex_11_184_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4491) (Sat.Literal.pos 4490) (Sat.Literal.pos 184) (Sat.Literal.pos 23)) := by
  exact equality_gate s permutation11 184 (assignment s)
    (Sat.Literal.pos 4491) (Sat.Literal.pos 4490) (Sat.Literal.pos 184) (Sat.Literal.pos 23) (positive_of_descriptor s 4491 (.lex permutation11 184) (by rfl)) (lex_11_184_prefix s) (positive_select s 184) (lex_11_184_image s)

theorem lex_11_184_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4490), (Sat.Literal.pos 184), (Sat.Literal.neg 23)] := by
  exact comparison_gate s permutation11 184 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4490) (Sat.Literal.pos 184) (Sat.Literal.pos 23) (lex_11_184_prefix s) (positive_select s 184) (lex_11_184_image s)

theorem lex_11_184_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4491), (Sat.Literal.pos 4490)] :=
  (lex_11_184_gate s).prop _ (List.Mem.head _)

theorem lex_11_184_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4491), (Sat.Literal.neg 184), (Sat.Literal.pos 23)] :=
  (lex_11_184_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_184_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4491), (Sat.Literal.pos 184), (Sat.Literal.neg 23)] :=
  (lex_11_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_184_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4490), (Sat.Literal.neg 184), (Sat.Literal.neg 23), (Sat.Literal.pos 4491)] :=
  (lex_11_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_184_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4490), (Sat.Literal.pos 184), (Sat.Literal.pos 23), (Sat.Literal.pos 4491)] :=
  (lex_11_184_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_183_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4491) = lexBefore s permutation11 183 := by
  exact (positive_lex_of_descriptor s 4491 permutation11 184 (by rfl)).trans ((lex_skipped s permutation11 183 184 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 184 184 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_183_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 246) = s (permuteMask permutation11 183) := by
  exact (positive_select s 246).trans (congrArg s (show (246 : Fin 256) = permuteMask permutation11 183 by rw [image11_eq]; rfl))

theorem lex_11_183_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4492) (Sat.Literal.pos 4491) (Sat.Literal.pos 183) (Sat.Literal.pos 246)) := by
  exact equality_gate s permutation11 183 (assignment s)
    (Sat.Literal.pos 4492) (Sat.Literal.pos 4491) (Sat.Literal.pos 183) (Sat.Literal.pos 246) (positive_of_descriptor s 4492 (.lex permutation11 183) (by rfl)) (lex_11_183_prefix s) (positive_select s 183) (lex_11_183_image s)

theorem lex_11_183_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4491), (Sat.Literal.pos 183), (Sat.Literal.neg 246)] := by
  exact comparison_gate s permutation11 183 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4491) (Sat.Literal.pos 183) (Sat.Literal.pos 246) (lex_11_183_prefix s) (positive_select s 183) (lex_11_183_image s)

theorem lex_11_183_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4492), (Sat.Literal.pos 4491)] :=
  (lex_11_183_gate s).prop _ (List.Mem.head _)

theorem lex_11_183_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4492), (Sat.Literal.neg 183), (Sat.Literal.pos 246)] :=
  (lex_11_183_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_183_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4492), (Sat.Literal.pos 183), (Sat.Literal.neg 246)] :=
  (lex_11_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_183_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4491), (Sat.Literal.neg 183), (Sat.Literal.neg 246), (Sat.Literal.pos 4492)] :=
  (lex_11_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_183_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4491), (Sat.Literal.pos 183), (Sat.Literal.pos 246), (Sat.Literal.pos 4492)] :=
  (lex_11_183_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_182_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4492) = lexBefore s permutation11 182 := by
  exact (positive_lex_of_descriptor s 4492 permutation11 183 (by rfl)).trans ((lex_skipped s permutation11 182 183 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 183 183 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_182_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 214) = s (permuteMask permutation11 182) := by
  exact (positive_select s 214).trans (congrArg s (show (214 : Fin 256) = permuteMask permutation11 182 by rw [image11_eq]; rfl))

theorem lex_11_182_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4493) (Sat.Literal.pos 4492) (Sat.Literal.pos 182) (Sat.Literal.pos 214)) := by
  exact equality_gate s permutation11 182 (assignment s)
    (Sat.Literal.pos 4493) (Sat.Literal.pos 4492) (Sat.Literal.pos 182) (Sat.Literal.pos 214) (positive_of_descriptor s 4493 (.lex permutation11 182) (by rfl)) (lex_11_182_prefix s) (positive_select s 182) (lex_11_182_image s)

theorem lex_11_182_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4492), (Sat.Literal.pos 182), (Sat.Literal.neg 214)] := by
  exact comparison_gate s permutation11 182 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4492) (Sat.Literal.pos 182) (Sat.Literal.pos 214) (lex_11_182_prefix s) (positive_select s 182) (lex_11_182_image s)

theorem lex_11_182_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4493), (Sat.Literal.pos 4492)] :=
  (lex_11_182_gate s).prop _ (List.Mem.head _)

theorem lex_11_182_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4493), (Sat.Literal.neg 182), (Sat.Literal.pos 214)] :=
  (lex_11_182_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_182_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4493), (Sat.Literal.pos 182), (Sat.Literal.neg 214)] :=
  (lex_11_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_182_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4492), (Sat.Literal.neg 182), (Sat.Literal.neg 214), (Sat.Literal.pos 4493)] :=
  (lex_11_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_182_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4492), (Sat.Literal.pos 182), (Sat.Literal.pos 214), (Sat.Literal.pos 4493)] :=
  (lex_11_182_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_181_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4493) = lexBefore s permutation11 181 := by
  exact (positive_lex_of_descriptor s 4493 permutation11 182 (by rfl)).trans ((lex_skipped s permutation11 181 182 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 182 182 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_181_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation11 181) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation11 181 by rw [image11_eq]; rfl))

theorem lex_11_181_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4494) (Sat.Literal.pos 4493) (Sat.Literal.pos 181) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation11 181 (assignment s)
    (Sat.Literal.pos 4494) (Sat.Literal.pos 4493) (Sat.Literal.pos 181) (Sat.Literal.pos 182) (positive_of_descriptor s 4494 (.lex permutation11 181) (by rfl)) (lex_11_181_prefix s) (positive_select s 181) (lex_11_181_image s)

theorem lex_11_181_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4493), (Sat.Literal.pos 181), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation11 181 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4493) (Sat.Literal.pos 181) (Sat.Literal.pos 182) (lex_11_181_prefix s) (positive_select s 181) (lex_11_181_image s)

theorem lex_11_181_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4494), (Sat.Literal.pos 4493)] :=
  (lex_11_181_gate s).prop _ (List.Mem.head _)

theorem lex_11_181_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4494), (Sat.Literal.neg 181), (Sat.Literal.pos 182)] :=
  (lex_11_181_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_181_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4494), (Sat.Literal.pos 181), (Sat.Literal.neg 182)] :=
  (lex_11_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_181_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4493), (Sat.Literal.neg 181), (Sat.Literal.neg 182), (Sat.Literal.pos 4494)] :=
  (lex_11_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_181_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4493), (Sat.Literal.pos 181), (Sat.Literal.pos 182), (Sat.Literal.pos 4494)] :=
  (lex_11_181_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_180_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4494) = lexBefore s permutation11 180 := by
  exact (positive_lex_of_descriptor s 4494 permutation11 181 (by rfl)).trans ((lex_skipped s permutation11 180 181 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 181 181 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_180_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation11 180) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation11 180 by rw [image11_eq]; rfl))

theorem lex_11_180_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4495) (Sat.Literal.pos 4494) (Sat.Literal.pos 180) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation11 180 (assignment s)
    (Sat.Literal.pos 4495) (Sat.Literal.pos 4494) (Sat.Literal.pos 180) (Sat.Literal.pos 150) (positive_of_descriptor s 4495 (.lex permutation11 180) (by rfl)) (lex_11_180_prefix s) (positive_select s 180) (lex_11_180_image s)

theorem lex_11_180_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4494), (Sat.Literal.pos 180), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation11 180 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4494) (Sat.Literal.pos 180) (Sat.Literal.pos 150) (lex_11_180_prefix s) (positive_select s 180) (lex_11_180_image s)

theorem lex_11_180_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4495), (Sat.Literal.pos 4494)] :=
  (lex_11_180_gate s).prop _ (List.Mem.head _)

theorem lex_11_180_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4495), (Sat.Literal.neg 180), (Sat.Literal.pos 150)] :=
  (lex_11_180_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_180_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4495), (Sat.Literal.pos 180), (Sat.Literal.neg 150)] :=
  (lex_11_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_180_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4494), (Sat.Literal.neg 180), (Sat.Literal.neg 150), (Sat.Literal.pos 4495)] :=
  (lex_11_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_180_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4494), (Sat.Literal.pos 180), (Sat.Literal.pos 150), (Sat.Literal.pos 4495)] :=
  (lex_11_180_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_179_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4495) = lexBefore s permutation11 179 := by
  exact (positive_lex_of_descriptor s 4495 permutation11 180 (by rfl)).trans ((lex_skipped s permutation11 179 180 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 180 180 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_179_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 118) = s (permuteMask permutation11 179) := by
  exact (positive_select s 118).trans (congrArg s (show (118 : Fin 256) = permuteMask permutation11 179 by rw [image11_eq]; rfl))

theorem lex_11_179_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4496) (Sat.Literal.pos 4495) (Sat.Literal.pos 179) (Sat.Literal.pos 118)) := by
  exact equality_gate s permutation11 179 (assignment s)
    (Sat.Literal.pos 4496) (Sat.Literal.pos 4495) (Sat.Literal.pos 179) (Sat.Literal.pos 118) (positive_of_descriptor s 4496 (.lex permutation11 179) (by rfl)) (lex_11_179_prefix s) (positive_select s 179) (lex_11_179_image s)

theorem lex_11_179_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4495), (Sat.Literal.pos 179), (Sat.Literal.neg 118)] := by
  exact comparison_gate s permutation11 179 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4495) (Sat.Literal.pos 179) (Sat.Literal.pos 118) (lex_11_179_prefix s) (positive_select s 179) (lex_11_179_image s)

theorem lex_11_179_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4496), (Sat.Literal.pos 4495)] :=
  (lex_11_179_gate s).prop _ (List.Mem.head _)

theorem lex_11_179_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4496), (Sat.Literal.neg 179), (Sat.Literal.pos 118)] :=
  (lex_11_179_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_179_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4496), (Sat.Literal.pos 179), (Sat.Literal.neg 118)] :=
  (lex_11_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_179_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4495), (Sat.Literal.neg 179), (Sat.Literal.neg 118), (Sat.Literal.pos 4496)] :=
  (lex_11_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_179_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4495), (Sat.Literal.pos 179), (Sat.Literal.pos 118), (Sat.Literal.pos 4496)] :=
  (lex_11_179_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_178_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4496) = lexBefore s permutation11 178 := by
  exact (positive_lex_of_descriptor s 4496 permutation11 179 (by rfl)).trans ((lex_skipped s permutation11 178 179 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 179 179 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_178_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation11 178) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation11 178 by rw [image11_eq]; rfl))

theorem lex_11_178_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4497) (Sat.Literal.pos 4496) (Sat.Literal.pos 178) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation11 178 (assignment s)
    (Sat.Literal.pos 4497) (Sat.Literal.pos 4496) (Sat.Literal.pos 178) (Sat.Literal.pos 86) (positive_of_descriptor s 4497 (.lex permutation11 178) (by rfl)) (lex_11_178_prefix s) (positive_select s 178) (lex_11_178_image s)

theorem lex_11_178_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4496), (Sat.Literal.pos 178), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation11 178 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4496) (Sat.Literal.pos 178) (Sat.Literal.pos 86) (lex_11_178_prefix s) (positive_select s 178) (lex_11_178_image s)

theorem lex_11_178_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4497), (Sat.Literal.pos 4496)] :=
  (lex_11_178_gate s).prop _ (List.Mem.head _)

theorem lex_11_178_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4497), (Sat.Literal.neg 178), (Sat.Literal.pos 86)] :=
  (lex_11_178_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_178_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4497), (Sat.Literal.pos 178), (Sat.Literal.neg 86)] :=
  (lex_11_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_178_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4496), (Sat.Literal.neg 178), (Sat.Literal.neg 86), (Sat.Literal.pos 4497)] :=
  (lex_11_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_178_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4496), (Sat.Literal.pos 178), (Sat.Literal.pos 86), (Sat.Literal.pos 4497)] :=
  (lex_11_178_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_177_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4497) = lexBefore s permutation11 177 := by
  exact (positive_lex_of_descriptor s 4497 permutation11 178 (by rfl)).trans ((lex_skipped s permutation11 177 178 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 178 178 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_177_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 54) = s (permuteMask permutation11 177) := by
  exact (positive_select s 54).trans (congrArg s (show (54 : Fin 256) = permuteMask permutation11 177 by rw [image11_eq]; rfl))

theorem lex_11_177_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4498) (Sat.Literal.pos 4497) (Sat.Literal.pos 177) (Sat.Literal.pos 54)) := by
  exact equality_gate s permutation11 177 (assignment s)
    (Sat.Literal.pos 4498) (Sat.Literal.pos 4497) (Sat.Literal.pos 177) (Sat.Literal.pos 54) (positive_of_descriptor s 4498 (.lex permutation11 177) (by rfl)) (lex_11_177_prefix s) (positive_select s 177) (lex_11_177_image s)

theorem lex_11_177_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4497), (Sat.Literal.pos 177), (Sat.Literal.neg 54)] := by
  exact comparison_gate s permutation11 177 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4497) (Sat.Literal.pos 177) (Sat.Literal.pos 54) (lex_11_177_prefix s) (positive_select s 177) (lex_11_177_image s)

theorem lex_11_177_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4498), (Sat.Literal.pos 4497)] :=
  (lex_11_177_gate s).prop _ (List.Mem.head _)

theorem lex_11_177_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4498), (Sat.Literal.neg 177), (Sat.Literal.pos 54)] :=
  (lex_11_177_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_177_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4498), (Sat.Literal.pos 177), (Sat.Literal.neg 54)] :=
  (lex_11_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_177_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4497), (Sat.Literal.neg 177), (Sat.Literal.neg 54), (Sat.Literal.pos 4498)] :=
  (lex_11_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_177_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4497), (Sat.Literal.pos 177), (Sat.Literal.pos 54), (Sat.Literal.pos 4498)] :=
  (lex_11_177_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_176_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4498) = lexBefore s permutation11 176 := by
  exact (positive_lex_of_descriptor s 4498 permutation11 177 (by rfl)).trans ((lex_skipped s permutation11 176 177 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 177 177 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_176_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 22) = s (permuteMask permutation11 176) := by
  exact (positive_select s 22).trans (congrArg s (show (22 : Fin 256) = permuteMask permutation11 176 by rw [image11_eq]; rfl))

theorem lex_11_176_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4499) (Sat.Literal.pos 4498) (Sat.Literal.pos 176) (Sat.Literal.pos 22)) := by
  exact equality_gate s permutation11 176 (assignment s)
    (Sat.Literal.pos 4499) (Sat.Literal.pos 4498) (Sat.Literal.pos 176) (Sat.Literal.pos 22) (positive_of_descriptor s 4499 (.lex permutation11 176) (by rfl)) (lex_11_176_prefix s) (positive_select s 176) (lex_11_176_image s)

theorem lex_11_176_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4498), (Sat.Literal.pos 176), (Sat.Literal.neg 22)] := by
  exact comparison_gate s permutation11 176 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4498) (Sat.Literal.pos 176) (Sat.Literal.pos 22) (lex_11_176_prefix s) (positive_select s 176) (lex_11_176_image s)

theorem lex_11_176_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4499), (Sat.Literal.pos 4498)] :=
  (lex_11_176_gate s).prop _ (List.Mem.head _)

theorem lex_11_176_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4499), (Sat.Literal.neg 176), (Sat.Literal.pos 22)] :=
  (lex_11_176_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_176_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4499), (Sat.Literal.pos 176), (Sat.Literal.neg 22)] :=
  (lex_11_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_176_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4498), (Sat.Literal.neg 176), (Sat.Literal.neg 22), (Sat.Literal.pos 4499)] :=
  (lex_11_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_176_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4498), (Sat.Literal.pos 176), (Sat.Literal.pos 22), (Sat.Literal.pos 4499)] :=
  (lex_11_176_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_175_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4499) = lexBefore s permutation11 175 := by
  exact (positive_lex_of_descriptor s 4499 permutation11 176 (by rfl)).trans ((lex_skipped s permutation11 175 176 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 176 176 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_175_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 245) = s (permuteMask permutation11 175) := by
  exact (positive_select s 245).trans (congrArg s (show (245 : Fin 256) = permuteMask permutation11 175 by rw [image11_eq]; rfl))

theorem lex_11_175_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4500) (Sat.Literal.pos 4499) (Sat.Literal.pos 175) (Sat.Literal.pos 245)) := by
  exact equality_gate s permutation11 175 (assignment s)
    (Sat.Literal.pos 4500) (Sat.Literal.pos 4499) (Sat.Literal.pos 175) (Sat.Literal.pos 245) (positive_of_descriptor s 4500 (.lex permutation11 175) (by rfl)) (lex_11_175_prefix s) (positive_select s 175) (lex_11_175_image s)

theorem lex_11_175_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4499), (Sat.Literal.pos 175), (Sat.Literal.neg 245)] := by
  exact comparison_gate s permutation11 175 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4499) (Sat.Literal.pos 175) (Sat.Literal.pos 245) (lex_11_175_prefix s) (positive_select s 175) (lex_11_175_image s)

theorem lex_11_175_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4500), (Sat.Literal.pos 4499)] :=
  (lex_11_175_gate s).prop _ (List.Mem.head _)

theorem lex_11_175_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4500), (Sat.Literal.neg 175), (Sat.Literal.pos 245)] :=
  (lex_11_175_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_175_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4500), (Sat.Literal.pos 175), (Sat.Literal.neg 245)] :=
  (lex_11_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_175_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4499), (Sat.Literal.neg 175), (Sat.Literal.neg 245), (Sat.Literal.pos 4500)] :=
  (lex_11_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_175_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4499), (Sat.Literal.pos 175), (Sat.Literal.pos 245), (Sat.Literal.pos 4500)] :=
  (lex_11_175_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_174_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4500) = lexBefore s permutation11 174 := by
  exact (positive_lex_of_descriptor s 4500 permutation11 175 (by rfl)).trans ((lex_skipped s permutation11 174 175 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 175 175 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_174_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 213) = s (permuteMask permutation11 174) := by
  exact (positive_select s 213).trans (congrArg s (show (213 : Fin 256) = permuteMask permutation11 174 by rw [image11_eq]; rfl))

theorem lex_11_174_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4501) (Sat.Literal.pos 4500) (Sat.Literal.pos 174) (Sat.Literal.pos 213)) := by
  exact equality_gate s permutation11 174 (assignment s)
    (Sat.Literal.pos 4501) (Sat.Literal.pos 4500) (Sat.Literal.pos 174) (Sat.Literal.pos 213) (positive_of_descriptor s 4501 (.lex permutation11 174) (by rfl)) (lex_11_174_prefix s) (positive_select s 174) (lex_11_174_image s)

theorem lex_11_174_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4500), (Sat.Literal.pos 174), (Sat.Literal.neg 213)] := by
  exact comparison_gate s permutation11 174 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4500) (Sat.Literal.pos 174) (Sat.Literal.pos 213) (lex_11_174_prefix s) (positive_select s 174) (lex_11_174_image s)

theorem lex_11_174_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4501), (Sat.Literal.pos 4500)] :=
  (lex_11_174_gate s).prop _ (List.Mem.head _)

theorem lex_11_174_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4501), (Sat.Literal.neg 174), (Sat.Literal.pos 213)] :=
  (lex_11_174_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_174_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4501), (Sat.Literal.pos 174), (Sat.Literal.neg 213)] :=
  (lex_11_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_174_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4500), (Sat.Literal.neg 174), (Sat.Literal.neg 213), (Sat.Literal.pos 4501)] :=
  (lex_11_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_174_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4500), (Sat.Literal.pos 174), (Sat.Literal.pos 213), (Sat.Literal.pos 4501)] :=
  (lex_11_174_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_173_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4501) = lexBefore s permutation11 173 := by
  exact (positive_lex_of_descriptor s 4501 permutation11 174 (by rfl)).trans ((lex_skipped s permutation11 173 174 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 174 174 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_173_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation11 173) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation11 173 by rw [image11_eq]; rfl))

theorem lex_11_173_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4502) (Sat.Literal.pos 4501) (Sat.Literal.pos 173) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation11 173 (assignment s)
    (Sat.Literal.pos 4502) (Sat.Literal.pos 4501) (Sat.Literal.pos 173) (Sat.Literal.pos 181) (positive_of_descriptor s 4502 (.lex permutation11 173) (by rfl)) (lex_11_173_prefix s) (positive_select s 173) (lex_11_173_image s)

theorem lex_11_173_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4501), (Sat.Literal.pos 173), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation11 173 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4501) (Sat.Literal.pos 173) (Sat.Literal.pos 181) (lex_11_173_prefix s) (positive_select s 173) (lex_11_173_image s)

theorem lex_11_173_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4502), (Sat.Literal.pos 4501)] :=
  (lex_11_173_gate s).prop _ (List.Mem.head _)

theorem lex_11_173_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4502), (Sat.Literal.neg 173), (Sat.Literal.pos 181)] :=
  (lex_11_173_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_173_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4502), (Sat.Literal.pos 173), (Sat.Literal.neg 181)] :=
  (lex_11_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_173_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4501), (Sat.Literal.neg 173), (Sat.Literal.neg 181), (Sat.Literal.pos 4502)] :=
  (lex_11_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_173_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4501), (Sat.Literal.pos 173), (Sat.Literal.pos 181), (Sat.Literal.pos 4502)] :=
  (lex_11_173_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_172_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4502) = lexBefore s permutation11 172 := by
  exact (positive_lex_of_descriptor s 4502 permutation11 173 (by rfl)).trans ((lex_skipped s permutation11 172 173 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 173 173 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_172_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation11 172) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation11 172 by rw [image11_eq]; rfl))

theorem lex_11_172_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4503) (Sat.Literal.pos 4502) (Sat.Literal.pos 172) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation11 172 (assignment s)
    (Sat.Literal.pos 4503) (Sat.Literal.pos 4502) (Sat.Literal.pos 172) (Sat.Literal.pos 149) (positive_of_descriptor s 4503 (.lex permutation11 172) (by rfl)) (lex_11_172_prefix s) (positive_select s 172) (lex_11_172_image s)

theorem lex_11_172_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4502), (Sat.Literal.pos 172), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation11 172 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4502) (Sat.Literal.pos 172) (Sat.Literal.pos 149) (lex_11_172_prefix s) (positive_select s 172) (lex_11_172_image s)

theorem lex_11_172_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4503), (Sat.Literal.pos 4502)] :=
  (lex_11_172_gate s).prop _ (List.Mem.head _)

theorem lex_11_172_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4503), (Sat.Literal.neg 172), (Sat.Literal.pos 149)] :=
  (lex_11_172_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_172_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4503), (Sat.Literal.pos 172), (Sat.Literal.neg 149)] :=
  (lex_11_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_172_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4502), (Sat.Literal.neg 172), (Sat.Literal.neg 149), (Sat.Literal.pos 4503)] :=
  (lex_11_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_172_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4502), (Sat.Literal.pos 172), (Sat.Literal.pos 149), (Sat.Literal.pos 4503)] :=
  (lex_11_172_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_171_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4503) = lexBefore s permutation11 171 := by
  exact (positive_lex_of_descriptor s 4503 permutation11 172 (by rfl)).trans ((lex_skipped s permutation11 171 172 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 172 172 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_171_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 117) = s (permuteMask permutation11 171) := by
  exact (positive_select s 117).trans (congrArg s (show (117 : Fin 256) = permuteMask permutation11 171 by rw [image11_eq]; rfl))

theorem lex_11_171_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4504) (Sat.Literal.pos 4503) (Sat.Literal.pos 171) (Sat.Literal.pos 117)) := by
  exact equality_gate s permutation11 171 (assignment s)
    (Sat.Literal.pos 4504) (Sat.Literal.pos 4503) (Sat.Literal.pos 171) (Sat.Literal.pos 117) (positive_of_descriptor s 4504 (.lex permutation11 171) (by rfl)) (lex_11_171_prefix s) (positive_select s 171) (lex_11_171_image s)

theorem lex_11_171_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4503), (Sat.Literal.pos 171), (Sat.Literal.neg 117)] := by
  exact comparison_gate s permutation11 171 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4503) (Sat.Literal.pos 171) (Sat.Literal.pos 117) (lex_11_171_prefix s) (positive_select s 171) (lex_11_171_image s)

theorem lex_11_171_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4504), (Sat.Literal.pos 4503)] :=
  (lex_11_171_gate s).prop _ (List.Mem.head _)

theorem lex_11_171_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4504), (Sat.Literal.neg 171), (Sat.Literal.pos 117)] :=
  (lex_11_171_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_171_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4504), (Sat.Literal.pos 171), (Sat.Literal.neg 117)] :=
  (lex_11_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_171_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4503), (Sat.Literal.neg 171), (Sat.Literal.neg 117), (Sat.Literal.pos 4504)] :=
  (lex_11_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_171_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4503), (Sat.Literal.pos 171), (Sat.Literal.pos 117), (Sat.Literal.pos 4504)] :=
  (lex_11_171_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_170_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4504) = lexBefore s permutation11 170 := by
  exact (positive_lex_of_descriptor s 4504 permutation11 171 (by rfl)).trans ((lex_skipped s permutation11 170 171 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 171 171 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_170_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation11 170) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation11 170 by rw [image11_eq]; rfl))

theorem lex_11_170_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4505) (Sat.Literal.pos 4504) (Sat.Literal.pos 170) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation11 170 (assignment s)
    (Sat.Literal.pos 4505) (Sat.Literal.pos 4504) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (positive_of_descriptor s 4505 (.lex permutation11 170) (by rfl)) (lex_11_170_prefix s) (positive_select s 170) (lex_11_170_image s)

theorem lex_11_170_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4504), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation11 170 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4504) (Sat.Literal.pos 170) (Sat.Literal.pos 85) (lex_11_170_prefix s) (positive_select s 170) (lex_11_170_image s)

theorem lex_11_170_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4505), (Sat.Literal.pos 4504)] :=
  (lex_11_170_gate s).prop _ (List.Mem.head _)

theorem lex_11_170_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4505), (Sat.Literal.neg 170), (Sat.Literal.pos 85)] :=
  (lex_11_170_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_170_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4505), (Sat.Literal.pos 170), (Sat.Literal.neg 85)] :=
  (lex_11_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_170_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4504), (Sat.Literal.neg 170), (Sat.Literal.neg 85), (Sat.Literal.pos 4505)] :=
  (lex_11_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_170_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4504), (Sat.Literal.pos 170), (Sat.Literal.pos 85), (Sat.Literal.pos 4505)] :=
  (lex_11_170_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_169_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4505) = lexBefore s permutation11 169 := by
  exact (positive_lex_of_descriptor s 4505 permutation11 170 (by rfl)).trans ((lex_skipped s permutation11 169 170 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 170 170 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_169_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 53) = s (permuteMask permutation11 169) := by
  exact (positive_select s 53).trans (congrArg s (show (53 : Fin 256) = permuteMask permutation11 169 by rw [image11_eq]; rfl))

theorem lex_11_169_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4506) (Sat.Literal.pos 4505) (Sat.Literal.pos 169) (Sat.Literal.pos 53)) := by
  exact equality_gate s permutation11 169 (assignment s)
    (Sat.Literal.pos 4506) (Sat.Literal.pos 4505) (Sat.Literal.pos 169) (Sat.Literal.pos 53) (positive_of_descriptor s 4506 (.lex permutation11 169) (by rfl)) (lex_11_169_prefix s) (positive_select s 169) (lex_11_169_image s)

theorem lex_11_169_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4505), (Sat.Literal.pos 169), (Sat.Literal.neg 53)] := by
  exact comparison_gate s permutation11 169 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4505) (Sat.Literal.pos 169) (Sat.Literal.pos 53) (lex_11_169_prefix s) (positive_select s 169) (lex_11_169_image s)

theorem lex_11_169_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4506), (Sat.Literal.pos 4505)] :=
  (lex_11_169_gate s).prop _ (List.Mem.head _)

theorem lex_11_169_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4506), (Sat.Literal.neg 169), (Sat.Literal.pos 53)] :=
  (lex_11_169_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_169_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4506), (Sat.Literal.pos 169), (Sat.Literal.neg 53)] :=
  (lex_11_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_169_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4505), (Sat.Literal.neg 169), (Sat.Literal.neg 53), (Sat.Literal.pos 4506)] :=
  (lex_11_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_169_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4505), (Sat.Literal.pos 169), (Sat.Literal.pos 53), (Sat.Literal.pos 4506)] :=
  (lex_11_169_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_168_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4506) = lexBefore s permutation11 168 := by
  exact (positive_lex_of_descriptor s 4506 permutation11 169 (by rfl)).trans ((lex_skipped s permutation11 168 169 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 169 169 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_168_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 21) = s (permuteMask permutation11 168) := by
  exact (positive_select s 21).trans (congrArg s (show (21 : Fin 256) = permuteMask permutation11 168 by rw [image11_eq]; rfl))

theorem lex_11_168_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4507) (Sat.Literal.pos 4506) (Sat.Literal.pos 168) (Sat.Literal.pos 21)) := by
  exact equality_gate s permutation11 168 (assignment s)
    (Sat.Literal.pos 4507) (Sat.Literal.pos 4506) (Sat.Literal.pos 168) (Sat.Literal.pos 21) (positive_of_descriptor s 4507 (.lex permutation11 168) (by rfl)) (lex_11_168_prefix s) (positive_select s 168) (lex_11_168_image s)

theorem lex_11_168_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4506), (Sat.Literal.pos 168), (Sat.Literal.neg 21)] := by
  exact comparison_gate s permutation11 168 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4506) (Sat.Literal.pos 168) (Sat.Literal.pos 21) (lex_11_168_prefix s) (positive_select s 168) (lex_11_168_image s)

theorem lex_11_168_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4507), (Sat.Literal.pos 4506)] :=
  (lex_11_168_gate s).prop _ (List.Mem.head _)

theorem lex_11_168_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4507), (Sat.Literal.neg 168), (Sat.Literal.pos 21)] :=
  (lex_11_168_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_168_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4507), (Sat.Literal.pos 168), (Sat.Literal.neg 21)] :=
  (lex_11_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_168_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4506), (Sat.Literal.neg 168), (Sat.Literal.neg 21), (Sat.Literal.pos 4507)] :=
  (lex_11_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_168_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4506), (Sat.Literal.pos 168), (Sat.Literal.pos 21), (Sat.Literal.pos 4507)] :=
  (lex_11_168_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_167_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4507) = lexBefore s permutation11 167 := by
  exact (positive_lex_of_descriptor s 4507 permutation11 168 (by rfl)).trans ((lex_skipped s permutation11 167 168 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 168 168 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_167_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 244) = s (permuteMask permutation11 167) := by
  exact (positive_select s 244).trans (congrArg s (show (244 : Fin 256) = permuteMask permutation11 167 by rw [image11_eq]; rfl))

theorem lex_11_167_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4508) (Sat.Literal.pos 4507) (Sat.Literal.pos 167) (Sat.Literal.pos 244)) := by
  exact equality_gate s permutation11 167 (assignment s)
    (Sat.Literal.pos 4508) (Sat.Literal.pos 4507) (Sat.Literal.pos 167) (Sat.Literal.pos 244) (positive_of_descriptor s 4508 (.lex permutation11 167) (by rfl)) (lex_11_167_prefix s) (positive_select s 167) (lex_11_167_image s)

theorem lex_11_167_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4507), (Sat.Literal.pos 167), (Sat.Literal.neg 244)] := by
  exact comparison_gate s permutation11 167 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4507) (Sat.Literal.pos 167) (Sat.Literal.pos 244) (lex_11_167_prefix s) (positive_select s 167) (lex_11_167_image s)

theorem lex_11_167_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4508), (Sat.Literal.pos 4507)] :=
  (lex_11_167_gate s).prop _ (List.Mem.head _)

theorem lex_11_167_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4508), (Sat.Literal.neg 167), (Sat.Literal.pos 244)] :=
  (lex_11_167_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_167_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4508), (Sat.Literal.pos 167), (Sat.Literal.neg 244)] :=
  (lex_11_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_167_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4507), (Sat.Literal.neg 167), (Sat.Literal.neg 244), (Sat.Literal.pos 4508)] :=
  (lex_11_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_167_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4507), (Sat.Literal.pos 167), (Sat.Literal.pos 244), (Sat.Literal.pos 4508)] :=
  (lex_11_167_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_166_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4508) = lexBefore s permutation11 166 := by
  exact (positive_lex_of_descriptor s 4508 permutation11 167 (by rfl)).trans ((lex_skipped s permutation11 166 167 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 167 167 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_166_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 212) = s (permuteMask permutation11 166) := by
  exact (positive_select s 212).trans (congrArg s (show (212 : Fin 256) = permuteMask permutation11 166 by rw [image11_eq]; rfl))

theorem lex_11_166_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4509) (Sat.Literal.pos 4508) (Sat.Literal.pos 166) (Sat.Literal.pos 212)) := by
  exact equality_gate s permutation11 166 (assignment s)
    (Sat.Literal.pos 4509) (Sat.Literal.pos 4508) (Sat.Literal.pos 166) (Sat.Literal.pos 212) (positive_of_descriptor s 4509 (.lex permutation11 166) (by rfl)) (lex_11_166_prefix s) (positive_select s 166) (lex_11_166_image s)

theorem lex_11_166_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4508), (Sat.Literal.pos 166), (Sat.Literal.neg 212)] := by
  exact comparison_gate s permutation11 166 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4508) (Sat.Literal.pos 166) (Sat.Literal.pos 212) (lex_11_166_prefix s) (positive_select s 166) (lex_11_166_image s)

theorem lex_11_166_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4509), (Sat.Literal.pos 4508)] :=
  (lex_11_166_gate s).prop _ (List.Mem.head _)

theorem lex_11_166_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4509), (Sat.Literal.neg 166), (Sat.Literal.pos 212)] :=
  (lex_11_166_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_166_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4509), (Sat.Literal.pos 166), (Sat.Literal.neg 212)] :=
  (lex_11_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_166_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4508), (Sat.Literal.neg 166), (Sat.Literal.neg 212), (Sat.Literal.pos 4509)] :=
  (lex_11_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_166_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4508), (Sat.Literal.pos 166), (Sat.Literal.pos 212), (Sat.Literal.pos 4509)] :=
  (lex_11_166_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_165_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4509) = lexBefore s permutation11 165 := by
  exact (positive_lex_of_descriptor s 4509 permutation11 166 (by rfl)).trans ((lex_skipped s permutation11 165 166 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 166 166 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_165_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation11 165) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation11 165 by rw [image11_eq]; rfl))

theorem lex_11_165_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4510) (Sat.Literal.pos 4509) (Sat.Literal.pos 165) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation11 165 (assignment s)
    (Sat.Literal.pos 4510) (Sat.Literal.pos 4509) (Sat.Literal.pos 165) (Sat.Literal.pos 180) (positive_of_descriptor s 4510 (.lex permutation11 165) (by rfl)) (lex_11_165_prefix s) (positive_select s 165) (lex_11_165_image s)

theorem lex_11_165_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4509), (Sat.Literal.pos 165), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation11 165 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4509) (Sat.Literal.pos 165) (Sat.Literal.pos 180) (lex_11_165_prefix s) (positive_select s 165) (lex_11_165_image s)

theorem lex_11_165_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4510), (Sat.Literal.pos 4509)] :=
  (lex_11_165_gate s).prop _ (List.Mem.head _)

theorem lex_11_165_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4510), (Sat.Literal.neg 165), (Sat.Literal.pos 180)] :=
  (lex_11_165_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_165_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4510), (Sat.Literal.pos 165), (Sat.Literal.neg 180)] :=
  (lex_11_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_165_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4509), (Sat.Literal.neg 165), (Sat.Literal.neg 180), (Sat.Literal.pos 4510)] :=
  (lex_11_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_165_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4509), (Sat.Literal.pos 165), (Sat.Literal.pos 180), (Sat.Literal.pos 4510)] :=
  (lex_11_165_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_164_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4510) = lexBefore s permutation11 164 := by
  exact (positive_lex_of_descriptor s 4510 permutation11 165 (by rfl)).trans ((lex_skipped s permutation11 164 165 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 165 165 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_164_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation11 164) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation11 164 by rw [image11_eq]; rfl))

theorem lex_11_164_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4511) (Sat.Literal.pos 4510) (Sat.Literal.pos 164) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation11 164 (assignment s)
    (Sat.Literal.pos 4511) (Sat.Literal.pos 4510) (Sat.Literal.pos 164) (Sat.Literal.pos 148) (positive_of_descriptor s 4511 (.lex permutation11 164) (by rfl)) (lex_11_164_prefix s) (positive_select s 164) (lex_11_164_image s)

theorem lex_11_164_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4510), (Sat.Literal.pos 164), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation11 164 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4510) (Sat.Literal.pos 164) (Sat.Literal.pos 148) (lex_11_164_prefix s) (positive_select s 164) (lex_11_164_image s)

theorem lex_11_164_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4511), (Sat.Literal.pos 4510)] :=
  (lex_11_164_gate s).prop _ (List.Mem.head _)

theorem lex_11_164_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4511), (Sat.Literal.neg 164), (Sat.Literal.pos 148)] :=
  (lex_11_164_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_164_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4511), (Sat.Literal.pos 164), (Sat.Literal.neg 148)] :=
  (lex_11_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_164_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4510), (Sat.Literal.neg 164), (Sat.Literal.neg 148), (Sat.Literal.pos 4511)] :=
  (lex_11_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_164_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4510), (Sat.Literal.pos 164), (Sat.Literal.pos 148), (Sat.Literal.pos 4511)] :=
  (lex_11_164_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_163_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4511) = lexBefore s permutation11 163 := by
  exact (positive_lex_of_descriptor s 4511 permutation11 164 (by rfl)).trans ((lex_skipped s permutation11 163 164 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 164 164 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_163_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 116) = s (permuteMask permutation11 163) := by
  exact (positive_select s 116).trans (congrArg s (show (116 : Fin 256) = permuteMask permutation11 163 by rw [image11_eq]; rfl))

theorem lex_11_163_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4512) (Sat.Literal.pos 4511) (Sat.Literal.pos 163) (Sat.Literal.pos 116)) := by
  exact equality_gate s permutation11 163 (assignment s)
    (Sat.Literal.pos 4512) (Sat.Literal.pos 4511) (Sat.Literal.pos 163) (Sat.Literal.pos 116) (positive_of_descriptor s 4512 (.lex permutation11 163) (by rfl)) (lex_11_163_prefix s) (positive_select s 163) (lex_11_163_image s)

theorem lex_11_163_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4511), (Sat.Literal.pos 163), (Sat.Literal.neg 116)] := by
  exact comparison_gate s permutation11 163 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4511) (Sat.Literal.pos 163) (Sat.Literal.pos 116) (lex_11_163_prefix s) (positive_select s 163) (lex_11_163_image s)

theorem lex_11_163_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4512), (Sat.Literal.pos 4511)] :=
  (lex_11_163_gate s).prop _ (List.Mem.head _)

theorem lex_11_163_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4512), (Sat.Literal.neg 163), (Sat.Literal.pos 116)] :=
  (lex_11_163_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_163_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4512), (Sat.Literal.pos 163), (Sat.Literal.neg 116)] :=
  (lex_11_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_163_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4511), (Sat.Literal.neg 163), (Sat.Literal.neg 116), (Sat.Literal.pos 4512)] :=
  (lex_11_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_163_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4511), (Sat.Literal.pos 163), (Sat.Literal.pos 116), (Sat.Literal.pos 4512)] :=
  (lex_11_163_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_162_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4512) = lexBefore s permutation11 162 := by
  exact (positive_lex_of_descriptor s 4512 permutation11 163 (by rfl)).trans ((lex_skipped s permutation11 162 163 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 163 163 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_162_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation11 162) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation11 162 by rw [image11_eq]; rfl))

theorem lex_11_162_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4513) (Sat.Literal.pos 4512) (Sat.Literal.pos 162) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation11 162 (assignment s)
    (Sat.Literal.pos 4513) (Sat.Literal.pos 4512) (Sat.Literal.pos 162) (Sat.Literal.pos 84) (positive_of_descriptor s 4513 (.lex permutation11 162) (by rfl)) (lex_11_162_prefix s) (positive_select s 162) (lex_11_162_image s)

theorem lex_11_162_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4512), (Sat.Literal.pos 162), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation11 162 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4512) (Sat.Literal.pos 162) (Sat.Literal.pos 84) (lex_11_162_prefix s) (positive_select s 162) (lex_11_162_image s)

theorem lex_11_162_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4513), (Sat.Literal.pos 4512)] :=
  (lex_11_162_gate s).prop _ (List.Mem.head _)

theorem lex_11_162_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4513), (Sat.Literal.neg 162), (Sat.Literal.pos 84)] :=
  (lex_11_162_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_162_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4513), (Sat.Literal.pos 162), (Sat.Literal.neg 84)] :=
  (lex_11_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_162_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4512), (Sat.Literal.neg 162), (Sat.Literal.neg 84), (Sat.Literal.pos 4513)] :=
  (lex_11_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_162_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4512), (Sat.Literal.pos 162), (Sat.Literal.pos 84), (Sat.Literal.pos 4513)] :=
  (lex_11_162_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_161_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4513) = lexBefore s permutation11 161 := by
  exact (positive_lex_of_descriptor s 4513 permutation11 162 (by rfl)).trans ((lex_skipped s permutation11 161 162 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 162 162 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_161_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 52) = s (permuteMask permutation11 161) := by
  exact (positive_select s 52).trans (congrArg s (show (52 : Fin 256) = permuteMask permutation11 161 by rw [image11_eq]; rfl))

theorem lex_11_161_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4514) (Sat.Literal.pos 4513) (Sat.Literal.pos 161) (Sat.Literal.pos 52)) := by
  exact equality_gate s permutation11 161 (assignment s)
    (Sat.Literal.pos 4514) (Sat.Literal.pos 4513) (Sat.Literal.pos 161) (Sat.Literal.pos 52) (positive_of_descriptor s 4514 (.lex permutation11 161) (by rfl)) (lex_11_161_prefix s) (positive_select s 161) (lex_11_161_image s)

theorem lex_11_161_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4513), (Sat.Literal.pos 161), (Sat.Literal.neg 52)] := by
  exact comparison_gate s permutation11 161 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4513) (Sat.Literal.pos 161) (Sat.Literal.pos 52) (lex_11_161_prefix s) (positive_select s 161) (lex_11_161_image s)

theorem lex_11_161_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4514), (Sat.Literal.pos 4513)] :=
  (lex_11_161_gate s).prop _ (List.Mem.head _)

theorem lex_11_161_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4514), (Sat.Literal.neg 161), (Sat.Literal.pos 52)] :=
  (lex_11_161_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_161_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4514), (Sat.Literal.pos 161), (Sat.Literal.neg 52)] :=
  (lex_11_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_161_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4513), (Sat.Literal.neg 161), (Sat.Literal.neg 52), (Sat.Literal.pos 4514)] :=
  (lex_11_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_161_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4513), (Sat.Literal.pos 161), (Sat.Literal.pos 52), (Sat.Literal.pos 4514)] :=
  (lex_11_161_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_160_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4514) = lexBefore s permutation11 160 := by
  exact (positive_lex_of_descriptor s 4514 permutation11 161 (by rfl)).trans ((lex_skipped s permutation11 160 161 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 161 161 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_160_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 20) = s (permuteMask permutation11 160) := by
  exact (positive_select s 20).trans (congrArg s (show (20 : Fin 256) = permuteMask permutation11 160 by rw [image11_eq]; rfl))

theorem lex_11_160_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4515) (Sat.Literal.pos 4514) (Sat.Literal.pos 160) (Sat.Literal.pos 20)) := by
  exact equality_gate s permutation11 160 (assignment s)
    (Sat.Literal.pos 4515) (Sat.Literal.pos 4514) (Sat.Literal.pos 160) (Sat.Literal.pos 20) (positive_of_descriptor s 4515 (.lex permutation11 160) (by rfl)) (lex_11_160_prefix s) (positive_select s 160) (lex_11_160_image s)

theorem lex_11_160_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4514), (Sat.Literal.pos 160), (Sat.Literal.neg 20)] := by
  exact comparison_gate s permutation11 160 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4514) (Sat.Literal.pos 160) (Sat.Literal.pos 20) (lex_11_160_prefix s) (positive_select s 160) (lex_11_160_image s)

theorem lex_11_160_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4515), (Sat.Literal.pos 4514)] :=
  (lex_11_160_gate s).prop _ (List.Mem.head _)

theorem lex_11_160_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4515), (Sat.Literal.neg 160), (Sat.Literal.pos 20)] :=
  (lex_11_160_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_160_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4515), (Sat.Literal.pos 160), (Sat.Literal.neg 20)] :=
  (lex_11_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_160_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4514), (Sat.Literal.neg 160), (Sat.Literal.neg 20), (Sat.Literal.pos 4515)] :=
  (lex_11_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_160_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4514), (Sat.Literal.pos 160), (Sat.Literal.pos 20), (Sat.Literal.pos 4515)] :=
  (lex_11_160_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4515) = lexBefore s permutation11 159 := by
  exact (positive_lex_of_descriptor s 4515 permutation11 160 (by rfl)).trans ((lex_skipped s permutation11 159 160 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 243) = s (permuteMask permutation11 159) := by
  exact (positive_select s 243).trans (congrArg s (show (243 : Fin 256) = permuteMask permutation11 159 by rw [image11_eq]; rfl))

theorem lex_11_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4516) (Sat.Literal.pos 4515) (Sat.Literal.pos 159) (Sat.Literal.pos 243)) := by
  exact equality_gate s permutation11 159 (assignment s)
    (Sat.Literal.pos 4516) (Sat.Literal.pos 4515) (Sat.Literal.pos 159) (Sat.Literal.pos 243) (positive_of_descriptor s 4516 (.lex permutation11 159) (by rfl)) (lex_11_159_prefix s) (positive_select s 159) (lex_11_159_image s)

theorem lex_11_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4515), (Sat.Literal.pos 159), (Sat.Literal.neg 243)] := by
  exact comparison_gate s permutation11 159 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4515) (Sat.Literal.pos 159) (Sat.Literal.pos 243) (lex_11_159_prefix s) (positive_select s 159) (lex_11_159_image s)

theorem lex_11_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4516), (Sat.Literal.pos 4515)] :=
  (lex_11_159_gate s).prop _ (List.Mem.head _)

theorem lex_11_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4516), (Sat.Literal.neg 159), (Sat.Literal.pos 243)] :=
  (lex_11_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4516), (Sat.Literal.pos 159), (Sat.Literal.neg 243)] :=
  (lex_11_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4515), (Sat.Literal.neg 159), (Sat.Literal.neg 243), (Sat.Literal.pos 4516)] :=
  (lex_11_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4515), (Sat.Literal.pos 159), (Sat.Literal.pos 243), (Sat.Literal.pos 4516)] :=
  (lex_11_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4516) = lexBefore s permutation11 158 := by
  exact (positive_lex_of_descriptor s 4516 permutation11 159 (by rfl)).trans ((lex_skipped s permutation11 158 159 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 211) = s (permuteMask permutation11 158) := by
  exact (positive_select s 211).trans (congrArg s (show (211 : Fin 256) = permuteMask permutation11 158 by rw [image11_eq]; rfl))

theorem lex_11_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4517) (Sat.Literal.pos 4516) (Sat.Literal.pos 158) (Sat.Literal.pos 211)) := by
  exact equality_gate s permutation11 158 (assignment s)
    (Sat.Literal.pos 4517) (Sat.Literal.pos 4516) (Sat.Literal.pos 158) (Sat.Literal.pos 211) (positive_of_descriptor s 4517 (.lex permutation11 158) (by rfl)) (lex_11_158_prefix s) (positive_select s 158) (lex_11_158_image s)

theorem lex_11_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4516), (Sat.Literal.pos 158), (Sat.Literal.neg 211)] := by
  exact comparison_gate s permutation11 158 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4516) (Sat.Literal.pos 158) (Sat.Literal.pos 211) (lex_11_158_prefix s) (positive_select s 158) (lex_11_158_image s)

theorem lex_11_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4517), (Sat.Literal.pos 4516)] :=
  (lex_11_158_gate s).prop _ (List.Mem.head _)

theorem lex_11_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4517), (Sat.Literal.neg 158), (Sat.Literal.pos 211)] :=
  (lex_11_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4517), (Sat.Literal.pos 158), (Sat.Literal.neg 211)] :=
  (lex_11_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4516), (Sat.Literal.neg 158), (Sat.Literal.neg 211), (Sat.Literal.pos 4517)] :=
  (lex_11_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4516), (Sat.Literal.pos 158), (Sat.Literal.pos 211), (Sat.Literal.pos 4517)] :=
  (lex_11_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4517) = lexBefore s permutation11 157 := by
  exact (positive_lex_of_descriptor s 4517 permutation11 158 (by rfl)).trans ((lex_skipped s permutation11 157 158 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation11 157) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation11 157 by rw [image11_eq]; rfl))

theorem lex_11_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4518) (Sat.Literal.pos 4517) (Sat.Literal.pos 157) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation11 157 (assignment s)
    (Sat.Literal.pos 4518) (Sat.Literal.pos 4517) (Sat.Literal.pos 157) (Sat.Literal.pos 179) (positive_of_descriptor s 4518 (.lex permutation11 157) (by rfl)) (lex_11_157_prefix s) (positive_select s 157) (lex_11_157_image s)

theorem lex_11_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4517), (Sat.Literal.pos 157), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation11 157 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4517) (Sat.Literal.pos 157) (Sat.Literal.pos 179) (lex_11_157_prefix s) (positive_select s 157) (lex_11_157_image s)

theorem lex_11_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4518), (Sat.Literal.pos 4517)] :=
  (lex_11_157_gate s).prop _ (List.Mem.head _)

theorem lex_11_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4518), (Sat.Literal.neg 157), (Sat.Literal.pos 179)] :=
  (lex_11_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4518), (Sat.Literal.pos 157), (Sat.Literal.neg 179)] :=
  (lex_11_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4517), (Sat.Literal.neg 157), (Sat.Literal.neg 179), (Sat.Literal.pos 4518)] :=
  (lex_11_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4517), (Sat.Literal.pos 157), (Sat.Literal.pos 179), (Sat.Literal.pos 4518)] :=
  (lex_11_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4518) = lexBefore s permutation11 156 := by
  exact (positive_lex_of_descriptor s 4518 permutation11 157 (by rfl)).trans ((lex_skipped s permutation11 156 157 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation11 156) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation11 156 by rw [image11_eq]; rfl))

theorem lex_11_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4519) (Sat.Literal.pos 4518) (Sat.Literal.pos 156) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation11 156 (assignment s)
    (Sat.Literal.pos 4519) (Sat.Literal.pos 4518) (Sat.Literal.pos 156) (Sat.Literal.pos 147) (positive_of_descriptor s 4519 (.lex permutation11 156) (by rfl)) (lex_11_156_prefix s) (positive_select s 156) (lex_11_156_image s)

theorem lex_11_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4518), (Sat.Literal.pos 156), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation11 156 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4518) (Sat.Literal.pos 156) (Sat.Literal.pos 147) (lex_11_156_prefix s) (positive_select s 156) (lex_11_156_image s)

theorem lex_11_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4519), (Sat.Literal.pos 4518)] :=
  (lex_11_156_gate s).prop _ (List.Mem.head _)

theorem lex_11_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4519), (Sat.Literal.neg 156), (Sat.Literal.pos 147)] :=
  (lex_11_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4519), (Sat.Literal.pos 156), (Sat.Literal.neg 147)] :=
  (lex_11_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4518), (Sat.Literal.neg 156), (Sat.Literal.neg 147), (Sat.Literal.pos 4519)] :=
  (lex_11_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4518), (Sat.Literal.pos 156), (Sat.Literal.pos 147), (Sat.Literal.pos 4519)] :=
  (lex_11_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4519) = lexBefore s permutation11 155 := by
  exact (positive_lex_of_descriptor s 4519 permutation11 156 (by rfl)).trans ((lex_skipped s permutation11 155 156 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 115) = s (permuteMask permutation11 155) := by
  exact (positive_select s 115).trans (congrArg s (show (115 : Fin 256) = permuteMask permutation11 155 by rw [image11_eq]; rfl))

theorem lex_11_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4520) (Sat.Literal.pos 4519) (Sat.Literal.pos 155) (Sat.Literal.pos 115)) := by
  exact equality_gate s permutation11 155 (assignment s)
    (Sat.Literal.pos 4520) (Sat.Literal.pos 4519) (Sat.Literal.pos 155) (Sat.Literal.pos 115) (positive_of_descriptor s 4520 (.lex permutation11 155) (by rfl)) (lex_11_155_prefix s) (positive_select s 155) (lex_11_155_image s)

theorem lex_11_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4519), (Sat.Literal.pos 155), (Sat.Literal.neg 115)] := by
  exact comparison_gate s permutation11 155 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4519) (Sat.Literal.pos 155) (Sat.Literal.pos 115) (lex_11_155_prefix s) (positive_select s 155) (lex_11_155_image s)

theorem lex_11_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4520), (Sat.Literal.pos 4519)] :=
  (lex_11_155_gate s).prop _ (List.Mem.head _)

theorem lex_11_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4520), (Sat.Literal.neg 155), (Sat.Literal.pos 115)] :=
  (lex_11_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4520), (Sat.Literal.pos 155), (Sat.Literal.neg 115)] :=
  (lex_11_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4519), (Sat.Literal.neg 155), (Sat.Literal.neg 115), (Sat.Literal.pos 4520)] :=
  (lex_11_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4519), (Sat.Literal.pos 155), (Sat.Literal.pos 115), (Sat.Literal.pos 4520)] :=
  (lex_11_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4520) = lexBefore s permutation11 154 := by
  exact (positive_lex_of_descriptor s 4520 permutation11 155 (by rfl)).trans ((lex_skipped s permutation11 154 155 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation11 154) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation11 154 by rw [image11_eq]; rfl))

theorem lex_11_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4521) (Sat.Literal.pos 4520) (Sat.Literal.pos 154) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation11 154 (assignment s)
    (Sat.Literal.pos 4521) (Sat.Literal.pos 4520) (Sat.Literal.pos 154) (Sat.Literal.pos 83) (positive_of_descriptor s 4521 (.lex permutation11 154) (by rfl)) (lex_11_154_prefix s) (positive_select s 154) (lex_11_154_image s)

theorem lex_11_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4520), (Sat.Literal.pos 154), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation11 154 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4520) (Sat.Literal.pos 154) (Sat.Literal.pos 83) (lex_11_154_prefix s) (positive_select s 154) (lex_11_154_image s)

theorem lex_11_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4521), (Sat.Literal.pos 4520)] :=
  (lex_11_154_gate s).prop _ (List.Mem.head _)

theorem lex_11_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4521), (Sat.Literal.neg 154), (Sat.Literal.pos 83)] :=
  (lex_11_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4521), (Sat.Literal.pos 154), (Sat.Literal.neg 83)] :=
  (lex_11_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4520), (Sat.Literal.neg 154), (Sat.Literal.neg 83), (Sat.Literal.pos 4521)] :=
  (lex_11_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4520), (Sat.Literal.pos 154), (Sat.Literal.pos 83), (Sat.Literal.pos 4521)] :=
  (lex_11_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4521) = lexBefore s permutation11 153 := by
  exact (positive_lex_of_descriptor s 4521 permutation11 154 (by rfl)).trans ((lex_skipped s permutation11 153 154 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 51) = s (permuteMask permutation11 153) := by
  exact (positive_select s 51).trans (congrArg s (show (51 : Fin 256) = permuteMask permutation11 153 by rw [image11_eq]; rfl))

theorem lex_11_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4522) (Sat.Literal.pos 4521) (Sat.Literal.pos 153) (Sat.Literal.pos 51)) := by
  exact equality_gate s permutation11 153 (assignment s)
    (Sat.Literal.pos 4522) (Sat.Literal.pos 4521) (Sat.Literal.pos 153) (Sat.Literal.pos 51) (positive_of_descriptor s 4522 (.lex permutation11 153) (by rfl)) (lex_11_153_prefix s) (positive_select s 153) (lex_11_153_image s)

theorem lex_11_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4521), (Sat.Literal.pos 153), (Sat.Literal.neg 51)] := by
  exact comparison_gate s permutation11 153 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4521) (Sat.Literal.pos 153) (Sat.Literal.pos 51) (lex_11_153_prefix s) (positive_select s 153) (lex_11_153_image s)

theorem lex_11_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4522), (Sat.Literal.pos 4521)] :=
  (lex_11_153_gate s).prop _ (List.Mem.head _)

theorem lex_11_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4522), (Sat.Literal.neg 153), (Sat.Literal.pos 51)] :=
  (lex_11_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4522), (Sat.Literal.pos 153), (Sat.Literal.neg 51)] :=
  (lex_11_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4521), (Sat.Literal.neg 153), (Sat.Literal.neg 51), (Sat.Literal.pos 4522)] :=
  (lex_11_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4521), (Sat.Literal.pos 153), (Sat.Literal.pos 51), (Sat.Literal.pos 4522)] :=
  (lex_11_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4522) = lexBefore s permutation11 152 := by
  exact (positive_lex_of_descriptor s 4522 permutation11 153 (by rfl)).trans ((lex_skipped s permutation11 152 153 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 19) = s (permuteMask permutation11 152) := by
  exact (positive_select s 19).trans (congrArg s (show (19 : Fin 256) = permuteMask permutation11 152 by rw [image11_eq]; rfl))

theorem lex_11_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4523) (Sat.Literal.pos 4522) (Sat.Literal.pos 152) (Sat.Literal.pos 19)) := by
  exact equality_gate s permutation11 152 (assignment s)
    (Sat.Literal.pos 4523) (Sat.Literal.pos 4522) (Sat.Literal.pos 152) (Sat.Literal.pos 19) (positive_of_descriptor s 4523 (.lex permutation11 152) (by rfl)) (lex_11_152_prefix s) (positive_select s 152) (lex_11_152_image s)

theorem lex_11_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4522), (Sat.Literal.pos 152), (Sat.Literal.neg 19)] := by
  exact comparison_gate s permutation11 152 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4522) (Sat.Literal.pos 152) (Sat.Literal.pos 19) (lex_11_152_prefix s) (positive_select s 152) (lex_11_152_image s)

theorem lex_11_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4523), (Sat.Literal.pos 4522)] :=
  (lex_11_152_gate s).prop _ (List.Mem.head _)

theorem lex_11_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4523), (Sat.Literal.neg 152), (Sat.Literal.pos 19)] :=
  (lex_11_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4523), (Sat.Literal.pos 152), (Sat.Literal.neg 19)] :=
  (lex_11_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4522), (Sat.Literal.neg 152), (Sat.Literal.neg 19), (Sat.Literal.pos 4523)] :=
  (lex_11_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4522), (Sat.Literal.pos 152), (Sat.Literal.pos 19), (Sat.Literal.pos 4523)] :=
  (lex_11_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_11_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 4523) = lexBefore s permutation11 151 := by
  exact (positive_lex_of_descriptor s 4523 permutation11 152 (by rfl)).trans ((lex_skipped s permutation11 151 152 (by decide) (by intro j hj hp; rw [image11_eq]; exact fixedOnRange_spec image11 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_11_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 242) = s (permuteMask permutation11 151) := by
  exact (positive_select s 242).trans (congrArg s (show (242 : Fin 256) = permuteMask permutation11 151 by rw [image11_eq]; rfl))

theorem lex_11_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 4524) (Sat.Literal.pos 4523) (Sat.Literal.pos 151) (Sat.Literal.pos 242)) := by
  exact equality_gate s permutation11 151 (assignment s)
    (Sat.Literal.pos 4524) (Sat.Literal.pos 4523) (Sat.Literal.pos 151) (Sat.Literal.pos 242) (positive_of_descriptor s 4524 (.lex permutation11 151) (by rfl)) (lex_11_151_prefix s) (positive_select s 151) (lex_11_151_image s)

theorem lex_11_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4523), (Sat.Literal.pos 151), (Sat.Literal.neg 242)] := by
  exact comparison_gate s permutation11 151 (hmax permutation11) (assignment s)
    (Sat.Literal.pos 4523) (Sat.Literal.pos 151) (Sat.Literal.pos 242) (lex_11_151_prefix s) (positive_select s 151) (lex_11_151_image s)

theorem lex_11_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4524), (Sat.Literal.pos 4523)] :=
  (lex_11_151_gate s).prop _ (List.Mem.head _)

theorem lex_11_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4524), (Sat.Literal.neg 151), (Sat.Literal.pos 242)] :=
  (lex_11_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_11_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4524), (Sat.Literal.pos 151), (Sat.Literal.neg 242)] :=
  (lex_11_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_11_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4523), (Sat.Literal.neg 151), (Sat.Literal.neg 242), (Sat.Literal.pos 4524)] :=
  (lex_11_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_11_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 4523), (Sat.Literal.pos 151), (Sat.Literal.pos 242), (Sat.Literal.pos 4524)] :=
  (lex_11_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_11_250_gate

end Crown.CertificateData
