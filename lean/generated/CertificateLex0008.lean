import Crown.CertificateLexLookup

namespace Crown.CertificateData
open Crown.CertificateSemantics Crown.CertificateValuation Crown.CertificateAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem lex_6_159_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3324) = lexBefore s permutation6 159 := by
  exact (positive_lex_of_descriptor s 3324 permutation6 160 (by rfl)).trans ((lex_skipped s permutation6 159 160 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 160 160 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_159_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 95) = s (permuteMask permutation6 159) := by
  exact (positive_select s 95).trans (congrArg s (show (95 : Fin 256) = permuteMask permutation6 159 by rw [image6_eq]; rfl))

theorem lex_6_159_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3325) (Sat.Literal.pos 3324) (Sat.Literal.pos 159) (Sat.Literal.pos 95)) := by
  exact equality_gate s permutation6 159 (assignment s)
    (Sat.Literal.pos 3325) (Sat.Literal.pos 3324) (Sat.Literal.pos 159) (Sat.Literal.pos 95) (positive_of_descriptor s 3325 (.lex permutation6 159) (by rfl)) (lex_6_159_prefix s) (positive_select s 159) (lex_6_159_image s)

theorem lex_6_159_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3324), (Sat.Literal.pos 159), (Sat.Literal.neg 95)] := by
  exact comparison_gate s permutation6 159 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3324) (Sat.Literal.pos 159) (Sat.Literal.pos 95) (lex_6_159_prefix s) (positive_select s 159) (lex_6_159_image s)

theorem lex_6_159_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3325), (Sat.Literal.pos 3324)] :=
  (lex_6_159_gate s).prop _ (List.Mem.head _)

theorem lex_6_159_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3325), (Sat.Literal.neg 159), (Sat.Literal.pos 95)] :=
  (lex_6_159_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_159_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3325), (Sat.Literal.pos 159), (Sat.Literal.neg 95)] :=
  (lex_6_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_159_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3324), (Sat.Literal.neg 159), (Sat.Literal.neg 95), (Sat.Literal.pos 3325)] :=
  (lex_6_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_159_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3324), (Sat.Literal.pos 159), (Sat.Literal.pos 95), (Sat.Literal.pos 3325)] :=
  (lex_6_159_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_158_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3325) = lexBefore s permutation6 158 := by
  exact (positive_lex_of_descriptor s 3325 permutation6 159 (by rfl)).trans ((lex_skipped s permutation6 158 159 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 159 159 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_158_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 94) = s (permuteMask permutation6 158) := by
  exact (positive_select s 94).trans (congrArg s (show (94 : Fin 256) = permuteMask permutation6 158 by rw [image6_eq]; rfl))

theorem lex_6_158_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3326) (Sat.Literal.pos 3325) (Sat.Literal.pos 158) (Sat.Literal.pos 94)) := by
  exact equality_gate s permutation6 158 (assignment s)
    (Sat.Literal.pos 3326) (Sat.Literal.pos 3325) (Sat.Literal.pos 158) (Sat.Literal.pos 94) (positive_of_descriptor s 3326 (.lex permutation6 158) (by rfl)) (lex_6_158_prefix s) (positive_select s 158) (lex_6_158_image s)

theorem lex_6_158_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3325), (Sat.Literal.pos 158), (Sat.Literal.neg 94)] := by
  exact comparison_gate s permutation6 158 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3325) (Sat.Literal.pos 158) (Sat.Literal.pos 94) (lex_6_158_prefix s) (positive_select s 158) (lex_6_158_image s)

theorem lex_6_158_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3326), (Sat.Literal.pos 3325)] :=
  (lex_6_158_gate s).prop _ (List.Mem.head _)

theorem lex_6_158_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3326), (Sat.Literal.neg 158), (Sat.Literal.pos 94)] :=
  (lex_6_158_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_158_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3326), (Sat.Literal.pos 158), (Sat.Literal.neg 94)] :=
  (lex_6_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_158_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3325), (Sat.Literal.neg 158), (Sat.Literal.neg 94), (Sat.Literal.pos 3326)] :=
  (lex_6_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_158_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3325), (Sat.Literal.pos 158), (Sat.Literal.pos 94), (Sat.Literal.pos 3326)] :=
  (lex_6_158_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_157_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3326) = lexBefore s permutation6 157 := by
  exact (positive_lex_of_descriptor s 3326 permutation6 158 (by rfl)).trans ((lex_skipped s permutation6 157 158 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 158 158 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_157_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 93) = s (permuteMask permutation6 157) := by
  exact (positive_select s 93).trans (congrArg s (show (93 : Fin 256) = permuteMask permutation6 157 by rw [image6_eq]; rfl))

theorem lex_6_157_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3327) (Sat.Literal.pos 3326) (Sat.Literal.pos 157) (Sat.Literal.pos 93)) := by
  exact equality_gate s permutation6 157 (assignment s)
    (Sat.Literal.pos 3327) (Sat.Literal.pos 3326) (Sat.Literal.pos 157) (Sat.Literal.pos 93) (positive_of_descriptor s 3327 (.lex permutation6 157) (by rfl)) (lex_6_157_prefix s) (positive_select s 157) (lex_6_157_image s)

theorem lex_6_157_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3326), (Sat.Literal.pos 157), (Sat.Literal.neg 93)] := by
  exact comparison_gate s permutation6 157 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3326) (Sat.Literal.pos 157) (Sat.Literal.pos 93) (lex_6_157_prefix s) (positive_select s 157) (lex_6_157_image s)

theorem lex_6_157_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3327), (Sat.Literal.pos 3326)] :=
  (lex_6_157_gate s).prop _ (List.Mem.head _)

theorem lex_6_157_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3327), (Sat.Literal.neg 157), (Sat.Literal.pos 93)] :=
  (lex_6_157_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_157_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3327), (Sat.Literal.pos 157), (Sat.Literal.neg 93)] :=
  (lex_6_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_157_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3326), (Sat.Literal.neg 157), (Sat.Literal.neg 93), (Sat.Literal.pos 3327)] :=
  (lex_6_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_157_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3326), (Sat.Literal.pos 157), (Sat.Literal.pos 93), (Sat.Literal.pos 3327)] :=
  (lex_6_157_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_156_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3327) = lexBefore s permutation6 156 := by
  exact (positive_lex_of_descriptor s 3327 permutation6 157 (by rfl)).trans ((lex_skipped s permutation6 156 157 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 157 157 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_156_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 92) = s (permuteMask permutation6 156) := by
  exact (positive_select s 92).trans (congrArg s (show (92 : Fin 256) = permuteMask permutation6 156 by rw [image6_eq]; rfl))

theorem lex_6_156_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3328) (Sat.Literal.pos 3327) (Sat.Literal.pos 156) (Sat.Literal.pos 92)) := by
  exact equality_gate s permutation6 156 (assignment s)
    (Sat.Literal.pos 3328) (Sat.Literal.pos 3327) (Sat.Literal.pos 156) (Sat.Literal.pos 92) (positive_of_descriptor s 3328 (.lex permutation6 156) (by rfl)) (lex_6_156_prefix s) (positive_select s 156) (lex_6_156_image s)

theorem lex_6_156_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3327), (Sat.Literal.pos 156), (Sat.Literal.neg 92)] := by
  exact comparison_gate s permutation6 156 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3327) (Sat.Literal.pos 156) (Sat.Literal.pos 92) (lex_6_156_prefix s) (positive_select s 156) (lex_6_156_image s)

theorem lex_6_156_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3328), (Sat.Literal.pos 3327)] :=
  (lex_6_156_gate s).prop _ (List.Mem.head _)

theorem lex_6_156_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3328), (Sat.Literal.neg 156), (Sat.Literal.pos 92)] :=
  (lex_6_156_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_156_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3328), (Sat.Literal.pos 156), (Sat.Literal.neg 92)] :=
  (lex_6_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_156_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3327), (Sat.Literal.neg 156), (Sat.Literal.neg 92), (Sat.Literal.pos 3328)] :=
  (lex_6_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_156_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3327), (Sat.Literal.pos 156), (Sat.Literal.pos 92), (Sat.Literal.pos 3328)] :=
  (lex_6_156_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_155_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3328) = lexBefore s permutation6 155 := by
  exact (positive_lex_of_descriptor s 3328 permutation6 156 (by rfl)).trans ((lex_skipped s permutation6 155 156 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 156 156 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_155_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 91) = s (permuteMask permutation6 155) := by
  exact (positive_select s 91).trans (congrArg s (show (91 : Fin 256) = permuteMask permutation6 155 by rw [image6_eq]; rfl))

theorem lex_6_155_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3329) (Sat.Literal.pos 3328) (Sat.Literal.pos 155) (Sat.Literal.pos 91)) := by
  exact equality_gate s permutation6 155 (assignment s)
    (Sat.Literal.pos 3329) (Sat.Literal.pos 3328) (Sat.Literal.pos 155) (Sat.Literal.pos 91) (positive_of_descriptor s 3329 (.lex permutation6 155) (by rfl)) (lex_6_155_prefix s) (positive_select s 155) (lex_6_155_image s)

theorem lex_6_155_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3328), (Sat.Literal.pos 155), (Sat.Literal.neg 91)] := by
  exact comparison_gate s permutation6 155 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3328) (Sat.Literal.pos 155) (Sat.Literal.pos 91) (lex_6_155_prefix s) (positive_select s 155) (lex_6_155_image s)

theorem lex_6_155_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3329), (Sat.Literal.pos 3328)] :=
  (lex_6_155_gate s).prop _ (List.Mem.head _)

theorem lex_6_155_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3329), (Sat.Literal.neg 155), (Sat.Literal.pos 91)] :=
  (lex_6_155_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_155_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3329), (Sat.Literal.pos 155), (Sat.Literal.neg 91)] :=
  (lex_6_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_155_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3328), (Sat.Literal.neg 155), (Sat.Literal.neg 91), (Sat.Literal.pos 3329)] :=
  (lex_6_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_155_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3328), (Sat.Literal.pos 155), (Sat.Literal.pos 91), (Sat.Literal.pos 3329)] :=
  (lex_6_155_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_154_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3329) = lexBefore s permutation6 154 := by
  exact (positive_lex_of_descriptor s 3329 permutation6 155 (by rfl)).trans ((lex_skipped s permutation6 154 155 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 155 155 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_154_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 90) = s (permuteMask permutation6 154) := by
  exact (positive_select s 90).trans (congrArg s (show (90 : Fin 256) = permuteMask permutation6 154 by rw [image6_eq]; rfl))

theorem lex_6_154_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3330) (Sat.Literal.pos 3329) (Sat.Literal.pos 154) (Sat.Literal.pos 90)) := by
  exact equality_gate s permutation6 154 (assignment s)
    (Sat.Literal.pos 3330) (Sat.Literal.pos 3329) (Sat.Literal.pos 154) (Sat.Literal.pos 90) (positive_of_descriptor s 3330 (.lex permutation6 154) (by rfl)) (lex_6_154_prefix s) (positive_select s 154) (lex_6_154_image s)

theorem lex_6_154_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3329), (Sat.Literal.pos 154), (Sat.Literal.neg 90)] := by
  exact comparison_gate s permutation6 154 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3329) (Sat.Literal.pos 154) (Sat.Literal.pos 90) (lex_6_154_prefix s) (positive_select s 154) (lex_6_154_image s)

theorem lex_6_154_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3330), (Sat.Literal.pos 3329)] :=
  (lex_6_154_gate s).prop _ (List.Mem.head _)

theorem lex_6_154_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3330), (Sat.Literal.neg 154), (Sat.Literal.pos 90)] :=
  (lex_6_154_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_154_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3330), (Sat.Literal.pos 154), (Sat.Literal.neg 90)] :=
  (lex_6_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_154_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3329), (Sat.Literal.neg 154), (Sat.Literal.neg 90), (Sat.Literal.pos 3330)] :=
  (lex_6_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_154_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3329), (Sat.Literal.pos 154), (Sat.Literal.pos 90), (Sat.Literal.pos 3330)] :=
  (lex_6_154_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_153_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3330) = lexBefore s permutation6 153 := by
  exact (positive_lex_of_descriptor s 3330 permutation6 154 (by rfl)).trans ((lex_skipped s permutation6 153 154 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 154 154 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_153_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 89) = s (permuteMask permutation6 153) := by
  exact (positive_select s 89).trans (congrArg s (show (89 : Fin 256) = permuteMask permutation6 153 by rw [image6_eq]; rfl))

theorem lex_6_153_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3331) (Sat.Literal.pos 3330) (Sat.Literal.pos 153) (Sat.Literal.pos 89)) := by
  exact equality_gate s permutation6 153 (assignment s)
    (Sat.Literal.pos 3331) (Sat.Literal.pos 3330) (Sat.Literal.pos 153) (Sat.Literal.pos 89) (positive_of_descriptor s 3331 (.lex permutation6 153) (by rfl)) (lex_6_153_prefix s) (positive_select s 153) (lex_6_153_image s)

theorem lex_6_153_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3330), (Sat.Literal.pos 153), (Sat.Literal.neg 89)] := by
  exact comparison_gate s permutation6 153 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3330) (Sat.Literal.pos 153) (Sat.Literal.pos 89) (lex_6_153_prefix s) (positive_select s 153) (lex_6_153_image s)

theorem lex_6_153_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3331), (Sat.Literal.pos 3330)] :=
  (lex_6_153_gate s).prop _ (List.Mem.head _)

theorem lex_6_153_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3331), (Sat.Literal.neg 153), (Sat.Literal.pos 89)] :=
  (lex_6_153_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_153_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3331), (Sat.Literal.pos 153), (Sat.Literal.neg 89)] :=
  (lex_6_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_153_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3330), (Sat.Literal.neg 153), (Sat.Literal.neg 89), (Sat.Literal.pos 3331)] :=
  (lex_6_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_153_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3330), (Sat.Literal.pos 153), (Sat.Literal.pos 89), (Sat.Literal.pos 3331)] :=
  (lex_6_153_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_152_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3331) = lexBefore s permutation6 152 := by
  exact (positive_lex_of_descriptor s 3331 permutation6 153 (by rfl)).trans ((lex_skipped s permutation6 152 153 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 153 153 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_152_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 88) = s (permuteMask permutation6 152) := by
  exact (positive_select s 88).trans (congrArg s (show (88 : Fin 256) = permuteMask permutation6 152 by rw [image6_eq]; rfl))

theorem lex_6_152_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3332) (Sat.Literal.pos 3331) (Sat.Literal.pos 152) (Sat.Literal.pos 88)) := by
  exact equality_gate s permutation6 152 (assignment s)
    (Sat.Literal.pos 3332) (Sat.Literal.pos 3331) (Sat.Literal.pos 152) (Sat.Literal.pos 88) (positive_of_descriptor s 3332 (.lex permutation6 152) (by rfl)) (lex_6_152_prefix s) (positive_select s 152) (lex_6_152_image s)

theorem lex_6_152_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3331), (Sat.Literal.pos 152), (Sat.Literal.neg 88)] := by
  exact comparison_gate s permutation6 152 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3331) (Sat.Literal.pos 152) (Sat.Literal.pos 88) (lex_6_152_prefix s) (positive_select s 152) (lex_6_152_image s)

theorem lex_6_152_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3332), (Sat.Literal.pos 3331)] :=
  (lex_6_152_gate s).prop _ (List.Mem.head _)

theorem lex_6_152_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3332), (Sat.Literal.neg 152), (Sat.Literal.pos 88)] :=
  (lex_6_152_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_152_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3332), (Sat.Literal.pos 152), (Sat.Literal.neg 88)] :=
  (lex_6_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_152_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3331), (Sat.Literal.neg 152), (Sat.Literal.neg 88), (Sat.Literal.pos 3332)] :=
  (lex_6_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_152_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3331), (Sat.Literal.pos 152), (Sat.Literal.pos 88), (Sat.Literal.pos 3332)] :=
  (lex_6_152_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_151_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3332) = lexBefore s permutation6 151 := by
  exact (positive_lex_of_descriptor s 3332 permutation6 152 (by rfl)).trans ((lex_skipped s permutation6 151 152 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 152 152 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_151_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 87) = s (permuteMask permutation6 151) := by
  exact (positive_select s 87).trans (congrArg s (show (87 : Fin 256) = permuteMask permutation6 151 by rw [image6_eq]; rfl))

theorem lex_6_151_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3333) (Sat.Literal.pos 3332) (Sat.Literal.pos 151) (Sat.Literal.pos 87)) := by
  exact equality_gate s permutation6 151 (assignment s)
    (Sat.Literal.pos 3333) (Sat.Literal.pos 3332) (Sat.Literal.pos 151) (Sat.Literal.pos 87) (positive_of_descriptor s 3333 (.lex permutation6 151) (by rfl)) (lex_6_151_prefix s) (positive_select s 151) (lex_6_151_image s)

theorem lex_6_151_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3332), (Sat.Literal.pos 151), (Sat.Literal.neg 87)] := by
  exact comparison_gate s permutation6 151 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3332) (Sat.Literal.pos 151) (Sat.Literal.pos 87) (lex_6_151_prefix s) (positive_select s 151) (lex_6_151_image s)

theorem lex_6_151_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3333), (Sat.Literal.pos 3332)] :=
  (lex_6_151_gate s).prop _ (List.Mem.head _)

theorem lex_6_151_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3333), (Sat.Literal.neg 151), (Sat.Literal.pos 87)] :=
  (lex_6_151_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_151_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3333), (Sat.Literal.pos 151), (Sat.Literal.neg 87)] :=
  (lex_6_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_151_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3332), (Sat.Literal.neg 151), (Sat.Literal.neg 87), (Sat.Literal.pos 3333)] :=
  (lex_6_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_151_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3332), (Sat.Literal.pos 151), (Sat.Literal.pos 87), (Sat.Literal.pos 3333)] :=
  (lex_6_151_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_150_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3333) = lexBefore s permutation6 150 := by
  exact (positive_lex_of_descriptor s 3333 permutation6 151 (by rfl)).trans ((lex_skipped s permutation6 150 151 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 151 151 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_150_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 86) = s (permuteMask permutation6 150) := by
  exact (positive_select s 86).trans (congrArg s (show (86 : Fin 256) = permuteMask permutation6 150 by rw [image6_eq]; rfl))

theorem lex_6_150_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3334) (Sat.Literal.pos 3333) (Sat.Literal.pos 150) (Sat.Literal.pos 86)) := by
  exact equality_gate s permutation6 150 (assignment s)
    (Sat.Literal.pos 3334) (Sat.Literal.pos 3333) (Sat.Literal.pos 150) (Sat.Literal.pos 86) (positive_of_descriptor s 3334 (.lex permutation6 150) (by rfl)) (lex_6_150_prefix s) (positive_select s 150) (lex_6_150_image s)

theorem lex_6_150_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3333), (Sat.Literal.pos 150), (Sat.Literal.neg 86)] := by
  exact comparison_gate s permutation6 150 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3333) (Sat.Literal.pos 150) (Sat.Literal.pos 86) (lex_6_150_prefix s) (positive_select s 150) (lex_6_150_image s)

theorem lex_6_150_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3334), (Sat.Literal.pos 3333)] :=
  (lex_6_150_gate s).prop _ (List.Mem.head _)

theorem lex_6_150_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3334), (Sat.Literal.neg 150), (Sat.Literal.pos 86)] :=
  (lex_6_150_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_150_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3334), (Sat.Literal.pos 150), (Sat.Literal.neg 86)] :=
  (lex_6_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_150_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3333), (Sat.Literal.neg 150), (Sat.Literal.neg 86), (Sat.Literal.pos 3334)] :=
  (lex_6_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_150_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3333), (Sat.Literal.pos 150), (Sat.Literal.pos 86), (Sat.Literal.pos 3334)] :=
  (lex_6_150_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_149_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3334) = lexBefore s permutation6 149 := by
  exact (positive_lex_of_descriptor s 3334 permutation6 150 (by rfl)).trans ((lex_skipped s permutation6 149 150 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 150 150 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_149_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 85) = s (permuteMask permutation6 149) := by
  exact (positive_select s 85).trans (congrArg s (show (85 : Fin 256) = permuteMask permutation6 149 by rw [image6_eq]; rfl))

theorem lex_6_149_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3335) (Sat.Literal.pos 3334) (Sat.Literal.pos 149) (Sat.Literal.pos 85)) := by
  exact equality_gate s permutation6 149 (assignment s)
    (Sat.Literal.pos 3335) (Sat.Literal.pos 3334) (Sat.Literal.pos 149) (Sat.Literal.pos 85) (positive_of_descriptor s 3335 (.lex permutation6 149) (by rfl)) (lex_6_149_prefix s) (positive_select s 149) (lex_6_149_image s)

theorem lex_6_149_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3334), (Sat.Literal.pos 149), (Sat.Literal.neg 85)] := by
  exact comparison_gate s permutation6 149 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3334) (Sat.Literal.pos 149) (Sat.Literal.pos 85) (lex_6_149_prefix s) (positive_select s 149) (lex_6_149_image s)

theorem lex_6_149_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3335), (Sat.Literal.pos 3334)] :=
  (lex_6_149_gate s).prop _ (List.Mem.head _)

theorem lex_6_149_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3335), (Sat.Literal.neg 149), (Sat.Literal.pos 85)] :=
  (lex_6_149_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_149_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3335), (Sat.Literal.pos 149), (Sat.Literal.neg 85)] :=
  (lex_6_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_149_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3334), (Sat.Literal.neg 149), (Sat.Literal.neg 85), (Sat.Literal.pos 3335)] :=
  (lex_6_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_149_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3334), (Sat.Literal.pos 149), (Sat.Literal.pos 85), (Sat.Literal.pos 3335)] :=
  (lex_6_149_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_148_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3335) = lexBefore s permutation6 148 := by
  exact (positive_lex_of_descriptor s 3335 permutation6 149 (by rfl)).trans ((lex_skipped s permutation6 148 149 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 149 149 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_148_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 84) = s (permuteMask permutation6 148) := by
  exact (positive_select s 84).trans (congrArg s (show (84 : Fin 256) = permuteMask permutation6 148 by rw [image6_eq]; rfl))

theorem lex_6_148_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3336) (Sat.Literal.pos 3335) (Sat.Literal.pos 148) (Sat.Literal.pos 84)) := by
  exact equality_gate s permutation6 148 (assignment s)
    (Sat.Literal.pos 3336) (Sat.Literal.pos 3335) (Sat.Literal.pos 148) (Sat.Literal.pos 84) (positive_of_descriptor s 3336 (.lex permutation6 148) (by rfl)) (lex_6_148_prefix s) (positive_select s 148) (lex_6_148_image s)

theorem lex_6_148_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3335), (Sat.Literal.pos 148), (Sat.Literal.neg 84)] := by
  exact comparison_gate s permutation6 148 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3335) (Sat.Literal.pos 148) (Sat.Literal.pos 84) (lex_6_148_prefix s) (positive_select s 148) (lex_6_148_image s)

theorem lex_6_148_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3336), (Sat.Literal.pos 3335)] :=
  (lex_6_148_gate s).prop _ (List.Mem.head _)

theorem lex_6_148_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3336), (Sat.Literal.neg 148), (Sat.Literal.pos 84)] :=
  (lex_6_148_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_148_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3336), (Sat.Literal.pos 148), (Sat.Literal.neg 84)] :=
  (lex_6_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_148_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3335), (Sat.Literal.neg 148), (Sat.Literal.neg 84), (Sat.Literal.pos 3336)] :=
  (lex_6_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_148_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3335), (Sat.Literal.pos 148), (Sat.Literal.pos 84), (Sat.Literal.pos 3336)] :=
  (lex_6_148_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_147_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3336) = lexBefore s permutation6 147 := by
  exact (positive_lex_of_descriptor s 3336 permutation6 148 (by rfl)).trans ((lex_skipped s permutation6 147 148 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 148 148 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_147_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 83) = s (permuteMask permutation6 147) := by
  exact (positive_select s 83).trans (congrArg s (show (83 : Fin 256) = permuteMask permutation6 147 by rw [image6_eq]; rfl))

theorem lex_6_147_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3337) (Sat.Literal.pos 3336) (Sat.Literal.pos 147) (Sat.Literal.pos 83)) := by
  exact equality_gate s permutation6 147 (assignment s)
    (Sat.Literal.pos 3337) (Sat.Literal.pos 3336) (Sat.Literal.pos 147) (Sat.Literal.pos 83) (positive_of_descriptor s 3337 (.lex permutation6 147) (by rfl)) (lex_6_147_prefix s) (positive_select s 147) (lex_6_147_image s)

theorem lex_6_147_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3336), (Sat.Literal.pos 147), (Sat.Literal.neg 83)] := by
  exact comparison_gate s permutation6 147 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3336) (Sat.Literal.pos 147) (Sat.Literal.pos 83) (lex_6_147_prefix s) (positive_select s 147) (lex_6_147_image s)

theorem lex_6_147_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3337), (Sat.Literal.pos 3336)] :=
  (lex_6_147_gate s).prop _ (List.Mem.head _)

theorem lex_6_147_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3337), (Sat.Literal.neg 147), (Sat.Literal.pos 83)] :=
  (lex_6_147_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_147_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3337), (Sat.Literal.pos 147), (Sat.Literal.neg 83)] :=
  (lex_6_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_147_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3336), (Sat.Literal.neg 147), (Sat.Literal.neg 83), (Sat.Literal.pos 3337)] :=
  (lex_6_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_147_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3336), (Sat.Literal.pos 147), (Sat.Literal.pos 83), (Sat.Literal.pos 3337)] :=
  (lex_6_147_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_146_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3337) = lexBefore s permutation6 146 := by
  exact (positive_lex_of_descriptor s 3337 permutation6 147 (by rfl)).trans ((lex_skipped s permutation6 146 147 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 147 147 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_146_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 82) = s (permuteMask permutation6 146) := by
  exact (positive_select s 82).trans (congrArg s (show (82 : Fin 256) = permuteMask permutation6 146 by rw [image6_eq]; rfl))

theorem lex_6_146_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3338) (Sat.Literal.pos 3337) (Sat.Literal.pos 146) (Sat.Literal.pos 82)) := by
  exact equality_gate s permutation6 146 (assignment s)
    (Sat.Literal.pos 3338) (Sat.Literal.pos 3337) (Sat.Literal.pos 146) (Sat.Literal.pos 82) (positive_of_descriptor s 3338 (.lex permutation6 146) (by rfl)) (lex_6_146_prefix s) (positive_select s 146) (lex_6_146_image s)

theorem lex_6_146_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3337), (Sat.Literal.pos 146), (Sat.Literal.neg 82)] := by
  exact comparison_gate s permutation6 146 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3337) (Sat.Literal.pos 146) (Sat.Literal.pos 82) (lex_6_146_prefix s) (positive_select s 146) (lex_6_146_image s)

theorem lex_6_146_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3338), (Sat.Literal.pos 3337)] :=
  (lex_6_146_gate s).prop _ (List.Mem.head _)

theorem lex_6_146_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3338), (Sat.Literal.neg 146), (Sat.Literal.pos 82)] :=
  (lex_6_146_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_146_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3338), (Sat.Literal.pos 146), (Sat.Literal.neg 82)] :=
  (lex_6_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_146_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3337), (Sat.Literal.neg 146), (Sat.Literal.neg 82), (Sat.Literal.pos 3338)] :=
  (lex_6_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_146_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3337), (Sat.Literal.pos 146), (Sat.Literal.pos 82), (Sat.Literal.pos 3338)] :=
  (lex_6_146_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_145_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3338) = lexBefore s permutation6 145 := by
  exact (positive_lex_of_descriptor s 3338 permutation6 146 (by rfl)).trans ((lex_skipped s permutation6 145 146 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 146 146 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_145_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 81) = s (permuteMask permutation6 145) := by
  exact (positive_select s 81).trans (congrArg s (show (81 : Fin 256) = permuteMask permutation6 145 by rw [image6_eq]; rfl))

theorem lex_6_145_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3339) (Sat.Literal.pos 3338) (Sat.Literal.pos 145) (Sat.Literal.pos 81)) := by
  exact equality_gate s permutation6 145 (assignment s)
    (Sat.Literal.pos 3339) (Sat.Literal.pos 3338) (Sat.Literal.pos 145) (Sat.Literal.pos 81) (positive_of_descriptor s 3339 (.lex permutation6 145) (by rfl)) (lex_6_145_prefix s) (positive_select s 145) (lex_6_145_image s)

theorem lex_6_145_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3338), (Sat.Literal.pos 145), (Sat.Literal.neg 81)] := by
  exact comparison_gate s permutation6 145 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3338) (Sat.Literal.pos 145) (Sat.Literal.pos 81) (lex_6_145_prefix s) (positive_select s 145) (lex_6_145_image s)

theorem lex_6_145_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3339), (Sat.Literal.pos 3338)] :=
  (lex_6_145_gate s).prop _ (List.Mem.head _)

theorem lex_6_145_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3339), (Sat.Literal.neg 145), (Sat.Literal.pos 81)] :=
  (lex_6_145_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_145_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3339), (Sat.Literal.pos 145), (Sat.Literal.neg 81)] :=
  (lex_6_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_145_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3338), (Sat.Literal.neg 145), (Sat.Literal.neg 81), (Sat.Literal.pos 3339)] :=
  (lex_6_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_145_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3338), (Sat.Literal.pos 145), (Sat.Literal.pos 81), (Sat.Literal.pos 3339)] :=
  (lex_6_145_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_144_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3339) = lexBefore s permutation6 144 := by
  exact (positive_lex_of_descriptor s 3339 permutation6 145 (by rfl)).trans ((lex_skipped s permutation6 144 145 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 145 145 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_144_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 80) = s (permuteMask permutation6 144) := by
  exact (positive_select s 80).trans (congrArg s (show (80 : Fin 256) = permuteMask permutation6 144 by rw [image6_eq]; rfl))

theorem lex_6_144_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3340) (Sat.Literal.pos 3339) (Sat.Literal.pos 144) (Sat.Literal.pos 80)) := by
  exact equality_gate s permutation6 144 (assignment s)
    (Sat.Literal.pos 3340) (Sat.Literal.pos 3339) (Sat.Literal.pos 144) (Sat.Literal.pos 80) (positive_of_descriptor s 3340 (.lex permutation6 144) (by rfl)) (lex_6_144_prefix s) (positive_select s 144) (lex_6_144_image s)

theorem lex_6_144_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3339), (Sat.Literal.pos 144), (Sat.Literal.neg 80)] := by
  exact comparison_gate s permutation6 144 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3339) (Sat.Literal.pos 144) (Sat.Literal.pos 80) (lex_6_144_prefix s) (positive_select s 144) (lex_6_144_image s)

theorem lex_6_144_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3340), (Sat.Literal.pos 3339)] :=
  (lex_6_144_gate s).prop _ (List.Mem.head _)

theorem lex_6_144_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3340), (Sat.Literal.neg 144), (Sat.Literal.pos 80)] :=
  (lex_6_144_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_144_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3340), (Sat.Literal.pos 144), (Sat.Literal.neg 80)] :=
  (lex_6_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_144_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3339), (Sat.Literal.neg 144), (Sat.Literal.neg 80), (Sat.Literal.pos 3340)] :=
  (lex_6_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_144_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3339), (Sat.Literal.pos 144), (Sat.Literal.pos 80), (Sat.Literal.pos 3340)] :=
  (lex_6_144_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_143_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3340) = lexBefore s permutation6 143 := by
  exact (positive_lex_of_descriptor s 3340 permutation6 144 (by rfl)).trans ((lex_skipped s permutation6 143 144 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 144 144 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_143_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 79) = s (permuteMask permutation6 143) := by
  exact (positive_select s 79).trans (congrArg s (show (79 : Fin 256) = permuteMask permutation6 143 by rw [image6_eq]; rfl))

theorem lex_6_143_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3341) (Sat.Literal.pos 3340) (Sat.Literal.pos 143) (Sat.Literal.pos 79)) := by
  exact equality_gate s permutation6 143 (assignment s)
    (Sat.Literal.pos 3341) (Sat.Literal.pos 3340) (Sat.Literal.pos 143) (Sat.Literal.pos 79) (positive_of_descriptor s 3341 (.lex permutation6 143) (by rfl)) (lex_6_143_prefix s) (positive_select s 143) (lex_6_143_image s)

theorem lex_6_143_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3340), (Sat.Literal.pos 143), (Sat.Literal.neg 79)] := by
  exact comparison_gate s permutation6 143 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3340) (Sat.Literal.pos 143) (Sat.Literal.pos 79) (lex_6_143_prefix s) (positive_select s 143) (lex_6_143_image s)

theorem lex_6_143_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3341), (Sat.Literal.pos 3340)] :=
  (lex_6_143_gate s).prop _ (List.Mem.head _)

theorem lex_6_143_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3341), (Sat.Literal.neg 143), (Sat.Literal.pos 79)] :=
  (lex_6_143_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_143_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3341), (Sat.Literal.pos 143), (Sat.Literal.neg 79)] :=
  (lex_6_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_143_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3340), (Sat.Literal.neg 143), (Sat.Literal.neg 79), (Sat.Literal.pos 3341)] :=
  (lex_6_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_143_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3340), (Sat.Literal.pos 143), (Sat.Literal.pos 79), (Sat.Literal.pos 3341)] :=
  (lex_6_143_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_142_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3341) = lexBefore s permutation6 142 := by
  exact (positive_lex_of_descriptor s 3341 permutation6 143 (by rfl)).trans ((lex_skipped s permutation6 142 143 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 143 143 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_142_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 78) = s (permuteMask permutation6 142) := by
  exact (positive_select s 78).trans (congrArg s (show (78 : Fin 256) = permuteMask permutation6 142 by rw [image6_eq]; rfl))

theorem lex_6_142_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3342) (Sat.Literal.pos 3341) (Sat.Literal.pos 142) (Sat.Literal.pos 78)) := by
  exact equality_gate s permutation6 142 (assignment s)
    (Sat.Literal.pos 3342) (Sat.Literal.pos 3341) (Sat.Literal.pos 142) (Sat.Literal.pos 78) (positive_of_descriptor s 3342 (.lex permutation6 142) (by rfl)) (lex_6_142_prefix s) (positive_select s 142) (lex_6_142_image s)

theorem lex_6_142_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3341), (Sat.Literal.pos 142), (Sat.Literal.neg 78)] := by
  exact comparison_gate s permutation6 142 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3341) (Sat.Literal.pos 142) (Sat.Literal.pos 78) (lex_6_142_prefix s) (positive_select s 142) (lex_6_142_image s)

theorem lex_6_142_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3342), (Sat.Literal.pos 3341)] :=
  (lex_6_142_gate s).prop _ (List.Mem.head _)

theorem lex_6_142_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3342), (Sat.Literal.neg 142), (Sat.Literal.pos 78)] :=
  (lex_6_142_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_142_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3342), (Sat.Literal.pos 142), (Sat.Literal.neg 78)] :=
  (lex_6_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_142_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3341), (Sat.Literal.neg 142), (Sat.Literal.neg 78), (Sat.Literal.pos 3342)] :=
  (lex_6_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_142_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3341), (Sat.Literal.pos 142), (Sat.Literal.pos 78), (Sat.Literal.pos 3342)] :=
  (lex_6_142_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_141_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3342) = lexBefore s permutation6 141 := by
  exact (positive_lex_of_descriptor s 3342 permutation6 142 (by rfl)).trans ((lex_skipped s permutation6 141 142 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 142 142 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_141_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 77) = s (permuteMask permutation6 141) := by
  exact (positive_select s 77).trans (congrArg s (show (77 : Fin 256) = permuteMask permutation6 141 by rw [image6_eq]; rfl))

theorem lex_6_141_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3343) (Sat.Literal.pos 3342) (Sat.Literal.pos 141) (Sat.Literal.pos 77)) := by
  exact equality_gate s permutation6 141 (assignment s)
    (Sat.Literal.pos 3343) (Sat.Literal.pos 3342) (Sat.Literal.pos 141) (Sat.Literal.pos 77) (positive_of_descriptor s 3343 (.lex permutation6 141) (by rfl)) (lex_6_141_prefix s) (positive_select s 141) (lex_6_141_image s)

theorem lex_6_141_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3342), (Sat.Literal.pos 141), (Sat.Literal.neg 77)] := by
  exact comparison_gate s permutation6 141 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3342) (Sat.Literal.pos 141) (Sat.Literal.pos 77) (lex_6_141_prefix s) (positive_select s 141) (lex_6_141_image s)

theorem lex_6_141_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3343), (Sat.Literal.pos 3342)] :=
  (lex_6_141_gate s).prop _ (List.Mem.head _)

theorem lex_6_141_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3343), (Sat.Literal.neg 141), (Sat.Literal.pos 77)] :=
  (lex_6_141_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_141_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3343), (Sat.Literal.pos 141), (Sat.Literal.neg 77)] :=
  (lex_6_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_141_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3342), (Sat.Literal.neg 141), (Sat.Literal.neg 77), (Sat.Literal.pos 3343)] :=
  (lex_6_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_141_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3342), (Sat.Literal.pos 141), (Sat.Literal.pos 77), (Sat.Literal.pos 3343)] :=
  (lex_6_141_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_140_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3343) = lexBefore s permutation6 140 := by
  exact (positive_lex_of_descriptor s 3343 permutation6 141 (by rfl)).trans ((lex_skipped s permutation6 140 141 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 141 141 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_140_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 76) = s (permuteMask permutation6 140) := by
  exact (positive_select s 76).trans (congrArg s (show (76 : Fin 256) = permuteMask permutation6 140 by rw [image6_eq]; rfl))

theorem lex_6_140_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3344) (Sat.Literal.pos 3343) (Sat.Literal.pos 140) (Sat.Literal.pos 76)) := by
  exact equality_gate s permutation6 140 (assignment s)
    (Sat.Literal.pos 3344) (Sat.Literal.pos 3343) (Sat.Literal.pos 140) (Sat.Literal.pos 76) (positive_of_descriptor s 3344 (.lex permutation6 140) (by rfl)) (lex_6_140_prefix s) (positive_select s 140) (lex_6_140_image s)

theorem lex_6_140_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3343), (Sat.Literal.pos 140), (Sat.Literal.neg 76)] := by
  exact comparison_gate s permutation6 140 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3343) (Sat.Literal.pos 140) (Sat.Literal.pos 76) (lex_6_140_prefix s) (positive_select s 140) (lex_6_140_image s)

theorem lex_6_140_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3344), (Sat.Literal.pos 3343)] :=
  (lex_6_140_gate s).prop _ (List.Mem.head _)

theorem lex_6_140_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3344), (Sat.Literal.neg 140), (Sat.Literal.pos 76)] :=
  (lex_6_140_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_140_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3344), (Sat.Literal.pos 140), (Sat.Literal.neg 76)] :=
  (lex_6_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_140_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3343), (Sat.Literal.neg 140), (Sat.Literal.neg 76), (Sat.Literal.pos 3344)] :=
  (lex_6_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_140_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3343), (Sat.Literal.pos 140), (Sat.Literal.pos 76), (Sat.Literal.pos 3344)] :=
  (lex_6_140_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_139_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3344) = lexBefore s permutation6 139 := by
  exact (positive_lex_of_descriptor s 3344 permutation6 140 (by rfl)).trans ((lex_skipped s permutation6 139 140 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 140 140 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_139_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 75) = s (permuteMask permutation6 139) := by
  exact (positive_select s 75).trans (congrArg s (show (75 : Fin 256) = permuteMask permutation6 139 by rw [image6_eq]; rfl))

theorem lex_6_139_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3345) (Sat.Literal.pos 3344) (Sat.Literal.pos 139) (Sat.Literal.pos 75)) := by
  exact equality_gate s permutation6 139 (assignment s)
    (Sat.Literal.pos 3345) (Sat.Literal.pos 3344) (Sat.Literal.pos 139) (Sat.Literal.pos 75) (positive_of_descriptor s 3345 (.lex permutation6 139) (by rfl)) (lex_6_139_prefix s) (positive_select s 139) (lex_6_139_image s)

theorem lex_6_139_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3344), (Sat.Literal.pos 139), (Sat.Literal.neg 75)] := by
  exact comparison_gate s permutation6 139 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3344) (Sat.Literal.pos 139) (Sat.Literal.pos 75) (lex_6_139_prefix s) (positive_select s 139) (lex_6_139_image s)

theorem lex_6_139_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3345), (Sat.Literal.pos 3344)] :=
  (lex_6_139_gate s).prop _ (List.Mem.head _)

theorem lex_6_139_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3345), (Sat.Literal.neg 139), (Sat.Literal.pos 75)] :=
  (lex_6_139_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_139_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3345), (Sat.Literal.pos 139), (Sat.Literal.neg 75)] :=
  (lex_6_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_139_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3344), (Sat.Literal.neg 139), (Sat.Literal.neg 75), (Sat.Literal.pos 3345)] :=
  (lex_6_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_139_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3344), (Sat.Literal.pos 139), (Sat.Literal.pos 75), (Sat.Literal.pos 3345)] :=
  (lex_6_139_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_138_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3345) = lexBefore s permutation6 138 := by
  exact (positive_lex_of_descriptor s 3345 permutation6 139 (by rfl)).trans ((lex_skipped s permutation6 138 139 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 139 139 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_138_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 74) = s (permuteMask permutation6 138) := by
  exact (positive_select s 74).trans (congrArg s (show (74 : Fin 256) = permuteMask permutation6 138 by rw [image6_eq]; rfl))

theorem lex_6_138_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3346) (Sat.Literal.pos 3345) (Sat.Literal.pos 138) (Sat.Literal.pos 74)) := by
  exact equality_gate s permutation6 138 (assignment s)
    (Sat.Literal.pos 3346) (Sat.Literal.pos 3345) (Sat.Literal.pos 138) (Sat.Literal.pos 74) (positive_of_descriptor s 3346 (.lex permutation6 138) (by rfl)) (lex_6_138_prefix s) (positive_select s 138) (lex_6_138_image s)

theorem lex_6_138_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3345), (Sat.Literal.pos 138), (Sat.Literal.neg 74)] := by
  exact comparison_gate s permutation6 138 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3345) (Sat.Literal.pos 138) (Sat.Literal.pos 74) (lex_6_138_prefix s) (positive_select s 138) (lex_6_138_image s)

theorem lex_6_138_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3346), (Sat.Literal.pos 3345)] :=
  (lex_6_138_gate s).prop _ (List.Mem.head _)

theorem lex_6_138_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3346), (Sat.Literal.neg 138), (Sat.Literal.pos 74)] :=
  (lex_6_138_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_138_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3346), (Sat.Literal.pos 138), (Sat.Literal.neg 74)] :=
  (lex_6_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_138_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3345), (Sat.Literal.neg 138), (Sat.Literal.neg 74), (Sat.Literal.pos 3346)] :=
  (lex_6_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_138_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3345), (Sat.Literal.pos 138), (Sat.Literal.pos 74), (Sat.Literal.pos 3346)] :=
  (lex_6_138_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_137_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3346) = lexBefore s permutation6 137 := by
  exact (positive_lex_of_descriptor s 3346 permutation6 138 (by rfl)).trans ((lex_skipped s permutation6 137 138 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 138 138 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_137_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 73) = s (permuteMask permutation6 137) := by
  exact (positive_select s 73).trans (congrArg s (show (73 : Fin 256) = permuteMask permutation6 137 by rw [image6_eq]; rfl))

theorem lex_6_137_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3347) (Sat.Literal.pos 3346) (Sat.Literal.pos 137) (Sat.Literal.pos 73)) := by
  exact equality_gate s permutation6 137 (assignment s)
    (Sat.Literal.pos 3347) (Sat.Literal.pos 3346) (Sat.Literal.pos 137) (Sat.Literal.pos 73) (positive_of_descriptor s 3347 (.lex permutation6 137) (by rfl)) (lex_6_137_prefix s) (positive_select s 137) (lex_6_137_image s)

theorem lex_6_137_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3346), (Sat.Literal.pos 137), (Sat.Literal.neg 73)] := by
  exact comparison_gate s permutation6 137 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3346) (Sat.Literal.pos 137) (Sat.Literal.pos 73) (lex_6_137_prefix s) (positive_select s 137) (lex_6_137_image s)

theorem lex_6_137_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3347), (Sat.Literal.pos 3346)] :=
  (lex_6_137_gate s).prop _ (List.Mem.head _)

theorem lex_6_137_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3347), (Sat.Literal.neg 137), (Sat.Literal.pos 73)] :=
  (lex_6_137_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_137_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3347), (Sat.Literal.pos 137), (Sat.Literal.neg 73)] :=
  (lex_6_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_137_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3346), (Sat.Literal.neg 137), (Sat.Literal.neg 73), (Sat.Literal.pos 3347)] :=
  (lex_6_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_137_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3346), (Sat.Literal.pos 137), (Sat.Literal.pos 73), (Sat.Literal.pos 3347)] :=
  (lex_6_137_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_136_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3347) = lexBefore s permutation6 136 := by
  exact (positive_lex_of_descriptor s 3347 permutation6 137 (by rfl)).trans ((lex_skipped s permutation6 136 137 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 137 137 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_136_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 72) = s (permuteMask permutation6 136) := by
  exact (positive_select s 72).trans (congrArg s (show (72 : Fin 256) = permuteMask permutation6 136 by rw [image6_eq]; rfl))

theorem lex_6_136_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3348) (Sat.Literal.pos 3347) (Sat.Literal.pos 136) (Sat.Literal.pos 72)) := by
  exact equality_gate s permutation6 136 (assignment s)
    (Sat.Literal.pos 3348) (Sat.Literal.pos 3347) (Sat.Literal.pos 136) (Sat.Literal.pos 72) (positive_of_descriptor s 3348 (.lex permutation6 136) (by rfl)) (lex_6_136_prefix s) (positive_select s 136) (lex_6_136_image s)

theorem lex_6_136_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3347), (Sat.Literal.pos 136), (Sat.Literal.neg 72)] := by
  exact comparison_gate s permutation6 136 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3347) (Sat.Literal.pos 136) (Sat.Literal.pos 72) (lex_6_136_prefix s) (positive_select s 136) (lex_6_136_image s)

theorem lex_6_136_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3348), (Sat.Literal.pos 3347)] :=
  (lex_6_136_gate s).prop _ (List.Mem.head _)

theorem lex_6_136_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3348), (Sat.Literal.neg 136), (Sat.Literal.pos 72)] :=
  (lex_6_136_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_136_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3348), (Sat.Literal.pos 136), (Sat.Literal.neg 72)] :=
  (lex_6_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_136_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3347), (Sat.Literal.neg 136), (Sat.Literal.neg 72), (Sat.Literal.pos 3348)] :=
  (lex_6_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_136_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3347), (Sat.Literal.pos 136), (Sat.Literal.pos 72), (Sat.Literal.pos 3348)] :=
  (lex_6_136_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_135_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3348) = lexBefore s permutation6 135 := by
  exact (positive_lex_of_descriptor s 3348 permutation6 136 (by rfl)).trans ((lex_skipped s permutation6 135 136 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 136 136 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_135_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 71) = s (permuteMask permutation6 135) := by
  exact (positive_select s 71).trans (congrArg s (show (71 : Fin 256) = permuteMask permutation6 135 by rw [image6_eq]; rfl))

theorem lex_6_135_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3349) (Sat.Literal.pos 3348) (Sat.Literal.pos 135) (Sat.Literal.pos 71)) := by
  exact equality_gate s permutation6 135 (assignment s)
    (Sat.Literal.pos 3349) (Sat.Literal.pos 3348) (Sat.Literal.pos 135) (Sat.Literal.pos 71) (positive_of_descriptor s 3349 (.lex permutation6 135) (by rfl)) (lex_6_135_prefix s) (positive_select s 135) (lex_6_135_image s)

theorem lex_6_135_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3348), (Sat.Literal.pos 135), (Sat.Literal.neg 71)] := by
  exact comparison_gate s permutation6 135 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3348) (Sat.Literal.pos 135) (Sat.Literal.pos 71) (lex_6_135_prefix s) (positive_select s 135) (lex_6_135_image s)

theorem lex_6_135_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3349), (Sat.Literal.pos 3348)] :=
  (lex_6_135_gate s).prop _ (List.Mem.head _)

theorem lex_6_135_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3349), (Sat.Literal.neg 135), (Sat.Literal.pos 71)] :=
  (lex_6_135_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_135_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3349), (Sat.Literal.pos 135), (Sat.Literal.neg 71)] :=
  (lex_6_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_135_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3348), (Sat.Literal.neg 135), (Sat.Literal.neg 71), (Sat.Literal.pos 3349)] :=
  (lex_6_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_135_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3348), (Sat.Literal.pos 135), (Sat.Literal.pos 71), (Sat.Literal.pos 3349)] :=
  (lex_6_135_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_134_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3349) = lexBefore s permutation6 134 := by
  exact (positive_lex_of_descriptor s 3349 permutation6 135 (by rfl)).trans ((lex_skipped s permutation6 134 135 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 135 135 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_134_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 70) = s (permuteMask permutation6 134) := by
  exact (positive_select s 70).trans (congrArg s (show (70 : Fin 256) = permuteMask permutation6 134 by rw [image6_eq]; rfl))

theorem lex_6_134_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3350) (Sat.Literal.pos 3349) (Sat.Literal.pos 134) (Sat.Literal.pos 70)) := by
  exact equality_gate s permutation6 134 (assignment s)
    (Sat.Literal.pos 3350) (Sat.Literal.pos 3349) (Sat.Literal.pos 134) (Sat.Literal.pos 70) (positive_of_descriptor s 3350 (.lex permutation6 134) (by rfl)) (lex_6_134_prefix s) (positive_select s 134) (lex_6_134_image s)

theorem lex_6_134_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3349), (Sat.Literal.pos 134), (Sat.Literal.neg 70)] := by
  exact comparison_gate s permutation6 134 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3349) (Sat.Literal.pos 134) (Sat.Literal.pos 70) (lex_6_134_prefix s) (positive_select s 134) (lex_6_134_image s)

theorem lex_6_134_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3350), (Sat.Literal.pos 3349)] :=
  (lex_6_134_gate s).prop _ (List.Mem.head _)

theorem lex_6_134_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3350), (Sat.Literal.neg 134), (Sat.Literal.pos 70)] :=
  (lex_6_134_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_134_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3350), (Sat.Literal.pos 134), (Sat.Literal.neg 70)] :=
  (lex_6_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_134_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3349), (Sat.Literal.neg 134), (Sat.Literal.neg 70), (Sat.Literal.pos 3350)] :=
  (lex_6_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_134_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3349), (Sat.Literal.pos 134), (Sat.Literal.pos 70), (Sat.Literal.pos 3350)] :=
  (lex_6_134_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_133_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3350) = lexBefore s permutation6 133 := by
  exact (positive_lex_of_descriptor s 3350 permutation6 134 (by rfl)).trans ((lex_skipped s permutation6 133 134 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 134 134 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_133_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 69) = s (permuteMask permutation6 133) := by
  exact (positive_select s 69).trans (congrArg s (show (69 : Fin 256) = permuteMask permutation6 133 by rw [image6_eq]; rfl))

theorem lex_6_133_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3351) (Sat.Literal.pos 3350) (Sat.Literal.pos 133) (Sat.Literal.pos 69)) := by
  exact equality_gate s permutation6 133 (assignment s)
    (Sat.Literal.pos 3351) (Sat.Literal.pos 3350) (Sat.Literal.pos 133) (Sat.Literal.pos 69) (positive_of_descriptor s 3351 (.lex permutation6 133) (by rfl)) (lex_6_133_prefix s) (positive_select s 133) (lex_6_133_image s)

theorem lex_6_133_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3350), (Sat.Literal.pos 133), (Sat.Literal.neg 69)] := by
  exact comparison_gate s permutation6 133 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3350) (Sat.Literal.pos 133) (Sat.Literal.pos 69) (lex_6_133_prefix s) (positive_select s 133) (lex_6_133_image s)

theorem lex_6_133_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3351), (Sat.Literal.pos 3350)] :=
  (lex_6_133_gate s).prop _ (List.Mem.head _)

theorem lex_6_133_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3351), (Sat.Literal.neg 133), (Sat.Literal.pos 69)] :=
  (lex_6_133_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_133_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3351), (Sat.Literal.pos 133), (Sat.Literal.neg 69)] :=
  (lex_6_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_133_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3350), (Sat.Literal.neg 133), (Sat.Literal.neg 69), (Sat.Literal.pos 3351)] :=
  (lex_6_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_133_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3350), (Sat.Literal.pos 133), (Sat.Literal.pos 69), (Sat.Literal.pos 3351)] :=
  (lex_6_133_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_132_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3351) = lexBefore s permutation6 132 := by
  exact (positive_lex_of_descriptor s 3351 permutation6 133 (by rfl)).trans ((lex_skipped s permutation6 132 133 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 133 133 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_132_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 68) = s (permuteMask permutation6 132) := by
  exact (positive_select s 68).trans (congrArg s (show (68 : Fin 256) = permuteMask permutation6 132 by rw [image6_eq]; rfl))

theorem lex_6_132_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3352) (Sat.Literal.pos 3351) (Sat.Literal.pos 132) (Sat.Literal.pos 68)) := by
  exact equality_gate s permutation6 132 (assignment s)
    (Sat.Literal.pos 3352) (Sat.Literal.pos 3351) (Sat.Literal.pos 132) (Sat.Literal.pos 68) (positive_of_descriptor s 3352 (.lex permutation6 132) (by rfl)) (lex_6_132_prefix s) (positive_select s 132) (lex_6_132_image s)

theorem lex_6_132_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3351), (Sat.Literal.pos 132), (Sat.Literal.neg 68)] := by
  exact comparison_gate s permutation6 132 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3351) (Sat.Literal.pos 132) (Sat.Literal.pos 68) (lex_6_132_prefix s) (positive_select s 132) (lex_6_132_image s)

theorem lex_6_132_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3352), (Sat.Literal.pos 3351)] :=
  (lex_6_132_gate s).prop _ (List.Mem.head _)

theorem lex_6_132_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3352), (Sat.Literal.neg 132), (Sat.Literal.pos 68)] :=
  (lex_6_132_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_132_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3352), (Sat.Literal.pos 132), (Sat.Literal.neg 68)] :=
  (lex_6_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_132_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3351), (Sat.Literal.neg 132), (Sat.Literal.neg 68), (Sat.Literal.pos 3352)] :=
  (lex_6_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_132_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3351), (Sat.Literal.pos 132), (Sat.Literal.pos 68), (Sat.Literal.pos 3352)] :=
  (lex_6_132_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_131_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3352) = lexBefore s permutation6 131 := by
  exact (positive_lex_of_descriptor s 3352 permutation6 132 (by rfl)).trans ((lex_skipped s permutation6 131 132 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 132 132 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_131_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 67) = s (permuteMask permutation6 131) := by
  exact (positive_select s 67).trans (congrArg s (show (67 : Fin 256) = permuteMask permutation6 131 by rw [image6_eq]; rfl))

theorem lex_6_131_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3353) (Sat.Literal.pos 3352) (Sat.Literal.pos 131) (Sat.Literal.pos 67)) := by
  exact equality_gate s permutation6 131 (assignment s)
    (Sat.Literal.pos 3353) (Sat.Literal.pos 3352) (Sat.Literal.pos 131) (Sat.Literal.pos 67) (positive_of_descriptor s 3353 (.lex permutation6 131) (by rfl)) (lex_6_131_prefix s) (positive_select s 131) (lex_6_131_image s)

theorem lex_6_131_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3352), (Sat.Literal.pos 131), (Sat.Literal.neg 67)] := by
  exact comparison_gate s permutation6 131 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3352) (Sat.Literal.pos 131) (Sat.Literal.pos 67) (lex_6_131_prefix s) (positive_select s 131) (lex_6_131_image s)

theorem lex_6_131_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3353), (Sat.Literal.pos 3352)] :=
  (lex_6_131_gate s).prop _ (List.Mem.head _)

theorem lex_6_131_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3353), (Sat.Literal.neg 131), (Sat.Literal.pos 67)] :=
  (lex_6_131_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_131_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3353), (Sat.Literal.pos 131), (Sat.Literal.neg 67)] :=
  (lex_6_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_131_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3352), (Sat.Literal.neg 131), (Sat.Literal.neg 67), (Sat.Literal.pos 3353)] :=
  (lex_6_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_131_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3352), (Sat.Literal.pos 131), (Sat.Literal.pos 67), (Sat.Literal.pos 3353)] :=
  (lex_6_131_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_130_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3353) = lexBefore s permutation6 130 := by
  exact (positive_lex_of_descriptor s 3353 permutation6 131 (by rfl)).trans ((lex_skipped s permutation6 130 131 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 131 131 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_130_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 66) = s (permuteMask permutation6 130) := by
  exact (positive_select s 66).trans (congrArg s (show (66 : Fin 256) = permuteMask permutation6 130 by rw [image6_eq]; rfl))

theorem lex_6_130_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3354) (Sat.Literal.pos 3353) (Sat.Literal.pos 130) (Sat.Literal.pos 66)) := by
  exact equality_gate s permutation6 130 (assignment s)
    (Sat.Literal.pos 3354) (Sat.Literal.pos 3353) (Sat.Literal.pos 130) (Sat.Literal.pos 66) (positive_of_descriptor s 3354 (.lex permutation6 130) (by rfl)) (lex_6_130_prefix s) (positive_select s 130) (lex_6_130_image s)

theorem lex_6_130_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3353), (Sat.Literal.pos 130), (Sat.Literal.neg 66)] := by
  exact comparison_gate s permutation6 130 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3353) (Sat.Literal.pos 130) (Sat.Literal.pos 66) (lex_6_130_prefix s) (positive_select s 130) (lex_6_130_image s)

theorem lex_6_130_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3354), (Sat.Literal.pos 3353)] :=
  (lex_6_130_gate s).prop _ (List.Mem.head _)

theorem lex_6_130_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3354), (Sat.Literal.neg 130), (Sat.Literal.pos 66)] :=
  (lex_6_130_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_130_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3354), (Sat.Literal.pos 130), (Sat.Literal.neg 66)] :=
  (lex_6_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_130_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3353), (Sat.Literal.neg 130), (Sat.Literal.neg 66), (Sat.Literal.pos 3354)] :=
  (lex_6_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_130_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3353), (Sat.Literal.pos 130), (Sat.Literal.pos 66), (Sat.Literal.pos 3354)] :=
  (lex_6_130_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_129_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3354) = lexBefore s permutation6 129 := by
  exact (positive_lex_of_descriptor s 3354 permutation6 130 (by rfl)).trans ((lex_skipped s permutation6 129 130 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 130 130 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_129_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 65) = s (permuteMask permutation6 129) := by
  exact (positive_select s 65).trans (congrArg s (show (65 : Fin 256) = permuteMask permutation6 129 by rw [image6_eq]; rfl))

theorem lex_6_129_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3355) (Sat.Literal.pos 3354) (Sat.Literal.pos 129) (Sat.Literal.pos 65)) := by
  exact equality_gate s permutation6 129 (assignment s)
    (Sat.Literal.pos 3355) (Sat.Literal.pos 3354) (Sat.Literal.pos 129) (Sat.Literal.pos 65) (positive_of_descriptor s 3355 (.lex permutation6 129) (by rfl)) (lex_6_129_prefix s) (positive_select s 129) (lex_6_129_image s)

theorem lex_6_129_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3354), (Sat.Literal.pos 129), (Sat.Literal.neg 65)] := by
  exact comparison_gate s permutation6 129 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3354) (Sat.Literal.pos 129) (Sat.Literal.pos 65) (lex_6_129_prefix s) (positive_select s 129) (lex_6_129_image s)

theorem lex_6_129_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3355), (Sat.Literal.pos 3354)] :=
  (lex_6_129_gate s).prop _ (List.Mem.head _)

theorem lex_6_129_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3355), (Sat.Literal.neg 129), (Sat.Literal.pos 65)] :=
  (lex_6_129_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_129_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3355), (Sat.Literal.pos 129), (Sat.Literal.neg 65)] :=
  (lex_6_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_129_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3354), (Sat.Literal.neg 129), (Sat.Literal.neg 65), (Sat.Literal.pos 3355)] :=
  (lex_6_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_129_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3354), (Sat.Literal.pos 129), (Sat.Literal.pos 65), (Sat.Literal.pos 3355)] :=
  (lex_6_129_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_128_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3355) = lexBefore s permutation6 128 := by
  exact (positive_lex_of_descriptor s 3355 permutation6 129 (by rfl)).trans ((lex_skipped s permutation6 128 129 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 129 129 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_128_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 64) = s (permuteMask permutation6 128) := by
  exact (positive_select s 64).trans (congrArg s (show (64 : Fin 256) = permuteMask permutation6 128 by rw [image6_eq]; rfl))

theorem lex_6_128_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3356) (Sat.Literal.pos 3355) (Sat.Literal.pos 128) (Sat.Literal.pos 64)) := by
  exact equality_gate s permutation6 128 (assignment s)
    (Sat.Literal.pos 3356) (Sat.Literal.pos 3355) (Sat.Literal.pos 128) (Sat.Literal.pos 64) (positive_of_descriptor s 3356 (.lex permutation6 128) (by rfl)) (lex_6_128_prefix s) (positive_select s 128) (lex_6_128_image s)

theorem lex_6_128_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3355), (Sat.Literal.pos 128), (Sat.Literal.neg 64)] := by
  exact comparison_gate s permutation6 128 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3355) (Sat.Literal.pos 128) (Sat.Literal.pos 64) (lex_6_128_prefix s) (positive_select s 128) (lex_6_128_image s)

theorem lex_6_128_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3356), (Sat.Literal.pos 3355)] :=
  (lex_6_128_gate s).prop _ (List.Mem.head _)

theorem lex_6_128_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3356), (Sat.Literal.neg 128), (Sat.Literal.pos 64)] :=
  (lex_6_128_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_128_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3356), (Sat.Literal.pos 128), (Sat.Literal.neg 64)] :=
  (lex_6_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_128_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3355), (Sat.Literal.neg 128), (Sat.Literal.neg 64), (Sat.Literal.pos 3356)] :=
  (lex_6_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_128_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3355), (Sat.Literal.pos 128), (Sat.Literal.pos 64), (Sat.Literal.pos 3356)] :=
  (lex_6_128_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_127_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3356) = lexBefore s permutation6 127 := by
  exact (positive_lex_of_descriptor s 3356 permutation6 128 (by rfl)).trans ((lex_skipped s permutation6 127 128 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 128 128 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_127_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 191) = s (permuteMask permutation6 127) := by
  exact (positive_select s 191).trans (congrArg s (show (191 : Fin 256) = permuteMask permutation6 127 by rw [image6_eq]; rfl))

theorem lex_6_127_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3357) (Sat.Literal.pos 3356) (Sat.Literal.pos 127) (Sat.Literal.pos 191)) := by
  exact equality_gate s permutation6 127 (assignment s)
    (Sat.Literal.pos 3357) (Sat.Literal.pos 3356) (Sat.Literal.pos 127) (Sat.Literal.pos 191) (positive_of_descriptor s 3357 (.lex permutation6 127) (by rfl)) (lex_6_127_prefix s) (positive_select s 127) (lex_6_127_image s)

theorem lex_6_127_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3356), (Sat.Literal.pos 127), (Sat.Literal.neg 191)] := by
  exact comparison_gate s permutation6 127 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3356) (Sat.Literal.pos 127) (Sat.Literal.pos 191) (lex_6_127_prefix s) (positive_select s 127) (lex_6_127_image s)

theorem lex_6_127_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3357), (Sat.Literal.pos 3356)] :=
  (lex_6_127_gate s).prop _ (List.Mem.head _)

theorem lex_6_127_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3357), (Sat.Literal.neg 127), (Sat.Literal.pos 191)] :=
  (lex_6_127_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_127_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3357), (Sat.Literal.pos 127), (Sat.Literal.neg 191)] :=
  (lex_6_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_127_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3356), (Sat.Literal.neg 127), (Sat.Literal.neg 191), (Sat.Literal.pos 3357)] :=
  (lex_6_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_127_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3356), (Sat.Literal.pos 127), (Sat.Literal.pos 191), (Sat.Literal.pos 3357)] :=
  (lex_6_127_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_126_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3357) = lexBefore s permutation6 126 := by
  exact (positive_lex_of_descriptor s 3357 permutation6 127 (by rfl)).trans ((lex_skipped s permutation6 126 127 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 127 127 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_126_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 190) = s (permuteMask permutation6 126) := by
  exact (positive_select s 190).trans (congrArg s (show (190 : Fin 256) = permuteMask permutation6 126 by rw [image6_eq]; rfl))

theorem lex_6_126_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3358) (Sat.Literal.pos 3357) (Sat.Literal.pos 126) (Sat.Literal.pos 190)) := by
  exact equality_gate s permutation6 126 (assignment s)
    (Sat.Literal.pos 3358) (Sat.Literal.pos 3357) (Sat.Literal.pos 126) (Sat.Literal.pos 190) (positive_of_descriptor s 3358 (.lex permutation6 126) (by rfl)) (lex_6_126_prefix s) (positive_select s 126) (lex_6_126_image s)

theorem lex_6_126_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3357), (Sat.Literal.pos 126), (Sat.Literal.neg 190)] := by
  exact comparison_gate s permutation6 126 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3357) (Sat.Literal.pos 126) (Sat.Literal.pos 190) (lex_6_126_prefix s) (positive_select s 126) (lex_6_126_image s)

theorem lex_6_126_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3358), (Sat.Literal.pos 3357)] :=
  (lex_6_126_gate s).prop _ (List.Mem.head _)

theorem lex_6_126_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3358), (Sat.Literal.neg 126), (Sat.Literal.pos 190)] :=
  (lex_6_126_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_126_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3358), (Sat.Literal.pos 126), (Sat.Literal.neg 190)] :=
  (lex_6_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_126_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3357), (Sat.Literal.neg 126), (Sat.Literal.neg 190), (Sat.Literal.pos 3358)] :=
  (lex_6_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_126_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3357), (Sat.Literal.pos 126), (Sat.Literal.pos 190), (Sat.Literal.pos 3358)] :=
  (lex_6_126_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_125_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3358) = lexBefore s permutation6 125 := by
  exact (positive_lex_of_descriptor s 3358 permutation6 126 (by rfl)).trans ((lex_skipped s permutation6 125 126 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 126 126 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_125_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 189) = s (permuteMask permutation6 125) := by
  exact (positive_select s 189).trans (congrArg s (show (189 : Fin 256) = permuteMask permutation6 125 by rw [image6_eq]; rfl))

theorem lex_6_125_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3359) (Sat.Literal.pos 3358) (Sat.Literal.pos 125) (Sat.Literal.pos 189)) := by
  exact equality_gate s permutation6 125 (assignment s)
    (Sat.Literal.pos 3359) (Sat.Literal.pos 3358) (Sat.Literal.pos 125) (Sat.Literal.pos 189) (positive_of_descriptor s 3359 (.lex permutation6 125) (by rfl)) (lex_6_125_prefix s) (positive_select s 125) (lex_6_125_image s)

theorem lex_6_125_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3358), (Sat.Literal.pos 125), (Sat.Literal.neg 189)] := by
  exact comparison_gate s permutation6 125 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3358) (Sat.Literal.pos 125) (Sat.Literal.pos 189) (lex_6_125_prefix s) (positive_select s 125) (lex_6_125_image s)

theorem lex_6_125_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3359), (Sat.Literal.pos 3358)] :=
  (lex_6_125_gate s).prop _ (List.Mem.head _)

theorem lex_6_125_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3359), (Sat.Literal.neg 125), (Sat.Literal.pos 189)] :=
  (lex_6_125_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_125_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3359), (Sat.Literal.pos 125), (Sat.Literal.neg 189)] :=
  (lex_6_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_125_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3358), (Sat.Literal.neg 125), (Sat.Literal.neg 189), (Sat.Literal.pos 3359)] :=
  (lex_6_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_125_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3358), (Sat.Literal.pos 125), (Sat.Literal.pos 189), (Sat.Literal.pos 3359)] :=
  (lex_6_125_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_124_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3359) = lexBefore s permutation6 124 := by
  exact (positive_lex_of_descriptor s 3359 permutation6 125 (by rfl)).trans ((lex_skipped s permutation6 124 125 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 125 125 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_124_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 188) = s (permuteMask permutation6 124) := by
  exact (positive_select s 188).trans (congrArg s (show (188 : Fin 256) = permuteMask permutation6 124 by rw [image6_eq]; rfl))

theorem lex_6_124_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3360) (Sat.Literal.pos 3359) (Sat.Literal.pos 124) (Sat.Literal.pos 188)) := by
  exact equality_gate s permutation6 124 (assignment s)
    (Sat.Literal.pos 3360) (Sat.Literal.pos 3359) (Sat.Literal.pos 124) (Sat.Literal.pos 188) (positive_of_descriptor s 3360 (.lex permutation6 124) (by rfl)) (lex_6_124_prefix s) (positive_select s 124) (lex_6_124_image s)

theorem lex_6_124_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3359), (Sat.Literal.pos 124), (Sat.Literal.neg 188)] := by
  exact comparison_gate s permutation6 124 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3359) (Sat.Literal.pos 124) (Sat.Literal.pos 188) (lex_6_124_prefix s) (positive_select s 124) (lex_6_124_image s)

theorem lex_6_124_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3360), (Sat.Literal.pos 3359)] :=
  (lex_6_124_gate s).prop _ (List.Mem.head _)

theorem lex_6_124_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3360), (Sat.Literal.neg 124), (Sat.Literal.pos 188)] :=
  (lex_6_124_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_124_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3360), (Sat.Literal.pos 124), (Sat.Literal.neg 188)] :=
  (lex_6_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_124_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3359), (Sat.Literal.neg 124), (Sat.Literal.neg 188), (Sat.Literal.pos 3360)] :=
  (lex_6_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_124_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3359), (Sat.Literal.pos 124), (Sat.Literal.pos 188), (Sat.Literal.pos 3360)] :=
  (lex_6_124_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_123_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3360) = lexBefore s permutation6 123 := by
  exact (positive_lex_of_descriptor s 3360 permutation6 124 (by rfl)).trans ((lex_skipped s permutation6 123 124 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 124 124 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_123_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 187) = s (permuteMask permutation6 123) := by
  exact (positive_select s 187).trans (congrArg s (show (187 : Fin 256) = permuteMask permutation6 123 by rw [image6_eq]; rfl))

theorem lex_6_123_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3361) (Sat.Literal.pos 3360) (Sat.Literal.pos 123) (Sat.Literal.pos 187)) := by
  exact equality_gate s permutation6 123 (assignment s)
    (Sat.Literal.pos 3361) (Sat.Literal.pos 3360) (Sat.Literal.pos 123) (Sat.Literal.pos 187) (positive_of_descriptor s 3361 (.lex permutation6 123) (by rfl)) (lex_6_123_prefix s) (positive_select s 123) (lex_6_123_image s)

theorem lex_6_123_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3360), (Sat.Literal.pos 123), (Sat.Literal.neg 187)] := by
  exact comparison_gate s permutation6 123 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3360) (Sat.Literal.pos 123) (Sat.Literal.pos 187) (lex_6_123_prefix s) (positive_select s 123) (lex_6_123_image s)

theorem lex_6_123_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3361), (Sat.Literal.pos 3360)] :=
  (lex_6_123_gate s).prop _ (List.Mem.head _)

theorem lex_6_123_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3361), (Sat.Literal.neg 123), (Sat.Literal.pos 187)] :=
  (lex_6_123_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_123_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3361), (Sat.Literal.pos 123), (Sat.Literal.neg 187)] :=
  (lex_6_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_123_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3360), (Sat.Literal.neg 123), (Sat.Literal.neg 187), (Sat.Literal.pos 3361)] :=
  (lex_6_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_123_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3360), (Sat.Literal.pos 123), (Sat.Literal.pos 187), (Sat.Literal.pos 3361)] :=
  (lex_6_123_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_122_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3361) = lexBefore s permutation6 122 := by
  exact (positive_lex_of_descriptor s 3361 permutation6 123 (by rfl)).trans ((lex_skipped s permutation6 122 123 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 123 123 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_122_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 186) = s (permuteMask permutation6 122) := by
  exact (positive_select s 186).trans (congrArg s (show (186 : Fin 256) = permuteMask permutation6 122 by rw [image6_eq]; rfl))

theorem lex_6_122_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3362) (Sat.Literal.pos 3361) (Sat.Literal.pos 122) (Sat.Literal.pos 186)) := by
  exact equality_gate s permutation6 122 (assignment s)
    (Sat.Literal.pos 3362) (Sat.Literal.pos 3361) (Sat.Literal.pos 122) (Sat.Literal.pos 186) (positive_of_descriptor s 3362 (.lex permutation6 122) (by rfl)) (lex_6_122_prefix s) (positive_select s 122) (lex_6_122_image s)

theorem lex_6_122_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3361), (Sat.Literal.pos 122), (Sat.Literal.neg 186)] := by
  exact comparison_gate s permutation6 122 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3361) (Sat.Literal.pos 122) (Sat.Literal.pos 186) (lex_6_122_prefix s) (positive_select s 122) (lex_6_122_image s)

theorem lex_6_122_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3362), (Sat.Literal.pos 3361)] :=
  (lex_6_122_gate s).prop _ (List.Mem.head _)

theorem lex_6_122_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3362), (Sat.Literal.neg 122), (Sat.Literal.pos 186)] :=
  (lex_6_122_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_122_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3362), (Sat.Literal.pos 122), (Sat.Literal.neg 186)] :=
  (lex_6_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_122_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3361), (Sat.Literal.neg 122), (Sat.Literal.neg 186), (Sat.Literal.pos 3362)] :=
  (lex_6_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_122_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3361), (Sat.Literal.pos 122), (Sat.Literal.pos 186), (Sat.Literal.pos 3362)] :=
  (lex_6_122_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_121_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3362) = lexBefore s permutation6 121 := by
  exact (positive_lex_of_descriptor s 3362 permutation6 122 (by rfl)).trans ((lex_skipped s permutation6 121 122 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 122 122 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_121_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 185) = s (permuteMask permutation6 121) := by
  exact (positive_select s 185).trans (congrArg s (show (185 : Fin 256) = permuteMask permutation6 121 by rw [image6_eq]; rfl))

theorem lex_6_121_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3363) (Sat.Literal.pos 3362) (Sat.Literal.pos 121) (Sat.Literal.pos 185)) := by
  exact equality_gate s permutation6 121 (assignment s)
    (Sat.Literal.pos 3363) (Sat.Literal.pos 3362) (Sat.Literal.pos 121) (Sat.Literal.pos 185) (positive_of_descriptor s 3363 (.lex permutation6 121) (by rfl)) (lex_6_121_prefix s) (positive_select s 121) (lex_6_121_image s)

theorem lex_6_121_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3362), (Sat.Literal.pos 121), (Sat.Literal.neg 185)] := by
  exact comparison_gate s permutation6 121 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3362) (Sat.Literal.pos 121) (Sat.Literal.pos 185) (lex_6_121_prefix s) (positive_select s 121) (lex_6_121_image s)

theorem lex_6_121_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3363), (Sat.Literal.pos 3362)] :=
  (lex_6_121_gate s).prop _ (List.Mem.head _)

theorem lex_6_121_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3363), (Sat.Literal.neg 121), (Sat.Literal.pos 185)] :=
  (lex_6_121_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_121_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3363), (Sat.Literal.pos 121), (Sat.Literal.neg 185)] :=
  (lex_6_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_121_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3362), (Sat.Literal.neg 121), (Sat.Literal.neg 185), (Sat.Literal.pos 3363)] :=
  (lex_6_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_121_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3362), (Sat.Literal.pos 121), (Sat.Literal.pos 185), (Sat.Literal.pos 3363)] :=
  (lex_6_121_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_120_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3363) = lexBefore s permutation6 120 := by
  exact (positive_lex_of_descriptor s 3363 permutation6 121 (by rfl)).trans ((lex_skipped s permutation6 120 121 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 121 121 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_120_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 184) = s (permuteMask permutation6 120) := by
  exact (positive_select s 184).trans (congrArg s (show (184 : Fin 256) = permuteMask permutation6 120 by rw [image6_eq]; rfl))

theorem lex_6_120_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3364) (Sat.Literal.pos 3363) (Sat.Literal.pos 120) (Sat.Literal.pos 184)) := by
  exact equality_gate s permutation6 120 (assignment s)
    (Sat.Literal.pos 3364) (Sat.Literal.pos 3363) (Sat.Literal.pos 120) (Sat.Literal.pos 184) (positive_of_descriptor s 3364 (.lex permutation6 120) (by rfl)) (lex_6_120_prefix s) (positive_select s 120) (lex_6_120_image s)

theorem lex_6_120_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3363), (Sat.Literal.pos 120), (Sat.Literal.neg 184)] := by
  exact comparison_gate s permutation6 120 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3363) (Sat.Literal.pos 120) (Sat.Literal.pos 184) (lex_6_120_prefix s) (positive_select s 120) (lex_6_120_image s)

theorem lex_6_120_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3364), (Sat.Literal.pos 3363)] :=
  (lex_6_120_gate s).prop _ (List.Mem.head _)

theorem lex_6_120_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3364), (Sat.Literal.neg 120), (Sat.Literal.pos 184)] :=
  (lex_6_120_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_120_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3364), (Sat.Literal.pos 120), (Sat.Literal.neg 184)] :=
  (lex_6_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_120_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3363), (Sat.Literal.neg 120), (Sat.Literal.neg 184), (Sat.Literal.pos 3364)] :=
  (lex_6_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_120_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3363), (Sat.Literal.pos 120), (Sat.Literal.pos 184), (Sat.Literal.pos 3364)] :=
  (lex_6_120_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_119_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3364) = lexBefore s permutation6 119 := by
  exact (positive_lex_of_descriptor s 3364 permutation6 120 (by rfl)).trans ((lex_skipped s permutation6 119 120 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 120 120 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_119_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 183) = s (permuteMask permutation6 119) := by
  exact (positive_select s 183).trans (congrArg s (show (183 : Fin 256) = permuteMask permutation6 119 by rw [image6_eq]; rfl))

theorem lex_6_119_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3365) (Sat.Literal.pos 3364) (Sat.Literal.pos 119) (Sat.Literal.pos 183)) := by
  exact equality_gate s permutation6 119 (assignment s)
    (Sat.Literal.pos 3365) (Sat.Literal.pos 3364) (Sat.Literal.pos 119) (Sat.Literal.pos 183) (positive_of_descriptor s 3365 (.lex permutation6 119) (by rfl)) (lex_6_119_prefix s) (positive_select s 119) (lex_6_119_image s)

theorem lex_6_119_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3364), (Sat.Literal.pos 119), (Sat.Literal.neg 183)] := by
  exact comparison_gate s permutation6 119 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3364) (Sat.Literal.pos 119) (Sat.Literal.pos 183) (lex_6_119_prefix s) (positive_select s 119) (lex_6_119_image s)

theorem lex_6_119_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3365), (Sat.Literal.pos 3364)] :=
  (lex_6_119_gate s).prop _ (List.Mem.head _)

theorem lex_6_119_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3365), (Sat.Literal.neg 119), (Sat.Literal.pos 183)] :=
  (lex_6_119_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_119_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3365), (Sat.Literal.pos 119), (Sat.Literal.neg 183)] :=
  (lex_6_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_119_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3364), (Sat.Literal.neg 119), (Sat.Literal.neg 183), (Sat.Literal.pos 3365)] :=
  (lex_6_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_119_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3364), (Sat.Literal.pos 119), (Sat.Literal.pos 183), (Sat.Literal.pos 3365)] :=
  (lex_6_119_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_118_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3365) = lexBefore s permutation6 118 := by
  exact (positive_lex_of_descriptor s 3365 permutation6 119 (by rfl)).trans ((lex_skipped s permutation6 118 119 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 119 119 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_118_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 182) = s (permuteMask permutation6 118) := by
  exact (positive_select s 182).trans (congrArg s (show (182 : Fin 256) = permuteMask permutation6 118 by rw [image6_eq]; rfl))

theorem lex_6_118_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3366) (Sat.Literal.pos 3365) (Sat.Literal.pos 118) (Sat.Literal.pos 182)) := by
  exact equality_gate s permutation6 118 (assignment s)
    (Sat.Literal.pos 3366) (Sat.Literal.pos 3365) (Sat.Literal.pos 118) (Sat.Literal.pos 182) (positive_of_descriptor s 3366 (.lex permutation6 118) (by rfl)) (lex_6_118_prefix s) (positive_select s 118) (lex_6_118_image s)

theorem lex_6_118_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3365), (Sat.Literal.pos 118), (Sat.Literal.neg 182)] := by
  exact comparison_gate s permutation6 118 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3365) (Sat.Literal.pos 118) (Sat.Literal.pos 182) (lex_6_118_prefix s) (positive_select s 118) (lex_6_118_image s)

theorem lex_6_118_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3366), (Sat.Literal.pos 3365)] :=
  (lex_6_118_gate s).prop _ (List.Mem.head _)

theorem lex_6_118_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3366), (Sat.Literal.neg 118), (Sat.Literal.pos 182)] :=
  (lex_6_118_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_118_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3366), (Sat.Literal.pos 118), (Sat.Literal.neg 182)] :=
  (lex_6_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_118_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3365), (Sat.Literal.neg 118), (Sat.Literal.neg 182), (Sat.Literal.pos 3366)] :=
  (lex_6_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_118_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3365), (Sat.Literal.pos 118), (Sat.Literal.pos 182), (Sat.Literal.pos 3366)] :=
  (lex_6_118_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_117_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3366) = lexBefore s permutation6 117 := by
  exact (positive_lex_of_descriptor s 3366 permutation6 118 (by rfl)).trans ((lex_skipped s permutation6 117 118 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 118 118 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_117_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 181) = s (permuteMask permutation6 117) := by
  exact (positive_select s 181).trans (congrArg s (show (181 : Fin 256) = permuteMask permutation6 117 by rw [image6_eq]; rfl))

theorem lex_6_117_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3367) (Sat.Literal.pos 3366) (Sat.Literal.pos 117) (Sat.Literal.pos 181)) := by
  exact equality_gate s permutation6 117 (assignment s)
    (Sat.Literal.pos 3367) (Sat.Literal.pos 3366) (Sat.Literal.pos 117) (Sat.Literal.pos 181) (positive_of_descriptor s 3367 (.lex permutation6 117) (by rfl)) (lex_6_117_prefix s) (positive_select s 117) (lex_6_117_image s)

theorem lex_6_117_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3366), (Sat.Literal.pos 117), (Sat.Literal.neg 181)] := by
  exact comparison_gate s permutation6 117 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3366) (Sat.Literal.pos 117) (Sat.Literal.pos 181) (lex_6_117_prefix s) (positive_select s 117) (lex_6_117_image s)

theorem lex_6_117_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3367), (Sat.Literal.pos 3366)] :=
  (lex_6_117_gate s).prop _ (List.Mem.head _)

theorem lex_6_117_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3367), (Sat.Literal.neg 117), (Sat.Literal.pos 181)] :=
  (lex_6_117_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_117_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3367), (Sat.Literal.pos 117), (Sat.Literal.neg 181)] :=
  (lex_6_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_117_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3366), (Sat.Literal.neg 117), (Sat.Literal.neg 181), (Sat.Literal.pos 3367)] :=
  (lex_6_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_117_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3366), (Sat.Literal.pos 117), (Sat.Literal.pos 181), (Sat.Literal.pos 3367)] :=
  (lex_6_117_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_116_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3367) = lexBefore s permutation6 116 := by
  exact (positive_lex_of_descriptor s 3367 permutation6 117 (by rfl)).trans ((lex_skipped s permutation6 116 117 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 117 117 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_116_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 180) = s (permuteMask permutation6 116) := by
  exact (positive_select s 180).trans (congrArg s (show (180 : Fin 256) = permuteMask permutation6 116 by rw [image6_eq]; rfl))

theorem lex_6_116_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3368) (Sat.Literal.pos 3367) (Sat.Literal.pos 116) (Sat.Literal.pos 180)) := by
  exact equality_gate s permutation6 116 (assignment s)
    (Sat.Literal.pos 3368) (Sat.Literal.pos 3367) (Sat.Literal.pos 116) (Sat.Literal.pos 180) (positive_of_descriptor s 3368 (.lex permutation6 116) (by rfl)) (lex_6_116_prefix s) (positive_select s 116) (lex_6_116_image s)

theorem lex_6_116_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3367), (Sat.Literal.pos 116), (Sat.Literal.neg 180)] := by
  exact comparison_gate s permutation6 116 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3367) (Sat.Literal.pos 116) (Sat.Literal.pos 180) (lex_6_116_prefix s) (positive_select s 116) (lex_6_116_image s)

theorem lex_6_116_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3368), (Sat.Literal.pos 3367)] :=
  (lex_6_116_gate s).prop _ (List.Mem.head _)

theorem lex_6_116_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3368), (Sat.Literal.neg 116), (Sat.Literal.pos 180)] :=
  (lex_6_116_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_116_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3368), (Sat.Literal.pos 116), (Sat.Literal.neg 180)] :=
  (lex_6_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_116_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3367), (Sat.Literal.neg 116), (Sat.Literal.neg 180), (Sat.Literal.pos 3368)] :=
  (lex_6_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_116_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3367), (Sat.Literal.pos 116), (Sat.Literal.pos 180), (Sat.Literal.pos 3368)] :=
  (lex_6_116_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_115_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3368) = lexBefore s permutation6 115 := by
  exact (positive_lex_of_descriptor s 3368 permutation6 116 (by rfl)).trans ((lex_skipped s permutation6 115 116 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 116 116 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_115_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 179) = s (permuteMask permutation6 115) := by
  exact (positive_select s 179).trans (congrArg s (show (179 : Fin 256) = permuteMask permutation6 115 by rw [image6_eq]; rfl))

theorem lex_6_115_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3369) (Sat.Literal.pos 3368) (Sat.Literal.pos 115) (Sat.Literal.pos 179)) := by
  exact equality_gate s permutation6 115 (assignment s)
    (Sat.Literal.pos 3369) (Sat.Literal.pos 3368) (Sat.Literal.pos 115) (Sat.Literal.pos 179) (positive_of_descriptor s 3369 (.lex permutation6 115) (by rfl)) (lex_6_115_prefix s) (positive_select s 115) (lex_6_115_image s)

theorem lex_6_115_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3368), (Sat.Literal.pos 115), (Sat.Literal.neg 179)] := by
  exact comparison_gate s permutation6 115 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3368) (Sat.Literal.pos 115) (Sat.Literal.pos 179) (lex_6_115_prefix s) (positive_select s 115) (lex_6_115_image s)

theorem lex_6_115_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3369), (Sat.Literal.pos 3368)] :=
  (lex_6_115_gate s).prop _ (List.Mem.head _)

theorem lex_6_115_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3369), (Sat.Literal.neg 115), (Sat.Literal.pos 179)] :=
  (lex_6_115_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_115_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3369), (Sat.Literal.pos 115), (Sat.Literal.neg 179)] :=
  (lex_6_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_115_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3368), (Sat.Literal.neg 115), (Sat.Literal.neg 179), (Sat.Literal.pos 3369)] :=
  (lex_6_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_115_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3368), (Sat.Literal.pos 115), (Sat.Literal.pos 179), (Sat.Literal.pos 3369)] :=
  (lex_6_115_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_114_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3369) = lexBefore s permutation6 114 := by
  exact (positive_lex_of_descriptor s 3369 permutation6 115 (by rfl)).trans ((lex_skipped s permutation6 114 115 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 115 115 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_114_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 178) = s (permuteMask permutation6 114) := by
  exact (positive_select s 178).trans (congrArg s (show (178 : Fin 256) = permuteMask permutation6 114 by rw [image6_eq]; rfl))

theorem lex_6_114_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3370) (Sat.Literal.pos 3369) (Sat.Literal.pos 114) (Sat.Literal.pos 178)) := by
  exact equality_gate s permutation6 114 (assignment s)
    (Sat.Literal.pos 3370) (Sat.Literal.pos 3369) (Sat.Literal.pos 114) (Sat.Literal.pos 178) (positive_of_descriptor s 3370 (.lex permutation6 114) (by rfl)) (lex_6_114_prefix s) (positive_select s 114) (lex_6_114_image s)

theorem lex_6_114_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3369), (Sat.Literal.pos 114), (Sat.Literal.neg 178)] := by
  exact comparison_gate s permutation6 114 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3369) (Sat.Literal.pos 114) (Sat.Literal.pos 178) (lex_6_114_prefix s) (positive_select s 114) (lex_6_114_image s)

theorem lex_6_114_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3370), (Sat.Literal.pos 3369)] :=
  (lex_6_114_gate s).prop _ (List.Mem.head _)

theorem lex_6_114_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3370), (Sat.Literal.neg 114), (Sat.Literal.pos 178)] :=
  (lex_6_114_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_114_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3370), (Sat.Literal.pos 114), (Sat.Literal.neg 178)] :=
  (lex_6_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_114_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3369), (Sat.Literal.neg 114), (Sat.Literal.neg 178), (Sat.Literal.pos 3370)] :=
  (lex_6_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_114_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3369), (Sat.Literal.pos 114), (Sat.Literal.pos 178), (Sat.Literal.pos 3370)] :=
  (lex_6_114_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_113_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3370) = lexBefore s permutation6 113 := by
  exact (positive_lex_of_descriptor s 3370 permutation6 114 (by rfl)).trans ((lex_skipped s permutation6 113 114 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 114 114 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_113_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 177) = s (permuteMask permutation6 113) := by
  exact (positive_select s 177).trans (congrArg s (show (177 : Fin 256) = permuteMask permutation6 113 by rw [image6_eq]; rfl))

theorem lex_6_113_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3371) (Sat.Literal.pos 3370) (Sat.Literal.pos 113) (Sat.Literal.pos 177)) := by
  exact equality_gate s permutation6 113 (assignment s)
    (Sat.Literal.pos 3371) (Sat.Literal.pos 3370) (Sat.Literal.pos 113) (Sat.Literal.pos 177) (positive_of_descriptor s 3371 (.lex permutation6 113) (by rfl)) (lex_6_113_prefix s) (positive_select s 113) (lex_6_113_image s)

theorem lex_6_113_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3370), (Sat.Literal.pos 113), (Sat.Literal.neg 177)] := by
  exact comparison_gate s permutation6 113 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3370) (Sat.Literal.pos 113) (Sat.Literal.pos 177) (lex_6_113_prefix s) (positive_select s 113) (lex_6_113_image s)

theorem lex_6_113_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3371), (Sat.Literal.pos 3370)] :=
  (lex_6_113_gate s).prop _ (List.Mem.head _)

theorem lex_6_113_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3371), (Sat.Literal.neg 113), (Sat.Literal.pos 177)] :=
  (lex_6_113_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_113_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3371), (Sat.Literal.pos 113), (Sat.Literal.neg 177)] :=
  (lex_6_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_113_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3370), (Sat.Literal.neg 113), (Sat.Literal.neg 177), (Sat.Literal.pos 3371)] :=
  (lex_6_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_113_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3370), (Sat.Literal.pos 113), (Sat.Literal.pos 177), (Sat.Literal.pos 3371)] :=
  (lex_6_113_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_112_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3371) = lexBefore s permutation6 112 := by
  exact (positive_lex_of_descriptor s 3371 permutation6 113 (by rfl)).trans ((lex_skipped s permutation6 112 113 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 113 113 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_112_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 176) = s (permuteMask permutation6 112) := by
  exact (positive_select s 176).trans (congrArg s (show (176 : Fin 256) = permuteMask permutation6 112 by rw [image6_eq]; rfl))

theorem lex_6_112_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3372) (Sat.Literal.pos 3371) (Sat.Literal.pos 112) (Sat.Literal.pos 176)) := by
  exact equality_gate s permutation6 112 (assignment s)
    (Sat.Literal.pos 3372) (Sat.Literal.pos 3371) (Sat.Literal.pos 112) (Sat.Literal.pos 176) (positive_of_descriptor s 3372 (.lex permutation6 112) (by rfl)) (lex_6_112_prefix s) (positive_select s 112) (lex_6_112_image s)

theorem lex_6_112_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3371), (Sat.Literal.pos 112), (Sat.Literal.neg 176)] := by
  exact comparison_gate s permutation6 112 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3371) (Sat.Literal.pos 112) (Sat.Literal.pos 176) (lex_6_112_prefix s) (positive_select s 112) (lex_6_112_image s)

theorem lex_6_112_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3372), (Sat.Literal.pos 3371)] :=
  (lex_6_112_gate s).prop _ (List.Mem.head _)

theorem lex_6_112_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3372), (Sat.Literal.neg 112), (Sat.Literal.pos 176)] :=
  (lex_6_112_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_112_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3372), (Sat.Literal.pos 112), (Sat.Literal.neg 176)] :=
  (lex_6_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_112_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3371), (Sat.Literal.neg 112), (Sat.Literal.neg 176), (Sat.Literal.pos 3372)] :=
  (lex_6_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_112_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3371), (Sat.Literal.pos 112), (Sat.Literal.pos 176), (Sat.Literal.pos 3372)] :=
  (lex_6_112_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_111_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3372) = lexBefore s permutation6 111 := by
  exact (positive_lex_of_descriptor s 3372 permutation6 112 (by rfl)).trans ((lex_skipped s permutation6 111 112 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 112 112 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_111_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 175) = s (permuteMask permutation6 111) := by
  exact (positive_select s 175).trans (congrArg s (show (175 : Fin 256) = permuteMask permutation6 111 by rw [image6_eq]; rfl))

theorem lex_6_111_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3373) (Sat.Literal.pos 3372) (Sat.Literal.pos 111) (Sat.Literal.pos 175)) := by
  exact equality_gate s permutation6 111 (assignment s)
    (Sat.Literal.pos 3373) (Sat.Literal.pos 3372) (Sat.Literal.pos 111) (Sat.Literal.pos 175) (positive_of_descriptor s 3373 (.lex permutation6 111) (by rfl)) (lex_6_111_prefix s) (positive_select s 111) (lex_6_111_image s)

theorem lex_6_111_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3372), (Sat.Literal.pos 111), (Sat.Literal.neg 175)] := by
  exact comparison_gate s permutation6 111 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3372) (Sat.Literal.pos 111) (Sat.Literal.pos 175) (lex_6_111_prefix s) (positive_select s 111) (lex_6_111_image s)

theorem lex_6_111_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3373), (Sat.Literal.pos 3372)] :=
  (lex_6_111_gate s).prop _ (List.Mem.head _)

theorem lex_6_111_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3373), (Sat.Literal.neg 111), (Sat.Literal.pos 175)] :=
  (lex_6_111_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_111_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3373), (Sat.Literal.pos 111), (Sat.Literal.neg 175)] :=
  (lex_6_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_111_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3372), (Sat.Literal.neg 111), (Sat.Literal.neg 175), (Sat.Literal.pos 3373)] :=
  (lex_6_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_111_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3372), (Sat.Literal.pos 111), (Sat.Literal.pos 175), (Sat.Literal.pos 3373)] :=
  (lex_6_111_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_110_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3373) = lexBefore s permutation6 110 := by
  exact (positive_lex_of_descriptor s 3373 permutation6 111 (by rfl)).trans ((lex_skipped s permutation6 110 111 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 111 111 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_110_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 174) = s (permuteMask permutation6 110) := by
  exact (positive_select s 174).trans (congrArg s (show (174 : Fin 256) = permuteMask permutation6 110 by rw [image6_eq]; rfl))

theorem lex_6_110_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3374) (Sat.Literal.pos 3373) (Sat.Literal.pos 110) (Sat.Literal.pos 174)) := by
  exact equality_gate s permutation6 110 (assignment s)
    (Sat.Literal.pos 3374) (Sat.Literal.pos 3373) (Sat.Literal.pos 110) (Sat.Literal.pos 174) (positive_of_descriptor s 3374 (.lex permutation6 110) (by rfl)) (lex_6_110_prefix s) (positive_select s 110) (lex_6_110_image s)

theorem lex_6_110_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3373), (Sat.Literal.pos 110), (Sat.Literal.neg 174)] := by
  exact comparison_gate s permutation6 110 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3373) (Sat.Literal.pos 110) (Sat.Literal.pos 174) (lex_6_110_prefix s) (positive_select s 110) (lex_6_110_image s)

theorem lex_6_110_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3374), (Sat.Literal.pos 3373)] :=
  (lex_6_110_gate s).prop _ (List.Mem.head _)

theorem lex_6_110_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3374), (Sat.Literal.neg 110), (Sat.Literal.pos 174)] :=
  (lex_6_110_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_110_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3374), (Sat.Literal.pos 110), (Sat.Literal.neg 174)] :=
  (lex_6_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_110_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3373), (Sat.Literal.neg 110), (Sat.Literal.neg 174), (Sat.Literal.pos 3374)] :=
  (lex_6_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_110_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3373), (Sat.Literal.pos 110), (Sat.Literal.pos 174), (Sat.Literal.pos 3374)] :=
  (lex_6_110_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_109_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3374) = lexBefore s permutation6 109 := by
  exact (positive_lex_of_descriptor s 3374 permutation6 110 (by rfl)).trans ((lex_skipped s permutation6 109 110 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 110 110 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_109_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 173) = s (permuteMask permutation6 109) := by
  exact (positive_select s 173).trans (congrArg s (show (173 : Fin 256) = permuteMask permutation6 109 by rw [image6_eq]; rfl))

theorem lex_6_109_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3375) (Sat.Literal.pos 3374) (Sat.Literal.pos 109) (Sat.Literal.pos 173)) := by
  exact equality_gate s permutation6 109 (assignment s)
    (Sat.Literal.pos 3375) (Sat.Literal.pos 3374) (Sat.Literal.pos 109) (Sat.Literal.pos 173) (positive_of_descriptor s 3375 (.lex permutation6 109) (by rfl)) (lex_6_109_prefix s) (positive_select s 109) (lex_6_109_image s)

theorem lex_6_109_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3374), (Sat.Literal.pos 109), (Sat.Literal.neg 173)] := by
  exact comparison_gate s permutation6 109 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3374) (Sat.Literal.pos 109) (Sat.Literal.pos 173) (lex_6_109_prefix s) (positive_select s 109) (lex_6_109_image s)

theorem lex_6_109_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3375), (Sat.Literal.pos 3374)] :=
  (lex_6_109_gate s).prop _ (List.Mem.head _)

theorem lex_6_109_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3375), (Sat.Literal.neg 109), (Sat.Literal.pos 173)] :=
  (lex_6_109_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_109_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3375), (Sat.Literal.pos 109), (Sat.Literal.neg 173)] :=
  (lex_6_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_109_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3374), (Sat.Literal.neg 109), (Sat.Literal.neg 173), (Sat.Literal.pos 3375)] :=
  (lex_6_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_109_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3374), (Sat.Literal.pos 109), (Sat.Literal.pos 173), (Sat.Literal.pos 3375)] :=
  (lex_6_109_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_108_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3375) = lexBefore s permutation6 108 := by
  exact (positive_lex_of_descriptor s 3375 permutation6 109 (by rfl)).trans ((lex_skipped s permutation6 108 109 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 109 109 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_108_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 172) = s (permuteMask permutation6 108) := by
  exact (positive_select s 172).trans (congrArg s (show (172 : Fin 256) = permuteMask permutation6 108 by rw [image6_eq]; rfl))

theorem lex_6_108_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3376) (Sat.Literal.pos 3375) (Sat.Literal.pos 108) (Sat.Literal.pos 172)) := by
  exact equality_gate s permutation6 108 (assignment s)
    (Sat.Literal.pos 3376) (Sat.Literal.pos 3375) (Sat.Literal.pos 108) (Sat.Literal.pos 172) (positive_of_descriptor s 3376 (.lex permutation6 108) (by rfl)) (lex_6_108_prefix s) (positive_select s 108) (lex_6_108_image s)

theorem lex_6_108_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3375), (Sat.Literal.pos 108), (Sat.Literal.neg 172)] := by
  exact comparison_gate s permutation6 108 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3375) (Sat.Literal.pos 108) (Sat.Literal.pos 172) (lex_6_108_prefix s) (positive_select s 108) (lex_6_108_image s)

theorem lex_6_108_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3376), (Sat.Literal.pos 3375)] :=
  (lex_6_108_gate s).prop _ (List.Mem.head _)

theorem lex_6_108_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3376), (Sat.Literal.neg 108), (Sat.Literal.pos 172)] :=
  (lex_6_108_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_108_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3376), (Sat.Literal.pos 108), (Sat.Literal.neg 172)] :=
  (lex_6_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_108_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3375), (Sat.Literal.neg 108), (Sat.Literal.neg 172), (Sat.Literal.pos 3376)] :=
  (lex_6_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_108_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3375), (Sat.Literal.pos 108), (Sat.Literal.pos 172), (Sat.Literal.pos 3376)] :=
  (lex_6_108_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_107_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3376) = lexBefore s permutation6 107 := by
  exact (positive_lex_of_descriptor s 3376 permutation6 108 (by rfl)).trans ((lex_skipped s permutation6 107 108 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 108 108 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_107_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 171) = s (permuteMask permutation6 107) := by
  exact (positive_select s 171).trans (congrArg s (show (171 : Fin 256) = permuteMask permutation6 107 by rw [image6_eq]; rfl))

theorem lex_6_107_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3377) (Sat.Literal.pos 3376) (Sat.Literal.pos 107) (Sat.Literal.pos 171)) := by
  exact equality_gate s permutation6 107 (assignment s)
    (Sat.Literal.pos 3377) (Sat.Literal.pos 3376) (Sat.Literal.pos 107) (Sat.Literal.pos 171) (positive_of_descriptor s 3377 (.lex permutation6 107) (by rfl)) (lex_6_107_prefix s) (positive_select s 107) (lex_6_107_image s)

theorem lex_6_107_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3376), (Sat.Literal.pos 107), (Sat.Literal.neg 171)] := by
  exact comparison_gate s permutation6 107 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3376) (Sat.Literal.pos 107) (Sat.Literal.pos 171) (lex_6_107_prefix s) (positive_select s 107) (lex_6_107_image s)

theorem lex_6_107_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3377), (Sat.Literal.pos 3376)] :=
  (lex_6_107_gate s).prop _ (List.Mem.head _)

theorem lex_6_107_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3377), (Sat.Literal.neg 107), (Sat.Literal.pos 171)] :=
  (lex_6_107_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_107_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3377), (Sat.Literal.pos 107), (Sat.Literal.neg 171)] :=
  (lex_6_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_107_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3376), (Sat.Literal.neg 107), (Sat.Literal.neg 171), (Sat.Literal.pos 3377)] :=
  (lex_6_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_107_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3376), (Sat.Literal.pos 107), (Sat.Literal.pos 171), (Sat.Literal.pos 3377)] :=
  (lex_6_107_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_106_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3377) = lexBefore s permutation6 106 := by
  exact (positive_lex_of_descriptor s 3377 permutation6 107 (by rfl)).trans ((lex_skipped s permutation6 106 107 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 107 107 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_106_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 170) = s (permuteMask permutation6 106) := by
  exact (positive_select s 170).trans (congrArg s (show (170 : Fin 256) = permuteMask permutation6 106 by rw [image6_eq]; rfl))

theorem lex_6_106_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3378) (Sat.Literal.pos 3377) (Sat.Literal.pos 106) (Sat.Literal.pos 170)) := by
  exact equality_gate s permutation6 106 (assignment s)
    (Sat.Literal.pos 3378) (Sat.Literal.pos 3377) (Sat.Literal.pos 106) (Sat.Literal.pos 170) (positive_of_descriptor s 3378 (.lex permutation6 106) (by rfl)) (lex_6_106_prefix s) (positive_select s 106) (lex_6_106_image s)

theorem lex_6_106_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3377), (Sat.Literal.pos 106), (Sat.Literal.neg 170)] := by
  exact comparison_gate s permutation6 106 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3377) (Sat.Literal.pos 106) (Sat.Literal.pos 170) (lex_6_106_prefix s) (positive_select s 106) (lex_6_106_image s)

theorem lex_6_106_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3378), (Sat.Literal.pos 3377)] :=
  (lex_6_106_gate s).prop _ (List.Mem.head _)

theorem lex_6_106_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3378), (Sat.Literal.neg 106), (Sat.Literal.pos 170)] :=
  (lex_6_106_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_106_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3378), (Sat.Literal.pos 106), (Sat.Literal.neg 170)] :=
  (lex_6_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_106_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3377), (Sat.Literal.neg 106), (Sat.Literal.neg 170), (Sat.Literal.pos 3378)] :=
  (lex_6_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_106_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3377), (Sat.Literal.pos 106), (Sat.Literal.pos 170), (Sat.Literal.pos 3378)] :=
  (lex_6_106_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_105_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3378) = lexBefore s permutation6 105 := by
  exact (positive_lex_of_descriptor s 3378 permutation6 106 (by rfl)).trans ((lex_skipped s permutation6 105 106 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 106 106 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_105_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 169) = s (permuteMask permutation6 105) := by
  exact (positive_select s 169).trans (congrArg s (show (169 : Fin 256) = permuteMask permutation6 105 by rw [image6_eq]; rfl))

theorem lex_6_105_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3379) (Sat.Literal.pos 3378) (Sat.Literal.pos 105) (Sat.Literal.pos 169)) := by
  exact equality_gate s permutation6 105 (assignment s)
    (Sat.Literal.pos 3379) (Sat.Literal.pos 3378) (Sat.Literal.pos 105) (Sat.Literal.pos 169) (positive_of_descriptor s 3379 (.lex permutation6 105) (by rfl)) (lex_6_105_prefix s) (positive_select s 105) (lex_6_105_image s)

theorem lex_6_105_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3378), (Sat.Literal.pos 105), (Sat.Literal.neg 169)] := by
  exact comparison_gate s permutation6 105 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3378) (Sat.Literal.pos 105) (Sat.Literal.pos 169) (lex_6_105_prefix s) (positive_select s 105) (lex_6_105_image s)

theorem lex_6_105_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3379), (Sat.Literal.pos 3378)] :=
  (lex_6_105_gate s).prop _ (List.Mem.head _)

theorem lex_6_105_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3379), (Sat.Literal.neg 105), (Sat.Literal.pos 169)] :=
  (lex_6_105_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_105_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3379), (Sat.Literal.pos 105), (Sat.Literal.neg 169)] :=
  (lex_6_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_105_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3378), (Sat.Literal.neg 105), (Sat.Literal.neg 169), (Sat.Literal.pos 3379)] :=
  (lex_6_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_105_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3378), (Sat.Literal.pos 105), (Sat.Literal.pos 169), (Sat.Literal.pos 3379)] :=
  (lex_6_105_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_104_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3379) = lexBefore s permutation6 104 := by
  exact (positive_lex_of_descriptor s 3379 permutation6 105 (by rfl)).trans ((lex_skipped s permutation6 104 105 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 105 105 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_104_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 168) = s (permuteMask permutation6 104) := by
  exact (positive_select s 168).trans (congrArg s (show (168 : Fin 256) = permuteMask permutation6 104 by rw [image6_eq]; rfl))

theorem lex_6_104_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3380) (Sat.Literal.pos 3379) (Sat.Literal.pos 104) (Sat.Literal.pos 168)) := by
  exact equality_gate s permutation6 104 (assignment s)
    (Sat.Literal.pos 3380) (Sat.Literal.pos 3379) (Sat.Literal.pos 104) (Sat.Literal.pos 168) (positive_of_descriptor s 3380 (.lex permutation6 104) (by rfl)) (lex_6_104_prefix s) (positive_select s 104) (lex_6_104_image s)

theorem lex_6_104_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3379), (Sat.Literal.pos 104), (Sat.Literal.neg 168)] := by
  exact comparison_gate s permutation6 104 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3379) (Sat.Literal.pos 104) (Sat.Literal.pos 168) (lex_6_104_prefix s) (positive_select s 104) (lex_6_104_image s)

theorem lex_6_104_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3380), (Sat.Literal.pos 3379)] :=
  (lex_6_104_gate s).prop _ (List.Mem.head _)

theorem lex_6_104_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3380), (Sat.Literal.neg 104), (Sat.Literal.pos 168)] :=
  (lex_6_104_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_104_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3380), (Sat.Literal.pos 104), (Sat.Literal.neg 168)] :=
  (lex_6_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_104_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3379), (Sat.Literal.neg 104), (Sat.Literal.neg 168), (Sat.Literal.pos 3380)] :=
  (lex_6_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_104_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3379), (Sat.Literal.pos 104), (Sat.Literal.pos 168), (Sat.Literal.pos 3380)] :=
  (lex_6_104_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_103_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3380) = lexBefore s permutation6 103 := by
  exact (positive_lex_of_descriptor s 3380 permutation6 104 (by rfl)).trans ((lex_skipped s permutation6 103 104 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 104 104 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_103_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 167) = s (permuteMask permutation6 103) := by
  exact (positive_select s 167).trans (congrArg s (show (167 : Fin 256) = permuteMask permutation6 103 by rw [image6_eq]; rfl))

theorem lex_6_103_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3381) (Sat.Literal.pos 3380) (Sat.Literal.pos 103) (Sat.Literal.pos 167)) := by
  exact equality_gate s permutation6 103 (assignment s)
    (Sat.Literal.pos 3381) (Sat.Literal.pos 3380) (Sat.Literal.pos 103) (Sat.Literal.pos 167) (positive_of_descriptor s 3381 (.lex permutation6 103) (by rfl)) (lex_6_103_prefix s) (positive_select s 103) (lex_6_103_image s)

theorem lex_6_103_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3380), (Sat.Literal.pos 103), (Sat.Literal.neg 167)] := by
  exact comparison_gate s permutation6 103 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3380) (Sat.Literal.pos 103) (Sat.Literal.pos 167) (lex_6_103_prefix s) (positive_select s 103) (lex_6_103_image s)

theorem lex_6_103_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3381), (Sat.Literal.pos 3380)] :=
  (lex_6_103_gate s).prop _ (List.Mem.head _)

theorem lex_6_103_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3381), (Sat.Literal.neg 103), (Sat.Literal.pos 167)] :=
  (lex_6_103_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_103_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3381), (Sat.Literal.pos 103), (Sat.Literal.neg 167)] :=
  (lex_6_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_103_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3380), (Sat.Literal.neg 103), (Sat.Literal.neg 167), (Sat.Literal.pos 3381)] :=
  (lex_6_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_103_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3380), (Sat.Literal.pos 103), (Sat.Literal.pos 167), (Sat.Literal.pos 3381)] :=
  (lex_6_103_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_102_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3381) = lexBefore s permutation6 102 := by
  exact (positive_lex_of_descriptor s 3381 permutation6 103 (by rfl)).trans ((lex_skipped s permutation6 102 103 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 103 103 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_102_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 166) = s (permuteMask permutation6 102) := by
  exact (positive_select s 166).trans (congrArg s (show (166 : Fin 256) = permuteMask permutation6 102 by rw [image6_eq]; rfl))

theorem lex_6_102_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3382) (Sat.Literal.pos 3381) (Sat.Literal.pos 102) (Sat.Literal.pos 166)) := by
  exact equality_gate s permutation6 102 (assignment s)
    (Sat.Literal.pos 3382) (Sat.Literal.pos 3381) (Sat.Literal.pos 102) (Sat.Literal.pos 166) (positive_of_descriptor s 3382 (.lex permutation6 102) (by rfl)) (lex_6_102_prefix s) (positive_select s 102) (lex_6_102_image s)

theorem lex_6_102_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3381), (Sat.Literal.pos 102), (Sat.Literal.neg 166)] := by
  exact comparison_gate s permutation6 102 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3381) (Sat.Literal.pos 102) (Sat.Literal.pos 166) (lex_6_102_prefix s) (positive_select s 102) (lex_6_102_image s)

theorem lex_6_102_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3382), (Sat.Literal.pos 3381)] :=
  (lex_6_102_gate s).prop _ (List.Mem.head _)

theorem lex_6_102_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3382), (Sat.Literal.neg 102), (Sat.Literal.pos 166)] :=
  (lex_6_102_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_102_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3382), (Sat.Literal.pos 102), (Sat.Literal.neg 166)] :=
  (lex_6_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_102_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3381), (Sat.Literal.neg 102), (Sat.Literal.neg 166), (Sat.Literal.pos 3382)] :=
  (lex_6_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_102_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3381), (Sat.Literal.pos 102), (Sat.Literal.pos 166), (Sat.Literal.pos 3382)] :=
  (lex_6_102_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_101_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3382) = lexBefore s permutation6 101 := by
  exact (positive_lex_of_descriptor s 3382 permutation6 102 (by rfl)).trans ((lex_skipped s permutation6 101 102 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 102 102 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_101_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 165) = s (permuteMask permutation6 101) := by
  exact (positive_select s 165).trans (congrArg s (show (165 : Fin 256) = permuteMask permutation6 101 by rw [image6_eq]; rfl))

theorem lex_6_101_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3383) (Sat.Literal.pos 3382) (Sat.Literal.pos 101) (Sat.Literal.pos 165)) := by
  exact equality_gate s permutation6 101 (assignment s)
    (Sat.Literal.pos 3383) (Sat.Literal.pos 3382) (Sat.Literal.pos 101) (Sat.Literal.pos 165) (positive_of_descriptor s 3383 (.lex permutation6 101) (by rfl)) (lex_6_101_prefix s) (positive_select s 101) (lex_6_101_image s)

theorem lex_6_101_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3382), (Sat.Literal.pos 101), (Sat.Literal.neg 165)] := by
  exact comparison_gate s permutation6 101 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3382) (Sat.Literal.pos 101) (Sat.Literal.pos 165) (lex_6_101_prefix s) (positive_select s 101) (lex_6_101_image s)

theorem lex_6_101_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3383), (Sat.Literal.pos 3382)] :=
  (lex_6_101_gate s).prop _ (List.Mem.head _)

theorem lex_6_101_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3383), (Sat.Literal.neg 101), (Sat.Literal.pos 165)] :=
  (lex_6_101_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_101_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3383), (Sat.Literal.pos 101), (Sat.Literal.neg 165)] :=
  (lex_6_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_101_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3382), (Sat.Literal.neg 101), (Sat.Literal.neg 165), (Sat.Literal.pos 3383)] :=
  (lex_6_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_101_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3382), (Sat.Literal.pos 101), (Sat.Literal.pos 165), (Sat.Literal.pos 3383)] :=
  (lex_6_101_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_100_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3383) = lexBefore s permutation6 100 := by
  exact (positive_lex_of_descriptor s 3383 permutation6 101 (by rfl)).trans ((lex_skipped s permutation6 100 101 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 101 101 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_100_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 164) = s (permuteMask permutation6 100) := by
  exact (positive_select s 164).trans (congrArg s (show (164 : Fin 256) = permuteMask permutation6 100 by rw [image6_eq]; rfl))

theorem lex_6_100_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3384) (Sat.Literal.pos 3383) (Sat.Literal.pos 100) (Sat.Literal.pos 164)) := by
  exact equality_gate s permutation6 100 (assignment s)
    (Sat.Literal.pos 3384) (Sat.Literal.pos 3383) (Sat.Literal.pos 100) (Sat.Literal.pos 164) (positive_of_descriptor s 3384 (.lex permutation6 100) (by rfl)) (lex_6_100_prefix s) (positive_select s 100) (lex_6_100_image s)

theorem lex_6_100_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3383), (Sat.Literal.pos 100), (Sat.Literal.neg 164)] := by
  exact comparison_gate s permutation6 100 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3383) (Sat.Literal.pos 100) (Sat.Literal.pos 164) (lex_6_100_prefix s) (positive_select s 100) (lex_6_100_image s)

theorem lex_6_100_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3384), (Sat.Literal.pos 3383)] :=
  (lex_6_100_gate s).prop _ (List.Mem.head _)

theorem lex_6_100_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3384), (Sat.Literal.neg 100), (Sat.Literal.pos 164)] :=
  (lex_6_100_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_100_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3384), (Sat.Literal.pos 100), (Sat.Literal.neg 164)] :=
  (lex_6_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_100_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3383), (Sat.Literal.neg 100), (Sat.Literal.neg 164), (Sat.Literal.pos 3384)] :=
  (lex_6_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_100_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3383), (Sat.Literal.pos 100), (Sat.Literal.pos 164), (Sat.Literal.pos 3384)] :=
  (lex_6_100_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_99_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3384) = lexBefore s permutation6 99 := by
  exact (positive_lex_of_descriptor s 3384 permutation6 100 (by rfl)).trans ((lex_skipped s permutation6 99 100 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 100 100 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_99_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 163) = s (permuteMask permutation6 99) := by
  exact (positive_select s 163).trans (congrArg s (show (163 : Fin 256) = permuteMask permutation6 99 by rw [image6_eq]; rfl))

theorem lex_6_99_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3385) (Sat.Literal.pos 3384) (Sat.Literal.pos 99) (Sat.Literal.pos 163)) := by
  exact equality_gate s permutation6 99 (assignment s)
    (Sat.Literal.pos 3385) (Sat.Literal.pos 3384) (Sat.Literal.pos 99) (Sat.Literal.pos 163) (positive_of_descriptor s 3385 (.lex permutation6 99) (by rfl)) (lex_6_99_prefix s) (positive_select s 99) (lex_6_99_image s)

theorem lex_6_99_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3384), (Sat.Literal.pos 99), (Sat.Literal.neg 163)] := by
  exact comparison_gate s permutation6 99 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3384) (Sat.Literal.pos 99) (Sat.Literal.pos 163) (lex_6_99_prefix s) (positive_select s 99) (lex_6_99_image s)

theorem lex_6_99_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3385), (Sat.Literal.pos 3384)] :=
  (lex_6_99_gate s).prop _ (List.Mem.head _)

theorem lex_6_99_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3385), (Sat.Literal.neg 99), (Sat.Literal.pos 163)] :=
  (lex_6_99_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_99_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3385), (Sat.Literal.pos 99), (Sat.Literal.neg 163)] :=
  (lex_6_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_99_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3384), (Sat.Literal.neg 99), (Sat.Literal.neg 163), (Sat.Literal.pos 3385)] :=
  (lex_6_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_99_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3384), (Sat.Literal.pos 99), (Sat.Literal.pos 163), (Sat.Literal.pos 3385)] :=
  (lex_6_99_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_98_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3385) = lexBefore s permutation6 98 := by
  exact (positive_lex_of_descriptor s 3385 permutation6 99 (by rfl)).trans ((lex_skipped s permutation6 98 99 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 99 99 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_98_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 162) = s (permuteMask permutation6 98) := by
  exact (positive_select s 162).trans (congrArg s (show (162 : Fin 256) = permuteMask permutation6 98 by rw [image6_eq]; rfl))

theorem lex_6_98_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3386) (Sat.Literal.pos 3385) (Sat.Literal.pos 98) (Sat.Literal.pos 162)) := by
  exact equality_gate s permutation6 98 (assignment s)
    (Sat.Literal.pos 3386) (Sat.Literal.pos 3385) (Sat.Literal.pos 98) (Sat.Literal.pos 162) (positive_of_descriptor s 3386 (.lex permutation6 98) (by rfl)) (lex_6_98_prefix s) (positive_select s 98) (lex_6_98_image s)

theorem lex_6_98_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3385), (Sat.Literal.pos 98), (Sat.Literal.neg 162)] := by
  exact comparison_gate s permutation6 98 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3385) (Sat.Literal.pos 98) (Sat.Literal.pos 162) (lex_6_98_prefix s) (positive_select s 98) (lex_6_98_image s)

theorem lex_6_98_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3386), (Sat.Literal.pos 3385)] :=
  (lex_6_98_gate s).prop _ (List.Mem.head _)

theorem lex_6_98_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3386), (Sat.Literal.neg 98), (Sat.Literal.pos 162)] :=
  (lex_6_98_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_98_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3386), (Sat.Literal.pos 98), (Sat.Literal.neg 162)] :=
  (lex_6_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_98_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3385), (Sat.Literal.neg 98), (Sat.Literal.neg 162), (Sat.Literal.pos 3386)] :=
  (lex_6_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_98_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3385), (Sat.Literal.pos 98), (Sat.Literal.pos 162), (Sat.Literal.pos 3386)] :=
  (lex_6_98_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_97_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3386) = lexBefore s permutation6 97 := by
  exact (positive_lex_of_descriptor s 3386 permutation6 98 (by rfl)).trans ((lex_skipped s permutation6 97 98 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 98 98 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_97_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 161) = s (permuteMask permutation6 97) := by
  exact (positive_select s 161).trans (congrArg s (show (161 : Fin 256) = permuteMask permutation6 97 by rw [image6_eq]; rfl))

theorem lex_6_97_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3387) (Sat.Literal.pos 3386) (Sat.Literal.pos 97) (Sat.Literal.pos 161)) := by
  exact equality_gate s permutation6 97 (assignment s)
    (Sat.Literal.pos 3387) (Sat.Literal.pos 3386) (Sat.Literal.pos 97) (Sat.Literal.pos 161) (positive_of_descriptor s 3387 (.lex permutation6 97) (by rfl)) (lex_6_97_prefix s) (positive_select s 97) (lex_6_97_image s)

theorem lex_6_97_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3386), (Sat.Literal.pos 97), (Sat.Literal.neg 161)] := by
  exact comparison_gate s permutation6 97 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3386) (Sat.Literal.pos 97) (Sat.Literal.pos 161) (lex_6_97_prefix s) (positive_select s 97) (lex_6_97_image s)

theorem lex_6_97_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3387), (Sat.Literal.pos 3386)] :=
  (lex_6_97_gate s).prop _ (List.Mem.head _)

theorem lex_6_97_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3387), (Sat.Literal.neg 97), (Sat.Literal.pos 161)] :=
  (lex_6_97_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_97_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3387), (Sat.Literal.pos 97), (Sat.Literal.neg 161)] :=
  (lex_6_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_97_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3386), (Sat.Literal.neg 97), (Sat.Literal.neg 161), (Sat.Literal.pos 3387)] :=
  (lex_6_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_97_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3386), (Sat.Literal.pos 97), (Sat.Literal.pos 161), (Sat.Literal.pos 3387)] :=
  (lex_6_97_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_96_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3387) = lexBefore s permutation6 96 := by
  exact (positive_lex_of_descriptor s 3387 permutation6 97 (by rfl)).trans ((lex_skipped s permutation6 96 97 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 97 97 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_96_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 160) = s (permuteMask permutation6 96) := by
  exact (positive_select s 160).trans (congrArg s (show (160 : Fin 256) = permuteMask permutation6 96 by rw [image6_eq]; rfl))

theorem lex_6_96_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3388) (Sat.Literal.pos 3387) (Sat.Literal.pos 96) (Sat.Literal.pos 160)) := by
  exact equality_gate s permutation6 96 (assignment s)
    (Sat.Literal.pos 3388) (Sat.Literal.pos 3387) (Sat.Literal.pos 96) (Sat.Literal.pos 160) (positive_of_descriptor s 3388 (.lex permutation6 96) (by rfl)) (lex_6_96_prefix s) (positive_select s 96) (lex_6_96_image s)

theorem lex_6_96_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3387), (Sat.Literal.pos 96), (Sat.Literal.neg 160)] := by
  exact comparison_gate s permutation6 96 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3387) (Sat.Literal.pos 96) (Sat.Literal.pos 160) (lex_6_96_prefix s) (positive_select s 96) (lex_6_96_image s)

theorem lex_6_96_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3388), (Sat.Literal.pos 3387)] :=
  (lex_6_96_gate s).prop _ (List.Mem.head _)

theorem lex_6_96_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3388), (Sat.Literal.neg 96), (Sat.Literal.pos 160)] :=
  (lex_6_96_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_96_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3388), (Sat.Literal.pos 96), (Sat.Literal.neg 160)] :=
  (lex_6_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_96_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3387), (Sat.Literal.neg 96), (Sat.Literal.neg 160), (Sat.Literal.pos 3388)] :=
  (lex_6_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_96_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3387), (Sat.Literal.pos 96), (Sat.Literal.pos 160), (Sat.Literal.pos 3388)] :=
  (lex_6_96_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_95_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3388) = lexBefore s permutation6 95 := by
  exact (positive_lex_of_descriptor s 3388 permutation6 96 (by rfl)).trans ((lex_skipped s permutation6 95 96 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 96 96 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_95_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 159) = s (permuteMask permutation6 95) := by
  exact (positive_select s 159).trans (congrArg s (show (159 : Fin 256) = permuteMask permutation6 95 by rw [image6_eq]; rfl))

theorem lex_6_95_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3389) (Sat.Literal.pos 3388) (Sat.Literal.pos 95) (Sat.Literal.pos 159)) := by
  exact equality_gate s permutation6 95 (assignment s)
    (Sat.Literal.pos 3389) (Sat.Literal.pos 3388) (Sat.Literal.pos 95) (Sat.Literal.pos 159) (positive_of_descriptor s 3389 (.lex permutation6 95) (by rfl)) (lex_6_95_prefix s) (positive_select s 95) (lex_6_95_image s)

theorem lex_6_95_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3388), (Sat.Literal.pos 95), (Sat.Literal.neg 159)] := by
  exact comparison_gate s permutation6 95 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3388) (Sat.Literal.pos 95) (Sat.Literal.pos 159) (lex_6_95_prefix s) (positive_select s 95) (lex_6_95_image s)

theorem lex_6_95_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3389), (Sat.Literal.pos 3388)] :=
  (lex_6_95_gate s).prop _ (List.Mem.head _)

theorem lex_6_95_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3389), (Sat.Literal.neg 95), (Sat.Literal.pos 159)] :=
  (lex_6_95_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_95_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3389), (Sat.Literal.pos 95), (Sat.Literal.neg 159)] :=
  (lex_6_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_95_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3388), (Sat.Literal.neg 95), (Sat.Literal.neg 159), (Sat.Literal.pos 3389)] :=
  (lex_6_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_95_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3388), (Sat.Literal.pos 95), (Sat.Literal.pos 159), (Sat.Literal.pos 3389)] :=
  (lex_6_95_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_94_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3389) = lexBefore s permutation6 94 := by
  exact (positive_lex_of_descriptor s 3389 permutation6 95 (by rfl)).trans ((lex_skipped s permutation6 94 95 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 95 95 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_94_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 158) = s (permuteMask permutation6 94) := by
  exact (positive_select s 158).trans (congrArg s (show (158 : Fin 256) = permuteMask permutation6 94 by rw [image6_eq]; rfl))

theorem lex_6_94_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3390) (Sat.Literal.pos 3389) (Sat.Literal.pos 94) (Sat.Literal.pos 158)) := by
  exact equality_gate s permutation6 94 (assignment s)
    (Sat.Literal.pos 3390) (Sat.Literal.pos 3389) (Sat.Literal.pos 94) (Sat.Literal.pos 158) (positive_of_descriptor s 3390 (.lex permutation6 94) (by rfl)) (lex_6_94_prefix s) (positive_select s 94) (lex_6_94_image s)

theorem lex_6_94_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3389), (Sat.Literal.pos 94), (Sat.Literal.neg 158)] := by
  exact comparison_gate s permutation6 94 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3389) (Sat.Literal.pos 94) (Sat.Literal.pos 158) (lex_6_94_prefix s) (positive_select s 94) (lex_6_94_image s)

theorem lex_6_94_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3390), (Sat.Literal.pos 3389)] :=
  (lex_6_94_gate s).prop _ (List.Mem.head _)

theorem lex_6_94_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3390), (Sat.Literal.neg 94), (Sat.Literal.pos 158)] :=
  (lex_6_94_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_94_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3390), (Sat.Literal.pos 94), (Sat.Literal.neg 158)] :=
  (lex_6_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_94_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3389), (Sat.Literal.neg 94), (Sat.Literal.neg 158), (Sat.Literal.pos 3390)] :=
  (lex_6_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_94_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3389), (Sat.Literal.pos 94), (Sat.Literal.pos 158), (Sat.Literal.pos 3390)] :=
  (lex_6_94_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_93_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3390) = lexBefore s permutation6 93 := by
  exact (positive_lex_of_descriptor s 3390 permutation6 94 (by rfl)).trans ((lex_skipped s permutation6 93 94 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 94 94 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_93_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 157) = s (permuteMask permutation6 93) := by
  exact (positive_select s 157).trans (congrArg s (show (157 : Fin 256) = permuteMask permutation6 93 by rw [image6_eq]; rfl))

theorem lex_6_93_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3391) (Sat.Literal.pos 3390) (Sat.Literal.pos 93) (Sat.Literal.pos 157)) := by
  exact equality_gate s permutation6 93 (assignment s)
    (Sat.Literal.pos 3391) (Sat.Literal.pos 3390) (Sat.Literal.pos 93) (Sat.Literal.pos 157) (positive_of_descriptor s 3391 (.lex permutation6 93) (by rfl)) (lex_6_93_prefix s) (positive_select s 93) (lex_6_93_image s)

theorem lex_6_93_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3390), (Sat.Literal.pos 93), (Sat.Literal.neg 157)] := by
  exact comparison_gate s permutation6 93 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3390) (Sat.Literal.pos 93) (Sat.Literal.pos 157) (lex_6_93_prefix s) (positive_select s 93) (lex_6_93_image s)

theorem lex_6_93_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3391), (Sat.Literal.pos 3390)] :=
  (lex_6_93_gate s).prop _ (List.Mem.head _)

theorem lex_6_93_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3391), (Sat.Literal.neg 93), (Sat.Literal.pos 157)] :=
  (lex_6_93_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_93_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3391), (Sat.Literal.pos 93), (Sat.Literal.neg 157)] :=
  (lex_6_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_93_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3390), (Sat.Literal.neg 93), (Sat.Literal.neg 157), (Sat.Literal.pos 3391)] :=
  (lex_6_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_93_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3390), (Sat.Literal.pos 93), (Sat.Literal.pos 157), (Sat.Literal.pos 3391)] :=
  (lex_6_93_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_92_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3391) = lexBefore s permutation6 92 := by
  exact (positive_lex_of_descriptor s 3391 permutation6 93 (by rfl)).trans ((lex_skipped s permutation6 92 93 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 93 93 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_92_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 156) = s (permuteMask permutation6 92) := by
  exact (positive_select s 156).trans (congrArg s (show (156 : Fin 256) = permuteMask permutation6 92 by rw [image6_eq]; rfl))

theorem lex_6_92_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3392) (Sat.Literal.pos 3391) (Sat.Literal.pos 92) (Sat.Literal.pos 156)) := by
  exact equality_gate s permutation6 92 (assignment s)
    (Sat.Literal.pos 3392) (Sat.Literal.pos 3391) (Sat.Literal.pos 92) (Sat.Literal.pos 156) (positive_of_descriptor s 3392 (.lex permutation6 92) (by rfl)) (lex_6_92_prefix s) (positive_select s 92) (lex_6_92_image s)

theorem lex_6_92_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3391), (Sat.Literal.pos 92), (Sat.Literal.neg 156)] := by
  exact comparison_gate s permutation6 92 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3391) (Sat.Literal.pos 92) (Sat.Literal.pos 156) (lex_6_92_prefix s) (positive_select s 92) (lex_6_92_image s)

theorem lex_6_92_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3392), (Sat.Literal.pos 3391)] :=
  (lex_6_92_gate s).prop _ (List.Mem.head _)

theorem lex_6_92_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3392), (Sat.Literal.neg 92), (Sat.Literal.pos 156)] :=
  (lex_6_92_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_92_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3392), (Sat.Literal.pos 92), (Sat.Literal.neg 156)] :=
  (lex_6_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_92_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3391), (Sat.Literal.neg 92), (Sat.Literal.neg 156), (Sat.Literal.pos 3392)] :=
  (lex_6_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_92_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3391), (Sat.Literal.pos 92), (Sat.Literal.pos 156), (Sat.Literal.pos 3392)] :=
  (lex_6_92_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_91_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3392) = lexBefore s permutation6 91 := by
  exact (positive_lex_of_descriptor s 3392 permutation6 92 (by rfl)).trans ((lex_skipped s permutation6 91 92 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 92 92 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_91_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 155) = s (permuteMask permutation6 91) := by
  exact (positive_select s 155).trans (congrArg s (show (155 : Fin 256) = permuteMask permutation6 91 by rw [image6_eq]; rfl))

theorem lex_6_91_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3393) (Sat.Literal.pos 3392) (Sat.Literal.pos 91) (Sat.Literal.pos 155)) := by
  exact equality_gate s permutation6 91 (assignment s)
    (Sat.Literal.pos 3393) (Sat.Literal.pos 3392) (Sat.Literal.pos 91) (Sat.Literal.pos 155) (positive_of_descriptor s 3393 (.lex permutation6 91) (by rfl)) (lex_6_91_prefix s) (positive_select s 91) (lex_6_91_image s)

theorem lex_6_91_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3392), (Sat.Literal.pos 91), (Sat.Literal.neg 155)] := by
  exact comparison_gate s permutation6 91 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3392) (Sat.Literal.pos 91) (Sat.Literal.pos 155) (lex_6_91_prefix s) (positive_select s 91) (lex_6_91_image s)

theorem lex_6_91_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3393), (Sat.Literal.pos 3392)] :=
  (lex_6_91_gate s).prop _ (List.Mem.head _)

theorem lex_6_91_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3393), (Sat.Literal.neg 91), (Sat.Literal.pos 155)] :=
  (lex_6_91_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_91_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3393), (Sat.Literal.pos 91), (Sat.Literal.neg 155)] :=
  (lex_6_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_91_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3392), (Sat.Literal.neg 91), (Sat.Literal.neg 155), (Sat.Literal.pos 3393)] :=
  (lex_6_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_91_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3392), (Sat.Literal.pos 91), (Sat.Literal.pos 155), (Sat.Literal.pos 3393)] :=
  (lex_6_91_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_90_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3393) = lexBefore s permutation6 90 := by
  exact (positive_lex_of_descriptor s 3393 permutation6 91 (by rfl)).trans ((lex_skipped s permutation6 90 91 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 91 91 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_90_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 154) = s (permuteMask permutation6 90) := by
  exact (positive_select s 154).trans (congrArg s (show (154 : Fin 256) = permuteMask permutation6 90 by rw [image6_eq]; rfl))

theorem lex_6_90_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3394) (Sat.Literal.pos 3393) (Sat.Literal.pos 90) (Sat.Literal.pos 154)) := by
  exact equality_gate s permutation6 90 (assignment s)
    (Sat.Literal.pos 3394) (Sat.Literal.pos 3393) (Sat.Literal.pos 90) (Sat.Literal.pos 154) (positive_of_descriptor s 3394 (.lex permutation6 90) (by rfl)) (lex_6_90_prefix s) (positive_select s 90) (lex_6_90_image s)

theorem lex_6_90_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3393), (Sat.Literal.pos 90), (Sat.Literal.neg 154)] := by
  exact comparison_gate s permutation6 90 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3393) (Sat.Literal.pos 90) (Sat.Literal.pos 154) (lex_6_90_prefix s) (positive_select s 90) (lex_6_90_image s)

theorem lex_6_90_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3394), (Sat.Literal.pos 3393)] :=
  (lex_6_90_gate s).prop _ (List.Mem.head _)

theorem lex_6_90_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3394), (Sat.Literal.neg 90), (Sat.Literal.pos 154)] :=
  (lex_6_90_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_90_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3394), (Sat.Literal.pos 90), (Sat.Literal.neg 154)] :=
  (lex_6_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_90_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3393), (Sat.Literal.neg 90), (Sat.Literal.neg 154), (Sat.Literal.pos 3394)] :=
  (lex_6_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_90_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3393), (Sat.Literal.pos 90), (Sat.Literal.pos 154), (Sat.Literal.pos 3394)] :=
  (lex_6_90_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_89_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3394) = lexBefore s permutation6 89 := by
  exact (positive_lex_of_descriptor s 3394 permutation6 90 (by rfl)).trans ((lex_skipped s permutation6 89 90 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 90 90 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_89_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 153) = s (permuteMask permutation6 89) := by
  exact (positive_select s 153).trans (congrArg s (show (153 : Fin 256) = permuteMask permutation6 89 by rw [image6_eq]; rfl))

theorem lex_6_89_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3395) (Sat.Literal.pos 3394) (Sat.Literal.pos 89) (Sat.Literal.pos 153)) := by
  exact equality_gate s permutation6 89 (assignment s)
    (Sat.Literal.pos 3395) (Sat.Literal.pos 3394) (Sat.Literal.pos 89) (Sat.Literal.pos 153) (positive_of_descriptor s 3395 (.lex permutation6 89) (by rfl)) (lex_6_89_prefix s) (positive_select s 89) (lex_6_89_image s)

theorem lex_6_89_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3394), (Sat.Literal.pos 89), (Sat.Literal.neg 153)] := by
  exact comparison_gate s permutation6 89 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3394) (Sat.Literal.pos 89) (Sat.Literal.pos 153) (lex_6_89_prefix s) (positive_select s 89) (lex_6_89_image s)

theorem lex_6_89_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3395), (Sat.Literal.pos 3394)] :=
  (lex_6_89_gate s).prop _ (List.Mem.head _)

theorem lex_6_89_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3395), (Sat.Literal.neg 89), (Sat.Literal.pos 153)] :=
  (lex_6_89_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_89_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3395), (Sat.Literal.pos 89), (Sat.Literal.neg 153)] :=
  (lex_6_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_89_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3394), (Sat.Literal.neg 89), (Sat.Literal.neg 153), (Sat.Literal.pos 3395)] :=
  (lex_6_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_89_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3394), (Sat.Literal.pos 89), (Sat.Literal.pos 153), (Sat.Literal.pos 3395)] :=
  (lex_6_89_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_88_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3395) = lexBefore s permutation6 88 := by
  exact (positive_lex_of_descriptor s 3395 permutation6 89 (by rfl)).trans ((lex_skipped s permutation6 88 89 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 89 89 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_88_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 152) = s (permuteMask permutation6 88) := by
  exact (positive_select s 152).trans (congrArg s (show (152 : Fin 256) = permuteMask permutation6 88 by rw [image6_eq]; rfl))

theorem lex_6_88_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3396) (Sat.Literal.pos 3395) (Sat.Literal.pos 88) (Sat.Literal.pos 152)) := by
  exact equality_gate s permutation6 88 (assignment s)
    (Sat.Literal.pos 3396) (Sat.Literal.pos 3395) (Sat.Literal.pos 88) (Sat.Literal.pos 152) (positive_of_descriptor s 3396 (.lex permutation6 88) (by rfl)) (lex_6_88_prefix s) (positive_select s 88) (lex_6_88_image s)

theorem lex_6_88_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3395), (Sat.Literal.pos 88), (Sat.Literal.neg 152)] := by
  exact comparison_gate s permutation6 88 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3395) (Sat.Literal.pos 88) (Sat.Literal.pos 152) (lex_6_88_prefix s) (positive_select s 88) (lex_6_88_image s)

theorem lex_6_88_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3396), (Sat.Literal.pos 3395)] :=
  (lex_6_88_gate s).prop _ (List.Mem.head _)

theorem lex_6_88_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3396), (Sat.Literal.neg 88), (Sat.Literal.pos 152)] :=
  (lex_6_88_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_88_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3396), (Sat.Literal.pos 88), (Sat.Literal.neg 152)] :=
  (lex_6_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_88_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3395), (Sat.Literal.neg 88), (Sat.Literal.neg 152), (Sat.Literal.pos 3396)] :=
  (lex_6_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_88_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3395), (Sat.Literal.pos 88), (Sat.Literal.pos 152), (Sat.Literal.pos 3396)] :=
  (lex_6_88_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_87_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3396) = lexBefore s permutation6 87 := by
  exact (positive_lex_of_descriptor s 3396 permutation6 88 (by rfl)).trans ((lex_skipped s permutation6 87 88 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 88 88 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_87_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 151) = s (permuteMask permutation6 87) := by
  exact (positive_select s 151).trans (congrArg s (show (151 : Fin 256) = permuteMask permutation6 87 by rw [image6_eq]; rfl))

theorem lex_6_87_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3397) (Sat.Literal.pos 3396) (Sat.Literal.pos 87) (Sat.Literal.pos 151)) := by
  exact equality_gate s permutation6 87 (assignment s)
    (Sat.Literal.pos 3397) (Sat.Literal.pos 3396) (Sat.Literal.pos 87) (Sat.Literal.pos 151) (positive_of_descriptor s 3397 (.lex permutation6 87) (by rfl)) (lex_6_87_prefix s) (positive_select s 87) (lex_6_87_image s)

theorem lex_6_87_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3396), (Sat.Literal.pos 87), (Sat.Literal.neg 151)] := by
  exact comparison_gate s permutation6 87 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3396) (Sat.Literal.pos 87) (Sat.Literal.pos 151) (lex_6_87_prefix s) (positive_select s 87) (lex_6_87_image s)

theorem lex_6_87_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3397), (Sat.Literal.pos 3396)] :=
  (lex_6_87_gate s).prop _ (List.Mem.head _)

theorem lex_6_87_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3397), (Sat.Literal.neg 87), (Sat.Literal.pos 151)] :=
  (lex_6_87_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_87_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3397), (Sat.Literal.pos 87), (Sat.Literal.neg 151)] :=
  (lex_6_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_87_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3396), (Sat.Literal.neg 87), (Sat.Literal.neg 151), (Sat.Literal.pos 3397)] :=
  (lex_6_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_87_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3396), (Sat.Literal.pos 87), (Sat.Literal.pos 151), (Sat.Literal.pos 3397)] :=
  (lex_6_87_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_86_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3397) = lexBefore s permutation6 86 := by
  exact (positive_lex_of_descriptor s 3397 permutation6 87 (by rfl)).trans ((lex_skipped s permutation6 86 87 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 87 87 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_86_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 150) = s (permuteMask permutation6 86) := by
  exact (positive_select s 150).trans (congrArg s (show (150 : Fin 256) = permuteMask permutation6 86 by rw [image6_eq]; rfl))

theorem lex_6_86_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3398) (Sat.Literal.pos 3397) (Sat.Literal.pos 86) (Sat.Literal.pos 150)) := by
  exact equality_gate s permutation6 86 (assignment s)
    (Sat.Literal.pos 3398) (Sat.Literal.pos 3397) (Sat.Literal.pos 86) (Sat.Literal.pos 150) (positive_of_descriptor s 3398 (.lex permutation6 86) (by rfl)) (lex_6_86_prefix s) (positive_select s 86) (lex_6_86_image s)

theorem lex_6_86_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3397), (Sat.Literal.pos 86), (Sat.Literal.neg 150)] := by
  exact comparison_gate s permutation6 86 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3397) (Sat.Literal.pos 86) (Sat.Literal.pos 150) (lex_6_86_prefix s) (positive_select s 86) (lex_6_86_image s)

theorem lex_6_86_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3398), (Sat.Literal.pos 3397)] :=
  (lex_6_86_gate s).prop _ (List.Mem.head _)

theorem lex_6_86_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3398), (Sat.Literal.neg 86), (Sat.Literal.pos 150)] :=
  (lex_6_86_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_86_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3398), (Sat.Literal.pos 86), (Sat.Literal.neg 150)] :=
  (lex_6_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_86_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3397), (Sat.Literal.neg 86), (Sat.Literal.neg 150), (Sat.Literal.pos 3398)] :=
  (lex_6_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_86_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3397), (Sat.Literal.pos 86), (Sat.Literal.pos 150), (Sat.Literal.pos 3398)] :=
  (lex_6_86_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_85_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3398) = lexBefore s permutation6 85 := by
  exact (positive_lex_of_descriptor s 3398 permutation6 86 (by rfl)).trans ((lex_skipped s permutation6 85 86 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 86 86 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_85_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 149) = s (permuteMask permutation6 85) := by
  exact (positive_select s 149).trans (congrArg s (show (149 : Fin 256) = permuteMask permutation6 85 by rw [image6_eq]; rfl))

theorem lex_6_85_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3399) (Sat.Literal.pos 3398) (Sat.Literal.pos 85) (Sat.Literal.pos 149)) := by
  exact equality_gate s permutation6 85 (assignment s)
    (Sat.Literal.pos 3399) (Sat.Literal.pos 3398) (Sat.Literal.pos 85) (Sat.Literal.pos 149) (positive_of_descriptor s 3399 (.lex permutation6 85) (by rfl)) (lex_6_85_prefix s) (positive_select s 85) (lex_6_85_image s)

theorem lex_6_85_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3398), (Sat.Literal.pos 85), (Sat.Literal.neg 149)] := by
  exact comparison_gate s permutation6 85 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3398) (Sat.Literal.pos 85) (Sat.Literal.pos 149) (lex_6_85_prefix s) (positive_select s 85) (lex_6_85_image s)

theorem lex_6_85_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3399), (Sat.Literal.pos 3398)] :=
  (lex_6_85_gate s).prop _ (List.Mem.head _)

theorem lex_6_85_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3399), (Sat.Literal.neg 85), (Sat.Literal.pos 149)] :=
  (lex_6_85_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_85_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3399), (Sat.Literal.pos 85), (Sat.Literal.neg 149)] :=
  (lex_6_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_85_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3398), (Sat.Literal.neg 85), (Sat.Literal.neg 149), (Sat.Literal.pos 3399)] :=
  (lex_6_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_85_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3398), (Sat.Literal.pos 85), (Sat.Literal.pos 149), (Sat.Literal.pos 3399)] :=
  (lex_6_85_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_84_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3399) = lexBefore s permutation6 84 := by
  exact (positive_lex_of_descriptor s 3399 permutation6 85 (by rfl)).trans ((lex_skipped s permutation6 84 85 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 85 85 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_84_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 148) = s (permuteMask permutation6 84) := by
  exact (positive_select s 148).trans (congrArg s (show (148 : Fin 256) = permuteMask permutation6 84 by rw [image6_eq]; rfl))

theorem lex_6_84_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3400) (Sat.Literal.pos 3399) (Sat.Literal.pos 84) (Sat.Literal.pos 148)) := by
  exact equality_gate s permutation6 84 (assignment s)
    (Sat.Literal.pos 3400) (Sat.Literal.pos 3399) (Sat.Literal.pos 84) (Sat.Literal.pos 148) (positive_of_descriptor s 3400 (.lex permutation6 84) (by rfl)) (lex_6_84_prefix s) (positive_select s 84) (lex_6_84_image s)

theorem lex_6_84_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3399), (Sat.Literal.pos 84), (Sat.Literal.neg 148)] := by
  exact comparison_gate s permutation6 84 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3399) (Sat.Literal.pos 84) (Sat.Literal.pos 148) (lex_6_84_prefix s) (positive_select s 84) (lex_6_84_image s)

theorem lex_6_84_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3400), (Sat.Literal.pos 3399)] :=
  (lex_6_84_gate s).prop _ (List.Mem.head _)

theorem lex_6_84_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3400), (Sat.Literal.neg 84), (Sat.Literal.pos 148)] :=
  (lex_6_84_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_84_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3400), (Sat.Literal.pos 84), (Sat.Literal.neg 148)] :=
  (lex_6_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_84_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3399), (Sat.Literal.neg 84), (Sat.Literal.neg 148), (Sat.Literal.pos 3400)] :=
  (lex_6_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_84_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3399), (Sat.Literal.pos 84), (Sat.Literal.pos 148), (Sat.Literal.pos 3400)] :=
  (lex_6_84_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_83_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3400) = lexBefore s permutation6 83 := by
  exact (positive_lex_of_descriptor s 3400 permutation6 84 (by rfl)).trans ((lex_skipped s permutation6 83 84 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 84 84 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_83_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 147) = s (permuteMask permutation6 83) := by
  exact (positive_select s 147).trans (congrArg s (show (147 : Fin 256) = permuteMask permutation6 83 by rw [image6_eq]; rfl))

theorem lex_6_83_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3401) (Sat.Literal.pos 3400) (Sat.Literal.pos 83) (Sat.Literal.pos 147)) := by
  exact equality_gate s permutation6 83 (assignment s)
    (Sat.Literal.pos 3401) (Sat.Literal.pos 3400) (Sat.Literal.pos 83) (Sat.Literal.pos 147) (positive_of_descriptor s 3401 (.lex permutation6 83) (by rfl)) (lex_6_83_prefix s) (positive_select s 83) (lex_6_83_image s)

theorem lex_6_83_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3400), (Sat.Literal.pos 83), (Sat.Literal.neg 147)] := by
  exact comparison_gate s permutation6 83 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3400) (Sat.Literal.pos 83) (Sat.Literal.pos 147) (lex_6_83_prefix s) (positive_select s 83) (lex_6_83_image s)

theorem lex_6_83_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3401), (Sat.Literal.pos 3400)] :=
  (lex_6_83_gate s).prop _ (List.Mem.head _)

theorem lex_6_83_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3401), (Sat.Literal.neg 83), (Sat.Literal.pos 147)] :=
  (lex_6_83_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_83_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3401), (Sat.Literal.pos 83), (Sat.Literal.neg 147)] :=
  (lex_6_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_83_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3400), (Sat.Literal.neg 83), (Sat.Literal.neg 147), (Sat.Literal.pos 3401)] :=
  (lex_6_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_83_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3400), (Sat.Literal.pos 83), (Sat.Literal.pos 147), (Sat.Literal.pos 3401)] :=
  (lex_6_83_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_82_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3401) = lexBefore s permutation6 82 := by
  exact (positive_lex_of_descriptor s 3401 permutation6 83 (by rfl)).trans ((lex_skipped s permutation6 82 83 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 83 83 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_82_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 146) = s (permuteMask permutation6 82) := by
  exact (positive_select s 146).trans (congrArg s (show (146 : Fin 256) = permuteMask permutation6 82 by rw [image6_eq]; rfl))

theorem lex_6_82_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3402) (Sat.Literal.pos 3401) (Sat.Literal.pos 82) (Sat.Literal.pos 146)) := by
  exact equality_gate s permutation6 82 (assignment s)
    (Sat.Literal.pos 3402) (Sat.Literal.pos 3401) (Sat.Literal.pos 82) (Sat.Literal.pos 146) (positive_of_descriptor s 3402 (.lex permutation6 82) (by rfl)) (lex_6_82_prefix s) (positive_select s 82) (lex_6_82_image s)

theorem lex_6_82_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3401), (Sat.Literal.pos 82), (Sat.Literal.neg 146)] := by
  exact comparison_gate s permutation6 82 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3401) (Sat.Literal.pos 82) (Sat.Literal.pos 146) (lex_6_82_prefix s) (positive_select s 82) (lex_6_82_image s)

theorem lex_6_82_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3402), (Sat.Literal.pos 3401)] :=
  (lex_6_82_gate s).prop _ (List.Mem.head _)

theorem lex_6_82_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3402), (Sat.Literal.neg 82), (Sat.Literal.pos 146)] :=
  (lex_6_82_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_82_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3402), (Sat.Literal.pos 82), (Sat.Literal.neg 146)] :=
  (lex_6_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_82_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3401), (Sat.Literal.neg 82), (Sat.Literal.neg 146), (Sat.Literal.pos 3402)] :=
  (lex_6_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_82_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3401), (Sat.Literal.pos 82), (Sat.Literal.pos 146), (Sat.Literal.pos 3402)] :=
  (lex_6_82_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_81_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3402) = lexBefore s permutation6 81 := by
  exact (positive_lex_of_descriptor s 3402 permutation6 82 (by rfl)).trans ((lex_skipped s permutation6 81 82 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 82 82 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_81_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 145) = s (permuteMask permutation6 81) := by
  exact (positive_select s 145).trans (congrArg s (show (145 : Fin 256) = permuteMask permutation6 81 by rw [image6_eq]; rfl))

theorem lex_6_81_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3403) (Sat.Literal.pos 3402) (Sat.Literal.pos 81) (Sat.Literal.pos 145)) := by
  exact equality_gate s permutation6 81 (assignment s)
    (Sat.Literal.pos 3403) (Sat.Literal.pos 3402) (Sat.Literal.pos 81) (Sat.Literal.pos 145) (positive_of_descriptor s 3403 (.lex permutation6 81) (by rfl)) (lex_6_81_prefix s) (positive_select s 81) (lex_6_81_image s)

theorem lex_6_81_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3402), (Sat.Literal.pos 81), (Sat.Literal.neg 145)] := by
  exact comparison_gate s permutation6 81 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3402) (Sat.Literal.pos 81) (Sat.Literal.pos 145) (lex_6_81_prefix s) (positive_select s 81) (lex_6_81_image s)

theorem lex_6_81_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3403), (Sat.Literal.pos 3402)] :=
  (lex_6_81_gate s).prop _ (List.Mem.head _)

theorem lex_6_81_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3403), (Sat.Literal.neg 81), (Sat.Literal.pos 145)] :=
  (lex_6_81_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_81_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3403), (Sat.Literal.pos 81), (Sat.Literal.neg 145)] :=
  (lex_6_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_81_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3402), (Sat.Literal.neg 81), (Sat.Literal.neg 145), (Sat.Literal.pos 3403)] :=
  (lex_6_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_81_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3402), (Sat.Literal.pos 81), (Sat.Literal.pos 145), (Sat.Literal.pos 3403)] :=
  (lex_6_81_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_80_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3403) = lexBefore s permutation6 80 := by
  exact (positive_lex_of_descriptor s 3403 permutation6 81 (by rfl)).trans ((lex_skipped s permutation6 80 81 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 81 81 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_80_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 144) = s (permuteMask permutation6 80) := by
  exact (positive_select s 144).trans (congrArg s (show (144 : Fin 256) = permuteMask permutation6 80 by rw [image6_eq]; rfl))

theorem lex_6_80_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3404) (Sat.Literal.pos 3403) (Sat.Literal.pos 80) (Sat.Literal.pos 144)) := by
  exact equality_gate s permutation6 80 (assignment s)
    (Sat.Literal.pos 3404) (Sat.Literal.pos 3403) (Sat.Literal.pos 80) (Sat.Literal.pos 144) (positive_of_descriptor s 3404 (.lex permutation6 80) (by rfl)) (lex_6_80_prefix s) (positive_select s 80) (lex_6_80_image s)

theorem lex_6_80_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3403), (Sat.Literal.pos 80), (Sat.Literal.neg 144)] := by
  exact comparison_gate s permutation6 80 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3403) (Sat.Literal.pos 80) (Sat.Literal.pos 144) (lex_6_80_prefix s) (positive_select s 80) (lex_6_80_image s)

theorem lex_6_80_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3404), (Sat.Literal.pos 3403)] :=
  (lex_6_80_gate s).prop _ (List.Mem.head _)

theorem lex_6_80_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3404), (Sat.Literal.neg 80), (Sat.Literal.pos 144)] :=
  (lex_6_80_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_80_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3404), (Sat.Literal.pos 80), (Sat.Literal.neg 144)] :=
  (lex_6_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_80_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3403), (Sat.Literal.neg 80), (Sat.Literal.neg 144), (Sat.Literal.pos 3404)] :=
  (lex_6_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_80_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3403), (Sat.Literal.pos 80), (Sat.Literal.pos 144), (Sat.Literal.pos 3404)] :=
  (lex_6_80_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_79_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3404) = lexBefore s permutation6 79 := by
  exact (positive_lex_of_descriptor s 3404 permutation6 80 (by rfl)).trans ((lex_skipped s permutation6 79 80 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 80 80 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_79_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 143) = s (permuteMask permutation6 79) := by
  exact (positive_select s 143).trans (congrArg s (show (143 : Fin 256) = permuteMask permutation6 79 by rw [image6_eq]; rfl))

theorem lex_6_79_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3405) (Sat.Literal.pos 3404) (Sat.Literal.pos 79) (Sat.Literal.pos 143)) := by
  exact equality_gate s permutation6 79 (assignment s)
    (Sat.Literal.pos 3405) (Sat.Literal.pos 3404) (Sat.Literal.pos 79) (Sat.Literal.pos 143) (positive_of_descriptor s 3405 (.lex permutation6 79) (by rfl)) (lex_6_79_prefix s) (positive_select s 79) (lex_6_79_image s)

theorem lex_6_79_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3404), (Sat.Literal.pos 79), (Sat.Literal.neg 143)] := by
  exact comparison_gate s permutation6 79 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3404) (Sat.Literal.pos 79) (Sat.Literal.pos 143) (lex_6_79_prefix s) (positive_select s 79) (lex_6_79_image s)

theorem lex_6_79_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3405), (Sat.Literal.pos 3404)] :=
  (lex_6_79_gate s).prop _ (List.Mem.head _)

theorem lex_6_79_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3405), (Sat.Literal.neg 79), (Sat.Literal.pos 143)] :=
  (lex_6_79_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_79_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3405), (Sat.Literal.pos 79), (Sat.Literal.neg 143)] :=
  (lex_6_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_79_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3404), (Sat.Literal.neg 79), (Sat.Literal.neg 143), (Sat.Literal.pos 3405)] :=
  (lex_6_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_79_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3404), (Sat.Literal.pos 79), (Sat.Literal.pos 143), (Sat.Literal.pos 3405)] :=
  (lex_6_79_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_78_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3405) = lexBefore s permutation6 78 := by
  exact (positive_lex_of_descriptor s 3405 permutation6 79 (by rfl)).trans ((lex_skipped s permutation6 78 79 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 79 79 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_78_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 142) = s (permuteMask permutation6 78) := by
  exact (positive_select s 142).trans (congrArg s (show (142 : Fin 256) = permuteMask permutation6 78 by rw [image6_eq]; rfl))

theorem lex_6_78_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3406) (Sat.Literal.pos 3405) (Sat.Literal.pos 78) (Sat.Literal.pos 142)) := by
  exact equality_gate s permutation6 78 (assignment s)
    (Sat.Literal.pos 3406) (Sat.Literal.pos 3405) (Sat.Literal.pos 78) (Sat.Literal.pos 142) (positive_of_descriptor s 3406 (.lex permutation6 78) (by rfl)) (lex_6_78_prefix s) (positive_select s 78) (lex_6_78_image s)

theorem lex_6_78_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3405), (Sat.Literal.pos 78), (Sat.Literal.neg 142)] := by
  exact comparison_gate s permutation6 78 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3405) (Sat.Literal.pos 78) (Sat.Literal.pos 142) (lex_6_78_prefix s) (positive_select s 78) (lex_6_78_image s)

theorem lex_6_78_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3406), (Sat.Literal.pos 3405)] :=
  (lex_6_78_gate s).prop _ (List.Mem.head _)

theorem lex_6_78_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3406), (Sat.Literal.neg 78), (Sat.Literal.pos 142)] :=
  (lex_6_78_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_78_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3406), (Sat.Literal.pos 78), (Sat.Literal.neg 142)] :=
  (lex_6_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_78_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3405), (Sat.Literal.neg 78), (Sat.Literal.neg 142), (Sat.Literal.pos 3406)] :=
  (lex_6_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_78_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3405), (Sat.Literal.pos 78), (Sat.Literal.pos 142), (Sat.Literal.pos 3406)] :=
  (lex_6_78_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_77_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3406) = lexBefore s permutation6 77 := by
  exact (positive_lex_of_descriptor s 3406 permutation6 78 (by rfl)).trans ((lex_skipped s permutation6 77 78 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 78 78 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_77_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 141) = s (permuteMask permutation6 77) := by
  exact (positive_select s 141).trans (congrArg s (show (141 : Fin 256) = permuteMask permutation6 77 by rw [image6_eq]; rfl))

theorem lex_6_77_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3407) (Sat.Literal.pos 3406) (Sat.Literal.pos 77) (Sat.Literal.pos 141)) := by
  exact equality_gate s permutation6 77 (assignment s)
    (Sat.Literal.pos 3407) (Sat.Literal.pos 3406) (Sat.Literal.pos 77) (Sat.Literal.pos 141) (positive_of_descriptor s 3407 (.lex permutation6 77) (by rfl)) (lex_6_77_prefix s) (positive_select s 77) (lex_6_77_image s)

theorem lex_6_77_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3406), (Sat.Literal.pos 77), (Sat.Literal.neg 141)] := by
  exact comparison_gate s permutation6 77 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3406) (Sat.Literal.pos 77) (Sat.Literal.pos 141) (lex_6_77_prefix s) (positive_select s 77) (lex_6_77_image s)

theorem lex_6_77_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3407), (Sat.Literal.pos 3406)] :=
  (lex_6_77_gate s).prop _ (List.Mem.head _)

theorem lex_6_77_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3407), (Sat.Literal.neg 77), (Sat.Literal.pos 141)] :=
  (lex_6_77_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_77_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3407), (Sat.Literal.pos 77), (Sat.Literal.neg 141)] :=
  (lex_6_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_77_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3406), (Sat.Literal.neg 77), (Sat.Literal.neg 141), (Sat.Literal.pos 3407)] :=
  (lex_6_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_77_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3406), (Sat.Literal.pos 77), (Sat.Literal.pos 141), (Sat.Literal.pos 3407)] :=
  (lex_6_77_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_76_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3407) = lexBefore s permutation6 76 := by
  exact (positive_lex_of_descriptor s 3407 permutation6 77 (by rfl)).trans ((lex_skipped s permutation6 76 77 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 77 77 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_76_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 140) = s (permuteMask permutation6 76) := by
  exact (positive_select s 140).trans (congrArg s (show (140 : Fin 256) = permuteMask permutation6 76 by rw [image6_eq]; rfl))

theorem lex_6_76_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3408) (Sat.Literal.pos 3407) (Sat.Literal.pos 76) (Sat.Literal.pos 140)) := by
  exact equality_gate s permutation6 76 (assignment s)
    (Sat.Literal.pos 3408) (Sat.Literal.pos 3407) (Sat.Literal.pos 76) (Sat.Literal.pos 140) (positive_of_descriptor s 3408 (.lex permutation6 76) (by rfl)) (lex_6_76_prefix s) (positive_select s 76) (lex_6_76_image s)

theorem lex_6_76_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3407), (Sat.Literal.pos 76), (Sat.Literal.neg 140)] := by
  exact comparison_gate s permutation6 76 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3407) (Sat.Literal.pos 76) (Sat.Literal.pos 140) (lex_6_76_prefix s) (positive_select s 76) (lex_6_76_image s)

theorem lex_6_76_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3408), (Sat.Literal.pos 3407)] :=
  (lex_6_76_gate s).prop _ (List.Mem.head _)

theorem lex_6_76_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3408), (Sat.Literal.neg 76), (Sat.Literal.pos 140)] :=
  (lex_6_76_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_76_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3408), (Sat.Literal.pos 76), (Sat.Literal.neg 140)] :=
  (lex_6_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_76_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3407), (Sat.Literal.neg 76), (Sat.Literal.neg 140), (Sat.Literal.pos 3408)] :=
  (lex_6_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_76_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3407), (Sat.Literal.pos 76), (Sat.Literal.pos 140), (Sat.Literal.pos 3408)] :=
  (lex_6_76_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_75_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3408) = lexBefore s permutation6 75 := by
  exact (positive_lex_of_descriptor s 3408 permutation6 76 (by rfl)).trans ((lex_skipped s permutation6 75 76 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 76 76 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_75_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 139) = s (permuteMask permutation6 75) := by
  exact (positive_select s 139).trans (congrArg s (show (139 : Fin 256) = permuteMask permutation6 75 by rw [image6_eq]; rfl))

theorem lex_6_75_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3409) (Sat.Literal.pos 3408) (Sat.Literal.pos 75) (Sat.Literal.pos 139)) := by
  exact equality_gate s permutation6 75 (assignment s)
    (Sat.Literal.pos 3409) (Sat.Literal.pos 3408) (Sat.Literal.pos 75) (Sat.Literal.pos 139) (positive_of_descriptor s 3409 (.lex permutation6 75) (by rfl)) (lex_6_75_prefix s) (positive_select s 75) (lex_6_75_image s)

theorem lex_6_75_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3408), (Sat.Literal.pos 75), (Sat.Literal.neg 139)] := by
  exact comparison_gate s permutation6 75 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3408) (Sat.Literal.pos 75) (Sat.Literal.pos 139) (lex_6_75_prefix s) (positive_select s 75) (lex_6_75_image s)

theorem lex_6_75_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3409), (Sat.Literal.pos 3408)] :=
  (lex_6_75_gate s).prop _ (List.Mem.head _)

theorem lex_6_75_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3409), (Sat.Literal.neg 75), (Sat.Literal.pos 139)] :=
  (lex_6_75_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_75_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3409), (Sat.Literal.pos 75), (Sat.Literal.neg 139)] :=
  (lex_6_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_75_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3408), (Sat.Literal.neg 75), (Sat.Literal.neg 139), (Sat.Literal.pos 3409)] :=
  (lex_6_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_75_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3408), (Sat.Literal.pos 75), (Sat.Literal.pos 139), (Sat.Literal.pos 3409)] :=
  (lex_6_75_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_74_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3409) = lexBefore s permutation6 74 := by
  exact (positive_lex_of_descriptor s 3409 permutation6 75 (by rfl)).trans ((lex_skipped s permutation6 74 75 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 75 75 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_74_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 138) = s (permuteMask permutation6 74) := by
  exact (positive_select s 138).trans (congrArg s (show (138 : Fin 256) = permuteMask permutation6 74 by rw [image6_eq]; rfl))

theorem lex_6_74_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3410) (Sat.Literal.pos 3409) (Sat.Literal.pos 74) (Sat.Literal.pos 138)) := by
  exact equality_gate s permutation6 74 (assignment s)
    (Sat.Literal.pos 3410) (Sat.Literal.pos 3409) (Sat.Literal.pos 74) (Sat.Literal.pos 138) (positive_of_descriptor s 3410 (.lex permutation6 74) (by rfl)) (lex_6_74_prefix s) (positive_select s 74) (lex_6_74_image s)

theorem lex_6_74_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3409), (Sat.Literal.pos 74), (Sat.Literal.neg 138)] := by
  exact comparison_gate s permutation6 74 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3409) (Sat.Literal.pos 74) (Sat.Literal.pos 138) (lex_6_74_prefix s) (positive_select s 74) (lex_6_74_image s)

theorem lex_6_74_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3410), (Sat.Literal.pos 3409)] :=
  (lex_6_74_gate s).prop _ (List.Mem.head _)

theorem lex_6_74_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3410), (Sat.Literal.neg 74), (Sat.Literal.pos 138)] :=
  (lex_6_74_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_74_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3410), (Sat.Literal.pos 74), (Sat.Literal.neg 138)] :=
  (lex_6_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_74_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3409), (Sat.Literal.neg 74), (Sat.Literal.neg 138), (Sat.Literal.pos 3410)] :=
  (lex_6_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_74_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3409), (Sat.Literal.pos 74), (Sat.Literal.pos 138), (Sat.Literal.pos 3410)] :=
  (lex_6_74_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_73_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3410) = lexBefore s permutation6 73 := by
  exact (positive_lex_of_descriptor s 3410 permutation6 74 (by rfl)).trans ((lex_skipped s permutation6 73 74 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 74 74 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_73_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 137) = s (permuteMask permutation6 73) := by
  exact (positive_select s 137).trans (congrArg s (show (137 : Fin 256) = permuteMask permutation6 73 by rw [image6_eq]; rfl))

theorem lex_6_73_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3411) (Sat.Literal.pos 3410) (Sat.Literal.pos 73) (Sat.Literal.pos 137)) := by
  exact equality_gate s permutation6 73 (assignment s)
    (Sat.Literal.pos 3411) (Sat.Literal.pos 3410) (Sat.Literal.pos 73) (Sat.Literal.pos 137) (positive_of_descriptor s 3411 (.lex permutation6 73) (by rfl)) (lex_6_73_prefix s) (positive_select s 73) (lex_6_73_image s)

theorem lex_6_73_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3410), (Sat.Literal.pos 73), (Sat.Literal.neg 137)] := by
  exact comparison_gate s permutation6 73 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3410) (Sat.Literal.pos 73) (Sat.Literal.pos 137) (lex_6_73_prefix s) (positive_select s 73) (lex_6_73_image s)

theorem lex_6_73_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3411), (Sat.Literal.pos 3410)] :=
  (lex_6_73_gate s).prop _ (List.Mem.head _)

theorem lex_6_73_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3411), (Sat.Literal.neg 73), (Sat.Literal.pos 137)] :=
  (lex_6_73_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_73_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3411), (Sat.Literal.pos 73), (Sat.Literal.neg 137)] :=
  (lex_6_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_73_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3410), (Sat.Literal.neg 73), (Sat.Literal.neg 137), (Sat.Literal.pos 3411)] :=
  (lex_6_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_73_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3410), (Sat.Literal.pos 73), (Sat.Literal.pos 137), (Sat.Literal.pos 3411)] :=
  (lex_6_73_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_72_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3411) = lexBefore s permutation6 72 := by
  exact (positive_lex_of_descriptor s 3411 permutation6 73 (by rfl)).trans ((lex_skipped s permutation6 72 73 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 73 73 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_72_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 136) = s (permuteMask permutation6 72) := by
  exact (positive_select s 136).trans (congrArg s (show (136 : Fin 256) = permuteMask permutation6 72 by rw [image6_eq]; rfl))

theorem lex_6_72_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3412) (Sat.Literal.pos 3411) (Sat.Literal.pos 72) (Sat.Literal.pos 136)) := by
  exact equality_gate s permutation6 72 (assignment s)
    (Sat.Literal.pos 3412) (Sat.Literal.pos 3411) (Sat.Literal.pos 72) (Sat.Literal.pos 136) (positive_of_descriptor s 3412 (.lex permutation6 72) (by rfl)) (lex_6_72_prefix s) (positive_select s 72) (lex_6_72_image s)

theorem lex_6_72_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3411), (Sat.Literal.pos 72), (Sat.Literal.neg 136)] := by
  exact comparison_gate s permutation6 72 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3411) (Sat.Literal.pos 72) (Sat.Literal.pos 136) (lex_6_72_prefix s) (positive_select s 72) (lex_6_72_image s)

theorem lex_6_72_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3412), (Sat.Literal.pos 3411)] :=
  (lex_6_72_gate s).prop _ (List.Mem.head _)

theorem lex_6_72_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3412), (Sat.Literal.neg 72), (Sat.Literal.pos 136)] :=
  (lex_6_72_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_72_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3412), (Sat.Literal.pos 72), (Sat.Literal.neg 136)] :=
  (lex_6_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_72_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3411), (Sat.Literal.neg 72), (Sat.Literal.neg 136), (Sat.Literal.pos 3412)] :=
  (lex_6_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_72_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3411), (Sat.Literal.pos 72), (Sat.Literal.pos 136), (Sat.Literal.pos 3412)] :=
  (lex_6_72_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_71_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3412) = lexBefore s permutation6 71 := by
  exact (positive_lex_of_descriptor s 3412 permutation6 72 (by rfl)).trans ((lex_skipped s permutation6 71 72 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 72 72 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_71_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 135) = s (permuteMask permutation6 71) := by
  exact (positive_select s 135).trans (congrArg s (show (135 : Fin 256) = permuteMask permutation6 71 by rw [image6_eq]; rfl))

theorem lex_6_71_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3413) (Sat.Literal.pos 3412) (Sat.Literal.pos 71) (Sat.Literal.pos 135)) := by
  exact equality_gate s permutation6 71 (assignment s)
    (Sat.Literal.pos 3413) (Sat.Literal.pos 3412) (Sat.Literal.pos 71) (Sat.Literal.pos 135) (positive_of_descriptor s 3413 (.lex permutation6 71) (by rfl)) (lex_6_71_prefix s) (positive_select s 71) (lex_6_71_image s)

theorem lex_6_71_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3412), (Sat.Literal.pos 71), (Sat.Literal.neg 135)] := by
  exact comparison_gate s permutation6 71 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3412) (Sat.Literal.pos 71) (Sat.Literal.pos 135) (lex_6_71_prefix s) (positive_select s 71) (lex_6_71_image s)

theorem lex_6_71_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3413), (Sat.Literal.pos 3412)] :=
  (lex_6_71_gate s).prop _ (List.Mem.head _)

theorem lex_6_71_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3413), (Sat.Literal.neg 71), (Sat.Literal.pos 135)] :=
  (lex_6_71_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_71_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3413), (Sat.Literal.pos 71), (Sat.Literal.neg 135)] :=
  (lex_6_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_71_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3412), (Sat.Literal.neg 71), (Sat.Literal.neg 135), (Sat.Literal.pos 3413)] :=
  (lex_6_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_71_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3412), (Sat.Literal.pos 71), (Sat.Literal.pos 135), (Sat.Literal.pos 3413)] :=
  (lex_6_71_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_70_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3413) = lexBefore s permutation6 70 := by
  exact (positive_lex_of_descriptor s 3413 permutation6 71 (by rfl)).trans ((lex_skipped s permutation6 70 71 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 71 71 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_70_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 134) = s (permuteMask permutation6 70) := by
  exact (positive_select s 134).trans (congrArg s (show (134 : Fin 256) = permuteMask permutation6 70 by rw [image6_eq]; rfl))

theorem lex_6_70_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3414) (Sat.Literal.pos 3413) (Sat.Literal.pos 70) (Sat.Literal.pos 134)) := by
  exact equality_gate s permutation6 70 (assignment s)
    (Sat.Literal.pos 3414) (Sat.Literal.pos 3413) (Sat.Literal.pos 70) (Sat.Literal.pos 134) (positive_of_descriptor s 3414 (.lex permutation6 70) (by rfl)) (lex_6_70_prefix s) (positive_select s 70) (lex_6_70_image s)

theorem lex_6_70_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3413), (Sat.Literal.pos 70), (Sat.Literal.neg 134)] := by
  exact comparison_gate s permutation6 70 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3413) (Sat.Literal.pos 70) (Sat.Literal.pos 134) (lex_6_70_prefix s) (positive_select s 70) (lex_6_70_image s)

theorem lex_6_70_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3414), (Sat.Literal.pos 3413)] :=
  (lex_6_70_gate s).prop _ (List.Mem.head _)

theorem lex_6_70_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3414), (Sat.Literal.neg 70), (Sat.Literal.pos 134)] :=
  (lex_6_70_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_70_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3414), (Sat.Literal.pos 70), (Sat.Literal.neg 134)] :=
  (lex_6_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_70_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3413), (Sat.Literal.neg 70), (Sat.Literal.neg 134), (Sat.Literal.pos 3414)] :=
  (lex_6_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_70_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3413), (Sat.Literal.pos 70), (Sat.Literal.pos 134), (Sat.Literal.pos 3414)] :=
  (lex_6_70_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_69_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3414) = lexBefore s permutation6 69 := by
  exact (positive_lex_of_descriptor s 3414 permutation6 70 (by rfl)).trans ((lex_skipped s permutation6 69 70 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 70 70 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_69_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 133) = s (permuteMask permutation6 69) := by
  exact (positive_select s 133).trans (congrArg s (show (133 : Fin 256) = permuteMask permutation6 69 by rw [image6_eq]; rfl))

theorem lex_6_69_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3415) (Sat.Literal.pos 3414) (Sat.Literal.pos 69) (Sat.Literal.pos 133)) := by
  exact equality_gate s permutation6 69 (assignment s)
    (Sat.Literal.pos 3415) (Sat.Literal.pos 3414) (Sat.Literal.pos 69) (Sat.Literal.pos 133) (positive_of_descriptor s 3415 (.lex permutation6 69) (by rfl)) (lex_6_69_prefix s) (positive_select s 69) (lex_6_69_image s)

theorem lex_6_69_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3414), (Sat.Literal.pos 69), (Sat.Literal.neg 133)] := by
  exact comparison_gate s permutation6 69 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3414) (Sat.Literal.pos 69) (Sat.Literal.pos 133) (lex_6_69_prefix s) (positive_select s 69) (lex_6_69_image s)

theorem lex_6_69_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3415), (Sat.Literal.pos 3414)] :=
  (lex_6_69_gate s).prop _ (List.Mem.head _)

theorem lex_6_69_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3415), (Sat.Literal.neg 69), (Sat.Literal.pos 133)] :=
  (lex_6_69_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_69_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3415), (Sat.Literal.pos 69), (Sat.Literal.neg 133)] :=
  (lex_6_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_69_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3414), (Sat.Literal.neg 69), (Sat.Literal.neg 133), (Sat.Literal.pos 3415)] :=
  (lex_6_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_69_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3414), (Sat.Literal.pos 69), (Sat.Literal.pos 133), (Sat.Literal.pos 3415)] :=
  (lex_6_69_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_68_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3415) = lexBefore s permutation6 68 := by
  exact (positive_lex_of_descriptor s 3415 permutation6 69 (by rfl)).trans ((lex_skipped s permutation6 68 69 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 69 69 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_68_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 132) = s (permuteMask permutation6 68) := by
  exact (positive_select s 132).trans (congrArg s (show (132 : Fin 256) = permuteMask permutation6 68 by rw [image6_eq]; rfl))

theorem lex_6_68_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3416) (Sat.Literal.pos 3415) (Sat.Literal.pos 68) (Sat.Literal.pos 132)) := by
  exact equality_gate s permutation6 68 (assignment s)
    (Sat.Literal.pos 3416) (Sat.Literal.pos 3415) (Sat.Literal.pos 68) (Sat.Literal.pos 132) (positive_of_descriptor s 3416 (.lex permutation6 68) (by rfl)) (lex_6_68_prefix s) (positive_select s 68) (lex_6_68_image s)

theorem lex_6_68_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3415), (Sat.Literal.pos 68), (Sat.Literal.neg 132)] := by
  exact comparison_gate s permutation6 68 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3415) (Sat.Literal.pos 68) (Sat.Literal.pos 132) (lex_6_68_prefix s) (positive_select s 68) (lex_6_68_image s)

theorem lex_6_68_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3416), (Sat.Literal.pos 3415)] :=
  (lex_6_68_gate s).prop _ (List.Mem.head _)

theorem lex_6_68_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3416), (Sat.Literal.neg 68), (Sat.Literal.pos 132)] :=
  (lex_6_68_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_68_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3416), (Sat.Literal.pos 68), (Sat.Literal.neg 132)] :=
  (lex_6_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_68_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3415), (Sat.Literal.neg 68), (Sat.Literal.neg 132), (Sat.Literal.pos 3416)] :=
  (lex_6_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_68_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3415), (Sat.Literal.pos 68), (Sat.Literal.pos 132), (Sat.Literal.pos 3416)] :=
  (lex_6_68_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_67_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3416) = lexBefore s permutation6 67 := by
  exact (positive_lex_of_descriptor s 3416 permutation6 68 (by rfl)).trans ((lex_skipped s permutation6 67 68 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 68 68 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_67_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 131) = s (permuteMask permutation6 67) := by
  exact (positive_select s 131).trans (congrArg s (show (131 : Fin 256) = permuteMask permutation6 67 by rw [image6_eq]; rfl))

theorem lex_6_67_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3417) (Sat.Literal.pos 3416) (Sat.Literal.pos 67) (Sat.Literal.pos 131)) := by
  exact equality_gate s permutation6 67 (assignment s)
    (Sat.Literal.pos 3417) (Sat.Literal.pos 3416) (Sat.Literal.pos 67) (Sat.Literal.pos 131) (positive_of_descriptor s 3417 (.lex permutation6 67) (by rfl)) (lex_6_67_prefix s) (positive_select s 67) (lex_6_67_image s)

theorem lex_6_67_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3416), (Sat.Literal.pos 67), (Sat.Literal.neg 131)] := by
  exact comparison_gate s permutation6 67 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3416) (Sat.Literal.pos 67) (Sat.Literal.pos 131) (lex_6_67_prefix s) (positive_select s 67) (lex_6_67_image s)

theorem lex_6_67_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3417), (Sat.Literal.pos 3416)] :=
  (lex_6_67_gate s).prop _ (List.Mem.head _)

theorem lex_6_67_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3417), (Sat.Literal.neg 67), (Sat.Literal.pos 131)] :=
  (lex_6_67_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_67_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3417), (Sat.Literal.pos 67), (Sat.Literal.neg 131)] :=
  (lex_6_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_67_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3416), (Sat.Literal.neg 67), (Sat.Literal.neg 131), (Sat.Literal.pos 3417)] :=
  (lex_6_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_67_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3416), (Sat.Literal.pos 67), (Sat.Literal.pos 131), (Sat.Literal.pos 3417)] :=
  (lex_6_67_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_66_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3417) = lexBefore s permutation6 66 := by
  exact (positive_lex_of_descriptor s 3417 permutation6 67 (by rfl)).trans ((lex_skipped s permutation6 66 67 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 67 67 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_66_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 130) = s (permuteMask permutation6 66) := by
  exact (positive_select s 130).trans (congrArg s (show (130 : Fin 256) = permuteMask permutation6 66 by rw [image6_eq]; rfl))

theorem lex_6_66_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3418) (Sat.Literal.pos 3417) (Sat.Literal.pos 66) (Sat.Literal.pos 130)) := by
  exact equality_gate s permutation6 66 (assignment s)
    (Sat.Literal.pos 3418) (Sat.Literal.pos 3417) (Sat.Literal.pos 66) (Sat.Literal.pos 130) (positive_of_descriptor s 3418 (.lex permutation6 66) (by rfl)) (lex_6_66_prefix s) (positive_select s 66) (lex_6_66_image s)

theorem lex_6_66_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3417), (Sat.Literal.pos 66), (Sat.Literal.neg 130)] := by
  exact comparison_gate s permutation6 66 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3417) (Sat.Literal.pos 66) (Sat.Literal.pos 130) (lex_6_66_prefix s) (positive_select s 66) (lex_6_66_image s)

theorem lex_6_66_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3418), (Sat.Literal.pos 3417)] :=
  (lex_6_66_gate s).prop _ (List.Mem.head _)

theorem lex_6_66_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3418), (Sat.Literal.neg 66), (Sat.Literal.pos 130)] :=
  (lex_6_66_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_66_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3418), (Sat.Literal.pos 66), (Sat.Literal.neg 130)] :=
  (lex_6_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_66_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3417), (Sat.Literal.neg 66), (Sat.Literal.neg 130), (Sat.Literal.pos 3418)] :=
  (lex_6_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_66_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3417), (Sat.Literal.pos 66), (Sat.Literal.pos 130), (Sat.Literal.pos 3418)] :=
  (lex_6_66_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_65_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3418) = lexBefore s permutation6 65 := by
  exact (positive_lex_of_descriptor s 3418 permutation6 66 (by rfl)).trans ((lex_skipped s permutation6 65 66 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 66 66 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_65_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 129) = s (permuteMask permutation6 65) := by
  exact (positive_select s 129).trans (congrArg s (show (129 : Fin 256) = permuteMask permutation6 65 by rw [image6_eq]; rfl))

theorem lex_6_65_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3419) (Sat.Literal.pos 3418) (Sat.Literal.pos 65) (Sat.Literal.pos 129)) := by
  exact equality_gate s permutation6 65 (assignment s)
    (Sat.Literal.pos 3419) (Sat.Literal.pos 3418) (Sat.Literal.pos 65) (Sat.Literal.pos 129) (positive_of_descriptor s 3419 (.lex permutation6 65) (by rfl)) (lex_6_65_prefix s) (positive_select s 65) (lex_6_65_image s)

theorem lex_6_65_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3418), (Sat.Literal.pos 65), (Sat.Literal.neg 129)] := by
  exact comparison_gate s permutation6 65 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3418) (Sat.Literal.pos 65) (Sat.Literal.pos 129) (lex_6_65_prefix s) (positive_select s 65) (lex_6_65_image s)

theorem lex_6_65_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3419), (Sat.Literal.pos 3418)] :=
  (lex_6_65_gate s).prop _ (List.Mem.head _)

theorem lex_6_65_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3419), (Sat.Literal.neg 65), (Sat.Literal.pos 129)] :=
  (lex_6_65_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_65_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3419), (Sat.Literal.pos 65), (Sat.Literal.neg 129)] :=
  (lex_6_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_65_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3418), (Sat.Literal.neg 65), (Sat.Literal.neg 129), (Sat.Literal.pos 3419)] :=
  (lex_6_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_65_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3418), (Sat.Literal.pos 65), (Sat.Literal.pos 129), (Sat.Literal.pos 3419)] :=
  (lex_6_65_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_6_64_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3419) = lexBefore s permutation6 64 := by
  exact (positive_lex_of_descriptor s 3419 permutation6 65 (by rfl)).trans ((lex_skipped s permutation6 64 65 (by decide) (by intro j hj hp; rw [image6_eq]; exact fixedOnRange_spec image6 65 65 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_6_64_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 128) = s (permuteMask permutation6 64) := by
  exact (positive_select s 128).trans (congrArg s (show (128 : Fin 256) = permuteMask permutation6 64 by rw [image6_eq]; rfl))

theorem lex_6_64_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3420) (Sat.Literal.pos 3419) (Sat.Literal.pos 64) (Sat.Literal.pos 128)) := by
  exact equality_gate s permutation6 64 (assignment s)
    (Sat.Literal.pos 3420) (Sat.Literal.pos 3419) (Sat.Literal.pos 64) (Sat.Literal.pos 128) (positive_of_descriptor s 3420 (.lex permutation6 64) (by rfl)) (lex_6_64_prefix s) (positive_select s 64) (lex_6_64_image s)

theorem lex_6_64_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3419), (Sat.Literal.pos 64), (Sat.Literal.neg 128)] := by
  exact comparison_gate s permutation6 64 (hmax permutation6) (assignment s)
    (Sat.Literal.pos 3419) (Sat.Literal.pos 64) (Sat.Literal.pos 128) (lex_6_64_prefix s) (positive_select s 64) (lex_6_64_image s)

theorem lex_6_64_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3420), (Sat.Literal.pos 3419)] :=
  (lex_6_64_gate s).prop _ (List.Mem.head _)

theorem lex_6_64_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3420), (Sat.Literal.neg 64), (Sat.Literal.pos 128)] :=
  (lex_6_64_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_6_64_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3420), (Sat.Literal.pos 64), (Sat.Literal.neg 128)] :=
  (lex_6_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_6_64_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3419), (Sat.Literal.neg 64), (Sat.Literal.neg 128), (Sat.Literal.pos 3420)] :=
  (lex_6_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_6_64_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3419), (Sat.Literal.pos 64), (Sat.Literal.pos 128), (Sat.Literal.pos 3420)] :=
  (lex_6_64_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_254_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.neg 256) = lexBefore s permutation7 254 := by
  exact (negative_falsum s).trans ((lex_first s permutation7 254 (by intro j hj; rw [image7_eq]; exact fixedOnRange_spec image7 255 256 (by decide +kernel) j (by omega) j.isLt)).symm)

theorem lex_7_254_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 253) = s (permuteMask permutation7 254) := by
  exact (positive_select s 253).trans (congrArg s (show (253 : Fin 256) = permuteMask permutation7 254 by rw [image7_eq]; rfl))

theorem lex_7_254_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3421) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 253)) := by
  exact equality_gate s permutation7 254 (assignment s)
    (Sat.Literal.pos 3421) (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 253) (positive_of_descriptor s 3421 (.lex permutation7 254) (by rfl)) (lex_7_254_prefix s) (positive_select s 254) (lex_7_254_image s)

theorem lex_7_254_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.neg 253)] := by
  exact comparison_gate s permutation7 254 (hmax permutation7) (assignment s)
    (Sat.Literal.neg 256) (Sat.Literal.pos 254) (Sat.Literal.pos 253) (lex_7_254_prefix s) (positive_select s 254) (lex_7_254_image s)

theorem lex_7_254_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3421), (Sat.Literal.neg 256)] :=
  (lex_7_254_gate s).prop _ (List.Mem.head _)

theorem lex_7_254_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3421), (Sat.Literal.neg 254), (Sat.Literal.pos 253)] :=
  (lex_7_254_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_254_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3421), (Sat.Literal.pos 254), (Sat.Literal.neg 253)] :=
  (lex_7_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_254_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.neg 254), (Sat.Literal.neg 253), (Sat.Literal.pos 3421)] :=
  (lex_7_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_254_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.pos 256), (Sat.Literal.pos 254), (Sat.Literal.pos 253), (Sat.Literal.pos 3421)] :=
  (lex_7_254_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_253_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3421) = lexBefore s permutation7 253 := by
  exact (positive_lex_of_descriptor s 3421 permutation7 254 (by rfl)).trans ((lex_skipped s permutation7 253 254 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 254 254 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_253_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 251) = s (permuteMask permutation7 253) := by
  exact (positive_select s 251).trans (congrArg s (show (251 : Fin 256) = permuteMask permutation7 253 by rw [image7_eq]; rfl))

theorem lex_7_253_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3422) (Sat.Literal.pos 3421) (Sat.Literal.pos 253) (Sat.Literal.pos 251)) := by
  exact equality_gate s permutation7 253 (assignment s)
    (Sat.Literal.pos 3422) (Sat.Literal.pos 3421) (Sat.Literal.pos 253) (Sat.Literal.pos 251) (positive_of_descriptor s 3422 (.lex permutation7 253) (by rfl)) (lex_7_253_prefix s) (positive_select s 253) (lex_7_253_image s)

theorem lex_7_253_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3421), (Sat.Literal.pos 253), (Sat.Literal.neg 251)] := by
  exact comparison_gate s permutation7 253 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3421) (Sat.Literal.pos 253) (Sat.Literal.pos 251) (lex_7_253_prefix s) (positive_select s 253) (lex_7_253_image s)

theorem lex_7_253_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3422), (Sat.Literal.pos 3421)] :=
  (lex_7_253_gate s).prop _ (List.Mem.head _)

theorem lex_7_253_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3422), (Sat.Literal.neg 253), (Sat.Literal.pos 251)] :=
  (lex_7_253_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_253_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3422), (Sat.Literal.pos 253), (Sat.Literal.neg 251)] :=
  (lex_7_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_253_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3421), (Sat.Literal.neg 253), (Sat.Literal.neg 251), (Sat.Literal.pos 3422)] :=
  (lex_7_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_253_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3421), (Sat.Literal.pos 253), (Sat.Literal.pos 251), (Sat.Literal.pos 3422)] :=
  (lex_7_253_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_252_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3422) = lexBefore s permutation7 252 := by
  exact (positive_lex_of_descriptor s 3422 permutation7 253 (by rfl)).trans ((lex_skipped s permutation7 252 253 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 253 253 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_252_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 249) = s (permuteMask permutation7 252) := by
  exact (positive_select s 249).trans (congrArg s (show (249 : Fin 256) = permuteMask permutation7 252 by rw [image7_eq]; rfl))

theorem lex_7_252_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3423) (Sat.Literal.pos 3422) (Sat.Literal.pos 252) (Sat.Literal.pos 249)) := by
  exact equality_gate s permutation7 252 (assignment s)
    (Sat.Literal.pos 3423) (Sat.Literal.pos 3422) (Sat.Literal.pos 252) (Sat.Literal.pos 249) (positive_of_descriptor s 3423 (.lex permutation7 252) (by rfl)) (lex_7_252_prefix s) (positive_select s 252) (lex_7_252_image s)

theorem lex_7_252_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3422), (Sat.Literal.pos 252), (Sat.Literal.neg 249)] := by
  exact comparison_gate s permutation7 252 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3422) (Sat.Literal.pos 252) (Sat.Literal.pos 249) (lex_7_252_prefix s) (positive_select s 252) (lex_7_252_image s)

theorem lex_7_252_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3423), (Sat.Literal.pos 3422)] :=
  (lex_7_252_gate s).prop _ (List.Mem.head _)

theorem lex_7_252_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3423), (Sat.Literal.neg 252), (Sat.Literal.pos 249)] :=
  (lex_7_252_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_252_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3423), (Sat.Literal.pos 252), (Sat.Literal.neg 249)] :=
  (lex_7_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_252_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3422), (Sat.Literal.neg 252), (Sat.Literal.neg 249), (Sat.Literal.pos 3423)] :=
  (lex_7_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_252_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3422), (Sat.Literal.pos 252), (Sat.Literal.pos 249), (Sat.Literal.pos 3423)] :=
  (lex_7_252_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem lex_7_251_prefix (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 3423) = lexBefore s permutation7 251 := by
  exact (positive_lex_of_descriptor s 3423 permutation7 252 (by rfl)).trans ((lex_skipped s permutation7 251 252 (by decide) (by intro j hj hp; rw [image7_eq]; exact fixedOnRange_spec image7 252 252 (by decide +kernel) j (by omega) (by omega))).symm)

theorem lex_7_251_image (s : Fin 256 → Bool) :
    literalValue (assignment s) (Sat.Literal.pos 247) = s (permuteMask permutation7 251) := by
  exact (positive_select s 247).trans (congrArg s (show (247 : Fin 256) = permuteMask permutation7 251 by rw [image7_eq]; rfl))

theorem lex_7_251_gate (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies_fmla (equalityCNF (Sat.Literal.pos 3424) (Sat.Literal.pos 3423) (Sat.Literal.pos 251) (Sat.Literal.pos 247)) := by
  exact equality_gate s permutation7 251 (assignment s)
    (Sat.Literal.pos 3424) (Sat.Literal.pos 3423) (Sat.Literal.pos 251) (Sat.Literal.pos 247) (positive_of_descriptor s 3424 (.lex permutation7 251) (by rfl)) (lex_7_251_prefix s) (positive_select s 251) (lex_7_251_image s)

theorem lex_7_251_comparison (s : Fin 256 → Bool)
    (hmax : ∀ d, toColex (relabelSelector s d) ≤ toColex s) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3423), (Sat.Literal.pos 251), (Sat.Literal.neg 247)] := by
  exact comparison_gate s permutation7 251 (hmax permutation7) (assignment s)
    (Sat.Literal.pos 3423) (Sat.Literal.pos 251) (Sat.Literal.pos 247) (lex_7_251_prefix s) (positive_select s 251) (lex_7_251_image s)

theorem lex_7_251_clause0 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3424), (Sat.Literal.pos 3423)] :=
  (lex_7_251_gate s).prop _ (List.Mem.head _)

theorem lex_7_251_clause1 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3424), (Sat.Literal.neg 251), (Sat.Literal.pos 247)] :=
  (lex_7_251_gate s).prop _ (List.Mem.tail _ (List.Mem.head _))

theorem lex_7_251_clause2 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3424), (Sat.Literal.pos 251), (Sat.Literal.neg 247)] :=
  (lex_7_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem lex_7_251_clause3 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3423), (Sat.Literal.neg 251), (Sat.Literal.neg 247), (Sat.Literal.pos 3424)] :=
  (lex_7_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lex_7_251_clause4 (s : Fin 256 → Bool) :
    (valuation (assignment s)).satisfies [(Sat.Literal.neg 3423), (Sat.Literal.pos 251), (Sat.Literal.pos 247), (Sat.Literal.pos 3424)] :=
  (lex_7_251_gate s).prop _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

#print axioms lex_6_159_gate

end Crown.CertificateData
